Require Import ZArith.
Require Import Bool.

(*-------------------------- Syntax of Lambda+ -------------------------------*)
(* Arithmetic operations to distinguish different operations *)
Inductive aop : Type := 
	| Add 		: aop
	| Sub 		: aop
	| Mul			: aop. 
(* Boolan operations to distinguish different operations *)
Inductive bop : Type := 
	| And 		: bop
	| Or 			: bop
	| Greater : bop
	| Less		: bop
	| Equal 	: bop.

(* The actual syntax (post front-end) of Lambda+ *)
Inductive term : Type := 
	| Var 		: nat -> term										(* Variable *)
	| EInt 		: Z -> term 										(* Integer literal *)
	| EBool 	: bool -> term									(* Boolean literal *)
	| Aop 		: aop -> term -> term -> term 	(* Arithmetic operations *)
	| BBop 		: bop -> term -> term -> term   (* Boolean Binary operations *)
	| Not 		: term -> term									(* Not operation *)
	| If 			: term -> term -> term -> term	(* Conditional expression *)
	| Lambda 	: term -> term									(* Lambda abstraction *)
	| Apply 	: term -> term -> term.					(* Function application *)

(* Runtime values *)
Inductive value : Type :=
  | Int 		: Z -> value										(* Integer value *)
  | Bool 		: bool -> value									(* Boolean value *)
  | Closure : term -> env -> value					(* <f_body, f_denv> *)
(* Enviornment definition*)
with env : Type := 
  | Empty
  | Env : (value * env) -> env.

(*---------------------------- Utility Functions -----------------------------*)

(* Extends the enviornment with a new binding *)
Definition bind (env : env) (v : value) := Env (v, env).

(* Gets the value at position i, i-th De Bruijn's index *)
Fixpoint lookup (i : nat) (env : env) : option value :=  
	match env with
	  | Empty => None
	  | Env (e, renv) => 
	  		if i =? 0 
	  			then 
	  				Some(e) 
					else 
						lookup (i - 1) (renv)
	end.
	
(*---------------------------- Interpeter of Lambda+ -------------------------*)
Fixpoint eval (fuel : nat) (t : term) (env : env) : option value := 
	match fuel with 
		| 0 => Some (Int 10)	(* No fuel left, diverging *)
		
		| S rfuel =>					(* S rfuel == fuel + 1, rfuel = remaning fuel *)
				match t with 
					| Var x => 
							match (lookup x env) with
								| Some v => Some v
								| _ => None
							end
							
					| EInt n => Some (Int n)
					
					| EBool b => Some (Bool b)
					
					| Aop aop t0 t1 => 
							match (eval rfuel t0 env, eval rfuel t1 env) with
      					| (Some (Int i0), Some (Int i1)) =>
        						match aop with
        							| Add => Some (Int (i0 + i1))
        							| Sub => Some (Int (i0 - i1))
        							| Mul => Some (Int (i0 * i1))
        						end
      					| _ => None
							end
							
					| BBop bop t0 t1 => 
							match (eval rfuel t0 env, eval rfuel t1 env) with
								| (Some (Bool b0), Some (Bool b1)) => 
									match bop with
										| And => Some (Bool (andb b0 b1))
      							| Or => Some (Bool (orb b0 b1))
      							| _ => None
      						end
      					| (Some (Int i0), Some (Int i1)) => 
      							match bop with 
      								| Greater => Some (Bool (Z.gtb i0 i1))
      								| Less => Some (Bool (Z.ltb i0 i1))
      								| Equal => Some (Bool (Z.eqb i0 i1))
      								| _ => None
      							end
      					| _ => None
      				end
      				
					| Not t0 => 
							match (eval rfuel t0 env) with 
								| Some (Bool b0) => Some (Bool (negb b0))
								| _ => None
							end
							
					| If t t0 t1 => 
							match (eval rfuel t env) with 
								| Some (Bool true) => eval rfuel t0 env
								| Some (Bool false) => eval rfuel t1 env
								| _ => None
							end
					| Lambda t => Some (Closure t env)
					
					| Apply t1 t0 => 
							let param_val := eval rfuel t0 env 
							in 
								match param_val with
									| Some v => 
											let f_closure := eval rfuel t1 env 
												in
													match f_closure with 
														(* denv = Declaration Env*)
														| Some (Closure body denv) => 
																let new_env := bind denv v
																in 
																	eval rfuel body new_env
														| _ => None
													end
									| _ => None
								end
				end
	end.

(*-------------------------- Syntax of the VM --------------------------------*)
Inductive mterm : Type :=
  | PushVar     	: mvar -> mterm
  | PushClosure 	: mterm  -> mterm
  | PushVal   		: mvalue -> mterm
  | MAop      		: aop -> mterm
  | MBop					: bop -> mterm
  | MNot
	| MIf						: mterm -> mterm -> mterm
  | MApply
  | Return
  | Concat      	: mterm -> mterm -> mterm
  | Skip
  
with mvalue : Type :=
  | MBool      : bool -> mvalue
  | MInt       : Z -> mvalue
  | MClosure   : mterm -> menv -> mvalue
  | MRecord    : mterm -> menv -> mvalue
  
with mvar : Type := 
	| MVar : nat -> mvar
	
with menv : Type := 
	| MEmpty 
	| MEnv : (mvalue * menv) -> menv.

Inductive mstack : Type := 
	| SEmpty 
	| Stack : (mvalue * mstack) -> mstack.

(*-------------------------- Utility Functions -------------------------------*)

Definition mbind (env : menv) (v : mvalue) := MEnv (v, env).
Fixpoint mlookup (i : nat) (env : menv) : option mvalue :=  
	match env with
		| MEmpty => None
		| MEnv (e, renv) => 
				if i =? 0 
					then Some(e) 
				else 
					mlookup (i - 1) (renv)
	end.

Definition push (s : mstack) (v : mvalue) := Stack (v, s).
Definition pop (s : mstack) := 
	match s with
	  | SEmpty => (None, None)
	  | Stack (v, s') => (Some v, Some s')
	end.

(*-------------------------- MSteps of the VM --------------------------------*)
Inductive mstep : Type := 
  | MStep : mterm -> menv -> mstack -> mstep
  | MFStep : mvalue -> mstep
  | Error.

(*-------------------------- VM Interpreter ----------------------------------*)
Fixpoint meval (fuel: nat) (s : mstep) : mstep := match fuel with 
	| 0 => Error
	| S rfuel => match s with
	
		| MStep c env stack => match c with
		 
			| Skip => match pop stack with 
				| (Some v, Some sa1p) => match v with 
						| MRecord _ _ => Error
						| _ => MFStep v 
						end
				| _ => Error
				end
				
			| Concat c1 c2 => match c1 with 
			
				| Concat c3 c4 => meval rfuel (MStep (Concat c3 (Concat c4 c2)) env stack) 
				
				| Skip => meval rfuel (MStep c2 env stack)
			
				| PushVal v => meval rfuel (MStep c2 env (push stack v))
				
				| PushVar (MVar x) => match (mlookup x env) with
			 		| Some v => meval rfuel (MStep c2 env (push stack v))
			 		| _ => Error
				 	end
				 	
				| PushClosure c3 => meval rfuel (MStep c2 env (push stack (MClosure c3 env)))
				
				| MAop aop => match pop stack with 
	        | (Some (MInt z1), Some sa1p) => match pop sa1p with 
      			| (Some (MInt z2), Some sa2p) => match aop with 
                | Add => meval rfuel (MStep c2 env (push sa2p (MInt (z1 + z2))))
                | Sub => meval rfuel (MStep c2 env (push sa2p (MInt (z1 - z2))))
                | Mul => meval rfuel (MStep c2 env (push sa2p (MInt (z1 * z2))))
                end
            | _ => Error
            end
		        | _ => Error
					end
					
  			| MBop bop => match pop stack with 
      		| (Some v1, Some sa1p) => match pop sa1p with 
		      	| (Some v2, Some sa2p) => match v1, v2 with 
		          | MInt z1, MInt z2 => match bop with 
		            | Less => meval rfuel (MStep c2 env (push sa2p (MBool (Z.ltb z1 z2))))
		            | Equal => meval rfuel (MStep c2 env (push sa2p (MBool (Z.eqb z1 z2))))
		            | Greater => meval rfuel (MStep c2 env (push sa2p (MBool (Z.gtb z1 z2))))
		            | _ => Error
		        		end
		        	| MBool b1, MBool b2 => match bop with
		      		  | And => meval rfuel (MStep c2 env (push sa2p (MBool (andb b1 b2))))
		        	  | Or => meval rfuel (MStep c2 env (push sa2p (MBool (orb b1 b2))))
		        	  | _ => Error 
		        		end
		  				| _, _ => Error
							end
						| _ => Error
		 	 			end 
					|	 _ => Error 
	    		end
	    		
	    	| MNot => match pop stack with 
	    		| (Some (MBool b), Some sa1p) => 
	    				meval 
	    					rfuel 
	    					(MStep c2 env (push sa1p (MBool (negb b))))
	    		| _ => Error
	    		end
	    		
				| MIf c3 c4 => match pop stack with 
					| (Some (MBool b), Some sa1p) => match b with 
						| true => meval rfuel (MStep (Concat c3 c2) env sa1p)
						| false => meval rfuel (MStep (Concat c4 c2) env sa1p)
						end
					| _ => Error
					end
					
				| MApply => match pop stack with
					| (Some v1, Some sa1p) => match pop sa1p with  
						| (Some (MClosure c' denv), Some sa2p) => 
					 			meval 
									rfuel 
									(MStep c' (mbind denv v1) (push sa2p (MRecord c2 env)))
							
						| _ => Error
						end
					| _ => Error
					end
					
				| Return => match pop stack with 
					| (Some v, Some sa1p) => match pop sa1p with 
							| (Some (MRecord c' env'), Some sa2p) => 
									meval 
										rfuel 
										(MStep c' env' (push sa2p v))
							| _ => Error
							end
					| _ => Error
					end
				end
			| c1 => meval rfuel (MStep (Concat c1 Skip) env stack)
			end
		| _ => Error
		end
	end.
	
(*-------------------------- Compilation: term -> mterm ----------------------*)
Fixpoint compile (t: term) : option mterm :=
    match t with 
      | EInt i => Some (PushVal (MInt i))
      
      | EBool b => Some (PushVal (MBool b))
      
      | Var x => Some (PushVar (MVar x))
      
      | Aop aop t0 t1 => 
          match (compile t0), (compile t1) with 
              | Some ct0, Some ct1 => Some (Concat ct0 (Concat ct1 (MAop aop)))
              | _, _ => None
          end
          
      | BBop bop t0 t1 => 
          match (compile t0), (compile t1) with 
              | Some ct0, Some ct1 => Some (Concat ct0 (Concat ct1 (MBop bop)))
              | _, _ => None
          end
          
      | Not t => 
      		match (compile t) with
      				| Some ct => Some (Concat ct MNot)
      				| _ => None 
      		end
      		
      | If t t0 t1 => 
          match (compile t), (compile t0), (compile t1) with
              | Some ct, Some ct0, Some ct1 => Some (Concat ct (MIf ct0 ct1)) 
              | _, _, _ => None
          end
          
      | Lambda t => 
          match (compile t) with 
              | Some ct => Some (PushClosure(Concat ct Return))
              | _ => None
          end
          
      | Apply t0 t1 => 
          match (compile t0), (compile t1) with 
              | Some ct0, Some ct1 => Some (Concat ct0 (Concat ct1 MApply))
              | _, _ => None
          end
          
    end.
(*-------------------------------- Tests -------------------------------------*)
(* 
	In the context of Coq proofs, when you use reflexivity, Coq checks if 
	the goal is already in its simplest form, and if it is, the proof is complete. 
	If not, it tries to simplify both sides of the equation until they match, 
	at which point it concludes the proof.
*)

(* Interpreter Tests*)
Definition tadd := (Aop Add (EInt 3) (EInt 5)).
Example test_eval_add : eval 100 tadd Empty = Some (Int 8).
Proof. reflexivity. Qed.

Definition tand := (BBop And (EBool true) (EBool false)).
Example test_eval_and : eval 100 tand Empty = Some (Bool false).
Proof. reflexivity. Qed.

Definition tnot := (Not (EBool true)).
Example text_eval_not : eval 100 tnot Empty = Some (Bool false).
Proof. reflexivity. Qed.

Definition tiftrue := (If (EBool true) (EInt 3) (EInt 5)).
Example test_eval_iftrue : eval 100 tiftrue Empty = Some (Int 3).
Proof. reflexivity. Qed.

Definition tapply := (Apply (Lambda (Aop Add (EInt 5) (Var 0))) (EInt 3)).
Example test_eval_apply : eval 100 tapply Empty = Some (Int 8).
Proof. reflexivity. Qed.

(* Compiler Test *)
Compute compile tadd.
Compute compile tand.
Compute compile tnot.
Compute compile tiftrue.
Compute compile tapply.

(* VM Test *)
Definition test_madd := 
	match (compile tadd) with 
		| Some t => meval 100 (MStep t MEmpty SEmpty)
		| _ => Error
	end.
Example test_meval_add : test_madd = MFStep (MInt 8).
Proof. reflexivity. Qed.

Definition test_mand := 
	match (compile tand) with 
		| Some t => meval 100 (MStep t MEmpty SEmpty)
		| _ => Error
	end.
Example test_meval_and : test_mand = MFStep (MBool false).
Proof. reflexivity. Qed.

Definition test_mnot := 
	match (compile tnot) with 
		| Some t => meval 100 (MStep t MEmpty SEmpty)
		| _ => Error
	end.
Example test_meval_not : test_mnot = MFStep (MBool false).
Proof. reflexivity. Qed.

Definition test_mif := 
	match (compile tiftrue) with 
		| Some t => meval 100 (MStep t MEmpty SEmpty)
		| _ => Error
	end.
Example test_meval_if : test_mif = MFStep (MInt 3).
Proof. reflexivity. Qed.

Definition test_mapply := 
	match (compile tapply) with 
		| Some t => meval 100 (MStep t MEmpty SEmpty)
		| _ => Error
	end.
Example test_meval_apply : test_mapply = MFStep (MInt 8).
Proof. reflexivity. Qed.