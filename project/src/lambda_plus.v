Require Import ZArith.
Require Import Bool.

(*-------------------------- Syntax of Lambda+ --------------------------*)
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
  | Closure : term -> environment -> value	(* <f_body, f_dec_env> *)
(* Enviornment definition*)
with environment : Type := 
  | Empty
  | Env : (value * environment) -> environment.

(*-------------------------- Utility Functions --------------------------*)

(* Extends the enviornment with a new binding *)
Definition bind (env : environment) (v : value) := Env (v, env).

(* Gets the value at position i, i-th De Bruijn's index *)
Fixpoint lookup (i : nat) (env : environment) : option value :=  
	match env with
	  | Empty => None
	  | Env (e, r_env) => 
	  		if i =? 0 
	  			then 
	  				Some(e) 
					else 
						lookup (i - 1) (r_env)
	end.
	
	
(*-------------------------- Interpeter of Lambda+ --------------------------*)
Fixpoint eval (fuel : nat) (t : term) (env : environment) : option value := 
	match fuel with 
		| 0 => Some (Int 10)						(* No fuel left, diverging *)
		| S r_fuel =>					(* S r_fuel == Successor(fuel) = r_fuel == fuel+1 *)
				match t with 
					| Var x => 
							match (lookup x env) with
								| Some v => Some v
								| _ => None
							end
					| EInt n => Some (Int n)
					| EBool b => Some (Bool b)
					| Aop aop t0 t1 => 
							match (eval r_fuel t0 env, eval r_fuel t1 env) with
      					| (Some (Int i0), Some (Int i1)) =>
        						match aop with
        							| Add => Some (Int (i0 + i1))
        							| Sub => Some (Int (i0 - i1))
        							| Mul => Some (Int (i0 * i1))
        						end
      					| _ => None
							end
					| BBop bop t0 t1 => 
							match (eval r_fuel t0 env, eval r_fuel t1 env) with
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
							match (eval r_fuel t0 env) with 
								| Some (Bool b0) => Some (Bool (negb b0))
								| _ => None
							end
					| If t t0 t1 => 
							match (eval r_fuel t env) with 
								| Some (Bool true) => eval r_fuel t0 env
								| Some (Bool false) => eval r_fuel t1 env
								| _ => None
							end
					| Lambda t => Some (Closure t env)
					| Apply t1 t0 => 
							let param_val := eval r_fuel t0 env 
							in 
								match param_val with
									| Some v => 
											let f_closure := eval r_fuel t1 env 
												in
													match f_closure with 
														| Some (Closure body dec_env) => 
																let new_env := bind dec_env v
																in 
																	eval r_fuel body new_env
														| _ => None
													end
									| _ => None
								end
				end
	end.

(*-------------------------- Syntax of VM --------------------------*)

Inductive mterm : Type :=
  | PushVar     	: mvar -> mterm
  | PushClosure 	: mterm  -> mterm
  | PushVal   		: mvalue -> mterm
  | MAop      		: aop -> mterm
  | MBop					: bop -> mterm
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
with mvar : Type := MVar : nat -> mvar
with menv := MEmpty | MEnv : (mvalue * menv) -> menv.

Notation "A ; B" := (Concat A B) (at level 80, right associativity).

Inductive mstack := SEmpty | Stack : (mvalue * mstack) -> mstack.


(*-------------------------- States of the VM --------------------------*)
Inductive state : Type := 
  | State : mterm -> menv -> mstack -> state    (* Intermediate Step *)
  | Final : mvalue -> state									 	  (* Final Step *)
  | Error.																	    (* Computation ended with error *)

(*-------------------------- Utility Functions --------------------------*)
Definition mbind (env : menv) (v : mvalue) := MEnv (v, env).

Fixpoint mlookup (i : nat) (env : menv) : option mvalue :=  
	match env with
		| MEmpty => None
		| MEnv (e, r_env) => 
				if i =? 0 
					then Some(e) 
				else 
					mlookup (i - 1) (r_env)
	end.

(* Stack operations *)
Definition push (s : mstack) (v : mvalue) := Stack (v, s).

Definition pop (s : mstack) :=  match s with
  | SEmpty => (None, None)
  | Stack (v, s') => (Some v, Some s')
end.

(*-------------------------- VM Interpreter --------------------------*)
Definition step (s : state) : state := 
	match s with
		| State c env stack => 
				match c with 
					| Skip => 
							match (pop stack) with 
								| (None, _) => Error
								| (Some v, Some s1) => 
										match v with 
											| MRecord _ _ => Error
											| _ => Final v 
										end
								| (_, _) => Error
							end
					| Concat c1 c2 => 
							match c1 with 
								| PushVal (v) => State c2 env (push stack v)
								| PushVar (MVar x) => 
									 	match (mlookup x env) with
									 		| Some v => State c2 env (push stack v)
									 		| None => Error
									 	end
								| PushClosure c3 => 
										State c2 env (push stack (MClosure c3 env))
								| MAop aop => 
										match (pop stack) with 
											| (None, _) => Error 
											| (Some v1, Some s1) => 
													match (pop s1) with 
														| (None, _) => Error
														| (Some v2, Some s2) => 
																match v1, v2 with
																	| MInt z1, MInt z2 => 
																			match aop with 
																				| Add => State c2 env (push s2 (MInt (z1 + z2)))
																				| Sub => State c2 env (push s2 (MInt (z1 - z2)))
																				| Mul => State c2 env (push s2 (MInt (z1 * z2)))
																			end
																	| _, _ => Error
																end
														| (_, _) => Error
													end
											| (_, _) => Error
										end
								| MBop bop => 
										match (pop stack) with 
											| (None, _) => Error
											| (Some v1, Some s1) => 
													match (pop s1) with 
														| (None, _) => Error 
														| (Some v2, Some s2) => 
																match v1, v2 with 
																	| MInt z1, MInt z2 => 
																			match bop with 
																				| Less => 
																							State c2 env (push s2 (MBool (Z.ltb z1 z2)))
																				| Equal => 
																							State c2 env (push s2 (MBool (Z.eqb z1 z2)))
																				| Greater => 
																							State c2 env (push s2 (MBool (Z.gtb z1 z2)))
																				| _ => Error
																			end
																	| MBool b1, MBool b2 => 
																			match bop with
																				| And => State c2 env (push s2 (MBool (andb b1 b2)))
																				| Or => State c2 env (push s2 (MBool (orb b1 b2)))
																				| _ => Error
																			end
																	| _, _ => Error
																end
														| (_, _) => Error
														end 
												| (_, _) => Error
										end
								| MIf c3 c4 => 
										match (pop stack) with 
											| (None, _) => Error
											| (Some v, Some s1) => 
													match v with 
														| MBool b => 
																if b 
																	then 
																		(State (c3; c2) env s1)
																	else 
																		(State (c4; c2) env s1)
														| _ => Error
													end
											| (_, _) => Error
										end
								| MApply => 
										match (pop stack) with
											| (None, _) => Error
											| (Some v, Some s1) => 
													match (pop s1) with  
														| (None, _) => Error
														| (Some v1, Some s2) => 
																match v1 with 
																	| MClosure c' dec_env => 
																			State c' (mbind dec_env v) (push s2 (MRecord c2 env))
																	| _ => Error
																end
														| (_, _) => Error
													end
											| (_, _) => Error 
										end
								| Return => 
										match (pop stack) with 
											| (None, _) => Error
											| (Some v, Some s1) => 
													match (pop s1) with 
														| (None, _) => Error
														| (Some v1, Some s2) => 
																match v1 with 
																	| MRecord c' env' => State c' env' (push s2 v)
																	| _ => Error
																end
														| (_, _) => Error
													end
											| (_, _) => Error
										end
								| _ => Error
							end
					| c1 => (State (c1; Skip) env stack)
				end
		| Error => Error
		| _ => Error
	end.

(*-------------------------- Compilation Step --------------------------*)
Fixpoint compile (t: term) : option mterm :=
	match t with 
		|	EInt i => Some (PushVal (MInt i))
		| EBool b => Some (PushVal (MBool b))
		| Var x => Some (PushVar (MVar x))
		| Aop aop t0 t1 => 
				match (compile t0), (compile t1) with 
					| Some ct0, Some ct1 => Some (ct0;ct1; MAop aop)
					| _, None => None
					| None, _ => None
				end
		| BBop bop t0 t1 => 
				match (compile t0), (compile t1) with 
					| Some ct0, Some ct1 => Some (ct0;ct1; MBop bop)
					| _, None => None
					| None, _ => None
				end
		| Not t => None
		| If t t0 t1 => 
				match (compile t), (compile t0), (compile t1) with 
					| None, _, _ => None
					| _, None, _ => None
					| _, _, None => None
					| Some ct, Some ct0, Some ct1 => Some (ct; (MIf (ct0) (ct1)))
				end
		| Lambda t => 
				match (compile t) with 
					| Some ct => Some (PushClosure(ct; Return))
					| _ => None
				end
		| Apply t0 t1 => 
				match (compile t0), (compile t1) with 
					| Some ct0, Some ct1 => Some (ct0; ct1; MApply)
					| _, None => None
					| None, _ => None
				end
	end.	


(* State of limited execution *)
Inductive limState : Type :=
  | ExecutionOverflow : state -> limState
  | LState : state -> limState.

(* Limited execution of machine code *)
Fixpoint MEval (fuel : nat) (s : state) := 
	match fuel with
		| 0 => ExecutionOverflow s
		| S fuel' => match (step s) with
		  | Final f => LState(Final f)
		  | Error   => LState Error
		  | s => MEval (fuel') (s)
  end
end.


(*Compute eval 100 (Aop Add (EInt 5) (EInt 3)) Empty.*)

Definition term1 := (Aop Add (EInt 5) (EInt 3)).
(*Compute compile term1.*)

Definition mytest := 
	match (compile term1) with 
		| Some t => MEval 100 (State t MEmpty SEmpty)
		| _ => LState Error
	end.


Compute mytest.





