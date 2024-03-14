<center>
<h1>LCI Project Report</h1>
<h6> Giulio Paparelli </h6>
</center>
# Formal Definition
## Syntax
We start by defining the formal syntax of our extension of untyped Lambda Calculus, which we call *Lambda+*.
The syntax is inspired from the one on Leroy's slides and *HOFL* (Higher Order Functional Language) seen in the course Principles for Software Composition
$$
\begin{align}
t ::=\ &x\ |\ n\ |\ b\  \\
& |\ \text{aop}(t_0, t_1)\ |\ \text{bop}(t_0, t_1)\ |\ \text{not}(t) \\
& |\ \text{if}\ t\ \text{then}\ t_0\ \text{else}\ t_1 \\ 
& |\ \lambda t\ |\ t_1\ t_0
\end{align}
$$
where:
- $x \in Var$
- $n$ are integers
- $b$ are booleans
- $\text{aop} \in \{+, -,\times\}$
- $\text{bop}\in \{\land, \lor, =, \neq, >, <\}$ 

De Bruijn indices are used to represent variable bindings.
Instead of using variable names, De Bruijn indices encode the information about the scope of a variable by representing it as a number indicating how many lambdas must be traversed to reach its binding occurrence.

Consider the following example: 
$$(\lambda f.\lambda x.\lambda y.f\ x\ y) \equiv λ(λ(λ.2 1 0))$$
- $\lambda f$: $f$ is not bound by any enclosing lambda, so it's represented by index 0.
- $λx$: $x$ is bound by the enclosing $\lambda f$ abstraction, so it's represented by index $0$.
- $λy$: $y$ is bound by the enclosing $\lambda x$ abstraction, and $x$ is bound by the enclosing $\lambda f$ abstraction. So $y$ is represented by index $1$, and $x$ is represented by index $0$.

Therefore the set $Var$ is a set of De Bruijn indices. 

An environment $\sigma$ is used to store the bindings and it is defined as a sequence of values.
The value associated with the De Bruijn index $j$ will be $\rho[j]$.
The admissible values of Lambda+ are integers, booleans, and closures. 
## Type System
The above syntax allows *pre-terms*, terms that do not have a valid semantic.
Consider $t = \text{if}\ 3\ \text{then}\ 1\ \text{else}\ 2$. It is clear that $t$ has not a valid semantic as the guard of the `if` command has to be evaluated in a boolean. 

There is the need to introduce a **type system** to distinguish pre-terms from terms. 
Let's define the types of our values as follows
$$\tau = int\ |\ bool\ |\ \tau_0 \rightarrow \tau_1 $$
and then we denote with $\mathcal{T}$ the set of all possible types that can be made, e.g., $\mathcal{T} = \{\text{integer},\ \text{boolean}, \text{integer}\rightarrow\text{integer}, \text{integer}\rightarrow\text{boolean},\dots\}$ 

Then we assume that the variables are typed and that we have a *typing context* $\Gamma$:
- $Var = \{Var_\tau\}_{\tau\in \mathcal{T}}$
- $\Gamma$ is a list or set of variable-type pairs. Each pair associates a variable with its type

The type system, a set of inference rules using structural induction of the Lambda+ syntax, assigns to a pre-term a type, if possible. 
We use the type system to make type judgments, such as 
$$t : \tau \iff \text{t has type}\ \tau$$
A pre-term $t$ is **well-formed** if $\exists \tau\in \mathcal{T}. t : \tau$.
In other words: if we can assign a type to a pre-term $t$ than $t$ is well-formed.

The type system is made of the following inference rules: 
![[Screenshot from 2024-03-06 10-53-04.png | center | 600]]

The above type system will be "embedded" in the following sections.
## Semantics
### Small-Step Semantics
Now we define the small-step semantics of **well-formed** Lambda+ terms. To simplify the notation we represent with $\mathbb{T}$ the set of all the possible well-formed terms. 
We consider a structural operational semantics, i.e. specifying the execution recursively on syntax, in a machine-independent way. 

To help us determine the semantic of a term we define a **store** function $\sigma:Var\rightarrow \mathbb{N}\ \cup\ \mathbb{B}$, and with $\mathbb{M}$ we represent the set of all possible stores $\sigma$.
We also define a function $\text{bind}$, that adds (on top) to the current environment (store) a new value. 
Lambda calculus has no side effects, this is purely to make things easier in the actual implementation of the language.

A program written in Lambda+ that terminates returns a value $v \in V= \{int, bool, closure(t, \rho)\}$.
Since we will define a **bounded interpreter** with a fuel parameter that is decreased with each step we also have to consider the case that the fuel reaches $0$ before the program has terminated. 
We then define the set of the possible values returned by a Lambda+ program as
$$\bar{V} = V\ \cup \perp$$
where $\perp$ is called **bottom**, the value of non-terminating programs (as diverging programs that never terminates). 
Abusing the notation, we also use $\perp$ as a value of undefined variables. 

We represent intermediate states of the computation as pairs $\langle t, \sigma\rangle \in \mathbb{T}\times\mathbb{M}$.
Then we define a transition system $(S, \rightarrow)$  where the first is a set of states and the second is a transition system, where the transitions are of the form 
$$\langle t, \sigma\rangle \rightarrow \langle t',\sigma'\rangle$$

Mind that we distinguish between the syntactic operations and their actual semantic operations using an over line: 
- $\text{aop}$ is syntax
- $\overline{\text{aop}}$ is semantic

**The small-step semantics of Lambda+ is defined by the following inference rules:** 
![[Pasted image 20240306155136.png | center | 560]]
**Note:** For brevity not all the rules have been listed: 
- The rules above are under the assumption that the program terminates and that every variable is always defined in $\sigma$. In reality there will be rules to cover the scenario in which a part of the program diverge or a lookup error, giving as result $\perp$ 
- The rules for boolean expressions are basically identical to the one for arithmetic expression, hence are not shown
### Big-Step Semantics
To define the big-step semantics we build upon the small-step semantics. 
A big-step computation is denoted with $\longrightarrow$ instead that the $\rightarrow$ used for the small-step.

**The big-step semantics of Lambda+ is defined by the following inference rules:** 
![[Pasted image 20240307094654.png | center | 560]]
**Note:** For brevity not all the rules have been listed: 
- Some rules (e.g., the rule for the lambda abstraction) remain the same and not showed
- The rules above are under the assumption that the program terminates, i.e., we have enough fuel. In reality there will be rules to cover the scenario in which a part of the program diverge, giving as result $\perp$ 
- The rules for boolean expressions are basically identical to the one for arithmetic expression, hence are not shown
### Properties of the Semantics
#### Determinism
Is it true that two different "computations", on the same term and environment, always produce the same value?

We can express this properties in symbols: 
$$P(t) = \forall \sigma\in \mathbb{M}. \forall v, v' \in V. \langle t, \sigma\rangle \longrightarrow v \land \langle t,\sigma\rangle\longrightarrow v' \implies v = v'$$
And we ask ourselves if is it true that $\forall t . P(t)$. 

Assuming that the term is not diverging (e.g., it can be computed in a finite fuel) we could provide a formal proof using the Rule Induction Principle.
#### Termination
Is it true that every term terminates? This is immediately not true as we can define a term that always diverge, no matter the amount of fuel we provide. 
The lambda expression
$$(\lambda x.x\ x)(\lambda x. x\ x)$$
is the infinitely self applying function that never terminates, and it can be defined in Lambda+. 
# Definitional Interpreter 
We can represent the provided definitional interpreter as a function, in a way that resemble what we would do for defining denotational semantics. 

We introduce the function $[[\cdot]]_I: (\mathbb{Z}, \mathbb{M}, \mathbb{T}) \rightarrow (V \cup \{\perp\})$ as the *interpreter function*, where: 
- the first argument is the remaining fuel
- the second argument is the current store
- the third argument is the term currently being interpreted

The interpreter function the mathematical representation of the `eval` function defined in the attached source code, and it is defined as follows: 
$$
\begin{align}
& [[(0,\ \_,\ \_)]]_I\ =\ \perp \\
& [[(n+1,\ \sigma,\ x)]]_I\ =\ \sigma(x) \\
& [[(n+1,\ \sigma,\ m)]]_I\ =\ m \\
& [[(n+1,\ \sigma,\ b)]]_I\ =\ b \\
& [[(n+1,\ \sigma,\ t_0\ \text{aop}\ t_1)]]_I\ =\  \begin{cases}
m_0\ \overline{\text{aop}}\ m_1\ \text{if}\ [[(n,\ \sigma,\ t_0)]]_I = m_0 \in \mathbb{Z}\ \land [[(n,\ \sigma,\ t_1)]]_I = m_1 \in \mathbb{Z} \\ \perp\ \text{otherwise}
\end{cases}\\
& [[(n+1,\ \sigma,\ t_0\ \text{bop}\ t_1)]]_I\ =\  \begin{cases}
b_0\ \overline{\text{bop}}\ b_1\ \text{if}\ [[(n,\ \sigma,\ t_0)]]_I = b_0 \in \mathbb{B}\ \land [[(n,\ \sigma,\ t_1)]]_I = b_1 \in \mathbb{B} \\ \perp\ \text{otherwise}
\end{cases}\\
& [[(n+1,\ \sigma,\ \text{not}\ t)]]_I\ =\  \begin{cases}
\lnot b\ \text{if}\ [[(n,\ \sigma,\ t)]]_I = b \in \mathbb{B} \\ \perp\ \text{otherwise}
\end{cases}\\
& [[(n+1,\ \sigma,\ \text{if}\ t\ \text{then}\ t_0\ \text{else}\ t_1]]_I\ =\  \begin{cases}
	[[(n, \sigma, t_0)]]_I\ \text{if}\ [[(n,\ \sigma,\ t)]]_I = true \\
	[[(n, \sigma, t_1)]]_I\ \text{if}\ [[(n,\ \sigma,\ t)]]_I = false \\
	\perp \ \text{otherwise}
\end{cases}\\
& [[(n+1,\ \sigma,\ \lambda t)]]_I\ =\ closure(t, \sigma) \\ 
& [[(n+1,\ \sigma,\ t_0\ t_1)]]_I\ =\  \begin{cases}
	[[(n, \sigma', t)]]_I\ \text{if}\ [[(n,\ \sigma,\ t_0)]] = clsr(t, \sigma'') \land [[(n, \sigma, t_1)]]_I\ =\ v \land\ \sigma' = \text{bind}(\sigma'', v)  \\
	\perp \ \text{otherwise}
\end{cases}\\
\end{align}
$$
## Soundness
Now we want to prove that the interpreter is **sound:**
$$\forall n, t, v, \sigma. ([[(n, \sigma, t)]] = v \implies \langle t, \sigma\rangle\longrightarrow v)$$
We prove that statement by induction on $t$. 
**The base cases, where $t$ is either a variable, an integer or a boolean, are immediate to see.** 

Let's now consider (two of the) more complex cases. 
**If Than Else:**
$$\text{if}\ t\ \text{then}\ t_0\ \text{else}\ t_1$$
**Note:** we consider only the case where $t$ evaluates to $true$, as the other case is analogous.

We want to prove that 
$$\forall n, t, t_0, t_1 v, \sigma. ([[(n, \sigma, \text{if}\ t\ \text{then}\ t_0\ \text{else}\ t_1)]] = v \implies \langle \text{if}\ t\ \text{then}\ t_0\ \text{else}\ t_1, \sigma\rangle\longrightarrow v)$$

We can use the following inductive hypothesis: 
1) $\forall n, t, v, \sigma. ([[(n, \sigma, t)]] = true \implies \langle t, \sigma\rangle\longrightarrow true)$
2)  $\forall n, t_0, v, \sigma. ([[(n, \sigma, t_0)]] = v \implies \langle t_0, \sigma\rangle\longrightarrow v)$

Thanks to the first inductive hypothesis we only have to prove that
$$\forall n, t_0, v, \sigma. ([[(n, \sigma, t_0)]] = v \implies \langle t_0, \sigma\rangle\longrightarrow v)$$
which is true by the second inductive hypothesis.

**Application of a function:**
We want to prove that: 
$$\forall n, t_0, t_1, \overline{v}, \sigma. ([[(n, \sigma, t_0\ t_1)]] = v \implies \langle t_0\ t_1, \sigma\rangle\longrightarrow \overline{v})$$
We can use the following inductive hypothesis: 
1) $\forall n, t_0, closure(t, \sigma''), \sigma. ([[(n, \sigma, t_0)]] = closure(t, \sigma'') \implies \langle t_0, \sigma\rangle\longrightarrow closure(t, \sigma''))$ 
2) $\forall n, t_1, v, \sigma. ([[(n, \sigma, t_1)]] = v \implies \langle t_1, \sigma\rangle\longrightarrow v)$  
3) $\forall n, t, v, \sigma'. ([[(n, \sigma', t)]] = v \implies \langle t, \sigma'\rangle\longrightarrow v)$, where $\sigma' = \text{bind}(v, \sigma'')$ 

Using the hypothesis of the application: 
- *a:* $[[(n,\ \sigma,\ t_0)]] = closure(t, \sigma'')$ 
- *b:* $[[(n, \sigma, t_1)]]\ =\ v$
- *c:* $\sigma' = \text{bind}(\sigma'', v)$

We proceed by the definition of $[[\cdot]]$ and we get that: $$[[(n, \sigma, t_0\ t_1)]] = [[(n, \sigma', t_0)]]$$
And we want to prove that:
$$\forall n, t, \overline{v}, \sigma'. ([[(n, \sigma', t)]] = \overline{v} \implies \langle t, \sigma'\rangle\longrightarrow \overline{v})$$
Which is true by considering the three inductive hypothesis 1), 2) and 3) that makes applicable the hypothesis of the inference rule of the application.
## Completeness
Completeness is defined as follows: 
$$\forall t, \sigma, v. \exists n. \langle t, \sigma\rangle \longrightarrow v \implies [[(n, \sigma, t)]] =v$$
The proof is omitted. 
# Compilation and Virtual Machine 
To compile and execute our code in the virtual machine we need to: 
1) define the virtual machine that execute the code. 
	- define the syntax of the language of the VM
	- define the semantics of that language
	- define an interpreter for that language
2) define a compilation step for our code that transforms a program written in Lambda+ in the code that the VM executes, similar to the transformation of Java to Bytecode

Continuing the similarities with Java, our virtual machine will be a stack-based machine, its computation will be performed on an operand stack, in a way that resembles the JVM. 
To keep things manageable the stack is used as an operand stack and as a call stack, but in our case the "activation records" only stores the return address and the environment. 
## Virtual Machine
We start by defining the syntax for the language of our virtual machine:
$$
\begin{align}
C : =\ & \text{PVar}(Var)\ |\ \text{PClosure}(C)\ |\ \text{PValue}(Val)\ \\ & |\ \text{Apply}\ |\ \text{Return}\ |\ \text{If}(C_0,C_1)\ | \text{AOP}\ |\ \text{BOP}\ |\ C;C\ |\ \text{Skip} \\ \\
Val :=\  & \text{true}\ |\ \text{false}\ |\ n\in \mathbb{z}\ |\ \text{Closure}(C, \sigma)\ |\ \text{Record}(C, \sigma) \\ 

OP :=\ &\ \text{Add}\ |\ \text{Sub} \ |\ \text{Mul} \\ \
BOP :=\ &\ \text{And}\ |\ \text{Or}\ |\ \text{Not}\ |\ \text{Eq}\ |\ \text{Less}\ |\ \text{Greater}
\end{align}
$$

Now we have to define the semantics of the language. 
We provide a small-step semantic where the intermediate step is the triple $\langle c, \sigma, \gamma\rangle$, where: 
- $c$ is the command
- $\sigma$ is the environment
- $\gamma$ is the operand/call stack

**Notation:** 
1) A program is seen as a sequence of commands. We decide that the last command before the termination will always be a $\text{Skip}$. This is to make easier to identify the end of a program: a program has reached its end when it is no more a sequence of commands, and the remaining command is a $\text{Skip}$. We will present an inference rule for enforcing every non-skip command into a sequence where the last command $\text{Skip}$  
2) We represent the final state of the VM as a single value. 
3) We use $v :: \sigma$ to represent the insertion/presence of $v$ on top of the stack. 
4) We use the bottom symbol $\perp$ for representing errors. 

**The small-step semantics of the VM is defined by the following inference rules:** 
![[IMG_0441.png | center | 700]]

**Note:** For brevity not all the rules have been listed: 
- The rules for $\text{BOP}$ are basically identical to the one for arithmetic operations, hence are not shown
- As we did for Lambda+ we here presents only the rules for "correct" programs (rules that do not give $\perp$)
- The $\langle \text{Skip};C, \sigma,\gamma\rangle$ is not listed as the semantics of a "non-final" is trivial
## Compilation of Lambda+
We now present the compilation step that transforms a program written in *Lambda+* to the language of the virtual machine.

We proceed in a similar way of the "interpretation function" and define the "compilation function" as a function that goes from well-formed Lambda+ terms to $C$: $$[[\cdot]]_C : \mathbb{T}\rightarrow (C \cup \{\perp\})$$
The function $[[\cdot]]_C$ is defined by cases as follows: 
$$
\begin{align}
&[[v]]_C = \text{PVal(v)}\\ \\
&[[x]]_C = 
	\begin{cases}
		\text{PVar(x)}\ \text{if}\ x\in Var \\ 
		\perp \text{otherwise}
	\end{cases} \\ \\
&[[t_0\ \text{aop}\ t_1]]_C = 
	\begin{cases}
		([[t_0]]_C; [[t_1]]_C); \text{AOP}\ \text{if}\ [t_0]]_C, [[t_1]]_C \neq \perp \\
		\perp\ \text{otherwise}
	\end{cases}\\ \\
&[[\text{if}\ t\ \text{then}\ t_0\ \text{else}\ t_1]]_C = 
	\begin{cases}
		[[t]]_C; \text{If}([[t_0]]_C, [[t_1]]_C)\ \text{if}\ [[t]]_C,[[t_0]]_C,[[t_1]]_C \neq \perp  \\ 
		\perp \text{otherwise}
	\end{cases} \\ \\
&[[\lambda t]]_C = 
	\begin{cases}
		(\text{PClosure([$[t]]_C$; Return})\ \text{if}\ [t]]_C \neq \perp \\
		\perp\ \text{otherwise}
	\end{cases}\\ \\
&[[t_0\ t_1]]_C = 
	\begin{cases}
		(([[t_0]]_C; [[t_1]]_C);\text{Apply})\ \text{if}\ [[t_0]]_C, [[t_1]]_C \neq \perp \\
		\perp \text{otherwise}
	\end{cases}
\end{align}
$$
# Project Delivery
The file `lambda_plus.v` implements all content in the following report.