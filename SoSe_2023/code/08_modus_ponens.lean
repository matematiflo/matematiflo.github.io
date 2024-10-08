
/- # ***Modus ponens*** -/

/- Let us use tactic mode to write a proof of the rule of deductive reasoning known as *modus ponens*, which says that if we have a proof of proposition `P` and a proof of the implication `P → Q`, then we have a proof of the proposition `Q`. -/

def MP {P Q : Prop} (hP : P) (hPQ : P → Q) : Q :=
begin
  apply hPQ,
  exact hP,
end

/- The proof we give can be understood as follows. First, let us make it clear that `P` and `Q` are propositions, that we have a proof of `P` and of `P → Q`, and that our goal is to prove `Q`.

Since by assumption we have a proof of the implication `P → Q`, it suffices to prove `P`. This is what the `apply` tactic enables us to do. More precisely, the term `hPQ`, being of type `P → Q`, is a function from `P` to `Q`, so it sends a term of type `P` (i.e. a proof a `P`) to a term of type `Q`, i.e. a proof of `Q`.

Now, after the `apply` tactic, the goal is changed to `P`. And since, again by assumption, we have a proof of `P`, we can close the goal using the `exact` tactic.

Alternately, we can write the proof using just the `exact` tactic, because `hPQ hP` is the result of applying the function `hPQ : P → Q` to the term `hP`, which is of type `P`, so it is a term of type `Q`. -/

def MP_bis {P Q : Prop} (hP : P) (hPQ : P → Q) : Q :=
begin
  exact hPQ hP,
end

/- And in term mode, `MP` is defined as follows. -/

def MP_ter {P Q : Prop} (hP : P) (hPQ : P → Q) : Q := hPQ hP

/- In this example, we see three approaches to definitions in *Lean*:

* A concise term mode definition (`MP_ter`).
* A tactic mode definition that just adds the word `exact` in front of the term mode definition (`MP_bis`).
* A longer tactic mode definition, `MP`, that uses the `apply` tactic to change the goal before closing it.

The longer our proofs become, the more it becomes necessary to use the third approach (tactic mode). In that approach, *we work on the goal to reduce it to the assumptions*, and we close the reduced goal with the `exact` tactic.

We now check that `MP` is indeed a function that, in the presence of Propositions `P` and `Q`, sends a proof of the propositions `P` and `P → Q` to a proof of `Q`. -/

#check @MP

/- Here we use the `@` because `MP` has implicit arguments (namely `P` and `Q`). The result of `#check @MP` then looks as follows.

MP : ∀ {P Q : Prop}, P → (P → Q) → Q

It is instructive to check that the three definitions we have given are identical. -/

-- #print MP
-- #print MP_bis
-- #print MP_ter

/- Next, by using the command `variables`, we add to our context the Propositions `P` and `Q`, as well as a proof of `P` and a proof of the implication `P → Q`.  This is just for commodity here. -/

variables {P Q : Prop} (hP : P) (hPQ : P → Q)

/- And now, using the function MP and the variables `hP` and `hPQ`, we can give a proof of Proposition `Q`: we simply apply the *modus ponens* function to the proofs of the propositions `P` and `P → Q`. Note that `proof_of_Q` is a term of type `Q` and that we are *defining* it. -/

def proof_of_Q : Q := MP hP hPQ

/- Let us check that the term MP hP hPQ is indeed of type `Q`, i.e. that it is a proof of the Proposition `Q`. -/

#check MP hP hPQ

/- Alternately, we can write the following: -/

#check @MP P Q hP hPQ

/- The two terms `MP hP hPQ` and `@MP P Q hP hPQ` are in fact identical, but in the second notation we include the *implicit variables* `P` and `Q`. These implicit variables were declared with curly brackets `{ }` (see the definition of `MP`), as opposed to `hP` and `hPQ`, which were defined using round brackets `( )`. -/

/- We now give the tactic mode version of our proof of `Q`, using only the `exact` tactic. -/

def proof_of_Q_bis (hP : P) (hPQ : P → Q) : Q :=
begin
  exact MP hP hPQ,
end

/- Note that here, in order to use the variables `hP` and `hPQ` *in tactic mode*, we need to include them in the definition. However, we can check that the proof terms of `proof_of_Q` and `proof_of_Q_bis` are identical. -/

-- #print proof_of_Q
-- #print proof_of_Q_bis

/- To conclude, we give an alternate formulation for the definition of the *modus ponens*, where the variables `hP : P` and `hPQ : P → Q` do not appear explicitly, making the definition more compact. The tactic proof, however, is longer, as we must now introduce the variables ourselves, using the `intro` tactic. -/

def MP_no_var {P Q : Prop}: P → (P → Q) → Q :=
begin
  intro hP,
  intro hPQ,
  apply hPQ,
  exact hP,
end

/- Equivalently, we can write `P ∧ (P → Q) → Q`, instead of `P → (P → Q) → Q`. The symbol `∧` is read *and* and can be obtained by typing in the command `\and`.

In that case, the proof is even longer, and we wust apply the `cases` tactic in order to replace the hypothesis `h : P ∧ (P → Q)` by the two hypotheses `hP : P` and `hPQ : (P → Q)`.

The names `h` and `hPQ` are chosen arbitrarily. If we simply write `cases h` instead of `cases h with hP hPQ`, *Lean* will assign names automatically. -/

def MP_no_var_bis {P Q : Prop}: P ∧ (P → Q) → Q :=
begin
  intro h,
  cases h with hP hPQ,
  apply hPQ,
  exact hP,
end

/- It is instructive to see that the proof term corresponding to `MP_no_var` is quite simple (the `λ` term means that we are defining a function), while the one corresponding to `MP_no_var_bis` is more involved (because of the `cases` tactic). -/

-- #print MP_no_var
-- #print MP_no_var_bis

/-
---
-/
