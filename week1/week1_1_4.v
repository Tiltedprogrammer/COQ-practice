(*Require Import PeanoNat Le Gt Minus Bool Lt.*)
Set Implicit Arguments.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Check true. 

Parameter PropVars : Set.

Hypothesis Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.

Check PropVars.

Inductive PropFormula : Set := 
                       | Var : PropVars -> PropFormula 
                       | Top : PropFormula 
                       | Bot : PropFormula 
                       | Neg : PropFormula -> PropFormula
                       | Conj : PropFormula -> PropFormula -> PropFormula
                       | Disj : PropFormula -> PropFormula -> PropFormula.

Check Var .

Definition Impl (phi : PropFormula) (psi : PropFormula) : PropFormula := Disj (Neg phi) (psi).

Definition Eqi (phi : PropFormula) (psi : PropFormula) : PropFormula := Disj (Conj phi psi) (Conj (Neg psi) (Neg phi)).


Notation "⊥" := Bot.
Notation "⊤" := Top.
Notation "¬ P" := (Neg P) (at level 51).
Infix "∧" := Conj (left associativity, at level 52).
Infix "∨" := Disj (left associativity, at level 53).
Infix "⇀" := Impl (right associativity, at level 54).
Infix "⇋" := Eqi (right associativity, at level 55).

Definition min a b : bool :=
           match a,b with
           | false , _  => false
           | _ , false  => false
           | true , true  => true end.


Definition max a b : bool :=
           match a , b with
           | true , _ => true
           | _ , true => true

           | false, false => false end.

Fixpoint Interpretation (phi : PropFormula) (v : PropVars -> bool) {struct phi} : bool := 
          match phi with
          | Var p => v p
          | Top => true
          | Bot => false
          | ¬ psi => (match (Interpretation psi v) with | true => false | _ => true end)
          | psi ∧ ksi => min (Interpretation psi v) (Interpretation ksi v)
          | psi ∨ ksi => max (Interpretation psi v) (Interpretation ksi v) end.

Definition Satisfies (A : PropFormula) v  := (Interpretation A v) = true.

Check Satisfies.
Definition Tautology A := forall v, Satisfies A v.
Check Tautology.

Definition DoubleTurnstile phi psi := forall v, (Satisfies phi v) -> (Satisfies psi v).

Check @DoubleTurnstile.

Definition LogEqi phi psi := (DoubleTurnstile phi psi) /\ (DoubleTurnstile psi phi).


(*Problem 1 (a)*)
Theorem DoubleTurnstileImplIffDoubleTurnstilePhiPsi : 
                        forall (phi : PropFormula)
                               (psi : PropFormula),
                        (DoubleTurnstile phi psi) <-> (Tautology (phi ⇀ psi)).
Proof. split.
    - intros H v. assert((Satisfies phi v) -> (Satisfies psi v)). apply H. unfold DoubleTurnstile in H.
                 unfold Impl.
                   unfold Satisfies.
                   simpl. unfold Satisfies in H0.
                   destruct (Interpretation phi v) eqn:e. rewrite -> H0. reflexivity. reflexivity. reflexivity.
                 -  intros. unfold Impl in H. unfold Tautology in H.
                    unfold DoubleTurnstile. intros.
                    assert (Satisfies (¬ phi ∨ psi) v). apply H. unfold Satisfies.
                    unfold Satisfies in H0, H1. simpl in H1. rewrite -> H0 in H1.
                    destruct (Interpretation psi v) eqn:e. reflexivity. simpl in H1. assumption.  Qed.


(*Problem 1 (b)*)
Theorem EqiLogEqi : forall (phi : PropFormula) (psi : PropFormula), (Tautology (phi ⇋ psi)) <-> (LogEqi phi psi).
Proof. intros. split. 
        -intros H. unfold LogEqi. unfold Tautology in H. split.
              + unfold DoubleTurnstile. intros v. assert (Satisfies (phi ⇋ psi) v). apply H. unfold Eqi in H0. unfold Satisfies. unfold Satisfies in H0. simpl in H0. intros. rewrite -> H1 in H0. destruct (Interpretation psi v) eqn:ipv.
                   * reflexivity.
                   *  simpl in H0. assumption.
              +   unfold DoubleTurnstile. intros v. assert (Satisfies (phi ⇋ psi) v). apply H. unfold Eqi in H0. unfold Satisfies. unfold Satisfies in H0. simpl in H0. intros. rewrite -> H1 in H0. destruct (Interpretation phi v) eqn:ipv.
                   * reflexivity.
                   * simpl in H0. assumption.
       - intros H. unfold Tautology. intros v. unfold LogEqi in H. destruct H. unfold Eqi. unfold Satisfies. simpl. unfold DoubleTurnstile in H, H0. assert (Satisfies phi v -> Satisfies psi v). apply H. assert (Satisfies psi v -> Satisfies phi v). apply H0. unfold Satisfies in H1,H2. destruct (Interpretation phi v) eqn:phiv.
             + rewrite -> H1. simpl. reflexivity. reflexivity.
             + destruct (Interpretation psi v) eqn:psiv. auto. auto. Qed. 
            

(*Problem 2 (a)*)

Lemma DoubleNegationEqiId : forall phi: PropFormula, LogEqi (Neg (Neg phi)) phi.
Proof. intros. unfold LogEqi. split. 
          - unfold DoubleTurnstile. intros. unfold Satisfies in H. unfold Satisfies. destruct (Interpretation phi v) eqn:phiv. reflexivity. simpl in H. rewrite -> phiv in H. assumption.
          - unfold DoubleTurnstile. intros. unfold Satisfies in H. unfold Satisfies. simpl. rewrite -> H.  reflexivity. Qed.

(*Problem 2 (b)*)
Lemma ExcludedMiddleTautology : forall phi: PropFormula, Tautology (phi ∨ ¬ phi).
Proof. intros. unfold Tautology. intros. unfold Satisfies. simpl. destruct (Interpretation phi v) eqn:phiv. auto. auto. Qed.

(*Problem 2 (c)*)
Lemma DistributivityConj : forall (phi : PropFormula) (psi : PropFormula) (eta : PropFormula), LogEqi (phi ∧ (psi ∨ eta)) ((phi ∧ psi) ∨ (phi ∧ eta)).
Proof. intros. unfold LogEqi. split. 
              - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct ((Interpretation phi v)) eqn:phiv. 
                  + destruct (Interpretation psi v) eqn:psiv.
                     * auto.
                     * auto.
                  + auto.
             - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct ((Interpretation phi v)) eqn:phiv. 
                  + destruct (Interpretation psi v) eqn:psiv.
                     * auto.
                     * auto.
                  + auto. Qed.


(*Problem 2 (d)*)
Lemma DistributivityDisj : forall (phi : PropFormula) (psi : PropFormula) (eta : PropFormula), LogEqi (phi ∨ (psi ∧ eta)) ((phi ∨ psi) ∧ (phi ∨ eta)).
Proof. intros. unfold LogEqi. split. 
              - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct ((Interpretation phi v)) eqn:phiv. 
                  + destruct (Interpretation psi v) eqn:psiv.
                     * auto.
                     * auto.
                  + destruct (Interpretation psi v) eqn:psiv.
                     * auto.
                     * auto. 
             - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct ((Interpretation phi v)) eqn:phiv. 
                  + destruct (Interpretation psi v) eqn:psiv.
                     * auto.
                     * auto.
                  + destruct (Interpretation psi v) eqn:psiv.
                    * auto.
                    * auto. Qed.

(*Problem 2 (e)*)
Lemma AbsorptionDisj : forall (phi : PropFormula) (psi : PropFormula), LogEqi (phi ∨ (phi ∧ psi))  phi.
Proof. intros. unfold LogEqi. split.
            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. destruct (Interpretation phi v) eqn:psiv.
                  + reflexivity.
                  +  simpl in H. assumption.
            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. simpl. rewrite -> H. auto. Qed.


(*Problem 2 (f)*)
Lemma AbsorptionConj : forall (phi : PropFormula) (psi : PropFormula), LogEqi (phi ∧ (phi ∨ psi))  phi.
Proof. intros. unfold LogEqi. split.
            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. destruct (Interpretation phi v) eqn:psiv.
                  + reflexivity.
                  +  simpl in H. assumption.
            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. simpl. rewrite -> H. auto. Qed.

(*Problem 2 (g)*)
Lemma DeMorganConj : forall (phi : PropFormula) (psi : PropFormula), LogEqi (Neg (phi ∧ psi)) ((Neg phi) ∨ (Neg psi)).
Proof. intros. unfold LogEqi. split.
            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. simpl. destruct (Interpretation phi v) eqn:phiv.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto.

            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. simpl. destruct (Interpretation phi v) eqn:phiv.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto. Qed.


(*Problem 2 (h)*)
Lemma DeMorganDisj : forall (phi : PropFormula) (psi : PropFormula), LogEqi (Neg (phi ∨ psi)) ((Neg phi) ∧ (Neg psi)).
Proof. intros. unfold LogEqi. split.
            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. simpl. destruct (Interpretation phi v) eqn:phiv.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto.

            - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl in H. simpl. destruct (Interpretation phi v) eqn:phiv.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto.
                  +  destruct (Interpretation psi v) eqn:psiv.
                        ** auto.
                        ** auto. Qed.

(*Problem 3 (a)*)
(*As one could see this is similar to contraposition wich should be tautology intuitively.*)
Lemma PropsContraposition : forall (p : PropVars) (q : PropVars), Tautology (Eqi ((Var p) ⇀ (Var q)) (¬(Var q) ⇀ ¬(Var p))).
Proof. intros. unfold Tautology. intros. unfold Satisfies. simpl. destruct (v p) eqn:vp.
                         + destruct (v q) eqn:vq. auto. auto.
                         + destruct (v q) eqn:vq. auto. auto. Qed.

Lemma PropsAlmosrContraposition : forall (p : PropVars) (q : PropVars) (r : PropVars), Tautology (Eqi ((Var p) ⇀ ((Var q) ⇀ (Var r))) (¬(Var r) ⇀ (¬(Var p) ⇀ ¬ (Var q)))).
Proof. intros. unfold Tautology. intros. unfold Satisfies. simpl. destruct (v p) eqn:vp.
                        + destruct (v q) eqn:vq. 
                            - destruct (v r) eqn:vr. auto. simpl. Abort. 
  (*We get false = true in the goal with the empty context for {p -> true, q -> true, r -> false}, however {p -> true, q -> true, r -> true} satisfies*)
                         

(* cannot into quantified v from H
Lemma PropsAlmosrContraposition : forall (p : PropVars) (q : PropVars) (r : PropVars), not (Tautology (Eqi ((Var p) ⇀ ((Var q) ⇀ (Var r))) (¬(Var r) ⇀ (¬(Var p) ⇀ ¬ (Var q))))).
Proof. intros. unfold not. unfold Tautology. intros.  unfold Satisfies in H. simpl in H. assert (Satisfies (Var p ⇀ Var q ⇀ Var r ⇋ ¬ Var r ⇀ ¬ Var p ⇀ ¬ Var q) v). unfold Satisfies. simpl. destruct (v p) eqn:vp.
                      
*)

(*Problem 4*)
(*¬(¬(p ∧ q) → ¬r)*)
(*NNF should contain only literals and conj/disj, i.e. negation should negate only props and not other formulas*)
(* ¬(¬(p ∧ q) → ¬r) ~(DeMorgan)~ ¬((¬p ∨ ¬q) → ¬r) ~(Impl)~ ¬((p ∧ q) ∨ ¬r) ~ (DeMorgan) ~ (¬p ∨ ¬q) ∧ r*)
(*As one could see the formula conforms to CNF and NNF constraints : (¬p ∨ ¬q) and r  are disjuncts, ∧ is conjunction*)

Lemma NNFandDNFProblem4 : forall (p : PropVars) (q : PropVars) (r : PropVars), LogEqi (¬(¬((Var p) ∧ (Var q)) ⇀ ¬ (Var r))) ((¬ (Var p) ∨ ¬(Var q)) ∧ (Var r)).
Proof. intros. unfold LogEqi. split.
          - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct (v p) eqn:vp.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto.
         - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct (v p) eqn:vp.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto. Qed.
         
(*CNF conjunction of disjuncts*)
(* ¬(¬(p ∧ q) → ¬r) ~(DeMorgan) ¬((¬p ∨ ¬q) → ¬r) ~(Impl) ¬((p ∧ q) ∨ ¬r) ~ (DeMorgan) (¬p ∨ ¬q) ∧ r*)
(*We have not proved syymetricity of ∧ and ∨ , but will use it here: from the previous step (¬p ∨ ¬q) ∧ r ~ (Symm)~ r ∧ (¬p ∨ ¬q) ~ (Distributivity)~ (r ∧ ¬p) ∨ (r ∧ ¬q), it is DNF*)

Lemma DNFProblem4 : forall (p : PropVars) (q : PropVars) (r : PropVars), LogEqi (¬(¬((Var p) ∧ (Var q)) ⇀ ¬ (Var r)))  (Disj ((Var r) ∧ ¬ (Var p)) ((Var r) ∧ ¬ (Var q))).
Proof. intros. unfold LogEqi. split.
          - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct (v p) eqn:vp.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto.
         - unfold DoubleTurnstile. intros. unfold Satisfies. unfold Satisfies in H. simpl. simpl in H. destruct (v p) eqn:vp.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto.
                           + destruct (v q) eqn:vq. 
                                  * destruct (v r) eqn:vr. auto. auto.
                                  * destruct (v r) eqn:vr.  auto. auto. Qed.


