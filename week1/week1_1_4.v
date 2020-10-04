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

Reserved Notation "Γ ⊢ A" (at level 80).
Require Import Coq.Lists.List.
Import ListNotations.


Inductive Disjunct : Set := 
                       | Empty : Disjunct
                       | VarD : nat -> Disjunct (*lets coun all the props*)
                       | NegVarD : nat -> Disjunct
                       | DisjD : Disjunct -> Disjunct -> Disjunct.


Compute app [1;2] [4;6].

Fixpoint Negative (d : Disjunct) : list nat :=
      match d with 
                | NegVarD p     => p :: []
                | DisjD phi psi => app (Negative phi) (Negative psi)
                | _             => [] end.

Fixpoint Positive (d : Disjunct) : list nat :=
      match d with 
                | VarD p     => p :: []
                | DisjD phi psi => app (Positive phi) (Positive psi)
                | _             => [] end.


Fixpoint Contains elem (ls : list nat) : bool :=
  match ls with 
          | [] => false 
          | x :: xs => if (Nat.eqb elem x) then true else Contains elem xs end.

Fixpoint MakeSet (ls : list nat) : list nat :=
  match ls with 
      | [] => []
      | x :: xs => if Contains x xs then MakeSet xs else x :: (MakeSet xs) end.

Compute MakeSet [2;3;4;2;3;1;4;5;6].

Compute Positive (DisjD (NegVarD 1) (VarD 2)).


Fixpoint remove elem (ls : list nat) : list nat := 
      match ls with
              | [] => []
              | x :: xs => if Nat.eqb elem x then remove elem xs else x :: remove elem xs end.

Compute Contains 12 (remove 12 (app [12] [1;2;3;1])).

Check option.

Fixpoint Contrars (l1 l2 : list nat) : option nat := 
      match l1 with
                 | [] => None
                 | x :: xs => if Contains x l2 then Some x else Contrars xs l2 end.

Compute Contrars [1;2;3] [4;5;1].


Check map.

Definition ReduceList (ls : list Disjunct) : option (Disjunct) :=
  let fix ReduceNonEmpty ls' {struct ls'} : Disjunct :=
      match ls' with 
           |   [x] => x
           | x :: xs => (DisjD x (ReduceNonEmpty xs))
           | _ => (VarD 1) end in
  match ls with 
        | [] => None
        | l => Some (ReduceNonEmpty l) end.

Compute (ReduceList [(VarD 1)]).
Compute (ReduceList [(VarD 1); (VarD 2) ; (VarD 3); (NegVarD 4)]). 

Definition Resolve (d1: Disjunct) (d2: Disjunct) : Disjunct :=
    let d1_positive := MakeSet (Positive d1) in
      let d1_negative := MakeSet (Negative d1) in
        let d2_positive := MakeSet (Positive d2) in
          let d2_negative := MakeSet (Negative d2) in
           match Contrars d1_positive d2_negative with
          | Some p => let d1_positive_removed := remove p d1_positive in
            let d2_negative_removed := remove p d2_negative in
             match d1_positive_removed with 
              | [] => match d2_negative_removed with
                | [] => let d1_negative_reduced := ReduceList (map (fun x => NegVarD x) d1_negative) in
                        let d2_positive_reduced := ReduceList (map (fun x => VarD x) d2_positive) in
                    match d1_negative_reduced, d2_positive_reduced with
                     | None , None => Empty
                     | Some l, None => l
                     | None, Some l => l
                     | Some l, Some r => DisjD l r end
 (*d2_negative*)| ls => let d2_negative_reduced := ReduceList (map (fun x => NegVarD x) ls) in
                        let d1_negative_reduced := ReduceList (map (fun x => NegVarD x) d1_negative) in
                        let d2_positive_reduced := ReduceList (map (fun x => VarD x) d2_positive) in
                    match d2_negative_reduced, d1_negative_reduced,d2_positive_reduced with
                     | None, None, None => Empty
                     | Some v, None, None => v
                     | None, Some v, None => v
                     | None, None, Some v => v
                     | None, Some m, Some r => DisjD m r
                     | Some l, None, Some r => DisjD l r
                     | Some l, Some m, None => DisjD l m
                     | Some l, Some m, Some r => DisjD l (DisjD m r) end end
(*d1_positive*)| ls => match d2_negative_removed with
                | [] => let d1_positive_reduced := ReduceList (map (fun x => VarD x) ls) in
                        let d1_negative_reduced := ReduceList (map (fun x => NegVarD x) d1_negative) in
                        let d2_positive_reduced := ReduceList (map (fun x => VarD x) d2_positive) in
                    match d1_positive_reduced, d1_negative_reduced, d2_positive_reduced with
                     | None, None, None => Empty
                     | None, None, Some v => v
                     | Some v, None, None => v
                     | None, Some v, None => v 
                     | None, Some mv, Some rv => DisjD mv rv
                     | Some lv, None, Some rv => DisjD lv rv
                     | Some lv, Some mv, None => DisjD lv mv
                     | Some lv, Some mv, Some rv => DisjD lv (DisjD mv rv) end     
                | l => 
                        let d1_positive_reduced := ReduceList (map (fun x => VarD x) ls) in
                        let d2_negative_reduced := ReduceList (map (fun x => NegVarD x) l) in
                        let d1_negative_reduced := ReduceList (map (fun x => NegVarD x) d1_negative) in
                        let d2_positive_reduced := ReduceList (map (fun x => VarD x) d2_positive) in
                    match d1_positive_reduced,d2_negative_reduced, d1_negative_reduced,d2_positive_reduced with
                     | None,None, None, None => Empty
                     | Some v, None, None, None => v
                     | None, Some v, None, None => v
                     | None, None, Some v, None => v
                     | None, None, None, Some v => v
                     | Some lv, Some rv, None, None => DisjD lv rv
                     | Some lv, None, Some rv, None => DisjD lv rv
                     | Some lv, None , None , Some rv => DisjD lv rv
                     | None, Some lv, Some rv , None => DisjD lv rv
                     | None, None, Some lv, Some rv => DisjD lv rv
                     | None, Some lv, None, Some rv => DisjD lv rv 
                     | Some lv, Some mv, Some rv, None => DisjD mv (DisjD lv mv)
                     | None, Some lv, Some mv, Some rv => DisjD mv (DisjD lv mv)
                     | Some lv, None, Some mv, Some rv => DisjD mv (DisjD lv mv)
                     | Some lv, Some mv, None, Some rv => DisjD mv (DisjD lv mv)
                     | Some lv, Some mv, Some rv, Some qv => DisjD qv (DisjD mv (DisjD lv mv)) end end end   

          | None => match Contrars d1_negative d2_positive with
           | Some p => let d1_negative_removed := remove p d1_negative in
                       let d2_positive_removed := remove p d2_positive in
             match d1_negative_removed with 
              | [] => match d2_positive_removed with
                | [] => let d1_positive_reduced := ReduceList (map (fun x => VarD x) d1_positive) in
                        let d2_negative_reduced := ReduceList (map (fun x => NegVarD x) d2_negative) in
                    match d1_positive_reduced, d2_negative_reduced with
                     | None , None => Empty
                     | Some l, None => l
                     | None, Some l => l
                     | Some l, Some r => DisjD l r end
(*d2_positive*)| ls =>  let d2_negative_reduced := ReduceList (map (fun x => NegVarD x) d2_negative) in
                        let d1_positive_reduced := ReduceList (map (fun x => VarD x) d1_positive) in
                        let d2_positive_reduced := ReduceList (map (fun x => VarD x) ls) in
                    match d2_negative_reduced, d1_positive_reduced,d2_positive_reduced with
                     | None, None, None => Empty
                     | Some v, None , None => v
                     | None, Some v, None => v
                     | None, None, Some v => v
                     | None, Some m, Some r => DisjD m r
                     | Some l, None, Some r => DisjD l r
                     | Some l, Some m, None => DisjD l m
                     | Some l, Some m, Some r => DisjD l (DisjD m r) end end
(*d1_negative*)| ls => match d2_positive_removed with
                | [] => let d1_positive_reduced := ReduceList (map (fun x => VarD x) d1_positive) in
                        let d1_negative_reduced := ReduceList (map (fun x => NegVarD x) ls) in
                        let d2_negative_reduced := ReduceList (map (fun x => NegVarD x) d2_negative) in
                    match d1_positive_reduced, d1_negative_reduced, d2_negative_reduced with
                     | None, None, None => Empty
                     | None, None, Some v => v
                     | Some v, None, None => v
                     | None, Some v, None => v 
                     | None, Some mv, Some rv => DisjD mv rv
                     | Some lv, None, Some rv => DisjD lv rv
                     | Some lv, Some mv, None => DisjD lv mv
                     | Some lv, Some mv, Some rv => DisjD lv (DisjD mv rv) end     
                | l => 
                        let d1_positive_reduced := ReduceList (map (fun x => VarD x) d1_positive) in
                        let d2_negative_reduced := ReduceList (map (fun x => NegVarD x) d2_negative) in
                        let d1_negative_reduced := ReduceList (map (fun x => NegVarD x) ls) in
                        let d2_positive_reduced := ReduceList (map (fun x => VarD x) l) in
                    match d1_positive_reduced,d2_negative_reduced, d1_negative_reduced,d2_positive_reduced with
                     | None,None, None, None => Empty
                     | Some v, None, None, None => v
                     | None, Some v, None, None => v
                     | None, None, Some v, None => v
                     | None, None, None, Some v => v
                     | Some lv, Some rv, None, None => DisjD lv rv
                     | Some lv, None, Some rv, None => DisjD lv rv
                     | Some lv, None , None , Some rv => DisjD lv rv
                     | None, Some lv, Some rv , None => DisjD lv rv
                     | None, None, Some lv, Some rv => DisjD lv rv
                     | None, Some lv, None, Some rv => DisjD lv rv 
                     | Some lv, Some mv, Some rv, None => DisjD mv (DisjD lv mv)
                     | None, Some lv, Some mv, Some rv => DisjD mv (DisjD lv mv)
                     | Some lv, None, Some mv, Some rv => DisjD mv (DisjD lv mv)
                     | Some lv, Some mv, None, Some rv => DisjD mv (DisjD lv mv)
                     | Some lv, Some mv, Some rv, Some qv => DisjD qv (DisjD mv (DisjD lv mv)) end end end   

(*no contrars*)| None => d1 end end.
     
Compute (if false then 1 else 2).

Compute Resolve (DisjD (VarD 1) (VarD 2)) (NegVarD 1).

     
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).


Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.


Compute In 1 (app [2] [1;3;4]).
Lemma oneinarray : In 1 [1;3;4].
Proof. unfold In. left. reflexivity. Qed.

Check In.

Lemma my_lemma : In (DisjD (VarD 1) (NegVarD 1)) [DisjD (VarD 1) (NegVarD 1); VarD 1].
Proof. unfold In. left. reflexivity.

Require Import Coq.Arith.PeanoNat.
(*
Lemma DisjEq : forall (x y : Disjunct), {x = y}+{x <> y}.
induction x. destruct y. left. auto. right. discriminate. (right;discriminate). right. discriminate. intros. destruct y. right. discriminate.
    - destruct Nat.eq_dec with (n := n) (m := n0). left. auto. right. injection. intros. contradiction.
    - right. discriminate.
    - right. discriminate.
    - intros. destruct y. right. discriminate. right. discriminate.
       +  destruct Nat.eq_dec with (n := n) (m := n0). left. auto. right. injection. intros. contradiction.
       +  right. discriminate.
    - intros. destruct (IHx1 y). destruct (IHx2 y).
                  + left. rewrite -> e. rewrite -> e0. destruct y.
     assumption|]|];
  right;injection;intros;contradiction).
 - destruct Nat.eq_dec with (n := n) (m := n0).
            + f_equal. auto.
            + 
 
 destruct (Varseq_dec p p0).
   left;f_equal;assumption.
   right;injection;intro;contradiction.
 left;reflexivity.
Qed.
*)

Inductive ResolveCalculus : list Disjunct -> Disjunct -> Prop :=
| Nax   : forall Γ A  ,    In A Γ               -> Γ ⊢ A
| ResolventA : forall Γ A B, Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ (Resolve A B)
| ResolventB   : forall Γ A B , In A Γ -> In B Γ -> Γ ⊢ (Resolve A B)
where "Γ ⊢ A" := (ResolveCalculus Γ A).

Lemma lemma10 : ResolveCalculus [VarD 1; DisjD (NegVarD 1) (DisjD (NegVarD 2) (VarD 3)); DisjD (VarD 2) (NegVarD 4); VarD 4; DisjD (NegVarD 5) (NegVarD 3); VarD 5] Empty.
Proof. unfold ResolveCalculus. 
                                            

