Check true.
Require Import Coq.Lists.ListSet Coq.Arith.PeanoNat.
Set Implicit Arguments.

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

Inductive NNF : Set :=
                    | NNFVar : nat -> NNF
                    | NegNNFVar : nat -> NNF
                    | Disj : NNF -> NNF -> NNF
                    | Conj : NNF -> NNF -> NNF.


Fixpoint Interpretation (phi : NNF) (v : nat -> bool) : bool :=
            match phi with
                    | NNFVar p => v p
                    | NegNNFVar p => if v p then false else true
                    | Disj psi ksi => max (Interpretation psi v) (Interpretation ksi v)
                    | Conj psi ksi => min (Interpretation psi v) (Interpretation ksi v) end.

Check set_union.

Check Nat.eq_dec.

Compute set_union Nat.eq_dec (set_add Nat.eq_dec 1 (empty_set nat)) (set_add Nat.eq_dec 2 (empty_set nat)).

Fixpoint Positive (phi : NNF) (v : nat -> bool) : set nat := 
                  match phi with 
                        | NNFVar p => if v p then (set_add Nat.eq_dec p (empty_set nat)) else empty_set nat
                        | NegNNFVar p => if v p then empty_set nat else (set_add Nat.eq_dec p (empty_set nat))
                        | Disj psi ksi => set_union Nat.eq_dec (Positive psi v) (Positive ksi v)
                        | Conj psi ksi => set_union Nat.eq_dec (Positive psi v) (Positive ksi v) end.

Definition Satisfies (A : NNF) v  := (Interpretation A v) = true.


Definition f (p : nat) : bool :=
      match p with
          | 0 => false
          | 1 => true
          | 2 => false
          | _ => true end.

Definition Subset (s1 s2 : set nat) : Prop :=
        forall s, set_In s s1 -> set_In s s2.

(*
Compute Positive (Disj (Conj (NegNNFVar 0) (NNFVar 1)) (NNFVar 2))  f.
Theorem Monotony : forall (v1 : nat -> bool) (v2 : nat -> bool) (phi : NNF), (Subset (Positive phi v1) (Positive phi v2)) ->
                        (Satisfies phi v1) -> (Satisfies phi v2).
Proof. intros. induction phi.
          * unfold Satisfies. unfold Satisfies in H0. simpl. simpl in H0. unfold Positive in H. rewrite -> H0 in H. simpl in H.*)


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
                                            


