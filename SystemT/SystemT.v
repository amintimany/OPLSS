Require Import Coq.Unicode.Utf8.
Require Import Autosubst.Autosubst.
Require Import Coq.omega.Omega.

(* Gödel's System T types and terms *)

Open Scope list_scope.

Inductive type :=
| nt : type (* type of natural numbers *)
| fn : type → type → type (* function type *)
.

Inductive term :=
| Var (x : var)
| Z
| Sc (n : term)
| Lam (t : {bind 1 of term})
| App (t t' : term)
| nt_el (t1 t2 : term) (t3 : {bind 2 of term}).


Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(* reduction relation *)

Inductive step : term → term → Prop :=
| Sc_stp t t' : step t t' → step (Sc t) (Sc t')
| App_stp1 t1 t1' t2 : step t1 t1' → step (App t1 t2) (App t1' t2)
| App_stp2 t1 t2 t2' : step t2 t2' → step (App t1 t2) (App t1 t2')
| beta t1 t2 : step (App (Lam t1) t2) t1.[t2/]
| Lam_stp t t' : step t t' → step (Lam t) (Lam t')
| nt_el_stpZ t2 t3 : step (nt_el Z t2 t3) t2
| nt_el_stpSc t1 t2 t3 : step (nt_el (Sc t1) t2 t3)
                             (t3.[t1, nt_el t1 t2 t3/])
.

(* definition of strongly normalizing *)

Record red_sequence :=
  {
    seq :> nat → term;
    seq_red : ∀ n, step (seq n) (seq (S n))
  }.

Record red_sequence_from e :=
  {
    redseq :> red_sequence;
    redseq_from : redseq O = e
  }.

Definition SN e : Prop := (red_sequence_from e) → False.

(* typing *)
Definition Context := list type.

Program Fixpoint lookup (Γ : Context) (x : nat) (H : x < length Γ) : type :=
  match x as u return u < length Γ → type with
  | O =>
    λ h,
      match Γ as γ return O < length γ → type with
      | nil => λ h, _
      | v :: l => λ h, v
      end h
  | S x' =>
    λ h,
      match Γ with
      | nil => _
      | v :: l => lookup l x' _
      end
  end H.
Next Obligation. abstract omega. Qed.
Next Obligation. simpl in *. abstract omega. Qed.
Next Obligation. simpl in *. abstract omega. Qed.

Inductive types : Context → term → type → Prop :=
| VarT Γ x (H : x < length Γ) : types Γ (Var x) (lookup Γ x H)
| ZT Γ : types Γ Z nt
| ScT Γ t : types Γ t nt → types Γ (Sc t) nt
| LamT Γ t T T' : types (T :: Γ) t T' → types Γ (Lam t) (fn T T')
| AppT Γ t t' T T' : types Γ t (fn T T') → types Γ t' T → types Γ (App t t') T'
| nt_elT Γ t1 t2 t3 T : types Γ t1 nt → types Γ t2 T →
                        types (nt :: T :: Γ) t3 T →
                        types Γ (nt_el t1 t2 t3) T.

Notation "Γ ⊢ t : T" := (types Γ t T) (at level 74, t, T at next level).

(* an environment matching a context *)
Definition environment := nat → term.

Fixpoint env_matching (Γ : Context) (env : environment)
         (P : type → term → Prop) : Prop :=
  match Γ with
  | nil => True
  | v :: l => P v (env O) ∧ env_matching l (fun n => env (S n)) P
  end.

(* hereditary strong normalization over types *)

Fixpoint HSN (T : type) : term -> Prop :=
  match T with
  | nt => SN
  | fn T1 T2 => λ t, SN t ∧ ∀ t', (HSN T1 t') -> (HSN T2 (App t t'))
  end.

Theorem HSN_SN t T : HSN T t → SN t.
Proof. induction T; simpl; tauto. Qed.

Theorem SN_Var x : SN (Var x).
Proof.
  intros [[sq sqr] sq0]; simpl in *.
  specialize (sqr 0); rewrite sq0 in sqr.
  inversion sqr.
Qed.

(* The types we need to take a term down, ex.:
   T1 -> T2 => T1
   T1 -> T2 -> T3 => T1, T2
   T0 -> (T1 -> T2) -> (T3 -> T4) => T0, T1 -> T2, T3 *)

Fixpoint types_to_take_down (T : type) : Context :=
  match T with
  | nt => nil
  | fn T1 T2 => T1 :: types_to_take_down T2
  end.

(* This is always nt in our case! *)
Fixpoint end_type (T : type) : type :=
  match T with
  | nt => nt
  | fn T1 T2 => end_type T2
  end.

Fixpoint apply_through_context (env : environment) (Γ : Context) t :=
  match Γ with
  | nil => t
  | T :: l => apply_through_context (λ n, env (S n)) l (App t (env 0))
  end.

Theorem HSN_var_applied_to_types_to_take_down T env x :
  env_matching (types_to_take_down T) env HSN →
  HSN (end_type T) (apply_through_context env (types_to_take_down T) (Var x)).
Proof.
  revert env. induction T.
  - admit.
  - intros env [H1 H2].
    simpl in *.
    



    
Theorem Var_HSN T x : HSN T (Var x).
Proof.
  induction T.
  - admit.
  - split.
    + admit.
    + intros t' H1.
      



Inductive var_in_fun_pos : type → term → Prop :=
| var_in_fun_pos_nat x : var_in_fun_pos nt (Var x)
| var_in_fun_pos_fun T1 T2 t :
    var_in_fun_pos T2 t → var_in_fun_pos (fn T1 T2) (Lam t).

Theorem Var_HSN T x : HSN T (Var x).
Proof.
  revert x.
  induction T.
  - admit.
  - split.
    + admit.
    + intros t' H1.
      








      
    
  
  revert t.
  induction T; intros t H1.
  - inversion H1; subst. apply SN_Var.
  - simpl in *; split.
    + inversion H1; subst.
      admit.
    + intros t' H2. inversion H1; subst.
      








(* SN is a logical relation *)

Theorem Fundamental Γ t T env :
  Γ ⊢ t : T → env_matching Γ env HSN → HSN T t.[env].
  intros H. revert env. induction H; intros env.
  - revert x env H. induction Γ as [|T Γ]; intros x env H1 H2; simpl in *.
    + omega.
    + destruct x; try tauto; try omega.
      apply (IHΓ x (λ n, env (S n))); try omega; tauto.
  - intros H1 [[sq sqred] sq0]; simpl in *.
    specialize (sqred 0); rewrite sq0 in sqred. inversion sqred.
  - intros H1; simpl in *. admit.
  - intros H1; simpl in *. split.
    + 



    
  - intros H1; simpl in *. apply IHtypes1; auto.
  - intros H2; simpl in *. 