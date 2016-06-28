Require Import Categories.Essentials.Notations.
Require Import Categories.Essentials.Types.
Require Import Categories.Essentials.Facts_Tactics.
Require Import Categories.Category.Main.
Require Import Categories.Functor.Main.
Require Import Categories.Coq_Cats.Type_Cat.Type_Cat.
Require Import Categories.Ext_Cons.Prod_Cat.Main.

Local Open Scope morphism_scope.
Local Open Scope object_scope.

Section fib.
  Context {E B} (p : (E –≻ B)%functor).

  Section iscart.
    Context {e' e : E} (φ : (e' –≻ e)%morphism).

    Record iscart_for e'' (ψ : e'' –≻ e) (g : p _o e'' –≻ p _o e')
           (Heq : p _a φ ∘ g = p _a ψ) :=
      { iscart_mor : (e'' –≻ e');
        iscart_mor_eq1 : φ ∘ iscart_mor = ψ;
        iscart_mor_eq2 : p _a iscart_mor = g;
        iscart_mor_unique f : φ ∘ f = ψ → p _a f = g → f = iscart_mor }.

    Definition iscartesian :=
      ∀ e'' (ψ : e'' –≻ e) (g : p _o e'' –≻ p _o e')
        (Heq : p _a φ ∘ g = p _a ψ),
        iscart_for e'' ψ g Heq.
  End iscart.

  Record isFib_for {e : E} {b : B} (f : b –≻ p _o e) :=
    { isfib_obj : E;
      isfib_obj_eq : p _o isfib_obj = b;
      isfib_mor : isfib_obj –≻ e;
      isfib_cart : iscartesian isfib_mor;
      isfib_mor_eq : f =
      match isfib_obj_eq in _ = y return y –≻ _ with
        eq_refl => p _a isfib_mor
      end }.

  Definition isFib := ∀ {e : E} {b : B} (f : b –≻ p _o e), isFib_for f.

End fib.

Definition isOpFib {E B} (p : (E –≻ B)%functor) := isFib (p ^op).

Definition isBiFib {E B} (p : (E –≻ B)%functor) := (isFib p * isOpFib p)%type.

(* Category Rel *)

Record REL :=
  {
    Rdom : Type;
    Rcodom : Type;
    RRel : Rdom → Rcodom → Prop
  }.

Record RelMor (R R' : REL) :=
 {
   RelMor_fst : Rdom R → Rdom R';
   RelMor_snd : Rcodom R → Rcodom R';
   RelMor_cond : ∀ (x : Rdom R) (y : Rcodom R),
       RRel R x y → RRel R' (RelMor_fst x) (RelMor_snd y)
 }.

Arguments RelMor_fst {_ _} _ _.
Arguments RelMor_snd {_ _} _ _.

Lemma RelMor_eq_simplify {R R' : REL} (f g : RelMor R R')
  : RelMor_fst f = RelMor_fst g → RelMor_snd f = RelMor_snd g → f = g.
Proof.
  destruct f; destruct g; simpl in *; intros; ElimEq; PIR; trivial.
Qed.

Program Definition RelMor_id (R : REL) : RelMor R R :=
 {|
   RelMor_fst x := x;
   RelMor_snd x := x
 |}.

Program Definition RelMor_compose {R R' R'' : REL}
        (f : RelMor R R') (g : RelMor R' R'') : RelMor R R'' :=
 {|
   RelMor_fst x := RelMor_fst g ((RelMor_fst f) x);
   RelMor_snd x := RelMor_snd g ((RelMor_snd f) x);
 |}.

Next Obligation.
Proof.
  repeat apply RelMor_cond; trivial.
Qed.

Program Definition Rel : Category :=
  {|
    Obj := REL;
    Hom R R' := RelMor R R';
    id := RelMor_id;
    compose := @RelMor_compose
  |}.

Solve Obligations with basic_simpl; apply RelMor_eq_simplify; trivial.

Program Definition Rel_to_Sets : (Rel –≻ (Type_Cat × Type_Cat))%functor :=
  {|
    FO X := (Rdom X, Rcodom X);
    FA a b f:= (RelMor_fst f, RelMor_snd f)
  |}.

Section Rel_to_Sets_Fib.
  Context (R : Rel) (X : (Type_Cat × Type_Cat)%category)
          (f : X –≻ (Rel_to_Sets _o R)).

  Definition Rel_to_Sets_Fib_dom : Rel :=
    {|
      Rdom := fst X;
      Rcodom := snd X;
      RRel := fun x y => RRel R (fst f x) (snd f y)
    |}.

  Local Obligation Tactic := trivial.

  Program Definition Rel_to_Sets_Fib_mor : RelMor Rel_to_Sets_Fib_dom R :=
    {|
      RelMor_fst x := fst f x;
      RelMor_snd x := snd f x;
    |}.

  Definition Rel_to_Sets_Fib_mor_cart :
    iscartesian Rel_to_Sets Rel_to_Sets_Fib_mor.
    intros R' ψ g Heq. simpl in *.
    eapply (@Build_iscart_for Rel _ _ _ _ _ _ _ _ _ (Build_RelMor _ _ _ _ _)).
    - apply RelMor_eq_simplify;
        [apply (f_equal fst Heq) | apply (f_equal snd Heq)].
    - trivial.
    - intros h H1 H2. apply RelMor_eq_simplify;
                        [apply (f_equal fst H2) | apply (f_equal snd H2)].
      Unshelve.
      intros x y H; simpl in *.
      cbn_rewrite (equal_f (f_equal fst Heq) x).
      cbn_rewrite (equal_f (f_equal snd Heq) y).
      apply RelMor_cond; trivial.
  Qed.

End Rel_to_Sets_Fib.

Section Rel_to_Sets_OpFib.
  Context (R : Rel) (X : (Type_Cat × Type_Cat)%category)
          (f : (Rel_to_Sets _o R) –≻ X).

  Definition Rel_to_Sets_OpFib_dom : Rel :=
    {|
      Rdom := fst X;
      Rcodom := snd X;
      RRel := fun x y => ∃ x' y',
                  fst f x' = x ∧ snd f y' = y ∧ RRel R x' y'
    |}.

  Local Obligation Tactic := trivial.

  Program Definition Rel_to_Sets_OpFib_mor : RelMor R Rel_to_Sets_OpFib_dom :=
    {|
      RelMor_fst x := fst f x;
      RelMor_snd x := snd f x;
    |}.

  Next Obligation.
  Proof.
    intros x y H; simpl in *; eauto.
  Qed.

  Definition Rel_to_Sets_OpFib_mor_cart :
    iscartesian (Rel_to_Sets ^op) Rel_to_Sets_OpFib_mor.
    intros R' ψ g Heq. simpl in *.
    eapply (@Build_iscart_for _ _ (Rel_to_Sets ^op)
                              _ _ _ _ _ _ _ (Build_RelMor _ _ _ _ _)).
    - apply RelMor_eq_simplify;
        [apply (f_equal fst Heq) | apply (f_equal snd Heq)].
    - trivial.
    - intros h H1 H2. apply RelMor_eq_simplify;
                        [apply (f_equal fst H2) | apply (f_equal snd H2)].
      Unshelve.
      intros x y [x' [y' [H1 [H2 H3]]]]; simpl in *.
      set (Heq1 := equal_f (f_equal fst Heq) x'); clearbody Heq1.
      set (Heq2 := equal_f (f_equal snd Heq) y'); clearbody Heq2.
      simpl in *. rewrite H1 in Heq1. rewrite H2 in Heq2.
      destruct g; simpl in *; rewrite Heq1, Heq2.
      apply RelMor_cond; trivial.
  Qed.

End Rel_to_Sets_OpFib.

Theorem Rel_to_Sets_BiFib : isBiFib Rel_to_Sets.
Proof.
  split; intros R X f.
  - eapply (Build_isFib_for
              _ _ _ _ _ eq_refl _ (Rel_to_Sets_Fib_mor_cart R X f)).
    destruct f; simpl; trivial.
  - eapply (Build_isFib_for
              _ _ _ _ _ eq_refl _ (Rel_to_Sets_OpFib_mor_cart R X f)).
    destruct f; simpl; trivial.
Qed.