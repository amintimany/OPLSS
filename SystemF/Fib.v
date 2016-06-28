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