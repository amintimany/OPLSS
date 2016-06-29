Require Import Categories.Essentials.Notations.
Require Import Categories.Essentials.Types.
Require Import Categories.Essentials.Facts_Tactics.
Require Import Categories.Category.Main.
Require Import Categories.Functor.Main.
Require Import Categories.Cat.Cat.
Require Import Categories.Ext_Cons.Prod_Cat.Main.
Require Import Categories.Basic_Cons.PullBack.

Local Open Scope functor_scope.

Section CatPullBack.
  Context {C D E : Category} (F : C –≻ E) (G : D –≻ E).

  Notation FGOEQ :=
    (fun x => (F _o (fst x)) = (G _o (snd x)))%object (only parsing).

  Section CatPB.
    Local Obligation Tactic := idtac.

    Program Definition CatPB :=
      SubCategory
        (C × D)
        FGOEQ
        (fun x y h => ∃ u : FGOEQ x * FGOEQ y,
             match (fst u) in _ = v return Hom v _ with
               eq_refl =>
               match (snd u) in _ = w return Hom _ w with
                 eq_refl => (F _a (fst h))%morphism
               end
             end = (G _a (snd h))%morphism) _ _.
    Next Obligation.
    Proof.
      intros ? H; basic_simpl. eexists (H, H); eauto.
    Qed.

    Next Obligation.
    Proof.
      intros ? ? ? ? ? [[H11 H12] H13] [[H21 H22] H23]; basic_simpl.
      exists (H11, H22); simpl.
      rewrite ?F_compose. rewrite <- H13, <- H23.
      clear H13 H23. PIR. ElimEq; trivial.
    Qed.

  End CatPB.

  Program Definition CatPB_Proj1 : Functor CatPB C :=
    {|
      FO x := fst (projT1 x)
    |}.

  Program Definition CatPB_Proj2 : Functor CatPB D :=
    {|
      FO x := snd (projT1 x)
    |}.

  Program Definition into_CatPB
          (p' : Category)
          (pm1 : p' –≻ C)
          (pm2 : p' –≻ D)
          (H : F ∘ pm1 = G ∘ pm2)
    : p' –≻ CatPB :=
    {|
      FO x := existT _ (pm1 _o x, pm2 _o x)%object _;
      FA x y h := exist _ (pm1 _a h, pm2 _a h)%morphism _
    |}.

  Next Obligation.
  Proof. apply (equal_f (f_equal FO H) x). Qed.

  Next Obligation.
  Proof.
    destruct (Functor_eq_morph _ _ H) as [u HH].
    eexists (_, _); eauto.
  Qed.

  Next Obligation.
  Proof.
    apply sig_proof_irrelevance; simpl.
    rewrite ?F_compose; trivial.
  Qed.

  Lemma CatPB_morph_com :
    (F ∘ CatPB_Proj1)%functor = (G ∘ CatPB_Proj2)%functor.
  Proof.
    assert (HO : ((F ∘ CatPB_Proj1) _o)%object =
                 ((G ∘ CatPB_Proj2) _o)%object).
    {
      extensionality x. destruct x as [x Hx]; trivial.
    }
    apply (Functor_extensionality _ _ HO). intros a b h.
    transitivity (
        match equal_f HO a in _ = v return
              (v –≻ _)%morphism
        with
          eq_refl =>
          match equal_f HO b in _ = w return
                (_ –≻ w)%morphism
          with
            eq_refl => ((F ∘ CatPB_Proj1) _a h)%morphism
          end
        end
      ).
    { destruct HO; trivial. }
    destruct h as [[h1 h2] [[u1 u2] Hu]].
    generalize (equal_f HO b); generalize (equal_f HO a).
    intros Hb Ha. simpl in *. clear HO. PIR.
    rewrite <- Hu. clear Hu.
    destruct u1; destruct u2; trivial.
  Qed.

  Program Definition CatPullBack :
    @PullBack Cat _ _ _ F G :=
    {|
      pullback := CatPB;
      pullback_morph_1 := CatPB_Proj1;
      pullback_morph_2 := CatPB_Proj2;
      pullback_morph_com := CatPB_morph_com;
      pullback_morph_ex := into_CatPB
    |}.
  Local Obligation Tactic := idtac.
  Next Obligation.
  Proof.
    intros p' pm1 pm2 H1 u u' H2 H3 H4 H5.
    assert (HO : (u _o)%object = (u' _o)%object).
    {
      extensionality x.
      set (H2' := equal_f (f_equal FO H2) x); clearbody H2'.
      set (H3' := equal_f (f_equal FO H3) x); clearbody H3'.
      set (H4' := equal_f (f_equal FO H4) x); clearbody H4'.
      set (H5' := equal_f (f_equal FO H5) x); clearbody H5'.
      simpl in *.
      destruct (u _o x)%object as [[x1 x2] Hx].
      destruct (u' _o x)%object as [[y1 y2] H'x].
      simpl in *; subst.
      PIR; trivial.
    }
    apply (Functor_extensionality _ _ HO). intros a b h.
    transitivity (
        match equal_f HO a in _ = v return
              (v –≻ _)%morphism
        with
          eq_refl =>
          match equal_f HO b in _ = w return
                (_ –≻ w)%morphism
          with
            eq_refl => (u _a h)%morphism
          end
        end
      ).
    { destruct HO; trivial. }
    rewrite <- H4 in H2. rewrite <- H5 in H3. clear H4 H5.
    destruct (Functor_eq_morph _ _ H2) as [u2 HH2].
    destruct (Functor_eq_morph _ _ H3) as [u3 HH3].
    specialize (HH2 _ _ h). specialize (HH3 _ _ h).
    revert HH2 HH3.
    generalize (u2 a) as u2a; generalize (u2 b) as u2b;
      generalize (u3 a) as u3a; generalize (u3 b) as u3b.
    clear u2 u3.
    intros u3b u3a u2b u2a HH2 HH3.
    generalize (equal_f HO b); generalize (equal_f HO a).
    intros Hb Ha.
    simpl in * |-.
    unfold CatPB_Proj1_obligation_1, CatPB_Proj2_obligation_1 in *.
    destruct (u _a h)%morphism as [[h1 h2] [[v1 v2] Hv]].
    destruct (u' _a h)%morphism as [[h1' h2'] [[w1 w2] Hw]].
    destruct (u _o a)%object as [[a1 a2] Ia].
    destruct (u _o b)%object as [[b1 b2] Ib].
    destruct (u' _o a)%object as [[a'1 a'2] I'a].
    destruct (u' _o b)%object as [[b'1 b'2] I'b].
    simpl in *. subst.
    PIR. simpl in *.
    apply sig_proof_irrelevance. simpl.
    match type of Hb with
      ?A => replace Hb with (eq_refl : A) by (apply proof_irrelevance)
    end.
    match type of Ha with
      ?A => replace Ha with (eq_refl : A) by (apply proof_irrelevance)
    end.
    trivial.
  Qed.

End CatPullBack.