import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafHensH : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (C : Type) [CommRing C] (K : Ideal C), HenselianRing C K →
  IsUnit (q : C) → ∀ i : ℤ, Eqv (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i)

def LeafAffQuot : Prop := LeafQuot → ∀ (d : ℕ) (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) →
  ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I →
  Function.Bijective ((Ideal.Quotient.mk K).comp (η.comp (ψ.comp MvPolynomial.C)))

def LeafExcAff : Prop := Hyp → LeafIndExc → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I → ∃ h,
  Exc q (opnMap (Spec.map (CommRingCat.ofHom (η.comp ψ))) (off C K) (off _ (Ideal.span (Set.range MvPolynomial.X))) h)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `sch.map _ = sch.map _ ≫ sch.map _`. Rewrite using `[← Functor.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  change sch.map _ = sch.map _ ≫ sch.map _
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `sch.map (Spec.map (𝟙 _)) = _`. Rewrite using `[Spec.map_id, CategoryTheory.Functor.map_id]`.
-/
theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

/- English proof (translation)
Set `E` to `RingEquiv.ofBijective e he`. Establish `h1 : (E.symm : B →+* A).comp e = RingHom.id A` using `by ext x; exact E.symm_apply_apply x`. Establish `h2 : e.comp (E.symm : B →+* A) = RingHom.id B` using `by ext x; exact E.apply_symm_apply x`. Establish `: IsIso (spMap e)` using `⟨⟨spMap (E.symm : B →+* A), by rw [← spMap_comp', h2, spMap_id'], by rw [← spMap_comp', h1, spMap_id']⟩⟩`. Conclude with `eqv_iso _ F`.
-/
theorem eqv_spMap_bij {A B : Type} [CommRing A] [CommRing B] (e : A →+* B) (he : Function.Bijective e)
    {S : Type} [CommRing S] (F : Shv S) : Eqv S (spMap e) F := by
  let E := RingEquiv.ofBijective e he
  have h1 : (E.symm : B →+* A).comp e = RingHom.id A := by ext x; exact E.symm_apply_apply x
  have h2 : e.comp (E.symm : B →+* A) = RingHom.id B := by ext x; exact E.apply_symm_apply x
  have : IsIso (spMap e) := ⟨⟨spMap (E.symm : B →+* A), by rw [← spMap_comp', h2, spMap_id'],
    by rw [← spMap_comp', h1, spMap_id']⟩⟩
  exact eqv_iso _ F

/- English proof (translation)
Introduce `hyp d q _ R B C _ _ _ ψ η hq hψ I K hη hK hH hI' hy n i`. Establish `hth : IsThom d (thom d)` using `@pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hT hyp d)`. Establish `hqP : IsUnit (q : MvPolynomial (Fin d) R)` using `by simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)`. Establish `hqC : IsUnit (q : C)` using `by simpa using hq.map ((η.comp ψ).comp MvPolynomial.C)`. Take `⟨h, hE⟩` from `h3 hyp hI d q R B C ψ η hq hψ I K hη hK hI'`.

Establish `hnat` using `(hth q).1 (MvPolynomial (Fin d) R) C (η.comp ψ) (Ideal.span (Set.range MvPolynomial.X)) K MvPolynomial.X rfl hy h hqP`. Establish `hg` using `(hth q).2.2.1 R (Ideal.span (Set.range MvPolynomial.X)) rfl hq n i`. Set `p` to `pull (ZMod q) (spMap ((η.comp ψ).comp (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) (tw q i) n`. Establish `hmk` using `h1 hyp q C K hH hqC i n`. Establish `he` using `eqv_spMap_bij _ (h2 hQ d R B C ψ η hψ I K hη hK hI') (tw q i) n`.

Establish `hp : Function.Bijective p`. Rewrite `he` using `[spMap_comp']`. Establish `e2 : (pull (ZMod q) (spMap (Ideal.Quotient.mk K) ≫ spMap (η.comp (ψ.comp MvPolynomial.C))) (tw q i) n : _ → _) = (pull (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i) n) ∘ p` using `funext fun x => pull_comp _ _ _ _ _ x`. Rewrite `he` using `[e2]`. Conclude with `(Function.Bijective.of_comp_iff' hmk p).1 he`.

Establish `hpb : ∀ b, p b = pull (ZMod q) (spMap (η.comp ψ)) (tw q i) n (pull (ZMod q) (spMap MvPolynomial.C) (tw q i) n b)` using `fun b => by`. Express the relevant statement in the definitionally equal form `pull _ _ _ _ b = _`. Rewrite using `[← pull_comp, ← spMap_comp']`. Use `(Function.Bijective.of_comp_iff _ hp).1 ?_` and prove the remaining obligations. Establish `key` using `(hE (n + 2 * d) (i + d)).comp hg`.

Use `key using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `b`. Use `Eq.trans ?_ (hA hyp.2.2.2.2.1 q _ _ _ n (2 * d) i d _ _).symm` and prove the remaining obligations. Rewrite using `[hnat, Function.comp_apply, hpb]`. Both sides reduce to the same expression.
-/
theorem LeafPrdAff_of (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h2 : LeafAffQuot) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff := by
  intro hyp d q _ R B C _ _ _ ψ η hq hψ I K hη hK hH hI' hy n i
  have hth : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hT hyp d)
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqC : IsUnit (q : C) := by simpa using hq.map ((η.comp ψ).comp MvPolynomial.C)
  obtain ⟨h, hE⟩ := h3 hyp hI d q R B C ψ η hq hψ I K hη hK hI'
  have hnat := (hth q).1 (MvPolynomial (Fin d) R) C (η.comp ψ) (Ideal.span (Set.range MvPolynomial.X)) K MvPolynomial.X rfl
    hy h hqP
  have hg := (hth q).2.2.1 R (Ideal.span (Set.range MvPolynomial.X)) rfl hq n i
  let p := pull (ZMod q) (spMap ((η.comp ψ).comp (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) (tw q i) n
  have hmk := h1 hyp q C K hH hqC i n
  have he := eqv_spMap_bij _ (h2 hQ d R B C ψ η hψ I K hη hK hI') (tw q i) n
  have hp : Function.Bijective p := by
    rw [spMap_comp'] at he
    have e2 : (pull (ZMod q) (spMap (Ideal.Quotient.mk K) ≫ spMap (η.comp (ψ.comp MvPolynomial.C))) (tw q i) n : _ → _) =
        (pull (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i) n) ∘ p := funext fun x => pull_comp _ _ _ _ _ x
    rw [e2] at he
    exact (Function.Bijective.of_comp_iff' hmk p).1 he
  have hpb : ∀ b, p b = pull (ZMod q) (spMap (η.comp ψ)) (tw q i) n (pull (ZMod q) (spMap MvPolynomial.C) (tw q i) n b) :=
    fun b => by
      change pull _ _ _ _ b = _
      rw [← pull_comp, ← spMap_comp']
  refine (Function.Bijective.of_comp_iff _ hp).1 ?_
  have key := (hE (n + 2 * d) (i + d)).comp hg
  convert key using 1
  funext b
  refine Eq.trans ?_ (hA hyp.2.2.2.2.1 q _ _ _ n (2 * d) i d _ _).symm
  rw [hnat, Function.comp_apply, hpb]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut
