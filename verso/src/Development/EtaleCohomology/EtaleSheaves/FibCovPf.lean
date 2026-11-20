import Development.EtaleCohomology.EtaleSheaves.LineHighPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.FibCovPf

open LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

/- English proof (translation)
Take `⟨B, i1, i2, I, hB, hq, ⟨e'⟩⟩` from `h`. Conclude with `⟨B, i1, i2, I, hB, hq, ⟨e ≪≫ e'⟩⟩`.
-/
theorem qaic_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : QAIC q W') : QAIC q W := by
  obtain ⟨B, i1, i2, I, hB, hq, ⟨e'⟩⟩ := h
  exact ⟨B, i1, i2, I, hB, hq, ⟨e ≪≫ e'⟩⟩

/- English proof (translation)
Establish `: Subsingleton (B ⧸ (⊤ : Ideal B))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`. Establish `: IsEmpty (Spec (CommRingCat.of (B ⧸ (⊤ : Ideal B))))` using `inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ (⊤ : Ideal B))))`. Conclude with `⟨B, inferInstance, inferInstance, ⊤, hB, hq, ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty⟩⟩`.
-/
theorem qaic_empty (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (hB : AIC B) (hq : IsUnit (q : B))
    {W : Scheme.{0}} [IsEmpty W] : QAIC q W := by
  have : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have : IsEmpty (Spec (CommRingCat.of (B ⧸ (⊤ : Ideal B)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ (⊤ : Ideal B))))
  exact ⟨B, inferInstance, inferInstance, ⊤, hB, hq, ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty⟩⟩

/- English proof (translation)
Break down `hw with hE | ⟨B, i1, i2, i3, hB, e, he⟩` into its components or cases. Establish `: IsEmpty ↥(pullback w (cpt A) : Scheme.{0})` using `⟨fun x => hE.elim ((pullback.fst w (cpt A)).base x)⟩`. Conclude with `qaic_empty q B0 hB0 hq0`. Substitute `he` using the available equality. Use `⟨B, i1, i2, (IsLocalRing.maximalIdeal A).map (algebraMap A B), hB, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using hq.map (algebraMap A B)`. Take `⟨e2⟩` from `fibre_affine A B`. Conclude with `⟨(pullbackRightPullbackFstIso _ (cpt A) e.hom).symm ≪≫ asIso (pullback.snd e.hom _) ≪≫ e2⟩`.
-/
theorem qaic_good (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) (B0 : Type) [CommRing B0]
    [IsDomain B0] (hB0 : AIC B0) (hq0 : IsUnit (q : B0)) {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A))
    (hw : Good w) : QAIC q (pullback w (cpt A)) := by
  rcases hw with hE | ⟨B, i1, i2, i3, hB, e, he⟩
  · have : IsEmpty ↥(pullback w (cpt A) : Scheme.{0}) := ⟨fun x => hE.elim ((pullback.fst w (cpt A)).base x)⟩
    exact qaic_empty q B0 hB0 hq0
  · subst he
    refine ⟨B, i1, i2, (IsLocalRing.maximalIdeal A).map (algebraMap A B), hB, ?_, ?_⟩
    · simpa using hq.map (algebraMap A B)
    · obtain ⟨e2⟩ := fibre_affine A B
      exact ⟨(pullbackRightPullbackFstIso _ (cpt A) e.hom).symm ≪≫ asIso (pullback.snd e.hom _) ≪≫ e2⟩

/- English proof (translation)
Take `⟨hI, hA⟩` from `hZ`. Take `⟨x⟩ : Nonempty Z` from `hI.nonempty`. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Z.Opens) from trivial)`. Establish `: Nonempty U` using `⟨⟨x, hxU⟩⟩`. Use `⟨Γ(Z, U), inferInstance, IsIntegral.component_integral U, hA U hU ⟨x, hxU⟩, ?_⟩` and prove the remaining obligations.

Use `hq.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top).hom` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_absolutely_integrally_closed_domain_with_q_unit (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (hZ : AICSch Z) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B), AIC B ∧ IsUnit (q : B) := by
  obtain ⟨hI, hA⟩ := hZ
  obtain ⟨x⟩ : Nonempty Z := hI.nonempty
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Z.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨Γ(Z, U), inferInstance, IsIntegral.component_integral U, hA U hU ⟨x, hxU⟩, ?_⟩
  have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top).hom
  simpa using this

/- English proof (translation)
Introduce `q A _ _ hq Z p hZ U V f g _ _ hc hU hV hW`. Take `⟨B0, _, _, hB0, hq0⟩` from `exists_absolutely_integrally_closed_domain_with_q_unit q A hq p hZ`. Use `⟨pullback f (pullback.fst p (cpt A)), pullback g (pullback.fst p (cpt A)), pullback.snd f (pullback.fst p (cpt A)), pullback.snd g (pullback.fst p (cpt A)), inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hc, Set.preimage_univ]`. Conclude with `qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) f) (qaic_good q A hq B0 hB0 hq0 _ hU)`.

Conclude with `qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) g) (qaic_good q A hq B0 hB0 hq0 _ hV)`. Use `qaic_of_iso ?_ (qaic_good q A hq B0 hB0 hq0 _ hW)` and prove the remaining obligations. Conclude with `pullbackLeftPullbackSndIso f (pullback.fst p (cpt A)) (pullback.snd g (pullback.fst p (cpt A))) ≪≫ pullback.congrHom rfl pullback.condition.symm ≪≫ (pullbackLeftPullbackSndIso f g (pullback.fst g (pullback.fst p (cpt A)))).symm ≪≫ pullbackRightPullbackFstIso g (pullback.fst p (cp …`.
-/
theorem FibCov_of : FibCov := by
  intro q A _ _ hq Z p hZ U V f g _ _ hc hU hV hW
  obtain ⟨B0, _, _, hB0, hq0⟩ := exists_absolutely_integrally_closed_domain_with_q_unit q A hq p hZ
  refine ⟨pullback f (pullback.fst p (cpt A)), pullback g (pullback.fst p (cpt A)),
    pullback.snd f (pullback.fst p (cpt A)), pullback.snd g (pullback.fst p (cpt A)),
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hc, Set.preimage_univ]
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) f) (qaic_good q A hq B0 hB0 hq0 _ hU)
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) g) (qaic_good q A hq B0 hB0 hq0 _ hV)
  · refine qaic_of_iso ?_ (qaic_good q A hq B0 hB0 hq0 _ hW)
    exact pullbackLeftPullbackSndIso f (pullback.fst p (cpt A)) (pullback.snd g (pullback.fst p (cpt A))) ≪≫
      pullback.congrHom rfl pullback.condition.symm ≪≫
      (pullbackLeftPullbackSndIso f g (pullback.fst g (pullback.fst p (cpt A)))).symm ≪≫
      pullbackRightPullbackFstIso g (pullback.fst p (cpt A)) (pullback.snd f g) ≪≫
      pullback.congrHom pullback.condition.symm rfl ≪≫
      pullbackRightPullbackFstIso p (cpt A) (pullback.fst f g ≫ f) ≪≫
      pullback.congrHom (Category.assoc _ _ _) rfl

end LateralTheory.E.FibCovPf
