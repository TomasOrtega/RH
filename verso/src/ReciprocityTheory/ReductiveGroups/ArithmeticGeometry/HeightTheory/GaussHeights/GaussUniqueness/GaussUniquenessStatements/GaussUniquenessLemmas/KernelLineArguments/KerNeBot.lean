import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.NotInjOfTrdeg

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

/- English proof (translation)
Use `letI := resAlg (F := K) v`. Introduce `hbot`. Set `S : Set (IsLocalRing.ResidueField (vRing v))` to `{r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}`. Set `ρL : Fin N → IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S` to `fun k => ⟨IsLocalRing.residue (vRing v) ⟨a (j0.succAbove k), ha _⟩, IntermediateField.subset_adjoin _ _ ⟨j0.succAbove k, ha _, rfl⟩⟩`. Establish `hni` using `not_inj_of_trdeg (D := D) S j0 ρL hD htr`.

Rewrite `hni` using `[injective_iff_map_eq_zero]`. Use `push_neg at hni`. Take `⟨G, hG0, hG⟩` from `hni`. Take `⟨f, rfl⟩` from `MvPolynomial.map_surjective (gK v hv) (gK_surj v hv) G`. Establish `hf : f ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hG (map_zero _)`. Establish `H : psiR (D` using `D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) = (MvPolynomial.map (algebraMap (IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S) (IsLocalRing.ResidueField (vRing v)))).comp (((MvPolynomial.aeval (imgR (D := D) j0 ρL)).toRingHom).comp (Mv …`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]`. Use `congr 1`. Introduce `t`. Simplify using `only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]`. Rewrite using `[imgR_map, imgR_map]`.

Both sides reduce to the same expression. Establish `hmem : f ∈ RingHom.ker (psiR (D` using `D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by`. Rewrite using `[RingHom.mem_ker, H]`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG0, map_zero]`. Rewrite `hmem` using `[hbot]`.

Conclude with `hf (Ideal.mem_bot.mp hmem)`.
-/
theorem ker_ne_bot (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (ha : ∀ j, a j ∈ vRing v) (hD : 1 ≤ D)
    (htr : letI := resAlg (F := K) v
      Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
        (IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
          {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}) =
        ((D - 1 : ℕ) : Cardinal)) :
    RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) ≠ ⊥ := by
  letI := resAlg (F := K) v
  intro hbot
  let S : Set (IsLocalRing.ResidueField (vRing v)) :=
    {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}
  let ρL : Fin N → IntermediateField.adjoin
      (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S :=
    fun k => ⟨IsLocalRing.residue (vRing v) ⟨a (j0.succAbove k), ha _⟩,
      IntermediateField.subset_adjoin _ _ ⟨j0.succAbove k, ha _, rfl⟩⟩
  have hni := not_inj_of_trdeg (D := D) S j0 ρL hD htr
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨G, hG0, hG⟩ := hni
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective (gK v hv) (gK_surj v hv) G
  have hf : f ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  have H : psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) =
      (MvPolynomial.map (algebraMap (IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω))) S)
        (IsLocalRing.ResidueField (vRing v)))).comp
        (((MvPolynomial.aeval (imgR (D := D) j0 ρL)).toRingHom).comp
          (MvPolynomial.map (gK v hv))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply]
      congr 1
    · intro t
      simp only [psiR, psiT, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      rw [imgR_map, imgR_map]
      rfl
  have hmem : f ∈ RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    rw [RingHom.mem_ker, H]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG0, map_zero]
  rw [hbot] at hmem
  exact hf (Ideal.mem_bot.mp hmem)

end GaussValuationUniqueness
