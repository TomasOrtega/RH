import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ImgRSuccAbove

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

/- English proof (translation)
Introduce `hinj`. Establish `hai : AlgebraicIndependent F (imgR (D` using `D) j0 ρ) := hinj`. Establish `h1` using `hai.cardinalMk_le_trdeg`. Use `first`. Consider the case `rw [← Algebra.trdeg_add_eq F (IntermediateField.adjoin F S)] at h1`.

Consider the case `rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1`. Rewrite `h1` using `[htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]`. Establish `hT : Fintype.card (TVar D N) = (D + 1) * (N + 1)` using `by simp [TVar]`. Establish `hS : Fintype.card (SVar D N) = 1 + (D + 1) * N` using `by simp [SVar]`. Rewrite `h1` using `[Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS]`.

Normalize the coercions in `at h1`. Rewrite `h1` using `[show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring]`. Generalize the expression as in `(D + 1) * N = P at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_inj_of_trdeg {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (S : Set E)
    (j0 : Fin (N + 1)) (ρ : Fin N → IntermediateField.adjoin F S) (hD : 1 ≤ D)
    (htr : Algebra.trdeg F (IntermediateField.adjoin F S) = ((D - 1 : ℕ) : Cardinal)) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) (imgR (D := D) j0 ρ)) := by
  intro hinj
  have hai : AlgebraicIndependent F (imgR (D := D) j0 ρ) := hinj
  have h1 := hai.cardinalMk_le_trdeg
  first
  | rw [← Algebra.trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  | rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  rw [htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h1
  have hT : Fintype.card (TVar D N) = (D + 1) * (N + 1) := by simp [TVar]
  have hS : Fintype.card (SVar D N) = 1 + (D + 1) * N := by simp [SVar]
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS] at h1
  norm_cast at h1
  rw [show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring] at h1
  generalize (D + 1) * N = P at h1
  omega

section Tr

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

noncomputable def gK (hv : IsTrivOn K v) :
    K →+* IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)) :=
  (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict ((vRing v).comap (algebraMap K Ω))
    (fun x => by rw [ValuationSubring.mem_comap]; exact alg_mem v hv x))

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Conclude with `⟨x.1, rfl⟩`.
-/
theorem gK_surj (hv : IsTrivOn K v) : Function.Surjective (gK v hv) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨x.1, rfl⟩

end Tr

end GaussValuationUniqueness
