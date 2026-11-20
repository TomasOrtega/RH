import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `hfib` using `ConeFibreDegree.full n e δ (HermNorm.std n) W g hW hg hδ`. Establish `hpos` using `ChowDegreePos.proof n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ`. Establish `: (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot` using `ae_neBot.2 (NeZero.ne _)`.

Establish `: (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot` using `ae_neBot.2 (NeZero.ne _)`. Take `⟨π, hπ⟩` from `hfib.exists`. Take `⟨w, hw1, hw2⟩` from `(hπ.and (ae_fibreCount_eq_zero (by omega) (HermNorm.std n) W π)).exists`. Rewrite `hw2` using `[hw1]`. Establish `h0 : δ = 0` using `by exact_mod_cast hw2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem chowGroups_le {n e δ : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hW : IsProjPrime W) (hg : IsChowForm W (e + 1) g)
    (hδ : IsMultiHomog δ g) : e + 1 ≤ n := by
  by_contra hn
  have hfib := ConeFibreDegree.full n e δ (HermNorm.std n) W g hW hg hδ
  have hpos := ChowDegreePos.proof n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
    ae_neBot.2 (NeZero.ne _)
  obtain ⟨π, hπ⟩ := hfib.exists
  obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) (HermNorm.std n) W π)).exists
  rw [hw1] at hw2
  have h0 : δ = 0 := by exact_mod_cast hw2
  omega

/- English proof (translation)
Establish `hcl : IsClosed (coneSet h J)` using `isClosed_coneSet h J`. Take `⟨F, hF, -, hU, -⟩` from `hA.exists_iUnion_isClosed`. Rewrite using `[← hU, Set.inter_iUnion]`. Conclude with `isSigmaCompact_iUnion _ fun i => IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hcl.inter (hF i)) (Set.subset_univ _)`.
-/
theorem isSigmaCompact_cone_inter {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    {A : Set (EuclideanSpace ℂ (Fin n))} (hA : IsOpen A) : IsSigmaCompact (coneSet h J ∩ A) := by
  have hcl : IsClosed (coneSet h J) := isClosed_coneSet h J
  obtain ⟨F, hF, -, hU, -⟩ := hA.exists_iUnion_isClosed
  rw [← hU, Set.inter_iUnion]
  exact isSigmaCompact_iUnion _ fun i =>
    IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hcl.inter (hF i)) (Set.subset_univ _)

/- English proof (translation)
Introduce `y hy t _ q hq`. Rewrite using `[HermNorm.pointOf_smul']`. Conclude with `PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq`.
-/
theorem isScaleStable_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) : IsScaleStable (coneSet h J) := by
  intro y hy t _ q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq

/- English proof (translation)
Introduce `y hy t ht` and use `⟨hS y hy.1 t ht, hT y hy.2 t ht⟩`.
-/
theorem IsScaleStable.inter {n : ℕ} {S T : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    (hT : IsScaleStable T) : IsScaleStable (S ∩ T) :=
  fun y hy t ht => ⟨hS y hy.1 t ht, hT y hy.2 t ht⟩

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
