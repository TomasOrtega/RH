import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.WedgeSupport

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => norm_nonneg _`.
-/
theorem nF_nonneg' {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => norm_nonneg _`.
-/
theorem sz_nonneg' {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem map_mul_eq_one {R S ι κ : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq κ] (f : R →+* S)
    {A : Matrix ι κ R} {Y : Matrix κ ι R} (h : Y * A = 1) : Y.map f * A.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Establish `h1` using `(hF K ι κ κ A).1 Y`. Rewrite `h1` using `[h, (hF K κ κ κ 1).2.2 1, det_one, norm_one]`. Conclude with `h1`.
-/
theorem one_le_sz_pow_mul_nF (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) :
    1 ≤ sz Y ^ Fintype.card κ * nF A := by
  have h1 := (hF K ι κ κ A).1 Y
  rw [h, (hF K κ κ κ 1).2.2 1, det_one, norm_one] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `(hF K κ ι κ (1 : Matrix κ κ K)).1 A`. Rewrite `h1` using `[Matrix.mul_one, (hF K κ κ κ 1).2.2 1, det_one, norm_one, mul_one]`. Conclude with `h1`.
-/
theorem nF_le_sz_pow (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≤ sz A ^ Fintype.card κ := by
  have h1 := (hF K κ ι κ (1 : Matrix κ κ K)).1 A
  rw [Matrix.mul_one, (hF K κ κ κ 1).2.2 1, det_one, norm_one, mul_one] at h1
  exact h1

/- English proof (translation)
Introduce `h0`. Establish `h1` using `one_le_sz_pow_mul_nF hF h`. Rewrite `h1` using `[h0, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nF_ne_zero_of_left_inv (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) : nF A ≠ 0 := by
  intro h0
  have h1 := one_le_sz_pow_mul_nF hF h
  rw [h0, mul_zero] at h1
  linarith

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(nF_le_sz_pow hF A).trans (pow_le_one₀ (sz_nonneg' A) hA)`. Establish `h1` using `one_le_sz_pow_mul_nF hF h`. Establish `h2 : sz Y ^ Fintype.card κ ≤ 1` using `pow_le_one₀ (sz_nonneg' Y) hY`. Use polynomial arithmetic with `[nF_nonneg' A]`.
-/
theorem nF_eq_one_of_sz_le (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) (hY : sz Y ≤ 1) (hA : sz A ≤ 1) :
    nF A = 1 := by
  apply le_antisymm
  · exact (nF_le_sz_pow hF A).trans (pow_le_one₀ (sz_nonneg' A) hA)
  · have h1 := one_le_sz_pow_mul_nF hF h
    have h2 : sz Y ^ Fintype.card κ ≤ 1 := pow_le_one₀ (sz_nonneg' Y) hY
    nlinarith [nF_nonneg' A]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `(hI ι κ κ A).1 Y`. Rewrite `h1` using `[h, (hI κ κ κ 1).2.2 1, det_one, norm_one, h0, mul_zero]`. Evaluate the numerical expressions using `at h1`.
-/
theorem nI_ne_zero_of_left_inv (hI : MulI) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ ℂ} {Y : Matrix κ ι ℂ} (h : Y * A = 1) : nI A ≠ 0 := by
  intro h0
  have h1 := (hI ι κ κ A).1 Y
  rw [h, (hI κ κ κ 1).2.2 1, det_one, norm_one, h0, mul_zero] at h1
  norm_num at h1

/- English proof (translation)
Introduce `hF hI hS E _ _ _ ι κ _ _ _ _ A Y h`. Use `⟨fun v => nI_ne_zero_of_left_inv hI (map_mul_eq_one (cV v) h), fun w => nF_ne_zero_of_left_inv hF (map_mul_eq_one (cW w) h), ?_⟩` and prove the remaining obligations. Use `((hS E κ ι Y).union (hS E ι κ A)).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hn`.

Conclude with `hw (nF_eq_one_of_sz_le hF (map_mul_eq_one (cW w) h) hn.1 hn.2)`.
-/
theorem finSupp_of_mul : MulF → MulI → SzFin → FinSupp := by
  intro hF hI hS E _ _ _ ι κ _ _ _ _ A Y h
  refine ⟨fun v => nI_ne_zero_of_left_inv hI (map_mul_eq_one (cV v) h),
    fun w => nF_ne_zero_of_left_inv hF (map_mul_eq_one (cW w) h), ?_⟩
  refine ((hS E κ ι Y).union (hS E ι κ A)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hn
  exact hw (nF_eq_one_of_sz_le hF (map_mul_eq_one (cW w) h) hn.1 hn.2)

end GlobalTheory.CompanionTheory.WedgeSupport

end
