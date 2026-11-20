import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther

/- English proof (translation)
Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]`. Use `congr 1`. Distinguish the cases in `hc : c = ca`. Substitute `hc` using the available equality. Simplify using `[Matrix.mul_apply, Matrix.single_apply, mul_comm]`.

Simplify using `[Matrix.mul_apply, Matrix.single_apply, hc, Ne.symm hc]`.
-/
theorem mul_transv_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hc : c = ca
  · subst hc
    simp [Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · simp [Matrix.mul_apply, Matrix.single_apply, hc, Ne.symm hc]

/- English proof (translation)
Distinguish the cases in `hca : ca ∈ Set.range g`. Take `⟨qa, hqa⟩` from `hca`. Take `⟨qb, hqb⟩` from `hJ.mp ⟨qa, hqa⟩`. Establish `hq : qb ≠ qa`. Introduce and unpack `rfl`.

Conclude with `hne (hqa.symm.trans hqb)`. Establish `hiff : ∀ q, g q = ca ↔ q = qa` using `fun q => by`. Rewrite using `[← hqa]`. Conclude with `hg.eq_iff`. Establish `hM : (h * (1 + Matrix.single cb ca t)).submatrix f g = h.submatrix f g * (1 + Matrix.single qb qa t)`.

Use extensionality with `p q`. Simplify using `only [Matrix.submatrix_apply, mul_transv_apply, hqb, hiff]`. Establish `h1 : (1 + Matrix.single qb qa t : Matrix (Fin k) (Fin k) ℂ) = Matrix.transvection qb qa t`. Both sides reduce to the same expression. Rewrite using `[hM, Matrix.det_mul, h1, Matrix.det_transvection_of_ne qb qa hq t, mul_one]`.

Use `congr 1`. Use extensionality with `p q`. Establish `hq : g q ≠ ca` using `fun hh => hca ⟨q, hh⟩`. Simplify using `only [Matrix.submatrix_apply, mul_transv_apply, hq, if_false, add_zero]`.
-/
private lemma det_submatrix_mul_transvection_eq {N k : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N)
    (hne : ca ≠ cb) (f g : Fin k → Fin N) (hg : Function.Injective g)
    (hJ : ca ∈ Set.range g ↔ cb ∈ Set.range g) :
    ((h * (1 + Matrix.single cb ca t)).submatrix f g).det = (h.submatrix f g).det := by
  by_cases hca : ca ∈ Set.range g
  · obtain ⟨qa, hqa⟩ := hca
    obtain ⟨qb, hqb⟩ := hJ.mp ⟨qa, hqa⟩
    have hq : qb ≠ qa := by
      rintro rfl
      exact hne (hqa.symm.trans hqb)
    have hiff : ∀ q, g q = ca ↔ q = qa := fun q => by
      rw [← hqa]
      exact hg.eq_iff
    have hM : (h * (1 + Matrix.single cb ca t)).submatrix f g
        = h.submatrix f g * (1 + Matrix.single qb qa t) := by
      ext p q
      simp only [Matrix.submatrix_apply, mul_transv_apply, hqb, hiff]
    have h1 : (1 + Matrix.single qb qa t : Matrix (Fin k) (Fin k) ℂ) = Matrix.transvection qb qa t :=
      rfl
    rw [hM, Matrix.det_mul, h1, Matrix.det_transvection_of_ne qb qa hq t, mul_one]
  · congr 1
    ext p q
    have hq : g q ≠ ca := fun hh => hca ⟨q, hh⟩
    simp only [Matrix.submatrix_apply, mul_transv_apply, hq, if_false, add_zero]

/- English proof (translation)
Unfold `minorIJ`. Use `split_ifs with e`. Apply `det_submatrix_mul_transvection_eq h t ca cb hne` to reduce the goal to its premises. Conclude with `(J.orderEmbOfFin _).injective`. Rewrite using `[Finset.range_orderEmbOfFin, Finset.mem_coe, Finset.mem_coe]`.

Conclude with `hJ`. Both sides reduce to the same expression.
-/
theorem minorIJ_transv {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N) (hne : ca ≠ cb)
    (I J : Finset (Fin N)) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · apply det_submatrix_mul_transvection_eq h t ca cb hne
    · exact (J.orderEmbOfFin _).injective
    · rw [Finset.range_orderEmbOfFin, Finset.mem_coe, Finset.mem_coe]
      exact hJ
  · rfl

/- English proof (translation)
Introduce `N j a b ca cb hjN hb hab hca hcb h t i hi I`. Apply `minorIJ_transv h t ca cb` to reduce the goal to its premises. Introduce `heq`. Use `congrArg Fin.val heq` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Unfold `lastCol at hca`. Establish `hi' : (i : ℕ) ≠ a` using `fun h' => hi (Fin.ext h')`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact.

Use `i.isLt` as an intermediate fact. Use `ca.isLt` as an intermediate fact. Use `cb.isLt` as an intermediate fact. Apply the tactic sequence `split_ifs at hca ⊢ <;> omega`.
-/
theorem minorIJ_other_step : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  intro N j a b ca cb hjN hb hab hca hcb h t i hi I
  apply minorIJ_transv h t ca cb
  · intro heq
    have := congrArg Fin.val heq
    omega
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold lastCol at hca
    have hi' : (i : ℕ) ≠ a := fun h' => hi (Fin.ext h')
    have := a.isLt
    have := b.isLt
    have := i.isLt
    have := ca.isLt
    have := cb.isLt
    split_ifs at hca ⊢ <;> omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther
