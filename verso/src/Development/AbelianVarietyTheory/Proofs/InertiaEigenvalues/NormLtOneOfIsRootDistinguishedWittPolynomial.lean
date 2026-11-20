import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.RootLt

open Polynomial

/- English proof (translation)
Establish `hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a))`. Rewrite using `[span_teich]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨z, rfl⟩` from `hx`. Use `set ω := GlobalTheory.TameFrob.iotaO l a (WittVector.teichmuller l z)`. Establish `hω : ω ^ l ^ a = ω`. Simplify using `only [ω]`. Rewrite using `[← map_pow, ← map_pow, Fq.pow_card]`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h2 : 1 < l ^ a` using `Nat.one_lt_pow (NeZero.ne a) (Fact.out : l.Prime).one_lt`. Establish `h3 : ‖ω‖ ^ 1 < ‖ω‖ ^ l ^ a` using `pow_lt_pow_right₀ h h2`. Rewrite `h3` using `[pow_one, ← norm_pow, hω]`.

Conclude with `lt_irrefl _ h3`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`.

Consider the case `smul c x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, GlobalTheory.TameFrob.iotaO_algebraMap, norm_mul]`. Establish `hc : ‖algebraMap ℚ_[l] (Om l) (c : ℚ_[l])‖ ≤ 1` using `(PadicAlgCl.norm_extends l (c : ℚ_[l])).le.trans c.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_iotaO_le_one (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ‖GlobalTheory.TameFrob.iotaO l a w‖ ≤ 1 := by
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    set ω := GlobalTheory.TameFrob.iotaO l a (WittVector.teichmuller l z)
    have hω : ω ^ l ^ a = ω := by
      simp only [ω]
      rw [← map_pow, ← map_pow, Fq.pow_card]
    by_contra h
    push_neg at h
    have h2 : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (Fact.out : l.Prime).one_lt
    have h3 : ‖ω‖ ^ 1 < ‖ω‖ ^ l ^ a := pow_lt_pow_right₀ h h2
    rw [pow_one, ← norm_pow, hω] at h3
    exact lt_irrefl _ h3
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul, GlobalTheory.TameFrob.iotaO_algebraMap, norm_mul]
    have hc : ‖algebraMap ℚ_[l] (Om l) (c : ℚ_[l])‖ ≤ 1 :=
      (PadicAlgCl.norm_extends l (c : ℚ_[l])).le.trans c.2
    calc _ ≤ 1 * 1 := mul_le_mul hc hx (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/- English proof (translation)
Introduce `l _ a _ P hP hdiv x hx`. Use `set d := P.natDegree with hd`. Break down `Nat.eq_zero_or_pos d with h0 | hpos` into its components or cases. Establish `: P = 1` using `Polynomial.eq_one_of_monic_natDegree_zero hP h0`. Rewrite `hx` using `[this, Polynomial.map_one]`.

Simplify using `[Polynomial.IsRoot] at hx`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `hlpos : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Establish `hnl : ‖GlobalTheory.TameFrob.iotaO l a (l : Wq l a)‖ = (l : ℝ)⁻¹`. Rewrite using `[map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]`. Establish `hcoef : ∀ i < d, ‖GlobalTheory.TameFrob.iotaO l a (P.coeff i)‖ ≤ (l : ℝ)⁻¹`. Introduce `i hi`. Take `⟨c, hc⟩` from `hdiv i hi`.

Rewrite using `[hc, map_mul, norm_mul, hnl]`. Combine the equalities or inequalities in the displayed calculation. Establish `hxd : (1 : ℝ) ≤ ‖x‖ ^ d` using `one_le_pow₀ hge`. Establish `heq : x ^ d + ∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i = 0`. Establish `h` using `hx`.

Rewrite `h` using `[Polynomial.IsRoot, hP.as_sum]`. Simplify `h` using `[Polynomial.eval_finset_sum, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul]`. Establish `hsum : ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_range.1 hi`.

Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_mul (hcoef i hi') (pow_le_pow_right₀ hge hi'.le) (by positivity) (by positivity)`. Establish `hxeq : x ^ d = -∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i` using `eq_neg_of_add_eq_zero_left heq`. Establish `h1 : ‖x‖ ^ d ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : (l : ℝ)⁻¹ * ‖x‖ ^ d < ‖x‖ ^ d`. Establish `: (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `lt_irrefl _ (h1.trans_lt h2)`.
-/
theorem norm_lt_one_of_isRoot : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  intro l _ a _ P hP hdiv x hx
  set d := P.natDegree with hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · have : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    rw [this, Polynomial.map_one] at hx
    simp [Polynomial.IsRoot] at hx
  by_contra hge
  push_neg at hge
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

  have hnl : ‖GlobalTheory.TameFrob.iotaO l a (l : Wq l a)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hcoef : ∀ i < d, ‖GlobalTheory.TameFrob.iotaO l a (P.coeff i)‖ ≤ (l : ℝ)⁻¹ := by
    intro i hi
    obtain ⟨c, hc⟩ := hdiv i hi
    rw [hc, map_mul, norm_mul, hnl]
    calc _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left (norm_iotaO_le_one l a c) (by positivity)
      _ = _ := mul_one _
  have hxd : (1 : ℝ) ≤ ‖x‖ ^ d := one_le_pow₀ hge

  have heq : x ^ d + ∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i = 0 := by
    have h := hx
    rw [Polynomial.IsRoot, hP.as_sum] at h
    simpa [Polynomial.eval_finset_sum, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum,
      Polynomial.map_mul] using h
  have hsum : ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hcoef i hi') (pow_le_pow_right₀ hge hi'.le) (by positivity) (by positivity)
  have hxeq : x ^ d = -∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left heq
  have h1 : ‖x‖ ^ d ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    calc ‖x‖ ^ d = ‖x ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ := by rw [hxeq, norm_neg]
      _ ≤ _ := hsum
  have h2 : (l : ℝ)⁻¹ * ‖x‖ ^ d < ‖x‖ ^ d := by
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    nlinarith
  exact lt_irrefl _ (h1.trans_lt h2)

end GlobalTheory.RootLt
