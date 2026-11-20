import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomPlace

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_extension (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (σ : K →+* ℂ) (ι : K →+* ℂ_[p]) :
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k := by
  have hmem : ∀ k, σ k ∈ TaylorLogMetric.Qbar := fun k =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom σ.toRatAlgHom)
  let σ' : K →+* TaylorLogMetric.Qbar := σ.codRestrict TaylorLogMetric.Qbar hmem
  let : Algebra K TaylorLogMetric.Qbar := σ'.toAlgebra
  let : Algebra K ℂ_[p] := ι.toAlgebra
  have : IsScalarTower ℚ K TaylorLogMetric.Qbar := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast, eq_ratCast, map_ratCast]
  have : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar := by
    convert algebraicClosure.isAlgebraic ℚ ℂ <;> first | rfl | exact Subsingleton.elim _ _
  have : Algebra.IsAlgebraic K TaylorLogMetric.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : TaylorLogMetric.Qbar →ₐ[K] ℂ_[p] := IsAlgClosed.lift
  refine ⟨f.toRingHom, fun k => ⟨hmem k, ?_⟩⟩
  unfold TaylorLogMetric.lamC
  rw [dif_pos (hmem k)]
  exact f.commutes k

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem norm_le_one_of_valuation (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖ι x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hint : ∀ y : 𝓞 K, ‖ι (y : K)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖ι x‖ * ‖ι ((d : 𝓞 K) : K)‖ = ‖ι (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖ι z‖) h
  have h3 := hint n
  nlinarith [norm_nonneg (ι x)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_rat_pow_den (r : ℚ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ^ r.den = 1 := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-r.num, ?_⟩
  have h : ((r.den : ℂ)) * (r : ℂ) = (r.num : ℂ) := by
    exact_mod_cast Rat.den_mul_eq_num r
  push_cast
  rw [← h]; ring

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem root_of_unity_norm {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) : z ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam z‖ = 1 := by
  have hmem : z ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) ?_)
    rw [hz]; exact isAlgebraic_one
  refine ⟨hmem, ?_⟩
  unfold TaylorLogMetric.lamC
  rw [dif_pos hmem]
  have h1 : (⟨z, hmem⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by simpa using hz)
  have h2 : ‖lam ⟨z, hmem⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem places : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 :=
  fun K _ _ p _ σ ι => ⟨exists_extension K p σ ι, norm_le_one_of_valuation K p ι,
    fun lam r => root_of_unity_norm lam r.den_ne_zero (exp_rat_pow_den r)⟩

end GlobalTheory.MomPlace
