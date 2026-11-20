import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffInLetters

noncomputable section

namespace GlobalTheory.LiftTypePrime.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta

section Integral

/- English proof (translation)
Establish `h : x ∈ (NormedField.valuation (K` using `C)).integer := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

/- English proof (translation)
Unfold `IntAt lamC`. Conclude with `⟨fun ⟨h, h1⟩ => ⟨h, by rwa [dif_pos h] at h1⟩, fun ⟨h, h1⟩ => ⟨h, by rwa [dif_pos h]⟩⟩`.
-/
theorem intAt_iff {x : ℂ} : IntAt lam x ↔ ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ ≤ 1 := by
  unfold IntAt lamC
  exact ⟨fun ⟨h, h1⟩ => ⟨h, by rwa [dif_pos h] at h1⟩, fun ⟨h, h1⟩ => ⟨h, by rwa [dif_pos h]⟩⟩

/- English proof (translation)
Take `⟨h, h1⟩` from `intAt_iff.1 hx`. Take `⟨h', h2⟩` from `intAt_iff.1 hy`. Use `intAt_iff.2 ⟨mul_mem h h', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖lam (⟨x, h⟩ * ⟨y, h'⟩)‖ ≤ 1`. Rewrite using `[map_mul, norm_mul]`.

Conclude with `mul_le_one₀ h1 (norm_nonneg _) h2`.
-/
theorem intAt_mul {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x * y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨mul_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ * ⟨y, h'⟩)‖ ≤ 1
  rw [map_mul, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2

/- English proof (translation)
Take `⟨h, h1⟩` from `intAt_iff.1 hx`. Take `⟨h', h2⟩` from `intAt_iff.1 hy`. Use `intAt_iff.2 ⟨add_mem h h', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖lam (⟨x, h⟩ + ⟨y, h'⟩)‖ ≤ 1`. Rewrite using `[map_add]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`.
-/
theorem intAt_add {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x + y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨add_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ + ⟨y, h'⟩)‖ ≤ 1
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

/- English proof (translation)
Establish `h : x ∈ Qbar` using `mem_algebraicClosure_iff'.2 hx.tower_top`. Use `intAt_iff.2 ⟨h, ?_⟩` and prove the remaining obligations. Establish `h1 : IsIntegral ℤ (⟨x, h⟩ : Qbar)` using `(isIntegral_algHom_iff ((algebraMap Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx`. Conclude with `norm_le_one_of_isIntegral (map_isIntegral_int lam h1)`.
-/
theorem intAt_of_isIntegral {x : ℂ} (hx : IsIntegral ℤ x) : IntAt lam x := by
  have h : x ∈ Qbar := mem_algebraicClosure_iff'.2 hx.tower_top
  refine intAt_iff.2 ⟨h, ?_⟩
  have h1 : IsIntegral ℤ (⟨x, h⟩ : Qbar) :=
    (isIntegral_algHom_iff ((algebraMap Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx
  exact norm_le_one_of_isIntegral (map_isIntegral_int lam h1)

/- English proof (translation)
The claim follows from `Finset.sum_induction f (IntAt lam) (fun _ _ => intAt_add) (intAt_of_isIntegral isIntegral_zero) h`.
-/
theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntAt lam (f i)) : IntAt lam (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt lam) (fun _ _ => intAt_add) (intAt_of_isIntegral isIntegral_zero) h

end Integral

/- English proof (translation)
Establish `h' : (n : ℂ) * (x : ℂ) = m` using `by exact_mod_cast h`. Use `IsIntegral.of_pow (n := 2 * n) (by omega) ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul]`. Establish `: ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ)) = ((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)`. Use `push_cast`.

Take the linear combination `(2 * (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) * h'`. Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Conclude with `isIntegral_one`.
-/
theorem isIntegral_exp (k : ℤ) (x : ℝ) (n : ℕ) (hn : 0 < n) (m : ℤ) (h : (n : ℝ) * x = m) :
    IsIntegral ℤ (Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ))) := by
  have h' : (n : ℂ) * (x : ℂ) = m := by exact_mod_cast h
  refine IsIntegral.of_pow (n := 2 * n) (by omega) ?_
  rw [← Complex.exp_nat_mul]
  have : ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ)) =
      ((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (2 * (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) * h'
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
  exact isIntegral_one

variable {D : D7} {N N' : ℕ}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty]`. Conclude with `GlobalTheory.ThetaConj.taylor_zero D α`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`.

Rewrite using `[← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]`. Conclude with `GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α`.
-/
theorem taylor_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

/- English proof (translation)
Unfold `applyAt0`. Simplify using `only [taylor_sum s c f hf, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring`.
-/
theorem applyAt0_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (P : MvPolynomial (Idx D N N') ℂ) :
    applyAt0 D P (fun z => ∑ i ∈ s, c i * f i z) = ∑ i ∈ s, c i * applyAt0 D P (f i) := by
  unfold applyAt0
  simp only [taylor_sum s c f hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring

end GlobalTheory.LiftTypePrime.Jets

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta Jets

end GlobalTheory.LiftTypePrime

end
