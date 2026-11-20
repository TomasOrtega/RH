import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

/- English proof (translation)
Use `le_antisymm (fun y hy => (I.L_dual y).2 fun z hz => ?_) (GlobalTheory.Count.Test.le_lamX_one I)` and prove the remaining obligations. Conclude with `((GlobalTheory.PointLattice.lamX_selfDual I (1, 1)).2.2.2.1 y).1 hy z (GlobalTheory.Count.Test.le_lamX_one I hz)`.
-/
theorem lamX_one (I : AutInst) : lamX I (1, 1) = I.L := by
  refine le_antisymm (fun y hy => (I.L_dual y).2 fun z hz => ?_) (GlobalTheory.Count.Test.le_lamX_one I)
  exact ((GlobalTheory.PointLattice.lamX_selfDual I (1, 1)).2.2.2.1 y).1 hy z (GlobalTheory.Count.Test.le_lamX_one I hz)

/- English proof (translation)
Establish `: (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps (fun _ => true) y ≤ t}, gauss y) =ᶠ[nhds (sgn ℝ false)] fun _ => 0`. Establish `h : Set.Iio (0 : ℝ) ∈ nhds (sgn ℝ false)` using `Iio_mem_nhds (by simp [sgn])`. Use `filter_upwards [h] with t ht`. Establish `: {y : Fin n → ℂ | qEps (fun _ => true) y ≤ t} = ∅`. Use extensionality with `y`.

Establish `: 0 ≤ qEps (fun _ => true) y` using `Finset.sum_nonneg fun i _ => by simp`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]`. Conclude with `lt_of_lt_of_le ht this`. Simplify using `[this]`. Rewrite using `[gaussDens, this.deriv_eq]`.

Simplify using the standard rewrite rules.
-/
theorem gaussDens_definite (n : ℕ) : gaussDens (fun _ : Fin n => true) (sgn ℝ false) = 0 := by
  have : (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps (fun _ => true) y ≤ t}, gauss y) =ᶠ[nhds (sgn ℝ false)]
      fun _ => 0 := by
    have h : Set.Iio (0 : ℝ) ∈ nhds (sgn ℝ false) := Iio_mem_nhds (by simp [sgn])
    filter_upwards [h] with t ht
    have : {y : Fin n → ℂ | qEps (fun _ => true) y ≤ t} = ∅ := by
      ext y
      have : 0 ≤ qEps (fun _ => true) y := Finset.sum_nonneg fun i _ => by simp
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht this
    simp [this]
  rw [gaussDens, this.deriv_eq]; simp

/- English proof (translation)
Establish `h1 : ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y = ∫ z : ℂ, (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) ‖z‖`. Establish `hm : MeasurableSet {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}`. Use `measurableSet_le ?_ measurable_const` and prove the remaining obligations. Unfold `qEps`. Use `fun_prop`.

Rewrite using `[← integral_indicator hm, ← (volume_preserving_funUnique (Fin 1) ℂ).integral_comp']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [Set.indicator, Set.mem_setOf_eq, Set.mem_Iic, qEps, gauss, Real.le_sqrt (norm_nonneg _) ht.le]`. Simplify using the standard rewrite rules. Rewrite using `[h1, integral_fun_norm_addHaar]`.

Establish `h2 : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) y = (1 - Real.exp (-t)) / 2`. Establish `: (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) y) = (Set.Iic (Real.sqrt t)).indicator (fun r => r * Real.exp (-r ^ 2))`. Apply the tactic sequence `funext y; simp only [Set.indicator]; split_ifs <;> simp`. Rewrite using `[this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]`. Establish `hd : ∀ x ∈ Set.uIcc 0 (Real.sqrt t), HasDerivAt (fun r : ℝ => -Real.exp (-r ^ 2) / 2) (x * Real.exp (-x ^ 2)) x`.

Introduce `x _`. Use `(((hasDerivAt_pow 2 x).neg.exp).neg).div_const 2` as an intermediate fact. Use `HasDerivAt.congr_deriv this ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]`. Rewrite using `[Real.sq_sqrt ht.le]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Simplify using `[Measure.real, Complex.volume_ball]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem disc_integral {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y = Real.pi * (1 - Real.exp (-t)) := by
  have h1 : ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y =
      ∫ z : ℂ, (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) ‖z‖ := by
    have hm : MeasurableSet {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t} := by
      refine measurableSet_le ?_ measurable_const
      unfold qEps; fun_prop
    rw [← integral_indicator hm, ← (volume_preserving_funUnique (Fin 1) ℂ).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq, Set.mem_Iic, qEps, gauss, Real.le_sqrt (norm_nonneg _) ht.le]
    simp
  rw [h1, integral_fun_norm_addHaar]
  have h2 : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) y = (1 - Real.exp (-t)) / 2 := by
    have : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) y) =
        (Set.Iic (Real.sqrt t)).indicator (fun r => r * Real.exp (-r ^ 2)) := by
      funext y; simp only [Set.indicator]; split_ifs <;> simp
    rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
      ← intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]
    have hd : ∀ x ∈ Set.uIcc 0 (Real.sqrt t),
        HasDerivAt (fun r : ℝ => -Real.exp (-r ^ 2) / 2) (x * Real.exp (-x ^ 2)) x := by
      intro x _
      have := (((hasDerivAt_pow 2 x).neg.exp).neg).div_const 2
      refine HasDerivAt.congr_deriv this ?_
      simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [Real.sq_sqrt ht.le]; simp; ring
  rw [h2]
  simp [Measure.real, Complex.volume_ball]
  ring

/- English proof (translation)
Establish `: (fun t : ℝ => ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y) =ᶠ[nhds 1] fun t => Real.pi * (1 - Real.exp (-t))` using `by filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with t ht using disc_integral ht`. Establish `hs : sgn ℝ true = 1` using `by simp [sgn]`. Rewrite using `[gaussDens, hs, this.deriv_eq]`. Use `(((hasDerivAt_id (1 : ℝ)).neg.exp).const_sub 1).const_mul Real.pi` as an intermediate fact. Simplify using `using this.deriv`.
-/
theorem gaussDens_circle : gaussDens (fun _ : Fin 1 => true) (sgn ℝ true) = Real.pi * Real.exp (-1) := by
  have : (fun t : ℝ => ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y) =ᶠ[nhds 1]
      fun t => Real.pi * (1 - Real.exp (-t)) := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with t ht using disc_integral ht
  have hs : sgn ℝ true = 1 := by simp [sgn]
  rw [gaussDens, hs, this.deriv_eq]
  have := (((hasDerivAt_id (1 : ℝ)).neg.exp).const_sub 1).const_mul Real.pi
  simpa using this.deriv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Unfold `IsPerpInst`. Rewrite using `[lamX_one]`. Use `⟨fun _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ⬝ᵥ (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : E))) = sgn E s`. Simplify using `[signMat, sgn, dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal]`.

Use `show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ᵥ* (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)) = 0`. Use function extensionality and compare the values at `j`. Simplify using `[signMat, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_mul, (Fin.succ_ne_zero j).symm]`. Use `show (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)ᴴ * signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) = (signMat E ε).map (RingEquiv.refl E)`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.map_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Use `show (Pi.single (0 : Fin (n + 1)) (1 : E)) ∈ intLat E (n + 1)`. Conclude with `Submodule.subset_span ⟨0, by simp⟩`. Use `show ∀ y : Fin n → E, y ∈ intLat E n ↔ (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ y ∈ intLat E (n + 1)`. Introduce `y`.

Establish `e : (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ (y : Fin n → E) = (Fin.cons 0 y : Fin (n + 1) → E)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[Matrix.mulVec, dotProduct, (Fin.succ_ne_zero _).symm]`. Simplify using `[Matrix.mulVec, dotProduct]`.

Rewrite using `[e, mem_intLat, mem_intLat, Fin.forall_fin_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Conclude with `⟨fun h => ⟨zero_mem _, h⟩, fun h => h.2⟩`.
-/
theorem isPerpInst_ofSigns (cm : Formalism.BasicNotions.CMData F E) {n : ℕ} (s : Bool) (ε : Fin n → Bool) :
    IsPerpInst (ofSigns cm (Fin.cons s ε : Fin (n + 1) → Bool)) (ofSigns cm ε) (RingEquiv.refl E) s
      (Pi.single (0 : Fin (n + 1)) (1 : E)) (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) 1 := by
  unfold IsPerpInst
  rw [lamX_one]
  refine ⟨fun _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ⬝ᵥ (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : E))) = sgn E s
    simp [signMat, sgn, dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal]
  · show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ᵥ* (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)) = 0
    funext j
    simp [signMat, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_mul, (Fin.succ_ne_zero j).symm]
  · show (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)ᴴ * signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) = (signMat E ε).map (RingEquiv.refl E)
    ext i j
    rw [Matrix.mul_apply]
    simp only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.map_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · show (Pi.single (0 : Fin (n + 1)) (1 : E)) ∈ intLat E (n + 1)
    exact Submodule.subset_span ⟨0, by simp⟩
  · show ∀ y : Fin n → E, y ∈ intLat E n ↔ (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ y ∈ intLat E (n + 1)
    intro y
    have e : (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ (y : Fin n → E)
        = (Fin.cons 0 y : Fin (n + 1) → E) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, (Fin.succ_ne_zero _).symm]
      · simp [Matrix.mulVec, dotProduct]
    rw [e, mem_intLat, mem_intLat, Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨fun h => ⟨zero_mem _, h⟩, fun h => h.2⟩

/- English proof (translation)
Take `⟨I, -⟩` from `exists_signature 0 0`. Conclude with `⟨_, _, _, _, _, _, rfl, isPerpInst_ofSigns I.cm s (fun _ : Fin n => true)⟩`.
-/
theorem exists_isPerpInst (n : ℕ) (s : Bool) :
    ∃ (I I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf),
      I.n = n + 1 ∧ IsPerpInst I I' e s x A xf := by
  obtain ⟨I, -⟩ := exists_signature 0 0
  exact ⟨_, _, _, _, _, _, rfl, isPerpInst_ofSigns I.cm s (fun _ : Fin n => true)⟩

/- English proof (translation)
Introduce `h0`. Use `ENNReal.tsum_eq_zero.1 h0 ⟨x, h.2.2.2.2.2.1, h.2.2.1⟩` as an intermediate fact. Rewrite `this` using `[ENNReal.ofReal_eq_zero]`. Conclude with `absurd this (not_le.2 (Finset.prod_pos fun v _ => gauss_pos _))`.
-/
theorem gaussSum_ne_zero {I I' : AutInst} {e : I'.E ≃+* I.E} {s : Bool} {x : Fin I.n → I.E}
    {A : Matrix (Fin I.n) (Fin I'.n) I.E} {xf : I.Gf} (h : IsPerpInst I I' e s x A xf) :
    gaussSum I (sgn I.E s) (1, xf) ≠ 0 := by
  intro h0
  have := ENNReal.tsum_eq_zero.1 h0 ⟨x, h.2.2.2.2.2.1, h.2.2.1⟩
  rw [ENNReal.ofReal_eq_zero] at this
  exact absurd this (not_le.2 (Finset.prod_pos fun v _ => gauss_pos _))

/- English proof (translation)
Unfold `meanConst Formalism.HermitianLatticesTheory.massRatioRightSide`. Establish `h2 : (0 : ℝ) < 2 * Formalism.HermitianLatticesTheory.vInv E` using `by positivity`. Establish `hs : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2)`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2.le]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hp : 0 < (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2)` using `Real.rpow_pos_of_pos h2 _`. Establish `hf : (0 : ℝ) < ((M - 1).factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Use `Real.pi_pos` as an intermediate fact. Rewrite using `[hs]`.

Simplify using `only [mul_pow, div_pow, pow_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem const_agree (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) (hv : 0 < Formalism.HermitianLatticesTheory.vInv E)
    (hL : Formalism.HermitianLatticesTheory.lValEta E M ≠ 0) :
    meanConst E M * Formalism.HermitianLatticesTheory.massRatioRightSide E M *
      (2 ^ M * Real.pi ^ M / ((M - 1).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg E = 2 ^ (M * Formalism.HermitianLatticesTheory.fDeg E) := by
  unfold meanConst Formalism.HermitianLatticesTheory.massRatioRightSide
  have h2 : (0 : ℝ) < 2 * Formalism.HermitianLatticesTheory.vInv E := by positivity
  have hs : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) =
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2.le]; congr 1; ring
  have hp : 0 < (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) := Real.rpow_pos_of_pos h2 _
  have hf : (0 : ℝ) < ((M - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have := Real.pi_pos
  rw [hs]
  simp only [mul_pow, div_pow, pow_mul]
  field_simp

end GlobalTheory.GaussMean.Test
