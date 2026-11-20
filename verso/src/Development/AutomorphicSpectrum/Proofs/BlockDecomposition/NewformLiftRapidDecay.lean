import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Automorphic.AdelicGLn (integralFiniteGL FiniteAdelicGL prodEquiv)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate MatrixGroups ModularForm
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.NewformLiftDecay

/- English proof (translation)
Establish `e : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z`. Simplify using `[HeightOneSpectrum.algebraMap_adicCompletion]`. Rewrite using `[← e]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z`.
-/
theorem valued_algebraMap' {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (z : K) :
    Valued.v (algebraMap K (v.adicCompletion K) z) = v.valuation K z := by
  have e : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z := by
    simp [HeightOneSpectrum.algebraMap_adicCompletion]
  rw [← e]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Use `haveI : (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `(ValuativeRel.isEquiv (ValuativeRel.valuation (Qv v)) (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one`.
-/
theorem mem_O_iff (v : Pl) (x : Qv v) : x ∈ 𝒪[Qv v] ↔ x ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Qv v))
    (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

/- English proof (translation)
Establish `h1 : (((e : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) : Qv v) ∈ 𝒪[Qv v]` using `(mem_O_iff v _).2 (e : v.adicCompletionIntegers ℚ).2`. Establish `h2 : ((((e⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) : Qv v) ∈ 𝒪[Qv v]` using `(mem_O_iff v _).2 ((e⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ).2`. Establish `h3` using `congrArg (Subtype.val) e.mul_inv`. Establish `h4` using `congrArg (Subtype.val) e.inv_mul`. Conclude with `ord_unit (K := Qv v) (⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext h3, Subtype.ext h4⟩ : 𝒪[Qv v]ˣ)`.
-/
theorem ord_int_unit (v : Pl) (e : (v.adicCompletionIntegers ℚ)ˣ) :
    ord (((e : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) : Qv v) = 0 := by
  have h1 : (((e : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) : Qv v) ∈ 𝒪[Qv v] :=
    (mem_O_iff v _).2 (e : v.adicCompletionIntegers ℚ).2
  have h2 : ((((e⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) : Qv v) ∈ 𝒪[Qv v] :=
    (mem_O_iff v _).2 ((e⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ).2
  have h3 := congrArg (Subtype.val) e.mul_inv
  have h4 := congrArg (Subtype.val) e.inv_mul
  exact ord_unit (K := Qv v) (⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext h3, Subtype.ext h4⟩ : 𝒪[Qv v]ˣ)

/- English proof (translation)
Establish `h1 : ((pOf v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal` using `Ideal.absNorm_mem v.asIdeal`. Take `⟨m, rfl⟩` from `hv`. Establish `h2 : ((pOf v * m : ℕ) : 𝓞 ℚ) ∈ v.asIdeal`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ h1`.

Establish `h3` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := ℚ) v _).2 h2`. Establish `h6` using `valued_algebraMap' v (((pOf v * m : ℕ)) : ℚ)`. Rewrite `h6` using `[map_natCast]`. Rewrite using `[h6]`. Simplify using `using h3`.
-/
theorem val_nat_lt_one (v : Pl) (N : ℕ) (hv : pOf v ∣ N) :
    Valued.v ((N : Qv v)) < (1 : WithZero (Multiplicative ℤ)) := by
  have h1 : ((pOf v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  obtain ⟨m, rfl⟩ := hv
  have h2 : ((pOf v * m : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    push_cast
    exact Ideal.mul_mem_right _ _ h1
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := ℚ) v _).2 h2
  have h6 := valued_algebraMap' v (((pOf v * m : ℕ)) : ℚ)
  rw [map_natCast] at h6
  rw [h6]
  simpa using h3

/- English proof (translation)
Take `⟨hi, t, ht, hc⟩` from `hu`. Take `⟨h1, h2⟩` from `(GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff ℚ 2).1 hi`. Use `set d : Qv v := (u : Matrix (Fin 2) (Fin 2) Af) 1 1 v with hd`. Use `set c : Qv v := (u : Matrix (Fin 2) (Fin 2) Af) 1 0 v with hcdef`. Use `set x : Qv v := ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) Af) 1 1 v with hx`.

Use `set y : Qv v := ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) Af) 0 1 v with hy`. Establish `hdi : Valued.v d ≤ 1` using `h1 1 1 v`. Establish `hxi : Valued.v x ≤ 1` using `h2 1 1 v`. Establish `hyi : Valued.v y ≤ 1` using `h2 0 1 v`. Establish `hti : Valued.v (t v) ≤ 1` using `ht v`.

Establish `hrel : c * y + d * x = 1`. Establish `h` using `congrArg (fun M : Matrix (Fin 2) (Fin 2) Af => adeleAt v (M 1 1)) (Units.mul_inv u)`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Matrix.one_apply_eq, map_one] at h`. Conclude with `h`. Establish `hcv : c = (N : Qv v) * t v`.

Establish `h` using `congrArg (adeleAt v) hc`. Simplify using `only [map_mul, map_natCast] at h`. Conclude with `h`. Establish `hclt : Valued.v (c * y) < 1`. Rewrite using `[hcv, map_mul, map_mul]`.

Conclude with `lt_of_le_of_lt ((mul_le_of_le_one_right' hyi).trans (mul_le_of_le_one_right' hti)) (val_nat_lt_one v N hv)`. Establish `hone : Valued.v (d * x) = 1`. Establish `: d * x = 1 - c * y` using `by rw [← hrel]; ring`. Rewrite using `[this]`. Conclude with `Valuation.map_one_sub_of_lt _ hclt`.

Establish `hd1 : Valued.v d = 1`. Use `le_antisymm hdi (not_lt.1 fun h => ?_)` and prove the remaining obligations. Establish `h2 : Valued.v (d * x) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hxi) h`.

Rewrite `h2` using `[hone]`. Conclude with `lt_irrefl _ h2`. Establish `hd0 : d ≠ 0`. Introduce `h`. Rewrite `hd1` using `[h, map_zero]`.

Conclude with `zero_ne_one hd1`. Use `⟨⟨⟨d, hd1.le⟩, ⟨d⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v d⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hd1, inv_one]`.
-/
theorem unit_entry {N : ℕ} [NeZero N] {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (v : Pl) (hv : pOf v ∣ N) :
    ∃ e : (v.adicCompletionIntegers ℚ)ˣ, (((e : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) : Qv v) =
      (glAt v u : Matrix (Fin 2) (Fin 2) (Qv v)) 1 1 := by
  obtain ⟨hi, t, ht, hc⟩ := hu
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff ℚ 2).1 hi
  set d : Qv v := (u : Matrix (Fin 2) (Fin 2) Af) 1 1 v with hd
  set c : Qv v := (u : Matrix (Fin 2) (Fin 2) Af) 1 0 v with hcdef
  set x : Qv v := ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) Af) 1 1 v with hx
  set y : Qv v := ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) Af) 0 1 v with hy
  have hdi : Valued.v d ≤ 1 := h1 1 1 v
  have hxi : Valued.v x ≤ 1 := h2 1 1 v
  have hyi : Valued.v y ≤ 1 := h2 0 1 v
  have hti : Valued.v (t v) ≤ 1 := ht v
  have hrel : c * y + d * x = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) Af => adeleAt v (M 1 1)) (Units.mul_inv u)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Matrix.one_apply_eq, map_one] at h
    exact h
  have hcv : c = (N : Qv v) * t v := by
    have h := congrArg (adeleAt v) hc
    simp only [map_mul, map_natCast] at h
    exact h
  have hclt : Valued.v (c * y) < 1 := by
    rw [hcv, map_mul, map_mul]
    exact lt_of_le_of_lt ((mul_le_of_le_one_right' hyi).trans (mul_le_of_le_one_right' hti)) (val_nat_lt_one v N hv)
  have hone : Valued.v (d * x) = 1 := by
    have : d * x = 1 - c * y := by rw [← hrel]; ring
    rw [this]
    exact Valuation.map_one_sub_of_lt _ hclt
  have hd1 : Valued.v d = 1 := by
    refine le_antisymm hdi (not_lt.1 fun h => ?_)
    have h2 : Valued.v (d * x) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hxi) h
    rw [hone] at h2
    exact lt_irrefl _ h2
  have hd0 : d ≠ 0 := by
    intro h; rw [h, map_zero] at hd1; exact zero_ne_one hd1
  refine ⟨⟨⟨d, hd1.le⟩, ⟨d⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  change Valued.v d⁻¹ ≤ 1
  rw [map_inv₀, hd1, inv_one]

/- English proof (translation)
Apply the tactic sequence `let e : ∀ v : Pl, (v.adicCompletionIntegers ℚ)ˣ := fun v => if h : pOf v ∣ N then (unit_entry hu v h).choose else 1`. Use `⟨IdeleGroup.toFinite ℚ (IdeleGroup.ofIntegerUnits 1 e), fun v => ord_int_unit v (e v), fun v hv => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have h : e v = (unit_entry hu v hv).choose := dif_pos hv`. Apply the tactic sequence `have h2 := (unit_entry hu v hv).choose_spec`. Rewrite `h2` using `[← h]`.

Conclude with `h2`.
-/
theorem exists_level_idele (N : ℕ) [NeZero N] (u : FiniteAdelicGL ℚ 2) (hu : u ∈ Gamma0Level N) :
    ∃ d : Afˣ, (∀ v : Pl, ord (lf v d : Qv v) = 0) ∧
      ∀ v : Pl, pOf v ∣ N → (lf v d : Qv v) = (glAt v u : Matrix (Fin 2) (Fin 2) (Qv v)) 1 1 := by
  classical
  let e : ∀ v : Pl, (v.adicCompletionIntegers ℚ)ˣ := fun v =>
    if h : pOf v ∣ N then (unit_entry hu v h).choose else 1
  refine ⟨IdeleGroup.toFinite ℚ (IdeleGroup.ofIntegerUnits 1 e), fun v => ord_int_unit v (e v), fun v hv => ?_⟩
  have h : e v = (unit_entry hu v hv).choose := dif_pos hv
  have h2 := (unit_entry hu v hv).choose_spec
  rw [← h] at h2
  exact h2

open UpperHalfPlane in
/- English proof (translation)
Establish `hd : (g * borelGL z).det.val = g.det.val * z.im`. Rewrite using `[map_mul, Units.val_mul, det_borelGL]`. Establish `hs : (g * borelGL z) • UpperHalfPlane.I = g • z`. Rewrite using `[mul_smul, borelGL_smul_I]`. Establish `hj : denom (g * borelGL z) (UpperHalfPlane.I : ℂ) = denom g (z : ℂ)`.

Rewrite using `[denom_mul_of_det_pos _ (det_borelGL_pos z), borelGL_smul_I, denom_borelGL, mul_one]`. Rewrite using `[archLift, hd, hs, hj, ModularForm.slash_apply, σ_of_det_pos hD, abs_of_pos hD]`. Establish `hDc : (g.det.val : ℂ) ≠ 0` using `by exact_mod_cast hD.ne'`. Establish `h : (g.det.val : ℂ) ^ (k - 1) * (g.det.val : ℂ) ^ (1 - k) = 1`. Rewrite using `[← zpow_add₀ hDc]`.

Simplify using the standard rewrite rules. Take the linear combination `(-((Real.sqrt (g.det.val * z.im) : ℂ) ^ k * f (g • z) * denom g (z : ℂ) ^ (-k))) * h`.
-/
theorem archLift_translate (k : ℤ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hD : 0 < g.det.val) (z : ℍ) :
    archLift k f (g * borelGL z) =
      (Real.sqrt (g.det.val * z.im) : ℂ) ^ k * (f ∣[k] g) z * ((g.det.val : ℂ) ^ (1 - k)) := by
  have hd : (g * borelGL z).det.val = g.det.val * z.im := by
    rw [map_mul, Units.val_mul, det_borelGL]
  have hs : (g * borelGL z) • UpperHalfPlane.I = g • z := by
    rw [mul_smul, borelGL_smul_I]
  have hj : denom (g * borelGL z) (UpperHalfPlane.I : ℂ) = denom g (z : ℂ) := by
    rw [denom_mul_of_det_pos _ (det_borelGL_pos z), borelGL_smul_I, denom_borelGL, mul_one]
  rw [archLift, hd, hs, hj, ModularForm.slash_apply, σ_of_det_pos hD, abs_of_pos hD]
  have hDc : (g.det.val : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have h : (g.det.val : ℂ) ^ (k - 1) * (g.det.val : ℂ) ^ (1 - k) = 1 := by
    rw [← zpow_add₀ hDc]; simp
  linear_combination (-((Real.sqrt (g.det.val * z.im) : ℂ) ^ k * f (g • z) * denom g (z : ℂ) ^ (-k))) * h

/- English proof (translation)
Use `⟨n.factorial / c ^ n, by positivity, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h` using `Real.pow_div_factorial_le_exp (c * y) (by positivity) n`. Rewrite `h` using `[div_le_iff₀ (by positivity)]`. Rewrite using `[le_div_iff₀ (by positivity), neg_mul, Real.exp_neg]`. Establish `hE` using `Real.exp_pos (c * y)`.

Rewrite `h` using `[mul_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_mul_exp_le (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y → y ^ n * Real.exp (-c * y) ≤ K := by
  refine ⟨n.factorial / c ^ n, by positivity, fun y hy => ?_⟩
  have h := Real.pow_div_factorial_le_exp (c * y) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg]
  have hE := Real.exp_pos (c * y)
  rw [mul_pow] at h
  calc y ^ n * (Real.exp (c * y))⁻¹ * c ^ n = (c ^ n * y ^ n) * (Real.exp (c * y))⁻¹ := by ring
    _ ≤ (Real.exp (c * y) * n.factorial) * (Real.exp (c * y))⁻¹ := by gcongr
    _ = n.factorial := by field_simp

open UpperHalfPlane Asymptotics in
/- English proof (translation)
Take `⟨D0, hD0⟩` from `hO.bound`. Rewrite `hD0` using `[atImInfty, eventually_comap, eventually_atTop]`. Take `⟨A₀, hA⟩` from `hD0`. Use `set A := max A₀ 1 with hAdef`. Establish `hA1 : 1 ≤ A` using `le_max_right _ _`.

Take `⟨K, hK0, hK⟩` from `pow_mul_exp_le c hc (k.natAbs + M)`. Use `⟨|D0| * K + |C₁| * A ^ M, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hy : 0 < z.im` using `z.im_pos`. Establish `hsq1 : 1 ≤ Real.sqrt z.im` using `Real.one_le_sqrt.2 hz`. Establish `hsq0 : 0 < Real.sqrt z.im ^ k` using `zpow_pos (by linarith) _`.

Establish `hinv : 0 ≤ (z.im⁻¹) ^ M` using `by positivity`. Break down `le_total A z.im with h1 | h1` into its components or cases. Establish `h2` using `hA z.im ((le_max_left _ _).trans h1) z rfl`. Rewrite `h2` using `[Real.norm_of_nonneg (Real.exp_pos _).le]`. Establish `h4 : Real.sqrt z.im ≤ z.im`.

Rewrite using `[Real.sqrt_le_iff]; exact ⟨hy.le, by nlinarith⟩`. Establish `h3 : Real.sqrt z.im ^ k ≤ z.im ^ k.natAbs`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : ‖F z‖ ≤ |D0| * Real.exp (-c * z.im)` using `h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_add, inv_pow]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ |D0| * K * (z.im⁻¹) ^ M := by gcongr`. Conclude with `hK _ hy.le`. Use `_ ≤ _ := by gcongr`.

Establish `: 0 ≤ |C₁| * A ^ M` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Real.sqrt z.im ^ k * ‖F z‖ ≤ C₁`. Rewrite using `[sqrt_zpow_eq_rpow hy]`. Establish `hp : 0 < z.im ^ ((k : ℝ) / 2)` using `Real.rpow_pos_of_pos hy _`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : 1 ≤ A ^ M * (z.im⁻¹) ^ M`. Rewrite using `[← mul_pow]`. Conclude with `one_le_pow₀ (by rw [← div_eq_mul_inv]; exact (one_le_div hy).2 h1)`. Establish `h4 : 0 ≤ |D0| * K * (z.im⁻¹) ^ M` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem real_decay {F : ℍ → ℂ} {k : ℤ} {c C₁ : ℝ} (hc : 0 < c)
    (hO : F =O[atImInfty] fun τ => Real.exp (-c * τ.im))
    (hC : ∀ τ : ℍ, ‖F τ‖ ≤ C₁ / τ.im ^ ((k : ℝ) / 2)) (M : ℕ) :
    ∃ C : ℝ, ∀ z : ℍ, 1 ≤ z.im → Real.sqrt z.im ^ k * ‖F z‖ ≤ C * (z.im⁻¹) ^ M := by
  obtain ⟨D0, hD0⟩ := hO.bound
  rw [atImInfty, eventually_comap, eventually_atTop] at hD0
  obtain ⟨A₀, hA⟩ := hD0
  set A := max A₀ 1 with hAdef
  have hA1 : 1 ≤ A := le_max_right _ _
  obtain ⟨K, hK0, hK⟩ := pow_mul_exp_le c hc (k.natAbs + M)
  refine ⟨|D0| * K + |C₁| * A ^ M, fun z hz => ?_⟩
  have hy : 0 < z.im := z.im_pos
  have hsq1 : 1 ≤ Real.sqrt z.im := Real.one_le_sqrt.2 hz
  have hsq0 : 0 < Real.sqrt z.im ^ k := zpow_pos (by linarith) _
  have hinv : 0 ≤ (z.im⁻¹) ^ M := by positivity
  rcases le_total A z.im with h1 | h1
  · have h2 := hA z.im ((le_max_left _ _).trans h1) z rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    have h4 : Real.sqrt z.im ≤ z.im := by
      rw [Real.sqrt_le_iff]; exact ⟨hy.le, by nlinarith⟩
    have h3 : Real.sqrt z.im ^ k ≤ z.im ^ k.natAbs := by
      calc Real.sqrt z.im ^ k ≤ Real.sqrt z.im ^ ((k.natAbs : ℕ) : ℤ) :=
            zpow_le_zpow_right₀ hsq1 (by omega)
        _ = Real.sqrt z.im ^ k.natAbs := zpow_natCast _ _
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 _
    have h5 : ‖F z‖ ≤ |D0| * Real.exp (-c * z.im) :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    calc Real.sqrt z.im ^ k * ‖F z‖ ≤ z.im ^ k.natAbs * (|D0| * Real.exp (-c * z.im)) :=
          mul_le_mul h3 h5 (norm_nonneg _) (by positivity)
      _ = |D0| * (z.im ^ (k.natAbs + M) * Real.exp (-c * z.im)) * (z.im⁻¹) ^ M := by
          rw [pow_add, inv_pow]; field_simp
      _ ≤ |D0| * K * (z.im⁻¹) ^ M := by
          gcongr
          exact hK _ hy.le
      _ ≤ _ := by
          gcongr
          have : 0 ≤ |C₁| * A ^ M := by positivity
          linarith
  · have h2 : Real.sqrt z.im ^ k * ‖F z‖ ≤ C₁ := by
      rw [sqrt_zpow_eq_rpow hy]
      have hp : 0 < z.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hy _
      calc z.im ^ ((k : ℝ) / 2) * ‖F z‖ ≤ z.im ^ ((k : ℝ) / 2) * (C₁ / z.im ^ ((k : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hC z) hp.le
        _ = C₁ := by field_simp
    have h3 : 1 ≤ A ^ M * (z.im⁻¹) ^ M := by
      rw [← mul_pow]
      exact one_le_pow₀ (by rw [← div_eq_mul_inv]; exact (one_le_div hy).2 h1)
    have h4 : 0 ≤ |D0| * K * (z.im⁻¹) ^ M := by positivity
    calc _ ≤ C₁ := h2
      _ ≤ |C₁| := le_abs_self _
      _ ≤ |C₁| * (A ^ M * (z.im⁻¹) ^ M) := le_mul_of_one_le_right (abs_nonneg _) h3
      _ ≤ _ := by rw [add_mul]; linarith [mul_assoc |C₁| (A ^ M) ((z.im⁻¹) ^ M)]

open ConjAct Pointwise in
/- English proof (translation)
Establish `hD : 0 < (toReal γ).det.val`. Rewrite using `[det_toReal]`. Conclude with `hγ` after adjusting the coercions. Use `haveI hA : (ConjAct.toConjAct (toReal γ)⁻¹ • (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by`. Establish `h` using `Subgroup.IsArithmetic.conj (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) γ⁻¹`.

Establish `e : (γ⁻¹).map (Rat.castHom ℝ) = (toReal γ)⁻¹` using `map_inv toReal γ`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Take `⟨c, hc, hO⟩` from `ModularFormClass.exp_decay_atImInfty' (CuspForm.translate f (toReal γ)) (CuspFormClass.zero_at_infty (CuspForm.translate f (toReal γ)))`. Take `⟨C₁, hC₁⟩` from `CuspFormClass.exists_bound (CuspForm.translate f (toReal γ))`. Take `⟨C, hC⟩` from `real_decay hc hO hC₁ M`.

Establish `hDs : 0 < Real.sqrt (toReal γ).det.val` using `Real.sqrt_pos.2 hD`. Use `⟨Real.sqrt (toReal γ).det.val ^ k * (toReal γ).det.val ^ (1 - k) * C, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hF : (CuspForm.translate f (toReal γ) : UpperHalfPlane → ℂ) = (f : UpperHalfPlane → ℂ) ∣[k] toReal γ` using `rfl`. Rewrite using `[archLift_translate k _ _ hD z, norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hD.le, Real.sqrt_mul hD.le, mul_zpow, ← hF]`. Establish `h` using `hC z hz`.

Establish `hq : 0 < Real.sqrt (toReal γ).det.val ^ k * (toReal γ).det.val ^ (1 - k)` using `mul_pos (zpow_pos hDs _) (zpow_pos hD _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cusp_decay (k : ℤ) (N : ℕ) [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (γ : GL (Fin 2) ℚ)
    (hγ : 0 < (γ.det.val : ℚ)) (M : ℕ) :
    ∃ C : ℝ, ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖archLift k (f : UpperHalfPlane → ℂ) (toReal γ * borelGL z)‖ ≤ C * (z.im⁻¹) ^ M := by
  have hD : 0 < (toReal γ).det.val := by
    rw [det_toReal]; exact_mod_cast hγ
  haveI hA : (ConjAct.toConjAct (toReal γ)⁻¹ • (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) γ⁻¹
    have e : (γ⁻¹).map (Rat.castHom ℝ) = (toReal γ)⁻¹ := map_inv toReal γ
    rwa [e] at h
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_atImInfty' (CuspForm.translate f (toReal γ))
    (CuspFormClass.zero_at_infty (CuspForm.translate f (toReal γ)))
  obtain ⟨C₁, hC₁⟩ := CuspFormClass.exists_bound (CuspForm.translate f (toReal γ))
  obtain ⟨C, hC⟩ := real_decay hc hO hC₁ M
  have hDs : 0 < Real.sqrt (toReal γ).det.val := Real.sqrt_pos.2 hD
  refine ⟨Real.sqrt (toReal γ).det.val ^ k * (toReal γ).det.val ^ (1 - k) * C, fun z hz => ?_⟩
  have hF : (CuspForm.translate f (toReal γ) : UpperHalfPlane → ℂ) = (f : UpperHalfPlane → ℂ) ∣[k] toReal γ := rfl
  rw [archLift_translate k _ _ hD z, norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hD.le, Real.sqrt_mul hD.le, mul_zpow, ← hF]
  have h := hC z hz
  have hq : 0 < Real.sqrt (toReal γ).det.val ^ k * (toReal γ).det.val ^ (1 - k) :=
    mul_pos (zpow_pos hDs _) (zpow_pos hD _)
  calc _ = (Real.sqrt (toReal γ).det.val ^ k * (toReal γ).det.val ^ (1 - k)) *
        (Real.sqrt z.im ^ k * ‖(CuspForm.translate f (toReal γ)) z‖) := by ring
    _ ≤ _ := by rw [mul_assoc (_ * _) C]; exact mul_le_mul_of_nonneg_left h hq.le

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[dg2, pri, GroundTheory.Automorphic.AdelicGLn.diagonal, Matrix.GeneralLinearGroup.map]`.
-/
theorem dia_dg (α : ℚˣ) : dia2 (dg2 α 1) = dg2 (pri α) 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp [dg2, pri, GroundTheory.Automorphic.AdelicGLn.diagonal, Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Take `⟨h00, h11, h01⟩` from `realPart_orthogonal κ.2`. Use `⟨GroundTheory.Automorphic.GL2Classical.realPart κ.1, ?_, (prodEquiv ℚ 2 κ.1).2, finPart_mem_integralFiniteGL κ.2, (realEmb_realPart_mul_finEmb κ.1).symm⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith`.
-/
theorem compact_split (κ : KA) : ∃ (r : GL (Fin 2) ℝ), r.val * r.valᵀ = 1 ∧
    ∃ y ∈ integralFiniteGL ℚ 2, κ.1 = realEmb r * finEmb ℚ 2 y := by
  obtain ⟨h00, h11, h01⟩ := realPart_orthogonal κ.2
  refine ⟨GroundTheory.Automorphic.GL2Classical.realPart κ.1, ?_, (prodEquiv ℚ 2 κ.1).2, finPart_mem_integralFiniteGL κ.2,
    (realEmb_realPart_mul_finEmb κ.1).symm⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/- English proof (translation)
Apply `(prodEquiv ℚ 2).injective` to reduce the goal to its premises. Rewrite using `[map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`. Use `Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Apply the tactic sequence `change ((dg2 p 1 : G2).val i j).1 = RationalIdeles.realEquiv.symm ((dg2 (RationalIdeles.realPart p) 1 : GL (Fin 2) ℝ).val i j) fin_cases i <;> fin_cases j <;> simp [dg2, RationalIdeles.coe_realPart] <;> rfl`. Apply the tactic sequence `change ((dg2 p 1 : G2).val i j).2 = ((dg2 (IdeleGroup.toFinite ℚ p) 1 : GL (Fin 2) Af).val i j) fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl`.
-/
theorem dg_split (p : Jd) : (dg2 p 1 : G2) =
    realEmb (dg2 (RationalIdeles.realPart p) 1) * finEmb ℚ 2 (dg2 (IdeleGroup.toFinite ℚ p) 1) := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change ((dg2 p 1 : G2).val i j).1 = RationalIdeles.realEquiv.symm ((dg2 (RationalIdeles.realPart p) 1 : GL (Fin 2) ℝ).val i j)
    fin_cases i <;> fin_cases j <;> simp [dg2, RationalIdeles.coe_realPart] <;> rfl
  · change ((dg2 p 1 : G2).val i j).2 = ((dg2 (IdeleGroup.toFinite ℚ p) 1 : GL (Fin 2) Af).val i j)
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem dg_mul {R : Type*} [CommRing R] (a b : Rˣ) : (dg2 (a * b) 1 : GL (Fin 2) R) = dg2 a 1 * dg2 b 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Take `⟨h1, h2⟩` from `RationalIdeles.mem_positiveSubgroup.1 hp`. Establish `hreal` using `RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)`. Establish `e1 : md p = ‖(p : 𝔸[ℚ]).1 default‖`. Rewrite using `[md, IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule]`. Simplify using `[InfinitePlace.mult, hreal]`.

Rewrite using `[e1, RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply]`. Use `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero (map_zero _) ((p : 𝔸[ℚ]).1 default)` as an intermediate fact. Rewrite using `[← this, Real.norm_eq_abs, abs_of_pos]`. Simplify `h2` using `[RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply]`.
-/
theorem md_pos_eq (p : Jd) (hp : p ∈ RationalIdeles.positiveSubgroup) : ((RationalIdeles.realPart p : ℝˣ) : ℝ) = md p := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  have hreal := RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)
  have e1 : md p = ‖(p : 𝔸[ℚ]).1 default‖ := by
    rw [md, IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule]
    simp [InfinitePlace.mult, hreal]
  rw [e1, RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply]
  have := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero (map_zero _) ((p : 𝔸[ℚ]).1 default)
  rw [← this, Real.norm_eq_abs, abs_of_pos]
  simpa [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply] using h2

/- English proof (translation)
Take `⟨⟨α, p⟩, hp⟩` from `RationalIdeles.mulMap_bijective.2 a`. Establish `hp' : a = pri α * p.1` using `hp.symm`. Use `⟨α, RationalIdeles.realPart p.1, IdeleGroup.toFinite ℚ p.1, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : md (pri α * p.1) = md p.1`. Unfold `md`.

Rewrite using `[map_mul, show pri α = IdeleGroup.diagonal ℚ α from rfl, IdeleGroup.ideleModule_diagonal, one_mul]`. Rewrite using `[md_pos_eq _ p.2, hp', e]`. Take `⟨h1, -⟩` from `RationalIdeles.mem_positiveSubgroup.1 p.2`. Establish `hs` using `(IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1`. Establish `hb : ((IdeleGroup.toFinite ℚ p.1 : Afˣ) : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `fun v => (hs v).1`.

Establish `hbi : (((IdeleGroup.toFinite ℚ p.1)⁻¹ : Afˣ) : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `fun v => (hs v).2`. Establish `h0 : (0 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `zero_mem _`. Establish `h1' : (1 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `one_mem _`. Rewrite using `[GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff]`. Establish `hi : ((dg2 (IdeleGroup.toFinite ℚ p.1) 1)⁻¹ : GL (Fin 2) Af) = dg2 (IdeleGroup.toFinite ℚ p.1)⁻¹ 1`.

Use `inv_eq_of_mul_eq_one_right (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simpa [dg2]`. Apply the tactic sequence `rw [hi] fin_cases i <;> fin_cases j <;> simpa [dg2]`.

Rewrite using `[hp', dg_mul, dg_split p.1, dia_dg, mul_assoc]`.
-/
theorem idele_split (a : Jd) : ∃ (α : ℚˣ) (t : ℝˣ) (b : Afˣ), (t : ℝ) = md a ∧
    dg2 b 1 ∈ integralFiniteGL ℚ 2 ∧
    (dg2 a 1 : G2) = dia2 (dg2 α 1) * realEmb (dg2 t 1) * finEmb ℚ 2 (dg2 b 1) := by
  obtain ⟨⟨α, p⟩, hp⟩ := RationalIdeles.mulMap_bijective.2 a
  have hp' : a = pri α * p.1 := hp.symm
  refine ⟨α, RationalIdeles.realPart p.1, IdeleGroup.toFinite ℚ p.1, ?_, ?_, ?_⟩
  · have e : md (pri α * p.1) = md p.1 := by
      unfold md
      rw [map_mul, show pri α = IdeleGroup.diagonal ℚ α from rfl, IdeleGroup.ideleModule_diagonal, one_mul]
    rw [md_pos_eq _ p.2, hp', e]
  · obtain ⟨h1, -⟩ := RationalIdeles.mem_positiveSubgroup.1 p.2
    have hs := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1
    have hb : ((IdeleGroup.toFinite ℚ p.1 : Afˣ) : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun v => (hs v).1
    have hbi : (((IdeleGroup.toFinite ℚ p.1)⁻¹ : Afˣ) : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun v => (hs v).2
    have h0 : (0 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := zero_mem _
    have h1' : (1 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := one_mem _
    rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff]
    have hi : ((dg2 (IdeleGroup.toFinite ℚ p.1) 1)⁻¹ : GL (Fin 2) Af) = dg2 (IdeleGroup.toFinite ℚ p.1)⁻¹ 1 := by
      refine inv_eq_of_mul_eq_one_right (Units.ext (Matrix.ext fun i j => ?_))
      fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simpa [dg2]
    · rw [hi]
      fin_cases i <;> fin_cases j <;> simpa [dg2]
  · rw [hp', dg_mul, dg_split p.1, dia_dg, mul_assoc]

/- English proof (translation)
Apply `(prodEquiv ℚ 2).injective` to reduce the goal to its premises. Rewrite using `[map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`. Use `Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Apply the tactic sequence `change ((uni2 y : G2).val i j).1 = RationalIdeles.realEquiv.symm ((uni2 (RationalIdeles.realEquiv y.1) : GL (Fin 2) ℝ).val i j) fin_cases i <;> fin_cases j <;> simp [uni2] <;> rfl`. Apply the tactic sequence `change ((uni2 y : G2).val i j).2 = ((uni2 y.2 : GL (Fin 2) Af).val i j) fin_cases i <;> fin_cases j <;> simp [uni2] <;> rfl`.
-/
theorem uni_split (y : 𝔸[ℚ]) : (uni2 y : G2) =
    realEmb (uni2 (RationalIdeles.realEquiv y.1)) * finEmb ℚ 2 (uni2 y.2) := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change ((uni2 y : G2).val i j).1 = RationalIdeles.realEquiv.symm ((uni2 (RationalIdeles.realEquiv y.1) : GL (Fin 2) ℝ).val i j)
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> rfl
  · change ((uni2 y : G2).val i j).2 = ((uni2 y.2 : GL (Fin 2) Af).val i j)
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]`.
-/
theorem uni_add {R : Type*} [CommRing R] (a b : R) : (uni2 (a + b) : GL (Fin 2) R) = uni2 a * uni2 b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[uni2, GroundTheory.Automorphic.AdelicGLn.diagonal, Matrix.GeneralLinearGroup.map]`.
-/
theorem dia_uni (q : ℚ) : dia2 (uni2 q) = uni2 (algebraMap ℚ 𝔸[ℚ] q) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp [uni2, GroundTheory.Automorphic.AdelicGLn.diagonal, Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_sub_mem_integralFiniteAdeles x.2`. Use `⟨s, RationalIdeles.realEquiv (x - algebraMap ℚ 𝔸[ℚ] s).1, (x - algebraMap ℚ 𝔸[ℚ] s).2, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← uni_split, dia_uni, ← uni_add, add_sub_cancel]`.
-/
theorem adele_split (x : 𝔸[ℚ]) : ∃ (q : ℚ) (ρ : ℝ) (e : Af), e ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧
    (uni2 x : G2) = dia2 (uni2 q) * realEmb (uni2 ρ) * finEmb ℚ 2 (uni2 e) := by
  obtain ⟨s, hs⟩ := exists_sub_mem_integralFiniteAdeles x.2
  refine ⟨s, RationalIdeles.realEquiv (x - algebraMap ℚ 𝔸[ℚ] s).1, (x - algebraMap ℚ 𝔸[ℚ] s).2, hs, ?_⟩
  rw [mul_assoc, ← uni_split, dia_uni, ← uni_add, add_sub_cancel]

/- English proof (translation)
Take `⟨d, h1, h2⟩` from `exists_level_idele N u hu`. Rewrite using `[hL.level u hu d h1 h2 g, norm_mul, Circle.norm_coe, one_mul]`.
-/
theorem norm_level {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (g : G2) :
    ‖φ (g * finEmb ℚ 2 u)‖ = ‖φ g‖ := by
  obtain ⟨d, h1, h2⟩ := exists_level_idele N u hu
  rw [hL.level u hu d h1 h2 g, norm_mul, Circle.norm_coe, one_mul]

/- English proof (translation)
Rewrite using `[norm_level hL hu, hL.left, hL.real h hpos]`.
-/
theorem norm_eq_archLift {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) (γ : GL (Fin 2) ℚ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) {u : FiniteAdelicGL ℚ 2}
    (hu : u ∈ Gamma0Level N) : ‖φ (dia2 γ * realEmb h * finEmb ℚ 2 u)‖ = ‖archLift (k : ℤ) f h‖ := by
  rw [norm_level hL hu, hL.left, hL.real h hpos]

/- English proof (translation)
Take `⟨C, hC⟩` from `CuspFormClass.exists_bound f`. Use `⟨C, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, h, hpos, u, hu, rfl⟩` from `exists_decomposition N g`. Rewrite using `[norm_eq_archLift hL γ hpos hu, norm_archLift _ hpos]`. Use `set z : UpperHalfPlane := h • UpperHalfPlane.I`.

Establish `hy` using `z.im_pos`. Establish `hpow : 0 < z.im ^ (((k : ℤ) : ℝ) / 2)` using `Real.rpow_pos_of_pos hy _`. Establish `h1` using `hC z`. Rewrite using `[sqrt_zpow_eq_rpow hy]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bound {k N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ))
    {ω : HeckeCharacter ℚ} {φ : G2 → ℂ} (hL : Lift k N f ω φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, h, hpos, u, hu, rfl⟩ := exists_decomposition N g
  rw [norm_eq_archLift hL γ hpos hu, norm_archLift _ hpos]
  set z : UpperHalfPlane := h • UpperHalfPlane.I
  have hy := z.im_pos
  have hpow : 0 < z.im ^ (((k : ℤ) : ℝ) / 2) := Real.rpow_pos_of_pos hy _
  have h1 := hC z
  rw [sqrt_zpow_eq_rpow hy]
  calc z.im ^ (((k : ℤ) : ℝ) / 2) * ‖f z‖ ≤ z.im ^ (((k : ℤ) : ℝ) / 2) * (C / z.im ^ (((k : ℤ) : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h1 hpow.le
    _ = C := by field_simp

/- English proof (translation)
Take `⟨δ, u, hu, rfl⟩` from `exists_eq_finiteDiagonal_mul N g`. Establish `hne : (δ.det.val : ℚ) ≠ 0` using `δ.det.ne_zero`. Break down `lt_or_gt_of_ne hne with hneg | hpos` into its components or cases. Use `⟨δ * epsilon, ?_, ?_⟩` and prove the remaining obligations. Establish `he : (epsilon.det.val : ℚ) = -1`.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Simplify using `[epsilon, Matrix.det_fin_two_of]`. Rewrite using `[map_mul, Units.val_mul, he]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.

Conclude with `mul_mem (inv_mem (finiteDiagonal_epsilon_mem N)) hu`. Use `⟨δ, hpos, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_mul_cancel_left]` and apply the resulting hypothesis.
-/
theorem exists_pos_coset (N : ℕ) [NeZero N] (g : FiniteAdelicGL ℚ 2) :
    ∃ γ : GL (Fin 2) ℚ, 0 < (γ.det.val : ℚ) ∧
      (GroundTheory.Automorphic.AdelicGLn.finiteDiagonal ℚ 2 γ)⁻¹ * g ∈ Gamma0Level N := by
  obtain ⟨δ, u, hu, rfl⟩ := exists_eq_finiteDiagonal_mul N g
  have hne : (δ.det.val : ℚ) ≠ 0 := δ.det.ne_zero
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨δ * epsilon, ?_, ?_⟩
    · have he : (epsilon.det.val : ℚ) = -1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        simp [epsilon, Matrix.det_fin_two_of]
      rw [map_mul, Units.val_mul, he]
      linarith
    · rw [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      exact mul_mem (inv_mem (finiteDiagonal_epsilon_mem N)) hu
  · refine ⟨δ, hpos, ?_⟩
    rwa [inv_mul_cancel_left]

/- English proof (translation)
Establish `hK : IsCompact ((fun y => y * hf) '' (integralFiniteGL ℚ 2 : Set (FiniteAdelicGL ℚ 2)))` using `(GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL ℚ 2).image (continuous_id.mul continuous_const)`. Set `U : {γ : GL (Fin 2) ℚ // 0 < (γ.det.val : ℚ)} → Set (FiniteAdelicGL ℚ 2)` to `fun γ => {g | (GroundTheory.Automorphic.AdelicGLn.finiteDiagonal ℚ 2 γ.1)⁻¹ * g ∈ Gamma0Level N}`. Establish `hU : ∀ γ, IsOpen (U γ)` using `fun γ => (isOpen_Gamma0Level N).preimage (continuous_const.mul continuous_id)`. Establish `hcov : ((fun y => y * hf) '' (integralFiniteGL ℚ 2 : Set (FiniteAdelicGL ℚ 2))) ⊆ ⋃ γ, U γ`. Introduce `g _`.

Take `⟨γ, h1, h2⟩` from `exists_pos_coset N g`. Conclude with `Set.mem_iUnion.2 ⟨⟨γ, h1⟩, h2⟩`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover U hU hcov`. Use `⟨t.image Subtype.val, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ`.

Take `⟨γ', _, rfl⟩` from `Finset.mem_image.1 hγ`. Conclude with `γ'.2`. Introduce `y hy`. Take `⟨γ, hγ, hyγ⟩` from `Set.mem_iUnion₂.1 (ht ⟨y, hy, rfl⟩)`. Conclude with `⟨γ.1, Finset.mem_image_of_mem _ hγ, _, hyγ, by rw [mul_inv_cancel_left]⟩`.
-/
theorem cover (N : ℕ) [NeZero N] (hf : FiniteAdelicGL ℚ 2) :
    ∃ S : Finset (GL (Fin 2) ℚ), (∀ γ ∈ S, 0 < (γ.det.val : ℚ)) ∧ ∀ y ∈ integralFiniteGL ℚ 2,
      ∃ γ ∈ S, ∃ u ∈ Gamma0Level N, y * hf = GroundTheory.Automorphic.AdelicGLn.finiteDiagonal ℚ 2 γ * u := by
  classical
  have hK : IsCompact ((fun y => y * hf) '' (integralFiniteGL ℚ 2 : Set (FiniteAdelicGL ℚ 2))) :=
    (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL ℚ 2).image (continuous_id.mul continuous_const)
  let U : {γ : GL (Fin 2) ℚ // 0 < (γ.det.val : ℚ)} → Set (FiniteAdelicGL ℚ 2) := fun γ =>
    {g | (GroundTheory.Automorphic.AdelicGLn.finiteDiagonal ℚ 2 γ.1)⁻¹ * g ∈ Gamma0Level N}
  have hU : ∀ γ, IsOpen (U γ) := fun γ =>
    (isOpen_Gamma0Level N).preimage (continuous_const.mul continuous_id)
  have hcov : ((fun y => y * hf) '' (integralFiniteGL ℚ 2 : Set (FiniteAdelicGL ℚ 2))) ⊆ ⋃ γ, U γ := by
    intro g _
    obtain ⟨γ, h1, h2⟩ := exists_pos_coset N g
    exact Set.mem_iUnion.2 ⟨⟨γ, h1⟩, h2⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨γ', _, rfl⟩ := Finset.mem_image.1 hγ
    exact γ'.2
  · intro y hy
    obtain ⟨γ, hγ, hyγ⟩ := Set.mem_iUnion₂.1 (ht ⟨y, hy, rfl⟩)
    exact ⟨γ.1, Finset.mem_image_of_mem _ hγ, _, hyγ, by rw [mul_inv_cancel_left]⟩

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem uni_dg {R : Type*} [CommRing R] (a : Rˣ) (x : R) :
    (uni2 x * dg2 a 1 : GL (Fin 2) R) = dg2 a 1 * uni2 (((a⁻¹ : Rˣ) : R) * x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

def pointOf (ρ : ℝ) (t : ℝ) (ht : 0 < t) : UpperHalfPlane := ⟨⟨ρ, t⟩, ht⟩

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2, dg2, pointOf, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem borel_pointOf (ρ : ℝ) (t : ℝˣ) (ht : 0 < (t : ℝ)) :
    (uni2 ρ * dg2 t 1 : GL (Fin 2) ℝ) = borelGL (pointOf ρ t ht) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, pointOf, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `⟨pointOf (-z.re) z.im z.im_pos, rfl, Units.ext (Matrix.ext fun i j => ?_)⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [epsilon, pointOf, toReal, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem epsilon_borel (z : UpperHalfPlane) :
    ∃ z' : UpperHalfPlane, z'.im = z.im ∧ toReal epsilon * borelGL z' = borelGL z * toReal epsilon := by
  refine ⟨pointOf (-z.re) z.im z.im_pos, rfl, Units.ext (Matrix.ext fun i j => ?_)⟩
  fin_cases i <;> fin_cases j <;> simp [epsilon, pointOf, toReal, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Rewrite using `[← map_inv, epsilon_inv]`.
-/
theorem epsilon_inv' : (toReal epsilon)⁻¹ = toReal epsilon := by
  rw [← map_inv, epsilon_inv]

/- English proof (translation)
Take `⟨α, t, b, ht, hb, hab⟩` from `idele_split a`. Take `⟨r, hr, y, hy, hκ⟩` from `compact_split κ`. Take `⟨q, ρ, e, he, hx⟩` from `adele_split ((((pri α)⁻¹ : Jd) : 𝔸[ℚ]) * x)`. Establish `htpos : 0 < (t : ℝ)`. Rewrite using `[ht]`.

Conclude with `(IdeleGroup.ideleModule ℚ a).2`. Establish `he' : uni2 e ∈ integralFiniteGL ℚ 2`. Rewrite using `[GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff]`. Establish `h0 : (0 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `zero_mem _`. Establish `h1 : (1 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `one_mem _`.

Establish `hn : -e ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `neg_mem he`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simpa [uni2]`. Establish `hi : ((uni2 e)⁻¹ : GL (Fin 2) Af) = uni2 (-e)`. Use `inv_eq_of_mul_eq_one_right (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]`. Rewrite using `[hi]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simpa [uni2]`. Use `⟨dg2 α 1 * uni2 q, pointOf ρ t htpos, r, hr, ht, uni2 e * dg2 b 1 * y, mul_mem (mul_mem he' hb) hy, ?_⟩` and prove the remaining obligations. Establish `c1 : ∀ (h : GL (Fin 2) ℝ) (u : FiniteAdelicGL ℚ 2), finEmb ℚ 2 u * realEmb h = realEmb h * finEmb ℚ 2 u` using `fun h u => (realEmb_mul_finEmb_comm h u).symm`.

Establish `c2 : ∀ (h : GL (Fin 2) ℝ) (u : FiniteAdelicGL ℚ 2) (W : G2), finEmb ℚ 2 u * (realEmb h * W) = realEmb h * (finEmb ℚ 2 u * W)` using `fun h u W => by`. Rewrite using `[← mul_assoc, c1, mul_assoc]`. Rewrite using `[hab, hκ, ← borel_pointOf ρ t htpos]`. Establish `e1 : (uni2 x : G2) * dia2 (dg2 α 1) = dia2 (dg2 α 1) * uni2 ((((pri α)⁻¹ : Jd) : 𝔸[ℚ]) * x)`. Rewrite using `[dia_dg]`.

Conclude with `uni_dg _ _`. Establish `e2 : ∀ W : G2, (uni2 x : G2) * (dia2 (dg2 α 1) * W) = dia2 (dg2 α 1) * (uni2 ((((pri α)⁻¹ : Jd) : 𝔸[ℚ]) * x) * W)` using `fun W => by`. Rewrite using `[← mul_assoc, e1, mul_assoc]`. Simplify using `only [mul_assoc, e2]`. Rewrite using `[hx]`.

Simplify using `only [map_mul, mul_assoc, c1, c2]`.
-/
theorem selfDualLattice_projection_mem_of_unit_length (x : 𝔸[ℚ]) (a : Jd) (κ : KA) :
    ∃ (γ₀ : GL (Fin 2) ℚ) (z : UpperHalfPlane) (r : GL (Fin 2) ℝ), r.val * r.valᵀ = 1 ∧ z.im = md a ∧
      ∃ y ∈ integralFiniteGL ℚ 2, uni2 x * dg2 a 1 * κ.1 = dia2 γ₀ * realEmb (borelGL z * r) * finEmb ℚ 2 y := by
  obtain ⟨α, t, b, ht, hb, hab⟩ := idele_split a
  obtain ⟨r, hr, y, hy, hκ⟩ := compact_split κ
  obtain ⟨q, ρ, e, he, hx⟩ := adele_split ((((pri α)⁻¹ : Jd) : 𝔸[ℚ]) * x)
  have htpos : 0 < (t : ℝ) := by
    rw [ht]; exact (IdeleGroup.ideleModule ℚ a).2
  have he' : uni2 e ∈ integralFiniteGL ℚ 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff]
    have h0 : (0 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := zero_mem _
    have h1 : (1 : Af) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := one_mem _
    have hn : -e ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := neg_mem he
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simpa [uni2]
    · have hi : ((uni2 e)⁻¹ : GL (Fin 2) Af) = uni2 (-e) := by
        refine inv_eq_of_mul_eq_one_right (Units.ext (Matrix.ext fun i j => ?_))
        fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hi]
      fin_cases i <;> fin_cases j <;> simpa [uni2]
  refine ⟨dg2 α 1 * uni2 q, pointOf ρ t htpos, r, hr, ht, uni2 e * dg2 b 1 * y,
    mul_mem (mul_mem he' hb) hy, ?_⟩
  have c1 : ∀ (h : GL (Fin 2) ℝ) (u : FiniteAdelicGL ℚ 2), finEmb ℚ 2 u * realEmb h = realEmb h * finEmb ℚ 2 u :=
    fun h u => (realEmb_mul_finEmb_comm h u).symm
  have c2 : ∀ (h : GL (Fin 2) ℝ) (u : FiniteAdelicGL ℚ 2) (W : G2),
      finEmb ℚ 2 u * (realEmb h * W) = realEmb h * (finEmb ℚ 2 u * W) := fun h u W => by
    rw [← mul_assoc, c1, mul_assoc]
  rw [hab, hκ, ← borel_pointOf ρ t htpos]
  have e1 : (uni2 x : G2) * dia2 (dg2 α 1) = dia2 (dg2 α 1) * uni2 ((((pri α)⁻¹ : Jd) : 𝔸[ℚ]) * x) := by
    rw [dia_dg]; exact uni_dg _ _
  have e2 : ∀ W : G2, (uni2 x : G2) * (dia2 (dg2 α 1) * W) =
      dia2 (dg2 α 1) * (uni2 ((((pri α)⁻¹ : Jd) : 𝔸[ℚ]) * x) * W) := fun W => by
    rw [← mul_assoc, e1, mul_assoc]
  simp only [mul_assoc, e2]
  rw [hx]
  simp only [map_mul, mul_assoc, c1, c2]

/- English proof (translation)
Take `⟨γ₀, z, r, hr, hz, y, hy, e⟩` from `selfDualLattice_projection_mem_of_unit_length x a κ`. Establish `hd : r.det.val * r.det.val = 1`. Use `congrArg Matrix.det hr` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]`. Simplify `this` using `[Matrix.GeneralLinearGroup.val_det_apply]`.

Establish `hd' : r.det.val = 1 ∨ r.det.val = -1` using `mul_self_eq_one_iff.1 hd`. Break down `hd' with h1 | h1` into its components or cases. Conclude with `⟨γ₀, z, r, hr, h1, hz, y, hy, e⟩`. Take `⟨z', hz', hb⟩` from `epsilon_borel z`. Establish `heps : (toReal epsilon)⁻¹ * (borelGL z * r) = borelGL z' * ((toReal epsilon)⁻¹ * r)`.

Establish `h2 : (toReal epsilon)⁻¹ * borelGL z = borelGL z' * (toReal epsilon)⁻¹`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, hb, mul_inv_cancel_right]`. Rewrite using `[← mul_assoc, h2, mul_assoc]`. Use `⟨γ₀ * epsilon, z', (toReal epsilon)⁻¹ * r, ?_, ?_, hz'.trans hz, (GroundTheory.Automorphic.AdelicGLn.finiteDiagonal ℚ 2 epsilon)⁻¹ * y, ?_, ?_⟩` and prove the remaining obligations. Establish `hE : (toReal epsilon).val * (toReal epsilon).valᵀ = 1`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [epsilon, toReal, Matrix.mul_apply, Fin.sum_univ_two]`. Rewrite using `[epsilon_inv' , Units.val_mul, Matrix.transpose_mul, mul_assoc, ← mul_assoc r.val, hr, one_mul, hE]`. Rewrite using `[map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal_epsilon, h1]`. Evaluate the numerical expressions.

Conclude with `mul_mem (inv_mem (Gamma0Level_le_integralFiniteGL 1 (finiteDiagonal_epsilon_mem 1))) hy`. Rewrite using `[e, diagonal_mul_realEmb_mul_finEmb γ₀ epsilon, heps]`.
-/
theorem full_split (x : 𝔸[ℚ]) (a : Jd) (κ : KA) :
    ∃ (γ₀ : GL (Fin 2) ℚ) (z : UpperHalfPlane) (r : GL (Fin 2) ℝ), r.val * r.valᵀ = 1 ∧ r.det.val = 1 ∧ z.im = md a ∧
      ∃ y ∈ integralFiniteGL ℚ 2, uni2 x * dg2 a 1 * κ.1 = dia2 γ₀ * realEmb (borelGL z * r) * finEmb ℚ 2 y := by
  obtain ⟨γ₀, z, r, hr, hz, y, hy, e⟩ := selfDualLattice_projection_mem_of_unit_length x a κ
  have hd : r.det.val * r.det.val = 1 := by
    have := congrArg Matrix.det hr
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hd' : r.det.val = 1 ∨ r.det.val = -1 := mul_self_eq_one_iff.1 hd
  rcases hd' with h1 | h1
  · exact ⟨γ₀, z, r, hr, h1, hz, y, hy, e⟩
  · obtain ⟨z', hz', hb⟩ := epsilon_borel z
    have heps : (toReal epsilon)⁻¹ * (borelGL z * r) = borelGL z' * ((toReal epsilon)⁻¹ * r) := by
      have h2 : (toReal epsilon)⁻¹ * borelGL z = borelGL z' * (toReal epsilon)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hb, mul_inv_cancel_right]
      rw [← mul_assoc, h2, mul_assoc]
    refine ⟨γ₀ * epsilon, z', (toReal epsilon)⁻¹ * r, ?_, ?_, hz'.trans hz, (GroundTheory.Automorphic.AdelicGLn.finiteDiagonal ℚ 2 epsilon)⁻¹ * y, ?_, ?_⟩
    · have hE : (toReal epsilon).val * (toReal epsilon).valᵀ = 1 := by
        refine Matrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp [epsilon, toReal, Matrix.mul_apply, Fin.sum_univ_two]
      rw [epsilon_inv' , Units.val_mul, Matrix.transpose_mul, mul_assoc, ← mul_assoc r.val, hr, one_mul, hE]
    · rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal_epsilon, h1]; norm_num
    · exact mul_mem (inv_mem (Gamma0Level_le_integralFiniteGL 1 (finiteDiagonal_epsilon_mem 1))) hy
    · rw [e, diagonal_mul_realEmb_mul_finEmb γ₀ epsilon, heps]

/- English proof (translation)
Introduce `_ k N _ hk χ hχ f a hf ha ω φ hω hL`. Take `⟨C₀, hC₀⟩` from `exists_bound f hL`. Use `⟨⟨C₀, hC₀⟩, fun h hh M => ?_⟩` and prove the remaining obligations. Establish `hh' : h = finEmb ℚ 2 (prodEquiv ℚ 2 h).2`. Establish `hp : (prodEquiv ℚ 2 h).1 = 1`.

Use `Units.ext (Matrix.ext fun i j => funext fun w => ?_)` and prove the remaining obligations. Establish `h3 : ((prodEquiv ℚ 2 h).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j w = (h.val i j).1 w` using `rfl`. Establish `h4 : (h.val i j).1 w = (infAt w h).val i j` using `rfl`. Rewrite using `[h3, h4, hh w]`. Apply the tactic sequence `rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *] <;> rfl`.

Establish `hr : GroundTheory.Automorphic.GL2Classical.realPart h = 1`. Rewrite using `[GroundTheory.Automorphic.GL2Classical.realPart, hp, map_one]`. Use `conv_lhs => rw [← realEmb_realPart_mul_finEmb h, hr, map_one, one_mul]`. Take `⟨S, hS, hcov⟩` from `cover N (prodEquiv ℚ 2 h).2`. Establish `hdec : ∀ γ : GL (Fin 2) ℚ, ∃ C : ℝ, 0 < (γ.det.val : ℚ) → ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖archLift (k : ℤ) (f : UpperHalfPlane → ℂ) (toReal γ⁻¹ * borelGL z)‖ ≤ C * (z.im⁻¹) ^ M`.

Introduce `γ`. Distinguish the cases in `hγ : 0 < (γ.det.val : ℚ)`. Establish `hγ' : 0 < ((γ⁻¹).det.val : ℚ)`. Rewrite using `[map_inv, Units.val_inv_eq_inv_val]`. Conclude with `inv_pos.2 hγ`.

Take `⟨C, hC⟩` from `cusp_decay (k : ℤ) N f γ⁻¹ hγ' M`. Conclude with `⟨C, fun _ => hC⟩`. Conclude with `⟨0, fun h => absurd h hγ⟩`. Use `choose Cf hCf using hdec`. Use `⟨max C₀ 0 + ∑ γ ∈ S, |Cf γ|, fun x a' κ => ?_⟩` and prove the remaining obligations.

Establish `hsum : ∀ γ ∈ S, Cf γ ≤ max C₀ 0 + ∑ γ ∈ S, |Cf γ|` using `fun γ hγ => by`. Establish `h1 : |Cf γ| ≤ ∑ γ ∈ S, |Cf γ|` using `Finset.single_le_sum (f := fun γ => |Cf γ|) (fun _ _ => abs_nonneg _) hγ`. Establish `h2` using `le_abs_self (Cf γ)`. Establish `h3` using `le_max_right C₀ 0`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC₀' : C₀ ≤ max C₀ 0 + ∑ γ ∈ S, |Cf γ|`. Establish `h1 : 0 ≤ ∑ γ ∈ S, |Cf γ|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `h3` using `le_max_left C₀ 0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmd : 0 < md a'` using `(IdeleGroup.ideleModule ℚ a').2`.

Distinguish the cases in `h1 : md a' ≤ 1`. Establish `: min 1 (md a')⁻¹ = 1` using `min_eq_left ((one_le_inv₀ hmd).2 h1)`. Rewrite using `[this, one_pow, mul_one]`. Conclude with `(hC₀ _).trans hC₀'`. Establish `h1' : 1 ≤ md a'` using `(not_le.1 h1).le`.

Establish `hmin : min 1 (md a')⁻¹ = (md a')⁻¹` using `min_eq_right (inv_le_one_of_one_le₀ h1')`. Rewrite using `[hmin]`. Take `⟨γ₀, z, r, hr, hr1, hz, y, hy, e⟩` from `full_split x a' κ`. Take `⟨γ, hγS, u, hu, hyu⟩` from `hcov y hy`. Establish `hγ` using `hS γ hγS`.

Establish `hpos : 0 < ((toReal γ⁻¹ * borelGL z).det.val)`. Rewrite using `[map_mul, Units.val_mul, det_toReal]`. Use `mul_pos ?_ (det_borelGL_pos z)` and prove the remaining obligations. Rewrite using `[map_inv, Units.val_inv_eq_inv_val]`. Conclude with `inv_pos.2 hγ` after adjusting the coercions.

Establish `key : ‖φ (uni2 x * dg2 a' 1 * κ.1 * h)‖ = ‖archLift (k : ℤ) (f : UpperHalfPlane → ℂ) (toReal γ⁻¹ * borelGL z)‖`. Take `⟨w, hw, hrot⟩` from `hL.rot r hr hr1`. Establish `e2 : uni2 x * dg2 a' 1 * κ.1 * h = dia2 (γ₀ * γ) * realEmb (toReal γ⁻¹ * borelGL z) * realEmb r * finEmb ℚ 2 u` using `by conv_lhs => rw [e, hh', mul_assoc, ← map_mul, hyu, diagonal_mul_realEmb_mul_finEmb γ₀ γ, inv_mul_cancel_left]`. Rewrite using `[map_inv, ← mul_assoc ((toReal γ)⁻¹), map_mul realEmb (_ * _) r]`. Simplify using `only [mul_assoc]`.

Rewrite using `[e2, norm_level hL hu, hrot, norm_mul, hw, one_mul, ← norm_eq_archLift hL (γ₀ * γ) hpos (one_mem _), map_one, mul_one]`. Use `show ‖φ (uni2 x * dg2 a' 1 * κ.1 * h)‖ ≤ _`. Rewrite using `[key]`. Establish `hz1 : 1 ≤ z.im` using `hz ▸ h1'`. Use `(hCf γ hγ z hz1).trans ?_` and prove the remaining obligations.

Rewrite using `[hz]`. Conclude with `mul_le_mul_of_nonneg_right (hsum γ hγS) (pow_nonneg (inv_nonneg.2 hmd.le) _)`.
-/
theorem main : B0 → F5 := by
  intro _ k N _ hk χ hχ f a hf ha ω φ hω hL
  obtain ⟨C₀, hC₀⟩ := exists_bound f hL
  refine ⟨⟨C₀, hC₀⟩, fun h hh M => ?_⟩
  have hh' : h = finEmb ℚ 2 (prodEquiv ℚ 2 h).2 := by
    have hp : (prodEquiv ℚ 2 h).1 = 1 := by
      refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
      have h3 : ((prodEquiv ℚ 2 h).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j w = (h.val i j).1 w := rfl
      have h4 : (h.val i j).1 w = (infAt w h).val i j := rfl
      rw [h3, h4, hh w]
      rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *] <;> rfl
    have hr : GroundTheory.Automorphic.GL2Classical.realPart h = 1 := by
      rw [GroundTheory.Automorphic.GL2Classical.realPart, hp, map_one]
    conv_lhs => rw [← realEmb_realPart_mul_finEmb h, hr, map_one, one_mul]
  obtain ⟨S, hS, hcov⟩ := cover N (prodEquiv ℚ 2 h).2
  have hdec : ∀ γ : GL (Fin 2) ℚ, ∃ C : ℝ, 0 < (γ.det.val : ℚ) → ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖archLift (k : ℤ) (f : UpperHalfPlane → ℂ) (toReal γ⁻¹ * borelGL z)‖ ≤ C * (z.im⁻¹) ^ M := by
    intro γ
    by_cases hγ : 0 < (γ.det.val : ℚ)
    · have hγ' : 0 < ((γ⁻¹).det.val : ℚ) := by
        rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.2 hγ
      obtain ⟨C, hC⟩ := cusp_decay (k : ℤ) N f γ⁻¹ hγ' M
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hγ⟩
  choose Cf hCf using hdec
  refine ⟨max C₀ 0 + ∑ γ ∈ S, |Cf γ|, fun x a' κ => ?_⟩
  have hsum : ∀ γ ∈ S, Cf γ ≤ max C₀ 0 + ∑ γ ∈ S, |Cf γ| := fun γ hγ => by
    have h1 : |Cf γ| ≤ ∑ γ ∈ S, |Cf γ| := Finset.single_le_sum (f := fun γ => |Cf γ|) (fun _ _ => abs_nonneg _) hγ
    have h2 := le_abs_self (Cf γ)
    have h3 := le_max_right C₀ 0
    linarith
  have hC₀' : C₀ ≤ max C₀ 0 + ∑ γ ∈ S, |Cf γ| := by
    have h1 : 0 ≤ ∑ γ ∈ S, |Cf γ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h3 := le_max_left C₀ 0
    linarith
  have hmd : 0 < md a' := (IdeleGroup.ideleModule ℚ a').2
  by_cases h1 : md a' ≤ 1
  · have : min 1 (md a')⁻¹ = 1 := min_eq_left ((one_le_inv₀ hmd).2 h1)
    rw [this, one_pow, mul_one]
    exact (hC₀ _).trans hC₀'
  · have h1' : 1 ≤ md a' := (not_le.1 h1).le
    have hmin : min 1 (md a')⁻¹ = (md a')⁻¹ := min_eq_right (inv_le_one_of_one_le₀ h1')
    rw [hmin]
    obtain ⟨γ₀, z, r, hr, hr1, hz, y, hy, e⟩ := full_split x a' κ
    obtain ⟨γ, hγS, u, hu, hyu⟩ := hcov y hy
    have hγ := hS γ hγS
    have hpos : 0 < ((toReal γ⁻¹ * borelGL z).det.val) := by
      rw [map_mul, Units.val_mul, det_toReal]
      refine mul_pos ?_ (det_borelGL_pos z)
      rw [map_inv, Units.val_inv_eq_inv_val]
      exact_mod_cast inv_pos.2 hγ
    have key : ‖φ (uni2 x * dg2 a' 1 * κ.1 * h)‖ = ‖archLift (k : ℤ) (f : UpperHalfPlane → ℂ) (toReal γ⁻¹ * borelGL z)‖ := by
      obtain ⟨w, hw, hrot⟩ := hL.rot r hr hr1
      have e2 : uni2 x * dg2 a' 1 * κ.1 * h =
          dia2 (γ₀ * γ) * realEmb (toReal γ⁻¹ * borelGL z) * realEmb r * finEmb ℚ 2 u := by
        conv_lhs => rw [e, hh', mul_assoc, ← map_mul, hyu, diagonal_mul_realEmb_mul_finEmb γ₀ γ, inv_mul_cancel_left]
        rw [map_inv, ← mul_assoc ((toReal γ)⁻¹), map_mul realEmb (_ * _) r]
        simp only [mul_assoc]
      rw [e2, norm_level hL hu, hrot, norm_mul, hw, one_mul, ← norm_eq_archLift hL (γ₀ * γ) hpos (one_mem _), map_one, mul_one]
    show ‖φ (uni2 x * dg2 a' 1 * κ.1 * h)‖ ≤ _
    rw [key]
    have hz1 : 1 ≤ z.im := hz ▸ h1'
    refine (hCf γ hγ z hz1).trans ?_
    rw [hz]
    exact mul_le_mul_of_nonneg_right (hsum γ hγS) (pow_nonneg (inv_nonneg.2 hmd.le) _)

end GlobalTheory.CompanionTheory.NewformLiftDecay

end
