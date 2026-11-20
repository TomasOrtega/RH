import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RapidKernelDecay

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
The claim follows from `(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _`.
-/
theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

omit [IsTotallyComplex E] in

/- English proof (translation)
Unfold `height`. Rewrite using `[inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_inv (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring

omit [IsTotallyComplex E] in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vecMul, dotProduct, map_sum]`.
-/
theorem pFin_vecMul (x : Fin a → Ad E) (m : GA E a) :
    (fun i => pFin E ((x ᵥ* m.val) i)) = (fun i => pFin E (x i)) ᵥ* m.val.map (pFin E) := by
  funext i
  simp [vecMul, dotProduct, map_sum]

/- English proof (translation)
Establish `hy : ∀ j i, ‖pInf E ((infGL E a y).val j i)‖ ≤ height y`. Introduce `j i`. Establish `e : pInf E ((infGL E a y).val j i) = y.val j i` using `congrArg (fun u : GL (Fin a) (Cinf E) => u.val j i) (pInf_infGL (E := E) y)`. Rewrite using `[e]`. Establish `: ‖y.val j i‖ ≤ ‖toL y.val‖` using `(norm_le_pi_norm (toL y.val j) i).trans (norm_le_pi_norm (toL y.val) j)`.

Unfold `height`. Combine the linear relations using `[norm_nonneg (toL (y⁻¹).val)]`. Establish `h1` using `one_le_height y`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Simplify using `only [vecMul, dotProduct, map_sum, map_mul]`.

Use `(norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height y * ‖fun i => pInf E (x i)‖) fun j _ => ?_).trans ?_)` and prove the remaining obligations. Rewrite using `[mul_comm (height y)]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) (hy j i) (norm_nonneg _) (norm_nonneg _))`. Simplify using `only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Conclude with `le_of_eq (by ring)`.
-/
theorem norm_vecMul_infGL_le (y : GL (Fin a) (Cinf E)) (x : Fin a → Ad E) :
    ‖fun i => pInf E ((x ᵥ* (infGL E a y).val) i)‖ ≤ (a * height y) * ‖fun i => pInf E (x i)‖ := by
  have hy : ∀ j i, ‖pInf E ((infGL E a y).val j i)‖ ≤ height y := by
    intro j i
    have e : pInf E ((infGL E a y).val j i) = y.val j i :=
      congrArg (fun u : GL (Fin a) (Cinf E) => u.val j i) (pInf_infGL (E := E) y)
    rw [e]
    have : ‖y.val j i‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (toL y.val j) i).trans (norm_le_pi_norm (toL y.val) j)
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h1 := one_le_height y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [vecMul, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height y * ‖fun i => pInf E (x i)‖)
    fun j _ => ?_).trans ?_)
  · rw [mul_comm (height y)]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) (hy j i)
      (norm_nonneg _) (norm_nonneg _))
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)

/- English proof (translation)
Use `set u := GeneralLinearGroup.det (infGL E a z) with hu`. Establish `hB : 1 ≤ (a.factorial : ℝ) * height z ^ a` using `one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ (one_le_height z))`. Establish `hinf : pInf E (u : Ad E) = (GeneralLinearGroup.det z : Cinf E)`. Rewrite using `[hu, ← CuspRep.det_map, pInf_infGL]`. Establish `hfin : pFin E (u : Ad E) = 1`.

Rewrite using `[hu, ← CuspRep.det_map, pFin_infGL, map_one, Units.val_one]`. Rewrite using `[ideleModule_eq]`. Establish `h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(u : Ad E).2 v‖ = 1` using `finprod_eq_one_of_forall_eq_one fun v => by`. Establish `: (u : Ad E).2 = 1` using `hfin`. Rewrite using `[this]`.

Conclude with `norm_one`. Rewrite using `[h2, mul_one, pow_mul, ← Finset.card_univ, ← Finset.prod_const]`. Use `Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => ?_` and prove the remaining obligations. Establish `h1 : ‖(u : Ad E).1 w‖ ≤ a.factorial * height z ^ a`. Rewrite using `[← norm_pInf_apply, hinf]`.

Conclude with `(norm_le_pi_norm _ w).trans (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (z⁻¹).val)]))`. Apply the tactic sequence `have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num`. Conclude with `(pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_right₀ hB hm)`.
-/
theorem ideleModule_det_infGL_le (z : GL (Fin a) (Cinf E)) :
    (ideleModule E (GeneralLinearGroup.det (infGL E a z)) : ℝ) ≤
      ((a.factorial : ℝ) * height z ^ a) ^ (2 * Fintype.card (InfinitePlace E)) := by
  set u := GeneralLinearGroup.det (infGL E a z) with hu
  have hB : 1 ≤ (a.factorial : ℝ) * height z ^ a :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ (one_le_height z))
  have hinf : pInf E (u : Ad E) = (GeneralLinearGroup.det z : Cinf E) := by
    rw [hu, ← CuspRep.det_map, pInf_infGL]
  have hfin : pFin E (u : Ad E) = 1 := by
    rw [hu, ← CuspRep.det_map, pFin_infGL, map_one, Units.val_one]
  rw [ideleModule_eq]
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(u : Ad E).2 v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      have : (u : Ad E).2 = 1 := hfin
      rw [this]
      exact norm_one
  rw [h2, mul_one, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => ?_
  have h1 : ‖(u : Ad E).1 w‖ ≤ a.factorial * height z ^ a := by
    rw [← norm_pInf_apply, hinf]
    exact (norm_le_pi_norm _ w).trans (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (z⁻¹).val)]))
  have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_right₀ hB hm)

end GlobalTheory.RapidKernelDecay

namespace GlobalTheory.RapidKernelDecay

/- English proof (translation)
Introduce `E _ _ _ a F X _ ν _ k γ hk hF L hL C₀ hC₀ N`. Take `⟨-, -, hkI⟩` from `hk`. Take `⟨C, hC⟩` from `hF L hL C₀ hC₀ N`. Take `⟨M₁, hM₁, h₁⟩` from `GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀`. Take `⟨M₂, hM₂, h₂⟩` from `GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀.inv`.

Use `set n := a * Module.finrank ℚ E with hn`. Use `set p := 2 * Fintype.card (InfinitePlace E) with hp`. Use `set K₀ : ℝ := (M₂ * a * M₁) ^ n * (a.factorial : ℝ) ^ p with hK₀`. Use `set m := n + a * p with hm`. Use `set I := ∫ x, ‖k x‖ * height (γ x) ^ (m * N) ∂ν with hI`.

Use `⟨I * (|C| * K₀ ^ N), fun g c hc ξ hξ hξL => ?_⟩` and prove the remaining obligations. Use `set v : Fin a → Ad E := fun j => algebraMap E (Ad E) (ξ j) with hv`. Use `set Xn := ‖fun i => pInf E ((v ᵥ* g.val) i)‖ with hXn`. Use `set G := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG`. Establish `hGpos : 0 < G` using `(ideleModule E _).2`.

Establish `key : ∀ y : GL (Fin a) (Cinf E), ‖F (g * c * infGL E a y)‖ ≤ |C| * K₀ ^ N * height y ^ (m * N) * (Xn ^ n / G) ^ N`. Introduce `y`. Establish `hy1` using `one_le_height y`. Use `set g' := g * c * infGL E a y * c⁻¹ with hg'`. Establish `eg : g * c * infGL E a y = g' * c` using `(inv_mul_cancel_right _ c).symm`.

Establish `hfin : (fun i => pFin E ((v ᵥ* g'.val) i)) = (fun i => pFin E ((v ᵥ* g.val) i))`. Rewrite using `[pFin_vecMul, pFin_vecMul]`. Use `congr 1`. Use `show (GeneralLinearGroup.map (pFin E) g').val = (GeneralLinearGroup.map (pFin E) g).val`. Simplify using `[hg', map_mul, map_inv, pFin_infGL]`.

Establish `hinf : ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ≤ M₂ * a * M₁ * height y * Xn`. Establish `e : v ᵥ* g'.val = ((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) ᵥ* (c⁻¹ : GA E a).val`. Simplify using `only [hg', Units.val_mul, vecMul_vecMul]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Use `set D := (ideleModule E (GeneralLinearGroup.det (infGL E a y)) : ℝ) with hD`. Establish `hDpos : 0 < D` using `(ideleModule E _).2`. Establish `hdet : (ideleModule E (GeneralLinearGroup.det g') : ℝ) = G * D`. Establish `: GeneralLinearGroup.det g' = GeneralLinearGroup.det g * GeneralLinearGroup.det (infGL E a y)`. Simplify using `only [hg', map_mul, map_inv]`.

Rewrite using `[mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]`. Rewrite using `[this, map_mul, Positive.val_mul]`. Establish `hDinv : D⁻¹ ≤ ((a.factorial : ℝ) * height y ^ a) ^ p`. Establish `h` using `ideleModule_det_infGL_le (E := E) y⁻¹`. Rewrite `h` using `[height_inv]`.

Establish `hDD : D * (ideleModule E (GeneralLinearGroup.det (infGL E a y⁻¹)) : ℝ) = 1`. Rewrite using `[hD, ← Positive.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]`. Both sides reduce to the same expression. Rewrite `h` using `[eq_inv_of_mul_eq_one_right hDD]`. Conclude with `h`.

Establish `hq : (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ≤ K₀ * height y ^ m * (Xn ^ n / G)`. Rewrite using `[hdet]`. Establish `hXn0 : 0 ≤ Xn` using `norm_nonneg _`. Establish `hb0 : 0 ≤ M₂ * a * M₁ * height y * Xn`. Use `hM₁.le` as an intermediate fact.

Use `hM₂.le` as an intermediate fact. Check the signs of the components of the expression. Establish `hc0 : 0 ≤ ((a.factorial : ℝ) * height y ^ a) ^ p` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hL' : (fun i => pFin E ((v ᵥ* g'.val) i)) ∈ L` using `hfin ▸ hξL`.

Establish `hF'` using `hC g' c hc ξ hξ hL'`. Rewrite using `[eg]`. Establish `hnn : 0 ≤ (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N` using `pow_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) (ideleModule E _).2.le) _`. Combine the equalities or inequalities in the displayed calculation. Establish `hint : Integrable (fun x => ‖k x‖ * height (γ x) ^ (m * N)) ν` using `hkI (m * N)`.

Use `show ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖ ≤ I * (|C| * K₀ ^ N) * (Xn ^ n / G) ^ N`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by rw [integral_mul_const, hI]; ring`.
-/
theorem decays_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F →
      GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF L hL C₀ hC₀ N
  obtain ⟨-, -, hkI⟩ := hk
  obtain ⟨C, hC⟩ := hF L hL C₀ hC₀ N
  obtain ⟨M₁, hM₁, h₁⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀
  obtain ⟨M₂, hM₂, h₂⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀.inv
  set n := a * Module.finrank ℚ E with hn
  set p := 2 * Fintype.card (InfinitePlace E) with hp
  set K₀ : ℝ := (M₂ * a * M₁) ^ n * (a.factorial : ℝ) ^ p with hK₀
  set m := n + a * p with hm
  set I := ∫ x, ‖k x‖ * height (γ x) ^ (m * N) ∂ν with hI
  refine ⟨I * (|C| * K₀ ^ N), fun g c hc ξ hξ hξL => ?_⟩
  set v : Fin a → Ad E := fun j => algebraMap E (Ad E) (ξ j) with hv
  set Xn := ‖fun i => pInf E ((v ᵥ* g.val) i)‖ with hXn
  set G := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG
  have hGpos : 0 < G := (ideleModule E _).2
  have key : ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * c * infGL E a y)‖ ≤ |C| * K₀ ^ N * height y ^ (m * N) * (Xn ^ n / G) ^ N := by
    intro y
    have hy1 := one_le_height y
    set g' := g * c * infGL E a y * c⁻¹ with hg'
    have eg : g * c * infGL E a y = g' * c := (inv_mul_cancel_right _ c).symm
    have hfin : (fun i => pFin E ((v ᵥ* g'.val) i)) = (fun i => pFin E ((v ᵥ* g.val) i)) := by
      rw [pFin_vecMul, pFin_vecMul]
      congr 1
      show (GeneralLinearGroup.map (pFin E) g').val = (GeneralLinearGroup.map (pFin E) g).val
      simp [hg', map_mul, map_inv, pFin_infGL]
    have hinf : ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ≤ M₂ * a * M₁ * height y * Xn := by
      have e : v ᵥ* g'.val = ((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) ᵥ* (c⁻¹ : GA E a).val := by
        simp only [hg', Units.val_mul, vecMul_vecMul]
      rw [e]
      calc _ ≤ M₂ * ‖fun i => pInf E (((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) i)‖ :=
            h₂ c⁻¹ (Set.inv_mem_inv.2 hc) _
        _ ≤ M₂ * ((a * height y) * ‖fun i => pInf E ((v ᵥ* g.val ᵥ* c.val) i)‖) :=
            mul_le_mul_of_nonneg_left (norm_vecMul_infGL_le y _) hM₂.le
        _ ≤ M₂ * ((a * height y) * (M₁ * Xn)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h₁ c hc _) (by positivity)) hM₂.le
        _ = _ := by ring
    set D := (ideleModule E (GeneralLinearGroup.det (infGL E a y)) : ℝ) with hD
    have hDpos : 0 < D := (ideleModule E _).2
    have hdet : (ideleModule E (GeneralLinearGroup.det g') : ℝ) = G * D := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * GeneralLinearGroup.det (infGL E a y) := by
        simp only [hg', map_mul, map_inv]
        rw [mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      rw [this, map_mul, Positive.val_mul]
    have hDinv : D⁻¹ ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by
      have h := ideleModule_det_infGL_le (E := E) y⁻¹
      rw [height_inv] at h
      have hDD : D * (ideleModule E (GeneralLinearGroup.det (infGL E a y⁻¹)) : ℝ) = 1 := by
        rw [hD, ← Positive.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
        rfl
      rw [eq_inv_of_mul_eq_one_right hDD] at h
      exact h
    have hq : (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ≤
        K₀ * height y ^ m * (Xn ^ n / G) := by
      rw [hdet]
      have hXn0 : 0 ≤ Xn := norm_nonneg _
      have hb0 : 0 ≤ M₂ * a * M₁ * height y * Xn := by
        have := hM₁.le; have := hM₂.le; positivity
      have hc0 : 0 ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by positivity
      calc _ = ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n * D⁻¹ / G := by ring
        _ ≤ (M₂ * a * M₁ * height y * Xn) ^ n * ((a.factorial : ℝ) * height y ^ a) ^ p / G :=
            div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinf n) hDinv
              (inv_nonneg.2 hDpos.le) (pow_nonneg hb0 _)) hGpos.le
        _ = _ := by rw [hK₀, hm, pow_add, pow_mul]; ring
    have hL' : (fun i => pFin E ((v ᵥ* g'.val) i)) ∈ L := hfin ▸ hξL
    have hF' := hC g' c hc ξ hξ hL'
    rw [eg]
    have hnn : 0 ≤ (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
      pow_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) (ideleModule E _).2.le) _
    calc ‖F (g' * c)‖ ≤ |C| * (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n /
          (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
          hF'.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)
      _ ≤ |C| * (K₀ * height y ^ m * (Xn ^ n / G)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (pow_nonneg (norm_nonneg _) _)
            (ideleModule E _).2.le) hq N) (abs_nonneg C)
      _ = _ := by ring
  have hint : Integrable (fun x => ‖k x‖ * height (γ x) ^ (m * N)) ν := hkI (m * N)
  show ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖ ≤ I * (|C| * K₀ ^ N) * (Xn ^ n / G) ^ N
  calc ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖
      ≤ ∫ x, ‖k x‖ * height (γ x) ^ (m * N) * (|C| * K₀ ^ N * (Xn ^ n / G) ^ N) ∂ν :=
        norm_integral_le_of_norm_le (hint.mul_const _) (.of_forall fun x => by
          rw [norm_mul]
          calc ‖k x‖ * ‖F (g * c * infGL E a (γ x))‖
              ≤ ‖k x‖ * (|C| * K₀ ^ N * height (γ x) ^ (m * N) * (Xn ^ n / G) ^ N) :=
                mul_le_mul_of_nonneg_left (key _) (norm_nonneg _)
            _ = _ := by ring)
    _ = _ := by rw [integral_mul_const, hI]; ring

end GlobalTheory.RapidKernelDecay
