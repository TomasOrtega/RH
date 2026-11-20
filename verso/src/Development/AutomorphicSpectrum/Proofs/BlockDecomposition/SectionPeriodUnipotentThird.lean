import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierBoundSeminorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormWhittakerGL2LeIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceMapTemperate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionQuotientComplex

noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.PerUThreeC

def Ax (k : ℕ) (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) : ℂ :=
  W2 k (sl Ψ (Matrix.of.symm (Matrix.of h * blk x))) M

def Rw (k : ℕ) (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) : ℂ :=
  ∫ x0 : ℂ, Ax k Ψ h M ![x0, w]

/- English proof (translation)
Use `set Φ : ℂˣ → ℂ := fun t => chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * F (-(t : ℂ)⁻¹) with hΦ`. Establish `h1 : ∫ t, Φ t ∂mulC = ∫ t, Φ ((-1 : ℂˣ) * t) ∂mulC` using `(integral_mul_left_eq_self Φ (-1 : ℂˣ)).symm`. Establish `h2 : ∫ t, Φ ((-1 : ℂˣ) * t) ∂mulC = ∫ r, Φ ((-1 : ℂˣ) * r⁻¹) ∂mulC`. Use `(mp_inv.integral_comp (MeasurableEquiv.inv ℂˣ).measurableEmbedding (fun t => Φ ((-1 : ℂˣ) * t)))` as an intermediate fact. Conclude with `this.symm`.

Rewrite using `[h1, h2, z1, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)` and prove the remaining obligations. Establish `hz : (r : ℂ) ≠ 0` using `r.ne_zero`. Establish `hρ : 0 < ‖(r : ℂ)‖` using `norm_pos_iff.2 hz`. Use `set z : ℂ := (r : ℂ) with hzd`.

Use `set ρ : ℝ := ‖z‖ with hρd`. Establish `hρc : (ρ : ℂ) ≠ 0` using `by exact_mod_cast hρ.ne'`. Establish `hv : (((-1 : ℂˣ) * r⁻¹ : ℂˣ) : ℂ) = -z⁻¹` using `by simp [hzd]`. Establish `hn : ‖(-z⁻¹)‖ = ρ⁻¹` using `by simp [hρd]`. Use `set B : ℂ := ((ρ ^ 2 : ℝ) : ℂ) with hB`.

Establish `hB0 : B ≠ 0`. Rewrite using `[hB]`. Conclude with `(pow_pos hρ 2).ne'` after adjusting the coercions. Establish `harg : B.arg ≠ Real.pi`. Rewrite using `[hB, Complex.arg_ofReal_of_nonneg (by positivity)]`.

Conclude with `Real.pi_pos.ne`. Establish `hBi : (((ρ⁻¹) ^ 2 : ℝ) : ℂ) = B⁻¹`. Rewrite using `[hB]`. Use `push_cast`. Rewrite using `[inv_pow]`.

Establish `hpow : (B⁻¹) ^ s * B = B ^ (1 - s)`. Rewrite using `[Complex.inv_cpow _ _ harg, Complex.cpow_sub _ _ hB0, Complex.cpow_one]`. Clear the denominators using the available nonvanishing facts. Establish `hph : (-z⁻¹ / ((ρ⁻¹ : ℝ) : ℂ)) ^ n = (-1) ^ n * (z / (ρ : ℂ)) ^ (-n)`. Establish `: -z⁻¹ / ((ρ⁻¹ : ℝ) : ℂ) = (-1) * (z / (ρ : ℂ))⁻¹`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, mul_zpow, _root_.inv_zpow, _root_.zpow_neg]`. Simplify using `only [hΦ, chC, hv, hn, neg_neg, inv_inv]`. Establish `hFz : -(-z⁻¹)⁻¹ = z` using `by simp`.

Rewrite using `[hph, hBi, inv_inv, hFz]`. Express the relevant statement in the definitionally equal form `(-1) ^ n * (z / (ρ : ℂ)) ^ (-n) * B⁻¹ ^ s * B * F z = (-1) ^ n * (F z * ((z / (ρ : ℂ)) ^ (-n) * B ^ (1 - s)))`. Rewrite using `[← hpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem left_side (F : ℂ → ℂ) (n : ℤ) (s : ℂ) :
    ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * F (-(t : ℂ)⁻¹) ∂mulC =
      (-1) ^ n * z1 F (-n) (1 - s) := by
  set Φ : ℂˣ → ℂ := fun t => chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * F (-(t : ℂ)⁻¹) with hΦ
  have h1 : ∫ t, Φ t ∂mulC = ∫ t, Φ ((-1 : ℂˣ) * t) ∂mulC :=
    (integral_mul_left_eq_self Φ (-1 : ℂˣ)).symm
  have h2 : ∫ t, Φ ((-1 : ℂˣ) * t) ∂mulC = ∫ r, Φ ((-1 : ℂˣ) * r⁻¹) ∂mulC := by
    have := (mp_inv.integral_comp (MeasurableEquiv.inv ℂˣ).measurableEmbedding
      (fun t => Φ ((-1 : ℂˣ) * t)))
    exact this.symm
  rw [h1, h2, z1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  have hz : (r : ℂ) ≠ 0 := r.ne_zero
  have hρ : 0 < ‖(r : ℂ)‖ := norm_pos_iff.2 hz
  set z : ℂ := (r : ℂ) with hzd
  set ρ : ℝ := ‖z‖ with hρd
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hv : (((-1 : ℂˣ) * r⁻¹ : ℂˣ) : ℂ) = -z⁻¹ := by simp [hzd]
  have hn : ‖(-z⁻¹)‖ = ρ⁻¹ := by simp [hρd]
  set B : ℂ := ((ρ ^ 2 : ℝ) : ℂ) with hB
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact_mod_cast (pow_pos hρ 2).ne'
  have harg : B.arg ≠ Real.pi := by
    rw [hB, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  have hBi : (((ρ⁻¹) ^ 2 : ℝ) : ℂ) = B⁻¹ := by
    rw [hB]
    push_cast
    rw [inv_pow]
  have hpow : (B⁻¹) ^ s * B = B ^ (1 - s) := by
    rw [Complex.inv_cpow _ _ harg, Complex.cpow_sub _ _ hB0, Complex.cpow_one]
    field_simp
  have hph : (-z⁻¹ / ((ρ⁻¹ : ℝ) : ℂ)) ^ n = (-1) ^ n * (z / (ρ : ℂ)) ^ (-n) := by
    have : -z⁻¹ / ((ρ⁻¹ : ℝ) : ℂ) = (-1) * (z / (ρ : ℂ))⁻¹ := by
      push_cast
      field_simp
    rw [this, mul_zpow, _root_.inv_zpow, _root_.zpow_neg]
  simp only [hΦ, chC, hv, hn, neg_neg, inv_inv]
  have hFz : -(-z⁻¹)⁻¹ = z := by simp
  rw [hph, hBi, inv_inv, hFz]
  change (-1) ^ n * (z / (ρ : ℂ)) ^ (-n) * B⁻¹ ^ s * B * F z =
    (-1) ^ n * (F z * ((z / (ρ : ℂ)) ^ (-n) * B ^ (1 - s)))
  rw [← hpow]
  ring

/- English proof (translation)
Establish `h1 : z1 R n s = ∫ a : ℂˣ, (fun z : ℂ => R z * (ph n z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s)) a ∂mulC` using `rfl`. Rewrite using `[h1, integral_mulC (fun z : ℂ => R z * (ph n z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s))]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with w hw`. Establish `hw0 : w ≠ 0` using `hw`.

Establish `hB0 : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0`. Establish `: 0 < ‖w‖` using `norm_pos_iff.2 hw0`. Conclude with `(pow_pos this 2).ne'` after adjusting the coercions. Rewrite using `[Complex.cpow_sub _ _ hB0, Complex.cpow_one]`. Use `push_cast`.

Move the coercions through the operations in `at hB0`. Clear the denominators using the available nonvanishing facts.
-/
theorem tate_integral_eq_plane_integral (R : ℂ → ℂ) (n : ℤ) (s : ℂ) :
    z1 R n s = ∫ w : ℂ, ph n w * ((‖w‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * R w := by
  have h1 : z1 R n s = ∫ a : ℂˣ, (fun z : ℂ => R z * (ph n z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s)) a ∂mulC := rfl
  rw [h1, integral_mulC (fun z : ℂ => R z * (ph n z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s))]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with w hw
  have hw0 : w ≠ 0 := hw
  have hB0 : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖w‖ := norm_pos_iff.2 hw0
    exact_mod_cast (pow_pos this 2).ne'
  rw [Complex.cpow_sub _ _ hB0, Complex.cpow_one]
  push_cast
  push_cast at hB0
  field_simp

def rtL (G : Matrix (Fin 3) (Fin 3) ℂ) : (M23 × (Fin 2 → ℂ)) →ₗ[ℝ] (M23 × (Fin 2 → ℂ)) where
  toFun p := (Matrix.of.symm (Matrix.of p.1 * G), p.2)
  map_add' p q := by
    refine Prod.ext ?_ rfl
    have e : (Matrix.of (p.1 + q.1) : Matrix (Fin 2) (Fin 3) ℂ) = Matrix.of p.1 + Matrix.of q.1 := rfl
    change Matrix.of.symm (Matrix.of (p.1 + q.1) * G) = _
    rw [e, Matrix.add_mul]
    rfl
  map_smul' r p := by
    refine Prod.ext ?_ rfl
    have e : (Matrix.of (r • p.1) : Matrix (Fin 2) (Fin 3) ℂ) = r • Matrix.of p.1 := rfl
    change Matrix.of.symm (Matrix.of (r • p.1) * G) = r • _
    rw [e, Matrix.smul_mul]
    rfl

/- English proof (translation)
Use `set G : Matrix (Fin 3) (Fin 3) ℂ := (g : Matrix (Fin 3) (Fin 3) ℂ) with hG`. Establish `hGu : IsUnit G.det` using `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit`. Establish `hinj : Function.Injective (rtL G)`. Use `(injective_iff_map_eq_zero _).2 fun p hp => ?_` and prove the remaining obligations. Establish `e1 : Matrix.of p.1 * G = 0` using `congrArg Prod.fst hp`.

Establish `e2 : p.2 = 0` using `congrArg Prod.snd hp`. Establish `e3 : Matrix.of p.1 = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]`. Use `_ = 0 := by rw [e1]; simp`.

Conclude with `Prod.ext e3 e2`. Take `⟨K, -, hK⟩` from `(LinearMap.injective_iff_antilipschitz (rtL G)).1 hinj`. Establish `hT : Function.HasTemperateGrowth (rtL G)` using `(LinearMap.toContinuousLinearMap (rtL G)).hasTemperateGrowth`. Use `⟨SchwartzMap.compCLMOfAntilipschitz ℂ hT hK Ψ, fun X q => ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem right_translate (Ψ : Sw) (g : GL (Fin 3) ℂ) : ∃ Ψ' : Sw, ∀ (X : M23) (q : Fin 2 → ℂ),
    Ψ' (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℂ)), q) := by
  set G : Matrix (Fin 3) (Fin 3) ℂ := (g : Matrix (Fin 3) (Fin 3) ℂ) with hG
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  have hinj : Function.Injective (rtL G) := by
    refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
    have e1 : Matrix.of p.1 * G = 0 := congrArg Prod.fst hp
    have e2 : p.2 = 0 := congrArg Prod.snd hp
    have e3 : Matrix.of p.1 = 0 := by
      calc Matrix.of p.1 = Matrix.of p.1 * G * G⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]
        _ = 0 := by rw [e1]; simp
    exact Prod.ext e3 e2
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz (rtL G)).1 hinj
  have hT : Function.HasTemperateGrowth (rtL G) :=
    (LinearMap.toContinuousLinearMap (rtL G)).hasTemperateGrowth
  refine ⟨SchwartzMap.compCLMOfAntilipschitz ℂ hT hK Ψ, fun X q => ?_⟩
  rfl

/- English proof (translation)
Use `set m := max 1 (e ^ 2)⁻¹ with hm`. Establish `h1 : 1 ≤ m` using `le_max_left _ _`. Establish `h2 : 1 ≤ m * e ^ 2`. Establish `: (e ^ 2)⁻¹ ≤ m` using `le_max_right _ _`. Establish `he2 : 0 < e ^ 2` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `hb : 1 ≤ 1 + ρ * e` using `by nlinarith [mul_nonneg hρ he.le]`. Establish `h3 : (1 + ρ * e) ^ 2 ≤ (1 + ρ * e) ^ L` using `pow_le_pow_right₀ hb hL`. Establish `hp : 0 < 1 + ρ ^ 2` using `by positivity`. Establish `h4 : 1 + ρ ^ 2 ≤ m * (1 + ρ * e) ^ 2`.

Establish `a1 : 0 ≤ ρ * e` using `by positivity`. Establish `a2 : ρ ^ 2 ≤ m * e ^ 2 * ρ ^ 2` using `by nlinarith [sq_nonneg ρ]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← div_eq_mul_inv, inv_le_comm₀ (by positivity) (by positivity), inv_div]`. Rewrite using `[div_le_iff₀ (by linarith)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem decay_alg {ρ e : ℝ} (hρ : 0 ≤ ρ) (he : 0 < e) {L : ℕ} (hL : 2 ≤ L) :
    ((1 + ρ * e) ^ L)⁻¹ ≤ max 1 (e ^ 2)⁻¹ * (1 + ρ ^ 2)⁻¹ := by
  set m := max 1 (e ^ 2)⁻¹ with hm
  have h1 : 1 ≤ m := le_max_left _ _
  have h2 : 1 ≤ m * e ^ 2 := by
    have : (e ^ 2)⁻¹ ≤ m := le_max_right _ _
    have he2 : 0 < e ^ 2 := by positivity
    calc (1 : ℝ) = (e ^ 2)⁻¹ * e ^ 2 := by field_simp
      _ ≤ m * e ^ 2 := by gcongr
  have hb : 1 ≤ 1 + ρ * e := by nlinarith [mul_nonneg hρ he.le]
  have h3 : (1 + ρ * e) ^ 2 ≤ (1 + ρ * e) ^ L := pow_le_pow_right₀ hb hL
  have hp : 0 < 1 + ρ ^ 2 := by positivity
  have h4 : 1 + ρ ^ 2 ≤ m * (1 + ρ * e) ^ 2 := by
    have a1 : 0 ≤ ρ * e := by positivity
    have a2 : ρ ^ 2 ≤ m * e ^ 2 * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    nlinarith
  rw [← div_eq_mul_inv, inv_le_comm₀ (by positivity) (by positivity), inv_div]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

def vmL (M : Matrix (Fin 2) (Fin 2) ℂ) : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun v := Matrix.vecMul v M
  map_add' a b := Matrix.add_vecMul M a b
  map_smul' r a := by
    funext i
    simp [Matrix.vecMul, dotProduct, Finset.smul_sum, mul_assoc]

/- English proof (translation)
The claim follows from `(injective_iff_map_eq_zero _).2 fun _ hv => Matrix.eq_zero_of_vecMul_eq_zero hM hv`.
-/
theorem vmL_inj {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det ≠ 0) : Function.Injective (vmL M) :=
  (injective_iff_map_eq_zero _).2 fun _ hv => Matrix.eq_zero_of_vecMul_eq_zero hM hv

/- English proof (translation)
Establish `hp : ‖t‖ ≠ 0` using `norm_ne_zero_iff.2 ht`. Simplify using `only [dd, norm_inv, inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dd_inv_mul {t : ℂ} (ht : t ≠ 0) : (‖t‖ ^ 2)⁻¹ * (dd t * dd t⁻¹) = dd t ^ 2 := by
  have hp : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  simp only [dd, norm_inv, inv_pow]
  field_simp
  ring

/- English proof (translation)
Take `⟨K, -, hK⟩` from `(LinearMap.injective_iff_antilipschitz (vmL M)).1 (vmL_inj hM)`. Establish `hTg : Function.HasTemperateGrowth (vmL M)` using `(LinearMap.toContinuousLinearMap (vmL M)).hasTemperateGrowth`. Set `T : Unif.Sp →L[ℝ] Unif.Sp` to `SchwartzMap.compCLMOfAntilipschitz ℝ hTg hK`. Establish `hTa : ∀ (f : Unif.Sp) (v : Fin 2 → ℂ), T f v = f (Matrix.vecMul v M)` using `fun _ _ => rfl`. Take `⟨N0, D0, hD0, b0⟩` from `Unif.exists_P6_comp_le_mul_seminorm T`.

Take `⟨N1, D1, hD1, b1⟩` from `Unif.exists_P6_comp_le_mul_seminorm ((Unif.T2 1).comp T)`. Take `⟨N2, D2, hD2, b2⟩` from `Unif.exists_P6_comp_le_mul_seminorm ((Unif.T2 Complex.I).comp T)`. Establish `hc` using `Unif.weightConst_nonneg`. Use `⟨Unif.c0 * (D0 + D1 + D2), max N0 (max N1 N2), by positivity, fun f t ht => ?_⟩` and prove the remaining obligations. Use `set N := max N0 (max N1 N2) with hN`.

Use `set A := pS N f with hA`. Establish `h0 : Unif.P6 (T f) ≤ D0 * A` using `(b0 f).trans (mul_le_mul_of_nonneg_left (Unif.pS_mono (le_max_left _ _) f) hD0)`. Establish `h1 : Unif.P6 (Unif.T2 1 (T f)) ≤ D1 * A` using `(b1 f).trans (mul_le_mul_of_nonneg_left (Unif.pS_mono ((le_max_left _ _).trans (le_max_right _ _)) f) hD1)`. Establish `h2 : Unif.P6 (Unif.T2 Complex.I (T f)) ≤ D2 * A` using `(b2 f).trans (mul_le_mul_of_nonneg_left (Unif.pS_mono ((le_max_right _ _).trans (le_max_right _ _)) f) hD2)`. Establish `hdx` using `(dd_pos t).le`.

Establish `key : ∀ (g : Unif.Sp) (B : ℝ), Unif.P6 g ≤ B → ‖sF g t t⁻¹‖ ≤ Unif.c0 * B * dd t` using `fun g B hB => (Unif.sF_bound_unif g t t⁻¹).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hc) hdx)`. Establish `hdec` using `Unif.decay_of_bounds (T f) (Unif.c0 * (D0 * A)) (Unif.c0 * (D1 * A)) (Unif.c0 * (D2 * A)) t t⁻¹ (key _ _ h0) (by rw [← Unif.secondLineDeriv_apply]; exact key _ _ h1) (by rw [← Unif.secondLineDeriv_apply]; exact key _ _ h2)`. Establish `hin` using `norm_inner_tri (⇑(T f)) t 0 t ht`. Simplify using `only [zero_add, hTa] at hin`. Rewrite using `[hin]`.

Establish `hp : 0 ≤ (‖t‖ ^ 2)⁻¹` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem row_bound (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (t : ℂ), t ≠ 0 →
      ‖∫ y : ℂ, f (Matrix.vecMul ![t, t * y] M) * psiC (-y)‖ ≤ C * pS N f * dd t ^ 2 := by
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz (vmL M)).1 (vmL_inj hM)
  have hTg : Function.HasTemperateGrowth (vmL M) :=
    (LinearMap.toContinuousLinearMap (vmL M)).hasTemperateGrowth
  let T : Unif.Sp →L[ℝ] Unif.Sp := SchwartzMap.compCLMOfAntilipschitz ℝ hTg hK
  have hTa : ∀ (f : Unif.Sp) (v : Fin 2 → ℂ), T f v = f (Matrix.vecMul v M) := fun _ _ => rfl
  obtain ⟨N0, D0, hD0, b0⟩ := Unif.exists_P6_comp_le_mul_seminorm T
  obtain ⟨N1, D1, hD1, b1⟩ := Unif.exists_P6_comp_le_mul_seminorm ((Unif.T2 1).comp T)
  obtain ⟨N2, D2, hD2, b2⟩ := Unif.exists_P6_comp_le_mul_seminorm ((Unif.T2 Complex.I).comp T)
  have hc := Unif.weightConst_nonneg
  refine ⟨Unif.c0 * (D0 + D1 + D2), max N0 (max N1 N2), by positivity, fun f t ht => ?_⟩
  set N := max N0 (max N1 N2) with hN
  set A := pS N f with hA
  have h0 : Unif.P6 (T f) ≤ D0 * A :=
    (b0 f).trans (mul_le_mul_of_nonneg_left (Unif.pS_mono (le_max_left _ _) f) hD0)
  have h1 : Unif.P6 (Unif.T2 1 (T f)) ≤ D1 * A :=
    (b1 f).trans (mul_le_mul_of_nonneg_left
      (Unif.pS_mono ((le_max_left _ _).trans (le_max_right _ _)) f) hD1)
  have h2 : Unif.P6 (Unif.T2 Complex.I (T f)) ≤ D2 * A :=
    (b2 f).trans (mul_le_mul_of_nonneg_left
      (Unif.pS_mono ((le_max_right _ _).trans (le_max_right _ _)) f) hD2)
  have hdx := (dd_pos t).le
  have key : ∀ (g : Unif.Sp) (B : ℝ), Unif.P6 g ≤ B → ‖sF g t t⁻¹‖ ≤ Unif.c0 * B * dd t := fun g B hB =>
    (Unif.sF_bound_unif g t t⁻¹).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB hc) hdx)
  have hdec := Unif.decay_of_bounds (T f) (Unif.c0 * (D0 * A)) (Unif.c0 * (D1 * A)) (Unif.c0 * (D2 * A)) t t⁻¹
    (key _ _ h0) (by rw [← Unif.secondLineDeriv_apply]; exact key _ _ h1) (by rw [← Unif.secondLineDeriv_apply]; exact key _ _ h2)
  have hin := norm_inner_tri (⇑(T f)) t 0 t ht
  simp only [zero_add, hTa] at hin
  rw [hin]
  have hp : 0 ≤ (‖t‖ ^ 2)⁻¹ := by positivity
  calc (‖t‖ ^ 2)⁻¹ * ‖sF (fun v => f (Matrix.vecMul v M)) t t⁻¹‖
      ≤ (‖t‖ ^ 2)⁻¹ * ((Unif.c0 * (D0 * A) + Unif.c0 * (D1 * A) + Unif.c0 * (D2 * A)) * (dd t * dd t⁻¹)) :=
        mul_le_mul_of_nonneg_left hdec hp
    _ = (Unif.c0 * (D0 + D1 + D2) * A) * ((‖t‖ ^ 2)⁻¹ * (dd t * dd t⁻¹)) := by ring
    _ = _ := by rw [dd_inv_mul ht]

/- English proof (translation)
Use `set I := ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ) with hI`. Establish `e : ⇑f = (fun p => Ψ (p + (X, 0))) ∘ I`. Rewrite using `[hf]`. Use function extensionality and compare the values at `v`. Simplify using `[sl, hI]`.

Establish `hc : ContDiff ℝ (⊤ : ℕ∞) (fun p => Ψ (p + ((X, 0) : M23 × (Fin 2 → ℂ))))` using `(Ψ.smooth ⊤).comp (by fun_prop)`. Rewrite using `[e, I.iteratedFDeriv_comp_right hc q (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]`. Establish `hx : I q + ((X, 0) : M23 × (Fin 2 → ℂ)) = (X, q)` using `by simp [hI]`. Rewrite using `[hx]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations.

Establish `h1 : ‖I‖ ≤ 1` using `ContinuousLinearMap.norm_inr_le_one ℝ M23 (Fin 2 → ℂ)`. Establish `h2 : ∏ _i : Fin j, ‖I‖ ≤ 1`. Rewrite using `[Finset.prod_const]`. Conclude with `pow_le_one₀ (norm_nonneg _) h1`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) h2`.
-/
theorem slice_iter (Ψ : Sw) (X : M23) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (hf : ⇑f = sl Ψ X) (j : ℕ)
    (q : Fin 2 → ℂ) : ‖iteratedFDeriv ℝ j f q‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, q)‖ := by
  set I := ContinuousLinearMap.inr ℝ M23 (Fin 2 → ℂ) with hI
  have e : ⇑f = (fun p => Ψ (p + (X, 0))) ∘ I := by
    rw [hf]
    funext v
    simp [sl, hI]
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p => Ψ (p + ((X, 0) : M23 × (Fin 2 → ℂ)))) :=
    (Ψ.smooth ⊤).comp (by fun_prop)
  rw [e, I.iteratedFDeriv_comp_right hc q (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]
  have hx : I q + ((X, 0) : M23 × (Fin 2 → ℂ)) = (X, q) := by simp [hI]
  rw [hx]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ M23 (Fin 2 → ℂ)
  have h2 : ∏ _i : Fin j, ‖I‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) h1
  exact mul_le_of_le_one_right (norm_nonneg _) h2

/- English proof (translation)
Use `set S : ℝ := (Finset.Iic ((N + L, N) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hS`. Establish `hS0 : 0 ≤ S` using `apply_nonneg _ _`. Use `⟨(N + 1) * (N + 1) * (2 ^ (N + L) * S), by positivity, fun X f hf => ?_⟩` and prove the remaining obligations. Establish `hXp : 0 < (1 + ‖X‖) ^ L` using `by positivity`. Establish `hij : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℝ i j f ≤ 2 ^ (N + L) * S / (1 + ‖X‖) ^ L`.

Introduce `i hi j hj`. Establish `hi' : i ≤ N` using `by simpa [Nat.lt_succ_iff] using hi`. Establish `hj' : j ≤ N` using `by simpa [Nat.lt_succ_iff] using hj`. Use `SchwartzMap.seminorm_le_bound ℝ i j f (by positivity) fun q => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hXp]`.

Establish `hb` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((N + L, N) : ℕ × ℕ)) (k := N + L) (n := j) le_rfl hj' Ψ (X, q)`. Establish `hq : ‖q‖ ≤ ‖((X, q) : M23 × (Fin 2 → ℂ))‖` using `le_max_right _ _`. Establish `hx : ‖X‖ ≤ ‖((X, q) : M23 × (Fin 2 → ℂ))‖` using `le_max_left _ _`. Use `set P := ‖((X, q) : M23 × (Fin 2 → ℂ))‖ with hP`. Establish `hP0 : 0 ≤ P` using `norm_nonneg _`.

Establish `e1 : ‖q‖ ^ i * (1 + ‖X‖) ^ L ≤ (1 + P) ^ (N + L)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul ?_ ?_ (by positivity) (by positivity)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `gcongr`.

Use `_ = _ := by rw [pow_add]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : pS N f ≤ (N + 1) * (N + 1) * (2 ^ (N + L) * S / (1 + ‖X‖) ^ L)`. Unfold `pS`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem slice_decay (Ψ : Sw) (N L : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : M23) (f : SchwartzMap (Fin 2 → ℂ) ℂ),
    ⇑f = sl Ψ X → (1 + ‖X‖) ^ L * pS N f ≤ C := by
  set S : ℝ := (Finset.Iic ((N + L, N) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  refine ⟨(N + 1) * (N + 1) * (2 ^ (N + L) * S), by positivity, fun X f hf => ?_⟩
  have hXp : 0 < (1 + ‖X‖) ^ L := by positivity
  have hij : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      SchwartzMap.seminorm ℝ i j f ≤ 2 ^ (N + L) * S / (1 + ‖X‖) ^ L := by
    intro i hi j hj
    have hi' : i ≤ N := by simpa [Nat.lt_succ_iff] using hi
    have hj' : j ≤ N := by simpa [Nat.lt_succ_iff] using hj
    refine SchwartzMap.seminorm_le_bound ℝ i j f (by positivity) fun q => ?_
    rw [le_div_iff₀ hXp]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((N + L, N) : ℕ × ℕ)) (k := N + L) (n := j)
      le_rfl hj' Ψ (X, q)
    have hq : ‖q‖ ≤ ‖((X, q) : M23 × (Fin 2 → ℂ))‖ := le_max_right _ _
    have hx : ‖X‖ ≤ ‖((X, q) : M23 × (Fin 2 → ℂ))‖ := le_max_left _ _
    set P := ‖((X, q) : M23 × (Fin 2 → ℂ))‖ with hP
    have hP0 : 0 ≤ P := norm_nonneg _
    have e1 : ‖q‖ ^ i * (1 + ‖X‖) ^ L ≤ (1 + P) ^ (N + L) := by
      calc ‖q‖ ^ i * (1 + ‖X‖) ^ L ≤ (1 + P) ^ N * (1 + P) ^ L := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · calc ‖q‖ ^ i ≤ (1 + P) ^ i := by gcongr; linarith
                _ ≤ (1 + P) ^ N := pow_le_pow_right₀ (by linarith) hi'
            · gcongr
        _ = _ := by rw [pow_add]
    calc ‖q‖ ^ i * ‖iteratedFDeriv ℝ j f q‖ * (1 + ‖X‖) ^ L
        = (‖q‖ ^ i * (1 + ‖X‖) ^ L) * ‖iteratedFDeriv ℝ j f q‖ := by ring
      _ ≤ (1 + P) ^ (N + L) * ‖iteratedFDeriv ℝ j Ψ (X, q)‖ :=
          mul_le_mul e1 (slice_iter Ψ X f hf j q) (norm_nonneg _) (by positivity)
      _ ≤ _ := hb
  have hsum : pS N f ≤ (N + 1) * (N + 1) * (2 ^ (N + L) * S / (1 + ‖X‖) ^ L) := by
    unfold pS
    calc _ ≤ ∑ _i ∈ Finset.range (N + 1), ∑ _j ∈ Finset.range (N + 1), 2 ^ (N + L) * S / (1 + ‖X‖) ^ L :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hij i hi j hj
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc (1 + ‖X‖) ^ L * pS N f ≤ (1 + ‖X‖) ^ L * ((N + 1) * (N + 1) * (2 ^ (N + L) * S / (1 + ‖X‖) ^ L)) :=
        mul_le_mul_of_nonneg_left hsum hXp.le
    _ = _ := by field_simp

def ellL (h : M22) : (Fin 2 → ℂ) →ₗ[ℝ] M23 where
  toFun x := Matrix.of.symm (Matrix.of h * GlobalTheory.CompanionTheory.SecFubini.nb x)
  map_add' a b := by
    rw [GlobalTheory.CompanionTheory.SecFubini.nb_add, Matrix.mul_add]
    rfl
  map_smul' r a := by
    rw [GlobalTheory.CompanionTheory.SecFubini.nb_smul, Matrix.mul_smul]
    rfl

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Establish `hu : IsUnit (Matrix.of h).det` using `isUnit_iff_ne_zero.2 hh`. Establish `e1 : Matrix.of h * GlobalTheory.CompanionTheory.SecFubini.nb x = 0` using `hx`. Establish `e2 : GlobalTheory.CompanionTheory.SecFubini.nb x = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Use `_ = 0 := by rw [e1]; simp`. Use extensionality with `i`. Use `congrFun (congrFun e2 i) 2` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> simpa [GlobalTheory.CompanionTheory.SecFubini.nb] using this`.
-/
theorem ellL_inj {h : M22} (hh : (Matrix.of h).det ≠ 0) : Function.Injective (ellL h) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hu : IsUnit (Matrix.of h).det := isUnit_iff_ne_zero.2 hh
  have e1 : Matrix.of h * GlobalTheory.CompanionTheory.SecFubini.nb x = 0 := hx
  have e2 : GlobalTheory.CompanionTheory.SecFubini.nb x = 0 := by
    calc GlobalTheory.CompanionTheory.SecFubini.nb x = (Matrix.of h)⁻¹ * (Matrix.of h * GlobalTheory.CompanionTheory.SecFubini.nb x) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [e1]; simp
  ext i
  have := congrFun (congrFun e2 i) 2
  fin_cases i <;> simpa [GlobalTheory.CompanionTheory.SecFubini.nb] using this

def cstX (h : M22) : M23 := Matrix.of.symm (Matrix.of h * blk 0)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = Matrix.of.symm (Matrix.of h * GlobalTheory.CompanionTheory.SecFubini.nb x + Matrix.of h * blk 0)`. Rewrite using `[GlobalTheory.CompanionTheory.SecFubini.blk_eq x, Matrix.mul_add]`.
-/
theorem x_affine (h : M22) (x : Fin 2 → ℂ) :
    (Matrix.of.symm (Matrix.of h * blk x) : M23) = ellL h x + cstX h := by
  change _ = Matrix.of.symm (Matrix.of h * GlobalTheory.CompanionTheory.SecFubini.nb x + Matrix.of h * blk 0)
  rw [GlobalTheory.CompanionTheory.SecFubini.blk_eq x, Matrix.mul_add]

/- English proof (translation)
Take `⟨K, -, hK⟩` from `(LinearMap.injective_iff_antilipschitz (ellL h)).1 (ellL_inj hh)`. Use `⟨1 + K + K * ‖cstX h‖, by positivity, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖x‖ ≤ K * ‖ellL h x‖`. Use `hK.le_mul_dist x 0` as an intermediate fact. Simplify `this` using `[dist_zero_right]`.

Rewrite using `[x_affine]`. Use `set Y := ellL h x + cstX h with hY`. Establish `h2 : ‖ellL h x‖ ≤ ‖Y‖ + ‖cstX h‖`. Establish `: ellL h x = Y - cstX h` using `by rw [hY]; abel`. Rewrite using `[this]`.

Conclude with `norm_sub_le _ _`. Establish `hK0 : (0 : ℝ) ≤ K` using `K.2`. Establish `hYn` using `norm_nonneg Y`. Establish `hcn` using `norm_nonneg (cstX h)`. Establish `h3 : K * ‖ellL h x‖ ≤ K * (‖Y‖ + ‖cstX h‖)` using `mul_le_mul_of_nonneg_left h2 hK0`.

Use polynomial arithmetic with `[mul_nonneg hK0 hYn, mul_nonneg (mul_nonneg hK0 hcn) hYn]`.
-/
theorem x_lower (h : M22) (hh : (Matrix.of h).det ≠ 0) : ∃ c : ℝ, 0 < c ∧ ∀ x : Fin 2 → ℂ,
    1 + ‖x‖ ≤ c * (1 + ‖(Matrix.of.symm (Matrix.of h * blk x) : M23)‖) := by
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz (ellL h)).1 (ellL_inj hh)
  refine ⟨1 + K + K * ‖cstX h‖, by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ K * ‖ellL h x‖ := by
    have := hK.le_mul_dist x 0
    simpa [dist_zero_right] using this
  rw [x_affine]
  set Y := ellL h x + cstX h with hY
  have h2 : ‖ellL h x‖ ≤ ‖Y‖ + ‖cstX h‖ := by
    have : ellL h x = Y - cstX h := by rw [hY]; abel
    rw [this]
    exact norm_sub_le _ _
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hYn := norm_nonneg Y
  have hcn := norm_nonneg (cstX h)
  have h3 : K * ‖ellL h x‖ ≤ K * (‖Y‖ + ‖cstX h‖) := mul_le_mul_of_nonneg_left h2 hK0
  nlinarith [mul_nonneg hK0 hYn, mul_nonneg (mul_nonneg hK0 hcn) hYn]

/- English proof (translation)
Establish `: (fun x : Fin 2 → ℂ => (Matrix.of.symm (Matrix.of h * blk x) : M23)) = fun x => ellL h x + cstX h`. Use function extensionality and compare the values at `(x_affine h)`. Rewrite using `[this]`. Conclude with `(LinearMap.continuous_of_finiteDimensional (ellL h)).add continuous_const`.
-/
theorem continuous_X (h : M22) : Continuous fun x : Fin 2 → ℂ => (Matrix.of.symm (Matrix.of h * blk x) : M23) := by
  have : (fun x : Fin 2 → ℂ => (Matrix.of.symm (Matrix.of h * blk x) : M23)) = fun x => ellL h x + cstX h :=
    funext (x_affine h)
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional (ellL h)).add continuous_const

/- English proof (translation)
Use `Continuous.mul (Ψ.continuous.comp (Continuous.prodMk ?_ ?_)) (continuous_psiC.comp (by fun_prop))` and prove the remaining obligations. Conclude with `(continuous_X h).comp (by fun_prop)`. Conclude with `Continuous.matrix_vecMul (continuous_vec.comp (Continuous.prodMk (by fun_prop) (by fun_prop))) continuous_const`.
-/
theorem continuous_G (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun p : ((Fin 2 → ℂ) × ℂ) × ℂ =>
      Ψ (Matrix.of.symm (Matrix.of h * blk p.1.1), Matrix.vecMul ![p.1.2, p.1.2 * p.2] M) * psiC (-p.2) := by
  refine Continuous.mul (Ψ.continuous.comp (Continuous.prodMk ?_ ?_)) (continuous_psiC.comp (by fun_prop))
  · exact (continuous_X h).comp (by fun_prop)
  · exact Continuous.matrix_vecMul (continuous_vec.comp (Continuous.prodMk (by fun_prop) (by fun_prop))) continuous_const

def Gy (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (t : ℂ) : ℂ :=
  ∫ y : ℂ, Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) * psiC (-y)

/- English proof (translation)
The claim follows from `(continuous_G Ψ h M).stronglyMeasurable.integral_prod_right'`.
-/
theorem Gy_sm (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    StronglyMeasurable (fun p : (Fin 2 → ℂ) × ℂ => Gy Ψ h M p.1 p.2) :=
  (continuous_G Ψ h M).stronglyMeasurable.integral_prod_right'

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ax_eq (k : ℕ) (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    Ax k Ψ h M x = ph (2 * (k : ℤ) - 2) M.det * ((‖M.det‖ : ℝ) : ℂ) *
      ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t * Gy Ψ h M x t := rfl

/- English proof (translation)
Establish `hT : StronglyMeasurable fun p : (Fin 2 → ℂ) × ℂ => ph (4 * (k : ℤ) - 4) p.2` using `((measurable_ph _).comp measurable_snd).stronglyMeasurable`. Establish `hH : StronglyMeasurable fun x : Fin 2 → ℂ => ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t * Gy Ψ h M x t` using `(hT.mul (Gy_sm Ψ h M)).integral_prod_right'`. Conclude with `(funext (Ax_eq k Ψ h M) : Ax k Ψ h M = _) ▸ hH.const_mul _`.
-/
theorem ax_sm (k : ℕ) (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    StronglyMeasurable (Ax k Ψ h M) := by
  have hT : StronglyMeasurable fun p : (Fin 2 → ℂ) × ℂ => ph (4 * (k : ℤ) - 4) p.2 :=
    ((measurable_ph _).comp measurable_snd).stronglyMeasurable
  have hH : StronglyMeasurable fun x : Fin 2 → ℂ => ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t * Gy Ψ h M x t :=
    (hT.mul (Gy_sm Ψ h M)).integral_prod_right'
  exact (funext (Ax_eq k Ψ h M) : Ax k Ψ h M = _) ▸ hH.const_mul _

/- English proof (translation)
Take `⟨C1, N, hC1, hR⟩` from `row_bound M hM`. Take `⟨C2, hC2, hS⟩` from `slice_decay Ψ N 5`. Take `⟨c, hc, hX⟩` from `x_lower h hh`. Use `⟨C1 * (C2 * c ^ 5), by positivity, fun x t ht => ?_⟩` and prove the remaining obligations. Use `set X : M23 := Matrix.of.symm (Matrix.of h * blk x) with hXd`.

Take `⟨f, hf⟩` from `GlobalTheory.CompanionTheory.SchwartzSlice.slices_schwartz Ψ X`. Establish `hG : Gy Ψ h M x t = ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] M) * psiC (-y)`. Rewrite using `[Gy, hf]`. Both sides reduce to the same expression. Establish `h1` using `hS X f hf`.

Establish `h2` using `hX x`. Rewrite `h2` using `[← hXd]`. Establish `hx0 : 0 < 1 + ‖x‖` using `by positivity`. Establish `e5 : (1 + ‖x‖) ^ (-(5 : ℝ)) = ((1 + ‖x‖) ^ 5)⁻¹`. Rewrite using `[Real.rpow_neg hx0.le]`.

Use `norm_cast`. Establish `h3 : (1 + ‖x‖) ^ 5 ≤ c ^ 5 * (1 + ‖X‖) ^ 5`. Rewrite using `[← mul_pow]`. Use `gcongr`. Establish `hP` using `Unif.pS_nonneg N f`.

Establish `h4 : pS N f ≤ C2 * c ^ 5 * ((1 + ‖x‖) ^ 5)⁻¹`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hG, e5]`. Use `(hR f t ht).trans ?_` and prove the remaining obligations.

Establish `hd : 0 ≤ dd t ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gy_bound (Ψ : Sw) {h : M22} {M : Matrix (Fin 2) (Fin 2) ℂ} (hh : (Matrix.of h).det ≠ 0)
    (hM : M.det ≠ 0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin 2 → ℂ) (t : ℂ), t ≠ 0 →
      ‖Gy Ψ h M x t‖ ≤ C * ((1 + ‖x‖) ^ (-(5 : ℝ)) * dd t ^ 2) := by
  obtain ⟨C1, N, hC1, hR⟩ := row_bound M hM
  obtain ⟨C2, hC2, hS⟩ := slice_decay Ψ N 5
  obtain ⟨c, hc, hX⟩ := x_lower h hh
  refine ⟨C1 * (C2 * c ^ 5), by positivity, fun x t ht => ?_⟩
  set X : M23 := Matrix.of.symm (Matrix.of h * blk x) with hXd
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.SchwartzSlice.slices_schwartz Ψ X
  have hG : Gy Ψ h M x t = ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] M) * psiC (-y) := by
    rw [Gy, hf]
    rfl
  have h1 := hS X f hf
  have h2 := hX x
  rw [← hXd] at h2
  have hx0 : 0 < 1 + ‖x‖ := by positivity
  have e5 : (1 + ‖x‖) ^ (-(5 : ℝ)) = ((1 + ‖x‖) ^ 5)⁻¹ := by
    rw [Real.rpow_neg hx0.le]
    norm_cast
  have h3 : (1 + ‖x‖) ^ 5 ≤ c ^ 5 * (1 + ‖X‖) ^ 5 := by
    rw [← mul_pow]
    gcongr
  have hP := Unif.pS_nonneg N f
  have h4 : pS N f ≤ C2 * c ^ 5 * ((1 + ‖x‖) ^ 5)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc pS N f * (1 + ‖x‖) ^ 5 ≤ pS N f * (c ^ 5 * (1 + ‖X‖) ^ 5) :=
          mul_le_mul_of_nonneg_left h3 hP
      _ = c ^ 5 * ((1 + ‖X‖) ^ 5 * pS N f) := by ring
      _ ≤ c ^ 5 * C2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  rw [hG, e5]
  refine (hR f t ht).trans ?_
  have hd : 0 ≤ dd t ^ 2 := by positivity
  calc C1 * pS N f * dd t ^ 2 ≤ C1 * (C2 * c ^ 5 * ((1 + ‖x‖) ^ 5)⁻¹) * dd t ^ 2 := by gcongr
    _ = _ := by ring

def rowL (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : ℂ →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun y := Matrix.vecMul ![0, t * y] M
  map_add' a b := by
    have h2 : (![0, t * (a + b)] : Fin 2 → ℂ) = ![0, t * a] + ![0, t * b] := by
      ext i; fin_cases i <;> simp [mul_add]
    rw [h2, Matrix.add_vecMul]
  map_smul' r a := by
    have h2 : (![0, t * (r • a)] : Fin 2 → ℂ) = r • ![0, t * a] := by
      ext i; fin_cases i <;> simp; ring
    rw [h2, Matrix.smul_vecMul]
    rfl

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun y hy => ?_` and prove the remaining obligations. Establish `h1 : (![0, t * y] : Fin 2 → ℂ) = 0` using `Matrix.eq_zero_of_vecMul_eq_zero hM hy`. Use `congrFun h1 1` as an intermediate fact. Simplify `this` using `[ht]`.
-/
theorem rowL_inj {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    Function.Injective (rowL M t) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have h1 : (![0, t * y] : Fin 2 → ℂ) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hM hy
  have := congrFun h1 1
  simpa [ht] using this

/- English proof (translation)
Use `haveI hHaar : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by`. Rewrite using `[Measure.volume_eq_prod]`. Conclude with `Measure.prod.instIsAddHaarMeasure _ _`. Use `haveI : (volume : Measure ((Fin 2 → ℂ) × ℂ)).HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`. Establish `hI` using `GlobalTheory.CompanionTheory.SecFubini.integrable_schwartz_affine (volume : Measure ((Fin 2 → ℂ) × ℂ)) ((ellL h).prodMap (rowL M t)) ((ellL_inj hh).prodMap (rowL_inj hM ht)) (cstX h, Matrix.vecMul ![t, 0] M) Ψ`.

Establish `hL : (fun p : (Fin 2 → ℂ) × ℂ => Ψ ((ellL h).prodMap (rowL M t) p + (cstX h, Matrix.vecMul ![t, 0] M))) = fun p => Ψ (Matrix.of.symm (Matrix.of h * blk p.1), Matrix.vecMul ![t, t * p.2] M)`. Use function extensionality and compare the values at `p`. Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `(x_affine h p.1).symm`.

Express the relevant statement in the definitionally equal form `Matrix.vecMul ![0, t * p.2] M + Matrix.vecMul ![t, 0] M = _`. Establish `h2 : (![t, t * p.2] : Fin 2 → ℂ) = ![0, t * p.2] + ![t, 0]`. Apply the tactic sequence `ext i; fin_cases i <;> simp`. Rewrite using `[h2, Matrix.add_vecMul]`. Rewrite `hI` using `[hL]`.

Use `hI.mono ?_ (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Use `(hI.aestronglyMeasurable.mul ?_).mul ?_` and prove the remaining obligations. Conclude with `(continuous_psiC.comp (by fun_prop)).aestronglyMeasurable`. Conclude with `(continuous_psiC.comp (by fun_prop)).aestronglyMeasurable`. Simplify using `[norm_psiC]`.
-/
theorem xy_int (Ψ : Sw) {h : M22} {M : Matrix (Fin 2) (Fin 2) ℂ} (hh : (Matrix.of h).det ≠ 0)
    (hM : M.det ≠ 0) {t : ℂ} (ht : t ≠ 0) (β : ℂ) :
    Integrable (fun p : (Fin 2 → ℂ) × ℂ =>
      Ψ (Matrix.of.symm (Matrix.of h * blk p.1), Matrix.vecMul ![t, t * p.2] M) *
        psiC (-(β * p.1 1)) * psiC (-p.2)) := by
  haveI hHaar : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure ((Fin 2 → ℂ) × ℂ)).HasTemperateGrowth :=
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hI := GlobalTheory.CompanionTheory.SecFubini.integrable_schwartz_affine (volume : Measure ((Fin 2 → ℂ) × ℂ))
    ((ellL h).prodMap (rowL M t)) ((ellL_inj hh).prodMap (rowL_inj hM ht))
    (cstX h, Matrix.vecMul ![t, 0] M) Ψ
  have hL : (fun p : (Fin 2 → ℂ) × ℂ => Ψ ((ellL h).prodMap (rowL M t) p +
      (cstX h, Matrix.vecMul ![t, 0] M))) =
      fun p => Ψ (Matrix.of.symm (Matrix.of h * blk p.1), Matrix.vecMul ![t, t * p.2] M) := by
    funext p
    congr 1
    refine Prod.ext ?_ ?_
    · exact (x_affine h p.1).symm
    · change Matrix.vecMul ![0, t * p.2] M + Matrix.vecMul ![t, 0] M = _
      have h2 : (![t, t * p.2] : Fin 2 → ℂ) = ![0, t * p.2] + ![t, 0] := by
        ext i; fin_cases i <;> simp
      rw [h2, Matrix.add_vecMul]
  rw [hL] at hI
  refine hI.mono ?_ (ae_of_all _ fun p => ?_)
  · refine (hI.aestronglyMeasurable.mul ?_).mul ?_
    · exact (continuous_psiC.comp (by fun_prop)).aestronglyMeasurable
    · exact (continuous_psiC.comp (by fun_prop)).aestronglyMeasurable
  · simp [norm_psiC]

/- English proof (translation)
Establish `hI` using `xy_int Ψ hh hM ht β`. Rewrite `hI` using `[Measure.volume_eq_prod]`. Establish `hsw` using `integral_integral_swap (f := fun (x : Fin 2 → ℂ) (y : ℂ) => Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) * psiC (-(β * x 1)) * psiC (-y)) hI`. Establish `e1 : ∀ y : ℂ, innQ Ψ 1 h β (Matrix.vecMul ![t, t * y] M) * psiC (-y) = ∫ x : Fin 2 → ℂ, Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) * psiC (-(β * x 1)) * psiC (-y)`. Introduce `y`.

Rewrite using `[integral_mul_const, innQ]`. Simplify using the standard rewrite rules. Establish `e2 : ∀ x : Fin 2 → ℂ, Gy Ψ h M x t * psiC (-(β * x 1)) = ∫ y : ℂ, Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) * psiC (-(β * x 1)) * psiC (-y)`. Introduce `x`. Rewrite using `[Gy, ← integral_mul_const]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1, e2]`. Conclude with `hsw.symm`.
-/
theorem inner_swap (Ψ : Sw) {h : M22} {M : Matrix (Fin 2) (Fin 2) ℂ} (hh : (Matrix.of h).det ≠ 0)
    (hM : M.det ≠ 0) {t : ℂ} (ht : t ≠ 0) (β : ℂ) :
    ∫ y : ℂ, innQ Ψ 1 h β (Matrix.vecMul ![t, t * y] M) * psiC (-y) =
      ∫ x : Fin 2 → ℂ, Gy Ψ h M x t * psiC (-(β * x 1)) := by
  have hI := xy_int Ψ hh hM ht β
  rw [Measure.volume_eq_prod] at hI
  have hsw := integral_integral_swap (f := fun (x : Fin 2 → ℂ) (y : ℂ) =>
      Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) *
        psiC (-(β * x 1)) * psiC (-y)) hI
  have e1 : ∀ y : ℂ, innQ Ψ 1 h β (Matrix.vecMul ![t, t * y] M) * psiC (-y) =
      ∫ x : Fin 2 → ℂ, Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) *
        psiC (-(β * x 1)) * psiC (-y) := by
    intro y
    rw [integral_mul_const, innQ]
    simp
  have e2 : ∀ x : Fin 2 → ℂ, Gy Ψ h M x t * psiC (-(β * x 1)) =
      ∫ y : ℂ, Ψ (Matrix.of.symm (Matrix.of h * blk x), Matrix.vecMul ![t, t * y] M) *
        psiC (-(β * x 1)) * psiC (-y) := by
    intro x
    rw [Gy, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  simp only [e1, e2]
  exact hsw.symm

/- English proof (translation)
Take `⟨C, hC0, hb⟩` from `gy_bound Ψ hh hM`. Establish `hxw : Integrable (fun x : Fin 2 → ℂ => (1 + ‖x‖) ^ (-(5 : ℝ)))`. Use `integrable_one_add_norm ?_` and prove the remaining obligations. Simplify using `[Module.finrank_pi_fintype]`. Evaluate the numerical expressions.

Use `set P := ph (4 * (k : ℤ) - 4) with hPd`. Establish `hJ : Integrable (Function.uncurry fun (t : ℂ) (x : Fin 2 → ℂ) => P t * Gy Ψ h M x t * psiC (-(β * x 1))) ((volume : Measure ℂ).prod (volume : Measure (Fin 2 → ℂ)))`. Establish `hd` using `(dd_sq_int.mul_prod hxw).const_mul C`. Use `hd.mono' ?_ ?_` and prove the remaining obligations. Establish `h1 : AEStronglyMeasurable (fun p : ℂ × (Fin 2 → ℂ) => P p.1) (volume.prod volume)` using `((measurable_ph _).comp measurable_fst).aestronglyMeasurable`.

Establish `h2 : AEStronglyMeasurable (fun p : ℂ × (Fin 2 → ℂ) => Gy Ψ h M p.2 p.1) (volume.prod volume)` using `((Gy_sm Ψ h M).comp_measurable measurable_swap).aestronglyMeasurable`. Establish `h3 : AEStronglyMeasurable (fun p : ℂ × (Fin 2 → ℂ) => psiC (-(β * p.2 1))) (volume.prod volume)` using `(continuous_psiC.comp (by fun_prop)).aestronglyMeasurable`. Conclude with `(h1.mul h2).mul h3`. Establish `hae : ∀ᵐ p : ℂ × (Fin 2 → ℂ) ∂(volume.prod volume), p.1 ≠ 0` using `Measure.quasiMeasurePreserving_fst.ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))) filter_upwards [hae] with p hp`. Simplify using `only [Function.uncurry, norm_mul, norm_psiC, mul_one]`.

Rewrite using `[norm_ph_tri_of_ne _ hp, one_mul]`. Use `(hb p.2 p.1 hp).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hstep : ∫ t : ℂ, P t * ∫ y : ℂ, innQ Ψ 1 h β (Matrix.vecMul ![t, t * y] M) * psiC (-y) = ∫ t : ℂ, ∫ x : Fin 2 → ℂ, P t * Gy Ψ h M x t * psiC (-(β * x 1))`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht`. Rewrite using `[inner_swap Ψ hh hM ht β, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsw` using `integral_integral_swap hJ`.

Unfold `W2`. Rewrite using `[hstep, hsw, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Ax_eq]`. Rewrite using `[← hPd, integral_mul_const]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ax_fourier (k : ℕ) (Ψ : Sw) (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) (β : ℂ)
    (hh : (Matrix.of h).det ≠ 0) (hM : M.det ≠ 0) :
    W2 k (innQ Ψ 1 h β) M = ∫ x : Fin 2 → ℂ, Ax k Ψ h M x * psiC (-(β * x 1)) := by
  obtain ⟨C, hC0, hb⟩ := gy_bound Ψ hh hM
  have hxw : Integrable (fun x : Fin 2 → ℂ => (1 + ‖x‖) ^ (-(5 : ℝ))) := by
    refine integrable_one_add_norm ?_
    simp [Module.finrank_pi_fintype]
    norm_num
  set P := ph (4 * (k : ℤ) - 4) with hPd
  have hJ : Integrable (Function.uncurry fun (t : ℂ) (x : Fin 2 → ℂ) =>
      P t * Gy Ψ h M x t * psiC (-(β * x 1))) ((volume : Measure ℂ).prod (volume : Measure (Fin 2 → ℂ))) := by
    have hd := (dd_sq_int.mul_prod hxw).const_mul C
    refine hd.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : ℂ × (Fin 2 → ℂ) => P p.1) (volume.prod volume) :=
        ((measurable_ph _).comp measurable_fst).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℂ × (Fin 2 → ℂ) => Gy Ψ h M p.2 p.1) (volume.prod volume) :=
        ((Gy_sm Ψ h M).comp_measurable measurable_swap).aestronglyMeasurable
      have h3 : AEStronglyMeasurable (fun p : ℂ × (Fin 2 → ℂ) => psiC (-(β * p.2 1))) (volume.prod volume) :=
        (continuous_psiC.comp (by fun_prop)).aestronglyMeasurable
      exact (h1.mul h2).mul h3
    · have hae : ∀ᵐ p : ℂ × (Fin 2 → ℂ) ∂(volume.prod volume), p.1 ≠ 0 :=
        Measure.quasiMeasurePreserving_fst.ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)))
      filter_upwards [hae] with p hp
      simp only [Function.uncurry, norm_mul, norm_psiC, mul_one]
      rw [norm_ph_tri_of_ne _ hp, one_mul]
      refine (hb p.2 p.1 hp).trans (le_of_eq ?_)
      ring
  have hstep : ∫ t : ℂ, P t * ∫ y : ℂ, innQ Ψ 1 h β (Matrix.vecMul ![t, t * y] M) * psiC (-y) =
      ∫ t : ℂ, ∫ x : Fin 2 → ℂ, P t * Gy Ψ h M x t * psiC (-(β * x 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
    rw [inner_swap Ψ hh hM ht β, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hsw := integral_integral_swap hJ
  unfold W2
  rw [hstep, hsw, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Ax_eq]
  rw [← hPd, integral_mul_const]
  ring

/- English proof (translation)
Take `⟨C, N, hC, hb⟩` from `row_bound M hM`. Use `⟨‖ph (2 * (k : ℤ) - 2) M.det‖ * ‖M.det‖ * (C * ∫ t : ℂ, dd t ^ 2), N, ?_, fun f => ?_⟩` and prove the remaining obligations. Establish `: 0 ≤ ∫ t : ℂ, dd t ^ 2` using `integral_nonneg fun t => by positivity`. Check the signs of the components of the expression. Establish `hP` using `Unif.pS_nonneg N f`.

Establish `h1 : ‖∫ t : ℂ, ph (4 * (k : ℤ) - 4) t * ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] M) * psiC (-y)‖ ≤ ∫ t : ℂ, C * pS N f * dd t ^ 2`. Use `norm_integral_le_of_norm_le (dd_sq_int.const_mul _) ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h1` using `[integral_const_mul]`. Unfold `W2`. Rewrite using `[norm_mul, norm_mul, Complex.norm_real, norm_norm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem whittakerGL2_le_schwartz_seminorm (k : ℕ) {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det ≠ 0) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ f : SchwartzMap (Fin 2 → ℂ) ℂ, ‖W2 k f M‖ ≤ C * pS N f := by
  obtain ⟨C, N, hC, hb⟩ := row_bound M hM
  refine ⟨‖ph (2 * (k : ℤ) - 2) M.det‖ * ‖M.det‖ * (C * ∫ t : ℂ, dd t ^ 2), N, ?_, fun f => ?_⟩
  · have : 0 ≤ ∫ t : ℂ, dd t ^ 2 := integral_nonneg fun t => by positivity
    positivity
  · have hP := Unif.pS_nonneg N f
    have h1 : ‖∫ t : ℂ, ph (4 * (k : ℤ) - 4) t *
        ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] M) * psiC (-y)‖ ≤ ∫ t : ℂ, C * pS N f * dd t ^ 2 := by
      refine norm_integral_le_of_norm_le (dd_sq_int.const_mul _) ?_
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with t ht
      rw [norm_mul]
      calc _ ≤ 1 * (C * pS N f * dd t ^ 2) :=
            mul_le_mul (norm_ph_tri_le _ _) (hb f t ht) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    rw [integral_const_mul] at h1
    unfold W2
    rw [norm_mul, norm_mul, Complex.norm_real, norm_norm]
    calc _ ≤ ‖ph (2 * (k : ℤ) - 2) M.det‖ * ‖M.det‖ * (C * pS N f * ∫ t : ℂ, dd t ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring

/- English proof (translation)
Take `⟨C1, N, hC1, hW⟩` from `whittakerGL2_le_schwartz_seminorm k hM`. Take `⟨C2, hC2, hS⟩` from `slice_decay Ψ N 8`. Take `⟨c, hc, hX⟩` from `x_lower h hh`. Use `⟨C1 * C2 * c ^ 8, by positivity, fun a b => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `GlobalTheory.CompanionTheory.SchwartzSlice.slices_schwartz Ψ (Matrix.of.symm (Matrix.of h * blk ![a, b]))`.

Use `set v : Fin 2 → ℂ := ![a, b] with hv`. Use `set X : M23 := Matrix.of.symm (Matrix.of h * blk v) with hXd`. Establish `hA : Ax k Ψ h M v = W2 k f M` using `by rw [Ax, ← hXd, hf]`. Establish `h1` using `hS X f hf`. Establish `h2` using `hX v`.

Establish `ha : ‖a‖ ≤ ‖v‖` using `by simpa [hv] using norm_le_pi_norm v 0`. Establish `hb : ‖b‖ ≤ ‖v‖` using `by simpa [hv] using norm_le_pi_norm v 1`. Establish `hr : 0 ≤ ‖v‖` using `norm_nonneg _`. Establish `hA' : 1 + ‖a‖ ^ 2 ≤ (1 + ‖v‖) ^ 2` using `by nlinarith [norm_nonneg a]`. Establish `hB' : 1 + ‖b‖ ^ 2 ≤ (1 + ‖v‖) ^ 2` using `by nlinarith [norm_nonneg b]`.

Establish `hAB : (1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2 ≤ (c * (1 + ‖X‖)) ^ 8`. Combine the equalities or inequalities in the displayed calculation. Establish `hP` using `Unif.pS_nonneg N f`. Establish `hpos : 0 < (1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2` using `by positivity`. Establish `e : C1 * C2 * c ^ 8 * (dd a ^ 2 * dd b ^ 2) = C1 * C2 * c ^ 8 / ((1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2)`.

Simplify using `only [dd]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hA, e, le_div_iff₀ hpos]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ax_bound (k : ℕ) (Ψ : Sw) {h : M22} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : (Matrix.of h).det ≠ 0) (hM : M.det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, ‖Ax k Ψ h M ![a, b]‖ ≤ C * (dd a ^ 2 * dd b ^ 2) := by
  obtain ⟨C1, N, hC1, hW⟩ := whittakerGL2_le_schwartz_seminorm k hM
  obtain ⟨C2, hC2, hS⟩ := slice_decay Ψ N 8
  obtain ⟨c, hc, hX⟩ := x_lower h hh
  refine ⟨C1 * C2 * c ^ 8, by positivity, fun a b => ?_⟩
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.SchwartzSlice.slices_schwartz Ψ (Matrix.of.symm (Matrix.of h * blk ![a, b]))
  set v : Fin 2 → ℂ := ![a, b] with hv
  set X : M23 := Matrix.of.symm (Matrix.of h * blk v) with hXd
  have hA : Ax k Ψ h M v = W2 k f M := by rw [Ax, ← hXd, hf]
  have h1 := hS X f hf
  have h2 := hX v
  have ha : ‖a‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 0
  have hb : ‖b‖ ≤ ‖v‖ := by simpa [hv] using norm_le_pi_norm v 1
  have hr : 0 ≤ ‖v‖ := norm_nonneg _
  have hA' : 1 + ‖a‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg a]
  have hB' : 1 + ‖b‖ ^ 2 ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg b]
  have hAB : (1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2 ≤ (c * (1 + ‖X‖)) ^ 8 := by
    calc (1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2
        ≤ ((1 + ‖v‖) ^ 2) ^ 2 * ((1 + ‖v‖) ^ 2) ^ 2 := by gcongr
      _ = (1 + ‖v‖) ^ 8 := by ring
      _ ≤ _ := by gcongr
  have hP := Unif.pS_nonneg N f
  have hpos : 0 < (1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2 := by positivity
  have e : C1 * C2 * c ^ 8 * (dd a ^ 2 * dd b ^ 2) =
      C1 * C2 * c ^ 8 / ((1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2) := by
    simp only [dd]
    field_simp
  rw [hA, e, le_div_iff₀ hpos]
  calc ‖W2 k f M‖ * ((1 + ‖a‖ ^ 2) ^ 2 * (1 + ‖b‖ ^ 2) ^ 2)
      ≤ (C1 * pS N f) * (c * (1 + ‖X‖)) ^ 8 :=
        mul_le_mul (hW f) hAB hpos.le (by positivity)
    _ = C1 * c ^ 8 * ((1 + ‖X‖) ^ 8 * pS N f) := by ring
    _ ≤ C1 * c ^ 8 * C2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/- English proof (translation)
Establish `hmp` using `(volume_preserving_finTwoArrow ℂ).symm`. Rewrite using `[← hmp.integral_comp']`. Conclude with `integral_prod_symm (f := fun p : ℂ × ℂ => F ![p.1, p.2]) hF`.
-/
theorem fin_two_integral (F : (Fin 2 → ℂ) → ℂ) (hF : Integrable (fun p : ℂ × ℂ => F ![p.1, p.2])) :
    ∫ x, F x = ∫ w : ℂ, ∫ x0 : ℂ, F ![x0, w] := by
  have hmp := (volume_preserving_finTwoArrow ℂ).symm
  rw [← hmp.integral_comp']
  exact integral_prod_symm (f := fun p : ℂ × ℂ => F ![p.1, p.2]) hF

section marg
variable {A : (Fin 2 → ℂ) → ℂ} {C : ℝ} {W : ℂ → ℂ}

/- English proof (translation)
Establish `hd` using `(dd_sq_int.mul_prod hW).const_mul C`. Use `hd.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Establish `h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => W p.2) (volume.prod volume)` using `hWm.comp_snd`. Establish `h2 : StronglyMeasurable (fun p : ℂ × ℂ => A ![p.1, p.2])` using `hA.comp_measurable continuous_vec.measurable`. Conclude with `h1.mul h2.aestronglyMeasurable`.

Rewrite using `[norm_mul]`. Establish `e` using `hb p.1 p.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem joint_int (hA : StronglyMeasurable A) (hb : ∀ a b : ℂ, ‖A ![a, b]‖ ≤ C * (dd a ^ 2 * dd b ^ 2))
    (hWm : AEStronglyMeasurable W volume) (hW : Integrable fun w => ‖W w‖ * dd w ^ 2) :
    Integrable (fun p : ℂ × ℂ => W p.2 * A ![p.1, p.2]) := by
  have hd := (dd_sq_int.mul_prod hW).const_mul C
  refine hd.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => W p.2) (volume.prod volume) :=
      hWm.comp_snd
    have h2 : StronglyMeasurable (fun p : ℂ × ℂ => A ![p.1, p.2]) :=
      hA.comp_measurable continuous_vec.measurable
    exact h1.mul h2.aestronglyMeasurable
  · rw [norm_mul]
    have e := hb p.1 p.2
    calc ‖W p.2‖ * ‖A ![p.1, p.2]‖ ≤ ‖W p.2‖ * (C * (dd p.1 ^ 2 * dd p.2 ^ 2)) := by gcongr
      _ = _ := by ring

/- English proof (translation)
Rewrite using `[fin_two_integral (fun x => W (x 1) * A x) (by simpa using hJ)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_one, Matrix.cons_val_zero]`. Rewrite using `[← integral_const_mul]`.
-/
theorem integral_fubini_last_coordinate (hJ : Integrable (fun p : ℂ × ℂ => W p.2 * A ![p.1, p.2])) :
    ∫ x, W (x 1) * A x = ∫ w, W w * ∫ x0 : ℂ, A ![x0, w] := by
  rw [fin_two_integral (fun x => W (x 1) * A x) (by simpa using hJ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [← integral_const_mul]

end marg

/- English proof (translation)
Use `norm_pos_iff.2 fun he => ?_` and prove the remaining obligations. Establish `h1 : ((Matrix.of h)⁻¹).det = 0` using `Matrix.det_eq_zero_of_row_eq_zero 1 fun j => congrFun he j`. Rewrite `h1` using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `inv_ne_zero hh h1`.
-/
theorem eta_pos {h : M22} (hh : (Matrix.of h).det ≠ 0) : 0 < ‖eta h‖ := by
  refine norm_pos_iff.2 fun he => ?_
  have h1 : ((Matrix.of h)⁻¹).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero 1 fun j => congrFun he j
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h1
  exact inv_ne_zero hh h1

/- English proof (translation)
Unfold `dd`. Conclude with `inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖z‖])`.
-/
theorem dd_le_one (z : ℂ) : dd z ≤ 1 := by
  unfold dd
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖z‖])

/- English proof (translation)
Use `(wt_vol σ h0 h1).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `continuous_dd` as an intermediate fact. Conclude with `(((measurable_norm.pow_const _).mul (by fun_prop)).aestronglyMeasurable)`. Establish `hd` using `dd_pos z`. Establish `hn : 0 ≤ ‖z‖ ^ (2 * σ - 2)` using `Real.rpow_nonneg (norm_nonneg _) _`.

Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Use `mul_le_mul_of_nonneg_left ?_ hn` and prove the remaining obligations. Use polynomial arithmetic with `[dd_le_one z]`.
-/
theorem wt_sq {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    Integrable fun z : ℂ => ‖z‖ ^ (2 * σ - 2) * dd z ^ 2 := by
  refine (wt_vol σ h0 h1).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have := continuous_dd
    exact (((measurable_norm.pow_const _).mul (by fun_prop)).aestronglyMeasurable)
  · have hd := dd_pos z
    have hn : 0 ≤ ‖z‖ ^ (2 * σ - 2) := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ hn
    nlinarith [dd_le_one z]

def Wn (n : ℤ) (s : ℂ) (w : ℂ) : ℂ := ph n w * ((‖w‖ ^ 2 : ℝ) : ℂ) ^ (s - 1)

/- English proof (translation)
Unfold `Wn`. Use `(measurable_ph n).mul (Measurable.pow_const ?_ _)` and prove the remaining obligations. Use `fun_prop`.
-/
theorem Wn_meas (n : ℤ) (s : ℂ) : Measurable (Wn n s) := by
  unfold Wn
  refine (measurable_ph n).mul (Measurable.pow_const ?_ _)
  fun_prop

/- English proof (translation)
Distinguish the cases in `hw : w = 0`. Establish `hs : s - 1 ≠ 0` using `fun e => by`. Establish `: (s - 1).re = 0` using `by rw [e]; simp`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Substitute `hw` using the available equality. Simplify using `only [Wn, norm_zero]`. Evaluate the numerical expressions using `[Complex.zero_cpow hs]`. Check the signs of the components of the expression. Establish `hp : 0 < ‖w‖` using `norm_pos_iff.2 hw`.

Unfold `Wn`. Rewrite using `[norm_mul, norm_ph_tri_of_ne _ hw, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]`. Establish `e : (s - 1).re = s.re - 1` using `by simp`. Rewrite using `[e, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]`. Apply `le_of_eq` to reduce the goal to its premises.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wn_norm (n : ℤ) {s : ℂ} (h1 : s.re < 1) (w : ℂ) : ‖Wn n s w‖ ≤ ‖w‖ ^ (2 * s.re - 2) := by
  by_cases hw : w = 0
  · have hs : s - 1 ≠ 0 := fun e => by
      have : (s - 1).re = 0 := by rw [e]; simp
      simp at this
      linarith
    subst hw
    simp only [Wn, norm_zero]
    norm_num [Complex.zero_cpow hs]
    positivity
  · have hp : 0 < ‖w‖ := norm_pos_iff.2 hw
    unfold Wn
    rw [norm_mul, norm_ph_tri_of_ne _ hw, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have e : (s - 1).re = s.re - 1 := by simp
    rw [e, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    apply le_of_eq
    congr 1
    push_cast
    ring

/- English proof (translation)
Take `⟨C, hC0, hb⟩` from `ax_bound k Ψ hh hM`. Establish `hA` using `ax_sm k Ψ h M`. Use `set A := Ax k Ψ h M with hAdef`. Use `set R := Rw k Ψ h M with hRdef`. Establish `hR : ∀ w, R w = ∫ x0 : ℂ, A ![x0, w]` using `fun w => rfl`.

Establish `hJ : ∀ {W : ℂ → ℂ}, AEStronglyMeasurable W volume → Integrable (fun w => ‖W w‖ * dd w ^ 2) → Integrable (fun p : ℂ × ℂ => W p.2 * A ![p.1, p.2])` using `fun hm hw => joint_int hA hb hm hw`. Establish `hmarg : ∀ {W : ℂ → ℂ}, AEStronglyMeasurable W volume → Integrable (fun w => ‖W w‖ * dd w ^ 2) → Integrable (fun w => W w * R w)`. Introduce `W hm hw`. Use `(hJ hm hw).integral_prod_right.congr (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [hR]`.

Rewrite using `[integral_const_mul]`. Establish `hfub : ∀ {W : ℂ → ℂ}, AEStronglyMeasurable W volume → Integrable (fun w => ‖W w‖ * dd w ^ 2) → ∫ x, W (x 1) * A x = ∫ w, W w * R w` using `fun hm hw => integral_fubini_last_coordinate (hJ hm hw)`. Establish `hRi : Integrable R`. Use `hmarg (W := fun _ => 1) aestronglyMeasurable_const (by simpa using dd_sq_int)` as an intermediate fact. Simplify using `using this`.

Establish `hRw : Integrable (fun w => R w * ((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ))`. Establish `hm : AEStronglyMeasurable (fun w : ℂ => ((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ)) volume` using `(Complex.measurable_ofReal.comp (measurable_norm.pow_const _)).aestronglyMeasurable`. Establish `hw : Integrable (fun w : ℂ => ‖((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ)‖ * dd w ^ 2)`. Use `(wt_sq h0 h1).congr (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Complex.norm_real, norm_norm]`.

Rewrite using `[Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Simplify `hmarg hm hw` using `[mul_comm]`. Establish `hF : ∀ r, fC R r = 2 * W2 k (innQ Ψ 1 h (-r)) M`.

Introduce `r`. Establish `hm : AEStronglyMeasurable (fun w : ℂ => psiC (w * r)) volume` using `(continuous_psiC.comp (by fun_prop)).aestronglyMeasurable`. Establish `hw : Integrable (fun w : ℂ => ‖psiC (w * r)‖ * dd w ^ 2)`. Simplify `dd_sq_int` using `[norm_psiC]`. Establish `e` using `hfub hm hw`.

Rewrite using `[ax_fourier k Ψ h M (-r) hh hM]`. Establish `e2 : ∫ x : Fin 2 → ℂ, Ax k Ψ h M x * psiC (-(-r * x 1)) = ∫ x, psiC (x 1 * r) * A x`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [hAdef]`. Rewrite using `[mul_comm]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, e, fC, volC, integral_smul_measure]`. Simplify using `only [mul_comm (psiC _)]`. Simplify using the standard rewrite rules.

Choose the witnesses or unpack the hypotheses as in `⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ r, ‖fC R r‖ ≤ D * dd r := by`. Take `⟨C1, N, hC1, hW⟩` from `whittakerGL2_le_schwartz_seminorm k hM`. Take `⟨C2, N', hI'⟩` from `hI (max N 2)`. Use `set L := max N 2 with hLd`. Establish `he` using `eta_pos hh`.

Use `set e := ‖eta h‖ with hed`. Use `set K := |C2 * pS N' Ψ * (‖(Matrix.of h).det‖ ^ 2)⁻¹| with hK`. Establish `hK0 : 0 ≤ K` using `abs_nonneg _`. Use `⟨2 * C1 * K * max 1 (e ^ 2)⁻¹, by positivity, fun r => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hp⟩` from `hI' Ψ h (-r) hh`.

Establish `h2 : ‖fC R r‖ = 2 * ‖W2 k f M‖`. Rewrite using `[hF, ← hf, norm_mul]`. Simplify using the standard rewrite rules. Establish `h3 : pS N f ≤ pS L f` using `Unif.pS_mono (le_max_left _ _) f`. Establish `h4 : pS L f ≤ K * ((1 + ‖r‖ * e) ^ L)⁻¹`.

Use `hp.trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg, div_eq_mul_inv]`. Establish `hh1 : (1 : ℝ) ≤ (1 + ‖h‖) ^ L` using `one_le_pow₀ (by linarith [norm_nonneg h])`. Establish `hr1 : 0 < (1 + ‖r‖ * e) ^ L` using `by positivity`. Rewrite using `[mul_inv]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul (le_abs_self _) le_rfl (by positivity) hK0`. Use `_ ≤ K * (1 * ((1 + ‖r‖ * e) ^ L)⁻¹) := by gcongr`. Conclude with `inv_le_one_of_one_le₀ hh1`. Use `_ = _ := by rw [one_mul]`.

Establish `h5` using `decay_alg (norm_nonneg r) he (show 2 ≤ L from le_max_right _ _)`. Establish `hP` using `Unif.pS_nonneg N f`. Rewrite using `[h2]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(hW f).trans (mul_le_mul_of_nonneg_left (h3.trans (h4.trans (mul_le_mul_of_nonneg_left h5 hK0))) hC1)`.

Use `_ = _ := by simp only [dd]; ring`. Establish `hFw : Integrable (fun r => fC R r * ((‖r‖ ^ (-2 * s.re) : ℝ) : ℂ))`. Establish `hc : Continuous (fC R)` using `GlobalTheory.CompanionTheory.TateC.continuous_fC hRi`. Establish `hv` using `(wt_vol (1 - s.re) (by linarith) (by linarith)).const_mul D`. Use `hv.mono' (hc.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp (measurable_norm.pow_const _)).aestronglyMeasurable) (Filter.Eventually.of_forall fun r => ?_)` and prove the remaining obligations.

Establish `hn : 0 ≤ ‖r‖ ^ (-2 * s.re)` using `Real.rpow_nonneg (norm_nonneg _) _`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]`. Establish `e : 2 * (1 - s.re) - 2 = -2 * s.re` using `by ring`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hTate` using `hT R n s h0 h1 hRi hRw hFw`. Establish `hLS` using `left_side (fC R) n s`. Establish `hL : ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) M ∂mulC = (1 / 2 : ℂ) * ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * fC R (-(t : ℂ)⁻¹) ∂mulC`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `only [hF, neg_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX : ∫ x : Fin 2 → ℂ, ph n (x 1) * ((‖x 1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * A x = z1 R n s`. Establish `hw : Integrable (fun w => ‖Wn n s w‖ * dd w ^ 2)`. Use `(wt_sq h0 h1).mono' ((Wn_meas n s).norm.mul (by have := continuous_dd; fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations.

Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Conclude with `mul_le_mul_of_nonneg_right (Wn_norm n h1 w) (by positivity)`. Establish `e` using `hfub (Wn_meas n s).aestronglyMeasurable hw`. Rewrite using `[tate_integral_eq_plane_integral]`. Conclude with `e`.

Rewrite using `[hL, hLS, hTate, hX]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core (hT : TateFunctionalEquationComplex) (hI : IbpQ) (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (h : M22) (M : Matrix (Fin 2) (Fin 2) ℂ) (hh : (Matrix.of h).det ≠ 0) (hM : M.det ≠ 0) :
    ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) M ∂mulC =
      (1 / 2 : ℂ) * (-1) ^ n * gC n s * ∫ x : Fin 2 → ℂ, ph n (x 1) * ((‖x 1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        Ax k Ψ h M x := by
  obtain ⟨C, hC0, hb⟩ := ax_bound k Ψ hh hM
  have hA := ax_sm k Ψ h M
  set A := Ax k Ψ h M with hAdef
  set R := Rw k Ψ h M with hRdef
  have hR : ∀ w, R w = ∫ x0 : ℂ, A ![x0, w] := fun w => rfl
  have hJ : ∀ {W : ℂ → ℂ}, AEStronglyMeasurable W volume → Integrable (fun w => ‖W w‖ * dd w ^ 2) →
      Integrable (fun p : ℂ × ℂ => W p.2 * A ![p.1, p.2]) := fun hm hw => joint_int hA hb hm hw
  have hmarg : ∀ {W : ℂ → ℂ}, AEStronglyMeasurable W volume → Integrable (fun w => ‖W w‖ * dd w ^ 2) →
      Integrable (fun w => W w * R w) := by
    intro W hm hw
    refine (hJ hm hw).integral_prod_right.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [hR]
    rw [integral_const_mul]
  have hfub : ∀ {W : ℂ → ℂ}, AEStronglyMeasurable W volume → Integrable (fun w => ‖W w‖ * dd w ^ 2) →
      ∫ x, W (x 1) * A x = ∫ w, W w * R w := fun hm hw => integral_fubini_last_coordinate (hJ hm hw)
  have hRi : Integrable R := by
    have := hmarg (W := fun _ => 1) aestronglyMeasurable_const (by simpa using dd_sq_int)
    simpa using this
  have hRw : Integrable (fun w => R w * ((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ)) := by
    have hm : AEStronglyMeasurable (fun w : ℂ => ((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ)) volume :=
      (Complex.measurable_ofReal.comp (measurable_norm.pow_const _)).aestronglyMeasurable
    have hw : Integrable (fun w : ℂ => ‖((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ)‖ * dd w ^ 2) := by
      refine (wt_sq h0 h1).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Complex.norm_real, norm_norm]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      congr 2
      ring
    simpa [mul_comm] using hmarg hm hw
  have hF : ∀ r, fC R r = 2 * W2 k (innQ Ψ 1 h (-r)) M := by
    intro r
    have hm : AEStronglyMeasurable (fun w : ℂ => psiC (w * r)) volume :=
      (continuous_psiC.comp (by fun_prop)).aestronglyMeasurable
    have hw : Integrable (fun w : ℂ => ‖psiC (w * r)‖ * dd w ^ 2) := by
      simpa [norm_psiC] using dd_sq_int
    have e := hfub hm hw
    rw [ax_fourier k Ψ h M (-r) hh hM]
    have e2 : ∫ x : Fin 2 → ℂ, Ax k Ψ h M x * psiC (-(-r * x 1)) = ∫ x, psiC (x 1 * r) * A x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hAdef]
      rw [mul_comm]
      congr 2
      ring
    rw [e2, e, fC, volC, integral_smul_measure]
    simp only [mul_comm (psiC _)]
    simp

  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ r, ‖fC R r‖ ≤ D * dd r := by
    obtain ⟨C1, N, hC1, hW⟩ := whittakerGL2_le_schwartz_seminorm k hM
    obtain ⟨C2, N', hI'⟩ := hI (max N 2)
    set L := max N 2 with hLd
    have he := eta_pos hh
    set e := ‖eta h‖ with hed
    set K := |C2 * pS N' Ψ * (‖(Matrix.of h).det‖ ^ 2)⁻¹| with hK
    have hK0 : 0 ≤ K := abs_nonneg _
    refine ⟨2 * C1 * K * max 1 (e ^ 2)⁻¹, by positivity, fun r => ?_⟩
    obtain ⟨f, hf, hp⟩ := hI' Ψ h (-r) hh
    have h2 : ‖fC R r‖ = 2 * ‖W2 k f M‖ := by
      rw [hF, ← hf, norm_mul]
      simp
    have h3 : pS N f ≤ pS L f := Unif.pS_mono (le_max_left _ _) f
    have h4 : pS L f ≤ K * ((1 + ‖r‖ * e) ^ L)⁻¹ := by
      refine hp.trans ?_
      rw [norm_neg, div_eq_mul_inv]
      have hh1 : (1 : ℝ) ≤ (1 + ‖h‖) ^ L := one_le_pow₀ (by linarith [norm_nonneg h])
      have hr1 : 0 < (1 + ‖r‖ * e) ^ L := by positivity
      rw [mul_inv]
      calc _ ≤ K * (((1 + ‖h‖) ^ L)⁻¹ * ((1 + ‖r‖ * e) ^ L)⁻¹) := by
            exact mul_le_mul (le_abs_self _) le_rfl (by positivity) hK0
        _ ≤ K * (1 * ((1 + ‖r‖ * e) ^ L)⁻¹) := by
            gcongr
            exact inv_le_one_of_one_le₀ hh1
        _ = _ := by rw [one_mul]
    have h5 := decay_alg (norm_nonneg r) he (show 2 ≤ L from le_max_right _ _)
    have hP := Unif.pS_nonneg N f
    rw [h2]
    calc 2 * ‖W2 k f M‖ ≤ 2 * (C1 * (K * (max 1 (e ^ 2)⁻¹ * (1 + ‖r‖ ^ 2)⁻¹))) := by
          gcongr
          exact (hW f).trans (mul_le_mul_of_nonneg_left (h3.trans (h4.trans (mul_le_mul_of_nonneg_left h5 hK0))) hC1)
      _ = _ := by simp only [dd]; ring
  have hFw : Integrable (fun r => fC R r * ((‖r‖ ^ (-2 * s.re) : ℝ) : ℂ)) := by
    have hc : Continuous (fC R) := GlobalTheory.CompanionTheory.TateC.continuous_fC hRi
    have hv := (wt_vol (1 - s.re) (by linarith) (by linarith)).const_mul D
    refine hv.mono' (hc.aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (measurable_norm.pow_const _)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r => ?_)
    have hn : 0 ≤ ‖r‖ ^ (-2 * s.re) := Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
    have e : 2 * (1 - s.re) - 2 = -2 * s.re := by ring
    rw [e]
    calc _ ≤ D * dd r * ‖r‖ ^ (-2 * s.re) := mul_le_mul_of_nonneg_right (hD r) hn
      _ = _ := by ring
  have hTate := hT R n s h0 h1 hRi hRw hFw
  have hLS := left_side (fC R) n s
  have hL : ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) M ∂mulC =
      (1 / 2 : ℂ) * ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * fC R (-(t : ℂ)⁻¹) ∂mulC := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, neg_neg]
    ring
  have hX : ∫ x : Fin 2 → ℂ, ph n (x 1) * ((‖x 1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * A x = z1 R n s := by
    have hw : Integrable (fun w => ‖Wn n s w‖ * dd w ^ 2) := by
      refine (wt_sq h0 h1).mono' ((Wn_meas n s).norm.mul (by have := continuous_dd; fun_prop)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (Wn_norm n h1 w) (by positivity)
    have e := hfub (Wn_meas n s).aestronglyMeasurable hw
    rw [tate_integral_eq_plane_integral]
    exact e
  rw [hL, hLS, hTate, hX]
  ring

/- English proof (translation)
Introduce `hT hI k _ Ψ n s h0 h1 g h M hh hM`. Take `⟨Ψ', hΨ⟩` from `right_translate Ψ g`. Establish `e0 : ∀ (x : Fin 2 → ℂ) (q : Fin 2 → ℂ), Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ)), q) = Ψ' (Matrix.of.symm (Matrix.of h * blk x), q)`. Introduce `x q`. Rewrite using `[hΨ]`.

Both sides reduce to the same expression. Establish `e1 : ∀ β, innQ Ψ g h β = innQ Ψ' 1 h β`. Introduce `β`. Use function extensionality and compare the values at `q`. Unfold `innQ`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[e0]`. Establish `e2 : ∀ x : Fin 2 → ℂ, sl Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ))) = sl Ψ' (Matrix.of.symm (Matrix.of h * blk x))`. Introduce `x`. Use function extensionality and compare the values at `q`.

Conclude with `e0 x q`. Simplify using `only [e1, e2]`. Conclude with `core hT hI k Ψ' n s h0 h1 h M hh hM`.
-/
theorem main : TateFunctionalEquationComplex → IbpQ → UnipotentTateFunctionalEquation := by
  intro hT hI k _ Ψ n s h0 h1 g h M hh hM
  obtain ⟨Ψ', hΨ⟩ := right_translate Ψ g
  have e0 : ∀ (x : Fin 2 → ℂ) (q : Fin 2 → ℂ),
      Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ)), q) =
        Ψ' (Matrix.of.symm (Matrix.of h * blk x), q) := by
    intro x q
    rw [hΨ]
    rfl
  have e1 : ∀ β, innQ Ψ g h β = innQ Ψ' 1 h β := by
    intro β
    funext q
    unfold innQ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [e0]
  have e2 : ∀ x : Fin 2 → ℂ, sl Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ))) =
      sl Ψ' (Matrix.of.symm (Matrix.of h * blk x)) := by
    intro x
    funext q
    exact e0 x q
  simp only [e1, e2]
  exact core hT hI k Ψ' n s h0 h1 h M hh hM

end GlobalTheory.CompanionTheory.PerUThreeC
