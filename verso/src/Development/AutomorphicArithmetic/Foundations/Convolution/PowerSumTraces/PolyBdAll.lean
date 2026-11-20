import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelH
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Use `set a := diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i) with ha`. Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Establish `hw : locHeight (infAt w a) ≤ AutomorphicForm.height a`. Establish `h1 : locHeight (infAt w a) ≤ locHeight (infAt w a) ^ w.mult` using `le_self_pow₀ (one_le_locHeight _) InfinitePlace.mult_ne_zero`. Establish `h2 : locHeight (infAt w a) ^ w.mult ≤ ∏ v : InfinitePlace K, locHeight (infAt v a) ^ v.mult`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]`. Use `le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) ?_` and prove the remaining obligations. Conclude with `Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _)`. Use `(h1.trans h2).trans ?_` and prove the remaining obligations. Unfold `AutomorphicForm.height`.

Conclude with `le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight a)) (one_le_finprod_locHeight a)`. Prove the components needed by the constructor for the conclusion. Use `le_trans ?_ hw` and prove the remaining obligations. Establish `e1` using `norm_apply_le_locHeight (infAt w a) i i`. Rewrite `e1` using `[infAt_diagUnits_posIdele, coe_diagUnits, Matrix.diagonal_apply_eq, norm_posRealToUnits w (hρ i)]`.

Rewrite using `[infAt_diagUnits_posIdele]` and apply the resulting hypothesis. Use `le_trans ?_ hw` and prove the remaining obligations. Establish `e2` using `norm_inv_apply_le_locHeight (infAt w a) i i`. Rewrite `e2` using `[infAt_diagUnits_posIdele, ← map_inv, coe_diagUnits, Matrix.diagonal_apply_eq, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, norm_posRealToUnits w (hρ i)]`. Rewrite using `[infAt_diagUnits_posIdele]` and apply the resulting hypothesis.
-/
private theorem rho_le_height {K : Type} [Field K] [NumberField K] {n : ℕ} {ρ : Fin n → ℝ}
    (hρ : ∀ i, 0 < ρ i) (i : Fin n) :
    ρ i ≤ AutomorphicForm.height (diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i)) ∧
      (ρ i)⁻¹ ≤ AutomorphicForm.height (diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i)) := by
  classical
  set a := diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i) with ha
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hw : locHeight (infAt w a) ≤ AutomorphicForm.height a := by
    have h1 : locHeight (infAt w a) ≤ locHeight (infAt w a) ^ w.mult :=
      le_self_pow₀ (one_le_locHeight _) InfinitePlace.mult_ne_zero
    have h2 : locHeight (infAt w a) ^ w.mult ≤ ∏ v : InfinitePlace K, locHeight (infAt v a) ^ v.mult := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      refine le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) ?_
      exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
        (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl
        fun _ _ => one_le_pow₀ (one_le_locHeight _)
    refine (h1.trans h2).trans ?_
    unfold AutomorphicForm.height
    exact le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight a)) (one_le_finprod_locHeight a)
  constructor
  · refine le_trans ?_ hw
    have e1 := norm_apply_le_locHeight (infAt w a) i i
    rw [infAt_diagUnits_posIdele, coe_diagUnits, Matrix.diagonal_apply_eq, norm_posRealToUnits w (hρ i)] at e1
    rwa [infAt_diagUnits_posIdele]
  · refine le_trans ?_ hw
    have e2 := norm_inv_apply_le_locHeight (infAt w a) i i
    rw [infAt_diagUnits_posIdele, ← map_inv, coe_diagUnits, Matrix.diagonal_apply_eq, Pi.inv_apply,
      Units.val_inv_eq_inv_val, norm_inv, norm_posRealToUnits w (hρ i)] at e2
    rwa [infAt_diagUnits_posIdele]

/- English proof (translation)
Introduce `K _ _ n μ _ a`. Take `⟨ω, hω, hωB, t, ht, hsieg⟩` from `exists_siegelSet (K := K) n`. Take `⟨C₀, N₀, hC₀⟩` from `exists_norm_rconv_le_siegel_basic μ a hω ht`. Take `⟨C₁, N₁, hC₁⟩` from `UpperTheory.V.Fb.siegelHeight K n ω hω hωB t ht`. Take `⟨M, hM⟩` from `exists_height_le_of_isCompact hω`.

Take `⟨c, hcdef⟩ : ∃ c, c = heightConst K n` from `⟨_, rfl⟩`. Establish `hc : 1 ≤ c` using `hcdef ▸ one_le_heightConst`. Take `⟨M', hM'def⟩ : ∃ M', M' = max M 1` from `⟨_, rfl⟩`. Establish `hM'1 : 1 ≤ M'` using `hM'def ▸ le_max_right _ _`. Take `⟨E, hEdef⟩ : ∃ E, E = max C₁ 1 * 2 ^ N₁` from `⟨_, rfl⟩`.

Take `⟨D, hDdef⟩ : ∃ D, D = c * (c * M')` from `⟨_, rfl⟩`. Establish `hD1 : 1 ≤ D`. Rewrite using `[hDdef]`. Conclude with `one_le_mul_of_one_le_of_one_le hc (one_le_mul_of_one_le_of_one_le hc hM'1)`. Use `⟨max C₀ 0 * (D * E) ^ N₀, N₁ * N₀, fun φ x => ?_⟩` and prove the remaining obligations.

Establish `hq1 : 1 ≤ qht x` using `le_ciInf fun γ => one_le_height _`. Take `⟨γ, hγ⟩` from `hsieg (x : AdelicGLn.AdelicGL K n)`. Establish `hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n` using `rationalGL_le_normOneGL ⟨γ, rfl⟩`. Take `⟨γ₁, hγ₁⟩ : ∃ γ₁ : normOneGL K n, γ₁ = ⟨AdelicGLn.diagonal K n γ, hγ1⟩` from `⟨_, rfl⟩`. Establish `hγΓ : γ₁ ∈ Gam K n` using `⟨γ, by rw [hγ₁]; rfl⟩`.

Establish `hhq : AutomorphicForm.height (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) ≤ E * qht x ^ N₁`. Take `⟨γ', hγ'⟩ : ∃ γ' : Gam K n, AutomorphicForm.height (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) < 2 * qht x` from `exists_lt_of_ciInf_lt (show qht x < 2 * qht x by linarith)`. Take `⟨δ, hδ⟩` from `γ'.2`. Establish `hδ' : AdelicGLn.diagonal K n δ = (((γ' : G1 K n)) : AdelicGLn.AdelicGL K n)` using `hδ`. Establish `e : AdelicGLn.diagonal K n (γ * δ⁻¹) * (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)`.

Rewrite using `[Subgroup.coe_mul, ← hδ', map_mul, map_inv]`. Use `group`. Establish `h1` using `hC₁ (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) (γ * δ⁻¹) (e ▸ hγ)`. Rewrite `h1` using `[e]`. Use `h1.trans ?_` and prove the remaining obligations.

Establish `hy` using `height_pos (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← rconv_mul_left (Gam K n) μ a φ hγΓ x]`. Take `⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hx⟩` from `hγ`. Establish `hx' : ((γ₁ * x : normOneGL K n) : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K` using `K) (ρ i) (hρ i)) * kk := by`.

Rewrite using `[hγ₁]`. Conclude with `hx`. Take `⟨h, hhdef⟩ : ∃ h, h = AutomorphicForm.height (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))` from `⟨_, rfl⟩`. Rewrite `hhq` using `[← hhdef]`. Establish `hh1 : 1 ≤ h` using `hhdef ▸ one_le_height _`.

Establish `hdiag : AutomorphicForm.height (diagUnits n fun i => posIdele (K` using `K) (ρ i) (hρ i)) ≤ D * h := by`. Establish `e : diagUnits n (fun i => posIdele (K` using `K) (ρ i) (hρ i)) = b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) * kk⁻¹ := by`. Rewrite using `[hx]`. Use `group`. Rewrite using `[e]`.

Establish `hbM : AutomorphicForm.height b⁻¹ ≤ M'`. Rewrite using `[height_inv, hM'def]`. Conclude with `(hM b hb).trans (le_max_left _ _)`. Establish `hk : AutomorphicForm.height kk⁻¹ = 1` using `height_eq_one_of_mem_maxCompact (inv_mem hkk)`. Establish `h1` using `height_mul_le (b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))) kk⁻¹`.

Establish `h2` using `height_mul_le b⁻¹ (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))`. Rewrite `h1` using `[hk, mul_one, ← hcdef]`. Rewrite `h2` using `[← hcdef, ← hhdef]`. Establish `hc0 : 0 ≤ c` using `zero_le_one.trans hc`. Establish `h3 : c * AutomorphicForm.height b⁻¹ * h ≤ c * M' * h` using `by gcongr`.

Combine the equalities or inequalities in the displayed calculation. Establish `hDh1 : 1 ≤ D * h` using `one_le_mul_of_one_le_of_one_le hD1 hh1`. Establish `hR1 : 1 ≤ (D * h) ^ 2` using `one_le_pow₀ hDh1`. Establish `hratio : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ (D * h) ^ 2`. Introduce `i j _`.

Establish `h1` using `((rho_le_height (K := K) hρ i).1).trans hdiag`. Establish `h2` using `((rho_le_height (K := K) hρ j).2).trans hdiag`. Rewrite using `[div_eq_mul_inv, sq]`. Conclude with `mul_le_mul h1 h2 (inv_pos.2 (hρ j)).le (zero_le_one.trans hDh1)`. Establish `hmain` using `hC₀ φ b hb ρ hρ hs kk hkk (γ₁ * x) hx' _ hR1 hratio`.

Establish `hsq : √(((D * h) ^ 2) ^ N₀) = (D * h) ^ N₀`. Rewrite using `[pow_right_comm, Real.sqrt_sq (pow_nonneg (zero_le_one.trans hDh1) _)]`. Rewrite `hmain` using `[hsq]`. Establish `hfin : (D * h) ^ N₀ ≤ (D * E) ^ N₀ * qht x ^ (N₁ * N₀)`. Rewrite using `[pow_mul, ← mul_pow, mul_assoc]`.

Conclude with `pow_le_pow_left₀ (zero_le_one.trans hDh1) (mul_le_mul_of_nonneg_left hhq (zero_le_one.trans hD1)) _`. Establish `hnn : 0 ≤ (D * h) ^ N₀` using `pow_nonneg (zero_le_one.trans hDh1) _`. Combine the equalities or inequalities in the displayed calculation. Establish `: (0 : ℝ) ≤ max C₀ 0` using `le_max_right _ _`. Use `gcongr`.

Use `_ = max C₀ 0 * (D * E) ^ N₀ * qht x ^ (N₁ * N₀) * ‖φ‖ := by ring`.
-/
theorem UpperTheory.ConvolutionTheory.C.polyBdAll :
    UpperTheory.ConvolutionTheory.C.PolyBdAll := by
  intro K _ _ n μ _ a
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  obtain ⟨C₀, N₀, hC₀⟩ := exists_norm_rconv_le_siegel_basic μ a hω ht
  obtain ⟨C₁, N₁, hC₁⟩ := UpperTheory.V.Fb.siegelHeight K n ω hω hωB t ht
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hω
  obtain ⟨c, hcdef⟩ : ∃ c, c = heightConst K n := ⟨_, rfl⟩
  have hc : 1 ≤ c := hcdef ▸ one_le_heightConst
  obtain ⟨M', hM'def⟩ : ∃ M', M' = max M 1 := ⟨_, rfl⟩
  have hM'1 : 1 ≤ M' := hM'def ▸ le_max_right _ _
  obtain ⟨E, hEdef⟩ : ∃ E, E = max C₁ 1 * 2 ^ N₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = c * (c * M') := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    exact one_le_mul_of_one_le_of_one_le hc (one_le_mul_of_one_le_of_one_le hc hM'1)
  refine ⟨max C₀ 0 * (D * E) ^ N₀, N₁ * N₀, fun φ x => ?_⟩
  have hq1 : 1 ≤ qht x := le_ciInf fun γ => one_le_height _
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K n)
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : normOneGL K n, γ₁ = ⟨AdelicGLn.diagonal K n γ, hγ1⟩ := ⟨_, rfl⟩
  have hγΓ : γ₁ ∈ Gam K n := ⟨γ, by rw [hγ₁]; rfl⟩
  have hhq : AutomorphicForm.height (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) ≤
      E * qht x ^ N₁ := by
    obtain ⟨γ', hγ'⟩ : ∃ γ' : Gam K n,
        AutomorphicForm.height (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) < 2 * qht x :=
      exists_lt_of_ciInf_lt (show qht x < 2 * qht x by linarith)
    obtain ⟨δ, hδ⟩ := γ'.2
    have hδ' : AdelicGLn.diagonal K n δ = (((γ' : G1 K n)) : AdelicGLn.AdelicGL K n) := hδ
    have e : AdelicGLn.diagonal K n (γ * δ⁻¹) * (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) =
        AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n) := by
      rw [Subgroup.coe_mul, ← hδ', map_mul, map_inv]
      group
    have h1 := hC₁ (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) (γ * δ⁻¹) (e ▸ hγ)
    rw [e] at h1
    refine h1.trans ?_
    have hy := height_pos (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)
    calc C₁ * _ ≤ max C₁ 1 * (2 * qht x) ^ N₁ :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hy.le hγ'.le _) (pow_nonneg hy.le _)
            (zero_le_one.trans (le_max_right _ _))
      _ = E * qht x ^ N₁ := by rw [hEdef, mul_pow]; ring
  rw [← rconv_mul_left (Gam K n) μ a φ hγΓ x]
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hx⟩ := hγ
  have hx' : ((γ₁ * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk := by
    rw [hγ₁]; exact hx
  obtain ⟨h, hhdef⟩ : ∃ h, h = AutomorphicForm.height (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) :=
    ⟨_, rfl⟩
  rw [← hhdef] at hhq
  have hh1 : 1 ≤ h := hhdef ▸ one_le_height _
  have hdiag : AutomorphicForm.height (diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i)) ≤ D * h := by
    have e : diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) =
        b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) * kk⁻¹ := by
      rw [hx]; group
    rw [e]
    have hbM : AutomorphicForm.height b⁻¹ ≤ M' := by
      rw [height_inv, hM'def]; exact (hM b hb).trans (le_max_left _ _)
    have hk : AutomorphicForm.height kk⁻¹ = 1 :=
      height_eq_one_of_mem_maxCompact (inv_mem hkk)
    have h1 := height_mul_le (b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))) kk⁻¹
    have h2 := height_mul_le b⁻¹ (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))
    rw [hk, mul_one, ← hcdef] at h1
    rw [← hcdef, ← hhdef] at h2
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have h3 : c * AutomorphicForm.height b⁻¹ * h ≤ c * M' * h := by gcongr
    calc _ ≤ c * AutomorphicForm.height (b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))) := h1
      _ ≤ c * (c * M' * h) := mul_le_mul_of_nonneg_left (h2.trans h3) hc0
      _ = D * h := by rw [hDdef]; ring
  have hDh1 : 1 ≤ D * h := one_le_mul_of_one_le_of_one_le hD1 hh1
  have hR1 : 1 ≤ (D * h) ^ 2 := one_le_pow₀ hDh1
  have hratio : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ (D * h) ^ 2 := by
    intro i j _
    have h1 := ((rho_le_height (K := K) hρ i).1).trans hdiag
    have h2 := ((rho_le_height (K := K) hρ j).2).trans hdiag
    rw [div_eq_mul_inv, sq]
    exact mul_le_mul h1 h2 (inv_pos.2 (hρ j)).le (zero_le_one.trans hDh1)
  have hmain := hC₀ φ b hb ρ hρ hs kk hkk (γ₁ * x) hx' _ hR1 hratio
  have hsq : √(((D * h) ^ 2) ^ N₀) = (D * h) ^ N₀ := by
    rw [pow_right_comm, Real.sqrt_sq (pow_nonneg (zero_le_one.trans hDh1) _)]
  rw [hsq] at hmain
  have hfin : (D * h) ^ N₀ ≤ (D * E) ^ N₀ * qht x ^ (N₁ * N₀) := by
    rw [pow_mul, ← mul_pow, mul_assoc]
    exact pow_le_pow_left₀ (zero_le_one.trans hDh1) (mul_le_mul_of_nonneg_left hhq (zero_le_one.trans hD1)) _
  have hnn : 0 ≤ (D * h) ^ N₀ := pow_nonneg (zero_le_one.trans hDh1) _
  calc _ ≤ C₀ * (D * h) ^ N₀ * ‖φ‖ := hmain
    _ ≤ max C₀ 0 * (D * h) ^ N₀ * ‖φ‖ := by gcongr; exact le_max_left _ _
    _ ≤ max C₀ 0 * ((D * E) ^ N₀ * qht x ^ (N₁ * N₀)) * ‖φ‖ := by
        have : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
        gcongr
    _ = max C₀ 0 * (D * E) ^ N₀ * qht x ^ (N₁ * N₀) * ‖φ‖ := by ring
