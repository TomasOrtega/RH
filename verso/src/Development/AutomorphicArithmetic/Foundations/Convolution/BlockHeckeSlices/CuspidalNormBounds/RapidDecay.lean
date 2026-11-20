import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel

noncomputable section

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.ConvolutionTheory.BW

section

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

private structure Good (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  sm : φ ∈ archSmooth K n
  cont : Continuous φ
  left : IsLeftInvariant φ
  lev : ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n), ∀ g, ∀ u ∈ U, φ (g * finEmb K n u) = φ g
  gr : ∃ N : ℕ, ∀ u : UEnv K n, HasGrowth (uAction u ⟨φ, sm⟩ : AdelicGLn.AdelicGL K n → ℂ) N
  cusp : IsCuspidal φ

/- English proof (translation)
Take `⟨N, hN⟩` from `hφ.gr`. Use `hN 1` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `⟨N, this⟩`.
-/
private theorem Good.mod {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Good φ) : ∃ N, HasGrowth φ N := by
  obtain ⟨N, hN⟩ := hφ.gr
  have := hN 1
  rw [map_one] at this
  exact ⟨N, this⟩

/- English proof (translation)
Take `⟨N, hN⟩` from `hφ.gr`. Use `⟨N, fun k T => ?_⟩` and prove the remaining obligations. Take `⟨c, hc0, hc⟩` from `exists_abs_archBasis_repr_le (K := K) (n := n)`. Establish `hgrowth : ∀ J : Fin k → Fin (archDim K n), HasGrowth (uAction (uJ k J) ⟨φ, hφ.sm⟩ : AdelicGLn.AdelicGL K n → ℂ) N` using `fun J => hN _`. Use `choose CJ hCJ using hgrowth`.

Use `set T' := (k : ℝ) * max T 0`. Use `set S : Set (archGroup K n) := (fun Z : ArchMatrix K n => (isExpLieAlgebra K n).expG ⟨Z, Submodule.mem_top⟩) '' Metric.closedBall 0 T'`. Establish `hS : IsCompact S` using `(isCompact_closedBall _ _).image ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _))`. Take `⟨Mh, hMh⟩` from `exists_height_infEmb_le (K := K) (n := n) hS`. Use `set Mh' := max Mh 1`.

Use `set Cs := ∑ J, |CJ J|`. Establish `hCs : 0 ≤ Cs` using `Finset.sum_nonneg fun J _ => abs_nonneg _`. Establish `hc0' : 0 ≤ heightConst K n` using `le_trans zero_le_one one_le_heightConst`. Use `⟨(archDim K n * c) ^ k * (Cs * (heightConst K n * Mh') ^ N), fun x Y hYY hYT => ?_⟩` and prove the remaining obligations. Establish `hcomm : ∀ i j, Commute (Y i) (Y j)` using `fun i j => (hYY i j).trans (hYY j i).symm`.

Establish `hB0 : 0 ≤ Cs * (heightConst K n * Mh') ^ N * height x ^ N`. Use `height_pos x` as an intermediate fact. Establish `: 0 ≤ Mh'` using `le_trans zero_le_one (le_max_right _ _)`. Check the signs of the components of the expression. Establish `h` using `norm_diffSum_le hc0 hc k ⟨φ, hφ.sm⟩ x Y hcomm _ hB0 fun J t ht => by`.

Establish `hZ : ‖∑ i, t i • Y i‖ ≤ T'`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, Real.norm_of_nonneg (ht i).1]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = T' := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hmem : (isExpLieAlgebra K n).expG ⟨∑ i, t i • Y i, Submodule.mem_top⟩ ∈ S` using `⟨_, mem_closedBall_zero_iff.2 hZ, rfl⟩`. Establish `hh : height (x * archExp (∑ i, t i • Y i)) ≤ heightConst K n * height x * Mh'` using `(height_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((hMh _ hmem).trans (le_max_left _ _)) (mul_nonneg hc0' (height_pos x).le))`. Combine the equalities or inequalities in the displayed calculation. Use `height_pos x` as an intermediate fact.

Establish `: 0 ≤ Mh'` using `le_trans zero_le_one (le_max_right _ _)`. Use the proof step `positivity)`. Use `_ = Cs * (heightConst K n * Mh') ^ N * height x ^ N := by ring`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem diff_le {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Good φ) :
    ∃ N : ℕ, ∀ (k : ℕ) (T : ℝ), ∃ C : ℝ, ∀ (x : AdelicGLn.AdelicGL K n)
      (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ T) →
      ‖diffSum φ x Y‖ ≤ C * (∏ i, ‖Y i‖) * height x ^ N := by
  obtain ⟨N, hN⟩ := hφ.gr
  refine ⟨N, fun k T => ?_⟩
  obtain ⟨c, hc0, hc⟩ := exists_abs_archBasis_repr_le (K := K) (n := n)
  have hgrowth : ∀ J : Fin k → Fin (archDim K n),
      HasGrowth (uAction (uJ k J) ⟨φ, hφ.sm⟩ : AdelicGLn.AdelicGL K n → ℂ) N :=
    fun J => hN _
  choose CJ hCJ using hgrowth
  set T' := (k : ℝ) * max T 0
  set S : Set (archGroup K n) :=
    (fun Z : ArchMatrix K n => (isExpLieAlgebra K n).expG ⟨Z, Submodule.mem_top⟩) ''
      Metric.closedBall 0 T'
  have hS : IsCompact S := (isCompact_closedBall _ _).image
    ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _))
  obtain ⟨Mh, hMh⟩ := exists_height_infEmb_le (K := K) (n := n) hS
  set Mh' := max Mh 1
  set Cs := ∑ J, |CJ J|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun J _ => abs_nonneg _
  have hc0' : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  refine ⟨(archDim K n * c) ^ k * (Cs * (heightConst K n * Mh') ^ N), fun x Y hYY hYT => ?_⟩
  have hcomm : ∀ i j, Commute (Y i) (Y j) := fun i j => (hYY i j).trans (hYY j i).symm
  have hB0 : 0 ≤ Cs * (heightConst K n * Mh') ^ N * height x ^ N := by
    have := height_pos x
    have : 0 ≤ Mh' := le_trans zero_le_one (le_max_right _ _)
    positivity
  have h := norm_diffSum_le hc0 hc k ⟨φ, hφ.sm⟩ x Y hcomm _ hB0 fun J t ht => by
    have hZ : ‖∑ i, t i • Y i‖ ≤ T' := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖t i • Y i‖ ≤ ∑ _i : Fin k, max T 0 := Finset.sum_le_sum fun i _ => by
            rw [norm_smul, Real.norm_of_nonneg (ht i).1]
            calc t i * ‖Y i‖ ≤ 1 * max T 0 :=
                  mul_le_mul (ht i).2 ((hYT i).trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
              _ = max T 0 := one_mul _
        _ = T' := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmem : (isExpLieAlgebra K n).expG ⟨∑ i, t i • Y i, Submodule.mem_top⟩ ∈ S :=
      ⟨_, mem_closedBall_zero_iff.2 hZ, rfl⟩
    have hh : height (x * archExp (∑ i, t i • Y i)) ≤ heightConst K n * height x * Mh' :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((hMh _ hmem).trans (le_max_left _ _))
        (mul_nonneg hc0' (height_pos x).le))
    calc ‖(uAction (uJ k J) ⟨φ, hφ.sm⟩ : AdelicGLn.AdelicGL K n → ℂ)
          (x * archExp (∑ i, t i • Y i))‖
        ≤ CJ J * height (x * archExp (∑ i, t i • Y i)) ^ N := hCJ J _
      _ ≤ |CJ J| * (heightConst K n * height x * Mh') ^ N :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (height_pos _).le hh _)
            (pow_nonneg (height_pos _).le _) (abs_nonneg _)
      _ ≤ Cs * (heightConst K n * height x * Mh') ^ N :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun J => |CJ J|)
            (fun J _ => abs_nonneg _) (Finset.mem_univ J)) (by
              have := height_pos x
              have : 0 ≤ Mh' := le_trans zero_le_one (le_max_right _ _)
              positivity)
      _ = Cs * (heightConst K n * Mh') ^ N * height x ^ N := by ring
  refine h.trans (le_of_eq ?_)
  ring

/- English proof (translation)
Take `⟨N, hN⟩` from `diff_le hφ`. Use `⟨N, fun k => ?_⟩` and prove the remaining obligations. Take `⟨U₀, hU₀⟩` from `hφ.lev`. Use `set U : Subgroup (AdelicGLn.integralFiniteGL K n) := (U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)).subgroupOf (AdelicGLn.integralFiniteGL K n)`. Establish `hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))` using `U₀.isOpen.preimage continuous_subtype_val`.

Take `⟨M, hM, hMconj⟩` from `exists_natCast_conj_unipGL_mem U hU hω r`. Take `⟨C₁, hC₁⟩` from `exists_norm_archMat_conj_le hω hωB ht hr hrn (isCompact_scaledInfSet (K := K) M)`. Use `set C₁' := max C₁ 0`. Establish `hC₁'0 : 0 ≤ C₁'` using `le_max_right _ _`. Take `⟨C, hC⟩` from `hN k (C₁' * t⁻¹)`.

Use `⟨max C 0 * C₁' ^ k, ?_⟩` and prove the remaining obligations. Introduce `b hb ρ hρ hsieg kk hkk x hx`. Use `set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩`. Establish `hgain0 : 0 ≤ gain` using `div_nonneg (hρ _).le (hρ _).le`. Establish `hgain : gain ≤ t⁻¹`.

Establish `h1` using `hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)`. Rewrite using `[div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]`. Conclude with `h1`. Use `set H : (UPos n r → 𝔸[K]) → ℂ := fun s => φ (unipGL s * x) with hH`. Establish `hHc : Continuous H` using `hφ.cont.comp (continuous_unipGL.mul continuous_const)`.

Establish `hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s` using `fun ξ hξ s => hφ.left.unipGL_vadd x ⟨ξ, hξ⟩ s`. Establish `hD` using `isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM`. Take `⟨Cc, hCc, hDC⟩` from `exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM`. Establish `hint : ∀ t', IntegrableOn (fun y => H (t' + y)) (scaledUnipFD K n r M) (unipMeasure K n r)` using `fun t' => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact hCc).mono_set hDC`. Establish `hmean : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = 0`.

Rewrite using `[hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]`. Conclude with `hφ.cusp r hr hrn x`. Establish `h0` using `norm_le_of_forall_altSum_le hD (unipMeasure_scaledUnipFD hM) k H hper hint hmean (max C 0 * (C₁' * gain) ^ k * height x ^ N) ?_`. Establish `hH0 : H 0 = φ x` using `by simp [hH, unipGL_zero]`. Rewrite `h0` using `[hH0]`.

Use `h0.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Introduce `y hy`. Use `set Y : Fin k → ArchMatrix K n := fun i => conjArch K n x (truncInf (y i)) with hYdef`.

Establish `hYY : ∀ i j, Y i * Y j = 0` using `fun i j => conjArch_mul_conjArch _ _ _`. Establish `hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain`. Introduce `i`. Establish `h1` using `hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM (hy i) p)`. Apply the tactic sequence `have h2 : Y i = archMat K n ((((b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry (truncInf (y i)) * ((b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) ( …`.

Simplify using `only [hYdef, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]`. Rewrite using `[h2]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)`. Establish `hYT : ∀ i, ‖Y i‖ ≤ C₁' * t⁻¹` using `fun i => (hYn i).trans (mul_le_mul_of_nonneg_left hgain hC₁'0)`. Establish `key : ∀ ε : Fin k → Bool, H (0 + altPoint y ε) = φ (x * archExp (altPoint Y ε))`.

Introduce `ε`. Rewrite using `[zero_add]`. Use `set P := altPoint y ε`. Take `⟨u, hu⟩` from `hMconj b hb ρ hρ kk hkk (truncFin P) (fun p => rfl) fun p => by`. Take `⟨a, ha, hPa⟩` from `exists_finite_altPoint_eq_natCast_mul hM y hy ε p`.

Conclude with `⟨a, ha, hPa⟩`. Rewrite `hu` using `[← hx]`. Establish `hsplit : unipGL P * x = unipGL (truncInf P) * x * (x⁻¹ * unipGL (truncFin P) * x)`. Rewrite using `[show unipGL P = unipGL (truncInf P) * unipGL (truncFin P) by`. Rewrite using `[← unipGL_add, truncInf_add_truncFin]]`.

Use `group`. Establish `hinf : unipGL (truncInf P) * x = x * (x⁻¹ * unipGL (truncInf P) * x)` using `by group`. Establish `hY : conjArch K n x (truncInf P) = altPoint Y ε`. Rewrite using `[← truncInfHom_apply, map_altPoint (truncInfHom n r), map_altPoint (conjArch K n x)]`. Both sides reduce to the same expression.

Simplify using `only [hH]`. Rewrite using `[hsplit, hu, hU₀ _ ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) (Subgroup.mem_subgroupOf.1 u.2), hinf, conj_unipGL_eq_archExp x _ fun p => rfl, hY]`. Establish `hsum : altSum k H y 0 = diffSum φ x Y`. Rewrite using `[altSum_eq_sum, diffSum]`. Use `Finset.sum_congr rfl fun ε _ => ?_` and prove the remaining obligations.

Rewrite using `[key ε, zsmul_eq_mul]`. Rewrite using `[hsum]`. Use `(hC x Y hYY hYT).trans ?_` and prove the remaining obligations. Establish `hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k`. Rewrite using `[← Fin.prod_const]`.

Conclude with `Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i`. Establish `hh` using `pow_nonneg (height_pos x).le N`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem root_le {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Good φ)
    {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((Reduction.adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) :
      Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n,
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ‖φ x‖ ≤ C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * height x ^ N := by
  obtain ⟨N, hN⟩ := diff_le hφ
  refine ⟨N, fun k => ?_⟩
  obtain ⟨U₀, hU₀⟩ := hφ.lev
  set U : Subgroup (AdelicGLn.integralFiniteGL K n) :=
    (U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)).subgroupOf (AdelicGLn.integralFiniteGL K n)
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) :=
    U₀.isOpen.preimage continuous_subtype_val
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  obtain ⟨C, hC⟩ := hN k (C₁' * t⁻¹)
  refine ⟨max C 0 * C₁' ^ k, ?_⟩
  intro b hb ρ hρ hsieg kk hkk x hx
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => φ (unipGL s * x) with hH
  have hHc : Continuous H := hφ.cont.comp (continuous_unipGL.mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := fun ξ hξ s =>
    hφ.left.unipGL_vadd x ⟨ξ, hξ⟩ s
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t', IntegrableOn (fun y => H (t' + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t' => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hmean : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = 0 := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    exact hφ.cusp r hr hrn x
  have h0 := norm_le_of_forall_altSum_le hD (unipMeasure_scaledUnipFD hM) k H hper hint hmean
    (max C 0 * (C₁' * gain) ^ k * height x ^ N) ?_
  · have hH0 : H 0 = φ x := by simp [hH, unipGL_zero]
    rw [hH0] at h0
    refine h0.trans (le_of_eq ?_)
    rw [mul_pow]
    ring
  intro y hy
  set Y : Fin k → ArchMatrix K n := fun i => conjArch K n x (truncInf (y i)) with hYdef
  have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
  have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
    intro i
    have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
      (fun p => infinite_mem_scaledInfSet hM (hy i) p)
    have h2 : Y i = archMat K n ((((b * Reduction.diagUnits n (fun i =>
        Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk)⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry (truncInf (y i)) *
        ((b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk :
          AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
      simp only [hYdef, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
    rw [h2]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
  have hYT : ∀ i, ‖Y i‖ ≤ C₁' * t⁻¹ := fun i =>
    (hYn i).trans (mul_le_mul_of_nonneg_left hgain hC₁'0)
  have key : ∀ ε : Fin k → Bool, H (0 + altPoint y ε) = φ (x * archExp (altPoint Y ε)) := by
    intro ε
    rw [zero_add]
    set P := altPoint y ε
    obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk (truncFin P) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    rw [← hx] at hu
    have hsplit : unipGL P * x = unipGL (truncInf P) * x * (x⁻¹ * unipGL (truncFin P) * x) := by
      rw [show unipGL P = unipGL (truncInf P) * unipGL (truncFin P) by
        rw [← unipGL_add, truncInf_add_truncFin]]
      group
    have hinf : unipGL (truncInf P) * x = x * (x⁻¹ * unipGL (truncInf P) * x) := by group
    have hY : conjArch K n x (truncInf P) = altPoint Y ε := by
      rw [← truncInfHom_apply, map_altPoint (truncInfHom n r), map_altPoint (conjArch K n x)]
      rfl
    simp only [hH]
    rw [hsplit, hu, hU₀ _ ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)
      (Subgroup.mem_subgroupOf.1 u.2), hinf, conj_unipGL_eq_archExp x _ fun p => rfl, hY]
  have hsum : altSum k H y 0 = diffSum φ x Y := by
    rw [altSum_eq_sum, diffSum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [key ε, zsmul_eq_mul]
  rw [hsum]
  refine (hC x Y hYY hYT).trans ?_
  have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k := by
    rw [← Fin.prod_const]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
  have hh := pow_nonneg (height_pos x).le N
  calc C * (∏ i, ‖Y i‖) * height x ^ N ≤ max C 0 * (∏ i, ‖Y i‖) * height x ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)) hh
    _ ≤ max C 0 * (C₁' * gain) ^ k * height x ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (le_max_right _ _)) hh

/- English proof (translation)
Take `⟨N₀, C₀, hC₀⟩` from `hφ.mod`. Take `⟨Ch, hCh0, hCh⟩` from `exists_height_le_normOne (K := K) (n := n) hω`. Use `set e := 2 * Fintype.card (InfinitePlace K)`. Use `set τ := (max 1 t⁻¹) ^ n with hτ`. Establish `hτ1 : 1 ≤ τ` using `one_le_pow₀ (le_max_left _ _)`.

Use `set D := max (Ch * τ ^ e) 1 with hD`. Establish `hD1 : 1 ≤ D` using `le_max_right _ _`. Establish `hD0 : 0 ≤ D` using `le_trans zero_le_one hD1`. Establish `hroot` using `fun (r : ℕ) (hr : 0 < r) (hrn : r < n) => root_le hφ hω hωB ht hr hrn`. Use `choose Nf hNf using hroot`.

Establish `hroot2` using `fun (r : ℕ) (hr : 0 < r) (hrn : r < n) => hNf r hr hrn (n * e * (Nf r hr hrn + N'))`. Use `choose Cf hCf using hroot2`. Use `set S : ℝ := ∑ r : Fin n, if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 * D ^ (Nf r h r.2 + N') else 0 with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun r _ => by split_ifs`. Conclude with `mul_nonneg (le_max_right _ _) (pow_nonneg hD0 _)`.

Conclude with `le_rfl`. Establish `hSle : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), max (Cf r hr hrn) 0 * D ^ (Nf r hr hrn + N') ≤ S`. Introduce `r hr hrn`. Establish `h1` using `Finset.single_le_sum (f := fun r : Fin n => if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 * D ^ (Nf r h r.2 + N') else 0) (fun r _ => by split_ifs`. Conclude with `mul_nonneg (le_max_right _ _) (pow_nonneg hD0 _)`.

Conclude with `le_rfl) (Finset.mem_univ ⟨r, hrn⟩)`. Simplify `h1` using `only [hr, dif_pos]`. Use `set C₀' := |C₀| * D ^ (N₀ + N')`. Establish `hC₀'0 : 0 ≤ C₀'` using `mul_nonneg (abs_nonneg _) (pow_nonneg hD0 _)`. Use `⟨C₀' + S, ?_⟩` and prove the remaining obligations.

Introduce `b hb ρ hρ hsieg kk hkk x hx1 hx`. Establish `hh0 : 0 < height x` using `height_pos x`. Establish `hhN' : 0 < height x ^ N'` using `pow_pos hh0 _`. Establish `hsmall : height x ≤ D → ‖φ x‖ ≤ (C₀' + S) * (height x ^ N')⁻¹`. Introduce `hxD`.

Establish `h1 : ‖φ x‖ ≤ |C₀| * D ^ N₀` using `(hC₀ x).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hh0.le hxD _) (pow_nonneg hh0.le _) (abs_nonneg _))`. Establish `h2 : |C₀| * D ^ N₀ ≤ C₀' * (height x ^ N')⁻¹`. Rewrite using `[le_mul_inv_iff₀ hhN']`. Simplify using `only [C₀', pow_add, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0.le hxD _) (pow_nonneg hD0 _)) (abs_nonneg _)`.

Use `h1.trans (h2.trans ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (inv_nonneg.2 hhN'.le)`. Establish `hheight : ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) → height x ≤ D * R ^ e`. Introduce `R hR1 hR`. Establish `hall : ∀ i j : Fin n, ρ i / ρ j ≤ τ * R` using `fun i j => siegel_div_le_mul ht hρ hsieg hR1 hR i j`.

Establish `h1` using `hCh b hb ρ hρ kk hkk x hx1 hx (τ * R) (one_le_mul_of_one_le_of_one_le hτ1 hR1) hall`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hn : 2 ≤ n`. Take `⟨r, hr, hrn, hratio⟩` from `exists_le_max_pow hn ρ hρ set α := ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ with hα`. Establish `hα0 : 0 < α` using `div_pos (hρ _) (hρ _)`.

Break down `le_or_gt α 1 with hα1 | hα1` into its components or cases. Use `hsmall ?_` and prove the remaining obligations. Use `hheight 1 le_rfl fun i j hij => (hratio i j hij).trans (by` as an intermediate fact. Rewrite using `[max_eq_left hα1, one_pow])`. Simplify using `using this`.

Establish `hM : max 1 α = α` using `max_eq_right hα1.le set A := α ^ (n * e) with hA`. Establish `hA1 : 1 ≤ A` using `one_le_pow₀ hα1.le`. Establish `hxA : height x ≤ D * A`. Use `hheight (α ^ n) (one_le_pow₀ hα1.le) fun i j hij => (hratio i j hij).trans (by rw [hM])` as an intermediate fact. Rewrite `this` using `[← pow_mul]`. Then use the resulting hypothesis.

Use `set k := n * e * (Nf r hr hrn + N')`. Establish `h1` using `hCf r hr hrn b hb ρ hρ hsieg kk hkk x hx`. Establish `hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩ = α⁻¹` using `by rw [hα, inv_div]`. Rewrite `h1` using `[hgain]`. Establish `hk : (α⁻¹) ^ k = (A ^ (Nf r hr hrn + N'))⁻¹`.

Rewrite using `[inv_pow, hA, ← pow_mul]`. Rewrite `h1` using `[hk]`. Establish `hApos : 0 < A` using `lt_of_lt_of_le one_pos hA1`. Establish `hAN : 0 < A ^ N'` using `pow_pos hApos _`. Establish `hhN : height x ^ Nf r hr hrn ≤ D ^ Nf r hr hrn * A ^ Nf r hr hrn`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hh0.le hxA _`. Establish `hhN'' : height x ^ N' ≤ D ^ N' * A ^ N'`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hh0.le hxA _`.

Use `set Cr := max (Cf r hr hrn) 0`. Establish `hCr0 : 0 ≤ Cr` using `le_max_right _ _`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (pow_nonneg hApos.le _))) hhN (pow_nonneg hh0.le _) (mul_nonneg hCr0 (inv_nonneg.2 (pow_nonneg hApos.le _)))` and prove the remaining obligations. Use `_ = Cr * D ^ Nf r hr hrn * (A ^ N')⁻¹ := by`.

Rewrite using `[pow_add]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ Cr * D ^ Nf r hr hrn * (D ^ N' * (height x ^ N')⁻¹) := by`. Use `mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCr0 (pow_nonneg hD0 _))` and prove the remaining obligations. Rewrite using `[inv_le_iff_one_le_mul₀ hAN, mul_right_comm, ← div_eq_mul_inv, le_div_iff₀ hhN', one_mul]`.

Conclude with `hhN''`. Use `_ = Cr * D ^ (Nf r hr hrn + N') * (height x ^ N')⁻¹ := by rw [pow_add]; ring`. Use `_ ≤ (C₀' + S) * (height x ^ N')⁻¹ := by`. Use `mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hhN'.le)` and prove the remaining obligations. Conclude with `(hSle r hr hrn).trans (le_add_of_nonneg_left hC₀'0)`.

Use `hsmall ?_` and prove the remaining obligations. Use `hheight 1 le_rfl fun i j hij => by` as an intermediate fact. It suffices to derive a contradiction. Establish `: (i : ℕ) < j` using `hij`. Use linear arithmetic over natural numbers and integers.

Simplify using `using this`.
-/
private theorem siegel_le {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : Good φ) {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((Reduction.adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) :
      Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) (N' : ℕ) :
    ∃ C : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n, x ∈ Reduction.normOneGL K n →
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ‖φ x‖ ≤ C * (height x ^ N')⁻¹ := by
  obtain ⟨N₀, C₀, hC₀⟩ := hφ.mod
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := K) (n := n) hω
  set e := 2 * Fintype.card (InfinitePlace K)
  set τ := (max 1 t⁻¹) ^ n with hτ
  have hτ1 : 1 ≤ τ := one_le_pow₀ (le_max_left _ _)
  set D := max (Ch * τ ^ e) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  have hroot := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) => root_le hφ hω hωB ht hr hrn
  choose Nf hNf using hroot
  have hroot2 := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) => hNf r hr hrn (n * e * (Nf r hr hrn + N'))
  choose Cf hCf using hroot2
  set S : ℝ := ∑ r : Fin n, if h : 0 < (r : ℕ) then
    max (Cf r h r.2) 0 * D ^ (Nf r h r.2 + N') else 0 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => by
    split_ifs
    · exact mul_nonneg (le_max_right _ _) (pow_nonneg hD0 _)
    · exact le_rfl
  have hSle : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n),
      max (Cf r hr hrn) 0 * D ^ (Nf r hr hrn + N') ≤ S := by
    intro r hr hrn
    have h1 := Finset.single_le_sum (f := fun r : Fin n => if h : 0 < (r : ℕ) then
      max (Cf r h r.2) 0 * D ^ (Nf r h r.2 + N') else 0)
      (fun r _ => by
        split_ifs
        · exact mul_nonneg (le_max_right _ _) (pow_nonneg hD0 _)
        · exact le_rfl) (Finset.mem_univ ⟨r, hrn⟩)
    simpa only [hr, dif_pos] using h1
  set C₀' := |C₀| * D ^ (N₀ + N')
  have hC₀'0 : 0 ≤ C₀' := mul_nonneg (abs_nonneg _) (pow_nonneg hD0 _)
  refine ⟨C₀' + S, ?_⟩
  intro b hb ρ hρ hsieg kk hkk x hx1 hx
  have hh0 : 0 < height x := height_pos x
  have hhN' : 0 < height x ^ N' := pow_pos hh0 _

  have hsmall : height x ≤ D → ‖φ x‖ ≤ (C₀' + S) * (height x ^ N')⁻¹ := by
    intro hxD
    have h1 : ‖φ x‖ ≤ |C₀| * D ^ N₀ :=
      (hC₀ x).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hh0.le hxD _)
        (pow_nonneg hh0.le _) (abs_nonneg _))
    have h2 : |C₀| * D ^ N₀ ≤ C₀' * (height x ^ N')⁻¹ := by
      rw [le_mul_inv_iff₀ hhN']
      simp only [C₀', pow_add, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hh0.le hxD _) (pow_nonneg hD0 _)) (abs_nonneg _)
    refine h1.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (inv_nonneg.2 hhN'.le)

  have hheight : ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      height x ≤ D * R ^ e := by
    intro R hR1 hR
    have hall : ∀ i j : Fin n, ρ i / ρ j ≤ τ * R := fun i j =>
      siegel_div_le_mul ht hρ hsieg hR1 hR i j
    have h1 := hCh b hb ρ hρ kk hkk x hx1 hx (τ * R) (one_le_mul_of_one_le_of_one_le hτ1 hR1) hall
    calc height x ≤ Ch * (τ * R) ^ e := h1
      _ = Ch * τ ^ e * R ^ e := by rw [mul_pow]; ring
      _ ≤ D * R ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (le_trans zero_le_one hR1) _)
  by_cases hn : 2 ≤ n
  · obtain ⟨r, hr, hrn, hratio⟩ := exists_le_max_pow hn ρ hρ
    set α := ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ with hα
    have hα0 : 0 < α := div_pos (hρ _) (hρ _)
    rcases le_or_gt α 1 with hα1 | hα1
    · refine hsmall ?_
      have := hheight 1 le_rfl fun i j hij => (hratio i j hij).trans (by
        rw [max_eq_left hα1, one_pow])
      simpa using this
    · have hM : max 1 α = α := max_eq_right hα1.le
      set A := α ^ (n * e) with hA
      have hA1 : 1 ≤ A := one_le_pow₀ hα1.le
      have hxA : height x ≤ D * A := by
        have := hheight (α ^ n) (one_le_pow₀ hα1.le) fun i j hij =>
          (hratio i j hij).trans (by rw [hM])
        rwa [← pow_mul] at this
      set k := n * e * (Nf r hr hrn + N')
      have h1 := hCf r hr hrn b hb ρ hρ hsieg kk hkk x hx
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩ = α⁻¹ := by rw [hα, inv_div]
      rw [hgain] at h1
      have hk : (α⁻¹) ^ k = (A ^ (Nf r hr hrn + N'))⁻¹ := by
        rw [inv_pow, hA, ← pow_mul]
      rw [hk] at h1
      have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
      have hAN : 0 < A ^ N' := pow_pos hApos _
      have hhN : height x ^ Nf r hr hrn ≤ D ^ Nf r hr hrn * A ^ Nf r hr hrn := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hh0.le hxA _
      have hhN'' : height x ^ N' ≤ D ^ N' * A ^ N' := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hh0.le hxA _
      set Cr := max (Cf r hr hrn) 0
      have hCr0 : 0 ≤ Cr := le_max_right _ _
      calc ‖φ x‖ ≤ Cf r hr hrn * (A ^ (Nf r hr hrn + N'))⁻¹ * height x ^ Nf r hr hrn := h1
        _ ≤ Cr * (A ^ (Nf r hr hrn + N'))⁻¹ * (D ^ Nf r hr hrn * A ^ Nf r hr hrn) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (inv_nonneg.2 (pow_nonneg hApos.le _))) hhN (pow_nonneg hh0.le _)
              (mul_nonneg hCr0 (inv_nonneg.2 (pow_nonneg hApos.le _)))
        _ = Cr * D ^ Nf r hr hrn * (A ^ N')⁻¹ := by
            rw [pow_add]; field_simp
        _ ≤ Cr * D ^ Nf r hr hrn * (D ^ N' * (height x ^ N')⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCr0 (pow_nonneg hD0 _))
            rw [inv_le_iff_one_le_mul₀ hAN, mul_right_comm, ← div_eq_mul_inv, le_div_iff₀ hhN',
              one_mul]
            exact hhN''
        _ = Cr * D ^ (Nf r hr hrn + N') * (height x ^ N')⁻¹ := by rw [pow_add]; ring
        _ ≤ (C₀' + S) * (height x ^ N')⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hhN'.le)
            exact (hSle r hr hrn).trans (le_add_of_nonneg_left hC₀'0)
  · refine hsmall ?_
    have := hheight 1 le_rfl fun i j hij => by
      exfalso
      have : (i : ℕ) < j := hij
      omega
    simpa using this

end

open GlobalTheory.CuspRep UpperTheory.V.Cm in
/- English proof (translation)
Set `S : Subgroup (GL (Fin n) (Af E))` to `{ carrier := {k | GlobalTheory.CuspRep.finRep E n k φ = φ} one_mem' := by simp mul_mem' := fun {k l} hk hl => by`. Express the relevant statement in the definitionally equal form `GlobalTheory.CuspRep.finRep E n (k * l) φ = φ`. Rewrite using `[map_mul, Module.End.mul_apply, hl, hk]`. Use the proof step `inv_mem' := fun {k} hk => by`. Express the relevant statement in the definitionally equal form `GlobalTheory.CuspRep.finRep E n k⁻¹ φ = φ`.

Use `conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E n k φ = φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Use `rfl }`. Use `⟨(smEq E n φ).2, GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n φ h.level, h.left, ⟨⟨S, h.level⟩, fun g u hu => ?_⟩, ?_, hc⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.V.Fb.finEmb_eq]`. Conclude with `congrFun (congrArg Subtype.val (show GlobalTheory.CuspRep.finRep E n u φ = φ from hu)) g`.

Take `⟨N, hN⟩` from `h.growth`. Use `⟨N, fun u => ?_⟩` and prove the remaining obligations. Use `hN (1 ⊗ₜ u)` as an intermediate fact. Rewrite `this` using `[uC_tmul, one_smul]`. Conclude with `this`.
-/
private theorem good_of {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {φ : Sm E n} (h : Umg φ)
    (hc : Cusp φ.1) : Good φ.1 := by
  let S : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E n k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E n (k * l) φ = φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E n k⁻¹ φ = φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E n k φ = φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine ⟨(smEq E n φ).2, GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n φ h.level, h.left, ⟨⟨S, h.level⟩, fun g u hu => ?_⟩, ?_, hc⟩
  · rw [UpperTheory.V.Fb.finEmb_eq]
    exact congrFun (congrArg Subtype.val (show GlobalTheory.CuspRep.finRep E n u φ = φ from hu)) g
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun u => ?_⟩
    have := hN (1 ⊗ₜ u)
    rw [uC_tmul, one_smul] at this
    exact this

end UpperTheory.ConvolutionTheory.BW

/- English proof (translation)
Introduce `E _ _ _ n φ hU hc N`. Establish `h0` using `good_of hU hc`. Take `⟨ω, hω, hωB, t, ht, hsieg⟩` from `Reduction.exists_siegelSet (K := E) n`. Take `⟨C, hC⟩` from `siegel_le h0 hω hωB ht N`. Use `⟨C, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩` from `hsieg g.1`. Establish `hγ1 : AdelicGLn.diagonal E n γ ∈ Reduction.normOneGL E n` using `Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩`. Establish `h` using `hC b hb ρ hρ hs kk hkk _ (mul_mem hγ1 g.2) hxe`. Rewrite `h` using `[h0.left γ g.1]`. Establish `hp` using `height_pos (AdelicGLn.diagonal E n γ * g.1)`.

Establish `hq : PositivityTheory.Rg.Tf.Core.qht g ≤ height (AdelicGLn.diagonal E n γ * g.1)` using `ciInf_le (f := fun γ : PositivityTheory.Rg.Tf.Core.Gam E n => height (((γ : Reduction.normOneGL E n) * g : Reduction.normOneGL E n) : AdelicGLn.AdelicGL E n)) ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ ⟨⟨_, hγ1⟩, ⟨γ, rfl⟩⟩`. Establish `hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht g` using `le_ciInf fun _ => (height_pos _).le`. Rewrite `h` using `[le_mul_inv_iff₀ (pow_pos hp N)]`. Conclude with `(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq N) (norm_nonneg _)).trans h`.
-/
theorem UpperTheory.ConvolutionTheory.BW.rapidDecay :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.RapidDecay E := by
  intro E _ _ _ n φ hU hc N
  have h0 := good_of hU hc
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) n
  obtain ⟨C, hC⟩ := siegel_le h0 hω hωB ht N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγ1 : AdelicGLn.diagonal E n γ ∈ Reduction.normOneGL E n := Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩
  have h := hC b hb ρ hρ hs kk hkk _ (mul_mem hγ1 g.2) hxe
  rw [h0.left γ g.1] at h
  have hp := height_pos (AdelicGLn.diagonal E n γ * g.1)
  have hq : PositivityTheory.Rg.Tf.Core.qht g ≤ height (AdelicGLn.diagonal E n γ * g.1) :=
    ciInf_le (f := fun γ : PositivityTheory.Rg.Tf.Core.Gam E n => height (((γ : Reduction.normOneGL E n) * g : Reduction.normOneGL E n) : AdelicGLn.AdelicGL E n))
      ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ ⟨⟨_, hγ1⟩, ⟨γ, rfl⟩⟩
  have hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht g := le_ciInf fun _ => (height_pos _).le
  rw [le_mul_inv_iff₀ (pow_pos hp N)] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq N) (norm_nonneg _)).trans h
