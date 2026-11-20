import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDataLinearChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormVerticalNegativeImagPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTorusFlatCoordsInverse
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqCexpQuadraticOfEquivalentFactors
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat InducesPolarisation cov per herm riem)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology MonoidalCategory
open scoped ContDiff CategoryTheory.Obj MonObj ComplexOrder

namespace GlobalTheory.ThetaPol

/- English proof (translation)
Take `⟨hI, hrig, hsym, hamp, hk, hc⟩` from `hT`. Establish `h` using `isGrpPullback_pullback P.A y`. Establish `hL` using `pull_isLB hI (Limits.pullback.fst P.A.hom y)`. Take `⟨w, hw⟩` from `(CechPic.cls_eq_iff hL hL).1 rfl`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S) (x := y (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial`.

Set `Q' : Out.PolAV (Sp ℂ)` to `⟨(Over.pullback y).obj P.A, PolPull.isAbelianScheme_of_isGrpPullback P.isAb h, P.g, (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim, _, hL, PolBaseChange.rigidified_pull h hrig, PolBaseChange.sym_pull h hsym, relAmple_pull h.1 hI hL ((isGen_iff …`. Take `⟨rig, hr⟩` from `Q'.rigid`. Take `⟨u, H, χ, -, hH, -⟩` from `thetaUnifAV_all Q' rig hr`. Conclude with `⟨⟨Q'.A, _, h, Q'.L, hL, (congrArg _ hc).trans ((PPAS.pull_sqMap_lam h _).trans (congrArg (CechPic.lam · _ _) (CechPic.cls_pull hI _ hL).symm)), u, H, χ, hH⟩, rfl⟩`.
-/
theorem exists_riemannData {S : Scheme.{0}} {P : PPAS S} {L : LB P.A.left} (hT : IsTheta P L) (y : Sp ℂ ⟶ S) :
    ∃ d : P.RiemannData y, d.L = L.pull d.φ := by
  obtain ⟨hI, hrig, hsym, hamp, hk, hc⟩ := hT
  have h := isGrpPullback_pullback P.A y
  have hL := pull_isLB hI (Limits.pullback.fst P.A.hom y)
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL hL).1 rfl
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := y (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  let Q' : Out.PolAV (Sp ℂ) := ⟨(Over.pullback y).obj P.A,
    PolPull.isAbelianScheme_of_isGrpPullback P.isAb h, P.g,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim, _, hL,
    PolBaseChange.rigidified_pull h hrig, PolBaseChange.sym_pull h hsym,
    relAmple_pull h.1 hI hL ((isGen_iff w).1 hw) U hU
      (fun z => by rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]) hamp,
    kTriv_pull h hI hL ((isGen_iff w).1 hw) hk⟩
  obtain ⟨rig, hr⟩ := Q'.rigid
  obtain ⟨u, H, χ, -, hH, -⟩ := thetaUnifAV_all Q' rig hr
  exact ⟨⟨Q'.A, _, h, Q'.L, hL, (congrArg _ hc).trans ((PPAS.pull_sqMap_lam h _).trans
    (congrArg (CechPic.lam · _ _) (CechPic.cls_pull hI _ hL).symm)), u, H, χ, hH⟩, rfl⟩

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `LiePull.exists_pushEquiv d.isPull (𝟙_ (Over (Sp ℂ))) y (Category.id_comp _).symm`. Take `⟨t1, t2⟩` from `UnifTangent.riemannData_tangent S P y d`. Establish `hG : ∀ z, (Φ.symm (e z)).left ≫ d.φ = (e z).left` using `fun z => by`. Rewrite using `[← hΦ, MulEquiv.apply_symm_apply]`. Establish `hGhol : IsHolTo Set.univ fun z => (Φ.symm (e z)).left`.

Use `HolTorsion.isHolTo_of_isPullback d.isPull.1 ?_ ?_` and prove the remaining obligations. Conclude with `HolTorsion.isHolTo_congr hhol fun z _ => hG z`. Conclude with `HolTorsion.isHolTo_congr (ExpCompare.isHolTo_const (𝟙 _)) fun z _ => Over.w (Φ.symm (e z))`. Take `⟨F, hF, -⟩` from `existsUnique_linear_lift_of_isHolTo d.B (PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull) d.L P.g g d.u t1 t2 (fun z => Φ.symm (e z)) (fun z w => by rw [hadd, map_mul]) hGhol`. Conclude with `⟨F, fun z => by rw [hF, hG]⟩`.
-/
theorem exists_linear {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y) {g : ℕ}
    (e : (Fin g → ℂ) → (Over.mk y ⟶ P.A)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (hhol : IsHolTo Set.univ fun z => (e z).left) :
    ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, (d.u.ex (F z)).left ≫ d.φ = (e z).left := by
  obtain ⟨Φ, hΦ⟩ := LiePull.exists_pushEquiv d.isPull (𝟙_ (Over (Sp ℂ))) y (Category.id_comp _).symm
  obtain ⟨t1, t2⟩ := UnifTangent.riemannData_tangent S P y d
  have hG : ∀ z, (Φ.symm (e z)).left ≫ d.φ = (e z).left := fun z => by
    rw [← hΦ, MulEquiv.apply_symm_apply]
  have hGhol : IsHolTo Set.univ fun z => (Φ.symm (e z)).left := by
    refine HolTorsion.isHolTo_of_isPullback d.isPull.1 ?_ ?_
    · exact HolTorsion.isHolTo_congr hhol fun z _ => hG z
    · exact HolTorsion.isHolTo_congr (ExpCompare.isHolTo_const (𝟙 _)) fun z _ => Over.w (Φ.symm (e z))
  obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo d.B
    (PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull) d.L P.g g d.u t1 t2 (fun z => Φ.symm (e z))
    (fun z w => by rw [hadd, map_mul]) hGhol
  exact ⟨F, fun z => by rw [hF, hG]⟩

/- English proof (translation)
Establish `h₁` using `(d.u.hol (d.φ ⁻¹ᵁ W') 0).1`. Rewrite `h` using `[← d.ex_zero]`. Establish `e : d.fn W' (resG _ hle f) =ᶠ[𝓝 0] d.fn W f` using `by filter_upwards [h₁.mem_nhds h] with z hz`. Conclude with `Points.valR_res _ hle hz f`. Use function extensionality and compare the values at `a`.

Simplify using `only [PPAS.RiemannData.cov, e.fderiv_eq]`.
-/
theorem cov_res {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y) {W W' : P.A.left.Opens}
    (hle : W' ≤ W) (f : Γ(P.A.left, W)) (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W') :
    d.cov W' (resG _ hle f) = d.cov W f := by
  have h₁ := (d.u.hol (d.φ ⁻¹ᵁ W') 0).1
  rw [← d.ex_zero] at h
  have e : d.fn W' (resG _ hle f) =ᶠ[𝓝 0] d.fn W f := by
    filter_upwards [h₁.mem_nhds h] with z hz
    exact Points.valR_res _ hle hz f
  funext a
  simp only [PPAS.RiemannData.cov, e.fderiv_eq]

/- English proof (translation)
Establish `key` using `UnifImmersive.eq_zero_of_cov S P y d (UnifTangent.riemannData_tangent S P y d)`. Establish `h1 : ∀ (W' : P.A.left.Opens) (f' : Γ(P.A.left, W')), ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W' → D *ᵥ star (d.cov W' f') = 0` using `fun W' f' hW' => key _ fun W f hW => by`. Establish `hi` using `PullHermitian.inf_of _ hW hW'`. Rewrite using `[← cov_res d inf_le_left f hi, ← cov_res d inf_le_right f' hi]`. Conclude with `hD _ _ _ hi`.

Use extensionality with `a b`. Establish `h2 : star (D a) = 0` using `key _ fun W f hW => by`. Use `congrArg star (congrFun (h1 W f hW) a)` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, mul_comm]`. Simplify using `using congrFun h2 b`.
-/
theorem eq_zero_of_form_cov {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)
    (D : Matrix (Fin P.g) (Fin P.g) ℂ)
    (hD : ∀ (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W →
      d.cov W f ⬝ᵥ D *ᵥ star (d.cov W f') = 0) : D = 0 := by
  have key := UnifImmersive.eq_zero_of_cov S P y d (UnifTangent.riemannData_tangent S P y d)
  have h1 : ∀ (W' : P.A.left.Opens) (f' : Γ(P.A.left, W')), ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W' →
      D *ᵥ star (d.cov W' f') = 0 := fun W' f' hW' => key _ fun W f hW => by
    have hi := PullHermitian.inf_of _ hW hW'
    rw [← cov_res d inf_le_left f hi, ← cov_res d inf_le_right f' hi]
    exact hD _ _ _ hi
  ext a b
  have h2 : star (D a) = 0 := key _ fun W f hW => by
    have := congrArg star (congrFun (h1 W f hW) a)
    simpa [mulVec, dotProduct, mul_comm] using this
  simpa using congrFun h2 b

/- English proof (translation)
Use `set K : Matrix (Fin g) (Fin g) ℂ := τ.map fun t => (t.im : ℂ) with hK'`. Use `set Q : Matrix (Fin g) (Fin g) ℂ := (τ.map Complex.im)⁻¹.map fun t => (t : ℂ) with hQ`. Establish `hKQ : K * Q = 1`. Establish `hK : K = (τ.map Complex.im).map Complex.ofRealHom`. Rewrite using `[hK', Matrix.map_map]`.

Both sides reduce to the same expression. Establish `hQ' : Q = (τ.map Complex.im)⁻¹.map Complex.ofRealHom` using `rfl`. Rewrite using `[hK, hQ', ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hτ.2.det_pos.ne'), Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hsymK : Kᵀ = K`. Rewrite using `[hK', ← Matrix.transpose_map, hτ.1]`.

Establish `hinv : M.map star * ((2 : ℂ) • K) * Mᵀ = (((1 / 2 : ℝ) : ℂ) • H)⁻¹`. Use `congrArg transpose h` as an intermediate fact. Rewrite `this` using `[HermFrame.dualGram, transpose_transpose, transpose_mul, transpose_mul, transpose_smul, hsymK, ← Matrix.mul_assoc]`. Conclude with `this`. Establish `hu : IsUnit (((1 / 2 : ℝ) : ℂ) • H).det`.

Rewrite using `[det_smul]`. Conclude with `(IsUnit.pow _ (by simp)).mul ((Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit)`. Establish `h2 : (H * M.map star * K) * Mᵀ = 1`. Use `Matrix.mul_nonsing_inv _ hu` as an intermediate fact. Rewrite `this` using `[← hinv, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`.

Simplify using `using this`. Establish `h1 : Mᵀ * (H * M.map star * K) = 1` using `mul_eq_one_comm.1 h2`. Establish `hform : Mᵀ * H * M.map star = Q`. Use `congrArg (· * Q) h1` as an intermediate fact. Simplify `this` using `only [Matrix.mul_assoc, hKQ, Matrix.mul_one, Matrix.one_mul]`.

Rewrite using `[herm, ← hQ, ← hform, HermFrame.form, ← dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, PeriodChart.map_star_mulVec_star, dotProduct_mulVec z, Matrix.vecMul_transpose]`.
-/
theorem form_eq_herm {g : ℕ} {τ H M : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) (hH : H.PosDef)
    (h : M * ((2 : ℂ) • τ.map fun t => (t.im : ℂ)) * Mᴴ = HermFrame.dualGram (((1 / 2 : ℝ) : ℂ) • H))
    (z w : Fin g → ℂ) : HermFrame.form H (M *ᵥ z) (M *ᵥ w) = herm τ z w := by
  set K : Matrix (Fin g) (Fin g) ℂ := τ.map fun t => (t.im : ℂ) with hK'
  set Q : Matrix (Fin g) (Fin g) ℂ := (τ.map Complex.im)⁻¹.map fun t => (t : ℂ) with hQ
  have hKQ : K * Q = 1 := by
    have hK : K = (τ.map Complex.im).map Complex.ofRealHom := by
      rw [hK', Matrix.map_map]; rfl
    have hQ' : Q = (τ.map Complex.im)⁻¹.map Complex.ofRealHom := rfl
    rw [hK, hQ', ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hτ.2.det_pos.ne'),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hsymK : Kᵀ = K := by
    rw [hK', ← Matrix.transpose_map, hτ.1]
  have hinv : M.map star * ((2 : ℂ) • K) * Mᵀ = (((1 / 2 : ℝ) : ℂ) • H)⁻¹ := by
    have := congrArg transpose h
    rw [HermFrame.dualGram, transpose_transpose, transpose_mul, transpose_mul, transpose_smul, hsymK,
      ← Matrix.mul_assoc] at this
    exact this
  have hu : IsUnit (((1 / 2 : ℝ) : ℂ) • H).det := by
    rw [det_smul]
    exact (IsUnit.pow _ (by simp)).mul ((Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit)
  have h2 : (H * M.map star * K) * Mᵀ = 1 := by
    have := Matrix.mul_nonsing_inv _ hu
    rw [← hinv, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc] at this
    simpa using this
  have h1 : Mᵀ * (H * M.map star * K) = 1 := mul_eq_one_comm.1 h2
  have hform : Mᵀ * H * M.map star = Q := by
    have := congrArg (· * Q) h1
    simpa only [Matrix.mul_assoc, hKQ, Matrix.mul_one, Matrix.one_mul] using this
  rw [herm, ← hQ, ← hform, HermFrame.form, ← dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    PeriodChart.map_star_mulVec_star, dotProduct_mulVec z, Matrix.vecMul_transpose]

/- English proof (translation)
Take `⟨G, hG, hG'⟩` from `exists_differentiable_cexp_eq hr h0`. Use `choose! a ha ha' using hj`. Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Use `⟨fun l z => (2 * Real.pi * Complex.I)⁻¹ * (Complex.log (a l) + Real.pi * herm τ z (per τ l) + G z - G (z + per τ l)), fun l hl => ⟨?_, fun z => ?_⟩, fun l _ l' _ z => ?_⟩` and prove the remaining obligations. Establish `: Differentiable ℂ fun z => herm τ z (per τ l)`.

Simplify using `only [herm, dotProduct, vecMul]`. Use `fun_prop`. Use `fun_prop`. Rewrite using `[mul_inv_cancel_left₀ hne, Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_log (ha l hl), hG', hG', eq_div_iff (h0 _), ha' l hl]`. Establish `hadd : ∀ u v w, herm τ (u + v) w = herm τ u w + herm τ v w` using `fun u v w => by`.

Simplify using `only [herm, Matrix.add_vecMul, add_dotProduct]`. Establish `e1` using `FlatFibre.riem_flatOf τ hτ.1 (per τ l) (per τ l')`. Rewrite `e1` using `[(flatOf_per_inv τ hτ.2).1, (flatOf_per_inv τ hτ.2).1]`. Establish `e2 : herm τ (per τ l') (per τ l) = star (herm τ (per τ l) (per τ l'))`. Establish `s : ((τ.map Complex.im)⁻¹)ᵀ = (τ.map Complex.im)⁻¹` using `(hτ.1.map Complex.im).inv`.

Simplify using `only [herm, dotProduct, vecMul, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, Pi.star_apply, star_star, map_apply, Complex.star_def, Complex.conj_ofReal, map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← congrFun (congrFun s a) b, transpose_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e3` using `Complex.sub_conj (herm τ (per τ l) (per τ l'))`. Use `beta_reduce`. Rewrite using `[e1, hadd, hadd, e2, add_right_comm z (per τ l') (per τ l), Complex.star_def]`. Clear the denominators using the available nonvanishing facts. Move the coercions through the operations in `at e3 ⊢`.

Take the linear combination `-Real.pi * e3`.
-/
theorem exists_log {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) (j : Fl g → (Fin g → ℂ) → ℂ)
    (r : (Fin g → ℂ) → ℂ) (hr : Differentiable ℂ r) (h0 : ∀ z, r z ≠ 0)
    (hj : ∀ l ∈ stdLat g, ∃ a : ℂ, a ≠ 0 ∧ ∀ z, j l z * r (z + per τ l) =
      a * Complex.exp (Real.pi * herm τ z (per τ l)) * r z) :
    ∃ f : Fl g → (Fin g → ℂ) → ℂ,
      (∀ l ∈ stdLat g, Differentiable ℂ (f l) ∧
        ∀ z, j l z = Complex.exp (2 * Real.pi * Complex.I * f l z)) ∧
      ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ z,
        f l (z + per τ l') + f l' z - f l' (z + per τ l) - f l z = (riem l l' : ℂ) := by
  obtain ⟨G, hG, hG'⟩ := exists_differentiable_cexp_eq hr h0
  choose! a ha ha' using hj
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  refine ⟨fun l z => (2 * Real.pi * Complex.I)⁻¹ *
    (Complex.log (a l) + Real.pi * herm τ z (per τ l) + G z - G (z + per τ l)), fun l hl => ⟨?_, fun z => ?_⟩,
    fun l _ l' _ z => ?_⟩
  · have : Differentiable ℂ fun z => herm τ z (per τ l) := by
      simp only [herm, dotProduct, vecMul]
      fun_prop
    fun_prop
  · rw [mul_inv_cancel_left₀ hne, Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_log (ha l hl),
      hG', hG', eq_div_iff (h0 _), ha' l hl]
  · have hadd : ∀ u v w, herm τ (u + v) w = herm τ u w + herm τ v w := fun u v w => by
      simp only [herm, Matrix.add_vecMul, add_dotProduct]
    have e1 := FlatFibre.riem_flatOf τ hτ.1 (per τ l) (per τ l')
    rw [(flatOf_per_inv τ hτ.2).1, (flatOf_per_inv τ hτ.2).1] at e1
    have e2 : herm τ (per τ l') (per τ l) = star (herm τ (per τ l) (per τ l')) := by
      have s : ((τ.map Complex.im)⁻¹)ᵀ = (τ.map Complex.im)⁻¹ := (hτ.1.map Complex.im).inv
      simp only [herm, dotProduct, vecMul, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, Pi.star_apply,
        star_star, map_apply, Complex.star_def, Complex.conj_ofReal, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← congrFun (congrFun s a) b, transpose_apply]
      ring
    have e3 := Complex.sub_conj (herm τ (per τ l) (per τ l'))
    beta_reduce
    rw [e1, hadd, hadd, e2, add_right_comm z (per τ l') (per τ l), Complex.star_def]
    field_simp
    push_cast at e3 ⊢
    linear_combination -Real.pi * e3

/- English proof (translation)
Establish `hFd : Differentiable ℂ F` using `(LinearMap.toContinuousLinearMap F).differentiable`. Establish `hw` using `fun z i => PullHermitian.wchart_of (u.ex (F z)).left L φ i`. Take `⟨r, hr, hrφ⟩` from `PullHermitian.exists_glue (fun i : L.ι => F ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U i)}) (fun i => (u.hol _ 0).1.preimage hFd.continuous) (fun z => PullHermitian.exists_chart ((u.ex (F z)).left ≫ φ) hL) (fun i z => fr i z * (u.fr (fun _ => i) (F z))⁻¹) (fun i => (hd i).mul (((u …`. Establish `hii` using `PullHermitian.inf_of _ (hw z i hi) (hw z i' hi')`. Establish `hii'` using `PullHermitian.inf_of ((u.ex (F z)).left ≫ φ) hi hi'`.

Establish `h2` using `u.fr_compat (fun _ => i) (fun _ => i') (F z) hii`. Establish `h3` using `(PullHermitian.valAt'_eq_unitVal _ hii _).trans (congrArg Units.val (PullHermitian.unitVal_linComb (u.ex (F z)).left L φ 1 i i' hii hii'))`. Rewrite `h3` using `[zpow_one]`. Use `replace h2 := h2.trans (congrArg (· * _) h3)`. Rewrite using `[hc i i' z hi hi', h2, PullHermitian.valAt'_eq_unitVal _ hii']`.

Use `u.fr_ne _ _ (hw z i' hi')` as an intermediate fact. Use the proof step `field_simp)`. Use `⟨r, hr, fun i z hi => ?_⟩` and prove the remaining obligations. Rewrite using `[hrφ i z hi, inv_mul_cancel_right₀ (u.fr_ne _ _ (hw z i hi))]`.
-/
theorem exists_ratio {A : Over (Sp ℂ)} [GrpObj A] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : A.left ⟶ X)
    {g g' : ℕ} (u : HolUnif A (L.pull φ) g') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (fr : L.ι → (Fin g → ℂ) → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U i})
    (hc : ∀ i i' z, ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U i' →
      fr i z = valAt' ((u.ex (F z)).left ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * fr i' z) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ ∀ i z, ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U i →
      fr i z = r z * u.fr (fun _ => i) (F z) := by
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have hw := fun z i => PullHermitian.wchart_of (u.ex (F z)).left L φ i
  obtain ⟨r, hr, hrφ⟩ := PullHermitian.exists_glue
    (fun i : L.ι => F ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U i)})
    (fun i => (u.hol _ 0).1.preimage hFd.continuous)
    (fun z => PullHermitian.exists_chart ((u.ex (F z)).left ≫ φ) hL)
    (fun i z => fr i z * (u.fr (fun _ => i) (F z))⁻¹)
    (fun i => (hd i).mul (((u.fr_hol fun _ => i).comp hFd.differentiableOn fun z hz => hw z i hz).inv
      fun z hz => u.fr_ne _ _ (hw z i hz)))
    (fun i i' z hi hi' => by
      have hii := PullHermitian.inf_of _ (hw z i hi) (hw z i' hi')
      have hii' := PullHermitian.inf_of ((u.ex (F z)).left ≫ φ) hi hi'
      have h2 := u.fr_compat (fun _ => i) (fun _ => i') (F z) hii
      have h3 := (PullHermitian.valAt'_eq_unitVal _ hii _).trans (congrArg Units.val
        (PullHermitian.unitVal_linComb (u.ex (F z)).left L φ 1 i i' hii hii'))
      rw [zpow_one] at h3
      replace h2 := h2.trans (congrArg (· * _) h3)
      rw [hc i i' z hi hi', h2, PullHermitian.valAt'_eq_unitVal _ hii']
      have := u.fr_ne _ _ (hw z i' hi')
      field_simp)
  refine ⟨r, hr, fun i z hi => ?_⟩
  rw [hrφ i z hi, inv_mul_cancel_right₀ (u.fr_ne _ _ (hw z i hi))]

/- English proof (translation)
Introduce `k _ S p _ P h hh L hT σ c τ ex j m ⟨hτ, hhol, hb⟩ ⟨fr, hfr⟩ _ b hbt`. Take `⟨hover, hmul, -, hker, hmet⟩` from `hb b hbt`. Establish `hS` using `hτ.2.2 b hbt`. Use `set s := c.e.symm b with hs`. Take `⟨d, hdL⟩` from `exists_riemannData hT s.1`.

Establish `hι : Differentiable ℂ fun z : Fin P.g → ℂ => ((b, z) : Pt (V 1) P.g)` using `by fun_prop`. Establish `hcov : ∀ z : Fin P.g → ℂ, ((b, z) : Pt (V 1) P.g) ∈ cov c.e.target P.g` using `fun z => ⟨hbt, trivial⟩`. Take `⟨F, hF⟩` from `exists_linear d (fun z => Over.homMk (ex (b, z)).1 (hover z)) (fun z w => Over.OverMorphism.ext (hmul z w _ _ rfl rfl).symm) fun U f => by`. Take `⟨h1, h2⟩` from `hhol U f`. Use `⟨?_, h2.comp hι.differentiableOn fun z hz => ⟨hcov z, hz.2⟩⟩` and prove the remaining obligations.

Conclude with `(Set.ext fun z => ⟨fun hz => And.intro trivial hz.2, fun hz => And.intro (hcov z) hz.2⟩ : (fun z : Fin P.g → ℂ => ((b, z) : Pt (V 1) P.g)) ⁻¹' {a ∈ cov c.e.target P.g | ⊤ ≤ (ex a).1 ⁻¹ᵁ U} = {z ∈ univ | ⊤ ≤ (ex (b, z)).1 ⁻¹ᵁ U}) ▸ h1.preimage hι.continuous`. Use `replace hF : ∀ z, (d.u.ex (F z)).left ≫ d.φ = (ex (b, z)).1 := hF`. Use `set M := LinearMap.toMatrix' F with hM`. Establish `chain : ∀ (W : P.A.left.Opens) (q : Γ(P.A.left, W)), ⊤ ≤ (s.1 ≫ unitSec P.A) ⁻¹ᵁ W → cot ex W q b = d.cov W q ᵥ* M`. Introduce `W q hW`.

Establish `e1 : (fun z => ev (P.A.hom ≫ p) σ W q (ex (b, z))) = d.fn W q ∘ (LinearMap.toContinuousLinearMap F)`. Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap']`. Rewrite using `[PPAS.RiemannData.fn, hF]`. Both sides reduce to the same expression.

Establish `h1 : HasFDerivAt (d.fn W q) (fderiv ℂ (d.fn W q) 0) ((LinearMap.toContinuousLinearMap F) 0)`. Rewrite using `[map_zero]`. Conclude with `(d.differentiableAt_fn q hW).hasFDerivAt`. Establish `hd` using `h1.comp 0 (LinearMap.toContinuousLinearMap F).hasFDerivAt`. Use function extensionality and compare the values at `a`.

Rewrite using `[cot, e1, hd.fderiv, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', PeriodChart.clm_apply_eq_sum, Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[PPAS.RiemannData.cov, hM, LinearMap.toMatrix'_apply, mul_comm]`. Establish `hD` using `eq_zero_of_form_cov d (M * ((2 : ℂ) • imPart τ b) * Mᴴ - HermFrame.dualGram (((1 / 2 : ℝ) : ℂ) • d.H)) fun W f f' hW => by`. Establish `e1` using `hmet _ W le_rfl f f' hW`.

Rewrite `e1` using `[(hh σ s).2 d _ W le_rfl f f' hW, chain W f hW, chain W f' hW, HermFrame.form, HermFrame.form, Matrix.star_vecMul]`. Rewrite using `[sub_mulVec, dotProduct_sub, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (d.cov W f) M, sub_self]`. Establish `hform : ∀ z w, HermFrame.form d.H (F z) (F w) = herm (τ b) z w` using `fun z w => by`. Rewrite using `[← LinearMap.toMatrix'_mulVec F z, ← LinearMap.toMatrix'_mulVec F w]`. Conclude with `form_eq_herm hS d.posDef (sub_eq_zero.1 hD) z w`.

Establish `hlat : ∀ l ∈ stdLat P.g, F (per (τ b) l) ∈ d.u.Λ` using `fun l hl => by`. Use `(d.u.ker _).1 (Eq.trans (Over.OverMorphism.ext (d.isPull.1.hom_ext ?_ ?_)) ((d.u.ker 0).2 (zero_mem _)))` and prove the remaining obligations. Rewrite using `[hF, d.ex_zero]`. Conclude with `(hker _).2 ⟨l, hl, rfl⟩`. Rewrite using `[Over.w, Over.w]`.

Take `⟨B, φ, hP, L', hL', hpol, u, H, χ, hAH⟩` from `d`. Take `rfl : L' = L.B.pull φ` from `hdL`. Simplify using `only at hF hform hlat`. Take `⟨r, hr, hrφ⟩` from `exists_ratio L.isLB φ u F (fun i z => fr i (b, z)) (fun i => (hfr i).1.comp hι.differentiableOn fun z hz => ⟨hcov z, by`. Establish `hz' : ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.B.U i` using `hz`.

Rewrite using `[hF] at hz'⟩)` and apply the resulting hypothesis. Use the proof step `(fun i i' z hi hi' => by`. Rewrite `hi`, `hi'`, the goal using `[hF]`. Conclude with `((hfr i).2 _ (hcov z) hi).2.1 i' hi')`. Establish `hr0 : ∀ z, r z ≠ 0` using `fun z => by`.

Take `⟨i, hi⟩` from `PullHermitian.exists_chart ((u.ex (F z)).left ≫ φ) L.isLB`. Conclude with `left_ne_zero_of_mul (hrφ i z hi ▸ ((hfr i).2 _ (hcov z) (by rwa [hF] at hi)).1)`. Use `exists_log hS (fun l z => j l (b, z)) r hr hr0 fun l hl => ?_` and prove the remaining obligations. Use `⟨χ ⟨_, hlat l hl⟩ * Complex.exp (Real.pi / 2 * herm (τ b) (per (τ b) l) (per (τ b) l)), mul_ne_zero (fun e => by simpa [e] using hAH.2.2.1 ⟨_, hlat l hl⟩) (Complex.exp_ne_zero _), fun z => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `PullHermitian.exists_chart ((u.ex (F z)).left ≫ φ) L.isLB`.

Establish `hper : u.ex (F (z + per (τ b) l)) = u.ex (F z)`. Rewrite using `[map_add, u.ex_add, (u.ker _).2 (hlat l hl), _root_.mul_one]`. Establish `hi' : ⊤ ≤ ((u.ex (F (z + per (τ b) l))).left ≫ φ) ⁻¹ᵁ L.B.U i` using `by rwa [hper]`. Establish `h1` using `hAH.2.2.2 ⟨_, hlat l hl⟩ (fun _ => i) (F z) (PullHermitian.wchart_of _ L.B φ i hi)`. Establish `h2 : fr i (b, z) = j l (b, z) * fr i (b, z + per (τ b) l)` using `((hfr i).2 _ (hcov z) (by rwa [hF] at hi)).2.2.2 l hl`.

Establish `n` using `u.fr_ne (fun _ => i) _ (PullHermitian.wchart_of _ L.B φ i hi')`. Rewrite `h2` using `[hrφ i z hi, hrφ i _ hi', h1]`. Rewrite using `[← hform, ← hform]`. Rewrite `n`, `h2` using `[map_add]`. Use `mul_right_cancel₀ n ?_` and prove the remaining obligations.

Simplify using `only [HermFrame.form, Complex.exp_add] at h2 ⊢`. Take the linear combination `-h2`.
-/
theorem inducesPolarisation : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p →
    ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ L : HermLB (P.A.hom ≫ p),
    IsTheta P L.B → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
    (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ),
    IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m →
    InducesPolarisation c.e.target τ (stdLat P.g) j := by
  intro k _ S p _ P h hh L hT σ c τ ex j m ⟨hτ, hhol, hb⟩ ⟨fr, hfr⟩ _ b hbt
  obtain ⟨hover, hmul, -, hker, hmet⟩ := hb b hbt
  have hS := hτ.2.2 b hbt
  set s := c.e.symm b with hs
  obtain ⟨d, hdL⟩ := exists_riemannData hT s.1
  have hι : Differentiable ℂ fun z : Fin P.g → ℂ => ((b, z) : Pt (V 1) P.g) := by fun_prop
  have hcov : ∀ z : Fin P.g → ℂ, ((b, z) : Pt (V 1) P.g) ∈ cov c.e.target P.g := fun z => ⟨hbt, trivial⟩
  obtain ⟨F, hF⟩ := exists_linear d (fun z => Over.homMk (ex (b, z)).1 (hover z))
    (fun z w => Over.OverMorphism.ext (hmul z w _ _ rfl rfl).symm) fun U f => by
      obtain ⟨h1, h2⟩ := hhol U f
      refine ⟨?_, h2.comp hι.differentiableOn fun z hz => ⟨hcov z, hz.2⟩⟩
      exact (Set.ext fun z => ⟨fun hz => And.intro trivial hz.2, fun hz => And.intro (hcov z) hz.2⟩ :
        (fun z : Fin P.g → ℂ => ((b, z) : Pt (V 1) P.g)) ⁻¹' {a ∈ cov c.e.target P.g | ⊤ ≤ (ex a).1 ⁻¹ᵁ U} =
          {z ∈ univ | ⊤ ≤ (ex (b, z)).1 ⁻¹ᵁ U}) ▸ h1.preimage hι.continuous
  replace hF : ∀ z, (d.u.ex (F z)).left ≫ d.φ = (ex (b, z)).1 := hF
  set M := LinearMap.toMatrix' F with hM
  have chain : ∀ (W : P.A.left.Opens) (q : Γ(P.A.left, W)), ⊤ ≤ (s.1 ≫ unitSec P.A) ⁻¹ᵁ W →
      cot ex W q b = d.cov W q ᵥ* M := by
    intro W q hW
    have e1 : (fun z => ev (P.A.hom ≫ p) σ W q (ex (b, z))) =
        d.fn W q ∘ (LinearMap.toContinuousLinearMap F) := by
      funext z
      simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
      rw [PPAS.RiemannData.fn, hF]
      rfl
    have h1 : HasFDerivAt (d.fn W q) (fderiv ℂ (d.fn W q) 0) ((LinearMap.toContinuousLinearMap F) 0) := by
      rw [map_zero]
      exact (d.differentiableAt_fn q hW).hasFDerivAt
    have hd := h1.comp 0 (LinearMap.toContinuousLinearMap F).hasFDerivAt
    funext a
    rw [cot, e1, hd.fderiv, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      PeriodChart.clm_apply_eq_sum, Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [PPAS.RiemannData.cov, hM, LinearMap.toMatrix'_apply, mul_comm]
  have hD := eq_zero_of_form_cov d (M * ((2 : ℂ) • imPart τ b) * Mᴴ -
      HermFrame.dualGram (((1 / 2 : ℝ) : ℂ) • d.H)) fun W f f' hW => by
    have e1 := hmet _ W le_rfl f f' hW
    rw [(hh σ s).2 d _ W le_rfl f f' hW, chain W f hW, chain W f' hW, HermFrame.form, HermFrame.form,
      Matrix.star_vecMul] at e1
    rw [sub_mulVec, dotProduct_sub, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (d.cov W f) M, sub_self]
  have hform : ∀ z w, HermFrame.form d.H (F z) (F w) = herm (τ b) z w := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec F z, ← LinearMap.toMatrix'_mulVec F w]
    exact form_eq_herm hS d.posDef (sub_eq_zero.1 hD) z w
  have hlat : ∀ l ∈ stdLat P.g, F (per (τ b) l) ∈ d.u.Λ := fun l hl => by
    refine (d.u.ker _).1 (Eq.trans (Over.OverMorphism.ext (d.isPull.1.hom_ext ?_ ?_))
      ((d.u.ker 0).2 (zero_mem _)))
    · rw [hF, d.ex_zero]
      exact (hker _).2 ⟨l, hl, rfl⟩
    · rw [Over.w, Over.w]
  obtain ⟨B, φ, hP, L', hL', hpol, u, H, χ, hAH⟩ := d
  obtain rfl : L' = L.B.pull φ := hdL
  simp only at hF hform hlat
  obtain ⟨r, hr, hrφ⟩ := exists_ratio L.isLB φ u F (fun i z => fr i (b, z))
    (fun i => (hfr i).1.comp hι.differentiableOn fun z hz => ⟨hcov z, by
      have hz' : ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.B.U i := hz
      rwa [hF] at hz'⟩)
    (fun i i' z hi hi' => by
      rw [hF] at hi hi' ⊢
      exact ((hfr i).2 _ (hcov z) hi).2.1 i' hi')
  have hr0 : ∀ z, r z ≠ 0 := fun z => by
    obtain ⟨i, hi⟩ := PullHermitian.exists_chart ((u.ex (F z)).left ≫ φ) L.isLB
    exact left_ne_zero_of_mul (hrφ i z hi ▸ ((hfr i).2 _ (hcov z) (by rwa [hF] at hi)).1)
  refine exists_log hS (fun l z => j l (b, z)) r hr hr0 fun l hl => ?_
  refine ⟨χ ⟨_, hlat l hl⟩ * Complex.exp (Real.pi / 2 * herm (τ b) (per (τ b) l) (per (τ b) l)),
    mul_ne_zero (fun e => by simpa [e] using hAH.2.2.1 ⟨_, hlat l hl⟩) (Complex.exp_ne_zero _), fun z => ?_⟩
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart ((u.ex (F z)).left ≫ φ) L.isLB
  have hper : u.ex (F (z + per (τ b) l)) = u.ex (F z) := by
    rw [map_add, u.ex_add, (u.ker _).2 (hlat l hl), _root_.mul_one]
  have hi' : ⊤ ≤ ((u.ex (F (z + per (τ b) l))).left ≫ φ) ⁻¹ᵁ L.B.U i := by rwa [hper]
  have h1 := hAH.2.2.2 ⟨_, hlat l hl⟩ (fun _ => i) (F z) (PullHermitian.wchart_of _ L.B φ i hi)
  have h2 : fr i (b, z) = j l (b, z) * fr i (b, z + per (τ b) l) :=
    ((hfr i).2 _ (hcov z) (by rwa [hF] at hi)).2.2.2 l hl
  have n := u.fr_ne (fun _ => i) _ (PullHermitian.wchart_of _ L.B φ i hi')
  rw [hrφ i z hi, hrφ i _ hi', h1] at h2
  rw [← hform, ← hform]
  rw [map_add] at n h2
  refine mul_right_cancel₀ n ?_
  simp only [HermFrame.form, Complex.exp_add] at h2 ⊢
  linear_combination -h2

end GlobalTheory.ThetaPol
