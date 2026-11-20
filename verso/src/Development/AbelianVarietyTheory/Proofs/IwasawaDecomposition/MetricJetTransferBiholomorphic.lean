import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Filter Topology Matrix
open scoped ContDiff

namespace GlobalTheory.ChernReg

/- English proof (translation)
Establish `hs : ∀ l, DifferentiableAt ℝ (fun v => ∑ k, x k v * B k l v) z` using `fun l => DifferentiableAt.fun_sum fun k _ => (hx k).mul (hB k l)`. Simplify using `only [dotProduct, vecMul, Matrix.of_apply]`. Rewrite using `[GlobalTheory.del_sum (A := fun l v => (∑ k, x k v * B k l v) * y l v) (fun l _ => (hs l).mul (hy l)), ContinuousLinearMap.sum_apply, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.del_mul (hs l) (hy l), GlobalTheory.del_sum (A := fun k v => x k v * B k l v) (fun k _ => (hx k).mul (hB k l)), ContinuousLinearMap.sum_apply]`.

Simplify using `only [GlobalTheory.del_mul (hx _) (hB _ _)]`. Rewrite using `[Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem del_form_of_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {d : ℕ} {z w : E} (x y : Fin d → E → ℂ) (B : Fin d → Fin d → E → ℂ)
    (hx : ∀ k, DifferentiableAt ℝ (x k) z) (hB : ∀ k l, DifferentiableAt ℝ (B k l) z)
    (hy : ∀ l, DifferentiableAt ℝ (y l) z) :
    GlobalTheory.del (fun v => ((fun k => x k v) ᵥ* Matrix.of (fun k l => B k l v)) ⬝ᵥ (fun l => y l v)) z w =
      ((fun k => GlobalTheory.del (x k) z w) ᵥ* Matrix.of (fun k l => B k l z)) ⬝ᵥ (fun l => y l z)
      + ((fun k => x k z) ᵥ* Matrix.of (fun k l => GlobalTheory.del (B k l) z w)) ⬝ᵥ (fun l => y l z)
      + ((fun k => x k z) ᵥ* Matrix.of (fun k l => B k l z)) ⬝ᵥ (fun l => GlobalTheory.del (y l) z w) := by
  have hs : ∀ l, DifferentiableAt ℝ (fun v => ∑ k, x k v * B k l v) z := fun l =>
    DifferentiableAt.fun_sum fun k _ => (hx k).mul (hB k l)
  simp only [dotProduct, vecMul, Matrix.of_apply]
  rw [GlobalTheory.del_sum (A := fun l v => (∑ k, x k v * B k l v) * y l v) (fun l _ => (hs l).mul (hy l)), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [GlobalTheory.del_mul (hs l) (hy l), GlobalTheory.del_sum (A := fun k v => x k v * B k l v) (fun k _ => (hx k).mul (hB k l)),
    ContinuousLinearMap.sum_apply]
  simp only [GlobalTheory.del_mul (hx _) (hB _ _)]
  rw [Finset.sum_add_distrib]
  ring

open ReciprocityTheory.L2DbarEstimates in

/- English proof (translation)
Establish `h1 : u ᵥ* A = u' ᵥ* A` using `funext fun i => by`. Use `h (Pi.single i 1)` as an intermediate fact. Simplify `this` using `[dotProduct_single]`. Establish `h2` using `congrArg (fun w => w ᵥ* A⁻¹) h1`. Simplify `h2` using `[vecMul_vecMul, mul_nonsing_inv _ hA]`.
-/
theorem vecMul_eq_of_dotProduct {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : IsUnit A.det)
    {u u' : Fin d → ℂ} (h : ∀ s, (u ᵥ* A) ⬝ᵥ s = (u' ᵥ* A) ⬝ᵥ s) : u = u' := by
  have h1 : u ᵥ* A = u' ᵥ* A := funext fun i => by
    have := h (Pi.single i 1)
    simpa [dotProduct_single] using this
  have h2 := congrArg (fun w => w ᵥ* A⁻¹) h1
  simpa [vecMul_vecMul, mul_nonsing_inv _ hA] using h2

open ReciprocityTheory.L2DbarEstimates in

/- English proof (translation)
Establish `hUz : U ∈ 𝓝 z` using `hU.mem_nhds hz`. Establish `hτ2 : ContDiffAt ℂ 2 τ z` using `(GlobalTheory.SCV.contDiffOn_of_differentiableOn hU hτ 2).contDiffAt hUz`. Establish `hτ1 : DifferentiableAt ℂ τ z` using `hτ2.differentiableAt two_ne_zero`. Establish `hJd : DifferentiableAt ℂ (fderiv ℂ τ) z` using `(hτ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero`. Establish `hpd : ∀ η : V d, DifferentiableAt ℂ (fun v => fderiv ℂ τ v η) z` using `fun η => hJd.clm_apply (differentiableAt_const _)`.

Establish `hpf : ∀ η : V d, fderiv ℂ (fun v => fderiv ℂ τ v η) z ξ = fderiv ℂ (fderiv ℂ τ) z ξ η`. Introduce `η`. Rewrite using `[fderiv_clm_apply hJd (differentiableAt_const _)]`. Simplify using the standard rewrite rules. Establish `hbz : ∀ k l, DifferentiableAt ℝ (fun v => b v k l) z` using `fun k l => ((hb k l).contDiffAt hUz).differentiableAt (by simp)`.

Establish `hτz' : τ z ∈ U'` using `hmap hz`. Establish `hb'z : ∀ k l, DifferentiableAt ℝ (fun v => b' v k l) (τ z)` using `fun k l => ((hb' k l).contDiffAt (hU'.mem_nhds hτz')).differentiableAt (by simp)`. Set `P : Fin d → (V d →L[ℂ] ℂ)` to `fun k => EuclideanSpace.proj k`. Establish `hP : ∀ (k : Fin d) (x : V d), P k x = x.ofLp k` using `fun _ _ => rfl`. Establish `hxd : ∀ (η : V d) (k : Fin d), DifferentiableAt ℂ (fun v => (fderiv ℂ τ v η).ofLp k) z` using `fun η k => (P k).differentiableAt.comp z (hpd η)`.

Establish `hxdel : ∀ k, GlobalTheory.del (fun v => (fderiv ℂ τ v ξ).ofLp k) z ξ = (fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp k`. Introduce `k`. Use `GlobalTheory.del_clm_comp (P k) ((hpd ξ).restrictScalars ℝ) ξ` as an intermediate fact. Simplify using `only [hP] at this`. Rewrite using `[this, GlobalTheory.del_eq_fderiv (hpd ξ), hpf]`.

Establish `hydel : ∀ (ζ : V d) l, GlobalTheory.del (fun v => star ((fderiv ℂ τ v ζ).ofLp l)) z ξ = 0`. Introduce `ζ l`. Use `GlobalTheory.del_conj (fun v => (fderiv ℂ τ v ζ).ofLp l) z ξ` as an intermediate fact. Rewrite `this` using `[GlobalTheory.dbar_eq_zero (hxd ζ l)]`. Simplify using `using this`.

Establish `key : ∀ ζ : V d, ((fderiv ℂ τ z (christoffel b z ξ)).ofLp ᵥ* b' (τ z)) ⬝ᵥ star (fderiv ℂ τ z ζ).ofLp = ((christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp ᵥ* b' (τ z)) ⬝ᵥ star (fderiv ℂ τ z ζ).ofLp`. Introduce `ζ`. Establish `hev : (fun v => (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp) =ᶠ[𝓝 z] (fun v => ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp)` using `Filter.eventually_of_mem hUz fun v hv => hrel v hv ξ ζ`. Establish `h1` using `congrArg (fun L => L ξ) (GlobalTheory.del_congr hev)`. Establish `hL : GlobalTheory.del (fun v => (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp) z ξ = _` using `del_form_of_differentiable (w := ξ) (fun k _ => ξ.ofLp k) (fun l _ => star (ζ.ofLp l)) (fun k l v => b v k l) (fun _ => differentiableAt_const _) hbz (fun _ => differentiableAt_const _)`.

Establish `hR : GlobalTheory.del (fun v => ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) z ξ = _` using `del_form_of_differentiable (w := ξ) (fun k v => (fderiv ℂ τ v ξ).ofLp k) (fun l v => star ((fderiv ℂ τ v ζ).ofLp l)) (fun k l v => b' (τ v) k l) (fun k => (hxd ξ k).restrictScalars ℝ) (fun k l => (hb'z k l).comp z (hτ1.restrictScalars ℝ)) (fun l => ((hxd ζ l).restrictScalars ℝ).s …`. Simplify using `only at h1`. Rewrite `h1` using `[hL, hR]`. Simplify using `only [GlobalTheory.del_const, ContinuousLinearMap.zero_apply, hxdel, hydel] at h1`. Establish `hBdel : ∀ k l, GlobalTheory.del (fun v => b' (τ v) k l) z ξ = GlobalTheory.del (fun w => b' w k l) (τ z) (fderiv ℂ τ z ξ)` using `fun k l => GlobalTheory.del_comp_holo (u := fun w => b' w k l) (hb'z k l) hτ1 ξ`.

Rewrite `h1` using `[show (fun _ : Fin d => (0 : ℂ)) = 0 from rfl]`. Simplify using `only [zero_vecMul, zero_dotProduct, dotProduct_zero, zero_add, add_zero, hBdel] at h1`. Establish `h2 : (ξ.ofLp ᵥ* of fun k l => GlobalTheory.del (fun v => b v k l) z ξ) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp ᵥ* b' (τ z)) ⬝ᵥ star (fderiv ℂ τ z ζ).ofLp + ((fderiv ℂ τ z ξ).ofLp ᵥ* of fun k l => GlobalTheory.del (fun w => b' w k l) (τ z) (fderiv ℂ τ z ξ)) ⬝ᵥ star (f …` using `h1`. Rewrite `h2` using `[← chris_vecMul (hbu z hz), ← chris_vecMul (hbu' _ hτz'), hrel z hz]`. Rewrite using `[h2, WithLp.ofLp_add, add_vecMul, add_dotProduct, add_comm]`.

Establish `hinj : Function.Injective (fderiv ℂ τ z)`. Use `(injective_iff_map_eq_zero (fderiv ℂ τ z)).2 fun ζ₀ h0 => ?_` and prove the remaining obligations. Establish `hv : ∀ x : V d, (x.ofLp ᵥ* b z) ⬝ᵥ star ζ₀.ofLp = 0` using `fun x => by`. Rewrite using `[hrel z hz x ζ₀, h0]`. Simplify using the standard rewrite rules.

Establish `hm : b z *ᵥ star ζ₀.ofLp = 0` using `funext fun i => by`. Use `hv (EuclideanSpace.single i 1)` as an intermediate fact. Rewrite `this` using `[← dotProduct_mulVec]`. Simplify using `using this`. Establish `h3 : star ζ₀.ofLp = 0`.

Use `congrArg (fun w => (b z)⁻¹ *ᵥ w) hm` as an intermediate fact. Simplify `this` using `[mulVec_mulVec, nonsing_inv_mul _ (hbu z hz)]`. Establish `h4 : ζ₀.ofLp = 0` using `by simpa using h3`. Simplify using `using h4`. Establish `hsurj : Function.Surjective (fderiv ℂ τ z)` using `(LinearMap.injective_iff_surjective (f := (fderiv ℂ τ z).toLinearMap)).1 hinj`.

Establish `hfin : (fderiv ℂ τ z (christoffel b z ξ)).ofLp = (christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp`. Use `vecMul_eq_of_dotProduct (hbu' _ hτz') fun s => ?_` and prove the remaining obligations. Take `⟨ζ, hζ⟩` from `hsurj (WithLp.toLp 2 (star s))`. Use `key ζ` as an intermediate fact. Rewrite `this` using `[hζ]`.

Simplify using `using this`. Simplify `congrArg (WithLp.toLp 2) hfin` using `only [WithLp.toLp_ofLp]`.
-/
theorem chris_transform (d : ℕ) (U U' : Set (V d)) (τ : V d → V d)
    (b b' : V d → Matrix (Fin d) (Fin d) ℂ) (hU : IsOpen U) (hU' : IsOpen U')
    (hτ : DifferentiableOn ℂ τ U) (hmap : Set.MapsTo τ U U')
    (hb : ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) (hb' : ∀ k l, ContDiffOn ℝ ∞ (fun v => b' v k l) U')
    (hbu : ∀ v ∈ U, IsUnit (b v).det) (hbu' : ∀ v ∈ U', IsUnit (b' v).det)
    (hrel : ∀ v ∈ U, ∀ ξ ζ : V d, (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp =
      ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp)
    (z : V d) (hz : z ∈ U) (ξ : V d) :
    fderiv ℂ τ z (christoffel b z ξ) = christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ := by
  have hUz : U ∈ 𝓝 z := hU.mem_nhds hz
  have hτ2 : ContDiffAt ℂ 2 τ z := (GlobalTheory.SCV.contDiffOn_of_differentiableOn hU hτ 2).contDiffAt hUz
  have hτ1 : DifferentiableAt ℂ τ z := hτ2.differentiableAt two_ne_zero
  have hJd : DifferentiableAt ℂ (fderiv ℂ τ) z :=
    (hτ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hpd : ∀ η : V d, DifferentiableAt ℂ (fun v => fderiv ℂ τ v η) z := fun η =>
    hJd.clm_apply (differentiableAt_const _)
  have hpf : ∀ η : V d, fderiv ℂ (fun v => fderiv ℂ τ v η) z ξ = fderiv ℂ (fderiv ℂ τ) z ξ η := by
    intro η; rw [fderiv_clm_apply hJd (differentiableAt_const _)]; simp
  have hbz : ∀ k l, DifferentiableAt ℝ (fun v => b v k l) z := fun k l =>
    ((hb k l).contDiffAt hUz).differentiableAt (by simp)
  have hτz' : τ z ∈ U' := hmap hz
  have hb'z : ∀ k l, DifferentiableAt ℝ (fun v => b' v k l) (τ z) := fun k l =>
    ((hb' k l).contDiffAt (hU'.mem_nhds hτz')).differentiableAt (by simp)
  let P : Fin d → (V d →L[ℂ] ℂ) := fun k => EuclideanSpace.proj k
  have hP : ∀ (k : Fin d) (x : V d), P k x = x.ofLp k := fun _ _ => rfl
  have hxd : ∀ (η : V d) (k : Fin d), DifferentiableAt ℂ (fun v => (fderiv ℂ τ v η).ofLp k) z :=
    fun η k => (P k).differentiableAt.comp z (hpd η)
  have hxdel : ∀ k, GlobalTheory.del (fun v => (fderiv ℂ τ v ξ).ofLp k) z ξ =
      (fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp k := by
    intro k
    have := GlobalTheory.del_clm_comp (P k) ((hpd ξ).restrictScalars ℝ) ξ
    simp only [hP] at this
    rw [this, GlobalTheory.del_eq_fderiv (hpd ξ), hpf]
  have hydel : ∀ (ζ : V d) l, GlobalTheory.del (fun v => star ((fderiv ℂ τ v ζ).ofLp l)) z ξ = 0 := by
    intro ζ l
    have := GlobalTheory.del_conj (fun v => (fderiv ℂ τ v ζ).ofLp l) z ξ
    rw [GlobalTheory.dbar_eq_zero (hxd ζ l)] at this
    simpa using this
  have key : ∀ ζ : V d, ((fderiv ℂ τ z (christoffel b z ξ)).ofLp ᵥ* b' (τ z)) ⬝ᵥ star (fderiv ℂ τ z ζ).ofLp =
      ((christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp ᵥ* b' (τ z)) ⬝ᵥ
        star (fderiv ℂ τ z ζ).ofLp := by
    intro ζ
    have hev : (fun v => (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp) =ᶠ[𝓝 z]
        (fun v => ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) :=
      Filter.eventually_of_mem hUz fun v hv => hrel v hv ξ ζ
    have h1 := congrArg (fun L => L ξ) (GlobalTheory.del_congr hev)
    have hL : GlobalTheory.del (fun v => (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp) z ξ = _ :=
      del_form_of_differentiable (w := ξ) (fun k _ => ξ.ofLp k) (fun l _ => star (ζ.ofLp l)) (fun k l v => b v k l)
        (fun _ => differentiableAt_const _) hbz (fun _ => differentiableAt_const _)
    have hR : GlobalTheory.del (fun v => ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) z ξ
        = _ :=
      del_form_of_differentiable (w := ξ) (fun k v => (fderiv ℂ τ v ξ).ofLp k)
        (fun l v => star ((fderiv ℂ τ v ζ).ofLp l)) (fun k l v => b' (τ v) k l)
        (fun k => (hxd ξ k).restrictScalars ℝ)
        (fun k l => (hb'z k l).comp z (hτ1.restrictScalars ℝ))
        (fun l => ((hxd ζ l).restrictScalars ℝ).star)
    simp only at h1
    rw [hL, hR] at h1
    simp only [GlobalTheory.del_const, ContinuousLinearMap.zero_apply, hxdel, hydel] at h1
    have hBdel : ∀ k l, GlobalTheory.del (fun v => b' (τ v) k l) z ξ =
        GlobalTheory.del (fun w => b' w k l) (τ z) (fderiv ℂ τ z ξ) := fun k l =>
      GlobalTheory.del_comp_holo (u := fun w => b' w k l) (hb'z k l) hτ1 ξ
    rw [show (fun _ : Fin d => (0 : ℂ)) = 0 from rfl] at h1
    simp only [zero_vecMul, zero_dotProduct, dotProduct_zero, zero_add, add_zero, hBdel] at h1
    have h2 : (ξ.ofLp ᵥ* of fun k l => GlobalTheory.del (fun v => b v k l) z ξ) ⬝ᵥ star ζ.ofLp =
        ((fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp ᵥ* b' (τ z)) ⬝ᵥ star (fderiv ℂ τ z ζ).ofLp +
        ((fderiv ℂ τ z ξ).ofLp ᵥ* of fun k l => GlobalTheory.del (fun w => b' w k l) (τ z) (fderiv ℂ τ z ξ)) ⬝ᵥ
          star (fderiv ℂ τ z ζ).ofLp := h1
    rw [← chris_vecMul (hbu z hz), ← chris_vecMul (hbu' _ hτz'), hrel z hz] at h2
    rw [h2, WithLp.ofLp_add, add_vecMul, add_dotProduct, add_comm]
  have hinj : Function.Injective (fderiv ℂ τ z) := by
    refine (injective_iff_map_eq_zero (fderiv ℂ τ z)).2 fun ζ₀ h0 => ?_
    have hv : ∀ x : V d, (x.ofLp ᵥ* b z) ⬝ᵥ star ζ₀.ofLp = 0 := fun x => by
      rw [hrel z hz x ζ₀, h0]; simp
    have hm : b z *ᵥ star ζ₀.ofLp = 0 := funext fun i => by
      have := hv (EuclideanSpace.single i 1)
      rw [← dotProduct_mulVec] at this
      simpa using this
    have h3 : star ζ₀.ofLp = 0 := by
      have := congrArg (fun w => (b z)⁻¹ *ᵥ w) hm
      simpa [mulVec_mulVec, nonsing_inv_mul _ (hbu z hz)] using this
    have h4 : ζ₀.ofLp = 0 := by simpa using h3
    simpa using h4
  have hsurj : Function.Surjective (fderiv ℂ τ z) :=
    (LinearMap.injective_iff_surjective (f := (fderiv ℂ τ z).toLinearMap)).1 hinj
  have hfin : (fderiv ℂ τ z (christoffel b z ξ)).ofLp =
      (christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ).ofLp := by
    refine vecMul_eq_of_dotProduct (hbu' _ hτz') fun s => ?_
    obtain ⟨ζ, hζ⟩ := hsurj (WithLp.toLp 2 (star s))
    have := key ζ
    rw [hζ] at this
    simpa using this
  simpa only [WithLp.toLp_ofLp] using congrArg (WithLp.toLp 2) hfin

/- English proof (translation)
The claim follows from `chris_transform`.
-/
example : ∀ (d : ℕ) (U U' : Set (ReciprocityTheory.L2DbarEstimates.V d)) (τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (b b' : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → IsOpen U' → DifferentiableOn ℂ τ U → Set.MapsTo τ U U' → (∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) → (∀ k l, ContDiffOn ℝ ∞ (fun v => b' v k l) U') → (∀ v ∈ U, IsUnit (b v).det) → (∀ v ∈ U', IsUnit (b' v).det) → (∀ v ∈ U, ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) → ∀ z ∈ U, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, fderiv ℂ τ z (GlobalTheory.ChernReg.christoffel b z ξ) = GlobalTheory.ChernReg.christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ := chris_transform

end GlobalTheory.ChernReg
