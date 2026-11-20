import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.ProdExChart

/- English proof (translation)
Establish `: CompleteSpace V` using `FiniteDimensional.complete ℝ V`. Take `⟨p, hp⟩` from `LinearMap.exists_leftInverse_of_injective L.subtype (Submodule.ker_subtype L)`. Establish `hp' : ∀ y (hy : y ∈ L), (p y : V) = y` using `fun y hy => by`. Use `LinearMap.congr_fun hp ⟨y, hy⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this`.

Rewrite using `[this]`. Take `⟨g, hg⟩` from `LinearMap.exists_rightInverse_of_surjective ((M 0 : F →ₗ[ℝ] V).codRestrict L (hL 0)) (by`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `y`. Take `⟨c, hc⟩` from `h0 y y.2`.

Conclude with `⟨c, Subtype.ext hc⟩)`. Set `r : V →L[ℝ] F` to `LinearMap.toContinuousLinearMap (g ∘ₗ p)`. Set `π : V →L[ℝ] V` to `LinearMap.toContinuousLinearMap (L.subtype ∘ₗ p)`. Establish `hπ : ∀ v, π v = (p v : V)` using `fun v => rfl`. Establish `hr : ∀ v, M 0 (r v) = π v` using `fun v => congrArg Subtype.val (LinearMap.congr_fun hg (p v))`.

Set `N : P → V →L[ℝ] V` to `fun t => (M t).comp r + (1 - π)`. Establish `hN : ContDiff ℝ ∞ N` using `(hM.clm_comp contDiff_const).add contDiff_const`. Establish `hN0 : N 0 = 1`. Use extensionality with `v`. Simplify using `[N, hr]`.

Use `⟨N ⁻¹' {x | IsUnit x}, Units.isOpen.preimage hN.continuous, by simp [hN0], fun y hy hyL => ?_⟩` and prove the remaining obligations. Use `⟨fun t => r (Ring.inverse (N t) (y t)), ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨u, hu⟩` from `(show IsUnit (N t) from ht)`. Establish `h1 : ContDiffAt ℝ ∞ (fun t => Ring.inverse (N t)) t`.

Use `contDiffAt_ringInverse ℝ (n := ∞) u` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this.comp t hN.contDiffAt`. Conclude with `(r.contDiff.contDiffAt.comp t (h1.clm_apply hy.contDiffAt)).contDiffWithinAt`. Introduce `t ht`.

Establish `ht' : IsUnit (N t)` using `ht`. Use `set v := Ring.inverse (N t) (y t) with hv`. Establish `h1 : N t v = y t`. Rewrite using `[hv, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ ht']`. Both sides reduce to the same expression.

Establish `h2 : M t (r v) + (v - π v) = y t` using `h1`. Establish `h3` using `congrArg π h2`. Rewrite `h3` using `[map_add, map_sub, hπ (M t (r v)), hp' _ (hL _ _), hπ (π v), hp' (π v) (p v).2, hπ (y t), hp' _ (hyL t), sub_self, add_zero]`. Conclude with `h3`.
-/
theorem smooth_solve {P F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℝ V) (M : P → F →L[ℝ] V) (hM : ContDiff ℝ ∞ M) (hL : ∀ t c, M t c ∈ L)
    (h0 : ∀ y ∈ L, ∃ c, M 0 c = y) :
    ∃ U : Set P, IsOpen U ∧ (0 : P) ∈ U ∧ ∀ y : P → V, ContDiff ℝ ∞ y → (∀ t, y t ∈ L) →
      ∃ c : P → F, ContDiffOn ℝ ∞ c U ∧ ∀ t ∈ U, M t (c t) = y t := by
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective L.subtype (Submodule.ker_subtype L)
  have hp' : ∀ y (hy : y ∈ L), (p y : V) = y := fun y hy => by
    have := LinearMap.congr_fun hp ⟨y, hy⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [this]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    ((M 0 : F →ₗ[ℝ] V).codRestrict L (hL 0)) (by
      rw [LinearMap.range_eq_top]
      intro y
      obtain ⟨c, hc⟩ := h0 y y.2
      exact ⟨c, Subtype.ext hc⟩)
  let r : V →L[ℝ] F := LinearMap.toContinuousLinearMap (g ∘ₗ p)
  let π : V →L[ℝ] V := LinearMap.toContinuousLinearMap (L.subtype ∘ₗ p)
  have hπ : ∀ v, π v = (p v : V) := fun v => rfl
  have hr : ∀ v, M 0 (r v) = π v := fun v =>
    congrArg Subtype.val (LinearMap.congr_fun hg (p v))
  let N : P → V →L[ℝ] V := fun t => (M t).comp r + (1 - π)
  have hN : ContDiff ℝ ∞ N := (hM.clm_comp contDiff_const).add contDiff_const
  have hN0 : N 0 = 1 := by
    ext v
    simp [N, hr]
  refine ⟨N ⁻¹' {x | IsUnit x}, Units.isOpen.preimage hN.continuous, by simp [hN0], fun y hy hyL => ?_⟩
  refine ⟨fun t => r (Ring.inverse (N t) (y t)), ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu⟩ := (show IsUnit (N t) from ht)
    have h1 : ContDiffAt ℝ ∞ (fun t => Ring.inverse (N t)) t := by
      have := contDiffAt_ringInverse ℝ (n := ∞) u
      rw [hu] at this
      exact this.comp t hN.contDiffAt
    exact (r.contDiff.contDiffAt.comp t (h1.clm_apply hy.contDiffAt)).contDiffWithinAt
  · intro t ht
    have ht' : IsUnit (N t) := ht
    set v := Ring.inverse (N t) (y t) with hv
    have h1 : N t v = y t := by
      rw [hv, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ ht']; rfl
    have h2 : M t (r v) + (v - π v) = y t := h1
    have h3 := congrArg π h2
    rw [map_add, map_sub, hπ (M t (r v)), hp' _ (hL _ _), hπ (π v), hp' (π v) (p v).2, hπ (y t),
      hp' _ (hyL t), sub_self, add_zero] at h3
    exact h3

/- English proof (translation)
Set `A : Fin d → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] ℝ)` to `fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _)`. Set `B : Fin e → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] ℝ)` to `fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)`. Set `M : P → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] V)` to `fun t => ∑ j, (A j).smulRight (Z j t) + ∑ i, (B i).smulRight (Q i)`. Establish `hM : ∀ t c, M t c = ∑ j, c.1 j • Z j t + ∑ i, c.2 i • Q i` using `fun t c => by`. Simplify using `[M, A, B]`.

Establish `hsm : ContDiff ℝ ∞ M` using `(ContDiff.sum fun j _ => contDiff_const.smulRight (h3 j)).add contDiff_const`. Take `⟨U, hU, hU0, hsol⟩` from `smooth_solve L M hsm (fun t c => by`. Rewrite using `[hM]`. Conclude with `Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h1 j t)) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hQ i)))`. Use the proof step `(fun y hy => by`.

Take `⟨a, b, hab⟩` from `h0 y hy`. Conclude with `⟨(a, b), by rw [hM, hab]⟩)`. Use `⟨U, hU, hU0, fun y hy hyL => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hc'⟩` from `hsol y hy hyL`. Use `⟨fun j t => (c t).1 j, fun i t => (c t).2 i, fun j => (A j).contDiff.comp_contDiffOn hc, fun i => (B i).contDiff.comp_contDiffOn hc, fun t ht => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hM, hc' t ht]`.
-/
theorem smooth_coeffs {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d e : ℕ}
    (L : Submodule ℝ V) (Z : Fin d → P → V) (Q : Fin e → V) (h3 : ∀ j, ContDiff ℝ ∞ (Z j))
    (h1 : ∀ j t, Z j t ∈ L) (hQ : ∀ i, Q i ∈ L)
    (h0 : ∀ y ∈ L, ∃ (a : Fin d → ℝ) (b : Fin e → ℝ), y = ∑ j, a j • Z j 0 + ∑ i, b i • Q i) :
    ∃ U : Set P, IsOpen U ∧ (0 : P) ∈ U ∧ ∀ y : P → V, ContDiff ℝ ∞ y → (∀ t, y t ∈ L) →
      ∃ (a : Fin d → P → ℝ) (b : Fin e → P → ℝ), (∀ j, ContDiffOn ℝ ∞ (a j) U) ∧
        (∀ i, ContDiffOn ℝ ∞ (b i) U) ∧ ∀ t ∈ U, y t = ∑ j, a j t • Z j t + ∑ i, b i t • Q i := by
  let A : Fin d → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] ℝ) := fun j =>
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _)
  let B : Fin e → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] ℝ) := fun i =>
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)
  let M : P → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] V) := fun t =>
    ∑ j, (A j).smulRight (Z j t) + ∑ i, (B i).smulRight (Q i)
  have hM : ∀ t c, M t c = ∑ j, c.1 j • Z j t + ∑ i, c.2 i • Q i := fun t c => by
    simp [M, A, B]
  have hsm : ContDiff ℝ ∞ M :=
    (ContDiff.sum fun j _ => contDiff_const.smulRight (h3 j)).add contDiff_const
  obtain ⟨U, hU, hU0, hsol⟩ := smooth_solve L M hsm
    (fun t c => by
      rw [hM]
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h1 j t))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hQ i)))
    (fun y hy => by
      obtain ⟨a, b, hab⟩ := h0 y hy
      exact ⟨(a, b), by rw [hM, hab]⟩)
  refine ⟨U, hU, hU0, fun y hy hyL => ?_⟩
  obtain ⟨c, hc, hc'⟩ := hsol y hy hyL
  refine ⟨fun j t => (c t).1 j, fun i t => (c t).2 i, fun j => (A j).contDiff.comp_contDiffOn hc,
    fun i => (B i).contDiff.comp_contDiffOn hc, fun t ht => ?_⟩
  rw [← hM, hc' t ht]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[contDiff_infty]`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hasDerivAt_ex X t).continuousAt)`. Consider the case `succ m ih`.

Rewrite using `[Nat.cast_succ, contDiff_succ_iff_deriv]`. Use `⟨fun t => (hasDerivAt_ex X t).differentiableAt, by simp, ?_⟩` and prove the remaining obligations. Establish `hc : ContDiff ℝ m (fun t => ex X t * X)` using `(contDiff_mul.of_le (by exact_mod_cast le_top)).comp (ih.prodMk contDiff_const)`. Conclude with `contDiffOn_univ.1 ((contDiffOn_univ.2 hc).congr fun t _ => (hasDerivAt_ex X t).deriv)`.
-/
theorem contDiff_ex (X : Mat n) : ContDiff ℝ ∞ (ex X) := by
  rw [contDiff_infty]
  intro m
  induction m with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hasDerivAt_ex X t).continuousAt)
  | succ m ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_ex X t).differentiableAt, by simp, ?_⟩
    have hc : ContDiff ℝ m (fun t => ex X t * X) :=
      (contDiff_mul.of_le (by exact_mod_cast le_top)).comp (ih.prodMk contDiff_const)
    exact contDiffOn_univ.1 ((contDiffOn_univ.2 hc).congr fun t _ => (hasDerivAt_ex X t).deriv)

/- English proof (translation)
Set `T : Mat n →ₗ[ℝ] Mat n` to `{ toFun := fun A => Aᴴ map_add' := fun A B => conjTranspose_add A B map_smul' := fun c A => by simp [conjTranspose_smul] }`. Conclude with `(LinearMap.toContinuousLinearMap T).contDiff`.
-/
theorem contDiff_conjT : ContDiff ℝ ∞ (fun A : Mat n => Aᴴ) := by
  let T : Mat n →ₗ[ℝ] Mat n :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun c A => by simp [conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap T).contDiff

/- English proof (translation)
Establish `hg' : gᴴ * Hm * g = Hm` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem left_inv_of_mem {Hm g : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) :
    Hm * gᴴ * Hm * g = 1 := by
  have hg' : gᴴ * Hm * g = Hm := hg
  calc Hm * gᴴ * Hm * g = Hm * (gᴴ * Hm * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', h]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (left_inv_of_mem h hg)`.
-/
theorem inv_of_mem {Hm g : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) : g⁻¹ = Hm * gᴴ * Hm :=
  Matrix.inv_eq_left_inv (left_inv_of_mem h hg)

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (left_inv_of_mem h hg))`.
-/
theorem isUnit_of_mem {Hm g : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) : IsUnit g :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (left_inv_of_mem h hg))

/- English proof (translation)
Establish `hg' : gᴴ * Hm * g = Hm` using `hg`. Establish `hdet : IsUnit g.det` using `(Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_mem h hg)`. Establish `e2 : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Establish `e3 : (g⁻¹)ᴴ * gᴴ = 1` using `by rw [← conjTranspose_mul, e2, conjTranspose_one]`. Establish `a1 : (g⁻¹)ᴴ * Hm = Hm * g`.

Combine the equalities or inequalities in the displayed calculation. Establish `a2 : Hm * g⁻¹ = gᴴ * Hm`. Combine the equalities or inequalities in the displayed calculation. Establish `hY' : Yᴴ * Hm + Hm * Y = 0` using `hY`. Unfold `Lie`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = gᴴ * (Yᴴ * Hm + Hm * Y) * g := by`. Rewrite using `[a1, a2]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`.

Use `_ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem lie_conj {Hm g Y : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) (hY : Lie Hm Y) :
    Lie Hm (g⁻¹ * Y * g) := by
  have hg' : gᴴ * Hm * g = Hm := hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_mem h hg)
  have e2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e3 : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
  have a1 : (g⁻¹)ᴴ * Hm = Hm * g := by
    calc (g⁻¹)ᴴ * Hm = (g⁻¹)ᴴ * (gᴴ * Hm * g) := by rw [hg']
      _ = ((g⁻¹)ᴴ * gᴴ) * Hm * g := by simp only [Matrix.mul_assoc]
      _ = Hm * g := by rw [e3, Matrix.one_mul]
  have a2 : Hm * g⁻¹ = gᴴ * Hm := by
    calc Hm * g⁻¹ = (gᴴ * Hm * g) * g⁻¹ := by rw [hg']
      _ = gᴴ * Hm * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gᴴ * Hm := by rw [e2, Matrix.mul_one]
  have hY' : Yᴴ * Hm + Hm * Y = 0 := hY
  unfold Lie
  calc (g⁻¹ * Y * g)ᴴ * Hm + Hm * (g⁻¹ * Y * g)
      = gᴴ * Yᴴ * ((g⁻¹)ᴴ * Hm) + (Hm * g⁻¹) * Y * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Yᴴ * Hm + Hm * Y) * g := by
        rw [a1, a2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Unfold `ex`. Rewrite using `[← Matrix.exp_conj' g _ hg, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem ex_conj {g : Mat n} (hg : IsUnit g) (Y : Mat n) (τ : ℝ) :
    ex (g⁻¹ * Y * g) τ = g⁻¹ * ex Y τ * g := by
  unfold ex
  rw [← Matrix.exp_conj' g _ hg, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `: (fun t => (s t)⁻¹ * Y * s t) = fun t => Hm * (s t)ᴴ * Hm * Y * s t`. Use function extensionality and compare the values at `fun t => by rw [inv_of_mem h (hm t)]`. Rewrite using `[this]`. Conclude with `contDiff_mul' (contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const (contDiff_conjT.comp hs)) contDiff_const) contDiff_const) hs`.
-/
theorem contDiff_conj {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {Hm : Mat n}
    (h : Hm * Hm = 1) {s : P → Mat n} (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) (Y : Mat n) :
    ContDiff ℝ ∞ (fun t => (s t)⁻¹ * Y * s t) := by
  have : (fun t => (s t)⁻¹ * Y * s t) = fun t => Hm * (s t)ᴴ * Hm * Y * s t :=
    funext fun t => by rw [inv_of_mem h (hm t)]
  rw [this]
  exact contDiff_mul' (contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const
    (contDiff_conjT.comp hs)) contDiff_const) contDiff_const) hs

/- English proof (translation)
Simplify using `only [prodEx, List.ofFn_succ, List.prod_cons]`.
-/
theorem prodEx_succ {d : ℕ} (X : Fin (d + 1) → Mat n) (t : Fin (d + 1) → ℝ) :
    prodEx X t = ex (X 0) (t 0) * prodEx (fun j => X j.succ) (fun j => t j.succ) := by
  simp only [prodEx, List.ofFn_succ, List.prod_cons]

/- English proof (translation)
Unfold `prodEx`. Use `List.prod_eq_one fun x hx => ?_` and prove the remaining obligations. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `ex_zero _`.
-/
theorem prodEx_zero {d : ℕ} (X : Fin d → Mat n) : prodEx X 0 = 1 := by
  unfold prodEx
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact ex_zero _

/- English proof (translation)
The claim follows from `| 0, X, _, t => by simp [prodEx, UH] | d + 1, X, hX, t => by rw [prodEx_succ] exact CCRuleCW.UH_mul Hm _ _ (ex_mem_of_lie (hX 0) _) (prodEx_mem _ (fun j => hX j.succ) _)`.
-/
theorem prodEx_mem {Hm : Mat n} : ∀ {d : ℕ} (X : Fin d → Mat n), (∀ j, Lie Hm (X j)) →
    ∀ t, prodEx X t ∈ UH Hm
  | 0, X, _, t => by simp [prodEx, UH]
  | d + 1, X, hX, t => by
    rw [prodEx_succ]
    exact CCRuleCW.UH_mul Hm _ _ (ex_mem_of_lie (hX 0) _) (prodEx_mem _ (fun j => hX j.succ) _)

/- English proof (translation)
The claim follows from `contDiff_pi.2 fun j => contDiff_apply ℝ ℝ j.succ`.
-/
theorem contDiff_tail {d : ℕ} :
    ContDiff ℝ ∞ (fun (t : Fin (d + 1) → ℝ) (j : Fin d) => t j.succ) :=
  contDiff_pi.2 fun j => contDiff_apply ℝ ℝ j.succ

/- English proof (translation)
The claim follows from `| 0, X => by have : prodEx X = fun _ => 1 := funext fun t => by simp [prodEx] rw [this]; exact contDiff_const | d + 1, X => by rw [show prodEx X = _ from funext (prodEx_succ X)] exact contDiff_mul' ((contDiff_ex (X 0)).comp (contDiff_apply ℝ ℝ 0)) ((contDiff_prodEx _).comp contDi …`.
-/
theorem contDiff_prodEx : ∀ {d : ℕ} (X : Fin d → Mat n), ContDiff ℝ ∞ (prodEx X)
  | 0, X => by
    have : prodEx X = fun _ => 1 := funext fun t => by simp [prodEx]
    rw [this]; exact contDiff_const
  | d + 1, X => by
    rw [show prodEx X = _ from funext (prodEx_succ X)]
    exact contDiff_mul' ((contDiff_ex (X 0)).comp (contDiff_apply ℝ ℝ 0))
      ((contDiff_prodEx _).comp contDiff_tail)

/- English proof (translation)
The claim follows from `| 0, X, _ => ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩ | d + 1, X, hX => by obtain ⟨Z, h1, h2, h3, h4⟩ := exists_fields h (fun j : Fin d => X j.succ) (fun j => hX j.succ) have hm := prodEx_mem (fun j : Fin d => X j.succ) (fun j => …`.
-/
theorem exists_fields {Hm : Mat n} (h : Hm * Hm = 1) : ∀ {d : ℕ} (X : Fin d → Mat n),
    (∀ j, Lie Hm (X j)) → ∃ Z : Fin d → (Fin d → ℝ) → Mat n, (∀ j t, Lie Hm (Z j t)) ∧
      (∀ j t (τ : ℝ), prodEx X (t + τ • (Pi.single j 1 : Fin d → ℝ)) = prodEx X t * ex (Z j t) τ) ∧
      (∀ j, ContDiff ℝ ∞ (Z j)) ∧ ∀ j, Z j 0 = X j
  | 0, X, _ => ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0⟩
  | d + 1, X, hX => by
    obtain ⟨Z, h1, h2, h3, h4⟩ := exists_fields h (fun j : Fin d => X j.succ) (fun j => hX j.succ)
    have hm := prodEx_mem (fun j : Fin d => X j.succ) (fun j => hX j.succ)
    refine ⟨Fin.cons (α := fun _ => (Fin (d + 1) → ℝ) → Mat n)
      (fun t => (prodEx (fun j : Fin d => X j.succ) (fun j => t j.succ))⁻¹ * X 0 *
        prodEx (fun j : Fin d => X j.succ) (fun j => t j.succ))
      (fun j t => Z j (fun i => t i.succ)), ?_, ?_, ?_, ?_⟩
    · intro j t
      refine Fin.cases ?_ (fun j => ?_) j
      · exact lie_conj h (hm _) (hX 0)
      · exact h1 j _
    · intro j t τ
      refine Fin.cases ?_ (fun j => ?_) j
      · have hu := isUnit_of_mem h (hm fun j => t j.succ)
        have e : (fun j : Fin d => (t + τ • (Pi.single 0 1 : Fin (d + 1) → ℝ)) j.succ) =
            fun j => t j.succ := funext fun j => by simp
        have e0 : (t + τ • (Pi.single 0 1 : Fin (d + 1) → ℝ)) 0 = t 0 + τ := by simp
        rw [prodEx_succ, prodEx_succ X t, Fin.cons_zero, ex_conj hu, e, e0, ex_add]
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)]
      · have e : (fun i : Fin d => (t + τ • (Pi.single j.succ 1 : Fin (d + 1) → ℝ)) i.succ) =
            (fun i => t i.succ) + τ • (Pi.single j 1 : Fin d → ℝ) := funext fun i => by
          simp [Pi.single_apply]
        have e0 : (t + τ • (Pi.single j.succ 1 : Fin (d + 1) → ℝ)) 0 = t 0 := by
          simp [(Fin.succ_ne_zero j).symm]
        rw [prodEx_succ, prodEx_succ X t, Fin.cons_succ, e, e0, h2, Matrix.mul_assoc]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact contDiff_conj h ((contDiff_prodEx _).comp contDiff_tail) (fun t => hm _) (X 0)
      · exact (h3 j).comp contDiff_tail
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have := prodEx_zero (fun j : Fin d => X j.succ)
        change (prodEx (fun j : Fin d => X j.succ) 0)⁻¹ * X 0 * prodEx (fun j : Fin d => X j.succ) 0 = _
        rw [this]; simp
      · exact h4 j

def lieSub (Hm : Mat n) : Submodule ℝ (Mat n) where
  carrier := {Y | Lie Hm Y}
  add_mem' := fun {A B} hA hB => by
    have hA' : Aᴴ * Hm + Hm * A = 0 := hA
    have hB' : Bᴴ * Hm + Hm * B = 0 := hB
    change (A + B)ᴴ * Hm + Hm * (A + B) = 0
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hA', hB', add_zero]
  zero_mem' := by simp [Lie]
  smul_mem' := fun c A hA => by
    have hA' : Aᴴ * Hm + Hm * A = 0 := hA
    change (c • A)ᴴ * Hm + Hm * (c • A) = 0
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA', smul_zero]

/- English proof (translation)
Introduce `n Hm h d e X Q hX hQ hS`. Take `⟨Z, h1, h2, h3, h4⟩` from `exists_fields h X hX`. Take `⟨U, hU, hU0, hsol⟩` from `smooth_coeffs (lieSub Hm) Z Q h3 h1 hQ (fun y hy => by`. Take `⟨a, b, hab⟩` from `hS y hy`. Conclude with `⟨a, b, by simpa only [h4, Complex.coe_smul] using hab⟩)`.

Establish `hm` using `prodEx_mem X hX`. Use `⟨U, hU, hU0, contDiff_prodEx X, hm, hQ, Z, h1, h2, fun Y hY => ?_⟩` and prove the remaining obligations. Take `⟨a, b, ha, hb, hab⟩` from `hsol (fun t => (prodEx X t)⁻¹ * Y * prodEx X t) (contDiff_conj h (contDiff_prodEx X) hm Y) (fun t => lie_conj h (hm t) hY)`. Conclude with `⟨a, b, ha, hb, fun t ht => by simpa only [Complex.coe_smul] using hab t ht⟩`.
-/
theorem chartExists : ChartExists := by
  intro n Hm h d e X Q hX hQ hS
  obtain ⟨Z, h1, h2, h3, h4⟩ := exists_fields h X hX
  obtain ⟨U, hU, hU0, hsol⟩ := smooth_coeffs (lieSub Hm) Z Q h3 h1 hQ
    (fun y hy => by
      obtain ⟨a, b, hab⟩ := hS y hy
      exact ⟨a, b, by simpa only [h4, Complex.coe_smul] using hab⟩)
  have hm := prodEx_mem X hX
  refine ⟨U, hU, hU0, contDiff_prodEx X, hm, hQ, Z, h1, h2, fun Y hY => ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hsol (fun t => (prodEx X t)⁻¹ * Y * prodEx X t)
    (contDiff_conj h (contDiff_prodEx X) hm Y) (fun t => lie_conj h (hm t) hY)
  exact ⟨a, b, ha, hb, fun t ht => by simpa only [Complex.coe_smul] using hab t ht⟩

end GlobalTheory.CompanionTheory.ProdExChart
