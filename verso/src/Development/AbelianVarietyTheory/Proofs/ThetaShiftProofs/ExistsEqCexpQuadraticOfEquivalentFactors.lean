import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open Set Filter Topology Complex

namespace GlobalTheory

section Log

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Establish `hU : IsSimplyConnected (univ : Set V)` using `by haveI : ContractibleSpace (univ : Set V) := (convex_univ (𝕜 := ℝ)).contractibleSpace ⟨0, trivial⟩`. Conclude with `(inferInstance : SimplyConnectedSpace (univ : Set V))`. Take `⟨q, hq, hq'⟩` from `Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ hf.continuousOn (by rintro ⟨v, -, hv⟩; exact h0 v hv)`. Conclude with `⟨q, continuousOn_univ.1 hq, fun v => hq' (mem_univ v)⟩`.
-/
theorem exists_continuous_cexp_eq {f : V → ℂ} (hf : Continuous f) (h0 : ∀ v, f v ≠ 0) :
    ∃ q : V → ℂ, Continuous q ∧ ∀ v, cexp (q v) = f v := by
  have hU : IsSimplyConnected (univ : Set V) := by
    haveI : ContractibleSpace (univ : Set V) := (convex_univ (𝕜 := ℝ)).contractibleSpace ⟨0, trivial⟩
    exact (inferInstance : SimplyConnectedSpace (univ : Set V))
  obtain ⟨q, hq, hq'⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    hf.continuousOn (by rintro ⟨v, -, hv⟩; exact h0 v hv)
  exact ⟨q, continuousOn_univ.1 hq, fun v => hq' (mem_univ v)⟩

/- English proof (translation)
Introduce `x`. Establish `hc : Continuous fun v => (q v - q x).im` using `by fun_prop`. Establish `hev : ∀ᶠ v in 𝓝 x, (q v - q x).im ∈ Ioo (-Real.pi) Real.pi` using `hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))`. Establish `he : q =ᶠ[𝓝 x] fun v => q x + log (cexp (q v) * cexp (-q x))` using `by filter_upwards [hev] with v hv`. Rewrite using `[← exp_add, ← sub_eq_add_neg, log_exp hv.1 hv.2.le]`.

Expand and normalize the polynomial expressions, which then agree. Use `DifferentiableAt.congr_of_eventuallyEq ?_ he` and prove the remaining obligations. Use `DifferentiableAt.const_add _ (DifferentiableAt.clog ((hf x).mul_const _) ?_)` and prove the remaining obligations. Simplify using `[← exp_add]`.
-/
theorem differentiable_of_continuous_of_cexp {q : V → ℂ} (hq : Continuous q)
    (hf : Differentiable ℂ fun v => cexp (q v)) : Differentiable ℂ q := by
  intro x
  have hc : Continuous fun v => (q v - q x).im := by fun_prop
  have hev : ∀ᶠ v in 𝓝 x, (q v - q x).im ∈ Ioo (-Real.pi) Real.pi :=
    hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))
  have he : q =ᶠ[𝓝 x] fun v => q x + log (cexp (q v) * cexp (-q x)) := by
    filter_upwards [hev] with v hv
    rw [← exp_add, ← sub_eq_add_neg, log_exp hv.1 hv.2.le]
    ring
  refine DifferentiableAt.congr_of_eventuallyEq ?_ he
  refine DifferentiableAt.const_add _ (DifferentiableAt.clog ((hf x).mul_const _) ?_)
  simp [← exp_add]

/- English proof (translation)
Take `⟨q, hq, hq'⟩` from `exists_continuous_cexp_eq hf.continuous h0`. Conclude with `⟨q, differentiable_of_continuous_of_cexp hq (by simpa only [hq'] using hf), hq'⟩`.
-/
theorem exists_differentiable_cexp_eq {f : V → ℂ} (hf : Differentiable ℂ f) (h0 : ∀ v, f v ≠ 0) :
    ∃ q : V → ℂ, Differentiable ℂ q ∧ ∀ v, cexp (q v) = f v := by
  obtain ⟨q, hq, hq'⟩ := exists_continuous_cexp_eq hf.continuous h0
  exact ⟨q, differentiable_of_continuous_of_cexp hq (by simpa only [hq'] using hf), hq'⟩

/- English proof (translation)
Establish `hc : (range φ).Countable`. Use `(countable_range fun n : ℤ => (n : ℂ) * (2 * Real.pi * I)).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨n, hn⟩` from `exp_eq_one_iff.1 (h z)`. Conclude with `⟨n, hn.symm⟩`.

Conclude with `hc.isTotallyDisconnected _ Subset.rfl (isPreconnected_range hφ) ⟨x, rfl⟩ ⟨y, rfl⟩`.
-/
theorem apply_eq_of_continuous_of_cexp_eq_one {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {φ : X → ℂ} (hφ : Continuous φ) (h : ∀ x, cexp (φ x) = 1) (x y : X) :
    φ x = φ y := by
  have hc : (range φ).Countable := by
    refine (countable_range fun n : ℤ => (n : ℂ) * (2 * Real.pi * I)).mono ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := exp_eq_one_iff.1 (h z)
    exact ⟨n, hn.symm⟩
  exact hc.isTotallyDisconnected _ Subset.rfl (isPreconnected_range hφ) ⟨x, rfl⟩ ⟨y, rfl⟩

end Log

section Factor

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Establish `h1` using `(lin₁ g).continuous_of_finiteDimensional`. Establish `h2` using `(lin₂ g).continuous_of_finiteDimensional`. Use `apply_eq_of_continuous_of_cexp_eq_one (φ := fun v => lin₁ g v + c₁ g + q v - (lin₂ g v + c₂ g + q (v + p g))) (by fun_prop) (fun v => by rw [← exp_eq_exp_iff_exp_sub_eq_one, exp_add _ (q v), h, ← exp_add]) v 0` as an intermediate fact. Simplify using `only [map_zero, zero_add] at this`. Take the linear combination `-this`.
-/
theorem sub_eq_of_equivalent_factors (p : G → V) (lin₁ lin₂ : G → V →ₗ[ℂ] ℂ) (c₁ c₂ : G → ℂ)
    {q : V → ℂ} (hq : Continuous q)
    (h : ∀ g v, cexp (lin₁ g v + c₁ g) * cexp (q v) =
      cexp (lin₂ g v + c₂ g) * cexp (q (v + p g))) (g : G) (v : V) :
    q (v + p g) - q v = lin₁ g v - lin₂ g v + (q (p g) - q 0) := by
  have h1 := (lin₁ g).continuous_of_finiteDimensional
  have h2 := (lin₂ g).continuous_of_finiteDimensional
  have := apply_eq_of_continuous_of_cexp_eq_one
    (φ := fun v => lin₁ g v + c₁ g + q v - (lin₂ g v + c₂ g + q (v + p g))) (by fun_prop)
    (fun v => by rw [← exp_eq_exp_iff_exp_sub_eq_one, exp_add _ (q v), h, ← exp_add]) v 0
  simp only [map_zero, zero_add] at this
  linear_combination -this

/- English proof (translation)
Take `⟨q, hq, hq'⟩` from `exists_continuous_cexp_eq hf h0`. Establish `key` using `sub_eq_of_equivalent_factors p lin₁ lin₂ c₁ c₂ hq (by simpa only [hq'] using h)`. Establish `h1` using `key g (p g')`. Establish `h2` using `key g' (p g)`. Rewrite `h2` using `[add_comm (p g)]`.

Take the linear combination `h2 - h1`.
-/
theorem alternating_eq_of_equivalent_factors (p : G → V) (lin₁ lin₂ : G → V →ₗ[ℂ] ℂ)
    (c₁ c₂ : G → ℂ) {f : V → ℂ} (hf : Continuous f) (h0 : ∀ v, f v ≠ 0)
    (h : ∀ g v, cexp (lin₁ g v + c₁ g) * f v = cexp (lin₂ g v + c₂ g) * f (v + p g)) (g g' : G) :
    lin₁ g (p g') - lin₁ g' (p g) = lin₂ g (p g') - lin₂ g' (p g) := by
  obtain ⟨q, hq, hq'⟩ := exists_continuous_cexp_eq hf h0
  have key := sub_eq_of_equivalent_factors p lin₁ lin₂ c₁ c₂ hq (by simpa only [hq'] using h)
  have h1 := key g (p g')
  have h2 := key g' (p g)
  rw [add_comm (p g)] at h2
  linear_combination h2 - h1

variable [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

end Factor

section Unimodular

/- English proof (translation)
Set `e : L ≃ₗ[R] Module.Dual R L` to `LinearEquiv.ofBijective E hE`. Set `r : L' →ₗ[R] L` to `e.symm.toLinearMap ∘ₗ g.dualMap ∘ₗ E'`. Establish `hr : Function.LeftInverse r g` using `fun a => by`. Express the relevant statement in the definitionally equal form `e.symm (g.dualMap (E' (g a))) = a`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Use extensionality with `b`. Conclude with `hg a b`. Establish `hi : Function.Injective r` using `OrzechProperty.injective_of_surjective_of_injective (LinearEquiv.ofFinrankEq L' L hrk.symm).toLinearMap r (LinearEquiv.injective _) hr.surjective`. Conclude with `⟨hr.injective, fun y => ⟨r y, hi (hr _)⟩⟩`.
-/
theorem bijective_of_isometry_of_bijective_form {R L L' : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
    [AddCommGroup L'] [Module R L'] [Module.Free R L'] [Module.Finite R L']
    (hrk : Module.finrank R L = Module.finrank R L')
    (E : LinearMap.BilinForm R L) (E' : LinearMap.BilinForm R L') (hE : Function.Bijective E)
    (g : L →ₗ[R] L') (hg : ∀ a b, E' (g a) (g b) = E a b) : Function.Bijective g := by
  let e : L ≃ₗ[R] Module.Dual R L := LinearEquiv.ofBijective E hE
  let r : L' →ₗ[R] L := e.symm.toLinearMap ∘ₗ g.dualMap ∘ₗ E'
  have hr : Function.LeftInverse r g := fun a => by
    change e.symm (g.dualMap (E' (g a))) = a
    rw [LinearEquiv.symm_apply_eq]
    ext b
    exact hg a b
  have hi : Function.Injective r :=
    OrzechProperty.injective_of_surjective_of_injective
      (LinearEquiv.ofFinrankEq L' L hrk.symm).toLinearMap r (LinearEquiv.injective _) hr.surjective
  exact ⟨hr.injective, fun y => ⟨r y, hi (hr _)⟩⟩

variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']

/- English proof (translation)
Set `Λ : Submodule ℤ V` to `LinearMap.range P.toIntLinearMap`. Use `haveI : DiscreteTopology Λ := hd`. Use `haveI : IsZLattice ℝ Λ := ⟨hs⟩`. Set `e : L ≃ₗ[ℤ] Λ` to `LinearEquiv.ofInjective P.toIntLinearMap hP`. Conclude with `⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, e.finrank_eq.trans (ZLattice.rank ℝ Λ)⟩`.
-/
theorem free_finite_finrank_of_lattice_embedding {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : L →+ V) (hP : Function.Injective P)
    (hd : DiscreteTopology (range P)) (hs : Submodule.span ℝ (range P) = ⊤) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = Module.finrank ℝ V := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology Λ := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let e : L ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective P.toIntLinearMap hP
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm,
    e.finrank_eq.trans (ZLattice.rank ℝ Λ)⟩

/- English proof (translation)
Establish `hs : Function.Surjective h` using `fun y => by`. Establish `: Submodule.span ℝ S ≤ (LinearMap.range h).restrictScalars ℝ` using `Submodule.span_le.2 hh`. Conclude with `this (hS ▸ Submodule.mem_top)`. Conclude with `⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hs, hs⟩`.
-/
theorem bijective_of_image_range_eq {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [Module ℝ V'] [IsScalarTower ℝ ℂ V'] (hdim : Module.finrank ℂ V = Module.finrank ℂ V')
    (h : V →ₗ[ℂ] V') {S : Set V'} (hS : Submodule.span ℝ S = ⊤) (hh : S ⊆ range h) :
    Function.Bijective h := by
  have hs : Function.Surjective h := fun y => by
    have : Submodule.span ℝ S ≤ (LinearMap.range h).restrictScalars ℝ := Submodule.span_le.2 hh
    exact this (hS ▸ Submodule.mem_top)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hs, hs⟩

variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V']
  [NormedSpace ℝ V'] [IsScalarTower ℝ ℂ V']

end Unimodular

end GlobalTheory
