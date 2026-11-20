import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero

open Set

namespace GlobalTheory.InjHol

def padZero (m n : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i => if h : (i : ℕ) < m then LinearMap.proj ⟨i, h⟩ else 0

/- English proof (translation)
Simplify using `[padZero, h]`.
-/
theorem padZero_apply_of_lt {m n : ℕ} (y : Fin m → ℂ) (i : Fin n) (h : (i : ℕ) < m) :
    padZero m n y i = y ⟨i, h⟩ := by
  simp [padZero, h]

/- English proof (translation)
Introduce `y z hyz`. Use function extensionality and compare the values at `j`. Use `congrFun hyz ⟨j, lt_of_lt_of_le j.isLt hmn⟩` as an intermediate fact. Rewrite `this` using `[padZero_apply_of_lt (n := n) y ⟨j, _⟩ j.isLt, padZero_apply_of_lt (n := n) z ⟨j, _⟩ j.isLt]`. Then use the resulting hypothesis.
-/
theorem padZero_injective {m n : ℕ} (hmn : m ≤ n) : Function.Injective (padZero m n) := by
  intro y z hyz
  funext j
  have := congrFun hyz ⟨j, lt_of_lt_of_le j.isLt hmn⟩
  rwa [padZero_apply_of_lt (n := n) y ⟨j, _⟩ j.isLt, padZero_apply_of_lt (n := n) z ⟨j, _⟩ j.isLt] at this

/- English proof (translation)
Introduce `d d' U f hU hne hf hinj`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨a, ha⟩` from `hne`. Set `L : (Fin d' → ℂ) →L[ℂ] (Fin d → ℂ)` to `LinearMap.toContinuousLinearMap (padZero d' d)`.

Establish `hL : Function.Injective L` using `padZero_injective hlt.le`. Establish `hg : DifferentiableOn ℂ (fun x => L (f x)) U` using `L.differentiable.comp_differentiableOn hf`. Establish `hgi : Set.InjOn (fun x => L (f x)) U` using `fun x hx y hy hxy => hinj hx hy (hL hxy)`. Establish `hb` using `bijective_fderiv_of_injOn d U (fun x => L (f x)) hU hg hgi a ha`. Establish `hfa : DifferentiableAt ℂ f a` using `hf.differentiableAt (hU.mem_nhds ha)`.

Establish `hder : fderiv ℂ (fun x => L (f x)) a = L.comp (fderiv ℂ f a)` using `(L.hasFDerivAt.comp a hfa.hasFDerivAt).fderiv`. Rewrite `hb` using `[hder, ContinuousLinearMap.coe_comp']`. Establish `hsurj : Function.Surjective (padZero d' d)` using `Function.Surjective.of_comp hb.2`. Establish `hr` using `LinearMap.finrank_range_le (padZero d' d)`. Rewrite `hr` using `[LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_injOn_differentiableOn :
    ∀ (d d' : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d' → ℂ)), IsOpen U →
      U.Nonempty → DifferentiableOn ℂ f U → Set.InjOn f U → d ≤ d' := by
  intro d d' U f hU hne hf hinj
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha⟩ := hne
  let L : (Fin d' → ℂ) →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap (padZero d' d)
  have hL : Function.Injective L := padZero_injective hlt.le
  have hg : DifferentiableOn ℂ (fun x => L (f x)) U :=
    L.differentiable.comp_differentiableOn hf
  have hgi : Set.InjOn (fun x => L (f x)) U := fun x hx y hy hxy => hinj hx hy (hL hxy)
  have hb := bijective_fderiv_of_injOn d U (fun x => L (f x)) hU hg hgi a ha
  have hfa : DifferentiableAt ℂ f a := hf.differentiableAt (hU.mem_nhds ha)
  have hder : fderiv ℂ (fun x => L (f x)) a = L.comp (fderiv ℂ f a) :=
    (L.hasFDerivAt.comp a hfa.hasFDerivAt).fderiv
  rw [hder, ContinuousLinearMap.coe_comp'] at hb
  have hsurj : Function.Surjective (padZero d' d) := Function.Surjective.of_comp hb.2
  have hr := LinearMap.finrank_range_le (padZero d' d)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hr
  omega

end GlobalTheory.InjHol
