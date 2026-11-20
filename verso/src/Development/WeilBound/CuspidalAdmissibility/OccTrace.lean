import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.LocallyConstantCompact

open MeasureTheory GroundTheory.Automorphic

namespace PositivityTheory.TfC.OccursIff.Trace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {X : Type} [AddCommGroup X] [Module ℂ X]

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g`. Use `⟨(fun h => g⁻¹ * h) ⁻¹' (stabilizerOf ρ v : Set G), (hρ v).preimage (by fun_prop), ?_, fun h hh => ?_⟩` and prove the remaining obligations. Use `show g⁻¹ * g ∈ stabilizerOf ρ v`. Rewrite using `[inv_mul_cancel]`.

Conclude with `one_mem _`. Establish `hh' : ρ (g⁻¹ * h) v = v` using `hh`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Use `_ = ρ g v := by rw [hh']`.
-/
theorem orbit_isLocallyConstant (ρ : Representation ℂ G X) (hρ : IsSmooth ρ) (v : X) :
    IsLocallyConstant fun g => ρ g v := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (stabilizerOf ρ v : Set G), (hρ v).preimage (by fun_prop), ?_, fun h hh => ?_⟩
  · show g⁻¹ * g ∈ stabilizerOf ρ v
    rw [inv_mul_cancel]
    exact one_mem _
  · have hh' : ρ (g⁻¹ * h) v = v := hh
    calc ρ h v = ρ g (ρ (g⁻¹ * h) v) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ g v := by rw [hh']

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/- English proof (translation)
Establish `hloc` using `orbit_isLocallyConstant ρ hρ v`. Establish `hS : ((fun g => ρ g v) '' tsupport φ).Finite` using `by haveI : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.1 hφc`. Establish `h1` using `(hloc.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport φ)))).range_finite`. Rewrite `h1` using `[Set.range_comp, Subtype.range_coe]`. Then use the resulting hypothesis. Use `set S := hS.toFinset`.

Set `E : X → Set G` to `fun s => {g | ρ g v = s}`. Establish `hE : ∀ s, MeasurableSet (E s)` using `fun s => (hloc.isOpen_fiber s).measurableSet`. Establish `hφi : Integrable φ m` using `hφ.continuous.integrable_of_hasCompactSupport hφc`. Use `⟨∑ s ∈ S, (∫ g, (E s).indicator φ g ∂m) • s, fun l => ?_⟩` and prove the remaining obligations. Establish `hpt : ∀ g, φ g * l (ρ g v) = ∑ s ∈ S, (E s).indicator φ g * l s`.

Introduce `g`. Distinguish the cases in `hg : φ g = 0`. Simplify using `[hg, Set.indicator_apply]`. Establish `hgS : ρ g v ∈ S` using `hS.mem_toFinset.2 ⟨g, subset_tsupport φ hg, rfl⟩`. Rewrite using `[Finset.sum_eq_single (ρ g v)]`.

Simplify using `[E]`. Introduce `s _ hs`. Simplify using `[E, Ne.symm hs]`. Introduce `h`. Conclude with `absurd hgS h`.

Establish `hfun : (fun g => φ g * l (ρ g v)) = fun g => ∑ s ∈ S, (E s).indicator φ g * l s` using `funext hpt`. Rewrite using `[hfun, integral_finsetSum]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, integral_mul_const]`. Introduce `s _`. Conclude with `(hφi.indicator (hE s)).mul_const (l s)`.
-/
theorem exists_vec (m : Measure G) [m.IsHaarMeasure] (ρ : Representation ℂ G X) (hρ : IsSmooth ρ) (φ : G → ℂ)
    (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) (v : X) :
    ∃ a : X, ∀ l : Module.Dual ℂ X, l a = ∫ g, φ g * l (ρ g v) ∂m := by
  classical
  have hloc := orbit_isLocallyConstant ρ hρ v
  have hS : ((fun g => ρ g v) '' tsupport φ).Finite := by
    haveI : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.1 hφc
    have h1 := (hloc.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport φ)))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h1
  set S := hS.toFinset
  let E : X → Set G := fun s => {g | ρ g v = s}
  have hE : ∀ s, MeasurableSet (E s) := fun s => (hloc.isOpen_fiber s).measurableSet
  have hφi : Integrable φ m := hφ.continuous.integrable_of_hasCompactSupport hφc
  refine ⟨∑ s ∈ S, (∫ g, (E s).indicator φ g ∂m) • s, fun l => ?_⟩
  have hpt : ∀ g, φ g * l (ρ g v) = ∑ s ∈ S, (E s).indicator φ g * l s := by
    intro g
    by_cases hg : φ g = 0
    · simp [hg, Set.indicator_apply]
    · have hgS : ρ g v ∈ S := hS.mem_toFinset.2 ⟨g, subset_tsupport φ hg, rfl⟩
      rw [Finset.sum_eq_single (ρ g v)]
      · simp [E]
      · intro s _ hs
        simp [E, Ne.symm hs]
      · intro h
        exact absurd hgS h
  have hfun : (fun g => φ g * l (ρ g v)) = fun g => ∑ s ∈ S, (E s).indicator φ g * l s := funext hpt
  rw [hfun, integral_finsetSum]
  · simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]
  · intro s _
    exact (hφi.indicator (hE s)).mul_const (l s)

/- English proof (translation)
Establish `hint : ∀ v (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m` using `fun v l => (hφ.continuous.mul ((orbit_isLocallyConstant ρ hρ.1 v).comp l).continuous).integrable_of_hasCompactSupport hφc.mul_right`. Use `choose A0 hA0 using exists_vec m ρ hρ.1 φ hφ hφc`. Establish `huniq : ∀ a b : X, (∀ l : Module.Dual ℂ X, l a = l b) → a = b` using `fun a b h => sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).1 fun l => by rw [map_sub, h, sub_self])`. Set `A : X →ₗ[ℂ] X` to `{ toFun := A0 map_add' := fun v v' => huniq _ _ fun l => by`. Rewrite using `[map_add, hA0, hA0, hA0, ← integral_add (hint v l) (hint v' l)]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[map_add, map_add, mul_add]`. Use the proof step `map_smul' := fun c v => huniq _ _ fun l => by`. Rewrite using `[map_smul, hA0, hA0, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[map_smul, map_smul, smul_eq_mul]`. Use `ring }`. Take `⟨K, hKc, hK⟩` from `exists_forall_mul_left (R := ℂ) (E := ℂ) (show φ ∈ locallyConstantCompactSupport G ℂ ℂ from ⟨hφ, hφc⟩)`.

Use `⟨A, fun v l => ⟨hint v l, hA0 v l⟩, ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional ℂ (fixedVectors ρ (K : Subgroup G)) := hρ.2 K hKc K.isOpen`. Use `Submodule.finiteDimensional_of_le (S₂ := fixedVectors ρ (K : Subgroup G)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩ k hk`. Use `huniq _ _ fun l => ?_` and prove the remaining obligations.

Establish `h1` using `hA0 v (l ∘ₗ ρ k)`. Rewrite `h1` using `[LinearMap.comp_apply]`. Use `show l (ρ k (A0 v)) = l (A0 v)`. Rewrite using `[h1, hA0]`. Establish `e : (fun g => φ g * (l ∘ₗ ρ k) (ρ g v)) = fun g => (fun h => φ (k⁻¹ * h) * l (ρ h v)) (k * g)`.

Use function extensionality and compare the values at `g`. Simplify using `only [inv_mul_cancel_left, LinearMap.comp_apply]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Rewrite using `[e, integral_mul_left_eq_self (fun h => φ (k⁻¹ * h) * l (ρ h v)) k]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[hK k⁻¹ (inv_mem hk) g]`.
-/
theorem exists_integralOp (m : Measure G) [m.IsHaarMeasure] (ρ : Representation ℂ G X) (hρ : IsAdmissible ρ)
    (φ : G → ℂ) (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) :
    ∃ A : X →ₗ[ℂ] X, (∀ (v : X) (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m ∧
      l (A v) = ∫ g, φ g * l (ρ g v) ∂m) ∧ FiniteDimensional ℂ (LinearMap.range A) := by
  classical
  have hint : ∀ v (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m := fun v l =>
    (hφ.continuous.mul ((orbit_isLocallyConstant ρ hρ.1 v).comp l).continuous).integrable_of_hasCompactSupport
      hφc.mul_right
  choose A0 hA0 using exists_vec m ρ hρ.1 φ hφ hφc
  have huniq : ∀ a b : X, (∀ l : Module.Dual ℂ X, l a = l b) → a = b := fun a b h =>
    sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).1 fun l => by rw [map_sub, h, sub_self])
  let A : X →ₗ[ℂ] X :=
    { toFun := A0
      map_add' := fun v v' => huniq _ _ fun l => by
        rw [map_add, hA0, hA0, hA0, ← integral_add (hint v l) (hint v' l)]
        congr 1
        funext g
        rw [map_add, map_add, mul_add]
      map_smul' := fun c v => huniq _ _ fun l => by
        rw [map_smul, hA0, hA0, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext g
        rw [map_smul, map_smul, smul_eq_mul]
        ring }
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left (R := ℂ) (E := ℂ)
    (show φ ∈ locallyConstantCompactSupport G ℂ ℂ from ⟨hφ, hφc⟩)
  refine ⟨A, fun v l => ⟨hint v l, hA0 v l⟩, ?_⟩
  haveI : FiniteDimensional ℂ (fixedVectors ρ (K : Subgroup G)) := hρ.2 K hKc K.isOpen
  refine Submodule.finiteDimensional_of_le (S₂ := fixedVectors ρ (K : Subgroup G)) ?_
  rintro _ ⟨v, rfl⟩ k hk
  refine huniq _ _ fun l => ?_
  have h1 := hA0 v (l ∘ₗ ρ k)
  rw [LinearMap.comp_apply] at h1
  show l (ρ k (A0 v)) = l (A0 v)
  rw [h1, hA0]
  have e : (fun g => φ g * (l ∘ₗ ρ k) (ρ g v)) = fun g => (fun h => φ (k⁻¹ * h) * l (ρ h v)) (k * g) := by
    funext g
    simp only [inv_mul_cancel_left, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul]
  rw [e, integral_mul_left_eq_self (fun h => φ (k⁻¹ * h) * l (ρ h v)) k]
  congr 1
  funext g
  rw [hK k⁻¹ (inv_mem hk) g]

end PositivityTheory.TfC.OccursIff.Trace
