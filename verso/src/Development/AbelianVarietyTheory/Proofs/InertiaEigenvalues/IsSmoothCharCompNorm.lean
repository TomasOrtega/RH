import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
import GroundTheory.LocalFields.Uniqueness
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LBC
open scoped Topology

namespace GlobalTheory.LBC.Inh
open ValuativeRel Filter

section Cont
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']

/- English proof (translation)
Use `isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff').2 ⟨1, fun z hz => ?_⟩` and prove the remaining obligations. Establish `e : z = (z - x) + x` using `by ring`. Use `show valuation F z < 1`. Rewrite using `[e]`. Establish `hz' : valuation F (z - x) < 1` using `by simpa using hz`.

Conclude with `(valuation F).map_add_lt hz' hx`.
-/
theorem isOpen_lt_one (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen {x : F | valuation F x < 1} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff').2 ⟨1, fun z hz => ?_⟩
  have e : z = (z - x) + x := by ring
  show valuation F z < 1
  rw [e]
  have hz' : valuation F (z - x) < 1 := by simpa using hz
  exact (valuation F).map_add_lt hz' hx

/- English proof (translation)
Establish `h1` using `(GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff z).2 h`. Establish `h2` using `(hc.tendsto 0).comp h1`. Rewrite `h2` using `[map_zero]`. Apply `(GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).1` to reduce the goal to its premises. Use `h2.congr fun n => ?_` and prove the remaining obligations.

Simplify using `[Function.comp_apply, map_pow]`.
-/
theorem lt_one_of_lt_one (hc : Continuous (algebraMap k k')) {z : k} (h : valuation k z < 1) :
    valuation k' (algebraMap k k' z) < 1 := by
  have h1 := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff z).2 h
  have h2 := (hc.tendsto 0).comp h1
  rw [map_zero] at h2
  apply (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).1
  refine h2.congr fun n => ?_
  simp [Function.comp_apply, map_pow]

/- English proof (translation)
Use `⟨fun h => ?_, lt_one_of_lt_one hc⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hz`. Use `push_neg at hz`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hz`. Break down `hz.lt_or_eq with hlt | heq` into its components or cases. Establish `h2 : valuation k z⁻¹ < 1` using `by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt`. Establish `h3` using `lt_one_of_lt_one (k' := k') hc h2`. Establish `h4 : valuation k' (algebraMap k k' z) * valuation k' (algebraMap k k' z⁻¹) = 1`.

Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]`. Use `lt_of_le_of_lt (mul_le_of_le_one_left' h.le) h3` as an intermediate fact. Rewrite `this` using `[h4]`. Conclude with `lt_irrefl _ this`. Use `set S : Set k := {x | valuation k x ≤ 1} ∩ {x | valuation k x < 1}ᶜ with hS`.

Establish `hSc : IsCompact S` using `(IsNonarchimedeanLocalField.isCompact_closedBall k 1).inter_right (isOpen_lt_one k).isClosed_compl`. Use `haveI : T2Space k' := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k'`. Establish `hI : IsClosed (algebraMap k k' '' S)` using `(hSc.image hc).isClosed`. Establish `h0 : (0 : k') ∉ algebraMap k k' '' S`. Introduce and unpack `⟨x, hx, hx0⟩`.

Rewrite `hx0` using `[map_eq_zero_iff _ (algebraMap k k').injective]`. Substitute `hx0` using the available equality. Simplify using `[hS] at hx`. Establish `ht` using `(GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).2 h`. Take `⟨n, hn⟩` from `(ht.eventually (hI.isOpen_compl.mem_nhds h0)).exists`.

Apply `hn` to reduce the goal to its premises. Use `⟨z ^ n, ?_, by rw [map_pow]⟩` and prove the remaining obligations. Simplify using `[hS, map_pow, ← heq]`.
-/
theorem lt_one_iff (hc : Continuous (algebraMap k k')) (z : k) :
    valuation k' (algebraMap k k' z) < 1 ↔ valuation k z < 1 := by
  refine ⟨fun h => ?_, lt_one_of_lt_one hc⟩
  by_contra hz
  push_neg at hz
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  rcases hz.lt_or_eq with hlt | heq
  · have h2 : valuation k z⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    have h3 := lt_one_of_lt_one (k' := k') hc h2
    have h4 : valuation k' (algebraMap k k' z) * valuation k' (algebraMap k k' z⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
    have := lt_of_le_of_lt (mul_le_of_le_one_left' h.le) h3
    rw [h4] at this
    exact lt_irrefl _ this
  · set S : Set k := {x | valuation k x ≤ 1} ∩ {x | valuation k x < 1}ᶜ with hS
    have hSc : IsCompact S :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).inter_right (isOpen_lt_one k).isClosed_compl
    haveI : T2Space k' := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k'
    have hI : IsClosed (algebraMap k k' '' S) := (hSc.image hc).isClosed
    have h0 : (0 : k') ∉ algebraMap k k' '' S := by
      rintro ⟨x, hx, hx0⟩
      rw [map_eq_zero_iff _ (algebraMap k k').injective] at hx0
      subst hx0
      simp [hS] at hx
    have ht := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).2 h
    obtain ⟨n, hn⟩ := (ht.eventually (hI.isOpen_compl.mem_nhds h0)).exists
    apply hn
    refine ⟨z ^ n, ?_, by rw [map_pow]⟩
    simp [hS, map_pow, ← heq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨GroundTheory.LocalField.vle_map_iff_of_valuation_lt_one_iff (algebraMap k k') (lt_one_iff hc)⟩`.
-/
theorem valuativeExtension (hc : Continuous (algebraMap k k')) : ValuativeExtension k k' :=
  ⟨GroundTheory.LocalField.vle_map_iff_of_valuation_lt_one_iff (algebraMap k k') (lt_one_iff hc)⟩

/- English proof (translation)
Use `haveI := valuativeExtension hc`. Use `haveI := GroundTheory.LocalField.isModuleTopology k k'`. Set `b` to `Module.finBasis k k'`. Establish `h : (Algebra.norm k : k' → k) = fun t => (Algebra.leftMulMatrix b t).det`. Use function extensionality and compare the values at `t`.

Conclude with `Algebra.norm_eq_matrix_det b t`. Rewrite using `[h]`. Use `Continuous.matrix_det ?_` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `: (fun t : k' => Algebra.leftMulMatrix b t i j) = fun t => (b.coord i) (LinearMap.mulRight k (b j) t)`.

Use function extensionality and compare the values at `t`. Simplify using `[Algebra.leftMulMatrix_eq_repr_mul]`. Rewrite using `[this]`. Conclude with `IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight k (b j)))`.
-/
theorem continuous_algNorm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) :
    Continuous (Algebra.norm k : k' → k) := by
  classical
  haveI := valuativeExtension hc
  haveI := GroundTheory.LocalField.isModuleTopology k k'
  let b := Module.finBasis k k'
  have h : (Algebra.norm k : k' → k) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : k' => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight k (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight k (b j)))

/- English proof (translation)
The claim follows from `hχ.comp _ (Continuous.units_map _ (continuous_algNorm hc))`.
-/
theorem isSmoothChar_comp_norm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) {χ : kˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k))) :=
  hχ.comp _ (Continuous.units_map _ (continuous_algNorm hc))

end Cont

end GlobalTheory.LBC.Inh
