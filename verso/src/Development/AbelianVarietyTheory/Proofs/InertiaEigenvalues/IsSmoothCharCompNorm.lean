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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
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
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Supply the required witnesses or components.
-/
theorem valuativeExtension (hc : Continuous (algebraMap k k')) : ValuativeExtension k k' :=
  ⟨GroundTheory.LocalField.vle_map_iff_of_valuation_lt_one_iff (algebraMap k k') (lt_one_iff hc)⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem isSmoothChar_comp_norm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) {χ : kˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k))) :=
  hχ.comp _ (Continuous.units_map _ (continuous_algNorm hc))

end Cont

end GlobalTheory.LBC.Inh
