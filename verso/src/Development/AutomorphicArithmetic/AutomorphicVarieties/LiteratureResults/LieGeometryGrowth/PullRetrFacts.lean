import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem retr_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem split_eq (s : {r : ℝ // 0 < r}) :
    splitCentre E a (Real.log s.1 / (a * Module.finrank ℚ E)) = Reduction.centralSection E a s := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [KernelIndexFullLattice.splitEq_holds E a]
  refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log s.2]

/- English proof (translation)
Supply the required witnesses or components.
-/
private theorem retr_split (g : GA E a) : ∃ t : ℝ, (retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g :=
  ⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem split_retr (g : GA E a) :
    splitCentre E a (Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)) *
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem cont_inf : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
private theorem compact_box (C : ℝ) :
    IsCompact {h : GL (Fin a) (Cinf E) | ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C} := by
  have hB : IsCompact {x : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL x‖ ≤ C} := by
    have h := isCompact_closedBall (0 : Lie E a) C
    have e : Metric.closedBall (0 : Lie E a) C = {x : Lie E a | ‖x‖ ≤ C} := Set.ext fun _ => mem_closedBall_zero_iff
    rw [e] at h
    exact h
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  refine and_congr Iff.rfl ⟨fun hx => ⟨_, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  have e' : y = (x⁻¹).val := MulOpposite.op_injective e
  rwa [e'] at hy

end UpperTheory.V.Lit.Geo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.Lit.Geo.retrFacts :
    RetrFacts := by
  intro E _ _ _ a
  refine ⟨retr_split, retr_left, fun C => ?_⟩
  have hc : Continuous fun h : GL (Fin a) (Cinf E) =>
      Real.log (Reduction.detModule E a (infGL E a h)).1 / (a * Module.finrank ℚ E) :=
    ((continuous_subtype_val.comp (Reduction.continuous_detModule.comp cont_inf)).log
      fun h => (Reduction.detModule E a (infGL E a h)).2.ne').div_const _
  obtain ⟨T, hT⟩ := (compact_box (E := E) (a := a) C).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨T, fun g h h1 h2 => ⟨_, hT h ⟨h1, h2⟩, ?_⟩⟩
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, split_retr]
