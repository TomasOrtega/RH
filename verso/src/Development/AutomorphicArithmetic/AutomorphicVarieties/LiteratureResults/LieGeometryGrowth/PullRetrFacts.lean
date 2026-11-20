import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Set `y : KernelIndexFullLattice.G1 E a` to `⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩`. Express the relevant statement in the definitionally equal form `(retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _`. Rewrite using `[mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]`. Both sides reduce to the same expression.
-/
private theorem retr_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Conclude with `Units.ext (Subsingleton.elim _ _)`. Establish `h1 : (0 : ℝ) < a` using `Nat.cast_pos.2 ha`. Establish `h2 : (0 : ℝ) < Module.finrank ℚ E` using `Nat.cast_pos.2 Module.finrank_pos`. Rewrite using `[KernelIndexFullLattice.splitEq_holds E a]`.

Use `congrArg (Reduction.centralSection E a) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.exp _ = _`. Rewrite using `[mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log s.2]`.
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
Assemble the required witnesses or components as `⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩`.
-/
private theorem retr_split (g : GA E a) : ∃ t : ℝ, (retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g :=
  ⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩

/- English proof (translation)
Rewrite using `[GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]`.
-/
private theorem split_retr (g : GA E a) :
    splitCentre E a (Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)) *
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]

/- English proof (translation)
Establish `hs : Continuous (sInf E)` using `((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))`. Conclude with `Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))`.
-/
private theorem cont_inf : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

/- English proof (translation)
Establish `hB : IsCompact {x : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL x‖ ≤ C}`. Establish `h` using `isCompact_closedBall (0 : Lie E a) C`. Establish `e : Metric.closedBall (0 : Lie E a) C = {x : Lie E a | ‖x‖ ≤ C}` using `Set.ext fun _ => mem_closedBall_zero_iff`. Rewrite `h` using `[e]`. Conclude with `h`.

Establish `h` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Use `and_congr Iff.rfl ⟨fun hx => ⟨_, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy, e⟩`.

Establish `e' : y = (x⁻¹).val` using `MulOpposite.op_injective e`. Rewrite `hy` using `[e']`. Then use the resulting hypothesis.
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
Introduce `E _ _ _ a`. Use `⟨retr_split, retr_left, fun C => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun h : GL (Fin a) (Cinf E) => Real.log (Reduction.detModule E a (infGL E a h)).1 / (a * Module.finrank ℚ E)` using `((continuous_subtype_val.comp (Reduction.continuous_detModule.comp cont_inf)).log fun h => (Reduction.detModule E a (infGL E a h)).2.ne').div_const _`. Take `⟨T, hT⟩` from `(compact_box (E := E) (a := a) C).exists_bound_of_continuousOn hc.continuousOn`. Use `⟨T, fun g h h1 h2 => ⟨_, hT h ⟨h1, h2⟩, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[retractOne_mul, Subgroup.coe_mul, ← mul_assoc, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, split_retr]`.
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
