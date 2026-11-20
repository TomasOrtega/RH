import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo.Cs

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private noncomputable def lam0 (g : GA E a) : ℝ :=
  Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)

/- English proof (translation)
The claim follows from `mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)`.
-/
private theorem deg_pos (ha : 1 ≤ a) : (0 : ℝ) < a * Module.finrank ℚ E :=
  mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)

/- English proof (translation)
Unfold `lam0`. Rewrite using `[map_mul, ← add_div, ← Real.log_mul (Reduction.detModule E a g).2.ne' (Reduction.detModule E a h).2.ne']`. Both sides reduce to the same expression.
-/
private theorem central_log_mul (g h : GA E a) : lam0 (g * h) = lam0 g + lam0 h := by
  unfold lam0
  rw [map_mul, ← add_div, ← Real.log_mul (Reduction.detModule E a g).2.ne' (Reduction.detModule E a h).2.ne']
  rfl

/- English proof (translation)
Establish `e : splitCentre E a (lam0 g) = Reduction.centralSection E a (Reduction.detModule E a g)`. Rewrite using `[KernelIndexFullLattice.splitEq_holds E a]`. Use `congrArg (Reduction.centralSection E a) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.exp _ = _`. Rewrite using `[lam0, mul_div_cancel₀ _ (deg_pos ha).ne', Real.exp_log (Reduction.detModule E a g).2]`.

Rewrite using `[GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, e, coe_retractOne, inv_mul_cancel_right]`.
-/
private theorem central_split_mul_retract (ha : 1 ≤ a) (g : GA E a) :
    splitCentre E a (lam0 g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  have e : splitCentre E a (lam0 g) = Reduction.centralSection E a (Reduction.detModule E a g) := by
    rw [KernelIndexFullLattice.splitEq_holds E a]
    refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
    change Real.exp _ = _
    rw [lam0, mul_div_cancel₀ _ (deg_pos ha).ne', Real.exp_log (Reduction.detModule E a g).2]
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, e, coe_retractOne, inv_mul_cancel_right]

/- English proof (translation)
Rewrite using `[lam0, (Reduction.mem_normOneGL_iff_detModule).1 x.2]`. Simplify using the standard rewrite rules.
-/
private theorem central_log_eq_zero_on_norm_one (x : KernelIndexFullLattice.G1 E a) : lam0 (x.1 : GA E a) = 0 := by
  rw [lam0, (Reduction.mem_normOneGL_iff_detModule).1 x.2]
  simp

/- English proof (translation)
Rewrite using `[lam0, KernelIndexFullLattice.splitEq_holds E a, Reduction.detModule_centralSection (by omega)]`. Express the relevant statement in the definitionally equal form `Real.log (Real.exp _) / _ = _`. Rewrite using `[Real.log_exp, mul_div_cancel_left₀ _ (deg_pos ha).ne']`.
-/
private theorem central_log_split (ha : 1 ≤ a) (t : ℝ) : lam0 (splitCentre E a t) = t := by
  rw [lam0, KernelIndexFullLattice.splitEq_holds E a, Reduction.detModule_centralSection (by omega)]
  change Real.log (Real.exp _) / _ = _
  rw [Real.log_exp, mul_div_cancel_left₀ _ (deg_pos ha).ne']

end UpperTheory.V.Lit.Geo.Cs

/- English proof (translation)
Introduce `E _ _ _ a ha`. Use `⟨lam0, central_log_mul, central_split_mul_retract ha, fun c => ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩` from `(UpperTheory.V.Lit.Geo.retrFacts E a).2.2 c`. Use `⟨T, fun h hh => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, e⟩` from `hT 1 h hh.1 hh.2`.

Establish `e'` using `congrArg lam0 e`. Rewrite `e'` using `[central_log_mul, central_log_mul, central_log_eq_zero_on_norm_one, central_log_eq_zero_on_norm_one, central_log_split ha, zero_add, add_zero]`. Rewrite using `[e']` and apply the resulting hypothesis.
-/
theorem UpperTheory.V.Lit.Geo.Cs.lamEx :
    LamEx := by
  intro E _ _ _ a ha
  refine ⟨lam0, central_log_mul, central_split_mul_retract ha, fun c => ?_⟩
  obtain ⟨T, hT⟩ := (UpperTheory.V.Lit.Geo.retrFacts E a).2.2 c
  refine ⟨T, fun h hh => ?_⟩
  obtain ⟨t, ht, e⟩ := hT 1 h hh.1 hh.2
  have e' := congrArg lam0 e
  rw [central_log_mul, central_log_mul, central_log_eq_zero_on_norm_one, central_log_eq_zero_on_norm_one, central_log_split ha, zero_add, add_zero] at e'
  rwa [e']
