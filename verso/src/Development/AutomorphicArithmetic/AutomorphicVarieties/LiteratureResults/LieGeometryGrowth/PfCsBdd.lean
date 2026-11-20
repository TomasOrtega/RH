import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Conclude with `⟨0, Units.ext (Subsingleton.elim _ _)⟩`. Establish `h1 : (0 : ℝ) < a` using `Nat.cast_pos.2 ha`. Establish `h2 : (0 : ℝ) < Module.finrank ℚ E` using `Nat.cast_pos.2 Module.finrank_pos`. Use `⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩` and prove the remaining obligations.

Rewrite using `[UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm, ← map_inv (Reduction.centralSection E a)]`. Use `congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.exp _ = _`. Rewrite using `[mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]`.
-/
private theorem exists_split' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    ∃ t : ℝ, splitCentre E a t * g = (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

/- English proof (translation)
Introduce `E _ _ _ a F hF h`. Break down `h with ⟨R, hR⟩ | ⟨C, hC⟩` into its components or cases. Take `⟨K, hK, hK'⟩` from `(qhtFacts E a).2.2.2 R`. Take `⟨M, hM⟩` from `hK.exists_bound_of_continuousOn hF.cont.continuousOn`. Use `⟨max M 0, fun g => ?_⟩` and prove the remaining obligations.

Break down `lt_or_ge R (qht g) with hg | hg` into its components or cases. Rewrite using `[hR g hg, norm_zero]`. Conclude with `le_max_right _ _`. Take `⟨γ, t, hm⟩` from `hK' g hg`. Use `hM _ hm` as an intermediate fact.

Rewrite `this` using `[mul_assoc, hF.left, hF.centre]`. Conclude with `this.trans (le_max_left _ _)`. Use `⟨C, fun g => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `exists_split' g`. Rewrite using `[← hF.centre t g, ht]`.

Conclude with `hC _`.
-/
theorem UpperTheory.V.Lit.Geo.Pf.csBdd :
    UpperTheory.V.Lit.Geo.Pf.CsBdd := by
  intro E _ _ _ a F hF h
  rcases h with ⟨R, hR⟩ | ⟨C, hC⟩
  · obtain ⟨K, hK, hK'⟩ := (qhtFacts E a).2.2.2 R
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
    refine ⟨max M 0, fun g => ?_⟩
    rcases lt_or_ge R (qht g) with hg | hg
    · rw [hR g hg, norm_zero]; exact le_max_right _ _
    · obtain ⟨γ, t, hm⟩ := hK' g hg
      have := hM _ hm
      rw [mul_assoc, hF.left, hF.centre] at this
      exact this.trans (le_max_left _ _)
  · refine ⟨C, fun g => ?_⟩
    obtain ⟨t, ht⟩ := exists_split' g
    rw [← hF.centre t g, ht]
    exact hC _

end
