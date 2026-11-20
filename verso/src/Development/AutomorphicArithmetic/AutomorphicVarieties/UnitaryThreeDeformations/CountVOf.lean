import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbstractCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostDataOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostLocVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostPhi
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsIsUniv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Establish `hp : 0 ≤ X ^ C` using `pow_nonneg (by linarith) C`. Break down `Nat.eq_zero_or_pos E with rfl | hE` into its components or cases. Simplify using `only [Nat.cast_zero, div_zero, zero_mul]`. Conclude with `pow_nonneg (by linarith) _`. Establish `hE' : (0 : ℝ) < E` using `by exact_mod_cast hE`.

Establish `ha' : (a : ℝ) ≤ V` using `by exact_mod_cast ha`. Establish `h1 : (a : ℝ) / E ≤ 2 * s`. Rewrite using `[div_le_iff₀ hE']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `mul_le_mul_of_nonneg_right h1 hL`.

Establish `h3` using `mul_le_mul_of_nonneg_left hX hp`. Rewrite using `[pow_succ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem arith {a V E : ℕ} {s L X : ℝ} {C : ℕ} (ha : a ≤ V) (hV : (V : ℝ) ≤ 2 * E * s) (hL : 0 ≤ L)
    (hs : s * L ≤ X ^ C) (hX : 2 ≤ X) : (a : ℝ) / E * L ≤ X ^ (C + 1) := by
  have hp : 0 ≤ X ^ C := pow_nonneg (by linarith) C
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    exact pow_nonneg (by linarith) _
  · have hE' : (0 : ℝ) < E := by exact_mod_cast hE
    have ha' : (a : ℝ) ≤ V := by exact_mod_cast ha
    have h1 : (a : ℝ) / E ≤ 2 * s := by
      rw [div_le_iff₀ hE']
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hL
    have h3 := mul_le_mul_of_nonneg_left hX hp
    rw [pow_succ]
    linarith

/- English proof (translation)
Use `haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1`. Establish `h : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l]`. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _`. Use `map_nonunit (algebraMap ℤ_[l] c.O) _ h` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
private theorem l_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  have h : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have := map_nonunit (algebraMap ℤ_[l] c.O) _ h
  rwa [map_natCast] at this
