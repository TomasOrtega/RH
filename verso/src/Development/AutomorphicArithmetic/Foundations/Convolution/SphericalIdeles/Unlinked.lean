import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteCharacterNorms.UnitExponentHolds
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.CBC

/- English proof (translation)
Introduce `K _ _ _ n hn π v B hB a ha b hb hab`. Establish `hB' : (CG.mk π).HasSat v B` using `hB`. Take `⟨ν, hν, h⟩` from `PositivityTheory.RgJS.unit_exponent_holds K`. Take `⟨π₀, t, hu, he⟩` from `h n (CG.mk π) hn`. Establish `hχ : ((ν t)⁻¹).UnrAt v` using `fun x hx => by`.

Express the relevant statement in the definitionally equal form `((ν t).loc v x)⁻¹ = 1`. Rewrite using `[(hν t).1 v x hx, inv_one]`. Establish `e0 : (CG.mk π).twist (ν t)⁻¹ = π₀`. Rewrite using `[he, ← CG.twist_mul, mul_inv_cancel, CG.twist_one]`. Establish `hS : π₀.HasSat v (B.map (· * ((ν t)⁻¹).val v))` using `e0 ▸ PositivityTheory.RgJS.satake_twist_holds K n (CG.mk π) (ν t)⁻¹ v B hχ hB'`.

Establish `hJ` using `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound K n π₀ hu v _ hS`. Establish `h1` using `(hJ _ (Multiset.mem_map_of_mem _ ha)).2`. Establish `h2` using `(hJ _ (Multiset.mem_map_of_mem _ hb)).1`. Establish `hq : (1 : ℝ) < Ideal.absNorm v.asIdeal`. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm v` after adjusting the coercions.

Establish `hq0 : (0 : ℝ) < Ideal.absNorm v.asIdeal` using `by linarith`. Simplify using `only [Units.val_mul, norm_mul] at h1 h2`. Establish `ha' : ‖(a : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) * ‖(b : ℂ)‖`. Rewrite using `[hab, norm_mul]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[ha', mul_assoc]`. Establish `h3 : (Ideal.absNorm v.asIdeal : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ)` using `by nth_rewrite 1 [← Real.rpow_one (Ideal.absNorm v.asIdeal : ℝ)]`. Rewrite using `[← Real.rpow_add hq0]`. Evaluate the numerical expressions. Establish `h4` using `mul_lt_mul_of_pos_left h2 hq0`.

Rewrite `h4` using `[h3]`. Conclude with `absurd h1 (not_lt.2 h4.le)`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.unlinked :
    UpperTheory.ConvolutionTheory.Sph.Unlinked := by
  intro K _ _ _ n hn π v B hB a ha b hb hab
  have hB' : (CG.mk π).HasSat v B := hB
  obtain ⟨ν, hν, h⟩ := PositivityTheory.RgJS.unit_exponent_holds K
  obtain ⟨π₀, t, hu, he⟩ := h n (CG.mk π) hn
  have hχ : ((ν t)⁻¹).UnrAt v := fun x hx => by
    change ((ν t).loc v x)⁻¹ = 1
    rw [(hν t).1 v x hx, inv_one]
  have e0 : (CG.mk π).twist (ν t)⁻¹ = π₀ := by
    rw [he, ← CG.twist_mul, mul_inv_cancel, CG.twist_one]
  have hS : π₀.HasSat v (B.map (· * ((ν t)⁻¹).val v)) :=
    e0 ▸ PositivityTheory.RgJS.satake_twist_holds K n (CG.mk π) (ν t)⁻¹ v B hχ hB'
  have hJ := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound K n π₀ hu v _ hS
  have h1 := (hJ _ (Multiset.mem_map_of_mem _ ha)).2
  have h2 := (hJ _ (Multiset.mem_map_of_mem _ hb)).1
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by linarith
  simp only [Units.val_mul, norm_mul] at h1 h2
  have ha' : ‖(a : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) * ‖(b : ℂ)‖ := by
    rw [hab, norm_mul]
    simp
  rw [ha', mul_assoc] at h1
  have h3 : (Ideal.absNorm v.asIdeal : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one (Ideal.absNorm v.asIdeal : ℝ)]
    rw [← Real.rpow_add hq0]
    norm_num
  have h4 := mul_lt_mul_of_pos_left h2 hq0
  rw [h3] at h4
  exact absurd h1 (not_lt.2 h4.le)
