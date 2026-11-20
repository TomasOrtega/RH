import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

/- English proof (translation)
Introduce `hC hI G _ _ _ _ _ _ _ _ μG hμ H H' y hH hc hy μ μ' h1 h2 hm F hF hFH`. Establish `hy' : ∀ z, z ∈ H' ↔ y * z * y⁻¹ ∈ H` using `fun z => by rw [hy]; simp [mul_assoc]`. Establish `hH' : IsClosed (H' : Set G)`. Establish `: (H' : Set G) = (fun z => y * z * y⁻¹) ⁻¹' H` using `Set.ext hy'`. Rewrite using `[this]`.

Conclude with `hH.preimage (by fun_prop)`. Establish `hc' : ∀ a ∈ H', ∀ b ∈ H', Commute a b` using `fun a ha b hb => by`. Use `(hc _ ((hy' a).1 ha) _ ((hy' b).1 hb)).eq` as an intermediate fact. Establish `h : y * a * b = y * b * a` using `by simpa [← mul_assoc] using this`. Rewrite `h` using `[mul_assoc, mul_assoc]`.

Conclude with `mul_left_cancel h`. Take `⟨s1, i1, -⟩` from `hC G H hH hc μ h1`. Take `⟨s2, i2, -⟩` from `hC G H' hH' hc' μ' h2`. Establish `key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h : H, f (y⁻¹ * h * y) ∂μ = ∫⁻ h : H', f h ∂μ'` using `fun f hf => by`. Rewrite using `[← lintegral_map hf (g := fun x : H => y⁻¹ * (x : G) * y) (by fun_prop), hm, lintegral_map hf (g := fun x : H' => (x : G)) measurable_subtype_coe]`.

Distinguish the cases in `hex : ∃ ρ, IsQuotNormaliser H μ ρ`. Take `⟨ρ, hρ⟩` from `hex`. Establish `hρ' : IsQuotNormaliser H' μ' fun g => ρ (y * g)` using `⟨hρ.1.comp (measurable_const_mul y), fun g => by`. Rewrite using `[← key (fun z => ρ (y * (z * g))) (hρ.1.comp (by fun_prop)), ← hρ.2 (y * g)]`. Conclude with `lintegral_congr fun h => by simp [mul_assoc]⟩`.

Rewrite using `[hI G μG hμ H μ s1 i1 F hF hFH ρ hρ, hI G μG hμ H' μ' s2 i2 (fun g => F (y * g)) (hF.comp (measurable_const_mul y)) (fun h hh g => by`. Rewrite using `[← hFH _ ((hy' h).1 hh) (y * g)]`. Simplify using `[mul_assoc]) _ hρ']`. Conclude with `integral_mul_left_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y`. Establish `hex' : ¬ ∃ ρ, IsQuotNormaliser H' μ' ρ` using `fun ⟨ρ, hρ⟩ => hex ⟨fun g => ρ (y⁻¹ * g), hρ.1.comp (measurable_const_mul _), fun g => by`.

Rewrite using `[← hρ.2 (y⁻¹ * g), ← key (fun z => ρ (z * (y⁻¹ * g))) (hρ.1.comp (by fun_prop))]`. Conclude with `lintegral_congr fun h => by simp [mul_assoc]⟩`. Rewrite using `[quotIntegral, quotIntegral, dif_neg hex, dif_neg hex']`.
-/
theorem UpperTheory.V.Z.Tf.Orb.quotConj :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotConj := by
  intro hC hI G _ _ _ _ _ _ _ _ μG hμ H H' y hH hc hy μ μ' h1 h2 hm F hF hFH
  have hy' : ∀ z, z ∈ H' ↔ y * z * y⁻¹ ∈ H := fun z => by rw [hy]; simp [mul_assoc]
  have hH' : IsClosed (H' : Set G) := by
    have : (H' : Set G) = (fun z => y * z * y⁻¹) ⁻¹' H := Set.ext hy'
    rw [this]
    exact hH.preimage (by fun_prop)
  have hc' : ∀ a ∈ H', ∀ b ∈ H', Commute a b := fun a ha b hb => by
    have := (hc _ ((hy' a).1 ha) _ ((hy' b).1 hb)).eq
    have h : y * a * b = y * b * a := by simpa [← mul_assoc] using this
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  obtain ⟨s1, i1, -⟩ := hC G H hH hc μ h1
  obtain ⟨s2, i2, -⟩ := hC G H' hH' hc' μ' h2
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h : H, f (y⁻¹ * h * y) ∂μ = ∫⁻ h : H', f h ∂μ' := fun f hf => by
    rw [← lintegral_map hf (g := fun x : H => y⁻¹ * (x : G) * y) (by fun_prop), hm,
      lintegral_map hf (g := fun x : H' => (x : G)) measurable_subtype_coe]
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H' μ' fun g => ρ (y * g) := ⟨hρ.1.comp (measurable_const_mul y), fun g => by
      rw [← key (fun z => ρ (y * (z * g))) (hρ.1.comp (by fun_prop)), ← hρ.2 (y * g)]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [hI G μG hμ H μ s1 i1 F hF hFH ρ hρ, hI G μG hμ H' μ' s2 i2 (fun g => F (y * g)) (hF.comp (measurable_const_mul y)) (fun h hh g => by
      rw [← hFH _ ((hy' h).1 hh) (y * g)]; simp [mul_assoc]) _ hρ']
    exact integral_mul_left_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' μ' ρ := fun ⟨ρ, hρ⟩ => hex ⟨fun g => ρ (y⁻¹ * g), hρ.1.comp (measurable_const_mul _), fun g => by
      rw [← hρ.2 (y⁻¹ * g), ← key (fun z => ρ (z * (y⁻¹ * g))) (hρ.1.comp (by fun_prop))]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [quotIntegral, quotIntegral, dif_neg hex, dif_neg hex']
