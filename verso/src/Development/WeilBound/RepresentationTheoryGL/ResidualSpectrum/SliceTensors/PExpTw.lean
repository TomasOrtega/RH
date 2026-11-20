import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem expTw_holds : ExpTw := by
  intro E _ _ _ N φ z _ r _ hrN c hc
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩ := hc
  set χ := Model.absC E z
  set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY
  have hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1 := fun x => by
    change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
    rw [det_unip, map_one]
  have hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ) := by
    rw [hF₀]
    funext g
    simp only [PositivityTheory.Affgl.CT.ct]
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [mulChi_apply, map_mul, hu, one_mul]
  have hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1 := fun g => Units.mul_inv _
  have hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := fun t => by
    simp only [hY]
    rw [Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]
  refine ⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) =
        ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) := by
      funext g
      simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]
      linear_combination (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro h
    apply hF0
    funext g
    have h2 := congrFun h g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2
    have h3 : Y g ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.1 h2).resolve_right h3
  · intro t g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply]
    have hYm : ∀ a b, Y (a * b) = Y a * Y b := fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]
    have e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) =
        Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hFt, hYm, hYa, e]
    ring

end PositivityTheory.Rg.Rs
