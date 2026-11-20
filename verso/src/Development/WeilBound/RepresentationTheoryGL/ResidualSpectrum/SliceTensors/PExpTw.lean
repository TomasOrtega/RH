import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
Introduce `E _ _ _ N φ z _ r _ hrN c hc`. Set `_ : MeasurableSpace (BlockIx N r → Ad E)` to `borel _`. Take `⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩` from `hc`. Use `set χ := Model.absC E z`. Use `set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY`.

Establish `hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1` using `fun x => by`. Express the relevant statement in the definitionally equal form `(χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1`. Rewrite using `[det_unip, map_one]`. Establish `hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ)`. Rewrite using `[hF₀]`.

Use function extensionality and compare the values at `g`. Simplify using `only [PositivityTheory.Affgl.CT.ct]`. Rewrite using `[← integral_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[mulChi_apply, map_mul, hu, one_mul]`. Establish `hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1` using `fun g => Units.mul_inv _`. Establish `hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t))` using `fun t => by`. Simplify using `only [hY]`. Rewrite using `[Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]`.

Use `⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF`. Rewrite `h1` using `[Submodule.map_span]`. Use `Submodule.span_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨t, rfl⟩, rfl⟩`.

Establish `e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) = ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g)`. Use function extensionality and compare the values at `g`. Simplify using `only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]`. Take the linear combination `(PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)`. Introduce `h`. Apply `hF0` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `h2` using `congrFun h g`.

Simplify using `only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2`. Establish `h3 : Y g ≠ 0` using `Units.ne_zero _`. Conclude with `(mul_eq_zero.1 h2).resolve_right h3`. Introduce `t g`. Simplify using `only [LinearMap.mulRight_apply, Pi.mul_apply]`.

Establish `hYm : ∀ a b, Y (a * b) = Y a * Y b` using `fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]`. Establish `e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) = Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t))`. Rewrite using `[← Complex.exp_add]`. Put the polynomial expressions in normal form. Rewrite using `[hFt, hYm, hYa, e]`.

Expand and normalize the polynomial expressions, which then agree.
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
