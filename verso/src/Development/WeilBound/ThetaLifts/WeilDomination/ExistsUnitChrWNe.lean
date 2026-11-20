import Development.WeilBound.ThetaLifts.WeilDomination.FacNeGauss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

noncomputable section

namespace PositivityTheory.ThK.Close

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}

/- English proof (translation)
The claim follows from `(continuous_locChar hχ (splitPrime τ)).comp (Continuous.units_map _ (SplitChart.continuous_complMap (splitPrime_under τ)))`.
-/
theorem continuous_chrW' {χ : Chr F E} (hχ : Continuous χ) (τ : E →ₐ[F] Fv F v) :
    Continuous fun x => (chrW χ τ x : ℂ) :=
  (continuous_locChar hχ (splitPrime τ)).comp
    (Continuous.units_map _ (SplitChart.continuous_complMap (splitPrime_under τ)))

/- English proof (translation)
Take `⟨ψ, h1, -, h3, -⟩` from `SplitChart.exists_equiv_complMap τ (splitPrime_under τ)`. Simplify using `only [UnrAt, not_forall] at h`. Take `⟨y, hy, hne⟩` from `h`. Establish `e : Units.map (complMap (splitPrime_under τ)).toMonoidHom (Units.map ψ.symm.toRingHom.toMonoidHom y) = y` using `Units.ext ((h1 _).symm.trans (ψ.apply_symm_apply _))`. Establish `hv : Valued.v ((Units.map ψ.symm.toRingHom.toMonoidHom y : (Fv F v)ˣ) : Fv F v) = 1`.

Rewrite using `[← h3]`. Conclude with `(congrArg Valued.v (ψ.apply_symm_apply (y : _))).trans hy`. Use `⟨Units.map ψ.symm.toRingHom.toMonoidHom y, ?_, ?_, fun h0 => hne ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hv.le`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]`. Rewrite using `[← e]`. Conclude with `h0`.
-/
theorem exists_unit_chrW_ne {χ : Chr F E} (τ : E →ₐ[F] Fv F v) (h : ¬ UnrAt χ (splitPrime τ)) :
    ∃ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F ∧ chrW χ τ x ≠ 1 := by
  obtain ⟨ψ, h1, -, h3, -⟩ := SplitChart.exists_equiv_complMap τ (splitPrime_under τ)
  simp only [UnrAt, not_forall] at h
  obtain ⟨y, hy, hne⟩ := h
  have e : Units.map (complMap (splitPrime_under τ)).toMonoidHom (Units.map ψ.symm.toRingHom.toMonoidHom y) = y :=
    Units.ext ((h1 _).symm.trans (ψ.apply_symm_apply _))
  have hv : Valued.v ((Units.map ψ.symm.toRingHom.toMonoidHom y : (Fv F v)ˣ) : Fv F v) = 1 := by
    rw [← h3]
    exact (congrArg Valued.v (ψ.apply_symm_apply (y : _))).trans hy
  refine ⟨Units.map ψ.symm.toRingHom.toMonoidHom y, ?_, ?_, fun h0 => hne ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hv.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  · rw [← e]
    exact h0

/- English proof (translation)
The claim follows from `mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.2 (one_lt_absNorm v).ne_bot)) h) (pow_ne_zero _ (Units.ne_zero _))`.
-/
theorem eps_ne_zero {ψ : AddChar (AF F) ℂ} {ν : (Fv F v)ˣ →* ℂˣ} (h : gauss ψ ν ≠ 0) (z : ℤ) : eps ψ ν z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.2 (one_lt_absNorm v).ne_bot)) h)
    (pow_ne_zero _ (Units.ne_zero _))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' h e₁ e₂ s 𝔟 𝔠 z`. Use `⟨mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun v hv => ?_), fun k hk => ?_⟩` and prove the remaining obligations. Establish `hv' : v.1 ∈ X.T` using `by simpa using hv`. Establish `hc : Continuous X.ν` using `h.chars.heckeα.1.div' h.chars.heckeβ.1`. Use `mul_ne_zero (Units.ne_zero _) (eps_ne_zero (GaussNe.gauss_ne_zero _ _ _ (h.base.psiP _ v.2) (continuous_chrW' hc _) (exists_unit_chrW_ne _ (h.chars.ram _ ?_))) z)` and prove the remaining obligations.

Rewrite using `[splitPrime_under]` and apply the resulting hypothesis. Use `(converges_charFam _ X.ν ?_).ne_zero` and prove the remaining obligations. Rewrite using `[Complex.natCast_re]`. Conclude with `hk` after adjusting the coercions.
-/
theorem facNe : GlobalTheory.ThK.FacNe := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' h e₁ e₂ s 𝔟 𝔠 z
  refine ⟨mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun v hv => ?_), fun k hk => ?_⟩
  · have hv' : v.1 ∈ X.T := by simpa using hv
    have hc : Continuous X.ν := h.chars.heckeα.1.div' h.chars.heckeβ.1
    refine mul_ne_zero (Units.ne_zero _) (eps_ne_zero (GaussNe.gauss_ne_zero _ _ _ (h.base.psiP _ v.2)
      (continuous_chrW' hc _) (exists_unit_chrW_ne _ (h.chars.ram _ ?_))) z)
    rwa [splitPrime_under]
  · refine (converges_charFam _ X.ν ?_).ne_zero
    rw [Complex.natCast_re]
    exact_mod_cast hk

end PositivityTheory.ThK.Close
