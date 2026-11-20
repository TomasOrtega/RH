import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkRam

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `K _ _ _`. Use `set I : Subgroup Gal(K/ℚ) := ⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ) with hI`. Establish `hconj : ∀ (τ : Gal(K/ℚ)) (w : HeightOneSpectrum (𝓞 K)), ∃ w' : HeightOneSpectrum (𝓞 K), ∀ σ ∈ w.asIdeal.inertia Gal(K/ℚ), τ * σ * τ⁻¹ ∈ w'.asIdeal.inertia Gal(K/ℚ)`. Introduce `τ w`. Use `⟨⟨τ • w.asIdeal, by haveI := w.isPrime; infer_instance, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `w.ne_bot` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `hx' : τ • x ∈ τ • w.asIdeal` using `Ideal.smul_mem_pointwise_smul τ x _ hx`.

Rewrite `hx'` using `[h, Ideal.mem_bot]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `(smul_eq_zero_iff_eq τ).mp hx'`. Introduce `σ hσ x`. Establish `hm` using `Ideal.smul_mem_pointwise_smul τ _ w.asIdeal (hσ (τ⁻¹ • x))`.

Rewrite `hm` using `[smul_sub, smul_inv_smul, ← mul_smul, ← mul_smul]`. Then use the resulting hypothesis. Use `haveI hN : I.Normal := by`. Prove the components needed by the constructor for the conclusion. Introduce `σ hσ τ`. Establish `hle : I ≤ I.comap (MulAut.conj τ).toMonoidHom`.

Use `iSup_le fun w => ?_` and prove the remaining obligations. Take `⟨w', hw'⟩` from `hconj τ w`. Introduce `σ' hσ'`. Conclude with `le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w' (hw' σ' hσ')`. Conclude with `hle hσ`.

Use `set F := IntermediateField.fixedField I with hF`. Use `haveI hFgal := IsGalois.of_fixedField_normal_subgroup I`. Use `haveI hgF : IsGalois ℚ F := by`. Use `hFgal` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.

Establish `hunr : ∀ p, Nat.Prime p → UnramAt F p`. Introduce `p hp`. Use `(UpperTheory.V.CF.ineFixQ F K p hp).mpr ?_` and prove the remaining obligations. Introduce `w _ σ hσ`. Rewrite using `[MonoidHom.mem_ker]`.

Use extensionality with `x`. Rewrite using `[AlgEquiv.one_apply]`. Establish `hc` using `UpperTheory.V.CF.resTo_commutes ℚ F K σ x`. Conclude with `hc.trans ((IntermediateField.mem_fixedField_iff I _).mp x.2 σ (le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w hσ))`. Establish `h1 : Module.finrank ℚ F = 1`.

Assume the negation of the conclusion as `h`. Take `⟨p, hp, hnot⟩` from `UpperTheory.V.CF.minkRam F h`. Conclude with `hnot (hunr p hp)`. Establish `hbot : F = ⊥` using `IntermediateField.finrank_eq_one_iff.mp h1`. Rewrite using `[← IntermediateField.fixingSubgroup_fixedField I, ← hF, hbot, IntermediateField.fixingSubgroup_bot]`.
-/
theorem UpperTheory.V.CF.minkGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K], (⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ)) = ⊤ := by
  intro K _ _ _
  set I : Subgroup Gal(K/ℚ) := ⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ) with hI
  have hconj : ∀ (τ : Gal(K/ℚ)) (w : HeightOneSpectrum (𝓞 K)), ∃ w' : HeightOneSpectrum (𝓞 K),
      ∀ σ ∈ w.asIdeal.inertia Gal(K/ℚ), τ * σ * τ⁻¹ ∈ w'.asIdeal.inertia Gal(K/ℚ) := by
    intro τ w
    refine ⟨⟨τ • w.asIdeal, by haveI := w.isPrime; infer_instance, ?_⟩, ?_⟩
    · intro h
      apply w.ne_bot
      rw [eq_bot_iff]
      intro x hx
      have hx' : τ • x ∈ τ • w.asIdeal := Ideal.smul_mem_pointwise_smul τ x _ hx
      rw [h, Ideal.mem_bot] at hx'
      rw [Ideal.mem_bot]
      exact (smul_eq_zero_iff_eq τ).mp hx'
    · intro σ hσ x
      have hm := Ideal.smul_mem_pointwise_smul τ _ w.asIdeal (hσ (τ⁻¹ • x))
      rwa [smul_sub, smul_inv_smul, ← mul_smul, ← mul_smul] at hm
  haveI hN : I.Normal := by
    constructor
    intro σ hσ τ
    have hle : I ≤ I.comap (MulAut.conj τ).toMonoidHom := by
      refine iSup_le fun w => ?_
      obtain ⟨w', hw'⟩ := hconj τ w
      intro σ' hσ'
      exact le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w' (hw' σ' hσ')
    exact hle hσ
  set F := IntermediateField.fixedField I with hF
  haveI hFgal := IsGalois.of_fixedField_normal_subgroup I
  haveI hgF : IsGalois ℚ F := by
    convert hFgal
    exact Subsingleton.elim _ _
  have hunr : ∀ p, Nat.Prime p → UnramAt F p := by
    intro p hp
    refine (UpperTheory.V.CF.ineFixQ F K p hp).mpr ?_
    intro w _ σ hσ
    rw [MonoidHom.mem_ker]
    ext x
    rw [AlgEquiv.one_apply]
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F K σ x
    exact hc.trans ((IntermediateField.mem_fixedField_iff I _).mp x.2 σ
      (le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w hσ))
  have h1 : Module.finrank ℚ F = 1 := by
    by_contra h
    obtain ⟨p, hp, hnot⟩ := UpperTheory.V.CF.minkRam F h
    exact hnot (hunr p hp)
  have hbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  rw [← IntermediateField.fixingSubgroup_fixedField I, ← hF, hbot,
    IntermediateField.fixingSubgroup_bot]
