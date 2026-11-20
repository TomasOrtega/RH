import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ O W _ _ _ M F n hF β ν hν δ hδ`. Take `⟨hN, -, hcomm, -⟩` from `galBasic Ω F hF`. Establish `hk : (↑hδ.unit⁻¹ : O) * ((β δ : O) - 1) = 1` using `hδ.val_inv_mul`. Establish `h1 : ν 1 = 0`. Use `hν.add 1 (fixMu ℚ Ω F).one_mem 1 (fixMu ℚ Ω F).one_mem` as an intermediate fact.

Simplify using `using this`. Establish `hinv : ∀ u ∈ fixMu ℚ Ω F, ν u⁻¹ = -ν u`. Introduce `u hu`. Use `hν.add u hu u⁻¹ ((fixMu ℚ Ω F).inv_mem hu)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, h1]`.

Conclude with `eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact this.symm)`. Establish `hcm : ∀ g, g * δ * g⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F` using `fun g => hcomm g δ`. Use `⟨fun g => (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹), ⟨?_, ?_⟩, ?_, fun g => ⟨_, hcm g, _, rfl⟩⟩` and prove the remaining obligations. Establish `hc : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹ * δ⁻¹)`. Establish `c1 : Continuous (fun g : G ℚ Ω => g * δ)` using `continuous_mul_right δ`.

Establish `c2 : Continuous (fun g : G ℚ Ω => g⁻¹)` using `continuous_inv`. Establish `c3 : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹)` using `c1.mul c2`. Conclude with `(continuous_mul_right δ⁻¹).comp c3`. Establish `hf : Continuous (fun g : G ℚ Ω => (⟨g * δ * g⁻¹ * δ⁻¹, hcm g⟩ : fixMu ℚ Ω F))` using `hc.subtype_mk hcm`. Establish `hl : IsLocallyConstant (fun g : G ℚ Ω => ν (g * δ * g⁻¹ * δ⁻¹))` using `hν.lc.comp_continuous hf`.

Conclude with `hl.comp (fun w => (-(↑hδ.unit⁻¹ : O)) • w)`. Introduce `g h`. Establish `e : g * h * δ * (g * h)⁻¹ * δ⁻¹ = g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ * (g * δ * g⁻¹ * δ⁻¹)` using `by group`. Establish `hmem : g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ ∈ fixMu ℚ Ω F` using `hN.conj_mem _ (hcm h) g`. Use `show (-(↑hδ.unit⁻¹ : O)) • ν (g * h * δ * (g * h)⁻¹ * δ⁻¹) = (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹) + (β g : O) • ((-(↑hδ.unit⁻¹ : O)) • ν (h * δ * h⁻¹ * δ⁻¹))`.

Rewrite using `[e, hν.add _ hmem _ (hcm g), hν.eqv g _ (hcm h), smul_add, smul_comm (-(↑hδ.unit⁻¹ : O)) (β g : O)]`. Normalize the expressions using the abelian group laws. Introduce `u hu`. Establish `hconj : δ * u⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F` using `hN.conj_mem _ ((fixMu ℚ Ω F).inv_mem hu) δ`. Establish `e : u * δ * u⁻¹ * δ⁻¹ = u * (δ * u⁻¹ * δ⁻¹)` using `by group`.

Establish `e2 : ν u + (β δ : O) • -ν u = -(((β δ : O) - 1) • ν u)`. Rewrite using `[sub_smul, one_smul, smul_neg]`. Normalize the expressions using the abelian group laws. Use `show (-(↑hδ.unit⁻¹ : O)) • ν (u * δ * u⁻¹ * δ⁻¹) = ν u`. Rewrite using `[e, hν.add u hu _ hconj, hν.eqv δ u⁻¹ ((fixMu ℚ Ω F).inv_mem hu), hinv u hu, e2, smul_neg, neg_smul, neg_neg, smul_smul, hk, one_smul]`.
-/
theorem UpperTheory.V.ML.ext :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ), F ≠ 0 → ∀ (β : G ℚ Ω →* Oˣ) (ν : G ℚ Ω → W), IsNu M F n β ν → ∀ δ : G ℚ Ω, IsUnit ((β δ : O) - 1) →
    ∃ c : G ℚ Ω → W, IsCoc β c ∧ (∀ u ∈ fixMu ℚ Ω F, c u = ν u) ∧ ∀ g, ∃ u ∈ fixMu ℚ Ω F, ∃ y : O, c g = y • ν u := by
  intro Ω _ _ _ O W _ _ _ M F n hF β ν hν δ hδ
  obtain ⟨hN, -, hcomm, -⟩ := galBasic Ω F hF
  have hk : (↑hδ.unit⁻¹ : O) * ((β δ : O) - 1) = 1 := hδ.val_inv_mul
  have h1 : ν 1 = 0 := by
    have := hν.add 1 (fixMu ℚ Ω F).one_mem 1 (fixMu ℚ Ω F).one_mem
    simpa using this
  have hinv : ∀ u ∈ fixMu ℚ Ω F, ν u⁻¹ = -ν u := by
    intro u hu
    have := hν.add u hu u⁻¹ ((fixMu ℚ Ω F).inv_mem hu)
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact this.symm)
  have hcm : ∀ g, g * δ * g⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := fun g => hcomm g δ
  refine ⟨fun g => (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹), ⟨?_, ?_⟩, ?_, fun g => ⟨_, hcm g, _, rfl⟩⟩
  · have hc : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹ * δ⁻¹) := by
      have c1 : Continuous (fun g : G ℚ Ω => g * δ) := continuous_mul_right δ
      have c2 : Continuous (fun g : G ℚ Ω => g⁻¹) := continuous_inv
      have c3 : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹) := c1.mul c2
      exact (continuous_mul_right δ⁻¹).comp c3
    have hf : Continuous (fun g : G ℚ Ω => (⟨g * δ * g⁻¹ * δ⁻¹, hcm g⟩ : fixMu ℚ Ω F)) := hc.subtype_mk hcm
    have hl : IsLocallyConstant (fun g : G ℚ Ω => ν (g * δ * g⁻¹ * δ⁻¹)) := hν.lc.comp_continuous hf
    exact hl.comp (fun w => (-(↑hδ.unit⁻¹ : O)) • w)
  · intro g h
    have e : g * h * δ * (g * h)⁻¹ * δ⁻¹ = g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ * (g * δ * g⁻¹ * δ⁻¹) := by
      group
    have hmem : g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ (hcm h) g
    show (-(↑hδ.unit⁻¹ : O)) • ν (g * h * δ * (g * h)⁻¹ * δ⁻¹) =
      (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹) + (β g : O) • ((-(↑hδ.unit⁻¹ : O)) • ν (h * δ * h⁻¹ * δ⁻¹))
    rw [e, hν.add _ hmem _ (hcm g), hν.eqv g _ (hcm h), smul_add, smul_comm (-(↑hδ.unit⁻¹ : O)) (β g : O)]
    abel
  · intro u hu
    have hconj : δ * u⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ ((fixMu ℚ Ω F).inv_mem hu) δ
    have e : u * δ * u⁻¹ * δ⁻¹ = u * (δ * u⁻¹ * δ⁻¹) := by
      group
    have e2 : ν u + (β δ : O) • -ν u = -(((β δ : O) - 1) • ν u) := by
      rw [sub_smul, one_smul, smul_neg]
      abel
    show (-(↑hδ.unit⁻¹ : O)) • ν (u * δ * u⁻¹ * δ⁻¹) = ν u
    rw [e, hν.add u hu _ hconj, hν.eqv δ u⁻¹ ((fixMu ℚ Ω F).inv_mem hu), hinv u hu, e2, smul_neg, neg_smul,
      neg_neg, smul_smul, hk, one_smul]
