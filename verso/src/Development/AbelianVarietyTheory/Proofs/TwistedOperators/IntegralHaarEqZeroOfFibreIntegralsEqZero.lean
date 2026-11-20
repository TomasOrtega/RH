import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ μ hμ P Q hP hQ hcomm hgen hdisj F hF`. Use `haveI : LocallyCompactSpace P := hP.locallyCompactSpace`. Use `haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace`. Use `haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set H)`. Use `haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set H)`.

Use `haveI : BorelSpace P := Subtype.borelSpace (P : Set H)`. Use `haveI : BorelSpace Q := Subtype.borelSpace (Q : Set H)`. Set `m : P × Q →* H` to `{ toFun := fun x => (x.1 : H) * x.2 map_one' := by simp map_mul' := by`. Introduce and unpack `⟨p, q⟩ ⟨p', q'⟩`. Simplify using `only [Prod.mk_mul_mk, Subgroup.coe_mul]`.

Establish `h` using `hcomm p' p'.2 q q.2`. Combine the equalities or inequalities in the displayed calculation. Establish `hm : ∀ x : P × Q, m x = (x.1 : H) * x.2` using `fun _ => rfl`. Establish `hcont : Continuous m` using `(continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)`. Establish `hsurj : Function.Surjective m`.

Introduce `h`. Take `⟨p, hp, q, hq, rfl⟩` from `hgen h`. Conclude with `⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩`. Establish `hinj : Function.Injective m`. Rewrite using `[injective_iff_map_eq_one]`.

Introduce and unpack `⟨p, q⟩ h`. Rewrite `h` using `[hm]`. Establish `h1 : (p : H) = (q : H)⁻¹` using `eq_inv_of_mul_eq_one_left h`. Establish `hp1 : (p : H) = 1` using `hdisj p p.2 (h1 ▸ Q.inv_mem q.2)`. Establish `hq1 : (q : H) = 1` using `by simpa [hp1] using h`.

Conclude with `Prod.ext (Subtype.ext hp1) (Subtype.ext hq1)`. Establish `hopen : IsOpenMap m` using `m.isOpenMap_of_sigmaCompact hsurj hcont`. Set `e : (P × Q) ≃* H` to `MulEquiv.ofBijective m ⟨hinj, hsurj⟩`. Set `φ : (P × Q) ≃ₜ H` to `e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen`. Set `νP : Measure P` to `Measure.haar`.

Set `νQ : Measure Q` to `Measure.haar`. Use `haveI : νP.IsHaarMeasure := inferInstance`. Use `haveI : νQ.IsHaarMeasure := inferInstance`. Use `haveI : (νP.prod νQ).IsHaarMeasure := inferInstance`. Use `haveI : ((νP.prod νQ).map e).IsHaarMeasure := e.isHaarMeasure_map (νP.prod νQ) φ.continuous φ.symm.continuous`.

Establish `hμeq` using `Measure.isMulLeftInvariant_eq_smul μ ((νP.prod νQ).map e)`. Establish `hzero : ∫ h, F h ∂((νP.prod νQ).map e) = 0`. Establish `hemb : MeasurableEmbedding e` using `φ.measurableEmbedding`. Rewrite using `[hemb.integral_map]`. Distinguish the cases in `hint : Integrable (fun x => F (e x)) (νP.prod νQ)`.

Rewrite using `[integral_prod_symm _ hint]`. Establish `: ∀ q : Q, ∫ p : P, F (e (p, q)) ∂νP = 0` using `fun q => hF νP inferInstance q q.2`. Simplify using `[this]`. Conclude with `integral_undef hint`. Rewrite using `[hμeq, integral_smul_nnreal_measure, hzero, smul_zero]`.
-/
theorem integral_haar_eq_zero_of_fibre_integrals_eq_zero :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  intro H _ _ _ _ _ _ _ _ μ hμ P Q hP hQ hcomm hgen hdisj F hF
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set H)
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set H)
  haveI : BorelSpace P := Subtype.borelSpace (P : Set H)
  haveI : BorelSpace Q := Subtype.borelSpace (Q : Set H)
  let m : P × Q →* H :=
    { toFun := fun x => (x.1 : H) * x.2
      map_one' := by simp
      map_mul' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
        have h := hcomm p' p'.2 q q.2
        calc (p : H) * p' * (q * q') = p * (p' * q) * q' := by simp only [mul_assoc]
          _ = p * (q * p') * q' := by rw [h]
          _ = p * q * (p' * q') := by simp only [mul_assoc] }
  have hm : ∀ x : P × Q, m x = (x.1 : H) * x.2 := fun _ => rfl
  have hcont : Continuous m :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective m := by
    intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := hgen h
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, q⟩ h
    rw [hm] at h
    have h1 : (p : H) = (q : H)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hp1 : (p : H) = 1 := hdisj p p.2 (h1 ▸ Q.inv_mem q.2)
    have hq1 : (q : H) = 1 := by simpa [hp1] using h
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hq1)
  have hopen : IsOpenMap m := m.isOpenMap_of_sigmaCompact hsurj hcont
  let e : (P × Q) ≃* H := MulEquiv.ofBijective m ⟨hinj, hsurj⟩
  let φ : (P × Q) ≃ₜ H := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  let νP : Measure P := Measure.haar
  let νQ : Measure Q := Measure.haar
  haveI : νP.IsHaarMeasure := inferInstance
  haveI : νQ.IsHaarMeasure := inferInstance
  haveI : (νP.prod νQ).IsHaarMeasure := inferInstance
  haveI : ((νP.prod νQ).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (νP.prod νQ) φ.continuous φ.symm.continuous
  have hμeq := Measure.isMulLeftInvariant_eq_smul μ ((νP.prod νQ).map e)
  have hzero : ∫ h, F h ∂((νP.prod νQ).map e) = 0 := by
    have hemb : MeasurableEmbedding e := φ.measurableEmbedding
    rw [hemb.integral_map]
    by_cases hint : Integrable (fun x => F (e x)) (νP.prod νQ)
    · rw [integral_prod_symm _ hint]
      have : ∀ q : Q, ∫ p : P, F (e (p, q)) ∂νP = 0 := fun q => hF νP inferInstance q q.2
      simp [this]
    · exact integral_undef hint
  rw [hμeq, integral_smul_nnreal_measure, hzero, smul_zero]

end GlobalTheory
