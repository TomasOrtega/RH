import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.FieldsLaws

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
The claim follows from `(H.gal).apply_symm_apply g`.
-/
theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

/- English proof (translation)
The claim follows from `(H.gal).symm_apply_apply σ`.
-/
theorem sigmaOf_galE (σ : H.E ≃ₐ[ℚ] H.E) : H.sigmaOf (H.galE σ) = σ :=
  (H.gal).symm_apply_apply σ

/- English proof (translation)
Apply `(H.gal).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, mul_comm]`.
-/
theorem gal_comm (s t : H.E ≃ₐ[ℚ] H.E) : s * t = t * s := by
  apply (H.gal).injective
  rw [map_mul, map_mul, mul_comm]

/- English proof (translation)
Establish `hG : IsGalois ℚ H.E` using `H.hostE_isGalois`. Establish `key : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ H.K.fixingSubgroup ↔ H.galE σ ∈ R.Psi`. Introduce `σ`. Rewrite using `[H.galE_mem_Psi_iff, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `h _ (IntermediateField.mem_adjoin_simple_self ℚ _)`. Introduce `h y hy`. Establish `hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ)`. Use `IntermediateField.adjoin_simple_le_iff.2 ?_` and prove the remaining obligations.

Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `f hf`. Establish `: Subgroup.zpowers σ ≤ MulAction.stabilizer _ (H.sqd)`. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `h`.

Conclude with `this hf`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (hle hy) σ (Subgroup.mem_zpowers σ)`. Prove the components needed by the constructor for the conclusion. Introduce `hx τ`. Establish `h : H.sigmaOf τ ∈ H.K.fixingSubgroup`.

Rewrite using `[key, galE_sigmaOf]`. Conclude with `τ.2`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hx`. Introduce `hx`. Rewrite using `[← IsGalois.fixedField_fixingSubgroup H.K, IntermediateField.mem_fixedField_iff]`.

Introduce `σ hσ`. Use `hx ⟨_, (key σ).1 hσ⟩` as an intermediate fact. Rewrite `this` using `[sigmaOf_galE]`. Then use the resulting hypothesis.
-/
theorem mem_K_iff (x : H.E) : x ∈ H.K ↔ ∀ τ : R.Psi, H.sigmaOf τ x = x := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have key : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ H.K.fixingSubgroup ↔ H.galE σ ∈ R.Psi := by
    intro σ
    rw [H.galE_mem_Psi_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      exact h _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    · intro h y hy
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ (H.sqd) := by
          rw [Subgroup.zpowers_le]
          exact h
        exact this hf
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hy) σ (Subgroup.mem_zpowers σ)
  constructor
  · intro hx τ
    have h : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [key, galE_sigmaOf]
      exact τ.2
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hx
  · intro hx
    rw [← IsGalois.fixedField_fixingSubgroup H.K, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have := hx ⟨_, (key σ).1 hσ⟩
    rwa [sigmaOf_galE] at this

/- English proof (translation)
Establish `hcm : IsCMField H.E` using `H.isCMField_hostE`. Introduce `hle`. Take `⟨π, hπ⟩` from `(P.under (𝓞 H.F)).intValuation_exists_uniformizer`. Establish `hmem : π ∈ (P.under (𝓞 H.F)).asIdeal`. Use `((P.under (𝓞 H.F)).intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `h2 : algebraMap (𝓞 H.F) (𝓞 H.E) π ∈ P.asIdeal ^ 2` using `hle (Ideal.mem_map_of_mem _ hmem)`. Establish `h3` using `(P.intValuation_le_pow_iff_mem _ 2).2 h2`. Establish `h4` using `HostCM.valuation_eq_of_unram H.E (fun P hP h0 h => H.der.unramEF P hP h0 fun x => by`. Establish `hx : H.conj • x = IsCMField.complexConj H.E • x` using `RingOfIntegers.ext (H.φ₀.injective ((H.conjE_apply H.φ₀ x).trans (IsCMField.complexEmbedding_complexConj H.E H.φ₀ x).symm))`.

Rewrite using `[hx]`. Conclude with `h x) P (π : H.F)`. Establish `h5 : P.valuation H.E (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) π)) = (P.under (𝓞 H.F)).valuation H.F (algebraMap (𝓞 H.F) H.F π)` using `h4`. Rewrite `h5` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ]`. Rewrite `h3` using `[h5, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem unram (P : HeightOneSpectrum (𝓞 H.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 H.F) (𝓞 H.E))).map (algebraMap (𝓞 H.F) (𝓞 H.E)) ≤ P.asIdeal ^ 2 := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  intro hle
  obtain ⟨π, hπ⟩ := (P.under (𝓞 H.F)).intValuation_exists_uniformizer
  have hmem : π ∈ (P.under (𝓞 H.F)).asIdeal := by
    have := ((P.under (𝓞 H.F)).intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) π ∈ P.asIdeal ^ 2 := hle (Ideal.mem_map_of_mem _ hmem)
  have h3 := (P.intValuation_le_pow_iff_mem _ 2).2 h2
  have h4 := HostCM.valuation_eq_of_unram H.E (fun P hP h0 h =>
    H.der.unramEF P hP h0 fun x => by
      have hx : H.conj • x = IsCMField.complexConj H.E • x :=
        RingOfIntegers.ext (H.φ₀.injective ((H.conjE_apply H.φ₀ x).trans
          (IsCMField.complexEmbedding_complexConj H.E H.φ₀ x).symm))
      rw [hx]
      exact h x) P (π : H.F)
  have h5 : P.valuation H.E (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) π)) =
      (P.under (𝓞 H.F)).valuation H.F (algebraMap (𝓞 H.F) H.F π) := h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ] at h5
  rw [h5, WithZero.exp_le_exp] at h3
  omega

end Host

variable (B : Base)

/- English proof (translation)
Apply `B.embLL.injective` to reduce the goal to its premises. Rewrite using `[B.starLL_cx]`. Conclude with `B.host.conjE_apply (B.embLL.comp B.embE) x`.
-/
theorem embE_conj (x : B.host.E) : B.embE (B.host.conj x) = star (B.embE x) := by
  apply B.embLL.injective
  rw [B.starLL_cx]
  exact B.host.conjE_apply (B.embLL.comp B.embE) x

/- English proof (translation)
Rewrite using `[Formalism.L2.Geo.emb_mul_cc_comp, ← B.fields_embC]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Conclude with `congrArg (fun y => B.embLL (B.tauLL τ y)) (B.fields_sig x)`.
-/
theorem embLL_comp_embBar (τ : Tau B.R) :
    B.embLL.comp (B.fields.embBar τ) = B.host.emb ((τ : B.R.GG) * B.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp, ← B.fields_embC]
  refine RingHom.ext fun x => ?_
  exact congrArg (fun y => B.embLL (B.tauLL τ y)) (B.fields_sig x)

/- English proof (translation)
The claim follows from `B.fields_embC τ`.
-/
theorem embLL_comp_emb (τ : Tau B.R) : B.embLL.comp (B.fields.emb τ) = B.host.emb (τ : B.R.GG) :=
  B.fields_embC τ

/- English proof (translation)
Rewrite using `[mem_K_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h τ`. Establish `h1` using `B.embE.injective (h τ (1 : B.R.Psi))`. Establish `h2 : B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) = 1` using `map_one (B.host.gal).symm`.

Establish `h3 : B.host.sigmaOf τ x = B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) x` using `h1`. Rewrite using `[h3, h2]`. Both sides reduce to the same expression. Introduce `h τ τ'`. Rewrite using `[B.fields_emb_apply, B.fields_emb_apply, h τ, h τ']`.
-/
theorem mem_Kq_iff (x : B.host.E) : x ∈ B.fields.Kq ↔ x ∈ B.host.K := by
  rw [mem_K_iff]
  constructor
  · intro h τ
    have h1 := B.embE.injective (h τ (1 : B.R.Psi))
    have h2 : B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) = 1 := map_one (B.host.gal).symm
    have h3 : B.host.sigmaOf τ x = B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) x := h1
    rw [h3, h2]
    rfl
  · intro h τ τ'
    rw [B.fields_emb_apply, B.fields_emb_apply, h τ, h τ']

/- English proof (translation)
Establish `hcm : IsCMField B.host.E` using `B.host.isCMField_hostE`. Use `letI := B.host.cmStar`. Establish `cm` using `host_cmData B.R B.host`. Establish `hinj : ∀ {φ ψ : B.host.E →+* B.LL}, B.embLL.comp φ = B.embLL.comp ψ → φ = ψ` using `fun h => RingHom.ext fun x => B.embLL.injective (RingHom.congr_fun h x)`. Use `{ realF := cm.totReal rankE := cm.deg2 star_F := fun x => (cm.fixed _).2 ⟨x, rfl⟩ conjE := fun φ x => ?_ cplxE := inferInstanceAs (IsTotallyComplex B.host.E) emb_star := fun τ x => ?_ card_Tau := ?_ emb_inj := fun τ τ' h => ?_ emb_ne := fun τ τ' h => ?_ emb_all := fun φ => ?_ cpl …` and prove the remaining obligations.

Conclude with `(congrArg φ (B.fields_star x)).trans (B.host.conjE_apply φ x)`. Apply `B.embLL.injective` to reduce the goal to its premises. Rewrite using `[B.starLL_cx]`. Conclude with `(congrArg (B.embLL.comp (B.tauLL τ)) (B.fields_star x)).trans (B.host.conjE_apply (B.embLL.comp (B.tauLL τ)) x)`. Use `(card_Tau B.host).trans (Eq.trans ?_ (B.host.finrank_hostF).symm)` and prove the remaining obligations.

Both sides reduce to the same expression. Establish `h1` using `congrArg B.embLL.comp h`. Rewrite `h1` using `[embLL_comp_emb, embLL_comp_emb]`. Conclude with `Subtype.ext ((factEmb B.R B.host).1.1 h1)`. Establish `h1` using `congrArg B.embLL.comp h`.

Rewrite `h1` using `[embLL_comp_emb, embLL_comp_embBar]`. Establish `h2` using `(factEmb B.R B.host).1.1 h1`. Conclude with `(Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 τ'.2 (h2 ▸ τ.2)`. Take `⟨g, hg⟩` from `(factEmb B.R B.host).1.2 (B.embLL.comp φ)`. Distinguish the cases in `h : g ∈ B.R.Psi`.

Conclude with `⟨⟨g, h⟩, Or.inl (hinj (by rw [← hg]; exact (embLL_comp_emb B ⟨g, h⟩).symm))⟩`. Establish `hcc : B.R.cc * B.R.cc = 1` using `B.R.cc_mul_cc`. Establish `h' : g * B.R.cc ∈ B.R.Psi`. Rewrite using `[Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, mul_assoc, hcc, mul_one]`. Conclude with `h`.

Use `⟨⟨_, h'⟩, Or.inr (hinj ?_)⟩` and prove the remaining obligations. Rewrite using `[← hg, embLL_comp_embBar B ⟨_, h'⟩]`. Use `show _ = B.host.emb (g * B.R.cc * B.R.cc)`. Rewrite using `[mul_assoc, hcc, mul_one]`. Use `letI : Algebra B.host.E B.LL := B.embE.toAlgebra`.

Conclude with `isTotallyComplex_of_algebra B.host.E B.LL`. Set `e : B.fields.Kq ≃+* B.host.K` to `RingEquiv.subringCongr (s := B.fields.Kq.toSubring) (t := B.host.K.toSubfield.toSubring) (Subring.ext fun x => mem_Kq_iff B x)`. Rewrite using `[← SplitK.finrank_K B.host.hyp.2.1.pos B.host.sqrtMinusD_sq]`. Conclude with `(AlgEquiv.ofRingEquiv (R := ℚ) (f := e) (fun r => map_ratCast e r)).toLinearEquiv.finrank_eq`.
-/
theorem fields_ok : B.fields.Ok := by
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  letI := B.host.cmStar
  have cm := host_cmData B.R B.host
  have hinj : ∀ {φ ψ : B.host.E →+* B.LL}, B.embLL.comp φ = B.embLL.comp ψ → φ = ψ := fun h =>
    RingHom.ext fun x => B.embLL.injective (RingHom.congr_fun h x)
  refine
    { realF := cm.totReal
      rankE := cm.deg2
      star_F := fun x => (cm.fixed _).2 ⟨x, rfl⟩
      conjE := fun φ x => ?_
      cplxE := inferInstanceAs (IsTotallyComplex B.host.E)
      emb_star := fun τ x => ?_
      card_Tau := ?_
      emb_inj := fun τ τ' h => ?_
      emb_ne := fun τ τ' h => ?_
      emb_all := fun φ => ?_
      cplxK := ?_
      normalK := inferInstanceAs (Normal ℚ B.LL)
      conjK := ⟨B.embLL, B.starLL_cx⟩
      quad := ?_ }
  · exact (congrArg φ (B.fields_star x)).trans (B.host.conjE_apply φ x)
  · apply B.embLL.injective
    rw [B.starLL_cx]
    exact (congrArg (B.embLL.comp (B.tauLL τ)) (B.fields_star x)).trans (B.host.conjE_apply (B.embLL.comp (B.tauLL τ)) x)
  · refine (card_Tau B.host).trans (Eq.trans ?_ (B.host.finrank_hostF).symm)
    rfl
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_emb] at h1
    exact Subtype.ext ((factEmb B.R B.host).1.1 h1)
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_embBar] at h1
    have h2 := (factEmb B.R B.host).1.1 h1
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 τ'.2 (h2 ▸ τ.2)
  · obtain ⟨g, hg⟩ := (factEmb B.R B.host).1.2 (B.embLL.comp φ)
    by_cases h : g ∈ B.R.Psi
    · exact ⟨⟨g, h⟩, Or.inl (hinj (by rw [← hg]; exact (embLL_comp_emb B ⟨g, h⟩).symm))⟩
    · have hcc : B.R.cc * B.R.cc = 1 := B.R.cc_mul_cc
      have h' : g * B.R.cc ∈ B.R.Psi := by
        rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, mul_assoc, hcc, mul_one]
        exact h
      refine ⟨⟨_, h'⟩, Or.inr (hinj ?_)⟩
      rw [← hg, embLL_comp_embBar B ⟨_, h'⟩]
      show _ = B.host.emb (g * B.R.cc * B.R.cc)
      rw [mul_assoc, hcc, mul_one]
  · letI : Algebra B.host.E B.LL := B.embE.toAlgebra
    exact isTotallyComplex_of_algebra B.host.E B.LL
  · let e : B.fields.Kq ≃+* B.host.K :=
      RingEquiv.subringCongr (s := B.fields.Kq.toSubring) (t := B.host.K.toSubfield.toSubring)
        (Subring.ext fun x => mem_Kq_iff B x)
    rw [← SplitK.finrank_K B.host.hyp.2.1.pos B.host.sqrtMinusD_sq]
    exact (AlgEquiv.ofRingEquiv (R := ℚ) (f := e) (fun r => map_ratCast e r)).toLinearEquiv.finrank_eq

/- English proof (translation)
Introduce `B`. Use `⟨⟨fields_ok B, ?_, B.host.hostE_isGalois, gal_comm B.host, unram B.host⟩, B.fields_f⟩` and prove the remaining obligations. Rewrite using `[B.fields_f]`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le B.host.two_le_e`. Take `⟨m, hm⟩` from `B.R.two_pow_dvd_ord`.

Use `⟨2 ^ k * m, ?_⟩` and prove the remaining obligations. Use `show 2 * B.R.ord = _`. Rewrite using `[hm, hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fields_satisfy_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  intro B
  refine ⟨⟨fields_ok B, ?_, B.host.hostE_isGalois, gal_comm B.host, unram B.host⟩, B.fields_f⟩
  rw [B.fields_f]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le B.host.two_le_e
  obtain ⟨m, hm⟩ := B.R.two_pow_dvd_ord
  refine ⟨2 ^ k * m, ?_⟩
  show 2 * B.R.ord = _
  rw [hm, hk]
  ring

end GlobalTheory.Mem.FieldsLaws
