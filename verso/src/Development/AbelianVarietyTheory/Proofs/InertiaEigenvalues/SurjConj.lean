import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne

noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.UnivCharIne

/- English proof (translation)
Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x` using `Formalism.BasicNotions.bridge_star_holds D.R D.host`. Take `⟨⟨j, hj⟩, -⟩` from `D.ntw.cc_cm`. Establish `hκ : ∀ x, D.host.conj (D.host.conj x) = x` using `fun x => by`. Rewrite using `[← hst, ← hst, IsCMField.complexConj_apply_apply]`.

Establish `hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)` using `fun x => by`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, ← hst]`. Conclude with `(IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E D.nd.Om)) x).symm`. Establish `hs' : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)` using `fun x => by`.

Rewrite using `[RingEquiv.symm_apply_eq, hc, hκ]`. Establish `hinv : ∀ x, D.ntw.cc (D.ntw.cc x) = x` using `fun x => by`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj, hj]`. Simplify using the standard rewrite rules.

Establish `hsymm : ∀ x, D.ntw.cc.symm x = D.ntw.cc x` using `fun x => by`. Rewrite using `[RingEquiv.symm_apply_eq, hinv]`. Establish `hP'P` using `GlobalTheory.GalChar.isConjPl_symm hPP`. Establish `hpl : IsPlaceOver (A.comap D.ntw.cc.symm.toRingHom) P` using `fun y => by`. Establish `hint : IsIntegral ℤ (D.host.conj (y : D.host.E))`.

Rewrite using `[← hst]`. Conclude with `(RingOfIntegers.isIntegral_coe y).map ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)`. Rewrite using `[GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]`. Conclude with `hA' ⟨_, hint⟩`. Take `⟨σ, hσ, hσb⟩` from `hs _ hpl b⁻¹`.

Take `⟨σ', h1, h2⟩` from `GlobalTheory.AntiRam.exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ`. Establish `eA : (A.comap D.ntw.cc.symm.toRingHom).comap D.ntw.cc.symm.toRingHom = A`. Use extensionality with `y`. Use `show D.ntw.cc.symm (D.ntw.cc.symm y) ∈ A ↔ y ∈ A`. Rewrite using `[hsymm, hsymm, hinv]`.

Use `⟨σ', eA ▸ h2, ?_⟩` and prove the remaining obligations. Rewrite using `[hA σ σ' h1, hσb, inv_inv]`.
-/
theorem surj_conj (D : D7) {B : Type} [CommGroup B] (χ : G D.host.E D.nd.Om →* B) (hA : AntiHom D.ntw.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring D.nd.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs' : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, D.ntw.cc.symm x = D.ntw.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap D.ntw.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap D.ntw.cc.symm.toRingHom).comap D.ntw.cc.symm.toRingHom = A := by
    ext y
    show D.ntw.cc.symm (D.ntw.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

/- English proof (translation)
Introduce `D hU i Q M hQ P hP`. Take `⟨-, hQ'⟩` from `hQ`. Establish `hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q` using `fun P hP P' h => by`. Take `⟨⟨P'', hP'', h''⟩, -⟩` from `hQ' P hP`. Rewrite using `[GlobalTheory.GalChar.isConjPl_unique h h'']` and apply the resulting hypothesis.

Take `⟨-, χ, h1, h2, h3, h4, h5⟩` from `hQ' P hP`. Establish `hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ b, ∃ σ ∈ Ine (F` using `D.host.E) A, χ σ = b := fun A hA b => by`. Take `⟨σ, hσ⟩` from `h5 A hA (Multiplicative.toAdd b)`. Conclude with `⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩`. Establish `hDel : GlobalTheory.GalChar.IsDel D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) χ`.

Use `⟨h1, h2, h3, fun v hv => h4 v (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e)), fun v hv A hA b => ?_⟩` and prove the remaining obligations. Break down `hv with rfl | hv` into its components or cases. Conclude with `hsP A hA b`. Conclude with `surj_conj D χ h2 hv hsP A hA b`. Establish `hD` using `GlobalTheory.GalChar.isDel_delOf D.host D.ntw.cc (D.ntw.l i) ⟨χ, hDel⟩`.

Establish `e : ∀ σ, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) σ)`. Introduce `σ`. Rewrite using `[hU]`. Conclude with `(GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.2.1 Q M hcl P hP σ`. Use `⟨fun A hA x => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩` and prove the remaining obligations.

Take `⟨σ, hσ, hx⟩` from `hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)`. Conclude with `⟨⟨σ, hσ⟩, by simp only [e, hx, toAdd_ofAdd]⟩`. Rewrite using `[e, hD.2.2.2.1 P' (by rintro (h | h); exacts [hne h, hnc h]) A hA σ hσ]`. Both sides reduce to the same expression.
-/
theorem delU_ine : ∀ D : D7, GlobalTheory.UnivChar.IsUnivChar D.nexp → (∀ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M → ∀ P (hP : P ∈ Q), (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧ ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0) := by
  intro D hU i Q M hQ P hP
  obtain ⟨-, hQ'⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hQ' P hP
    rwa [GlobalTheory.GalChar.isConjPl_unique h h'']
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hQ' P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun v hv => h4 v (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e)), fun v hv A hA b => ?_⟩
    rcases hv with rfl | hv
    · exact hsP A hA b
    · exact surj_conj D χ h2 hv hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host D.ntw.cc (D.ntw.l i) ⟨χ, hDel⟩
  have e : ∀ σ, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ =
      Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) σ) := by
    intro σ
    rw [hU]
    exact (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.2.1 Q M hcl P hP σ
  refine ⟨fun A hA x => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, hx⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, by simp only [e, hx, toAdd_ofAdd]⟩
  · rw [e, hD.2.2.2.1 P' (by rintro (h | h); exacts [hne h, hnc h]) A hA σ hσ]
    rfl

end GlobalTheory.UnivCharIne
