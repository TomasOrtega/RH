import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.UnrAtOfIsoTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.SV

/- English proof (translation)
The claim follows from `h`.
-/
theorem exRS' (h : ExRS) : ExRS := h

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl σ _ hB H` and use `frob_of hl σ hB H`.
-/
theorem satFrobL : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRecT h rc →
      IsWDOf ι r (rc (algNorm σ))) → FrobEig ι r w (algSat n (normV w) B) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl σ _ hB H => frob_of hl σ hB H

/- English proof (translation)
Introduce `P` and use `satFrobL P.litN`.
-/
theorem satFrobP : Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRecT h rc →
      IsWDOf ι r (rc (algNorm σ))) → FrobEig ι r w (algSat n (normV w) B) := fun P => satFrobL P.litN

/- English proof (translation)
Introduce `_ hA F _ _ _` and use `unrAt_of_isoTwist hA F`.
-/
theorem unrAt_alt : type_of% @GlobalTheory.RealGal.unrAt_of_isoTwist := fun _ hA F _ _ _ => unrAt_of_isoTwist hA F

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `H.ratio w hl A h (H.plain w B hB)`.
-/
theorem ratioW_of_hasSat [IsTotallyReal F] (_P : Hypotheses₂) {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    UpperTheory.GalN.V.RatioW (wdOf h hl ι r) := H.ratio w hl A h (H.plain w B hB)

/- English proof (translation)
Establish `hB : π.HasSat w S` using `((GlobalTheory.T.satakeParameters_local F n w σ).2 _ π.finPart ((GlobalTheory.T.local_global_compatibility_real admissibleReal F n π w).2 σ hσ) S).2 hS`. Establish `hp` using `H.plain w S hB σ hσ`. Conclude with `(((H.loc w σ hσ hp).1 A h rc hrc).1 hl).isWDOf (gdOf F Ω A w h rc hrc n σ hp)`.
-/
theorem isWDOf_satR [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRecT h rc) {σ : SmIrr (GL (Fin n) (w.adicCompletion F))}
    (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := by
  have hB : π.HasSat w S :=
    ((GlobalTheory.T.satakeParameters_local F n w σ).2 _ π.finPart ((GlobalTheory.T.local_global_compatibility_real admissibleReal F n π w).2 σ hσ) S).2 hS
  have hp := H.plain w S hB σ hσ
  exact (((H.loc w σ hσ hp).1 A h rc hrc).1 hl).isWDOf (gdOf F Ω A w h rc hrc n σ hp)

end UpperTheory.Gal.SV
