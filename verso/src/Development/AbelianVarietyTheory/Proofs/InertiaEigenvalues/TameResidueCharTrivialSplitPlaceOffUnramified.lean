import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

/- English proof (translation)
Introduce `D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu`. Establish `he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP` using `hP.isIdemAt hPP`. Establish `hinf : infPart D (idemAt PP) = 0` using `GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩`. Take `⟨hei, -⟩` from `GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he`. Establish `hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D)`.

Take the linear combination `hoff`. Establish `hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (toEAf D) hx` as an intermediate fact. Simplify using `only [map_add, map_sub, map_mul, map_one] at this`.

Conclude with `this.trans rfl`. Establish `hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0`. Introduce `PP'`. Distinguish the cases in `hq : PP' = PP`. Substitute `hq` using the available equality.

Rewrite using `[hu]`. Conclude with `u.ne_zero`. Use `PP'.isPrime` as an intermediate fact. Establish `hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0`. Establish `hnle : ¬ PP'.asIdeal ≤ PP.asIdeal` using `fun hle => hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))`.

Take `⟨a, ha', ha⟩` from `SetLike.not_le_iff_exists.1 hnle`. Establish `ha0 : a ≠ 0` using `fun h0 => ha (h0 ▸ zero_mem _)`. Establish `ha0' : (a : D.host.E) ≠ 0` using `fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)`. Establish `hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D`. Assume the negation of the conclusion as `k`.

Conclude with `ha ((he.2 a ha0).2 k)`. Establish `hint'` using `GlobalTheory.IdemRes.toEAf_mem_of_finPart hint`. Establish `hb : toEAf D (incA D (a : D.host.E)) = ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)` using `rfl`. Establish `hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _`. Rewrite using `[← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]`. Rewrite using `[hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]`. Rewrite using `[hxI, map_add, map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]`. Conclude with `one_ne_zero`.

Take `⟨w, hw⟩` from `Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres`. Establish `hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)`. Establish `h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1`. Rewrite using `[← RingHom.map_mul, Units.inv_mul, RingHom.map_one]`. Establish `h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1`.

Use `congrArg Subtype.val (Units.mul_inv w)` as an intermediate fact. Rewrite `this` using `[hw]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Establish `hl : IsLocUnit PP u x`.

Use `⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩` and prove the remaining obligations. Use `congrArg (infPart D) hx` as an intermediate fact. Rewrite `this` using `[map_add, map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero]`. Conclude with `this`. Rewrite using `[hinv]`.

Conclude with `Subtype.property _`. Rewrite using `[hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]`.
-/
theorem isResAt_one_of_unram : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  intro D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := hP.isIdemAt hPP
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hei, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  have hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D) := by
    linear_combination hoff
  have hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩ := by
    apply Subtype.ext
    have := congrArg (toEAf D) hx
    simp only [map_add, map_sub, map_mul, map_one] at this
    exact this.trans rfl

  have hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0 := by
    intro PP'
    by_cases hq : PP' = PP
    · subst hq
      rw [hu]
      exact u.ne_zero
    · have := PP'.isPrime
      have hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0 := by
        have hnle : ¬ PP'.asIdeal ≤ PP.asIdeal := fun hle =>
          hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))
        obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
        have ha0' : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
        have hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
          by_contra k
          exact ha ((he.2 a ha0).2 k)
        have hint' := GlobalTheory.IdemRes.toEAf_mem_of_finPart hint
        have hb : toEAf D (incA D (a : D.host.E)) =
            ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
        have hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a := by
          apply Subtype.ext
          change toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _
          rw [← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]
        rw [hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]
      rw [hxI, map_add, map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]
      exact one_ne_zero
  obtain ⟨w, hw⟩ := Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres
  have hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    have h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.inv_mul, RingHom.map_one]
    have h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv w)
      rw [hw] at this
      exact this
    calc _ = toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * (toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hl : IsLocUnit PP u x := by
    refine ⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩
    · have := congrArg (infPart D) hx
      rw [map_add, map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero] at this
      exact this
    · rw [hinv]
      exact Subtype.property _
  rw [hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]

end GlobalTheory.ConjTwist
