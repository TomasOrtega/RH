import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.OrdExT
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.HeckeIdealEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Adelise
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

end Norm

/- English proof (translation)
Establish `: Fact r.Prime` using `⟨hr⟩`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `: NeZero (ordCompl[r] N)` using `⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩`. Establish `hcop : (ordCompl[r] N).Coprime r` using `(Nat.coprime_ordCompl hr (NeZero.ne N)).symm`. Establish `hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 → ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ` using `fun ζ hζ => by`.

Rewrite using `[Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]`. Take `⟨w, hw⟩` from `KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)`. Take `⟨σ, hσ, hσw⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w`. Use `⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩` and prove the remaining obligations. Use `(LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.mem_ker.1 hu, hone ζ hζ]`. Conclude with `(LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ`. Establish `hc : cyclotomicCharacter Ω r σ.toRingEquiv = w` using `hσw`. Rewrite using `[hc, hw]`.
-/
private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

/- English proof (translation)
Introduce `hall` and use `by have hft : χ.FactorsThrough (ordCompl[p] N) := by refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_ obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ)) refine Mon …`.
-/
private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega

end Gal

end UpperTheory.V.Sd.EG
