import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem mem_mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL')
    (Sig : Finset (I →* LLˣ)) (x : I →* LL'ˣ) :
    x ∈ mapSig f Sig ↔ ∃ a ∈ Sig, (Units.map (f : LL →* LL')).comp a = x := by
  classical
  unfold mapSig
  exact Finset.mem_image

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem orbLen_map {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL')
    (I : Subgroup G) (Fr : G) (a b : I →* LLˣ) :
    Formalism.MainNotions.ElementDenominator.orbLen I Fr ((Units.map (f : LL →* LL')).comp a * ((Units.map (f : LL →* LL')).comp b)⁻¹) =
      Formalism.MainNotions.ElementDenominator.orbLen I Fr (a * b⁻¹) := by
  set φ : LLˣ →* LL'ˣ := Units.map (f : LL →* LL') with hφ
  have hinj : Function.Injective φ := by
    intro u v huv
    apply Units.ext
    have := congrArg Units.val huv
    simpa [hφ] using f.injective this
  have hcomp : φ.comp a * (φ.comp b)⁻¹ = φ.comp (a * b⁻¹) := by
    ext x
    simp
  rw [hcomp]
  unfold Formalism.MainNotions.ElementDenominator.orbLen
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, MonoidHom.comp_apply]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => hinj (h g g' hg)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => congrArg φ (h g g' hg)⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mapSig_props : ∀ {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL') (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)), (FrobStable I Fr Sig → FrobStable I Fr (mapSig f Sig)) ∧ Formalism.MainNotions.ElementDenominator.rPrime I Fr (mapSig f Sig) = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧ (mapSig f Sig).card ≤ Sig.card ∧ (1 ∈ Sig → 1 ∈ mapSig f Sig) := by
  intro G LL LL' _ _ _ f I Fr Sig
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig a').1 ha'
    obtain ⟨b, hb, hab⟩ := hS a ha
    refine ⟨(Units.map (f : LL →* LL')).comp b, (mem_mapSig f Sig _).2 ⟨b, hb, rfl⟩, ?_⟩
    intro g h hgh
    simp [hab g h hgh]
  · unfold Formalism.MainNotions.ElementDenominator.rPrime
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig p).1 hpq.1
      obtain ⟨b, hb, rfl⟩ := (mem_mapSig f Sig q).1 hpq.2
      rw [orbLen_map f I Fr a b]
      exact Finset.le_sup (s := Sig ×ˢ Sig)
        (f := fun p : (↥I →* LLˣ) × (↥I →* LLˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹)) (b := (a, b))
        (Finset.mem_product.2 ⟨ha, hb⟩)
    · apply Finset.sup_le
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have := Finset.le_sup (s := mapSig f Sig ×ˢ mapSig f Sig)
        (f := fun p : (↥I →* LL'ˣ) × (↥I →* LL'ˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹))
        (b := ((Units.map (f : LL →* LL')).comp a, (Units.map (f : LL →* LL')).comp b))
        (Finset.mem_product.2 ⟨(mem_mapSig f Sig _).2 ⟨a, hab.1, rfl⟩, (mem_mapSig f Sig _).2 ⟨b, hab.2, rfl⟩⟩)
      simpa only [orbLen_map f I Fr a b] using this
  · classical
    unfold mapSig
    exact Finset.card_image_le
  · intro h1
    exact (mem_mapSig f Sig 1).2 ⟨1, h1, MonoidHom.comp_one _⟩

end GlobalTheory.BaseCoef
