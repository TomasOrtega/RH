import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_map he`. Establish `: (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n` using `Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) = fun x => (x⁻¹).val.map e := by`. Use function extensionality and compare the values at `x`.

Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Units.continuous_coe_inv.matrix_map he`.
-/
theorem continuous_glMap {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map he
  · have : (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) =
        fun x => (x⁻¹).val.map e := by
      funext x; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map he

/- English proof (translation)
Use `set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ`. Establish `hsurj : Function.Surjective φ` using `fun y => ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by`. Use extensionality with `i j`. Simplify using `[hφ]⟩`. Use `⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩` and prove the remaining obligations.

Establish `hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W` using `fun y v hv => by`. Take `⟨x, rfl⟩` from `hsurj y`. Conclude with `hW x v hv`. Use `haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr`. Set `S : Subrepresentation σ.ρ` to `⟨W, fun y v hv => hW' y v hv⟩`.

Break down `eq_bot_or_eq_top S with h | h` into its components or cases. Use `left`. Conclude with `congrArg Subrepresentation.toSubmodule h`. Use `right`. Conclude with `congrArg Subrepresentation.toSubmodule h`.

Conclude with `(σ.smooth v).preimage (continuous_glMap e he n)`.
-/
theorem irrSm_pullback (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)) :
    IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ
  have hsurj : Function.Surjective φ := fun y =>
    ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by
      ext i j; simp [hφ]⟩
  refine ⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩
  · have hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W := fun y v hv => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact hW x v hv
    haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
    let S : Subrepresentation σ.ρ := ⟨W, fun y v hv => hW' y v hv⟩
    rcases eq_bot_or_eq_top S with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  · exact (σ.smooth v).preimage (continuous_glMap e he n)

end GlobalTheory.SerSys
