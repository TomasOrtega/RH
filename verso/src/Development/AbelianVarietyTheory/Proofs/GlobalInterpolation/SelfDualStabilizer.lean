import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerCompletions
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices

noncomputable section

namespace GlobalTheory.Proof.SelfDualStabilizer

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h P hP hne`. Conclude with `h ⟨P, hP, hne⟩`. Introduce `h P`. Conclude with `@h P.asIdeal P.isPrime P.ne_bot`.
-/
theorem unramifiedAtFinite_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.UnramifiedAtFinite F E ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.UnramifiedAtFinite F E := by
  constructor
  · intro h P hP hne
    exact h ⟨P, hP, hne⟩
  · intro h P
    exact @h P.asIdeal P.isPrime P.ne_bot

section Clauses

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isSelfDualLattice_iff (L : Submodule (𝓞 E) (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.IsSelfDualLat σ J L := Iff.rfl

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem perpPart_eq (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.perpPart σ J (L : Set (Fin M → E)) x = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.perpIn σ J L x := rfl

omit [NumberField E] in

/- English proof (translation)
The claim follows from `Subgroup.ext fun _ => Iff.rfl`.
-/
theorem stabHat_eq (S : Set (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.stabHat σ J S = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.stabLat (Af F) σ J (latHat F E S) :=
  Subgroup.ext fun _ => Iff.rfl

omit [NumberField E] in

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl`. Rewrite using `[stabHat_eq, stabHat_eq, perpPart_eq]`. Conclude with `Iff.rfl`.
-/
theorem orbitClaims_iff (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims σ J (L : Set (Fin M → E)) x β ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl F E σ J L x β := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl
  rw [stabHat_eq, stabHat_eq, perpPart_eq]
  exact Iff.rfl

end Clauses

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive`. Use `forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_` and prove the remaining obligations. Use `imp_congr (unramifiedAtFinite_iff F E) ?_` and prove the remaining obligations. Use `forall_congr' fun M => forall_congr' fun J => imp_congr_right fun _ => forall_congr' fun L => imp_congr (isSelfDualLattice_iff σ J L) ?_` and prove the remaining obligations. Conclude with `forall_congr' fun β => imp_congr_right fun _ => forall_congr' fun x => imp_congr_right fun _ => imp_congr_right fun _ => orbitClaims_iff σ J L x β`.
-/
theorem stabTransitive_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_
  refine imp_congr (unramifiedAtFinite_iff F E) ?_
  refine forall_congr' fun M => forall_congr' fun J => imp_congr_right fun _ =>
    forall_congr' fun L => imp_congr (isSelfDualLattice_iff σ J L) ?_
  exact forall_congr' fun β => imp_congr_right fun _ => forall_congr' fun x =>
    imp_congr_right fun _ => imp_congr_right fun _ => orbitClaims_iff σ J L x β

end GlobalTheory.Proof.SelfDualStabilizer
