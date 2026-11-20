import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.HasFiniteLengthJacSub
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskyCosets.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

/- English proof (translation)
The claim follows from `isSmooth_parInd _ _`.
-/
theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

/- English proof (translation)
Establish `hρ` using `CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l`. Establish `hsρ : IsSmooth (piTensor (segTerm σ.ρ l))` using `isSmooth_piTensor fun a => isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))`. Conclude with `GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)`.
-/
theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)

/- English proof (translation)
Introduce `v`. Establish `: {g : G | S.toRepresentation g v = v} = {g : G | π g v.1 = v.1}`. Use extensionality with `g`. Conclude with `Subtype.ext_iff`. Rewrite using `[this]`.

Conclude with `hπ v.1`.
-/
theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | π g v.1 = v.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ v.1

end SrEasy

open SrEasy

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Set `ι : T.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l))` to `⟨T.toSubmodule.subtype, fun _ => rfl⟩`. Establish `hnt : Nontrivial T.toSubmodule` using `Submodule.nontrivial_iff_ne_bot.2 hT`. Take `⟨S, f, hf⟩` from `GlobalTheory.T.exists_injective_irreducible_subrepresentation k _ _ _ T.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) (isSmooth_sub (isSmooth_prod σ) T) hnt (IsSubquotient.of_injective ι Subtype.val_injective) (hasFiniteLength_prod σ)`. Set `g : S.ρ.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l))` to `ι.comp f`. Establish `hg : Function.Injective g` using `Subtype.val_injective.comp hf`.

Establish `hat : IsAtom g.range` using `isAtom_range S.irr g hg`. Use `⟨g.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `(f x).2`.
-/
theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  let ι : T.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  have hnt : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hT
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.exists_injective_irreducible_subrepresentation k _ _ _ T.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))
    (isSmooth_sub (isSmooth_prod σ) T) hnt (IsSubquotient.of_injective ι Subtype.val_injective)
    (hasFiniteLength_prod σ)
  let g : S.ρ.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ι.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have hat : IsAtom g.range := isAtom_range S.irr g hg
  refine ⟨g.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (f x).2

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
The claim follows from `CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2`.
-/
theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Set `ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Establish `hS : HasFiniteLength S.toRepresentation` using `GlobalTheory.ProdLength.hasFiniteLength_of_injective ι Subtype.val_injective (hasFiniteLength_prod σ)`. Conclude with `GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation (isSmooth_sub (isSmooth_prod σ) S) hS`.
-/
theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : HasFiniteLength S.toRepresentation :=
    GlobalTheory.ProdLength.hasFiniteLength_of_injective ι Subtype.val_injective (hasFiniteLength_prod σ)
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) hS

end CompanionTheory.RgGu.SRC

end
