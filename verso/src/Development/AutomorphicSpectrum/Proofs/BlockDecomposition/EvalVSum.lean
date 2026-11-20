import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.UniformTransfer.UnitaryIntegralLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionary

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisUnif.EIdemP

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `only [eSF, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]`. Both sides reduce to the same expression.
-/
theorem eSF_eq (S : Finset (Pl F)) : eSF S = ((1, ∑ v ∈ S, singleFin v 1) : AF F) := by
  simp only [eSF, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rfl

open Classical in
/- English proof (translation)
Rewrite using `[map_sum]`. Establish `hs : ∀ v : Pl F, evalV F u (singleFin v 1) = if u = v then 1 else 0`. Introduce `v`. Establish `e1 : evalV F u (singleFin v 1) = (singleFin v (1 : Fv F v) : Af F) u` using `rfl`. Establish `e2 : (singleFin v (1 : Fv F v) : Af F) = singleV F v 1` using `rfl`.

Rewrite using `[e1, e2]`. Unfold `singleV`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Rewrite using `[if_pos rfl]`.

Conclude with `RestrictedProduct.single_eq_same _ _ _`. Rewrite using `[if_neg huv]`. Conclude with `RestrictedProduct.single_eq_of_ne _ _ huv`. Simplify using `only [hs]`. Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem evalV_sum (S : Finset (Pl F)) (u : Pl F) :
    evalV F u (∑ v ∈ S, singleFin v 1) = if u ∈ S then 1 else 0 := by
  rw [map_sum]
  have hs : ∀ v : Pl F, evalV F u (singleFin v 1) = if u = v then 1 else 0 := by
    intro v
    have e1 : evalV F u (singleFin v 1) = (singleFin v (1 : Fv F v) : Af F) u := rfl
    have e2 : (singleFin v (1 : Fv F v) : Af F) = singleV F v 1 := rfl
    rw [e1, e2]
    unfold singleV
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg huv]
      exact RestrictedProduct.single_eq_of_ne _ _ huv
  simp only [hs]
  rw [Finset.sum_ite_eq]

end GlobalTheory.CompanionTheory.RgEisUnif.EIdemP
