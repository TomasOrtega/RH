import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComapMapEqSelfOfInjectiveFiniteHopf.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  first | exact @GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | exact GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | (intros; apply GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective <;> assumption)
