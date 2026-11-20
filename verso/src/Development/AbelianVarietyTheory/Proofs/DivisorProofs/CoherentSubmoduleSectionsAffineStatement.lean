import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentSubmoduleSectionsAffine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatGlue.mem_glueSub_sec_iff_of_isAffineOpen` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoherentSubmoduleSectionsAffine.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.coherent_submodule_sections_affine : ∀ (Y : Scheme.{0}) (h : ℕ) (I : Type) (V : I → Y.Opens) (P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i))), (∀ (i j : I) (y : Y), y ∈ V i → y ∈ V j → ∃ k, y ∈ V k ∧ V k ≤ V i ∧ V k ≤ V j) → (∀ (i k : I) (hle : V k ≤ V i), P k = Submodule.span Γ(Y, V k) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i))))) → ∀ (i : I) (W : Y.Opens), IsAffineOpen W → ∀ (hle : W ≤ V i) (s : Γ(freeModule Y (Fin h), W)), s ∈ (glueSub V P).sec W ↔ coords Y h W s ∈ Submodule.span Γ(Y, W) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i)))) := by
  first | exact @GlobalTheory.LatGlue.mem_glueSub_sec_iff_of_isAffineOpen | exact GlobalTheory.LatGlue.mem_glueSub_sec_iff_of_isAffineOpen | (intros; apply GlobalTheory.LatGlue.mem_glueSub_sec_iff_of_isAffineOpen <;> assumption)
