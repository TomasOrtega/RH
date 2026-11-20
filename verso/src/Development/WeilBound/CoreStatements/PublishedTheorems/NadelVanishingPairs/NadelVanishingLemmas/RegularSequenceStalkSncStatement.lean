import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceStalkSnc
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPublishedTheorems%2FNadelVanishingPairs%2FNadelVanishingLemmas%2FRegularSequenceStalkSnc.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.regular_sequence_stalk_snc : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → (∀ x : X, IsClosed ({x} : Set X) → ∃ (n : ℕ) (t : Fin n → X.presheaf.stalk x) (c : ∀ i, (L i).ι) (hc : ∀ i, x ∈ (L i).U (c i)) (e : Fin s → Option (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧ ∀ i, Associated ((X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t)) → RelSnc f d L σ := by
  first | exact @_root_.GlobalTheory.RegParams.relSnc_of_regular_params | exact _root_.GlobalTheory.RegParams.relSnc_of_regular_params | (intros; apply _root_.GlobalTheory.RegParams.relSnc_of_regular_params <;> assumption)
