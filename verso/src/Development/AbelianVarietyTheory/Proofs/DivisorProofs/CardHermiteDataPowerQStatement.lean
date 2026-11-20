import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardHermiteDataPowerQ
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaExponentHnfGL
open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HermCount.card_hData` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardHermiteDataPowerQ.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.card_hermite_data_power_q : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℕ), Nat.card (GlobalTheory.HermCount.HData F n l) = Spherical.qF F ^ (∑ i : Fin n, (n - 1 - i.val) * l i) := by
  first | exact @GlobalTheory.HermCount.card_hData | exact GlobalTheory.HermCount.card_hData | (intros; apply GlobalTheory.HermCount.card_hData <;> assumption)
