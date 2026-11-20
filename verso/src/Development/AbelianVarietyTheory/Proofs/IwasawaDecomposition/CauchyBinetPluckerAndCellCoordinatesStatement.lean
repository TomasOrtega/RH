import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagEmb.CauchyBinet.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCauchyBinetPluckerAndCellCoordinates.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  first | exact @GlobalTheory.FlagEmb.CauchyBinet.main | exact GlobalTheory.FlagEmb.CauchyBinet.main | (intros; apply GlobalTheory.FlagEmb.CauchyBinet.main <;> assumption)
