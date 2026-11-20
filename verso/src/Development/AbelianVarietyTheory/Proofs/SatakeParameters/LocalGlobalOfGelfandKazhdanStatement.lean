import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalGlobalOfGelfandKazhdan.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.local_global_of_gelfand_kazhdan : GlobalTheory.Published.GelfandKazhdanDual → (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧ (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  first | exact @GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair | exact GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair | (intros; apply GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair <;> assumption)
