import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegIdentitySymm
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsPullDegIdentitySymm.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.isPullDeg_identity_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), IsPullDeg (RingHom.id R) D D' → Nonempty (IsPullDeg (RingHom.id R) D' D) := by
  first | exact @GlobalTheory.PullDegSymm.isPullDeg_symm | exact GlobalTheory.PullDegSymm.isPullDeg_symm | (intros; apply GlobalTheory.PullDegSymm.isPullDeg_symm <;> assumption)
