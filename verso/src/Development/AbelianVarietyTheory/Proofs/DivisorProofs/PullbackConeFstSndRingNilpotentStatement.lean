import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackConeFstSndRingNilpotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.pullbackCone_fst_snd_ring_nilpotent` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackConeFstSndRingNilpotent.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.pullbackCone_surjective_nilpotent_ker : ∀ {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C), Function.Surjective f.hom → IsNilpotent (RingHom.ker f.hom) → Function.Surjective g.hom → IsNilpotent (RingHom.ker g.hom) → (Function.Surjective (CommRingCat.pullbackCone f g).fst.hom ∧ IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).fst.hom)) ∧ (Function.Surjective (CommRingCat.pullbackCone f g).snd.hom ∧ IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).snd.hom)) ∧ (Function.Surjective ((CommRingCat.pullbackCone f g).fst ≫ f).hom ∧ IsNilpotent (RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom)) := by
  first | exact @GlobalTheory.pullbackCone_fst_snd_ring_nilpotent | exact GlobalTheory.pullbackCone_fst_snd_ring_nilpotent | (intros; apply GlobalTheory.pullbackCone_fst_snd_ring_nilpotent <;> assumption)
