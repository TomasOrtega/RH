import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Mathlib

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Establish `hF : Flat p'` using `inferInstance`. Take `⟨x, hx⟩` from `p'.surjective (IsLocalRing.closedPoint K)`. Establish `h` using `p'.one_le_finrank_map x`. Rewrite `h` using `[hx]`. Then use the resulting hypothesis.
-/
private theorem rank_pos {K : Type} [Field K] {Z' : Scheme.{0}} (p' : Z' ⟶ TranscendenceTraces.gp K) [IsFinite p'] [Surjective p'] :
    1 ≤ p'.finrank (IsLocalRing.closedPoint K) := by
  have hF : Flat p' := inferInstance
  obtain ⟨x, hx⟩ := p'.surjective (IsLocalRing.closedPoint K)
  have h := p'.one_le_finrank_map x
  rwa [hx] at h

/- English proof (translation)
Introduce `hT l _ X Y π hfin hsurj hint hloc hl n`. Take `⟨hW, -, hD, hTr⟩` from `hT`. Use `haveI := hfin`. Use `haveI := hsurj`. Use `haveI := hint`.

Establish `hw : TranscendenceTraces.IsNwt π (TranscendenceTraces.nwt π)` using `hW π hloc`. Set `g : TranscendenceTraces.gp (Y.residueField (genericPoint Y)) ⟶ Y` to `Y.fromSpecResidueField (genericPoint Y)`. Establish `hpt : TranscendenceTraces.pt g = genericPoint Y` using `Scheme.fromSpecResidueField_apply _ _`. Establish `hpush` using `hD (Y.residueField (genericPoint Y)) (pullback.fst π g) (pullback.snd π g) π g (IsPullback.of_hasPullback π g) hloc hpt`. Establish `hd` using `rank_pos (pullback.snd π g)`.

Establish `htr` using `hTr l n 0 π (TranscendenceTraces.nwt π) _ hw.1 hl hpush`. Introduce `a b hab`. Establish `key : ∀ c, ((Scheme.Hom.finrank (pullback.snd π g) (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) • c = TranscendenceTraces.trHQ l π (TranscendenceTraces.nwt π) n 0 (pb l π n c)`. Introduce `c`. Use `LinearMap.congr_fun htr c` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at this`. Rewrite using `[this, Int.cast_smul_eq_zsmul]`. Establish `hne : ((Scheme.Hom.finrank (pullback.snd π g) (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) ≠ 0`. Use `norm_cast`. Use linear arithmetic over natural numbers and integers.

Apply `smul_right_injective _ hne` to reduce the goal to its premises. Simplify using `only [key, hab]`.
-/
theorem injL_holds : InjL := by
  intro hT l _ X Y π hfin hsurj hint hloc hl n
  obtain ⟨hW, -, hD, hTr⟩ := hT
  haveI := hfin
  haveI := hsurj
  haveI := hint
  have hw : TranscendenceTraces.IsNwt π (TranscendenceTraces.nwt π) := hW π hloc
  let g : TranscendenceTraces.gp (Y.residueField (genericPoint Y)) ⟶ Y :=
    Y.fromSpecResidueField (genericPoint Y)
  have hpt : TranscendenceTraces.pt g = genericPoint Y :=
    Scheme.fromSpecResidueField_apply _ _
  have hpush := hD (Y.residueField (genericPoint Y)) (pullback.fst π g) (pullback.snd π g) π g
    (IsPullback.of_hasPullback π g) hloc hpt
  have hd := rank_pos (pullback.snd π g)
  have htr := hTr l n 0 π (TranscendenceTraces.nwt π) _ hw.1 hl hpush
  intro a b hab
  have key : ∀ c, ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) • c =
      TranscendenceTraces.trHQ l π (TranscendenceTraces.nwt π) n 0 (pb l π n c) := by
    intro c
    have := LinearMap.congr_fun htr c
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hne : ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) ≠ 0 := by
    norm_cast
    omega
  apply smul_right_injective _ hne
  simp only [key, hab]

end UpperTheory.Gal.KunnethLefschetz
