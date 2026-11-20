import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

/- English proof (translation)
Introduce `h`. Establish `h1` using `WittVector.coeff_p_one (p := p) (R := GaloisField p n')`. Rewrite `h1` using `[h]`. Simplify using `at h1`.
-/
theorem wittVector_prime_ne_zero (p n' : ℕ) [Fact p.Prime] : ((p : ℕ) : WF p n') ≠ 0 := by
  intro h
  have h1 := WittVector.coeff_p_one (p := p) (R := GaloisField p n')
  rw [h] at h1
  simp at h1

/- English proof (translation)
Introduce `p n' _ W Qq _ _ _ _ _ m φ h g g' e e' hfr hg hg' he he' hpl`. Establish `hp0 : (p : W) ≠ 0`. Introduce `h0`. Apply `wittVector_prime_ne_zero p n'` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[map_natCast, h0, map_zero]`. Establish `hpQ : (p : Qq) ≠ 0`. Rewrite using `[← map_natCast (algebraMap W Qq)]`. Conclude with `fun h1 => hp0 ((IsFractionRing.injective W Qq) (by rw [h1, map_zero]))`. Take `⟨-, hs, ht⟩` from `he`.

Take `⟨-, hs', ht'⟩` from `he'`. Rewrite `hs` using `[src_eq φ g hg h]`. Rewrite `hs'` using `[src_eq φ g' hg' h]`. Rewrite `ht` using `[matQ_inv φ g hg]`. Rewrite `ht'` using `[matQ_inv φ g' hg']`.

Express the relevant statement in the definitionally equal form `e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht`. Express the relevant statement in the definitionally equal form `e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht'`. Take `⟨s, t⟩` from `e`. Take `⟨s', t'⟩` from `e'`. Simplify using `only at hs hs' ht ht'`.

Rewrite using `[Edge.mk.injEq]`. Use `⟨by rw [hs, hs'], ?_⟩` and prove the remaining obligations. Rewrite using `[ht, ht']`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `tgt_le_of_plane φ 1 hpQ g' g hg' hg h hpl.le`.

Conclude with `tgt_le_of_plane φ 1 hpQ g g' hg hg' h hpl.ge`.
-/
theorem planeAt : PlaneAt := by
  intro p n' _ W Qq _ _ _ _ _ m φ h g g' e e' hfr hg hg' he he' hpl
  have hp0 : (p : W) ≠ 0 := by
    intro h0
    apply wittVector_prime_ne_zero p n'
    apply φ.injective
    rw [map_natCast, h0, map_zero]
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h1 => hp0 ((IsFractionRing.injective W Qq) (by rw [h1, map_zero]))
  obtain ⟨-, hs, ht⟩ := he
  obtain ⟨-, hs', ht'⟩ := he'
  rw [src_eq φ g hg h] at hs
  rw [src_eq φ g' hg' h] at hs'
  rw [matQ_inv φ g hg] at ht
  rw [matQ_inv φ g' hg'] at ht'
  change e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht
  change e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht'
  obtain ⟨s, t⟩ := e
  obtain ⟨s', t'⟩ := e'
  simp only at hs hs' ht ht'
  rw [Edge.mk.injEq]
  refine ⟨by rw [hs, hs'], ?_⟩
  rw [ht, ht']
  apply le_antisymm
  · exact tgt_le_of_plane φ 1 hpQ g' g hg' hg h hpl.le
  · exact tgt_le_of_plane φ 1 hpQ g g' hg hg' h hpl.ge

end Formalism.MainNotions.ColumnSystems.Pf
