import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

/- English proof (translation)
Introduce `K _ X q N m i y s k T T' φ h h'`. Take `⟨β, hQ, -⟩` from `h'`. Take `⟨-, V, hV, hT⟩` from `h`. Conclude with `⟨hQ, V, hV, GlobalTheory.CompanionTheory.ThickPt.inU_map V φ hT⟩`.
-/
theorem wK_rel : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  intro K _ X q N m i y s k T T' φ h h'
  obtain ⟨β, hQ, -⟩ := h'
  obtain ⟨-, V, hV, hT⟩ := h
  exact ⟨hQ, V, hV, GlobalTheory.CompanionTheory.ThickPt.inU_map V φ hT⟩

end GlobalTheory.CompanionTheory.ConeSite
