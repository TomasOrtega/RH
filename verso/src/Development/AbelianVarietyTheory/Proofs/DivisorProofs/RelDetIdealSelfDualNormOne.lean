import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.SelfDualDetNorm

/- English proof (translation)
Use `letI := D.host.cmStar`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Use `letI := D.host.isCMField_hostE`. Use `show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _`. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]`.
-/
theorem star_eq_conj (D : D7) (x : D.host.E) :
    (letI := D.host.cmStar; star x) = D.host.conj x := by
  letI := D.host.cmStar
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

/- English proof (translation)
Take `⟨hfg, hsp, hd⟩` from `hL`. Use `⟨⟨hfg, hsp⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[hd y]`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`.

Both sides reduce to the same expression.
-/
theorem isSdLat_of_isSDLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) : Formalism.L2.Col.IsSdLat (E := E) L := by
  obtain ⟨hfg, hsp, hd⟩ := hL
  refine ⟨⟨hfg, hsp⟩, ?_⟩
  ext y
  rw [hd y]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

/- English proof (translation)
Introduce `D N L hL`. Use `letI := D.host.cmStar`. Take `⟨J, hJ, hIJ⟩` from `GlobalTheory.CharValCompare.normOne_detI (isSdLat_of_isSDLat L hL)`. Use `⟨J, fun x => by rw [hJ, star_eq_conj]; exact Iff.rfl, ?_⟩` and prove the remaining obligations. Conclude with `hIJ`.
-/
theorem detId_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  intro D N L hL
  letI := D.host.cmStar
  obtain ⟨J, hJ, hIJ⟩ := GlobalTheory.CharValCompare.normOne_detI (isSdLat_of_isSDLat L hL)
  refine ⟨J, fun x => by rw [hJ, star_eq_conj]; exact Iff.rfl, ?_⟩
  exact hIJ

end GlobalTheory.SelfDualDetNorm
