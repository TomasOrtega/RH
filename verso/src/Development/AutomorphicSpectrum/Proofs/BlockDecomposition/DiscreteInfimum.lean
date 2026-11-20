import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Introduce `E _ _ _ M V hV τ`. Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 hV.ne_bot`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℂ h0`. Take `⟨m, hm, h⟩` from `exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf`. Use `⟨m, hm, fun u ψ hψ => ?_⟩` and prove the remaining obligations.

Take `⟨c, h1⟩` from `GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)`. Establish `h2 : f (cap τ u φ) = _` using `h u`. Rewrite `h2` using `[h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one]`. Rewrite using `[h1 ψ hψ, h2]`.
-/
theorem discInf : DiscInf := by
  intro E _ _ _ M V hV τ
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CompanionTheory.EGlue

end
