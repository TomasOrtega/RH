import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigAtLeast
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtD
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI

noncomputable section

open scoped Matrix ComplexConjugate
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Inertia NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open ReciprocityTheory.ChartRestriction.G

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `D V k hk hS`. Use `letI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hH` using `GlobalTheory.Doubling.isHermND_gram V`. Establish `hσ : ∀ x : D.host.E, D.sp.cm.sig x = FD.cc x` using `fun x => rfl`. Establish `hT : ∀ a b, FD.cc (V.gram a b) = V.gram b a` using `fun a b => by rw [← hσ]; exact hH.1 b a`.

Establish `hTt : V.gramᵀ = V.gram.map FD.cc` using `Matrix.ext fun a b => (hT a b).symm`. Establish `hG : ∀ a b, FD.cc (V.gramᵀ a b) = V.gramᵀ b a` using `fun a b => by`. Simplify using `only [transpose_apply]`. Conclude with `hT b a`. Establish `hd : V.gramᵀ.det ≠ 0` using `by rw [det_transpose]; exact hH.2`.

Establish `hsigτ : ∀ τ0 : D.what₂.Tau, k ≤ posIndex (V.gram.map (tauE D τ0)) ∧ k ≤ negIndex (V.gram.map (tauE D τ0))`. Introduce `τ0`. Take `⟨ε, fr, hu, hfr, hp, hq⟩` from `hS τ0`. Establish `hP : (fr.map (starRingEnd ℂ)).det ≠ 0`. Establish `: (fr.map (starRingEnd ℂ)).det = starRingEnd ℂ fr.det` using `(RingHom.map_det (starRingEnd ℂ) fr).symm`.

Rewrite using `[this]`. Conclude with `(map_ne_zero _).2 hu.ne_zero`. Establish `hd' : (fr.map (starRingEnd ℂ))ᵀ * V.gram.map (tauE D τ0) * (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) = diagonal (PositivityTheory.Rg.Sw.sgn ε)`. Establish `h1 : (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) = fr`. Use extensionality with `a b`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Conclude with `hfr`. Rewrite using `[posIndex_eq_card_of_congr_diagonal hP hd', negIndex_eq_card_of_congr_diagonal hP hd']`. Establish `e1 : (Finset.univ.filter fun a => 0 < (PositivityTheory.Rg.Sw.sgn ε a).re) = Finset.univ.filter fun a => ε a = true`.

Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `a _`. Simplify using `only [PositivityTheory.Rg.Sw.sgn]`. Apply the tactic sequence `cases ε a <;> norm_num`. Establish `e2 : (Finset.univ.filter fun a => (PositivityTheory.Rg.Sw.sgn ε a).re < 0) = Finset.univ.filter fun a => ε a = false`.

Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `a _`. Simplify using `only [PositivityTheory.Rg.Sw.sgn]`. Apply the tactic sequence `cases ε a <;> norm_num`. Rewrite using `[e1, e2]`.

Conclude with `⟨hp, hq⟩`. Establish `hsig : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gram.map φ) ∧ k ≤ negIndex (V.gram.map φ)`. Introduce `φ`. Take `⟨τ0, h | h⟩` from `Formalism.L2.Fam.ThC.tauE_or (D := D) φ`. Rewrite using `[← h]`.

Conclude with `hsigτ τ0`. Establish `hφ : φ = ComplexEmbedding.conjugate (tauE D τ0)` using `by rw [h]; exact (star_star φ).symm`. Rewrite using `[hφ, posIndex_map_conjugate _ hT, negIndex_map_conjugate _ hT]`. Conclude with `hsigτ τ0`. Establish `hsigT : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gramᵀ.map φ) ∧ k ≤ negIndex (V.gramᵀ.map φ)`.

Introduce `φ`. Establish `hm : V.gramᵀ.map φ = V.gram.map (ComplexEmbedding.conjugate φ)`. Rewrite using `[hTt]`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`.

Conclude with `WLt.emb_cc φ _`. Rewrite using `[hm]`. Conclude with `hsig _`. Take `⟨W, hWr, hW⟩` from `WLt.main_iso k V.gramᵀ hG hd (by simpa using hk) hsigT`. Rewrite using `[← GlobalTheory.SiegelWeilLitCompare.wittIdx_eq]`.

Use `le_csSup ⟨V.rank, ?_⟩ ⟨W, fun x hx y hy => ?_, hWr⟩` and prove the remaining obligations. Introduce and unpack `r ⟨W', -, rfl⟩`. Conclude with `(Submodule.finrank_le W').trans (by simp)`. Establish `h` using `hW y hy x hx`. Simplify using `only [WLt.hf, dotProduct, mulVec, Function.comp_apply] at h`.

Use `show ∑ i, ∑ j, FD.cc (x i) * V.gram i j * y j = 0`. Rewrite using `[Finset.sum_comm, ← h]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `show FD.cc (x b) * V.gram b a * y a = y a * (V.gram b a * FD.cc (x b))`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wittLBlt : WittLBlt := by
  intro D V k hk hS
  letI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hσ : ∀ x : D.host.E, D.sp.cm.sig x = FD.cc x := fun x => rfl
  have hT : ∀ a b, FD.cc (V.gram a b) = V.gram b a := fun a b => by rw [← hσ]; exact hH.1 b a
  have hTt : V.gramᵀ = V.gram.map FD.cc := Matrix.ext fun a b => (hT a b).symm
  have hG : ∀ a b, FD.cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => by
    simp only [transpose_apply]; exact hT b a
  have hd : V.gramᵀ.det ≠ 0 := by rw [det_transpose]; exact hH.2

  have hsigτ : ∀ τ0 : D.what₂.Tau, k ≤ posIndex (V.gram.map (tauE D τ0)) ∧ k ≤ negIndex (V.gram.map (tauE D τ0)) := by
    intro τ0
    obtain ⟨ε, fr, hu, hfr, hp, hq⟩ := hS τ0
    have hP : (fr.map (starRingEnd ℂ)).det ≠ 0 := by
      have : (fr.map (starRingEnd ℂ)).det = starRingEnd ℂ fr.det := (RingHom.map_det (starRingEnd ℂ) fr).symm
      rw [this]
      exact (map_ne_zero _).2 hu.ne_zero
    have hd' : (fr.map (starRingEnd ℂ))ᵀ * V.gram.map (tauE D τ0) * (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
        diagonal (PositivityTheory.Rg.Sw.sgn ε) := by
      have h1 : (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) = fr := by
        ext a b; simp
      rw [h1]
      exact hfr
    rw [posIndex_eq_card_of_congr_diagonal hP hd', negIndex_eq_card_of_congr_diagonal hP hd']
    have e1 : (Finset.univ.filter fun a => 0 < (PositivityTheory.Rg.Sw.sgn ε a).re) = Finset.univ.filter fun a => ε a = true := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    have e2 : (Finset.univ.filter fun a => (PositivityTheory.Rg.Sw.sgn ε a).re < 0) = Finset.univ.filter fun a => ε a = false := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    rw [e1, e2]
    exact ⟨hp, hq⟩
  have hsig : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gram.map φ) ∧ k ≤ negIndex (V.gram.map φ) := by
    intro φ
    obtain ⟨τ0, h | h⟩ := Formalism.L2.Fam.ThC.tauE_or (D := D) φ
    · rw [← h]; exact hsigτ τ0
    · have hφ : φ = ComplexEmbedding.conjugate (tauE D τ0) := by rw [h]; exact (star_star φ).symm
      rw [hφ, posIndex_map_conjugate _ hT, negIndex_map_conjugate _ hT]
      exact hsigτ τ0
  have hsigT : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gramᵀ.map φ) ∧ k ≤ negIndex (V.gramᵀ.map φ) := by
    intro φ
    have hm : V.gramᵀ.map φ = V.gram.map (ComplexEmbedding.conjugate φ) := by
      rw [hTt]
      ext a b
      simp only [Matrix.map_apply]
      exact WLt.emb_cc φ _
    rw [hm]
    exact hsig _
  obtain ⟨W, hWr, hW⟩ := WLt.main_iso k V.gramᵀ hG hd (by simpa using hk) hsigT
  rw [← GlobalTheory.SiegelWeilLitCompare.wittIdx_eq]
  refine le_csSup ⟨V.rank, ?_⟩ ⟨W, fun x hx y hy => ?_, hWr⟩
  · rintro r ⟨W', -, rfl⟩
    exact (Submodule.finrank_le W').trans (by simp)
  · have h := hW y hy x hx
    simp only [WLt.hf, dotProduct, mulVec, Function.comp_apply] at h
    show ∑ i, ∑ j, FD.cc (x i) * V.gram i j * y j = 0
    rw [Finset.sum_comm, ← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show FD.cc (x b) * V.gram b a * y a = y a * (V.gram b a * FD.cc (x b))
    ring

end PositivityTheory.Rg.Sw.Glob

end
