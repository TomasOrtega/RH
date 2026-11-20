import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormHeckeProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePolynomialFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NonVanBottom

/- English proof (translation)
Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers.
-/
theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  omega

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem exists_ne_zero_of_integral {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ}
    (h : (∫ y in S, ‖f y‖ ^ 2 ∂ν) ≠ 0) : ∃ y, f y ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (by simp [hc])

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_ne_zero_of_norm_formula {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ} {c : ℂ}
    {Λ : ℂ → ℂ} {a b : ℤ} (hc : c ≠ 0) (hΛ : ∀ s : ℤ, a ≤ s → s ≤ b → Λ s ≠ 0)
    (h : ((∫ y in S, ‖f y‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc a b, Λ s) : ∃ y, f y ≠ 0 := by
  refine exists_ne_zero_of_integral (ν := ν) (S := S) fun h0 => ?_
  have hp : ∏ s ∈ Icc a b, Λ s ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => hΛ s (mem_Icc.1 hs).1 (mem_Icc.1 hs).2
  rw [h0, Complex.ofReal_zero] at h
  exact mul_ne_zero hc hp h.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nonvan : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
      IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  intro hP hK hM hL
  obtain ⟨a1, h1⟩ := GlobalTheory.T.petersson_norm_hecke_product hP
  obtain ⟨a2, h2⟩ := GlobalTheory.T.bottom_triangle_polynomial_factor hP.howeDualityReal hP hK hM hL
  obtain ⟨a3, h3⟩ := hL
  refine ⟨max (max a1 a2) a3, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCF)
  obtain ⟨C3, x3, k3⟩ := h3 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max (max C1 C2) C3, max (max x1 x2) x3, fun C hC D large₂ he hx hr T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩
  have n1 := k1 C (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX t
  have n2 := k2 C (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Λ, hΛ, hne⟩ := ((k3 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G) i j).1 t
  have hh : ((h0 D i j : ℕ) : ℤ) ≤ (halfRank D i j : ℤ) := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨P, ν, 𝓕, c, hc, -, -, hf⟩ := n1
  obtain ⟨Pi, p, p', J, -, ⟨P', hP'⟩, hJ, hI, hI'⟩ := n2
  obtain ⟨y, hy⟩ := exists_ne_zero_of_norm_formula hc (fun s hs hs' => hne s hs (hs'.trans hh)) (hf Λ hΛ)
  refine ⟨⟨P, y, hy⟩, P', ?_⟩
  obtain ⟨lam, hlam⟩ := hI t
  have hinj : Function.Injective (J t) := by
    refine (hJ t).resolve_left fun h0 => hy ?_
    rw [hlam P, h0]
    simp
  by_contra hc'
  push_neg at hc'
  apply hP'
  apply hinj
  rw [← hI' t P', map_zero]
  exact funext hc'

end GlobalTheory.NonVanBottom

end
