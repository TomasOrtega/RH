import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLargeStatement

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

namespace GlobalTheory.HSApp

/- English proof (translation)
Take `⟨ε1, hε1, H⟩` from `GlobalTheory.T.runSizes_quotientGaps_large`. Use `⟨ε1, hε1, fun eps he hle => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `H eps he hle`. Use `⟨K, fun Fm CH hc hL => ?_⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `hK Fm CH hc hL`.

Use `⟨0, le_rfl, x0, fun x hx hxx ι p _ i hi => ?_⟩` and prove the remaining obligations. Take `⟨hD1, hDT, hG⟩` from `hx0 x hx hxx ι`. Take `⟨hr, hdim, hgap⟩` from `GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi`. Establish `hlen : lenT p i (Fm.parT x hx ι).PP = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) / ((Fm.D x ι).R.m : ℝ)⌉₊`. Rewrite using `[lenT, GlobalTheory.CompHS.dimFlag_eq, hdim]`.

Take `⟨hG1, hG2⟩` from `hG _ _ rfl hlen`. Establish `hc0 : ((cZero (Fm.D x ι) ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4`. Conclude with `(cZero_spec (Fm.D x ι) ((i : ℕ) + 1)).2.2` after adjusting the coercions. Use `clear H hK hx0 hG`. Use `⟨fun τ k hk => ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[WtPar.gap_u₁ _ τ hk, WtPar.gap_uMinus_sub_kap _ τ hk]`. Simplify using `only [WtPar.T₁]`. Rewrite using `[hdim]`. Establish `hGeq : ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * ((dat p i).p + (dat p i).q) + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) * (((Fm.D x ι).R.f * (Fm.D x ι).R.r. …` using `by rw [hr]`. Rewrite using `[hGeq]`.

Establish `hr2 : (((dat p i).p + (dat p i).q : ℕ) : ℤ) = (Fm.D x ι).R.r` using `by exact_mod_cast hr`. Generalize the expression as in `((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) = G at hG1 hG2 ⊢`. Generalize the expression as in `lenT p i (Fm.parT x hx ι).PP = T at hG1 hG2 ⊢`. Generalize the expression as in `(Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 = Dd at hG1 hG2 ⊢`. Establish `hT : (0 : ℤ) < (T : ℤ) + (Dd : ℤ) + 1` using `by positivity`.

Use `Int.le_ediv_of_mul_le hT ?_` and prove the remaining obligations. Take `⟨g1, g2⟩` from `hgap τ k hk`. Distinguish the cases in `hb : k + 1 = (dat p i).p`. Rewrite using `[if_pos hb, hr2]`. Establish `e` using `g2 hb`.

Establish `: (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤ ((gap (uW p i τ) k + (-(cZero (Fm.D x ι) ((i : ℕ) + 1)) - (2 * ((Fm.D x ι).R.r : ℤ) - 2)) : ℤ) : ℝ)`. Move the coercions through the operations in `at hG2 e ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Rewrite using `[if_neg hb]`.

Establish `e` using `g1 hb`. Establish `: (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤ ((gap (uW p i τ) k + 2 : ℤ) : ℝ)`. Move the coercions through the operations in `at hG1 e ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.

Use `show GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i (Fm.parT x hx ι).PP`. Rewrite using `[hdim, hlen]`. Conclude with `hDT`. Use `show 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i)`. Rewrite using `[hdim]`.

Conclude with `hD1`.
-/
theorem wtBig_run : Lifts fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    WtBig (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) := by
  obtain ⟨ε1, hε1, H⟩ := GlobalTheory.T.runSizes_quotientGaps_large
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨0, le_rfl, x0, fun x hx hxx ι p _ i hi => ?_⟩
  obtain ⟨hD1, hDT, hG⟩ := hx0 x hx hxx ι
  obtain ⟨hr, hdim, hgap⟩ := GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi
  have hlen : lenT p i (Fm.parT x hx ι).PP = ⌈(Fm.parT x hx ι).PP ^ 2 *
      (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) / ((Fm.D x ι).R.m : ℝ)⌉₊ := by
    rw [lenT, GlobalTheory.CompHS.dimFlag_eq, hdim]
  obtain ⟨hG1, hG2⟩ := hG _ _ rfl hlen
  have hc0 : ((cZero (Fm.D x ι) ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 := by
    exact_mod_cast (cZero_spec (Fm.D x ι) ((i : ℕ) + 1)).2.2
  clear H hK hx0 hG
  refine ⟨fun τ k hk => ?_, ?_, ?_⟩
  · rw [WtPar.gap_u₁ _ τ hk, WtPar.gap_uMinus_sub_kap _ τ hk]
    simp only [WtPar.T₁]
    rw [hdim]
    have hGeq : ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * ((dat p i).p + (dat p i).q) +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) =
        ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) := by rw [hr]
    rw [hGeq]
    have hr2 : (((dat p i).p + (dat p i).q : ℕ) : ℤ) = (Fm.D x ι).R.r := by exact_mod_cast hr
    generalize ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) = G at hG1 hG2 ⊢
    generalize lenT p i (Fm.parT x hx ι).PP = T at hG1 hG2 ⊢
    generalize (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 = Dd at hG1 hG2 ⊢
    have hT : (0 : ℤ) < (T : ℤ) + (Dd : ℤ) + 1 := by positivity
    refine Int.le_ediv_of_mul_le hT ?_
    obtain ⟨g1, g2⟩ := hgap τ k hk
    by_cases hb : k + 1 = (dat p i).p
    · rw [if_pos hb, hr2]
      have e := g2 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤
          ((gap (uW p i τ) k + (-(cZero (Fm.D x ι) ((i : ℕ) + 1)) - (2 * ((Fm.D x ι).R.r : ℤ) - 2)) : ℤ) : ℝ) := by
        push_cast at hG2 e ⊢
        linarith
      exact_mod_cast this
    · rw [if_neg hb]
      have e := g1 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤ ((gap (uW p i τ) k + 2 : ℤ) : ℝ) := by
        push_cast at hG1 e ⊢
        linarith
      exact_mod_cast this
  · show GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i (Fm.parT x hx ι).PP
    rw [hdim, hlen]; exact hDT
  · show 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i)
    rw [hdim]; exact hD1

end GlobalTheory.HSApp
