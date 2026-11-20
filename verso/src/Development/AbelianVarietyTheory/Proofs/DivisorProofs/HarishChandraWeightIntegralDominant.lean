import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

variable {n : ℕ}

/- English proof (translation)
Establish `h : (univ.filter fun b => ε b = ε a) = ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a)) ∪ {a}`. Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Break down `lt_trichotomy a b with h1 | h1 | h1` into its components or cases. Conclude with `Or.inl (Or.inl ⟨h1, h⟩)`. Conclude with `Or.inr h1.symm`. Conclude with `Or.inl (Or.inr ⟨h1, h⟩)`. Introduce and unpack `((⟨_, h⟩ | ⟨_, h⟩) | rfl)`.

Conclude with `h`. Conclude with `h`. Both sides reduce to the same expression. Establish `d1 : Disjoint (univ.filter fun b => a < b ∧ ε b = ε a) (univ.filter fun b => b < a ∧ ε b = ε a)`. Rewrite using `[disjoint_filter]`.

Introduce `x _ h1 h2`. Conclude with `lt_asymm h1.1 h2.1`. Establish `d2 : Disjoint ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a)) {a}`. Rewrite using `[disjoint_singleton_right]`. Simplify using the standard rewrite rules.

Rewrite using `[h, card_union_of_disjoint d2, card_union_of_disjoint d1, card_singleton]`.
-/
theorem card_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 =
      (univ.filter fun b => ε b = ε a).card := by
  have h : (univ.filter fun b => ε b = ε a) =
      ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a)) ∪ {a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
    constructor
    · intro h
      rcases lt_trichotomy a b with h1 | h1 | h1
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inr h1.symm
      · exact Or.inl (Or.inr ⟨h1, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | rfl)
      · exact h
      · exact h
      · rfl
  have d1 : Disjoint (univ.filter fun b => a < b ∧ ε b = ε a) (univ.filter fun b => b < a ∧ ε b = ε a) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    exact lt_asymm h1.1 h2.1
  have d2 : Disjoint ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a))
      {a} := by
    rw [disjoint_singleton_right]
    simp
  rw [h, card_union_of_disjoint d2, card_union_of_disjoint d1, card_singleton]

/- English proof (translation)
Unfold `pOf qOf`. Use `card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)` as an intermediate fact. Simplify using `using this`.
-/
theorem p_add_q (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simpa using this

/- English proof (translation)
Establish `hcR : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 = ((univ.filter fun b => ε b = ε a).card : ℝ)` using `by exact_mod_cast card_split ε a`. Establish `hpqR : (pOf ε : ℝ) + qOf ε = n` using `by exact_mod_cast p_add_q ε`. Establish `hma` using `hm a`. Simplify using `only [gaW, Pi.add_apply, Pi.sub_apply, rhoC, rhoHol, ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK]`. Distinguish the cases in `h : ε a = true`.

Establish `hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = pOf ε` using `by simp [pOf, h]`. Rewrite using `[if_pos h, if_pos h]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = qOf ε`.

Simplify using `only [Bool.not_eq_true] at h`. Simplify using `[qOf, h]`. Rewrite using `[if_neg h, if_neg h]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gaW_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (a : Fin n) :
    gaW ε lam a = ((m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a : ℤ) : ℝ) := by
  have hcR : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 =
      ((univ.filter fun b => ε b = ε a).card : ℝ) := by exact_mod_cast card_split ε a
  have hpqR : (pOf ε : ℝ) + qOf ε = n := by exact_mod_cast p_add_q ε
  have hma := hm a
  simp only [gaW, Pi.add_apply, Pi.sub_apply, rhoC, rhoHol, ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK]
  by_cases h : ε a = true
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = pOf ε := by simp [pOf, h]
    rw [if_pos h, if_pos h]
    push_cast
    linarith
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = qOf ε := by
      simp only [Bool.not_eq_true] at h
      simp [qOf, h]
    rw [if_neg h, if_neg h]
    push_cast
    linarith

end GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

namespace GlobalTheory.PsCo.PcEF

/- English proof (translation)
Introduce `n ε lam hlam`. Take `⟨hanti, hz⟩` from `hlam`. Use `choose z hz using hz`. Set `m : Fin n → ℤ` to `fun a => z a + ((n : ℤ) - 1)`. Establish `hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a`.

Introduce `a`. Use `hz a` as an intermediate fact. Simplify using `only [m]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `Λ : Fin n → ℤ` to `fun a => m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a`. Establish `hg : gaW ε lam = fun a => (Λ a : ℝ)` using `funext fun a => HarishChandraWeightIntegral.gaW_eq ε lam m hm a`. Use `⟨Λ, m, hg, ?_, hm, ?_⟩` and prove the remaining obligations. Introduce `a b hab he`. Establish `hBA : BlockAnti ε lam`.

Introduce `a b hab _`. Establish `h1` using `hanti hab`. Establish `h2 : (m b : ℝ) < m a` using `by linarith [hm a, hm b]`. Establish `h3 : m b < m a` using `by exact_mod_cast h2`. Establish `h4 : ((m b : ℤ) : ℝ) + 1 ≤ m a` using `by exact_mod_cast h3`.

Combine the linear relations using `[hm a, hm b]`. Establish `h` using `lf_dom_block hBA a b hab he`. Establish `e : lowK ε lam + (rhoHol ε - rhoN ε) = gaW ε lam`. Use function extensionality and compare the values at `x`. Simplify using `only [lowK, gaW, Pi.add_apply, Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e, hg]`. Establish `h' : (Λ b : ℝ) ≤ Λ a` using `h`. Conclude with `h'` after adjusting the coercions. Introduce `a`.

Simplify using `only [Λ, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem harishChandraWeight_integral_dominant : GaInt := by
  intro n ε lam hlam
  obtain ⟨hanti, hz⟩ := hlam
  choose z hz using hz
  let m : Fin n → ℤ := fun a => z a + ((n : ℤ) - 1)
  have hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a := by
    intro a
    have := hz a
    simp only [m]
    push_cast
    linarith
  let Λ : Fin n → ℤ := fun a =>
    m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a
  have hg : gaW ε lam = fun a => (Λ a : ℝ) := funext fun a => HarishChandraWeightIntegral.gaW_eq ε lam m hm a
  refine ⟨Λ, m, hg, ?_, hm, ?_⟩
  · intro a b hab he
    have hBA : BlockAnti ε lam := by
      intro a b hab _
      have h1 := hanti hab
      have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
      have h3 : m b < m a := by exact_mod_cast h2
      have h4 : ((m b : ℤ) : ℝ) + 1 ≤ m a := by exact_mod_cast h3
      linarith [hm a, hm b]
    have h := lf_dom_block hBA a b hab he
    have e : lowK ε lam + (rhoHol ε - rhoN ε) = gaW ε lam := by
      funext x
      simp only [lowK, gaW, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e, hg] at h
    have h' : (Λ b : ℝ) ≤ Λ a := h
    exact_mod_cast h'
  · intro a
    simp only [Λ, Pi.add_apply]
    ring

end GlobalTheory.PsCo.PcEF

end
end
