import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.WeilBound.CoreStatements.PublishedTheorems.LanglandsClassification.Bridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `nn : ∀ (Γ : Segment k) (a b : ℂ), (Γ.nu a).nu b = Γ.nu (a + b)`. Introduce `Γ a b`. Apply `GlobalTheory.SmGL.Segment.ext_first` to reduce the goal to its premises. Use `show (Γ.first.nu a).nu b = Γ.first.nu (a + b)`. Conclude with `GlobalTheory.LocGL.IrrGL.nu_nu _ _ _`.

Both sides reduce to the same expression. Establish `n0 : ∀ (Γ : Segment k), Γ.nu 0 = Γ`. Introduce `Γ`. Apply `GlobalTheory.SmGL.Segment.ext_first` to reduce the goal to its premises. Use `show Γ.first.nu 0 = Γ.first`.

Conclude with `GlobalTheory.LocGL.IrrGL.nu_zero _`. Both sides reduce to the same expression. Establish `pr : ∀ (Γ : Segment k), Γ.Precedes (Γ.nu 1)`. Introduce `Γ`. Rewrite using `[GlobalTheory.SmGL.Segment.precedes_iff]`.

Use `⟨1, Nat.one_pos, Γ.len_pos, ?_, ?_⟩` and prove the remaining obligations. Use `show Γ.len < 1 + Γ.len`. Use linear arithmetic over natural numbers and integers. Use `show Γ.first.nu 1 = Γ.first.nu ((1 : ℕ) : ℂ)`. Simplify using the standard rewrite rules.

Establish `le1 : s ≤ s'`. Establish `hp : (Δ.nu (s : ℂ)).Precedes (Δ'.nu ((s' + 1 : ℝ) : ℂ))`. Establish `: Δ'.nu ((s' + 1 : ℝ) : ℂ) = (Δ.nu (s : ℂ)).nu 1`. Rewrite using `[h, nn]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `pr _`. Use `PositivityTheory.UdReth2.add_one_le_of_precedes Δ Δ' hΔ hΔ' s (s' + 1) hp` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `le2 : s' ≤ s`. Establish `hp : (Δ'.nu (s' : ℂ)).Precedes (Δ.nu ((s + 1 : ℝ) : ℂ))`. Establish `: Δ.nu ((s + 1 : ℝ) : ℂ) = (Δ'.nu (s' : ℂ)).nu 1`. Rewrite using `[← h, nn]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `pr _`. Use `PositivityTheory.UdReth2.add_one_le_of_precedes Δ' Δ hΔ' hΔ s' (s + 1) hp` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs : s = s'` using `le_antisymm le1 le2`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Substitute `hs` using the available equality. Use `congrArg (fun Γ => Γ.nu (-(s : ℂ))) h` as an intermediate fact. Simplify using `only [nn, add_neg_cancel, n0] at this`.

Conclude with `this`.
-/
theorem eq_of_nu_eq {Δ Δ' : Segment k} (hΔ : PositivityTheory.UdReth2.IsCentred Δ) (hΔ' : PositivityTheory.UdReth2.IsCentred Δ')
    {s s' : ℝ} (h : Δ.nu (s : ℂ) = Δ'.nu (s' : ℂ)) : s = s' ∧ Δ = Δ' := by
  have nn : ∀ (Γ : Segment k) (a b : ℂ), (Γ.nu a).nu b = Γ.nu (a + b) := by
    intro Γ a b
    apply GlobalTheory.SmGL.Segment.ext_first
    · show (Γ.first.nu a).nu b = Γ.first.nu (a + b)
      exact GlobalTheory.LocGL.IrrGL.nu_nu _ _ _
    · rfl
  have n0 : ∀ (Γ : Segment k), Γ.nu 0 = Γ := by
    intro Γ
    apply GlobalTheory.SmGL.Segment.ext_first
    · show Γ.first.nu 0 = Γ.first
      exact GlobalTheory.LocGL.IrrGL.nu_zero _
    · rfl
  have pr : ∀ (Γ : Segment k), Γ.Precedes (Γ.nu 1) := by
    intro Γ
    rw [GlobalTheory.SmGL.Segment.precedes_iff]
    refine ⟨1, Nat.one_pos, Γ.len_pos, ?_, ?_⟩
    · show Γ.len < 1 + Γ.len
      omega
    · show Γ.first.nu 1 = Γ.first.nu ((1 : ℕ) : ℂ)
      simp
  have le1 : s ≤ s' := by
    have hp : (Δ.nu (s : ℂ)).Precedes (Δ'.nu ((s' + 1 : ℝ) : ℂ)) := by
      have : Δ'.nu ((s' + 1 : ℝ) : ℂ) = (Δ.nu (s : ℂ)).nu 1 := by
        rw [h, nn]
        push_cast
        rfl
      rw [this]
      exact pr _
    have := PositivityTheory.UdReth2.add_one_le_of_precedes Δ Δ' hΔ hΔ' s (s' + 1) hp
    linarith
  have le2 : s' ≤ s := by
    have hp : (Δ'.nu (s' : ℂ)).Precedes (Δ.nu ((s + 1 : ℝ) : ℂ)) := by
      have : Δ.nu ((s + 1 : ℝ) : ℂ) = (Δ'.nu (s' : ℂ)).nu 1 := by
        rw [← h, nn]
        push_cast
        rfl
      rw [this]
      exact pr _
    have := PositivityTheory.UdReth2.add_one_le_of_precedes Δ' Δ hΔ' hΔ s' (s + 1) hp
    linarith
  have hs : s = s' := le_antisymm le1 le2
  refine ⟨hs, ?_⟩
  subst hs
  have := congrArg (fun Γ => Γ.nu (-(s : ℂ))) h
  simp only [nn, add_neg_cancel, n0] at this
  exact this

/- English proof (translation)
The claim follows from `PositivityTheory.Lit1.eq_of_isLSeg h h'`.
-/
theorem eq_of_isLSeg' {Δ : Segment k} {δ δ' : IrrGL k} (h : IsLSeg Δ δ.rep) (h' : IsLSeg Δ δ'.rep) : δ = δ' :=
  PositivityTheory.Lit1.eq_of_isLSeg h h'

end Local

end PositivityTheory.Gud.Pf

end
