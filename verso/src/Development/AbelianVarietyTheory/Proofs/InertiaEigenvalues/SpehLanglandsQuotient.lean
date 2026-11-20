import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.LocGL

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsLSeg.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : IrrGL k} {Δ : Segment k} (h : IsLSeg Δ δ.rep) (c : ℂ) : IsLSeg (Δ.nu c) (δ.nu c).rep :=
  (h.tw (absPow k c) (isSmoothChar_absPow c)).of_equiv (δ.twEquiv _ _)

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsSpeh.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ x : IrrGL k} {m : ℕ} (h : IsSpeh δ m x.rep) (s : ℂ) : IsSpeh (δ.nu s) m (x.nu s).rep := by
  obtain ⟨hd, h'⟩ := h.tw (absPow k s) (isSmoothChar_absPow s)
  exact ⟨hd, h'.of_equiv (x.twEquiv _ _) (.refl _)⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isL_speh_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hP : ∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) :
    ∀ (δ x : IrrGL k) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  intro δ x Δ m hL hU hS s
  obtain ⟨hd, hc⟩ := hS.nu_rep (s : ℂ)
  set c : Fin m → ℝ := fun i => s + ((m : ℝ) - 1) / 2 - (i : ℕ) with hcdef
  have hy : ∀ i, spehFactor (δ.nu s) m i = δ.nu (c i : ℂ) := fun i => by
    simp only [spehFactor, IrrGL.nu_nu, hcdef]
    congr 1
    push_cast
    ring
  refine ⟨m, spehFactor (δ.nu s) m, hd, ⟨fun i => Δ.nu (c i : ℂ), ⟨?_, ?_⟩, ?_⟩, hc⟩
  · rw [Fin.univ_val_map]
  · intro i j hij hp
    have h1 := hP δ δ Δ Δ hL hU hL hU (c i) (c j) hp
    have h2 : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    simp only [hcdef] at h1
    linarith
  · intro i
    rw [hy i]
    exact hL.nu_rep _

end GlobalTheory.LocGL
