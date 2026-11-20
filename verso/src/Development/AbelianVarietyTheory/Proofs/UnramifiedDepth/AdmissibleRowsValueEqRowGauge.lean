import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ValOfKindIndep

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal

open GlobalTheory.RowValueCheck

/- English proof (translation)
Introduce `C _ V d _ I _ κ _ X H N P kind hk gr`. Rewrite using `[valOf_eq]`. Use `set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS`. Establish `key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf (X.rowData H).hL (kind ρ)) X.hRow`. Introduce `ρ μ hμ`.

Break down `hr : kind ρ with _ | ⟨g, a, a'⟩` into its components or cases. Take `⟨g, hg⟩` from `hk.2 ρ hr`. Establish `h1 : ∀ w, μ w ≠ 0 → w.1 = g` using `fun w hw => by`. Take `⟨ν, hν, hν'⟩` from `hμ w hw`. Conclude with `hg ν hν w hν'`.

Use `show (0 : C) = _`. Use `(H.axes μ ?_).symm` and prove the remaining obligations. Establish `hg2 : g = 0 ∨ g = 1` using `(by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g`. Break down `hg2 with rfl | rfl` into its components or cases. Conclude with `Or.inl fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)`.

Conclude with `Or.inr fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)`. Take `⟨-, -, hl⟩` from `hk.1 ρ g a a' hr`. Establish `h1 : ∀ w, μ w ≠ 0 → X.OnLf g a a' w` using `fun w hw => by`. Take `⟨ν, hν, hν'⟩` from `hμ w hw`. Conclude with `hl ν hν w hν'`.

Conclude with `if_pos fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)`. Establish `hA` using `Agree.prod (S := S) Finset.univ (fun ρ => Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl) (agree_rowCopy S ρ _ _ (key ρ)).exp)`. Unfold `jetAt0`. Conclude with `Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]`.
-/
theorem valOf_eq_hRow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  intro C _ V d _ I _ κ _ X H N P kind hk gr
  classical
  rw [valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf (X.rowData H).hL (kind ρ)) X.hRow := by
    intro ρ μ hμ
    rcases hr : kind ρ with _ | ⟨g, a, a'⟩
    · obtain ⟨g, hg⟩ := hk.2 ρ hr
      have h1 : ∀ w, μ w ≠ 0 → w.1 = g := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hg ν hν w hν'
      show (0 : C) = _
      refine (H.axes μ ?_).symm
      have hg2 : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
      rcases hg2 with rfl | rfl
      · exact Or.inl fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
      · exact Or.inr fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
    · obtain ⟨-, -, hl⟩ := hk.1 ρ g a a' hr
      have h1 : ∀ w, μ w ≠ 0 → X.OnLf g a a' w := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hl ν hν w hν'
      exact if_pos fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]

end GlobalTheory.RowVal
