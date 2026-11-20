import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

/- English proof (translation)
Introduce `l _ A _ D s hs`. Set `N` to `Ideal.span s`. Set `g : A →+* W2 l (A ⧸ N)` to `(W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)`. Establish `hg : ∀ a ∈ N, g a = 0`. Introduce `a ha`.

Establish `hle : N ≤ RingHom.ker g`. Use `Ideal.span_le.2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Use `W2.ext ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)`. Conclude with `hle ha`. Set `sec : A ⧸ N →+* W2 l (A ⧸ N)` to `Ideal.Quotient.lift N g hg`. Establish `hsec : ∀ a, (sec a).fst = a`. Introduce `a`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Both sides reduce to the same expression. Conclude with `⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩`.
-/
theorem GlobalTheory.BSP.delta_quot_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  intro l _ A _ D s hs
  let N := Ideal.span s
  let g : A →+* W2 l (A ⧸ N) := (W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)
  have hg : ∀ a ∈ N, g a = 0 := by
    intro a ha
    have hle : N ≤ RingHom.ker g := by
      refine Ideal.span_le.2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      refine W2.ext ?_ ?_
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)
    exact hle ha
  let sec : A ⧸ N →+* W2 l (A ⧸ N) := Ideal.Quotient.lift N g hg
  have hsec : ∀ a, (sec a).fst = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  exact ⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩
