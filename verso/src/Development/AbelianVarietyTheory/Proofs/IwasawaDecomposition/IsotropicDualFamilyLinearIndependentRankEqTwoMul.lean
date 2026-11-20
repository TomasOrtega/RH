import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `r d M e f hiso hdual hspan`. Establish `hli : LinearIndependent ℝ (Sum.elim e f)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fintype.sum_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hg`. Establish `hb : ∀ k, g (Sum.inr k) = 0`. Introduce `k`. Establish `h` using `congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg`. Simplify `h` using `[add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual]`.

Establish `ha : ∀ k, g (Sum.inl k) = 0`. Introduce `k`. Establish `hg' : ∑ i, g (Sum.inl i) • e i = 0` using `by simpa [hb] using hg`. Establish `h` using `congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'`. Simplify `h` using `[Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual]`.

Introduce and unpack `(k | k)`. Conclude with `ha k`. Conclude with `hb k`. Use `⟨hli, ?_⟩` and prove the remaining obligations. Establish `h1` using `finrank_span_eq_card hli`.

Rewrite `h1` using `[hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
