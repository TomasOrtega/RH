import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.KapSignFull

/- English proof (translation)
Establish `h0 : Valued.v x ≠ 0` using `by simpa using hx`. Establish `e : Valued.v (cj w x * x) = Valued.v x * Valued.v x` using `by rw [map_mul, hcj]`. Establish `h1 : Valued.v (cj w x * x) ≠ 0` using `by rw [e]; exact mul_ne_zero h0 h0`. Unfold `ordL`. Rewrite using `[dif_neg h1, dif_neg h0]`.

Establish `: WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, e]`. Rewrite using `[this, toAdd_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordL_cj_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (hcj : ∀ x, Valued.v (cj w x) = Valued.v x) (x : w.adicCompletion E) (hx : x ≠ 0) :
    ordL (cj w x * x) = 2 * ordL x := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  have e : Valued.v (cj w x * x) = Valued.v x * Valued.v x := by rw [map_mul, hcj]
  have h1 : Valued.v (cj w x * x) ≠ 0 := by rw [e]; exact mul_ne_zero h0 h0
  unfold ordL
  rw [dif_neg h1, dif_neg h0]
  have : WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, e]
  rw [this, toAdd_mul]; ring

/- English proof (translation)
Introduce `E _ _ _ n w hcj γ`. Unfold `kapSign`. Use `split_ifs with hs`. Both sides reduce to the same expression. Simplify using `only [] set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val γ.val.charpoly)) with hV`.

Establish `htop : V₁ = ⊤` using `by rw [hV, Matrix.aeval_self_charpoly]; simp`. Use `set b := Module.finBasis (w.adicCompletion E) V₁`. Establish `hm : Module.finrank (w.adicCompletion E) V₁ = n`. Rewrite using `[htop, finrank_top]`. Simplify using the standard rewrite rules.

Set `e : Fin (Module.finrank (w.adicCompletion E) V₁) ≃ Fin n` to `finCongr hm`. Set `M : Matrix (Fin n) (Fin n) (w.adicCompletion E)` to `fun k j => (b (e.symm j)).1 k`. Establish `hG : (Matrix.of fun i j => ∑ k, cj w ((b i).1 k) * (b j).1 k) = ((M.map (cj w))ᵀ * M).submatrix e e`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun k _ => rfl`. Establish `hM : M.det ≠ 0`. Establish `hli : LinearIndependent (w.adicCompletion E) M.col`. Establish `h1 : LinearIndependent (w.adicCompletion E) (fun i => ((b i : V₁) : Fin n → w.adicCompletion E))` using `b.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)`. Establish `h2` using `h1.comp e.symm e.symm.injective`.

Establish `hc : M.col = (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) ∘ e.symm` using `by funext j; rfl`. Rewrite using `[hc]`. Conclude with `h2`. Conclude with `(Matrix.isUnit_iff_isUnit_det M).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli) |>.ne_zero`. Rewrite using `[hG, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, show (M.map (cj w)).det = cj w M.det by rw [RingHom.map_det]; rfl, ordL_cj_mul w hcj _ hM]`.

Conclude with `Even.neg_one_zpow ⟨ordL M.det, by ring⟩`.
-/
theorem kapSign_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  intro E _ _ _ n w hcj γ
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only []
    set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val γ.val.charpoly)) with hV
    have htop : V₁ = ⊤ := by rw [hV, Matrix.aeval_self_charpoly]; simp
    set b := Module.finBasis (w.adicCompletion E) V₁
    have hm : Module.finrank (w.adicCompletion E) V₁ = n := by
      rw [htop, finrank_top]; simp
    let e : Fin (Module.finrank (w.adicCompletion E) V₁) ≃ Fin n := finCongr hm
    let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := fun k j => (b (e.symm j)).1 k
    have hG : (Matrix.of fun i j => ∑ k, cj w ((b i).1 k) * (b j).1 k) =
        ((M.map (cj w))ᵀ * M).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => rfl
    have hM : M.det ≠ 0 := by
      have hli : LinearIndependent (w.adicCompletion E) M.col := by
        have h1 : LinearIndependent (w.adicCompletion E) (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) :=
          b.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)
        have h2 := h1.comp e.symm e.symm.injective
        have hc : M.col = (fun i => ((b i : V₁) : Fin n → w.adicCompletion E)) ∘ e.symm := by funext j; rfl
        rw [hc]; exact h2
      exact (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli) |>.ne_zero
    rw [hG, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose, show (M.map (cj w)).det = cj w M.det by rw [RingHom.map_det]; rfl,
      ordL_cj_mul w hcj _ hM]
    exact Even.neg_one_zpow ⟨ordL M.det, by ring⟩

end GlobalTheory.BCT.KapSignFull
