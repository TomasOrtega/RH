import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `E L E' L' _ _ _ _ _ _ _ j jL hcomp hadj hrank z`. Use `set n := Module.finrank E L`. Set `b : Module.Basis (Fin n) E L` to `Module.finBasis E L`. Establish `hpos : 0 < Module.finrank E' L'` using `by rw [hrank]; exact Module.finrank_pos`. Use `haveI : FiniteDimensional E' L' := Module.finite_of_finrank_pos hpos`.

Set `v : Fin n → L'` to `fun k => jL (b k)`. Establish `hexp : ∀ w : L, jL w = ∑ k, j (b.repr w k) • v k`. Introduce `w`. Use `conv_lhs => rw [← b.sum_repr w]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, hcomp, ← Algebra.smul_def]`. Establish `hspan : Submodule.span E' (Set.range jL) ≤ Submodule.span E' (Set.range v)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`.

Rewrite using `[hexp w]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Establish `hadj' : Subalgebra.toSubmodule (Algebra.adjoin E' (Set.range jL)) = Submodule.span E' (Set.range jL)`. Apply `Algebra.adjoin_eq_span_of_subset` to reduce the goal to its premises. Establish `: (Submonoid.closure (Set.range jL) : Set L') = Set.range jL`.

Use `Submonoid.closure_eq (MonoidHom.mrange (jL : L →* L'))` as an intermediate fact. Simplify using `using congrArg (fun S : Submonoid L' => (S : Set L')) this`. Rewrite using `[this]`. Conclude with `Submodule.subset_span`. Establish `htop : (⊤ : Submodule E' L') ≤ Submodule.span E' (Set.range v)`.

Rewrite `hadj'` using `[hadj, Algebra.top_toSubmodule]`. Rewrite using `[hadj']`. Conclude with `hspan`. Set `b' : Module.Basis (Fin n) E' L'` to `basisOfTopLeSpanOfCardEqFinrank v htop (by simp [hrank, n])`. Establish `hb' : ∀ k, b' k = v k` using `fun k => by simp [b']`.

Establish `hrepr : ∀ w : L, ∀ i, b'.repr (jL w) i = j (b.repr w i)`. Introduce `w i`. Establish `: jL w = b'.equivFun.symm (fun k => j (b.repr w k))`. Rewrite using `[Module.Basis.equivFun_symm_apply, hexp w]`. Simplify using `[hb']`.

Rewrite using `[← b'.equivFun_apply, this, LinearEquiv.apply_symm_apply]`. Rewrite using `[Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', v, ← map_mul, hrepr]`.
-/
theorem trace_map_of_adjoin_range_eq_top_of_finrank_eq : ∀ (E L E' L' : Type) [Field E] [Field L] [Algebra E L] [FiniteDimensional E L] [Field E'] [Field L'] [Algebra E' L'] (j : E →+* E') (jL : L →+* L'), (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Module.finrank E' L' = Module.finrank E L → ∀ z, Algebra.trace E' L' (jL z) = j (Algebra.trace E L z) := by
  intro E L E' L' _ _ _ _ _ _ _ j jL hcomp hadj hrank z
  classical
  set n := Module.finrank E L
  let b : Module.Basis (Fin n) E L := Module.finBasis E L
  have hpos : 0 < Module.finrank E' L' := by rw [hrank]; exact Module.finrank_pos
  haveI : FiniteDimensional E' L' := Module.finite_of_finrank_pos hpos
  let v : Fin n → L' := fun k => jL (b k)
  have hexp : ∀ w : L, jL w = ∑ k, j (b.repr w k) • v k := by
    intro w
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hcomp, ← Algebra.smul_def]
  have hspan : Submodule.span E' (Set.range jL) ≤ Submodule.span E' (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [hexp w]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hadj' : Subalgebra.toSubmodule (Algebra.adjoin E' (Set.range jL)) = Submodule.span E' (Set.range jL) := by
    apply Algebra.adjoin_eq_span_of_subset
    have : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL := by
      have := Submonoid.closure_eq (MonoidHom.mrange (jL : L →* L'))
      simpa using congrArg (fun S : Submonoid L' => (S : Set L')) this
    rw [this]; exact Submodule.subset_span
  have htop : (⊤ : Submodule E' L') ≤ Submodule.span E' (Set.range v) := by
    rw [hadj, Algebra.top_toSubmodule] at hadj'
    rw [hadj']; exact hspan
  let b' : Module.Basis (Fin n) E' L' := basisOfTopLeSpanOfCardEqFinrank v htop (by simp [hrank, n])
  have hb' : ∀ k, b' k = v k := fun k => by simp [b']
  have hrepr : ∀ w : L, ∀ i, b'.repr (jL w) i = j (b.repr w i) := by
    intro w i
    have : jL w = b'.equivFun.symm (fun k => j (b.repr w k)) := by
      rw [Module.Basis.equivFun_symm_apply, hexp w]
      simp [hb']
    rw [← b'.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', v, ← map_mul, hrepr]

end GlobalTheory
