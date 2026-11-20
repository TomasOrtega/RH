import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def kgT : Lie E a →ₗ[ℝ] ℂ where
  toFun X := ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)
  map_add' X Y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← coordL_apply, map_smul, coordL_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kgT_apply (X : Lie E a) : kgT X = ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) := rfl

def kgH : Herm E a →ₗ[ℝ] Lie E a where
  toFun X := toL X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Establish `h : ∀ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = coord τ (Matrix.trace (X * Y - Y * X))`. Introduce `τ`. Simplify using `only [Matrix.trace, Matrix.diag, map_sum]`. Express the relevant statement in the definitionally equal form `∑ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = 0`. Simplify using `only [h, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, map_zero, Finset.sum_const_zero]`.
-/
theorem kgT_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : kgT (toL (X * Y - Y * X)) = 0 := by
  have h : ∀ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = coord τ (Matrix.trace (X * Y - Y * X)) := by
    intro τ; simp only [Matrix.trace, Matrix.diag, map_sum]
  change ∑ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = 0
  simp only [h, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, map_zero, Finset.sum_const_zero]

variable [IsTotallyComplex E]

/- English proof (translation)
Rewrite using `[kgT_apply, star_sum]`. Repeatedly rewrite using `[star_sum, ← J.coord_conjugate]`. Conclude with `Fintype.sum_equiv (Function.Involutive.toPerm _ fun τ => star_star τ) _ _ fun τ => rfl`.
-/
theorem kgT_star (X : Lie E a) : star (kgT X) = kgT X := by
  rw [kgT_apply, star_sum]
  simp_rw [star_sum, ← J.coord_conjugate]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ fun τ => star_star τ) _ _ fun τ => rfl

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Rewrite using `[J.coord_eq]`. Unfold `atEmb`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem kg_coord_atEmb_self (τ : E →+* ℂ) (z : ℂ) : coord τ (atEmb τ z) = z := by
  rw [J.coord_eq]
  unfold atEmb
  split_ifs <;> simp_all

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Rewrite using `[J.coord_eq]`. Unfold `atEmb`. Apply the tactic sequence `split_ifs <;> simp only [Pi.single_eq_of_ne h, map_zero]`.
-/
theorem kg_coord_atEmb_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  rw [J.coord_eq]
  unfold atEmb
  split_ifs <;> simp only [Pi.single_eq_of_ne h, map_zero]

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate τ ≠ τ`. Introduce `h`. Establish `h1 : (InfinitePlace.mk τ).IsReal` using `InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1`. Rewrite using `[Fintype.sum_eq_add τ (ComplexEmbedding.conjugate τ) hne.symm, J.coord_conjugate, kg_coord_atEmb_self]`.

Both sides reduce to the same expression. Introduce and unpack `τ' ⟨h1, h2⟩`. Use `kg_coord_atEmb_of_ne (fun h => ?_) z` and prove the remaining obligations. Break down `InfinitePlace.mk_eq_iff.1 h with h | h` into its components or cases. Conclude with `h1 h`.

Conclude with `h2 (by rw [← h]; exact (star_star τ').symm)`.
-/
theorem kg_sum_coord_atEmb (τ : E →+* ℂ) (z : ℂ) :
    ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) = z + starRingEnd ℂ z := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := by
    intro h
    have h1 : (InfinitePlace.mk τ).IsReal :=
      InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1
  rw [Fintype.sum_eq_add τ (ComplexEmbedding.conjugate τ) hne.symm, J.coord_conjugate, kg_coord_atEmb_self]
  · rfl
  · rintro τ' ⟨h1, h2⟩
    refine kg_coord_atEmb_of_ne (fun h => ?_) z
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact h1 h
    · exact h2 (by rw [← h]; exact (star_star τ').symm)

/- English proof (translation)
Establish `h : ∀ z : ℂ, kgT (toL (Matrix.single i j (atEmb τ z))) = if i = j then z + starRingEnd ℂ z else 0`. Introduce `z`. Rewrite using `[kgT_apply]`. Use `split_ifs with hij`. Substitute `hij` using the available equality.

Rewrite using `[← kg_sum_coord_atEmb τ z]`. Use `Finset.sum_congr rfl fun τ' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Simplify using `[Ne.symm hk]`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Simplify using `only [toL]`. Rewrite using `[Matrix.of_symm_apply, Matrix.single_apply]`.

Use `split_ifs with h`. Conclude with `absurd (h.1.trans h.2.symm) hij`. Conclude with `map_zero _`. Unfold `cx`. Rewrite using `[h, h]`.

Apply the tactic sequence `split_ifs <;> norm_num [Complex.conj_I]`.
-/
theorem cx_kgT (τ : E →+* ℂ) (i j : Fin a) : cx τ (kgT (E := E) (a := a)) i j = if i = j then 1 else 0 := by
  have h : ∀ z : ℂ, kgT (toL (Matrix.single i j (atEmb τ z))) = if i = j then z + starRingEnd ℂ z else 0 := by
    intro z
    rw [kgT_apply]
    split_ifs with hij
    · subst hij
      rw [← kg_sum_coord_atEmb τ z]
      refine Finset.sum_congr rfl fun τ' _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    · refine Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => ?_
      simp only [toL]
      rw [Matrix.of_symm_apply, Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hij
      · exact map_zero _
  unfold cx
  rw [h, h]
  split_ifs <;> norm_num [Complex.conj_I]

end
end PositivityTheory.Rg.Cz
