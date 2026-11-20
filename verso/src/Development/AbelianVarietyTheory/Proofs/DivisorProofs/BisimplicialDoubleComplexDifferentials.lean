import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]`. Break down `Fin.lt_or_le (Fin.castSucc j) i with hj | hj` into its components or cases. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ hj]`. Establish `: (j : ℕ) < i` using `hj`.

Simplify using `only [this, if_true, Fin.coe_castSucc]`. Use `j.isLt` as an intermediate fact. Simplify using `only [SimplexCategory.len_mk] at this ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ hj]`.

Establish `: ¬ (j : ℕ) < i` using `by simpa [Fin.le_iff_val_le_val] using hj`. Simplify using `only [this, if_false, Fin.val_succ]`. Use `j.isLt` as an intermediate fact. Simplify using `only [SimplexCategory.len_mk] at this ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem fc_eq_δ (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rcases Fin.lt_or_le (Fin.castSucc j) i with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have : (j : ℕ) < i := hj
    simp only [this, if_true, Fin.coe_castSucc]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ hj]
    have : ¬ (j : ℕ) < i := by simpa [Fin.le_iff_val_le_val] using hj
    simp only [this, if_false, Fin.val_succ]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega

/- English proof (translation)
Use extensionality with `j`. Simplify using `[idc, clampHom, SimplexCategory.mkHom]`. Use linear arithmetic over natural numbers and integers.
-/
theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom, SimplexCategory.mkHom]
  omega

/- English proof (translation)
The claim follows from `(HomologicalComplex.eval C c i).map_sum f s`.
-/
theorem hsum_f {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {α : Type} (s : Finset α) (f : α → (K ⟶ L)) (i : ι) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i :=
  (HomologicalComplex.eval C c i).map_sum f s

section
variable {C : Type u} [Category.{v} C] [Preadditive C]

/- English proof (translation)
Simplify using `only [dH, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop, idc_self, op_id, CategoryTheory.Functor.map_id, Category.comp_id]`. Rewrite using `[Finset.sum_range]`. Simplify using `only [dbl, alternatingFaceMapComplex]`. Rewrite using `[AlternatingFaceMapComplex.obj_d_eq, hsum_f]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[HomologicalComplex.zsmul_f_apply, fc_eq_δ]`. Both sides reduce to the same expression.
-/
theorem dbl_d_f (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).d (a + 1) a).f b = (ev Y).map (dH (a + 1) b a b) := by
  simp only [dH, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Finset.sum_range]
  dsimp only [dbl, alternatingFaceMapComplex]
  rw [AlternatingFaceMapComplex.obj_d_eq, hsum_f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [HomologicalComplex.zsmul_f_apply, fc_eq_δ]
  rfl

/- English proof (translation)
Simplify using `only [dV, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop, idc_self, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]`. Rewrite using `[Finset.sum_range]`. Express the relevant statement in the definitionally equal form `(AlternatingFaceMapComplex.obj (Y.obj (op (SimplexCategory.mk a)))).d (b + 1) b = _`. Rewrite using `[AlternatingFaceMapComplex.obj_d_eq]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[fc_eq_δ]`. Both sides reduce to the same expression.
-/
theorem dbl_X_d (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).X a).d (b + 1) b = (ev Y).map (dV a (b + 1) a b) := by
  simp only [dV, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [Finset.sum_range]
  change (AlternatingFaceMapComplex.obj (Y.obj (op (SimplexCategory.mk a)))).d (b + 1) b = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fc_eq_δ]
  rfl

variable [HasFiniteCoproducts C]

/- English proof (translation)
Rewrite using `[HomologicalComplex₂.ι_D₁]`. Break down `a with _ | a` into its components or cases. Rewrite using `[HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]`. Use `symm`. Use `Finset.sum_eq_zero (fun x _ => ?_)` and prove the remaining obligations.

Establish `hx : ¬ (0 = x.1.1 + 1 ∧ b = x.1.2)` using `by omega`. Simplify using `only [dH, hx, if_false, Functor.map_zero]`. Conclude with `zero_comp`. Rewrite using `[HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (a + 1) a from rfl) b k (by simp only [ComplexShape.π_def]; omega)]`. Rewrite using `[Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]`.

Rewrite using `[dbl_d_f]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Introduce and unpack `⟨⟨x1, x2⟩, hx⟩ _ hne`. Establish `: ¬ (a + 1 = x1 + 1 ∧ b = x2)`.

Introduce and unpack `⟨h1, h2⟩`. Apply `hne` to reduce the goal to its premises. Substitute `h2` using the available equality. Establish `: x1 = a` using `by omega`. Substitute `this` using the available equality.

Both sides reduce to the same expression. Simplify using `only [dH, this, if_false, Functor.map_zero]`. Conclude with `zero_comp`. Introduce `hn`. Conclude with `absurd (Finset.mem_attach _ _) hn`.
-/
theorem ιTotal_D₁ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₁ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dH a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  rw [HomologicalComplex₂.ι_D₁]
  rcases a with _ | a
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (0 = x.1.1 + 1 ∧ b = x.1.2) := by omega
    simp only [dH, hx, if_false, Functor.map_zero]
    exact zero_comp
  · rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (a + 1) a from rfl) b k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_d_f]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a + 1 = x1 + 1 ∧ b = x2) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h2
        have : x1 = a := by omega
        subst this
        rfl
      simp only [dH, this, if_false, Functor.map_zero]
      exact zero_comp
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

/- English proof (translation)
Rewrite using `[HomologicalComplex₂.ι_D₂]`. Break down `b with _ | b` into its components or cases. Rewrite using `[HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]`. Use `symm`. Use `Finset.sum_eq_zero (fun x _ => ?_)` and prove the remaining obligations.

Establish `hx : ¬ (a = x.1.1 ∧ 0 = x.1.2 + 1)` using `by omega`. Simplify using `only [dV, hx, if_false, Functor.map_zero]`. Conclude with `(congrArg _ zero_comp).trans (zsmul_zero _)`. Rewrite using `[HomologicalComplex₂.d₂_eq _ _ a (show (ComplexShape.down ℕ).Rel (b + 1) b from rfl) k (by simp only [ComplexShape.π_def]; omega)]`. Rewrite using `[Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]`.

Rewrite using `[dbl_X_d]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Introduce and unpack `⟨⟨x1, x2⟩, hx⟩ _ hne`. Establish `: ¬ (a = x1 ∧ b + 1 = x2 + 1)`.

Introduce and unpack `⟨h1, h2⟩`. Apply `hne` to reduce the goal to its premises. Substitute `h1` using the available equality. Establish `: x2 = b` using `by omega`. Substitute `this` using the available equality.

Both sides reduce to the same expression. Simplify using `only [dV, this, if_false, Functor.map_zero]`. Conclude with `(congrArg _ zero_comp).trans (zsmul_zero _)`. Introduce `hn`. Conclude with `absurd (Finset.mem_attach _ _) hn`.
-/
theorem ιTotal_D₂ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₂ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, ((-1 : ℤ) ^ a) • ((ev Y).map (dV a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)) := by
  rw [HomologicalComplex₂.ι_D₂]
  rcases b with _ | b
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (a = x.1.1 ∧ 0 = x.1.2 + 1) := by omega
    simp only [dV, hx, if_false, Functor.map_zero]
    exact (congrArg _ zero_comp).trans (zsmul_zero _)
  · rw [HomologicalComplex₂.d₂_eq _ _ a (show (ComplexShape.down ℕ).Rel (b + 1) b from rfl) k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_X_d]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a = x1 ∧ b + 1 = x2 + 1) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h1
        have : x2 = b := by omega
        subst this
        rfl
      simp only [dV, this, if_false, Functor.map_zero]
      exact (congrArg _ zero_comp).trans (zsmul_zero _)
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ ≫ ((dbl Y).total (ComplexShape.down ℕ)).d (k + 1) k = _`. Rewrite using `[HomologicalComplex₂.total_d, Preadditive.comp_add, ιTotal_D₁ Y a b k h, ιTotal_D₂ Y a b k h]`. Use `Eq.trans Finset.sum_add_distrib.symm (Finset.sum_congr rfl (fun x _ => ?_))` and prove the remaining obligations. Rewrite using `[dT, Functor.map_add, Functor.map_zsmul]`. Use `first`.

Consider the case `(rw [Preadditive.add_comp, Preadditive.zsmul_comp])`. Consider the case `(simp only [Preadditive.add_comp, Preadditive.zsmul_comp])`. Consider the case `(erw [Preadditive.add_comp, Preadditive.zsmul_comp])`. Both sides reduce to the same expression.
-/
theorem ιTotal_tot_d (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ)
    (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (tot Y).d (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  change _ ≫ ((dbl Y).total (ComplexShape.down ℕ)).d (k + 1) k = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, ιTotal_D₁ Y a b k h, ιTotal_D₂ Y a b k h]
  refine Eq.trans Finset.sum_add_distrib.symm (Finset.sum_congr rfl (fun x _ => ?_))
  rw [dT, Functor.map_add, Functor.map_zsmul]
  first
    | (rw [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (simp only [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (erw [Preadditive.add_comp, Preadditive.zsmul_comp])
  rfl

end

end GlobalTheory.EZ

/- English proof (translation)
The claim follows from `@GlobalTheory.EZ.ιTotal_tot_d`.
-/
example : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := @GlobalTheory.EZ.ιTotal_tot_d
