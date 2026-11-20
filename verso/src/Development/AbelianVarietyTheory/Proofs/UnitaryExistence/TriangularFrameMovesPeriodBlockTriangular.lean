import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerBor

/- English proof (translation)
Use `letI := Matrix.invertibleOfIsUnitDet h hu`. Establish `key : ∀ ι : α → ℤ, h⁻¹.BlockTriangular (fun j => toLex (ι (t j), w j))`. Introduce `ι`. Use `Matrix.blockTriangular_inv_of_blockTriangular ?_` and prove the remaining obligations. Introduce `j j' hlt`.

Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hs j j' hne`. Simplify using `only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hlt`. Use linear arithmetic over natural numbers and integers. Introduce `j j' hne`.

Establish `h1 : ¬ _` using `fun hlt => hne (key (fun a => (Fintype.equivFin α a : ℕ)) (i := j) (j := j') hlt)`. Establish `h2 : ¬ _` using `fun hlt => hne (key (fun a => -((Fintype.equivFin α a : ℕ) : ℤ)) (i := j) (j := j') hlt)`. Simplify using `only [Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at h1 h2`. Establish `h3 : ((Fintype.equivFin α (t j) : ℕ)) = (Fintype.equivFin α (t j') : ℕ)` using `by omega`. Establish `h4 : t j = t j'` using `(Fintype.equivFin α).injective (Fin.ext h3)`.

Conclude with `⟨h4, h1.2 (by rw [h4])⟩`.
-/
lemma inv_support {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    ∀ j j', h⁻¹ j j' ≠ 0 → t j = t j' ∧ w j ≤ w j' := by
  letI := Matrix.invertibleOfIsUnitDet h hu
  have key : ∀ ι : α → ℤ, h⁻¹.BlockTriangular (fun j => toLex (ι (t j), w j)) := by
    intro ι
    refine Matrix.blockTriangular_inv_of_blockTriangular ?_
    intro j j' hlt
    by_contra hne
    obtain ⟨h1, h2⟩ := hs j j' hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hlt
    omega
  intro j j' hne
  have h1 : ¬ _ := fun hlt => hne (key (fun a => (Fintype.equivFin α a : ℕ)) (i := j) (j := j') hlt)
  have h2 : ¬ _ := fun hlt => hne (key (fun a => -((Fintype.equivFin α a : ℕ) : ℤ)) (i := j) (j := j') hlt)
  simp only [Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at h1 h2
  have h3 : ((Fintype.equivFin α (t j) : ℕ)) = (Fintype.equivFin α (t j') : ℕ) := by omega
  have h4 : t j = t j' := (Fintype.equivFin α).injective (Fin.ext h3)
  exact ⟨h4, h1.2 (by rw [h4])⟩

/- English proof (translation)
Use `PerMove.det_of_triangular (fun j => toLex (Fintype.equivFin α (t j), w j)) ?_ _ fun k l hkl => ?_` and prove the remaining obligations. Introduce `k l hkl`. Establish `h'` using `toLex.injective hkl`. Rewrite `h'` using `[Prod.mk.injEq]`. Conclude with `hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2`.

Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hs k l hne`. Simplify using `only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl`. Use linear arithmetic over natural numbers and integers.
-/
lemma det_of_support {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  refine PerMove.det_of_triangular (fun j => toLex (Fintype.equivFin α (t j), w j)) ?_ _ fun k l hkl => ?_
  · intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  · by_contra hne
    obtain ⟨h1, h2⟩ := hs k l hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl
    omega

/- English proof (translation)
Establish `e` using `congrFun (congrFun (Matrix.nonsing_inv_mul h hu) a) a`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq]`. Conclude with `eq_inv_of_mul_eq_one_left e`. Introduce `c _ hc`. Assume the negation of the conclusion as `hne`.

Take `⟨h1, h2⟩` from `mul_ne_zero_iff.1 hne`. Take `⟨h3, h4⟩` from `inv_support t w h hu hs _ _ h1`. Take `⟨_, h6⟩` from `hs _ _ h2`. Conclude with `hc (hinj _ _ h3.symm (by omega))`. Simplify using the standard rewrite rules.
-/
lemma inv_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') (a : n) :
    h⁻¹ a a = (h a a)⁻¹ := by
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul h hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at e
  · exact eq_inv_of_mul_eq_one_left e
  · intro c _ hc
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨h3, h4⟩ := inv_support t w h hu hs _ _ h1
    obtain ⟨_, h6⟩ := hs _ _ h2
    exact hc (hinj _ _ h3.symm (by omega))
  · simp

noncomputable def moveMat {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    (b : Frame Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  open Classical in
  Matrix.of fun k l => if (idx l).1 = (idx k).1 then
      (if ((idx k).2 : ℕ) < q then FD.mat b (idx k).1 (idx l).2 (idx k).2
        else (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx l).2) else 0

section

variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    {b : Frame Ψ r}

/- English proof (translation)
Simplify using `only [moveMat, Matrix.of_apply, if_true]`. Use `split_ifs with hk`. Both sides reduce to the same expression. Conclude with `PerMove.bor_inv_diag hb _ _`.
-/
lemma moveMat_diag (hb : b ∈ Bor Ψ r) (k : Fin g) : moveMat q idx b k k =
    if ((idx k).2 : ℕ) < q then b (idx k).1 (idx k).2 (idx k).2 else (b (idx k).1 (idx k).2 (idx k).2)⁻¹ := by
  simp only [moveMat, Matrix.of_apply, if_true]
  split_ifs with hk
  · rfl
  · exact PerMove.bor_inv_diag hb _ _

/- English proof (translation)
Simplify using `only [moveMat, Matrix.of_apply] at h`. Distinguish the cases in `hτ : (idx l).1 = (idx k).1`. Rewrite `h` using `[if_pos hτ]`. Use `⟨hτ, ?_⟩` and prove the remaining obligations. Use `split_ifs at h ⊢ with hk`.

Assume the negation of the conclusion as `hlt`. Conclude with `h (PerMove.bor_tri hb _ (show (idx k).2 < (idx l).2 by rw [Fin.lt_def]; omega))`. Assume the negation of the conclusion as `hlt`. Conclude with `h (PerMove.bor_inv_tri hb _ (show (idx l).2 < (idx k).2 by rw [Fin.lt_def]; omega))`. Rewrite `h` using `[if_neg hτ]`.

Conclude with `absurd rfl h`.
-/
lemma moveMat_support (hb : b ∈ Bor Ψ r) (k l : Fin g) (h : moveMat q idx b k l ≠ 0) :
    (idx l).1 = (idx k).1 ∧ (if ((idx k).2 : ℕ) < q then ((idx l).2 : ℕ) ≤ (idx k).2
      else ((idx k).2 : ℕ) ≤ (idx l).2) := by
  simp only [moveMat, Matrix.of_apply] at h
  by_cases hτ : (idx l).1 = (idx k).1
  · rw [if_pos hτ] at h
    refine ⟨hτ, ?_⟩
    split_ifs at h ⊢ with hk
    · by_contra hlt
      exact h (PerMove.bor_tri hb _ (show (idx k).2 < (idx l).2 by rw [Fin.lt_def]; omega))
    · by_contra hlt
      exact h (PerMove.bor_inv_tri hb _ (show (idx l).2 < (idx k).2 by rw [Fin.lt_def]; omega))
  · rw [if_neg hτ] at h
    exact absurd rfl h

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `hm : FD.mat (FD.rmul x b) (idx k).1 = FD.mat x (idx k).1 * FD.mat b (idx k).1` using `rfl`. Rewrite using `[hP', hm]`. Simplify using `only [moveMat, Matrix.mulVec, dotProduct, Matrix.of_apply]`. Rewrite using `[← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (idx k).1]`.

Simplify using `only [Equiv.apply_symm_apply, if_true, hP] split_ifs with hk`. Rewrite using `[PerMove.hermC_col_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with hc`. Both sides reduce to the same expression.

Rewrite using `[PerMove.bor_tri hb (idx k).1 (show (idx k).2 < c by rw [Fin.lt_def]; omega), zero_mul, zero_mul]`. Express the relevant statement in the definitionally equal form `((FD.mat x (idx k).1 * FD.mat b (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2 = _`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with hc`.

Rewrite using `[PerMove.bor_inv_tri hb (idx k).1 (show c < (idx k).2 by rw [Fin.lt_def]; omega), zero_mul, zero_mul]`. Both sides reduce to the same expression. Introduce `τ _ hτ`. Simplify using `[hτ]`. Simplify using the standard rewrite rules.
-/
lemma moveMat_mulVec (hb : b ∈ Bor Ψ r) (Gm : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (v : Fin r → E)
    (P P' : Fin g → ℂ)
    (hP : ∀ k, P k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2)
    (hP' : ∀ k, P' k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat (rmul x b) (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat (rmul x b) (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2) :
    P' = moveMat q idx b *ᵥ P := by
  funext k
  have hm : FD.mat (FD.rmul x b) (idx k).1 = FD.mat x (idx k).1 * FD.mat b (idx k).1 := rfl
  rw [hP', hm]
  simp only [moveMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (idx k).1]
  · simp only [Equiv.apply_symm_apply, if_true, hP]
    split_ifs with hk
    · rw [PerMove.hermC_col_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rfl
      · rw [PerMove.bor_tri hb (idx k).1 (show (idx k).2 < c by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
    · change ((FD.mat x (idx k).1 * FD.mat b (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v)
        (idx k).2 = _
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rw [PerMove.bor_inv_tri hb (idx k).1 (show c < (idx k).2 by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
      · rfl
  · intro τ _ hτ
    simp [hτ]
  · simp

end

end GlobalTheory.PerBor

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx b hb`. Take `⟨⟨idx, hty, hcol, hper⟩, hp0, -⟩` from `GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k`. Take `⟨hbij, hrt, -, -⟩` from `GlobalTheory.Relab.relab_good E H l c σ hG`. Establish `hq : (F.Di k).q = Dw.q` using `hp0.symm.trans (hB.type k).1`. Establish `hlt : ∀ j, ((idx j).2 : ℕ) < (F.Di k).q → ((e j).2 : ℕ) < (F.Di k).q`.

Introduce `j hj`. Establish `h1` using `hty j`. Rewrite `h1` using `[if_pos hj]`. Establish `h2` using `((M.X k).cmType _).1 (idx j).1.2`. Rewrite `h2` using `[← h1, (hB.type k).2, hrt]`.

Establish `h3 : Dw.mult (e j).1 = Dw.q` using `if_neg h2`. Use `(e j).2.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j'`. Introduce `j j' h1 h2`.

Apply `e.injective` to reduce the goal to its premises. Use `Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)` and prove the remaining obligations. Establish `hs : ∀ j j', PerBor.moveMat (F.Di k).q idx b j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2`. Introduce `j j' hne`. Take `⟨h1, h2⟩` from `PerBor.moveMat_support _ idx hb j j' hne`.

Establish `c1` using `hcol j`. Establish `c2` using `hcol j'`. Establish `l1` using `hlt j`. Establish `l2` using `hlt j'`. Establish `t1` using `hty j`.

Establish `t2` using `hty j'`. Distinguish the cases in `hj : ((idx j).2 : ℕ) < (F.Di k).q`. Rewrite `h2`, `c1`, `t1` using `[if_pos hj]`. Establish `hj' : ((idx j').2 : ℕ) < (F.Di k).q` using `by omega`. Rewrite `c2`, `t2` using `[if_pos hj']`.

Use `⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩` and prove the remaining obligations. Use `l1 hj` as an intermediate fact. Use `l2 hj'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `h2`, `c1`, `t1` using `[if_neg hj]`.

Establish `hj' : ¬ ((idx j').2 : ℕ) < (F.Di k).q` using `by omega`. Rewrite `c2`, `t2` using `[if_neg hj']`. Use `⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Establish `hdet` using `PerBor.det_of_support _ _ hinj _ hs`.

Establish `hdiag` using `PerBor.moveMat_diag (F.Di k).q idx hb`. Establish `hbne : ∀ τ i, b τ i i ≠ 0` using `fun τ i => PerMove.bor_diag_ne hb τ i`. Establish `hu : IsUnit (PerBor.moveMat (F.Di k).q idx b).det`. Rewrite using `[hdet, isUnit_iff_ne_zero]`. Use `Finset.prod_ne_zero_iff.2 fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hdiag]`. Use `split_ifs`. Conclude with `hbne _ _`. Conclude with `inv_ne_zero (hbne _ _)`. Use `⟨PerBor.moveMat (F.Di k).q idx b, hu, fun a => ?_, PerBor.inv_support _ _ _ hu hs, by rw [hdet, norm_prod], fun h1 => ?_, fun un a n t₀ hn ht => ?_⟩` and prove the remaining obligations.

Conclude with `PerBor.moveMat_mulVec _ idx hb (M.X k).Gm x (M.φ k a : Fin r → E) _ _ (fun j => by rw [hPf, hper]) (fun j => by rw [hPf, hper])`. Rewrite using `[hdet, norm_prod]`. Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hdiag]`. Use `split_ifs`.

Conclude with `h1 _ _`. Rewrite using `[norm_inv, h1, inv_one]`. Take `⟨m, rfl⟩` from `hn`. Establish `ht2 : t₀ ^ 2 = ∏ j, (PerBor.moveMat (F.Di k).q idx b j j)⁻¹`. Rewrite using `[Finset.prod_inv_distrib, ← hdet]`.

Conclude with `eq_inv_of_mul_eq_one_left ht`. Rewrite using `[← two_mul, pow_mul, ht2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Unfold `bchar`. Use `Eq.trans ?_ (Fintype.prod_prod_type' (fun (τ : (M.X k).Ψ) (i : Fin r) => b τ i i ^ laU (unfOf e F M un) a (2 * m) k τ i))` and prove the remaining obligations. Rewrite using `[← idx.prod_comp]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[PerBor.inv_diag _ _ hinj _ hu hs, ← pow_add, hdiag]`. Establish `hm' : 2 * m / 2 = m` using `by omega`. Establish `hp : ((unfOf e F M un).X k).p0 = (F.Di k).q` using `hp0`. Establish `c1` using `hcol j`.

Establish `t1` using `hty j`. Establish `hinv` using `Function.leftInverse_invFun hbij.1 (e j).1`. Unfold `laU`. Rewrite using `[hp, hm']`. Distinguish the cases in `hj : ((idx j).2 : ℕ) < (F.Di k).q`.

Rewrite `c1`, `t1` using `[if_pos hj]`. Use `hlt j hj` as an intermediate fact. Establish `t2 : conjEmb (idx j).1.1 = relab c σ (e j).1` using `t1.symm`. Rewrite using `[if_pos hj, if_neg (by omega), t2, hinv, show (F.Di k).q - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `c1`, `t1` using `[if_neg hj]`. Rewrite using `[if_neg hj, if_pos (by omega), ← t1, hinv, show ((idx j).2 : ℕ) - (F.Di k).q = (e j).2 by omega, inv_inv, ← zpow_natCast]`. Use `congr 1`.
-/
theorem GlobalTheory.per_bor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ a, Pf (rmul x b) a = h₀ *ᵥ Pf x a) ∧ (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ ‖h₀.det‖ = ∏ j, ‖h₀ j j‖ ∧ ((∀ τ i, ‖b τ i i‖ = 1) → ‖h₀.det‖ = 1) ∧ ∀ (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : ℂ), Even n → t₀ ^ 2 * h₀.det = 1 → (∏ j, h₀⁻¹ j j ^ a ((e j).1, (e j).2)) * t₀ ^ n = bchar (laU (unfOf e F M un) a n k) b := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx b hb
  obtain ⟨⟨idx, hty, hcol, hper⟩, hp0, -⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  have hq : (F.Di k).q = Dw.q := hp0.symm.trans (hB.type k).1
  have hlt : ∀ j, ((idx j).2 : ℕ) < (F.Di k).q → ((e j).2 : ℕ) < (F.Di k).q := by
    intro j hj
    have h1 := hty j
    rw [if_pos hj] at h1
    have h2 := ((M.X k).cmType _).1 (idx j).1.2
    rw [← h1, (hB.type k).2, hrt] at h2
    have h3 : Dw.mult (e j).1 = Dw.q := if_neg h2
    have := (e j).2.isLt
    omega
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (F.Di k).q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have c1 := hcol j
    have c2 := hcol j'
    have l1 := hlt j
    have l2 := hlt j'
    have t1 := hty j
    have t2 := hty j'
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at h2 c1 t1
      have hj' : ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_pos hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      have := l1 hj
      have := l2 hj'
      omega
    · rw [if_neg hj] at h2 c1 t1
      have hj' : ¬ ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_neg hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      omega
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (F.Di k).q idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (F.Di k).q idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (F.Di k).q idx b, hu, fun a => ?_, PerBor.inv_support _ _ _ hu hs,
    by rw [hdet, norm_prod], fun h1 => ?_, fun un a n t₀ hn ht => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (M.X k).Gm x (M.φ k a : Fin r → E) _ _
      (fun j => by rw [hPf, hper]) (fun j => by rw [hPf, hper])
  · rw [hdet, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact h1 _ _
    · rw [norm_inv, h1, inv_one]
  · obtain ⟨m, rfl⟩ := hn
    have ht2 : t₀ ^ 2 = ∏ j, (PerBor.moveMat (F.Di k).q idx b j j)⁻¹ := by
      rw [Finset.prod_inv_distrib, ← hdet]
      exact eq_inv_of_mul_eq_one_left ht
    rw [← two_mul, pow_mul, ht2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (M.X k).Ψ) (i : Fin r) => b τ i i ^ laU (unfOf e F M un) a (2 * m) k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, ← pow_add, hdiag]
    have hm' : 2 * m / 2 = m := by omega
    have hp : ((unfOf e F M un).X k).p0 = (F.Di k).q := hp0
    have c1 := hcol j
    have t1 := hty j
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rw [hp, hm']
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at c1 t1
      have := hlt j hj
      have t2 : conjEmb (idx j).1.1 = relab c σ (e j).1 := t1.symm
      rw [if_pos hj, if_neg (by omega), t2, hinv,
        show (F.Di k).q - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    · rw [if_neg hj] at c1 t1
      rw [if_neg hj, if_pos (by omega), ← t1, hinv,
        show ((idx j).2 : ℕ) - (F.Di k).q = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
