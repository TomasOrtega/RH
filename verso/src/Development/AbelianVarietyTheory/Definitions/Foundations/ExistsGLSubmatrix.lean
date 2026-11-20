import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct

noncomputable section

namespace GlobalTheory.Doubling

open NumberField Matrix Formalism.BasicNotions Formalism.UG GlobalTheory.AdelicU

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`.
-/
theorem mem_hdual {S K V : Type} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] {B : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule S V} {x : V} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule S K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

variable {E : Type} [Field E] [NumberField E] [StarRing E]

@[reducible] def hneg (V : HSpace E) : HSpace E where
  V := V.V
  hT := -V.hT
  herm := ⟨fun x y => by simp [V.herm.eq x y]⟩
  nondeg := ⟨fun x h => V.nondeg.1 x fun y => neg_eq_zero.1 (h y), fun x h => V.nondeg.2 x fun y => neg_eq_zero.1 (h y)⟩
  rank := V.rank
  rank_eq := V.rank_eq
  frame := V.frame
  sig τ := ((V.sig τ).2, (V.sig τ).1)
  L0 := V.L0
  standardTuple_isLattice := V.standardTuple_isLattice
  baseLattice_isUnimodular := by
    refine Eq.trans (Submodule.ext fun x => ?_) V.baseLattice_isUnimodular
    simp only [mem_hdual, LinearMap.neg_apply, neg_mem_iff]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orthSum_apply (V W : HSpace E) (x y : V.V × W.V) :
    Formalism.E.orthSum V.hT W.hT x y = V.hT x.1 y.1 + W.hT x.2 y.2 := rfl

@[reducible] def hsum (V W : HSpace E) : HSpace E where
  V := V.V × W.V
  hT := Formalism.E.orthSum V.hT W.hT
  herm := ⟨fun x y => by rw [orthSum_apply, orthSum_apply, map_add, V.herm.eq, W.herm.eq]⟩
  nondeg := ⟨fun x h => Prod.ext (V.nondeg.1 _ fun y => by simpa [orthSum_apply] using h (y, 0))
      (W.nondeg.1 _ fun y => by simpa [orthSum_apply] using h (0, y)),
    fun x h => Prod.ext (V.nondeg.2 _ fun y => by simpa [orthSum_apply] using h (y, 0))
      (W.nondeg.2 _ fun y => by simpa [orthSum_apply] using h (0, y))⟩
  rank := V.rank + W.rank
  rank_eq := by rw [Module.finrank_prod, V.rank_eq, W.rank_eq]
  frame := (V.frame.prod W.frame).reindex finSumFinEquiv
  sig τ := V.sig τ + W.sig τ
  L0 := V.L0.prod W.L0
  standardTuple_isLattice := ⟨V.standardTuple_isLattice.fg.prod W.standardTuple_isLattice.fg, by
    rw [Submodule.prod_coe, Submodule.span_prod_eq E (zero_mem V.L0) (zero_mem W.L0), V.standardTuple_isLattice.span_eq_top,
      W.standardTuple_isLattice.span_eq_top, Submodule.prod_top]⟩
  baseLattice_isUnimodular := Submodule.ext fun x => by
    have h1 := SetLike.ext_iff.1 V.baseLattice_isUnimodular x.1
    have h2 := SetLike.ext_iff.1 W.baseLattice_isUnimodular x.2
    rw [Submodule.mem_prod, ← h1, ← h2, mem_hdual, mem_hdual, mem_hdual]
    exact ⟨fun h => ⟨fun y hy => by simpa [orthSum_apply] using h (y, 0) ⟨hy, zero_mem _⟩,
      fun y hy => by simpa [orthSum_apply] using h (0, y) ⟨zero_mem _, hy⟩⟩,
      fun h y hy => add_mem (h.1 _ hy.1) (h.2 _ hy.2)⟩

@[reducible] def hdbl (V : HSpace E) : HSpace E := hsum V (hneg V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gram_hneg (V : HSpace E) : (hneg V).gram = -V.gram := rfl

/- English proof (translation)
Simplify using `[Module.Basis.prod_apply]`.
-/
theorem frame_hsum_inl (V W : HSpace E) (i : Fin V.rank) :
    (hsum V W).frame (finSumFinEquiv (.inl i)) = (V.frame i, 0) := by
  simp [Module.Basis.prod_apply]

/- English proof (translation)
Simplify using `[Module.Basis.prod_apply]`.
-/
theorem frame_hsum_inr (V W : HSpace E) (i : Fin W.rank) :
    (hsum V W).frame (finSumFinEquiv (.inr i)) = (0, W.frame i) := by
  simp [Module.Basis.prod_apply]

/- English proof (translation)
Use extensionality with `i j`. Take `⟨a, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨b, rfl⟩` from `finSumFinEquiv.surjective j`. Establish `key : ∀ u v, (hsum V W).hT u v = V.hT u.1 v.1 + W.hT u.2 v.2` using `fun u v => orthSum_apply V W u v`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`.

Simplify using `[HSpace.gram, blkMat, key, frame_hsum_inl, frame_hsum_inr]`.
-/
theorem gram_hsum (V W : HSpace E) : (hsum V W).gram = blkMat finSumFinEquiv V.gram W.gram := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  have key : ∀ u v, (hsum V W).hT u v = V.hT u.1 v.1 + W.hT u.2 v.2 := fun u v => orthSum_apply V W u v
  rcases a with a | a <;> rcases b with b | b <;>
    simp [HSpace.gram, blkMat, key, frame_hsum_inl, frame_hsum_inr]

/- English proof (translation)
Use `show (hsum V (hneg V)).gram = _`. Rewrite using `[gram_hsum, gram_hneg]`. Both sides reduce to the same expression.
-/
theorem gram_hdbl (V : HSpace E) : (hdbl V).gram = dblGram finSumFinEquiv V.gram := by
  show (hsum V (hneg V)).gram = _
  rw [gram_hsum, gram_hneg]
  rfl

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]`. Simplify using `only [pairVec_inl, pairVec_inr, frame_hsum_inl, frame_hsum_inr, Prod.smul_mk, smul_zero]`. Apply the tactic sequence `ext <;> simp [Prod.fst_sum, Prod.snd_sum]`.
-/
theorem sum_pairVec_frame (V W : HSpace E) (x : Fin V.rank → E) (y : Fin W.rank → E) :
    ∑ i, pairVec finSumFinEquiv x y i • (hsum V W).frame i = (∑ i, x i • V.frame i, ∑ i, y i • W.frame i) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [pairVec_inl, pairVec_inr, frame_hsum_inl, frame_hsum_inr, Prod.smul_mk, smul_zero]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[mem_sumLat, mem_frameLat, mem_frameLat, mem_frameLat]`. Use `conv_lhs => rw [← pairVec_eta finSumFinEquiv w]`. Rewrite using `[sum_pairVec_frame]`. Conclude with `Submodule.mem_prod`.
-/
theorem frameLat_hsum (V W : HSpace E) : frameLat (hsum V W) = sumLat finSumFinEquiv (frameLat V) (frameLat W) := by
  ext w
  rw [mem_sumLat, mem_frameLat, mem_frameLat, mem_frameLat]
  conv_lhs => rw [← pairVec_eta finSumFinEquiv w]
  rw [sum_pairVec_frame]
  exact Submodule.mem_prod

/- English proof (translation)
Use `⟨frameLat_fg V, ?_⟩` and prove the remaining obligations. Establish `key : ((frameLat V : Submodule (𝓞 E) (Fin V.rank → E)) : Set (Fin V.rank → E)) = (V.frame.equivFun.toLinearMap : V.V →ₗ[E] (Fin V.rank → E)) '' (V.L0 : Set V.V)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨V.frame.equivFun.symm x, hx, V.frame.equivFun.apply_symm_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩ show V.frame.equivFun.symm (V.frame.equivFun y) ∈ V.L0`. Simplify using `using hy`. Rewrite using `[key, Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
theorem isLattice_frameLat (V : HSpace E) : Submodule.IsLattice E (frameLat V) := by
  refine ⟨frameLat_fg V, ?_⟩
  have key : ((frameLat V : Submodule (𝓞 E) (Fin V.rank → E)) : Set (Fin V.rank → E)) =
      (V.frame.equivFun.toLinearMap : V.V →ₗ[E] (Fin V.rank → E)) '' (V.L0 : Set V.V) := by
    ext x
    constructor
    · intro hx
      exact ⟨V.frame.equivFun.symm x, hx, V.frame.equivFun.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      show V.frame.equivFun.symm (V.frame.equivFun y) ∈ V.L0
      simpa using hy
  rw [key, Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Introduce `x y`. Use `show Formalism.E.orthSum V.hT W.hT _ _ = _`. Rewrite using `[orthSum_apply]`. Simplify using the standard rewrite rules.
-/
theorem isIsomEmb_inl (V W : HSpace E) : HSpace.IsIsomEmb V (hsum V W) (LinearMap.inl E V.V W.V) := by
  intro x y
  show Formalism.E.orthSum V.hT W.hT _ _ = _
  rw [orthSum_apply]
  simp

/- English proof (translation)
Introduce `x y`. Use `show Formalism.E.orthSum V.hT W.hT _ _ = _`. Rewrite using `[orthSum_apply]`. Simplify using the standard rewrite rules.
-/
theorem isIsomEmb_inr (V W : HSpace E) : HSpace.IsIsomEmb W (hsum V W) (LinearMap.inr E V.V W.V) := by
  intro x y
  show Formalism.E.orthSum V.hT W.hT _ _ = _
  rw [orthSum_apply]
  simp

/- English proof (translation)
Use `⟨⟨P.1.submatrix e e, (P⁻¹).1.submatrix e e, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Matrix.submatrix_mul_equiv, P.mul_inv, Matrix.submatrix_one_equiv]`. Rewrite using `[Matrix.submatrix_mul_equiv, P.inv_mul, Matrix.submatrix_one_equiv]`.
-/
theorem exists_GL_submatrix {A m n : Type} [CommRing A] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : GL m A) (e : n ≃ m) : ∃ P' : GL n A, P'.1 = P.1.submatrix e e := by
  refine ⟨⟨P.1.submatrix e e, (P⁻¹).1.submatrix e e, ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv, P.mul_inv, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, P.inv_mul, Matrix.submatrix_one_equiv]

/- English proof (translation)
Establish `hc : cT σ (P.submatrix e e) = (cT σ P).submatrix e e`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[hc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`.
-/
private lemma cT_submatrix_mul_mul {m n : Type} [Fintype m] [Fintype n] (σ : ℂ →+* ℂ) (e : n ≃ m)
    (P J Q : Matrix m m ℂ) :
    cT σ (P.submatrix e e) * J.submatrix e e * Q.submatrix e e = (cT σ P * J * Q).submatrix e e := by
  have hc : cT σ (P.submatrix e e) = (cT σ P).submatrix e e := by
    ext i j
    rfl
  rw [hc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Unfold `Formalism.UG.HasSignature`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, P, h⟩`. Take `⟨P', hP'⟩` from `exists_GL_submatrix P e`. Use `⟨e.symm, P', ?_⟩` and prove the remaining obligations.

Establish `hJ : J = ((reindex e e) J).submatrix e e`. Use extensionality with `i j`. Simplify using `[Matrix.reindex_apply]`. Rewrite using `[hP', hJ, cT_submatrix_mul_mul, h]`. Use extensionality with `i j`.

Simplify using `[blkMat, Formalism.UG.Jpq]`. Introduce and unpack `⟨e, P, h⟩`. Take `⟨P', hP'⟩` from `exists_GL_submatrix P e`. Use `⟨e.symm, P', ?_⟩` and prove the remaining obligations. Rewrite using `[hP', Matrix.reindex_apply, Equiv.symm_symm, cT_submatrix_mul_mul, h]`.

Use extensionality with `i j`. Simplify using `[blkMat, Formalism.UG.Jpq]`.
-/
theorem hasSignature_iff {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ} : HasSignature J p q ↔
    ∃ (e : Fin p ⊕ Fin q ≃ n) (P : GL n ℂ), cT (starRingEnd ℂ) P.1 * J * P.1 = blkMat e 1 (-1) := by
  unfold Formalism.UG.HasSignature
  constructor
  · rintro ⟨e, P, h⟩
    obtain ⟨P', hP'⟩ := exists_GL_submatrix P e
    refine ⟨e.symm, P', ?_⟩
    have hJ : J = ((reindex e e) J).submatrix e e := by
      ext i j
      simp [Matrix.reindex_apply]
    rw [hP', hJ, cT_submatrix_mul_mul, h]
    ext i j
    simp [blkMat, Formalism.UG.Jpq]
  · rintro ⟨e, P, h⟩
    obtain ⟨P', hP'⟩ := exists_GL_submatrix P e
    refine ⟨e.symm, P', ?_⟩
    rw [hP', Matrix.reindex_apply, Equiv.symm_symm, cT_submatrix_mul_mul, h]
    ext i j
    simp [blkMat, Formalism.UG.Jpq]

/- English proof (translation)
Unfold `blkMat`. Rewrite using `[Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]`. Both sides reduce to the same expression.
-/
private lemma blkMat_diagonal_eq_diagonal {m n ι : Type} [DecidableEq m] [DecidableEq n] [DecidableEq ι] (e : m ⊕ n ≃ ι)
    (d₁ : m → ℂ) (d₂ : n → ℂ) :
    blkMat e (Matrix.diagonal d₁) (Matrix.diagonal d₂) = Matrix.diagonal (fun i => Sum.elim d₁ d₂ (e.symm i)) := by
  unfold blkMat
  rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

/- English proof (translation)
Establish `h1 : (1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => 1)` using `Matrix.diagonal_one.symm`. Establish `h2 : (-1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => -1)`. Rewrite using `[← Matrix.diagonal_one, Matrix.diagonal_neg]`. Rewrite using `[h1, h2]`. Conclude with `blkMat_diagonal_eq_diagonal e _ _`.
-/
private lemma blkMat_one_neg_one_eq_diagonal {m n ι : Type} [DecidableEq m] [DecidableEq n] [DecidableEq ι] (e : m ⊕ n ≃ ι) :
    blkMat e (1 : Matrix m m ℂ) (-1) = Matrix.diagonal (fun i => Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (e.symm i)) := by
  have h1 : (1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
  have h2 : (-1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => -1) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_neg]
  rw [h1, h2]
  exact blkMat_diagonal_eq_diagonal e _ _

/- English proof (translation)
Introduce `τ`. Take `⟨e, P, hP⟩` from `hasSignature_iff.1 (h τ)`. Use `hasSignature_iff.2 ⟨(Equiv.sumComm _ _).trans e, P, ?_⟩` and prove the remaining obligations. Establish `hg : (hneg V).gram.map τ = -(V.gram.map τ)`. Rewrite using `[gram_hneg]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hg, Matrix.mul_neg, Matrix.neg_mul, hP, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal, Matrix.diagonal_neg]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `rcases hi : e.symm i with a | a <;> simp [hi]`.
-/
theorem sigOK_hneg {V : HSpace E} (h : V.SigOK) : (hneg V).SigOK := by
  intro τ
  obtain ⟨e, P, hP⟩ := hasSignature_iff.1 (h τ)
  refine hasSignature_iff.2 ⟨(Equiv.sumComm _ _).trans e, P, ?_⟩
  have hg : (hneg V).gram.map τ = -(V.gram.map τ) := by
    rw [gram_hneg]
    ext i j
    simp
  rw [hg, Matrix.mul_neg, Matrix.neg_mul, hP, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext i
  rcases hi : e.symm i with a | a <;> simp [hi]

/- English proof (translation)
Introduce `τ`. Take `⟨e1, P1, h1⟩` from `hasSignature_iff.1 (h τ)`. Take `⟨e2, P2, h2⟩` from `hasSignature_iff.1 (h' τ)`. Establish `hg : (hsum V W).gram.map τ = blkMat finSumFinEquiv (V.gram.map τ) (W.gram.map τ)`. Rewrite using `[gram_hsum, blkMat_map _ _ (map_zero τ)]`.

Use `hasSignature_iff.2 ⟨((Equiv.sumCongr (finSumFinEquiv (m := (V.sig τ).1) (n := (W.sig τ).1)).symm (finSumFinEquiv (m := (V.sig τ).2) (n := (W.sig τ).2)).symm).trans ((Equiv.sumSumSumComm _ _ _ _).trans ((Equiv.sumCongr e1 e2).trans finSumFinEquiv))), blkGL finSumFinEquiv (P1, P2), …` and prove the remaining obligations. Rewrite using `[hg, val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, h1, h2, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal, blkMat_diagonal_eq_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Take `⟨s, rfl⟩` from `finSumFinEquiv.surjective i`.

Break down `s with k | k` into its components or cases. Apply the tactic sequence `rcases hk : e1.symm k with a | a <;> simp [hk]`. Apply the tactic sequence `rcases hk : e2.symm k with a | a <;> simp [hk]`.
-/
theorem sigOK_hsum {V W : HSpace E} (h : V.SigOK) (h' : W.SigOK) : (hsum V W).SigOK := by
  intro τ
  obtain ⟨e1, P1, h1⟩ := hasSignature_iff.1 (h τ)
  obtain ⟨e2, P2, h2⟩ := hasSignature_iff.1 (h' τ)
  have hg : (hsum V W).gram.map τ = blkMat finSumFinEquiv (V.gram.map τ) (W.gram.map τ) := by
    rw [gram_hsum, blkMat_map _ _ (map_zero τ)]
  refine hasSignature_iff.2
    ⟨((Equiv.sumCongr (finSumFinEquiv (m := (V.sig τ).1) (n := (W.sig τ).1)).symm
        (finSumFinEquiv (m := (V.sig τ).2) (n := (W.sig τ).2)).symm).trans
      ((Equiv.sumSumSumComm _ _ _ _).trans ((Equiv.sumCongr e1 e2).trans finSumFinEquiv))),
      blkGL finSumFinEquiv (P1, P2), ?_⟩
  rw [hg, val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, h1, h2, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal,
    blkMat_one_neg_one_eq_diagonal, blkMat_diagonal_eq_diagonal]
  congr 1
  funext i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  rcases s with k | k
  · rcases hk : e1.symm k with a | a <;> simp [hk]
  · rcases hk : e2.symm k with a | a <;> simp [hk]

/- English proof (translation)
The claim follows from `sigOK_hsum h (sigOK_hneg h)`.
-/
theorem sigOK_hdbl {V : HSpace E} (h : V.SigOK) : (hdbl V).SigOK := sigOK_hsum h (sigOK_hneg h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, rfl⟩`.
-/
example (V : HSpace E) (τ : E →+* ℂ) : (hdbl V).rank = V.rank + V.rank ∧
    (hdbl V).sig τ = ((V.sig τ).1 + (V.sig τ).2, (V.sig τ).2 + (V.sig τ).1) := ⟨rfl, rfl⟩

/- English proof (translation)
The claim follows from `(sub_eq_add_neg _ _).symm`.
-/
example (V : HSpace E) (x y x' y' : V.V) : (hdbl V).hD (x, y) (x', y') = V.hD x x' - V.hD y y' :=
  (sub_eq_add_neg _ _).symm

end GlobalTheory.Doubling

end
