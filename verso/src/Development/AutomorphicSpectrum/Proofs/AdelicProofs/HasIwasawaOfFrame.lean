import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

namespace GlobalTheory.CompanionTheory.IwaDbl.FrameCore

section Generic

open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc

variable {S : Type} [CommRing S]

/- English proof (translation)
Establish `h : (diagCols β : Matrix (β ⊕ β) β S).map c = diagCols β`. Apply the tactic sequence `ext (i | i) j <;> simp [diagCols, Matrix.one_apply, apply_ite c]`. Rewrite using `[h]`. Simplify using `[diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]`.
-/
theorem diagCols_isotropic (c : S →ₐ[ℤ] S) {β : Type} [Fintype β] [DecidableEq β] (H : Matrix β β S) :
    (diagCols β : Matrix (β ⊕ β) β S)ᵀ * dbl H * (diagCols β : Matrix (β ⊕ β) β S).map c = 0 := by
  have h : (diagCols β : Matrix (β ⊕ β) β S).map c = diagCols β := by
    ext (i | i) j <;> simp [diagCols, Matrix.one_apply, apply_ite c]
  rw [h]
  simp [diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

/- English proof (translation)
Establish `hd : dbl J₀ᵀ = ((dblGram finSumFinEquiv J₀)ᵀ).submatrix finSumFinEquiv finSumFinEquiv`. Rewrite using `[← Matrix.transpose_submatrix, dblGram, submatrix_blkMat, dbl, Matrix.fromBlocks_transpose]`. Simplify using the standard rewrite rules. Establish `hL : (x.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * ((dblGram finSumFinEquiv J₀)ᵀ).submatrix finSumFinEquiv finSumFinEquiv * (x.submatrix finSumFinEquiv finSumFinEquiv).map c = ((cT c x * dblGram finSumFinEquiv J₀ * x)ᵀ).submatrix finSumFinEquiv finSumFinEquiv`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, cT, Matrix.transpose_transpose, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]`.

Rewrite using `[hd, hL]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Introduce `h`.

Use `congrArg (fun X => (X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᵀ) h` as an intermediate fact. Simplify using `using this`.
-/
theorem iso_iff {n : ℕ} (c : S →+* S) (J₀ : Matrix (Fin n) (Fin n) S) (x : Matrix (Fin (n + n)) (Fin (n + n)) S) :
    cT c x * dblGram finSumFinEquiv J₀ * x = dblGram finSumFinEquiv J₀ ↔
      (x.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * dbl J₀ᵀ * (x.submatrix finSumFinEquiv finSumFinEquiv).map c =
        dbl J₀ᵀ := by
  have hd : dbl J₀ᵀ = ((dblGram finSumFinEquiv J₀)ᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
    rw [← Matrix.transpose_submatrix, dblGram, submatrix_blkMat, dbl, Matrix.fromBlocks_transpose]
    simp
  have hL : (x.submatrix finSumFinEquiv finSumFinEquiv)ᵀ *
      ((dblGram finSumFinEquiv J₀)ᵀ).submatrix finSumFinEquiv finSumFinEquiv *
      (x.submatrix finSumFinEquiv finSumFinEquiv).map c =
      ((cT c x * dblGram finSumFinEquiv J₀ * x)ᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, cT, Matrix.transpose_transpose, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
  rw [hd, hL]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (fun X => (X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᵀ) h
    simpa using this

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[← cT_mul, Units.mul_inv]`. Simplify using `[cT, Matrix.map_one _ (map_zero c) (map_one c)]`.
-/
theorem cT_unit_mul (c : S →+* S) (B : GL ι S) : cT c (B⁻¹).1 * cT c B.1 = 1 := by
  rw [← cT_mul, Units.mul_inv]
  simp [cT, Matrix.map_one _ (map_zero c) (map_one c)]

/- English proof (translation)
Substitute `hB` using the available equality. Simplify using `only [Units.val_mul, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [cT_unit_mul, Units.mul_inv, Matrix.mul_one, Matrix.mul_one, hX]`.
-/
theorem conj_iso (c : S →+* S) {Q' Q₀ : Matrix ι ι S} (B : GL ι S) (hB : cT c B.1 * Q' * B.1 = Q₀) {X : GL ι S}
    (hX : cT c X.1 * Q' * X.1 = Q') : cT c (B⁻¹ * X * B).1 * Q₀ * (B⁻¹ * X * B).1 = Q₀ := by
  subst hB
  simp only [Units.val_mul, cT_mul]
  calc _ = cT c B.1 * (cT c X.1 * (cT c (B⁻¹).1 * cT c B.1) * Q' * (B.1 * (B⁻¹).1) * X.1) * B.1 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [cT_unit_mul, Units.mul_inv, Matrix.mul_one, Matrix.mul_one, hX]

/- English proof (translation)
Substitute `hB` using the available equality. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_back (c : S →+* S) {Q' Q₀ : Matrix ι ι S} (B : GL ι S) (hB : cT c B.1 * Q' * B.1 = Q₀) :
    cT c (B⁻¹).1 * Q₀ * (B⁻¹).1 = Q' := by
  subst hB
  calc _ = (cT c (B⁻¹).1 * cT c B.1) * Q' * (B.1 * (B⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = Q' := by rw [cT_unit_mul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

def reGL {α : Type} [Fintype α] [DecidableEq α] (e : α ≃ ι) (u : GL α S) : GL ι S :=
  ⟨u.1.submatrix e.symm e.symm, (u⁻¹).1.submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `[pairVec, diagCols, Matrix.fromRows_mulVec]`.
-/
theorem mulVec_diagCols {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) S) (u : Fin n → S) :
    (M.submatrix finSumFinEquiv finSumFinEquiv * diagCols (E := S) (Fin n)) *ᵥ u =
      (M *ᵥ pairVec finSumFinEquiv u u) ∘ finSumFinEquiv := by
  rw [← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
  congr 2
  funext j
  simp [pairVec, diagCols, Matrix.fromRows_mulVec]

/- English proof (translation)
Use `set B := blkGL finSumFinEquiv (b, b) with hBdef`. Use `set x := B⁻¹ * G⁻¹ * B with hx`. Establish `hB : G * B * x = B` using `by rw [hx]; group`. Use `keepsDiag_of_mulVec fun w hw => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `(mem_diagSub finSumFinEquiv).1 hw`.

Take `⟨u, hu⟩ : ∃ u, u = (b⁻¹).1 *ᵥ z` from `⟨_, rfl⟩`. Establish `e1 : (B⁻¹).1 *ᵥ pairVec finSumFinEquiv z z = pairVec finSumFinEquiv u u`. Establish `: B⁻¹ = blkGL finSumFinEquiv (b⁻¹, b⁻¹)` using `by rw [hBdef, ← map_inv, Prod.inv_mk]`. Rewrite using `[this, val_blkGL, hu]`. Conclude with `blkMat_mulVec _ _ _ _ _`.

Establish `e2 : Y.1 *ᵥ pairVec finSumFinEquiv u u = x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)`. Establish `h : (Y.1 *ᵥ pairVec finSumFinEquiv u u) ∘ finSumFinEquiv = (x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)) ∘ finSumFinEquiv`. Rewrite using `[← mulVec_diagCols, ← mulVec_diagCols, hY, Matrix.mulVec_mulVec]`. Conclude with `finSumFinEquiv.surjective.injective_comp_right h`. Establish `e3 : (G * (B * Y * B⁻¹)).1 *ᵥ pairVec finSumFinEquiv z z = pairVec finSumFinEquiv (b.1 *ᵥ t *ᵥ u) (b.1 *ᵥ t *ᵥ u)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Use `_ = (G * B).1 *ᵥ (x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)) := by rw [e1, e2]`. Use `_ = (G * B * x).1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by`. Simplify using `only [Units.val_mul, Matrix.mulVec_mulVec]`.

Use `_ = B.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by rw [hB]`. Use `_ = _ := by rw [hBdef, val_blkGL]; exact blkMat_mulVec _ _ _ _ _`. Rewrite using `[e3]`. Conclude with `(mem_diagSub finSumFinEquiv).2 ⟨_, rfl⟩`.
-/
theorem keepsDiag_of_frame {n : ℕ} (G : GL (Fin (n + n)) S) (b : GL (Fin n) S) (Y : GL (Fin (n + n)) S)
    (t : Matrix (Fin n) (Fin n) S)
    (hY : Y.1.submatrix finSumFinEquiv finSumFinEquiv * diagCols (E := S) (Fin n) =
      ((blkGL finSumFinEquiv (b, b))⁻¹ * G⁻¹ * blkGL finSumFinEquiv (b, b)).1.submatrix finSumFinEquiv finSumFinEquiv *
        diagCols (E := S) (Fin n) * t) :
    KeepsDiag finSumFinEquiv (G * (blkGL finSumFinEquiv (b, b) * Y * (blkGL finSumFinEquiv (b, b))⁻¹)).1 := by
  set B := blkGL finSumFinEquiv (b, b) with hBdef
  set x := B⁻¹ * G⁻¹ * B with hx
  have hB : G * B * x = B := by rw [hx]; group
  refine keepsDiag_of_mulVec fun w hw => ?_
  obtain ⟨z, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
  obtain ⟨u, hu⟩ : ∃ u, u = (b⁻¹).1 *ᵥ z := ⟨_, rfl⟩
  have e1 : (B⁻¹).1 *ᵥ pairVec finSumFinEquiv z z = pairVec finSumFinEquiv u u := by
    have : B⁻¹ = blkGL finSumFinEquiv (b⁻¹, b⁻¹) := by rw [hBdef, ← map_inv, Prod.inv_mk]
    rw [this, val_blkGL, hu]
    exact blkMat_mulVec _ _ _ _ _
  have e2 : Y.1 *ᵥ pairVec finSumFinEquiv u u = x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by
    have h : (Y.1 *ᵥ pairVec finSumFinEquiv u u) ∘ finSumFinEquiv =
        (x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)) ∘ finSumFinEquiv := by
      rw [← mulVec_diagCols, ← mulVec_diagCols, hY, Matrix.mulVec_mulVec]
    exact finSumFinEquiv.surjective.injective_comp_right h
  have e3 : (G * (B * Y * B⁻¹)).1 *ᵥ pairVec finSumFinEquiv z z =
      pairVec finSumFinEquiv (b.1 *ᵥ t *ᵥ u) (b.1 *ᵥ t *ᵥ u) := by
    calc _ = (G * B).1 *ᵥ (Y.1 *ᵥ ((B⁻¹).1 *ᵥ pairVec finSumFinEquiv z z)) := by
          simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (G * B).1 *ᵥ (x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)) := by rw [e1, e2]
      _ = (G * B * x).1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by
          simp only [Units.val_mul, Matrix.mulVec_mulVec]
      _ = B.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by rw [hB]
      _ = _ := by rw [hBdef, val_blkGL]; exact blkMat_mulVec _ _ _ _ _
  rw [e3]
  exact (mem_diagSub finSumFinEquiv).2 ⟨_, rfl⟩

end Generic

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {n : ℕ}

/- English proof (translation)
Substitute `hQ` using the available equality. Rewrite using `[JR_dblGram, val_blkGL, cT_blkMat, dblGram, blkMat_mul, blkMat_mul, dblGram, locGram]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul]`.
-/
theorem gram_blk (σ : E →ₐ[F] E) {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (b : GL (Fin n) (R ⊗[F] E)) :
    cT (sigR R σ) (blkGL finSumFinEquiv (b, b)).1 * JR R Q * (blkGL finSumFinEquiv (b, b)).1 =
      dblGram finSumFinEquiv (locGram σ J b) := by
  subst hQ
  rw [JR_dblGram, val_blkGL, cT_blkMat, dblGram, blkMat_mul, blkMat_mul, dblGram, locGram]
  simp only [Matrix.mul_neg, Matrix.neg_mul]

/- English proof (translation)
Establish `h1 : cT (sigR R σ) (JR (F` using `F) R J) = JR R J := by`. Use extensionality with `i j`. Simplify using `only [cT, JR, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[← hJ i j]`. Both sides reduce to the same expression.

Establish `h2 : cT (sigR R σ) (cT (sigR R σ) b.1) = b.1`. Use extensionality with `i j`. Simplify using `[cT, GlobalTheory.Doubling.sigR_invol hσ]`. Rewrite using `[locGram, cT_mul, cT_mul, h1, h2, Matrix.mul_assoc]`.
-/
theorem cT_locGram (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (b : GL (Fin n) (R ⊗[F] E)) :
    cT (sigR R σ) (locGram σ J b) = locGram σ J b := by
  have h1 : cT (sigR R σ) (JR (F := F) R J) = JR R J := by
    ext i j
    simp only [cT, JR, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hJ i j]
    rfl
  have h2 : cT (sigR R σ) (cT (sigR R σ) b.1) = b.1 := by
    ext i j
    simp [cT, GlobalTheory.Doubling.sigR_invol hσ]
  rw [locGram, cT_mul, cT_mul, h1, h2, Matrix.mul_assoc]

end Points

end GlobalTheory.CompanionTheory.IwaDbl.FrameCore

end
