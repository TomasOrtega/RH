import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousAtMN

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenInfH

open PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

variable {D : D7} {n : ℕ}

/- English proof (translation)
Take `⟨u, hu⟩` from `h2`. Use `set y : AE D := glueA D (splitInv D fun τ => (psiT D τ x)⁻¹) ((u⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)`. Establish `hxy : x * y = 1`. Apply `ae_ext' D` to reduce the goal to its premises. Introduce `τ`.

Rewrite using `[map_mul, psiT_glueA, map_one, mul_inv_cancel₀ (h1 τ)]`. Rewrite using `[map_mul, finPart_glueA, map_one, ← hu, Units.mul_inv]`. Conclude with `⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩`.
-/
theorem isUnit_of_comps (x : AE D) (h1 : ∀ τ, psiT D τ x ≠ 0) (h2 : IsUnit (finPart D x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h2
  set y : AE D := glueA D (splitInv D fun τ => (psiT D τ x)⁻¹) ((u⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)
  have hxy : x * y = 1 := by
    apply ae_ext' D
    · intro τ
      rw [map_mul, psiT_glueA, map_one, mul_inv_cancel₀ (h1 τ)]
    · rw [map_mul, finPart_glueA, map_one, ← hu, Units.mul_inv]
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl`.
-/
theorem cT_blk4 {R : Type} [CommRing R] (σ : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (blk4 a b c d) = blk4 (Formalism.UG.cT σ a) (Formalism.UG.cT σ c) (Formalism.UG.cT σ b) (Formalism.UG.cT σ d) := by
  ext i j
  simp only [Formalism.UG.cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_zero' {R : Type} [CommRing R] (σ : R →+* R) : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  ext i j; simp [Formalism.UG.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_neg' {R : Type} [CommRing R] (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (-M) = -Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [blk4, Matrix.neg_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl`.
-/
theorem blk4_neg {R : Type} [CommRing R] (a b c d : Matrix (Fin n) (Fin n) R) :
    blk4 (-a) (-b) (-c) (-d) = -blk4 a b c d := by
  ext i j
  simp only [blk4, Matrix.neg_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    blkDm (M.map f) = (blkDm M).map f := by
  ext i j; rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blkDm, Matrix.toBlocks₂₂, Matrix.one_apply]`.
-/
theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkDm, Matrix.toBlocks₂₂, Matrix.one_apply]

/- English proof (translation)
Simplify using `only [eI, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : i ∈ I <;> simp [h]`.
-/
theorem eI_mul_self {R : Type} [CommRing R] (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  simp only [eI, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

/- English proof (translation)
Simplify using `only [eI, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : i ∈ I <;> simp [h]`.
-/
theorem eI_conjTranspose (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) ℂ)ᴴ = eI I := by
  simp only [eI, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

/- English proof (translation)
Rewrite using `[submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.add_mul, he]`. Apply the tactic sequence `congr 1 <;> abel`.
-/
theorem weyl_idem {R : Type} [CommRing R] (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) :
    blk4 1 e 0 1 * blk4 1 0 (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.add_mul, he]
  congr 1 <;> abel

/- English proof (translation)
Rewrite using `[cT_blk4, Formalism.UG.cT_one, cT_zero', hb, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]`. Apply the tactic sequence `congr 1 <;> simp`.
-/
theorem unip_unitary {R : Type} [CommRing R] (σ : R →+* R) (b : Matrix (Fin n) (Fin n) R) (hb : Formalism.UG.cT σ b = b) :
    Formalism.UG.cT σ (blk4 1 b 0 1) * blk4 0 1 (-1) 0 * blk4 1 b 0 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hb, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

/- English proof (translation)
Rewrite using `[cT_blk4, Formalism.UG.cT_one, cT_zero', hc, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]`. Apply the tactic sequence `congr 1 <;> simp`.
-/
theorem unipBar_unitary {R : Type} [CommRing R] (σ : R →+* R) (c : Matrix (Fin n) (Fin n) R) (hc : Formalism.UG.cT σ c = c) :
    Formalism.UG.cT σ (blk4 1 0 c 1) * blk4 0 1 (-1) 0 * blk4 1 0 c 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hc, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

/- English proof (translation)
Rewrite using `[JR, Jst, block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]`.
-/
theorem JR_Jst (D : D7) (n : ℕ) : JR (F := D.host.F) (AF D.host.F) (Jst D n) = blk4 0 1 (-1) 0 := by
  rw [JR, Jst, block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _)]

def nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) b = b) : G D n :=
  (⟨⟨blk4 1 b 0 1, blk4 1 (-b) 0 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 b 0 1) * JR (AF D.host.F) (Jst D n) * blk4 1 b 0 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unip_unitary _ b hb⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) c = c) : G D n :=
  (⟨⟨blk4 1 0 c 1, blk4 1 0 (-c) 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 0 c 1) * JR (AF D.host.F) (Jst D n) * blk4 1 0 c 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unipBar_unitary _ c hc⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb) : mat (nEl b hb) = blk4 1 b 0 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc) : mat (nBarEl c hc) = blk4 1 0 c 1 := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`.
-/
theorem cT_starRingEnd (M : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set M := (mat k).map (psiT D τ) with hM`. Establish `hgU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k = JR (AF D.host.F) (Jst D n)` using `k.2`. Establish `hu : Mᴴ * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0`. Use `congrArg (fun X => X.map (psiT D τ)) hgU` as an intermediate fact. Simplify using `only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at this`.

Conclude with `this`. Establish `hJJ : (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1`. Rewrite using `[submatrix_fromBlocks_mul]`. Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg]`. Rewrite using `[← block_matrix_one, ← blk4_neg, neg_zero]`.

Establish `hinv : ((-(blk4 0 1 (-1) 0)) * Mᴴ * blk4 0 1 (-1) 0) * M = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, Matrix.neg_mul, hJJ, neg_neg]`. Establish `hdet : IsUnit M.det` using `Matrix.isUnit_det_of_left_inverse hinv`. Establish `hg : Matrix.nonsingInvUnit M hdet ∈ Formalism.UG.UJ (starRingEnd ℂ) (J2 ℂ n)` using `by show Formalism.UG.cT (starRingEnd ℂ) M * J2 ℂ n * M = J2 ℂ n`. Rewrite using `[cT_starRingEnd]`.

Conclude with `hu`. Take `⟨I, hI⟩` from `hL ℂ (starRingEnd ℂ) (fun a => star_star a) n _ hg`. Conclude with `⟨I, hI⟩`.
-/
theorem exists_I (hL : LocRedField) (k : G D n) (τ : D.what₂.Tau) :
    ∃ I : Finset (Fin n), IsUnit (blkDm ((mat k).map (psiT D τ) * wIm I)).det := by
  set M := (mat k).map (psiT D τ) with hM
  have hgU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k =
      JR (AF D.host.F) (Jst D n) := k.2
  have hu : Mᴴ * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0 := by
    have := congrArg (fun X => X.map (psiT D τ)) hgU
    simp only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at this
    exact this
  have hJJ : (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
    rw [submatrix_fromBlocks_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg]
    rw [← block_matrix_one, ← blk4_neg, neg_zero]
  have hinv : ((-(blk4 0 1 (-1) 0)) * Mᴴ * blk4 0 1 (-1) 0) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, Matrix.neg_mul, hJJ, neg_neg]
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hinv
  have hg : Matrix.nonsingInvUnit M hdet ∈ Formalism.UG.UJ (starRingEnd ℂ) (J2 ℂ n) := by
    show Formalism.UG.cT (starRingEnd ℂ) M * J2 ℂ n * M = J2 ℂ n
    rw [cT_starRingEnd]
    exact hu
  obtain ⟨I, hI⟩ := hL ℂ (starRingEnd ℂ) (fun a => star_star a) n _ hg
  exact ⟨I, hI⟩

end PositivityTheory.Rg.Sw.Glob.GenInfH

namespace PositivityTheory.Rg.Sw.Glob

open GenInfH PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D n k hk hfin`. Use `choose I hI using exists_I hL k`. Use `set B : Matrix (Fin n) (Fin n) (AE D) := Matrix.of fun i j => glueA D (splitInv D fun τ => (eI (I τ) : Matrix (Fin n) (Fin n) ℂ) i j) 0 with hBdef`. Establish `hBτ : ∀ τ, B.map (psiT D τ) = eI (I τ)`. Introduce `τ`.

Use extensionality with `i j`. Simplify using `only [hBdef, Matrix.map_apply, Matrix.of_apply, psiT_glueA]`. Establish `hBf : B.map (finPart D) = 0`. Use extensionality with `i j`. Simplify using `only [hBdef, Matrix.map_apply, Matrix.of_apply, finPart_glueA, Matrix.zero_apply]`.

Establish `hBB : B * B = B`. Apply `mat_ext D` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[Matrix.map_mul, hBτ, eI_mul_self]`. Rewrite using `[Matrix.map_mul, hBf, Matrix.zero_mul]`.

Establish `hBc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B`. Apply `mat_ext D` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[cT_map_psiT', hBτ, eI_conjTranspose]`. Rewrite using `[PositivityTheory.Rg.Sw.Glob.EmbP.cT_map_fin, hBf]`.

Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`. Establish `hBc' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B` using `by rw [cT_neg', hBc]`. Use `set W : G D n := nEl B hBc * nBarEl (-B) hBc' * nEl B hBc with hW`. Establish `hWmat : mat W = blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1` using `rfl`.

Establish `hWτ : ∀ τ, (mat W).map (psiT D τ) = wIm (I τ)`. Introduce `τ`. Rewrite using `[hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBτ, weyl_idem _ (eI_mul_self _)]`. Both sides reduce to the same expression. Establish `hWf : (mat W).map (finPart D) = 1`.

Rewrite using `[hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBf, neg_zero, block_matrix_one, Matrix.one_mul, Matrix.one_mul]`. Establish `hunit : IsUnit (blkDm (mat (k * W))).det`. Apply `GenInfH.isUnit_of_comps` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hWτ]`.

Conclude with `(hI τ).ne_zero`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hfin, hWf, Matrix.one_mul, blkDm_one, Matrix.det_one]`. Conclude with `isUnit_one`. Establish `h1` using `hU D n (k * W) hunit`. Establish `h2 : W ∈ Subgroup.closure (genSet D n)`.

Use `Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)`. Conclude with `Subgroup.subset_closure (Or.inr (Or.inr ⟨-B, rfl⟩))`. Conclude with `Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)`. Establish `: k = (k * W) * W⁻¹` using `by group`.

Rewrite using `[this]`. Conclude with `Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)`.
-/
theorem kInInf_of (hU : UnitD) (hL : LocRedField) : KInInf := by
  intro D n k hk hfin
  classical
  choose I hI using exists_I hL k
  set B : Matrix (Fin n) (Fin n) (AE D) :=
    Matrix.of fun i j => glueA D (splitInv D fun τ => (eI (I τ) : Matrix (Fin n) (Fin n) ℂ) i j) 0 with hBdef
  have hBτ : ∀ τ, B.map (psiT D τ) = eI (I τ) := by
    intro τ; ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  have hBf : B.map (finPart D) = 0 := by
    ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, finPart_glueA, Matrix.zero_apply]
  have hBB : B * B = B := by
    apply mat_ext D
    · intro τ; rw [Matrix.map_mul, hBτ, eI_mul_self]
    · rw [Matrix.map_mul, hBf, Matrix.zero_mul]
  have hBc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    apply mat_ext D
    · intro τ; rw [cT_map_psiT', hBτ, eI_conjTranspose]
    · rw [PositivityTheory.Rg.Sw.Glob.EmbP.cT_map_fin, hBf]
      ext i j; simp [Formalism.UG.cT]
  have hBc' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [cT_neg', hBc]
  set W : G D n := nEl B hBc * nBarEl (-B) hBc' * nEl B hBc with hW
  have hWmat : mat W = blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1 := rfl
  have hWτ : ∀ τ, (mat W).map (psiT D τ) = wIm (I τ) := by
    intro τ
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBτ, weyl_idem _ (eI_mul_self _)]
    rfl
  have hWf : (mat W).map (finPart D) = 1 := by
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBf, neg_zero, block_matrix_one, Matrix.one_mul, Matrix.one_mul]
  have hunit : IsUnit (blkDm (mat (k * W))).det := by
    apply GenInfH.isUnit_of_comps
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hWτ]
      exact (hI τ).ne_zero
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hfin, hWf, Matrix.one_mul,
        blkDm_one, Matrix.det_one]
      exact isUnit_one
  have h1 := hU D n (k * W) hunit
  have h2 : W ∈ Subgroup.closure (genSet D n) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr (Or.inr ⟨-B, rfl⟩))
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
  have : k = (k * W) * W⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

end PositivityTheory.Rg.Sw.Glob
