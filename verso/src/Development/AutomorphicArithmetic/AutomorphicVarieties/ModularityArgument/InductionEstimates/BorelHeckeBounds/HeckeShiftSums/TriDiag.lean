import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SubDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PluckOne

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private def pl {R : Type} [CommRing R] (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i j : Fin (2 + 2)) : R :=
  M (Fin.natAdd 2 0) i * M (Fin.natAdd 2 1) j - M (Fin.natAdd 2 0) j * M (Fin.natAdd 2 1) i

/- English proof (translation)
Rewrite using `[Matrix.det_fin_two]`. Simplify using `only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, pl]`.
-/
private theorem pl_det {R : Type} [CommRing R] (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i j : Fin (2 + 2)) :
    (M.submatrix (Fin.natAdd 2) ![i, j]).det = pl M i j := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, pl]

/- English proof (translation)
Simplify using `only [pl]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pl_swap {R : Type} [CommRing R] (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i j : Fin (2 + 2)) :
    pl M j i = - pl M i j := by
  simp only [pl]; ring

/- English proof (translation)
Simplify using `only [pl, Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pl_mul {R : Type} [CommRing R] (A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (p q : Fin (2 + 2)) :
    pl (A * B) p q = ∑ k, ∑ l, pl A k l * (B k p * B l q) := by
  simp only [pl, Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_two]
  ring

/- English proof (translation)
Establish `hzero : ∀ k l, ¬ (k = c₁ ∧ l = c₂) → pl A k l * (B k c₁ * B l c₂) = 0`. Introduce `k l hkl`. Distinguish the cases in `h1 : c₁ < k`. Rewrite using `[hB k c₁ h1, zero_mul, mul_zero]`. Distinguish the cases in `h2 : c₂ < l`.

Rewrite using `[hB l c₂ h2, mul_zero, mul_zero]`. Establish `h1'` using `not_lt.1 h1`. Establish `h2'` using `not_lt.1 h2`. Break down `lt_trichotomy k l with h | h | h` into its components or cases. Rewrite using `[hz k l h h1' h2' hkl, zero_mul]`.

Substitute `h` using the available equality. Establish `: pl A k k = 0` using `by simp only [pl]; ring`. Rewrite using `[this, zero_mul]`. Rewrite using `[pl_swap, hz l k h (h.le.trans ?_ |>.trans le_rfl) (h1'.trans hc.le) ?_, neg_zero, zero_mul]`. Conclude with `h1'`.

Introduce and unpack `⟨-, rfl⟩`. Conclude with `absurd hc (not_lt.2 h1')`. Rewrite using `[pl_mul, Finset.sum_eq_single c₁, Finset.sum_eq_single c₂]`. Introduce `l _ hl`. Conclude with `hzero _ _ fun h => hl h.2`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `k _ hk`. Conclude with `Finset.sum_eq_zero fun l _ => hzero _ _ fun h => hk h.1`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem pl_tri {R : Type} [CommRing R] (A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R)
    (hB : ∀ i j, j < i → B i j = 0) {c₁ c₂ : Fin (2 + 2)} (hc : c₁ < c₂)
    (hz : ∀ i j, i < j → i ≤ c₁ → j ≤ c₂ → ¬ (i = c₁ ∧ j = c₂) → pl A i j = 0) :
    pl (A * B) c₁ c₂ = pl A c₁ c₂ * (B c₁ c₁ * B c₂ c₂) := by
  have hzero : ∀ k l, ¬ (k = c₁ ∧ l = c₂) → pl A k l * (B k c₁ * B l c₂) = 0 := by
    intro k l hkl
    by_cases h1 : c₁ < k
    · rw [hB k c₁ h1, zero_mul, mul_zero]
    by_cases h2 : c₂ < l
    · rw [hB l c₂ h2, mul_zero, mul_zero]
    have h1' := not_lt.1 h1
    have h2' := not_lt.1 h2
    rcases lt_trichotomy k l with h | h | h
    · rw [hz k l h h1' h2' hkl, zero_mul]
    · subst h
      have : pl A k k = 0 := by simp only [pl]; ring
      rw [this, zero_mul]
    · rw [pl_swap, hz l k h (h.le.trans ?_ |>.trans le_rfl) (h1'.trans hc.le) ?_, neg_zero, zero_mul]
      · exact h1'
      · rintro ⟨-, rfl⟩
        exact absurd hc (not_lt.2 h1')
  rw [pl_mul, Finset.sum_eq_single c₁, Finset.sum_eq_single c₂]
  · intro l _ hl
    exact hzero _ _ fun h => hl h.2
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    exact Finset.sum_eq_zero fun l _ => hzero _ _ fun h => hk h.1
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `set M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑g with hM`. Set `S : Set (Fin (2 + 2) × Fin (2 + 2))` to `{p | p.1 < p.2 ∧ pl M p.1 p.2 ≠ 0}`. Establish `hne : S.Nonempty`. Take `⟨c, hc, hd⟩` from `(pluck g g).1`. Establish `e : c = ![c 0, c 1]`.

Apply the tactic sequence `ext x; fin_cases x <;> rfl`. Rewrite `hd` using `[e, pl_det]`. Establish `h01 : c 0 ≠ c 1` using `fun h => absurd (hc h) (by decide)`. Break down `lt_or_gt_of_ne h01 with h | h` into its components or cases. Conclude with `⟨(c 0, c 1), h, hd⟩`.

Use `⟨(c 1, c 0), h, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pl M (c 1) (c 0) ≠ 0`. Rewrite using `[pl_swap]`. Conclude with `neg_ne_zero.2 hd`. Take `⟨⟨c₁, c₂⟩, ⟨h1, h2⟩, hmin⟩` from `Set.exists_min_image S (fun p => 4 * (p.2 : ℕ) + (p.1 : ℕ)) S.toFinite hne`.

Use `⟨c₁, c₂, h1, h2, fun i j hij hi hj hn => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h3` using `hmin (i, j) ⟨hij, h⟩`. Simplify using `only at h3`. Establish `hi' : (i : ℕ) ≤ c₁` using `hi`.

Establish `hj' : (j : ℕ) ≤ c₂` using `hj`. Conclude with `hn ⟨Fin.ext (by omega), Fin.ext (by omega)⟩`.
-/
private theorem pl_pick {F : Type} [Field F] (g : GL (Fin (2 + 2)) F) :
    ∃ c₁ c₂ : Fin (2 + 2), c₁ < c₂ ∧ pl (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) c₁ c₂ ≠ 0 ∧
      ∀ i j, i < j → i ≤ c₁ → j ≤ c₂ → ¬ (i = c₁ ∧ j = c₂) → pl (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i j = 0 := by
  set M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑g with hM
  let S : Set (Fin (2 + 2) × Fin (2 + 2)) := {p | p.1 < p.2 ∧ pl M p.1 p.2 ≠ 0}
  have hne : S.Nonempty := by
    obtain ⟨c, hc, hd⟩ := (pluck g g).1
    have e : c = ![c 0, c 1] := by
      ext x; fin_cases x <;> rfl
    rw [e, pl_det] at hd
    have h01 : c 0 ≠ c 1 := fun h => absurd (hc h) (by decide)
    rcases lt_or_gt_of_ne h01 with h | h
    · exact ⟨(c 0, c 1), h, hd⟩
    · refine ⟨(c 1, c 0), h, ?_⟩
      change pl M (c 1) (c 0) ≠ 0
      rw [pl_swap]
      exact neg_ne_zero.2 hd
  obtain ⟨⟨c₁, c₂⟩, ⟨h1, h2⟩, hmin⟩ := Set.exists_min_image S (fun p => 4 * (p.2 : ℕ) + (p.1 : ℕ)) S.toFinite hne
  refine ⟨c₁, c₂, h1, h2, fun i j hij hi hj hn => ?_⟩
  by_contra h
  have h3 := hmin (i, j) ⟨hij, h⟩
  simp only at h3
  have hi' : (i : ℕ) ≤ c₁ := hi
  have hj' : (j : ℕ) ≤ c₂ := hj
  exact hn ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/- English proof (translation)
Establish `h2` using `hz j 2 (Fin.lt_def.2 hj) (by rintro ⟨rfl, -⟩; simp at hj)`. Establish `h3` using `hz j 3 (Fin.lt_def.2 (by simp; omega)) (by rintro ⟨rfl, -⟩; simp at hj)`. Simplify using `only [pl] at h h2 h3`. Establish `e0 : M (Fin.natAdd 2 0) j = 0`. Use `(mul_eq_zero.1 (?_ : M (Fin.natAdd 2 0) j * _ = 0)).resolve_right h` and prove the remaining obligations.

Take the linear combination `M (Fin.natAdd 2 0) 2 * h3 - M (Fin.natAdd 2 0) 3 * h2`. Establish `e1 : M (Fin.natAdd 2 1) j = 0`. Use `(mul_eq_zero.1 (?_ : M (Fin.natAdd 2 1) j * _ = 0)).resolve_right h` and prove the remaining obligations. Take the linear combination `M (Fin.natAdd 2 1) 2 * h3 - M (Fin.natAdd 2 1) 3 * h2`. Break down `(by have := i.isLt; omega : (i : ℕ) = 2 ∨ (i : ℕ) = 3) with e | e` into its components or cases.

Rewrite using `[show i = Fin.natAdd 2 0 from Fin.ext e]`. Conclude with `e0`. Rewrite using `[show i = Fin.natAdd 2 1 from Fin.ext e]`. Conclude with `e1`.
-/
private theorem pl_low {F : Type} [Field F] (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (h : pl M 2 3 ≠ 0)
    (hz : ∀ i j, i < j → ¬ (i = 2 ∧ j = 3) → pl M i j = 0) (i j : Fin (2 + 2)) (hi : 2 ≤ (i : ℕ)) (hj : (j : ℕ) < 2) :
    M i j = 0 := by
  have h2 := hz j 2 (Fin.lt_def.2 hj) (by rintro ⟨rfl, -⟩; simp at hj)
  have h3 := hz j 3 (Fin.lt_def.2 (by simp; omega)) (by rintro ⟨rfl, -⟩; simp at hj)
  simp only [pl] at h h2 h3
  have e0 : M (Fin.natAdd 2 0) j = 0 := by
    refine (mul_eq_zero.1 (?_ : M (Fin.natAdd 2 0) j * _ = 0)).resolve_right h
    linear_combination M (Fin.natAdd 2 0) 2 * h3 - M (Fin.natAdd 2 0) 3 * h2
  have e1 : M (Fin.natAdd 2 1) j = 0 := by
    refine (mul_eq_zero.1 (?_ : M (Fin.natAdd 2 1) j * _ = 0)).resolve_right h
    linear_combination M (Fin.natAdd 2 1) 2 * h3 - M (Fin.natAdd 2 1) 3 * h2
  rcases (by have := i.isLt; omega : (i : ℕ) = 2 ∨ (i : ℕ) = 3) with e | e
  · rw [show i = Fin.natAdd 2 0 from Fin.ext e]; exact e0
  · rw [show i = Fin.natAdd 2 1 from Fin.ext e]; exact e1

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single c]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hM h, zero_mul]`. Rewrite using `[hN h, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem tri_diag {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin n) (Fin n) R)
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (c : Fin n) : (M * N) c c = M c c * N c c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Set `B` to `(adelicBorel : Subgroup (AdelicGLn.AdelicGL K n))`. Establish `hmul : ∀ b : B, ((b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c * (((b : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c = 1` using `fun b => by`. Rewrite using `[← tri_diag _ _ (mem_adelicBorel.1 b.2) (mem_adelicBorel.1 (inv_mem b.2)), ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Establish `hmul' : ∀ b : B, (((b : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c * ((b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c = 1` using `fun b => by`.

Rewrite using `[mul_comm]`. Conclude with `hmul b`. Set `f : B → GroundTheory.Global.IdeleGroup K` to `fun b => ⟨_, _, hmul b, hmul' b⟩`. Establish `hf : Continuous f`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `((Units.continuous_val.comp continuous_subtype_val).matrix_elem c c)`. Conclude with `((Units.continuous_val.comp (continuous_subtype_val.inv)).matrix_elem c c)`. Establish `hC : IsCompact ((Subtype.val : B → AdelicGLn.AdelicGL K n) ⁻¹' ω)`. Rewrite using `[Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]`. Conclude with `hω.1`.

Rewrite using `[Subtype.range_coe]`. Conclude with `hω.2`. Take `⟨m, M, hm, -, h⟩` from `exists_pos_bounds hC (f := fun b => (GroundTheory.Global.IdeleGroup.ideleModule K (f b) : ℝ)) (continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp hf)) (fun b _ => (GroundTheory.Global.IdeleGroup.ideleModule K (f b)).2)`. Use `⟨m, hm, fun b hb u hu => ?_⟩` and prove the remaining obligations. Use `(h ⟨b, hω.2 hb⟩ hb).1` as an intermediate fact.

Rewrite `this` using `[show f ⟨b, hω.2 hb⟩ = u from Units.ext hu.symm]`. Then use the resulting hypothesis.
-/
private theorem diag_lb {K : Type} [Field K] [NumberField K] {n : ℕ} {ω : Set (AdelicGLn.AdelicGL K n)} (hω : Bor ω)
    (c : Fin n) : ∃ m : ℝ, 0 < m ∧ ∀ b ∈ ω, ∀ u : GroundTheory.Global.IdeleGroup K,
      (u : 𝔸[K]) = (b : Matrix (Fin n) (Fin n) 𝔸[K]) c c → m ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) := by
  let B := (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n))
  have hmul : ∀ b : B, ((b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c *
      (((b : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c = 1 := fun b => by
    rw [← tri_diag _ _ (mem_adelicBorel.1 b.2) (mem_adelicBorel.1 (inv_mem b.2)), ← Units.val_mul, mul_inv_cancel]
    simp
  have hmul' : ∀ b : B, (((b : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c *
      ((b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) c c = 1 := fun b => by
    rw [mul_comm]; exact hmul b
  let f : B → GroundTheory.Global.IdeleGroup K := fun b => ⟨_, _, hmul b, hmul' b⟩
  have hf : Continuous f := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact ((Units.continuous_val.comp continuous_subtype_val).matrix_elem c c)
    · exact ((Units.continuous_val.comp (continuous_subtype_val.inv)).matrix_elem c c)
  have hC : IsCompact ((Subtype.val : B → AdelicGLn.AdelicGL K n) ⁻¹' ω) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hω.1
    · rw [Subtype.range_coe]; exact hω.2
  obtain ⟨m, M, hm, -, h⟩ := exists_pos_bounds hC
    (f := fun b => (GroundTheory.Global.IdeleGroup.ideleModule K (f b) : ℝ))
    (continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp hf))
    (fun b _ => (GroundTheory.Global.IdeleGroup.ideleModule K (f b)).2)
  refine ⟨m, hm, fun b hb u hu => ?_⟩
  have := (h ⟨b, hω.2 hb⟩ hb).1
  rwa [show f ⟨b, hω.2 hb⟩ = u from Units.ext hu.symm] at this

/- English proof (translation)
Establish `h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i : Fin 2) j, (unipMatrix X * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j`. Introduce `M i j`. Apply the tactic sequence `have : (blockEntry X * M) (Fin.natAdd 2 i) j = 0 := by`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[blockEntry_apply, dif_neg (by simp), zero_mul]`. Rewrite using `[unipMatrix, add_mul, one_mul, Matrix.add_apply, this, add_zero]`. Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, Units.val_mul, coe_unipGL, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]`. Simplify using `only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]`.
-/
private theorem rows_eq {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R)
    (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (c : Fin 2 → Fin (2 + 2)) :
    (((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) * h).submatrix (Fin.natAdd 2) c =
      (b : Matrix (Fin 2) (Fin 2) R) * h.submatrix (Fin.natAdd 2) c := by
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i : Fin 2) j,
      (unipMatrix X * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro M i j
    have : (blockEntry X * M) (Fin.natAdd 2 i) j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [blockEntry_apply, dif_neg (by simp), zero_mul]
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, this, add_zero]
  ext i j
  rw [Matrix.submatrix_apply, Units.val_mul, coe_unipGL, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]

/- English proof (translation)
Establish `hBb` using `mul_mem hB (diagUnits_mem_adelicBorel (K := K) (2 + 2) (fun i => posIdele (K := K) (ρ i) (hρ i)))`. Establish `hent : ∀ c, ((b * diagUnits (2 + 2) (fun i => posIdele (K` using `K) (ρ i) (hρ i)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c = (b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c * ((posIdele (K := K) (ρ c) (hρ c) : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) := by`. Introduce `c`. Rewrite using `[Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]`. Use `⟨fun c => (isUnit_apply_self_of_mem_adelicBorel hBb c).unit, fun c => IsUnit.unit_spec _, fun c => ?_⟩` and prove the remaining obligations.

Establish `hβ : (((isUnit_apply_self_of_mem_adelicBorel hBb c).unit : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) = _` using `IsUnit.unit_spec _`. Establish `h1` using `hlb c ((isUnit_apply_self_of_mem_adelicBorel hBb c).unit * (posIdele (K := K) (ρ c) (hρ c))⁻¹) (by`. Rewrite using `[Units.val_mul, hβ, hent, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one])`. Rewrite `h1` using `[map_mul, map_inv, Positive.val_mul, Positive.coe_inv, ideleModule_posIdele]`. Establish `hp : 0 < ρ c ^ Module.finrank ℚ K` using `pow_pos (hρ c) _`.

Rewrite `h1` using `[← div_eq_mul_inv, le_div_iff₀ hp]`. Then use the resulting hypothesis.
-/
private theorem ent_step {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} {m₀ : ℝ}
    (hB : b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    (hlb : ∀ c, ∀ u : GroundTheory.Global.IdeleGroup K,
      (u : 𝔸[K]) = (b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c → m₀ ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ))
    (ρ : Fin (2 + 2) → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∃ β : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K,
      (∀ c, (β c : 𝔸[K]) = ((b * diagUnits (2 + 2) (fun i => posIdele (K := K) (ρ i) (hρ i)) : AdelicGLn.AdelicGL K (2 + 2)) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c) ∧
      ∀ c, m₀ * ρ c ^ Module.finrank ℚ K ≤ (GroundTheory.Global.IdeleGroup.ideleModule K (β c) : ℝ) := by
  have hBb := mul_mem hB (diagUnits_mem_adelicBorel (K := K) (2 + 2) (fun i => posIdele (K := K) (ρ i) (hρ i)))
  have hent : ∀ c, ((b * diagUnits (2 + 2) (fun i => posIdele (K := K) (ρ i) (hρ i)) : AdelicGLn.AdelicGL K (2 + 2)) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c =
      (b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c * ((posIdele (K := K) (ρ c) (hρ c) : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) := by
    intro c
    rw [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]
  refine ⟨fun c => (isUnit_apply_self_of_mem_adelicBorel hBb c).unit, fun c => IsUnit.unit_spec _, fun c => ?_⟩
  have hβ : (((isUnit_apply_self_of_mem_adelicBorel hBb c).unit : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) = _ := IsUnit.unit_spec _
  have h1 := hlb c ((isUnit_apply_self_of_mem_adelicBorel hBb c).unit * (posIdele (K := K) (ρ c) (hρ c))⁻¹) (by
    rw [Units.val_mul, hβ, hent, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one])
  rw [map_mul, map_inv, Positive.val_mul, Positive.coe_inv, ideleModule_posIdele] at h1
  have hp : 0 < ρ c ^ Module.finrank ℚ K := pow_pos (hρ c) _
  rwa [← div_eq_mul_inv, le_div_iff₀ hp] at h1

/- English proof (translation)
Establish `hy : (((AdelicGLn.det K 2 a)⁻¹ * (GroundTheory.Global.IdeleGroup.diagonal K p * (β₁ * β₂)) : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) = ((h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, e, ← AdelicGLn.coe_det, Units.inv_mul_cancel_left]`. Establish `hu : IsUnit ((h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det` using `hy ▸ Units.isUnit _`. Establish `hin : Function.Injective (Fin.natAdd 2 : Fin 2 → Fin (2 + 2))` using `fun x y hxy => by`. Simplify `hxy` using `[Fin.ext_iff]`.

Establish `h3` using `(subDet (K := K) (2 + 2) h hh (Fin.natAdd 2) c hin hc).2.2 (Matrix.GeneralLinearGroup.mk'' _ hu) rfl`. Establish `h4 : AdelicGLn.det K 2 (Matrix.GeneralLinearGroup.mk'' _ hu) = (AdelicGLn.det K 2 a)⁻¹ * (GroundTheory.Global.IdeleGroup.diagonal K p * (β₁ * β₂))` using `Units.ext (by rw [hy, AdelicGLn.coe_det]; rfl)`. Express the relevant statement in the definitionally equal form `((GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 _) : _) : ℝ) ≤ 1 at h3`. Rewrite `h3` using `[h4, map_mul, map_inv, map_mul, map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, one_mul]`. Express the relevant statement in the definitionally equal form `((detModule K 2 a)⁻¹ * (GroundTheory.Global.IdeleGroup.ideleModule K β₁ * GroundTheory.Global.IdeleGroup.ideleModule K β₂) : {r : ℝ // 0 < r}).1 ≤ 1 at h3`.

Rewrite `h3` using `[Positive.val_mul, Positive.coe_inv, Positive.val_mul, inv_mul_le_iff₀ (detModule K 2 a).2, mul_one]`. Conclude with `h3`.
-/
private theorem mod_step {K : Type} [Field K] [NumberField K] {h : AdelicGLn.AdelicGL K (2 + 2)}
    (hh : h ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))) (a : AdelicGLn.AdelicGL K 2)
    {c : Fin 2 → Fin (2 + 2)} (hc : Function.Injective c) (p : Kˣ) (β₁ β₂ : GroundTheory.Global.IdeleGroup K)
    (e : algebraMap K 𝔸[K] (p : K) * ((β₁ : 𝔸[K]) * (β₂ : 𝔸[K])) =
      (a : Matrix (Fin 2) (Fin 2) 𝔸[K]).det * ((h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det) :
    (GroundTheory.Global.IdeleGroup.ideleModule K β₁ : ℝ) * (GroundTheory.Global.IdeleGroup.ideleModule K β₂ : ℝ) ≤ (detModule K 2 a : ℝ) := by
  have hy : (((AdelicGLn.det K 2 a)⁻¹ * (GroundTheory.Global.IdeleGroup.diagonal K p * (β₁ * β₂)) : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) =
      ((h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, e, ← AdelicGLn.coe_det, Units.inv_mul_cancel_left]
  have hu : IsUnit ((h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det := hy ▸ Units.isUnit _
  have hin : Function.Injective (Fin.natAdd 2 : Fin 2 → Fin (2 + 2)) := fun x y hxy => by
    simpa [Fin.ext_iff] using hxy
  have h3 := (subDet (K := K) (2 + 2) h hh (Fin.natAdd 2) c hin hc).2.2
    (Matrix.GeneralLinearGroup.mk'' _ hu) rfl
  have h4 : AdelicGLn.det K 2 (Matrix.GeneralLinearGroup.mk'' _ hu) =
      (AdelicGLn.det K 2 a)⁻¹ * (GroundTheory.Global.IdeleGroup.diagonal K p * (β₁ * β₂)) :=
    Units.ext (by rw [hy, AdelicGLn.coe_det]; rfl)
  change ((GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 _) : _) : ℝ) ≤ 1 at h3
  rw [h4, map_mul, map_inv, map_mul, map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, one_mul] at h3
  change ((detModule K 2 a)⁻¹ * (GroundTheory.Global.IdeleGroup.ideleModule K β₁ * GroundTheory.Global.IdeleGroup.ideleModule K β₂) : {r : ℝ // 0 < r}).1 ≤ 1 at h3
  rw [Positive.val_mul, Positive.coe_inv, Positive.val_mul, inv_mul_le_iff₀ (detModule K 2 a).2, mul_one] at h3
  exact h3

/- English proof (translation)
Establish `hA : ∀ i j, pl ((AdelicGLn.diagonal K (2 + 2) g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j = algebraMap K 𝔸[K] (pl (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) i j)`. Introduce `i j`. Simplify using `only [pl, AdelicGLn.diagonal_apply, map_sub, map_mul]`. Establish `t1` using `pl_tri ((AdelicGLn.diagonal K (2 + 2) g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) (fun i j hij => mem_adelicBorel.1 hB hij) hc (fun i j h1 h2 h3 h4 => by rw [hA, hz i j h1 h2 h3 h4, map_zero])`. Rewrite `t1` using `[hA]`.

Rewrite using `[← t1, ← Units.val_mul, e, Units.val_mul _ h, ← pl_det, rows_eq, Matrix.det_mul]`.
-/
private theorem min_step {K : Type} [Field K] [NumberField K] (g : GL (Fin (2 + 2)) K) {B h : AdelicGLn.AdelicGL K (2 + 2)}
    (X : UPos (2 + 2) 2 → 𝔸[K]) (a₁ a₂ : AdelicGLn.AdelicGL K 2)
    (hB : B ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    (e : AdelicGLn.diagonal K (2 + 2) g * B = unipGL X * blk a₁ a₂ * h) {c₁ c₂ : Fin (2 + 2)} (hc : c₁ < c₂)
    (hz : ∀ i j, i < j → i ≤ c₁ → j ≤ c₂ → ¬ (i = c₁ ∧ j = c₂) → pl (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) i j = 0) :
    algebraMap K 𝔸[K] (pl (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) c₁ c₂) *
        ((B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c₁ c₁ * (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c₂ c₂) =
      (a₂ : Matrix (Fin 2) (Fin 2) 𝔸[K]).det *
        ((h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) ![c₁, c₂]).det := by
  have hA : ∀ i j, pl ((AdelicGLn.diagonal K (2 + 2) g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j =
      algebraMap K 𝔸[K] (pl (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) i j) := by
    intro i j
    simp only [pl, AdelicGLn.diagonal_apply, map_sub, map_mul]
  have t1 := pl_tri ((AdelicGLn.diagonal K (2 + 2) g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K])
    (B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) (fun i j hij => mem_adelicBorel.1 hB hij) hc
    (fun i j h1 h2 h3 h4 => by rw [hA, hz i j h1 h2 h3 h4, map_zero])
  rw [hA] at t1
  rw [← t1, ← Units.val_mul, e, Units.val_mul _ h, ← pl_det, rows_eq, Matrix.det_mul]

/- English proof (translation)
Establish `h1` using `congrArg (fun x : G1 K (2 + 2) => (x : AdelicGLn.AdelicGL K (2 + 2))) hq`. Simplify using `only [Subgroup.coe_mul, coe_unipOne, (blkLaws (K := K)).1, hz, ← hg] at h1`. Rewrite using `[← mul_assoc, ← h1]`. Use `group`.
-/
private theorem eq_step {K : Type} [Field K] [NumberField K] {γ z k' : G1 K (2 + 2)} {g : GL (Fin (2 + 2)) K}
    {B k : AdelicGLn.AdelicGL K (2 + 2)} (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (s : ℝ)
    (hg : AdelicGLn.diagonal K (2 + 2) g = (γ : AdelicGLn.AdelicGL K (2 + 2)))
    (hz : (z : AdelicGLn.AdelicGL K (2 + 2)) = B * k) (hq : γ * z = nn X * lv m₁ m₂ s * k') :
    AdelicGLn.diagonal K (2 + 2) g * B =
      unipGL X * blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K s) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-s)) *
        ((k' : AdelicGLn.AdelicGL K (2 + 2)) * k⁻¹) := by
  have h1 := congrArg (fun x : G1 K (2 + 2) => (x : AdelicGLn.AdelicGL K (2 + 2))) hq
  simp only [Subgroup.coe_mul, coe_unipOne, (blkLaws (K := K)).1, hz, ← hg] at h1
  rw [← mul_assoc, ← h1]
  group

/- English proof (translation)
Take `⟨hρ, b, hb, k, hk, hzb⟩` from `hz`. Take `⟨g, hg⟩` from `hγ`. Establish `hg' : AdelicGLn.diagonal K (2 + 2) g = (γ : AdelicGLn.AdelicGL K (2 + 2))` using `hg`. Take `⟨X, m₁, m₂, s, k', hk', hq⟩` from `iwa (γ * z)`. Establish `hs : HH (γ * z) = s`.

Rewrite using `[hq, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k' hk').1, add_zero]`. Take `⟨c₁, c₂, hc, hne, hzero⟩` from `pl_pick g`. Use `⟨c₁, c₂, hc, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨rfl, rfl⟩`. Apply `hP` to reduce the goal to its premises.

Use `⟨⟨γ, g, hg⟩, ?_, rfl⟩` and prove the remaining obligations. Use `((pkLaws (K := K)).1 _).2 fun i j hi hj => ?_` and prove the remaining obligations. Establish `e` using `pl_low (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) hne (fun i j hij hn => hzero i j hij (by`. Use `j.isLt` as an intermediate fact. Establish `h' : (i : ℕ) < j` using `hij`.

Conclude with `Fin.le_def.2 (by simp; omega)) (by`. Use `j.isLt` as an intermediate fact. Conclude with `Fin.le_def.2 (by simp; omega)) hn) i j hi hj`. Express the relevant statement in the definitionally equal form `(((γ : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K])) i j = 0`. Rewrite using `[← hg', AdelicGLn.diagonal_apply, e, map_zero]`.

Take `⟨β, hβ, hmod⟩` from `ent_step (hω.2 hb) (fun c u hu => hlb c b hb u hu) ρ hρ`. Establish `hBb` using `mul_mem (hω.2 hb) (diagUnits_mem_adelicBorel (K := K) (2 + 2) (fun i => posIdele (K := K) (ρ i) (hρ i)))`. Establish `e1` using `eq_step X m₁ m₂ s hg' hzb hq`. Establish `e2` using `min_step g X _ _ hBb e1 hc hzero`. Rewrite `e2` using `[← hβ, ← hβ]`.

Establish `hh : (k' : AdelicGLn.AdelicGL K (2 + 2)) * k⁻¹ ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))` using `mul_mem hk' (inv_mem hk)`. Establish `hin : Function.Injective ![c₁, c₂]`. Introduce `x y hxy`. Apply the tactic sequence `fin_cases x <;> fin_cases y <;> simp_all [hc.ne, hc.ne']`. Establish `h5` using `mod_step hh _ hin (Units.mk0 _ hne) (β c₁) (β c₂) e2`.

Establish `h6 : (detModule K 2 ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-s)) : ℝ) = Real.exp (-s)`. Rewrite using `[map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]`. Rewrite `h5` using `[h6]`. Rewrite using `[hs]`. Use `le_trans ?_ h5` and prove the remaining obligations.

Conclude with `mul_le_mul (hmod c₁) (hmod c₂) (mul_nonneg hm₀.le (pow_nonneg (hρ c₂).le _)) (GroundTheory.Global.IdeleGroup.ideleModule K (β c₁)).2.le`.
-/
private theorem core {K : Type} [Field K] [NumberField K] {ω : Set (AdelicGLn.AdelicGL K (2 + 2))} (hω : Bor ω)
    {m₀ : ℝ} (hlb : ∀ c, ∀ b ∈ ω, ∀ u : GroundTheory.Global.IdeleGroup K,
      (u : 𝔸[K]) = (b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c → m₀ ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ))
    (hm₀ : 0 < m₀) {ρ : Fin (2 + 2) → ℝ} {z γ : G1 K (2 + 2)} (hz : Sg ω ρ z) (hγ : γ ∈ Gam K (2 + 2)) (hP : γ ∉ PK K) :
    ∃ c₁ c₂ : Fin (2 + 2), c₁ < c₂ ∧ ¬ (c₁ = 2 ∧ c₂ = 3) ∧
      (m₀ * ρ c₁ ^ Module.finrank ℚ K) * (m₀ * ρ c₂ ^ Module.finrank ℚ K) ≤ Real.exp (- HH (γ * z)) := by
  obtain ⟨hρ, b, hb, k, hk, hzb⟩ := hz
  obtain ⟨g, hg⟩ := hγ
  have hg' : AdelicGLn.diagonal K (2 + 2) g = (γ : AdelicGLn.AdelicGL K (2 + 2)) := hg
  obtain ⟨X, m₁, m₂, s, k', hk', hq⟩ := iwa (γ * z)
  have hs : HH (γ * z) = s := by
    rw [hq, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k' hk').1, add_zero]
  obtain ⟨c₁, c₂, hc, hne, hzero⟩ := pl_pick g
  refine ⟨c₁, c₂, hc, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    apply hP
    refine ⟨⟨γ, g, hg⟩, ?_, rfl⟩
    refine ((pkLaws (K := K)).1 _).2 fun i j hi hj => ?_
    have e := pl_low (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) hne (fun i j hij hn => hzero i j hij (by
      have := j.isLt
      have h' : (i : ℕ) < j := hij
      exact Fin.le_def.2 (by simp; omega)) (by
      have := j.isLt
      exact Fin.le_def.2 (by simp; omega)) hn) i j hi hj
    change (((γ : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K])) i j = 0
    rw [← hg', AdelicGLn.diagonal_apply, e, map_zero]
  obtain ⟨β, hβ, hmod⟩ := ent_step (hω.2 hb) (fun c u hu => hlb c b hb u hu) ρ hρ
  have hBb := mul_mem (hω.2 hb) (diagUnits_mem_adelicBorel (K := K) (2 + 2) (fun i => posIdele (K := K) (ρ i) (hρ i)))
  have e1 := eq_step X m₁ m₂ s hg' hzb hq
  have e2 := min_step g X _ _ hBb e1 hc hzero
  rw [← hβ, ← hβ] at e2
  have hh : (k' : AdelicGLn.AdelicGL K (2 + 2)) * k⁻¹ ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) :=
    mul_mem hk' (inv_mem hk)
  have hin : Function.Injective ![c₁, c₂] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [hc.ne, hc.ne']
  have h5 := mod_step hh _ hin (Units.mk0 _ hne) (β c₁) (β c₂) e2
  have h6 : (detModule K 2 ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-s)) : ℝ) = Real.exp (-s) := by
    rw [map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
  rw [h6] at h5
  rw [hs]
  refine le_trans ?_ h5
  exact mul_le_mul (hmod c₁) (hmod c₂)
    (mul_nonneg hm₀.le (pow_nonneg (hρ c₂).le _)) (GroundTheory.Global.IdeleGroup.ideleModule K (β c₁)).2.le

/- English proof (translation)
Use `revert c`. Evaluate the decidable proposition.
-/
private theorem f4 (c : Fin (2 + 2)) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
  revert c; decide

/- English proof (translation)
Use `set u := min 1 t with hu`. Establish `u0 : 0 < u` using `lt_min one_pos ht`. Establish `u1 : u ≤ 1` using `min_le_left _ _`. Establish `ut : u ≤ t` using `min_le_right _ _`. Establish `h01 : u * ρ 1 ≤ ρ 0` using `(mul_le_mul_of_nonneg_right ut (hρ 1).le).trans (hF 0 1 rfl)`.

Establish `h12 : u * ρ 2 ≤ ρ 1` using `(mul_le_mul_of_nonneg_right ut (hρ 2).le).trans (hF 1 2 rfl)`. Establish `h23 : u * ρ 3 ≤ ρ 2` using `(mul_le_mul_of_nonneg_right ut (hρ 3).le).trans (hF 2 3 rfl)`. Establish `hX : 0 ≤ ρ 1 * ρ 3` using `(mul_pos (hρ 1) (hρ 3)).le`. Establish `a1 : u ^ 3 ≤ 1` using `pow_le_one₀ u0.le u1`. Establish `a2 : u ^ 3 ≤ u ^ 2` using `pow_le_pow_of_le_one u0.le u1 (by norm_num)`.

Establish `a3 : u ^ 3 ≤ u` using `by simpa using pow_le_pow_of_le_one u0.le u1 (show 1 ≤ 3 by norm_num)`. Establish `p13 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 1 * ρ 3` using `mul_le_of_le_one_left hX a1`. Establish `p12 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 1 * ρ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `p03 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 0 * ρ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `p02 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 0 * ρ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `p01 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 0 * ρ 1`. Establish `b1 : u * (u * ρ 3) ≤ u * ρ 2` using `mul_le_mul_of_nonneg_left h23 u0.le`.

Establish `b2 : u * (u * (u * ρ 3)) ≤ u * ρ 1` using `mul_le_mul_of_nonneg_left (b1.trans h12) u0.le`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rcases f4 c₁ with rfl | rfl | rfl | rfl <;> rcases f4 c₂ with rfl | rfl | rfl | rfl <;> first`. Consider the case `exact absurd hc (by decide)`. Consider the case `exact absurd ⟨rfl, rfl⟩ hn`.

Consider the case `exact p01`. Consider the case `exact p02`. Consider the case `exact p03`. Consider the case `exact p12`. Consider the case `exact p13`.
-/
private theorem pair_lb {t : ℝ} (ht : 0 < t) {ρ : Fin (2 + 2) → ℝ} (hρ : ∀ i, 0 < ρ i) (hF : Full t ρ)
    {c₁ c₂ : Fin (2 + 2)} (hc : c₁ < c₂) (hn : ¬ (c₁ = 2 ∧ c₂ = 3)) :
    min 1 t ^ 3 * (ρ 1 * ρ 3) ≤ ρ c₁ * ρ c₂ := by
  set u := min 1 t with hu
  have u0 : 0 < u := lt_min one_pos ht
  have u1 : u ≤ 1 := min_le_left _ _
  have ut : u ≤ t := min_le_right _ _
  have h01 : u * ρ 1 ≤ ρ 0 := (mul_le_mul_of_nonneg_right ut (hρ 1).le).trans (hF 0 1 rfl)
  have h12 : u * ρ 2 ≤ ρ 1 := (mul_le_mul_of_nonneg_right ut (hρ 2).le).trans (hF 1 2 rfl)
  have h23 : u * ρ 3 ≤ ρ 2 := (mul_le_mul_of_nonneg_right ut (hρ 3).le).trans (hF 2 3 rfl)
  have hX : 0 ≤ ρ 1 * ρ 3 := (mul_pos (hρ 1) (hρ 3)).le
  have a1 : u ^ 3 ≤ 1 := pow_le_one₀ u0.le u1
  have a2 : u ^ 3 ≤ u ^ 2 := pow_le_pow_of_le_one u0.le u1 (by norm_num)
  have a3 : u ^ 3 ≤ u := by simpa using pow_le_pow_of_le_one u0.le u1 (show 1 ≤ 3 by norm_num)
  have p13 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 1 * ρ 3 := mul_le_of_le_one_left hX a1
  have p12 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 1 * ρ 2 := by
    calc u ^ 3 * (ρ 1 * ρ 3) ≤ u * (ρ 1 * ρ 3) := mul_le_mul_of_nonneg_right a3 hX
      _ = ρ 1 * (u * ρ 3) := by ring
      _ ≤ ρ 1 * ρ 2 := mul_le_mul_of_nonneg_left h23 (hρ 1).le
  have p03 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 0 * ρ 3 := by
    calc u ^ 3 * (ρ 1 * ρ 3) ≤ u * (ρ 1 * ρ 3) := mul_le_mul_of_nonneg_right a3 hX
      _ = (u * ρ 1) * ρ 3 := by ring
      _ ≤ ρ 0 * ρ 3 := mul_le_mul_of_nonneg_right h01 (hρ 3).le
  have p02 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 0 * ρ 2 := by
    calc u ^ 3 * (ρ 1 * ρ 3) ≤ u ^ 2 * (ρ 1 * ρ 3) := mul_le_mul_of_nonneg_right a2 hX
      _ = (u * ρ 1) * (u * ρ 3) := by ring
      _ ≤ ρ 0 * ρ 2 := mul_le_mul h01 h23 (mul_pos u0 (hρ 3)).le (hρ 0).le
  have p01 : u ^ 3 * (ρ 1 * ρ 3) ≤ ρ 0 * ρ 1 := by
    have b1 : u * (u * ρ 3) ≤ u * ρ 2 := mul_le_mul_of_nonneg_left h23 u0.le
    have b2 : u * (u * (u * ρ 3)) ≤ u * ρ 1 := mul_le_mul_of_nonneg_left (b1.trans h12) u0.le
    calc u ^ 3 * (ρ 1 * ρ 3) = (u * (u * (u * ρ 3))) * ρ 1 := by ring
      _ ≤ ρ 0 * ρ 1 := mul_le_mul_of_nonneg_right (b2.trans h01) (hρ 1).le
  rcases f4 c₁ with rfl | rfl | rfl | rfl <;> rcases f4 c₂ with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hc (by decide)
    | exact absurd ⟨rfl, rfl⟩ hn
    | exact p01
    | exact p02
    | exact p03
    | exact p12
    | exact p13

/- English proof (translation)
Introduce `K _ _ ω t hω ht`. Take `⟨C₁, e₀, -, hS⟩` from `sgBasics ω hω`. Use `choose m hm hlb using fun c : Fin (2 + 2) => diag_lb hω c`. Take `⟨c₀, hc₀⟩` from `Finite.exists_min m`. Establish `hm₀` using `hm c₀`.

Establish `hlb' : ∀ c, ∀ b ∈ ω, ∀ u : GroundTheory.Global.IdeleGroup K, (u : 𝔸[K]) = (b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c → m c₀ ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ)` using `fun c b hb u hu => (hc₀ c).trans (hlb c b hb u hu)`. Establish `hτ : 0 < min 1 t ^ 3` using `pow_pos (lt_min one_pos ht) 3`. Use `set d : ℝ := (Module.finrank ℚ K : ℝ) with hd`. Establish `hd0 : 0 ≤ d` using `Nat.cast_nonneg _`. Use `⟨C₁ + d * C₁ - 2 * Real.log (m c₀) - d * Real.log (min 1 t ^ 3), fun ρ z γ hz hF hγ hP => ?_⟩` and prove the remaining obligations.

Take `⟨h2, h3, -⟩` from `hS ρ z hz`. Establish `hρ : ∀ i, 0 < ρ i` using `hz.1`. Take `⟨c₁, c₂, hc, hn, hle⟩` from `core hω hlb' hm₀ hz hγ hP`. Establish `hp` using `pair_lb ht hρ hF hc hn`. Establish `n1` using `(hρ c₁).ne'`.

Establish `n2` using `(hρ c₂).ne'`. Establish `q0` using `(hρ 0).ne'`. Establish `q1` using `(hρ 1).ne'`. Establish `q2` using `(hρ 2).ne'`. Establish `q3` using `(hρ 3).ne'`.

Establish `hpos : 0 < m c₀ * ρ c₁ ^ Module.finrank ℚ K * (m c₀ * ρ c₂ ^ Module.finrank ℚ K)` using `mul_pos (mul_pos hm₀ (pow_pos (hρ _) _)) (mul_pos hm₀ (pow_pos (hρ _) _))`. Establish `h0` using `Real.log_le_log hpos hle`. Rewrite `h0` using `[Real.log_exp, Real.log_mul (mul_pos hm₀ (pow_pos (hρ _) _)).ne' (mul_pos hm₀ (pow_pos (hρ _) _)).ne', Real.log_mul hm₀.ne' (pow_pos (hρ _) _).ne', Real.log_mul hm₀.ne' (pow_pos (hρ _) _).ne', Real.log_pow, Real.log_pow]`. Establish `h1` using `Real.log_le_log (mul_pos hτ (mul_pos (hρ 1) (hρ 3))) hp`. Rewrite `h1` using `[Real.log_mul hτ.ne' (mul_pos (hρ 1) (hρ 3)).ne', Real.log_mul q1 q3, Real.log_mul n1 n2]`.

Establish `h1'` using `mul_le_mul_of_nonneg_left h1 hd0`. Rewrite `h2` using `[Real.log_mul q0 q1]`. Rewrite `h3` using `[Real.log_mul (mul_pos (hρ 0) (hρ 1)).ne' (mul_pos (hρ 2) (hρ 3)).ne', Real.log_mul q0 q1, Real.log_mul q2 q3]`. Establish `h3'` using `mul_le_mul_of_nonneg_left (abs_le.1 h3).1 hd0`. Establish `h2'` using `(abs_le.1 h2).1`.

Rewrite using `[Real.log_div q1 q2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.gain :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Bor ω → 0 < t → ∃ C : ℝ, ∀ (ρ : Fin (2 + 2) → ℝ) (z γ : G1 K (2 + 2)), Sg ω ρ z → Full t ρ → γ ∈ Gam K (2 + 2) → γ ∉ PK K →
      HH (γ * z) ≤ HH z - (Module.finrank ℚ K : ℝ) * Real.log (ρ 1 / ρ 2) + C := by
  intro K _ _ ω t hω ht
  obtain ⟨C₁, e₀, -, hS⟩ := sgBasics ω hω
  choose m hm hlb using fun c : Fin (2 + 2) => diag_lb hω c
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min m
  have hm₀ := hm c₀
  have hlb' : ∀ c, ∀ b ∈ ω, ∀ u : GroundTheory.Global.IdeleGroup K,
      (u : 𝔸[K]) = (b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) c c →
        m c₀ ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) :=
    fun c b hb u hu => (hc₀ c).trans (hlb c b hb u hu)
  have hτ : 0 < min 1 t ^ 3 := pow_pos (lt_min one_pos ht) 3
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨C₁ + d * C₁ - 2 * Real.log (m c₀) - d * Real.log (min 1 t ^ 3), fun ρ z γ hz hF hγ hP => ?_⟩
  obtain ⟨h2, h3, -⟩ := hS ρ z hz
  have hρ : ∀ i, 0 < ρ i := hz.1
  obtain ⟨c₁, c₂, hc, hn, hle⟩ := core hω hlb' hm₀ hz hγ hP
  have hp := pair_lb ht hρ hF hc hn
  have n1 := (hρ c₁).ne'
  have n2 := (hρ c₂).ne'
  have q0 := (hρ 0).ne'
  have q1 := (hρ 1).ne'
  have q2 := (hρ 2).ne'
  have q3 := (hρ 3).ne'
  have hpos : 0 < m c₀ * ρ c₁ ^ Module.finrank ℚ K * (m c₀ * ρ c₂ ^ Module.finrank ℚ K) :=
    mul_pos (mul_pos hm₀ (pow_pos (hρ _) _)) (mul_pos hm₀ (pow_pos (hρ _) _))
  have h0 := Real.log_le_log hpos hle
  rw [Real.log_exp, Real.log_mul (mul_pos hm₀ (pow_pos (hρ _) _)).ne' (mul_pos hm₀ (pow_pos (hρ _) _)).ne',
    Real.log_mul hm₀.ne' (pow_pos (hρ _) _).ne', Real.log_mul hm₀.ne' (pow_pos (hρ _) _).ne', Real.log_pow, Real.log_pow] at h0
  have h1 := Real.log_le_log (mul_pos hτ (mul_pos (hρ 1) (hρ 3))) hp
  rw [Real.log_mul hτ.ne' (mul_pos (hρ 1) (hρ 3)).ne', Real.log_mul q1 q3, Real.log_mul n1 n2] at h1
  have h1' := mul_le_mul_of_nonneg_left h1 hd0
  rw [Real.log_mul q0 q1] at h2
  rw [Real.log_mul (mul_pos (hρ 0) (hρ 1)).ne' (mul_pos (hρ 2) (hρ 3)).ne', Real.log_mul q0 q1, Real.log_mul q2 q3] at h3
  have h3' := mul_le_mul_of_nonneg_left (abs_le.1 h3).1 hd0
  have h2' := (abs_le.1 h2).1
  rw [Real.log_div q1 q2]
  linarith
