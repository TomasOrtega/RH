import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecomposition
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

/- English proof (translation)
The claim follows from `(h.submatrix (Fin.castLE_injective _)).det_pos`.
-/
theorem lminor_pos_of_posDef {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) (k : Fin (m + 1)) :
    0 < lminor M k :=
  (h.submatrix (Fin.castLE_injective _)).det_pos

/- English proof (translation)
Unfold `lminor`. Rewrite using `[submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg, Fintype.card_fin]`.
-/
theorem lminor_neg' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) :
    lminor (-M) k = (-1) ^ (k : ℕ) * lminor M k := by
  unfold lminor
  rw [submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg, Fintype.card_fin]

/- English proof (translation)
The claim follows from `Finset.prod_eq_one fun a ha => by have := Finset.mem_range.1 ha simp [sgn, show a < q by omega]`.
-/
theorem psgn_of_le' {q i : ℕ} (h : i ≤ q) : psgn q i = 1 :=
  Finset.prod_eq_one fun a ha => by
    have := Finset.mem_range.1 ha
    simp [sgn, show a < q by omega]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using psgn_of_le' (le_refl q)`. Consider the case `succ k ih`. Establish `: psgn q (q + (k + 1)) = psgn q (q + k) * sgn q (q + k)` using `Finset.prod_range_succ _ _`. Rewrite using `[this, ih]`.

Simplify using `[sgn, pow_succ]`.
-/
theorem psgn_add' (q k : ℕ) : psgn q (q + k) = (-1) ^ k := by
  induction k with
  | zero => simpa using psgn_of_le' (le_refl q)
  | succ k ih =>
    have : psgn q (q + (k + 1)) = psgn q (q + k) * sgn q (q + k) := Finset.prod_range_succ _ _
    rw [this, ih]
    simp [sgn, pow_succ]

/- English proof (translation)
Take `⟨h₁, h₂⟩` from `GlobalTheory.FlagFibre.lminor_block r p q e he H h2.det_pos.ne'.isUnit`. Establish `hr` using `he.card`. Distinguish the cases in `hi : (i : ℕ) ≤ q`. Rewrite using `[psgn_of_le' hi, one_mul, h₁ i ⟨i, by omega⟩ rfl]`. Conclude with `(Complex.pos_iff.1 (lminor_pos_of_posDef h2 _)).1`.

Establish `hi2` using `i.2`. Take `⟨k, hk⟩ : ∃ k : Fin (p + 1), (i : ℕ) = q + k` from `⟨⟨i - q, by omega⟩, by simp only; omega⟩`. Establish `h3` using `mul_pos h2.det_pos (lminor_pos_of_posDef hs k)`. Rewrite `h3` using `[lminor_neg']`. Rewrite using `[h₂ i k hk, hk, psgn_add', ← Complex.re_ofReal_mul]`.

Establish `h4` using `(Complex.pos_iff.1 h3).1`. Use `h4 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem signs_of_blocks {r p q : ℕ} {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (H : Matrix (Fin r) (Fin r) ℂ)
    (h2 : (reindex e e H).toBlocks₂₂.PosDef) (hs : (-schur (reindex e e H)).PosDef) (i : Fin (r + 1)) :
    0 < psgn q i * (lminor H i).re := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.FlagFibre.lminor_block r p q e he H h2.det_pos.ne'.isUnit
  have hr := he.card
  by_cases hi : (i : ℕ) ≤ q
  · rw [psgn_of_le' hi, one_mul, h₁ i ⟨i, by omega⟩ rfl]
    exact (Complex.pos_iff.1 (lminor_pos_of_posDef h2 _)).1
  · have hi2 := i.2
    obtain ⟨k, hk⟩ : ∃ k : Fin (p + 1), (i : ℕ) = q + k := ⟨⟨i - q, by omega⟩, by simp only; omega⟩
    have h3 := mul_pos h2.det_pos (lminor_pos_of_posDef hs k)
    rw [lminor_neg'] at h3
    rw [h₂ i k hk, hk, psgn_add', ← Complex.re_ofReal_mul]
    have h4 := (Complex.pos_iff.1 h3).1
    convert h4 using 2
    push_cast
    ring

/- English proof (translation)
Introduce `r p q e he A hA y hy i`. Take `⟨w, rfl⟩` from `glue_surjective he y`. Rewrite `hy` using `[base_glue he]`. Establish `hy' : (1 - (toMat w.1)ᴴ * toMat w.1).PosDef` using `hy`. Establish `hinj : ∀ {m : ℕ} (u : Low m → ℂ), Function.Injective (uni u).mulVec` using `fun u => mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by rw [det_uni]; exact isUnit_one))`.

Use `set Z := toMat w.1 with hZ`. Use `set a := uni w.2.2 with ha`. Use `set b := uni w.2.1 with hb`. Establish `hH : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) = fromBlocks (-(aᴴ * a)) (-(aᴴ * Z * b)) (-(aᴴ * Z * b))ᴴ (bᴴ * (1 - Zᴴ * Z) * b)`. Establish `: reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) = (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w))`.

Simplify using `only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]`. Rewrite using `[this, reindex_uni_glue he, hA, Jpq, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Use `congr 1`. Simplify using `[ha]`. Simplify using `[ha, hb, hZ, Matrix.mul_assoc]`.

Simplify using `[ha, hb, hZ, Matrix.mul_assoc]`. Simplify using `[hb, hZ, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_neg_add]`. Establish `h2 : (bᴴ * (1 - Zᴴ * Z) * b).PosDef` using `hy'.conjTranspose_mul_mul_same (hinj _)`. Use `signs_of_blocks he _ ?_ ?_ i` and prove the remaining obligations. Rewrite using `[hH, toBlocks_fromBlocks₂₂]`.

Conclude with `h2`. Rewrite using `[hH, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, neg_sub, sub_neg_eq_add, add_comm]`. Use `PosDef.add_posSemidef ?_ (h2.inv.posSemidef.mul_mul_conjTranspose_same _)` and prove the remaining obligations. Simplify using `using (PosDef.one (n := Fin p) (R := ℂ)).conjTranspose_mul_mul_same (hinj w.2.2)`.
-/
theorem signs_over_dom : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ),
    reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q →
    ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  intro r p q e he A hA y hy i
  obtain ⟨w, rfl⟩ := glue_surjective he y
  rw [base_glue he] at hy
  have hy' : (1 - (toMat w.1)ᴴ * toMat w.1).PosDef := hy
  have hinj : ∀ {m : ℕ} (u : Low m → ℂ), Function.Injective (uni u).mulVec := fun u =>
    mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by rw [det_uni]; exact isUnit_one))
  set Z := toMat w.1 with hZ
  set a := uni w.2.2 with ha
  set b := uni w.2.1 with hb
  have hH : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      fromBlocks (-(aᴴ * a)) (-(aᴴ * Z * b)) (-(aᴴ * Z * b))ᴴ (bᴴ * (1 - Zᴴ * Z) * b) := by
    have : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
        (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
      simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [this, reindex_uni_glue he, hA, Jpq, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply]
    congr 1
    · simp [ha]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [hb, hZ, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_neg_add]
  have h2 : (bᴴ * (1 - Zᴴ * Z) * b).PosDef := hy'.conjTranspose_mul_mul_same (hinj _)
  refine signs_of_blocks he _ ?_ ?_ i
  · rw [hH, toBlocks_fromBlocks₂₂]; exact h2
  · rw [hH, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      neg_sub, sub_neg_eq_add, add_comm]
    refine PosDef.add_posSemidef ?_ (h2.inv.posSemidef.mul_mul_conjTranspose_same _)
    simpa using (PosDef.one (n := Fin p) (R := ℂ)).conjTranspose_mul_mul_same (hinj w.2.2)

end GlobalTheory.FlagFibre
