import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

namespace GlobalTheory.DefDblCompact

/- English proof (translation)
Establish `h1 : Commute M (blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ))`. Break down `hθ with rfl | rfl` into its components or cases. Conclude with `h`. Establish `e : blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ) = -blkMat finSumFinEquiv (-1 : Matrix (Fin n) (Fin n) ℂ) (- -1 : Matrix (Fin n) (Fin n) ℂ)`. Apply `submatrix_inj finSumFinEquiv` to reduce the goal to its premises.

Rewrite using `[Matrix.submatrix_neg]`. Simplify using `[submatrix_blkMat, Matrix.fromBlocks_neg]`. Rewrite using `[e]`. Conclude with `h.neg_right`. Establish `h2` using `congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) h1.eq`.

Simplify using `only [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv, submatrix_blkMat] at h2`. Use `set N := M.submatrix finSumFinEquiv finSumFinEquiv with hN`. Rewrite `h2` using `[← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]`. Take `⟨-, h12, h21, -⟩` from `h2`. Establish `e1` using `congrFun (congrFun h12 a) b`.

Establish `e2` using `congrFun (congrFun h21 a) b`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, Matrix.neg_apply, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.of_apply, hN, Matrix.submatrix_apply] at e1 e2`. Conclude with `⟨by linear_combination (-1 / 2 : ℂ) * e1, by linear_combination (1 / 2 : ℂ) * e2⟩`.
-/
theorem offDiag_eq_zero {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) ℂ} {θ : Matrix (Fin n) (Fin n) ℂ}
    (hθ : θ = 1 ∨ θ = -1) (h : Commute M (blkMat finSumFinEquiv θ (-θ))) (a b : Fin n) :
    M (finSumFinEquiv (.inl a)) (finSumFinEquiv (.inr b)) = 0 ∧
      M (finSumFinEquiv (.inr a)) (finSumFinEquiv (.inl b)) = 0 := by
  have h1 : Commute M (blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rcases hθ with rfl | rfl
    · exact h
    · have e : blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) ℂ) (-1 : Matrix (Fin n) (Fin n) ℂ) =
          -blkMat finSumFinEquiv (-1 : Matrix (Fin n) (Fin n) ℂ) (- -1 : Matrix (Fin n) (Fin n) ℂ) := by
        apply submatrix_inj finSumFinEquiv
        rw [Matrix.submatrix_neg]
        simp [submatrix_blkMat, Matrix.fromBlocks_neg]
      rw [e]; exact h.neg_right
  have h2 := congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) h1.eq
  simp only [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv, submatrix_blkMat] at h2
  set N := M.submatrix finSumFinEquiv finSumFinEquiv with hN
  rw [← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at h2
  obtain ⟨-, h12, h21, -⟩ := h2
  have e1 := congrFun (congrFun h12 a) b
  have e2 := congrFun (congrFun h21 a) b
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, zero_add,
    add_zero, Matrix.neg_apply, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.of_apply, hN, Matrix.submatrix_apply] at e1 e2
  exact ⟨by linear_combination (-1 / 2 : ℂ) * e1, by linear_combination (1 / 2 : ℂ) * e2⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n r s' X hX hmin X₂ i K₂ hD k hk`. Establish `hθ : ∀ w, X.θ w = 1 ∨ X.θ w = -1` using `fun w => by`. Break down `Nat.min_eq_zero_iff.1 hmin with rfl | rfl` into its components or cases. Conclude with `Or.inr (GlobalTheory.DefiniteLevel.eq_neg_one_of_hasSig (hX.sig w) (hX.cartan w))`. Conclude with `Or.inl (GlobalTheory.DefiniteCartan.eq_one_of_hasSig (hX.sig w) (hX.cartan w))`.

Establish `hat : ∀ p q, At (evI F) ((mat k - 1) p q)` using `fun p q u hu => by`. Use `congrFun (congrFun (hk.1 u hu) p) q` as an intermediate fact. Simplify using `using this`. Establish `hoff : ∀ p q, p ≠ q → (∀ w, piInf (B.emb w) (mat k p q) = 0) → mat k p q = 0` using `fun p q hpq h0 => by`. Establish `h1` using `hat p q`.

Rewrite `h1` using `[Matrix.sub_apply, Matrix.one_apply_ne hpq, sub_zero]`. Conclude with `GlobalTheory.RealLift.OneParam.eq_zero_of_at hB.cm B.emb h1 h0`. Establish `hc : ∀ w a b, _` using `fun w => offDiag_eq_zero (hθ w) (hD.maj w ▸ hk.2 w)`. Use `set A := ((mat k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ with hA`. Use `set D := ((mat k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ with hDd`.

Establish `hblk : mat k = blkMat finSumFinEquiv A D`. Apply `submatrix_inj finSumFinEquiv` to reduce the goal to its premises. Rewrite using `[submatrix_blkMat, ← Matrix.fromBlocks_toBlocks ((mat k).submatrix finSumFinEquiv finSumFinEquiv)]`. Use `congr 1`. Use extensionality with `a b`.

Conclude with `hoff _ _ (fun h => by simpa using finSumFinEquiv.injective h) fun w => (hc w a b).1`. Use extensionality with `a b`. Conclude with `hoff _ _ (fun h => by simpa using finSumFinEquiv.injective h) fun w => (hc w a b).2`. Establish `hdet : IsUnit (A.det * D.det)`. Rewrite using `[← det_blkMat finSumFinEquiv, ← hblk]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 k.1.isUnit`. Take `⟨a, ha⟩` from `(Matrix.isUnit_iff_isUnit_det A).2 (isUnit_of_mul_isUnit_left hdet)`. Take `⟨d, hd⟩` from `(Matrix.isUnit_iff_isUnit_det D).2 (isUnit_of_mul_isUnit_right hdet)`. Establish `hkv : k.1 = blkGL finSumFinEquiv (a, d)` using `Units.ext (by rw [val_blkGL, ha, hd]; exact hblk)`. Establish `hU` using `(GlobalTheory.DefDoubling.blkGL_mem_UG σ X.J (x := a) (y := d)).1 (by rw [← hkv, ← hD.gram]; exact k.2)`.

Establish `hcm : ∀ w (M : Matrix (Fin n) (Fin n) ℂ), Commute M (X.θ w)` using `fun w M => by`. Apply the tactic sequence `rcases hθ w with h | h <;> rw [h]`. Conclude with `Commute.one_right _`. Conclude with `Commute.neg_one_right _`. Use `⟨⟨a, hU.1⟩, ⟨fun u hu => ?_, fun w => hcm w _⟩, ⟨d, hU.2⟩, ⟨fun u hu => ?_, fun w => hcm w _⟩, ?_⟩` and prove the remaining obligations.

Use `show u • (a.1 - 1) = 0`. Use extensionality with `p q`. Use `hat (finSumFinEquiv (.inl p)) (finSumFinEquiv (.inl q)) u hu` as an intermediate fact. Rewrite using `[ha]`. Simplify `this` using `[hA, Matrix.toBlocks₁₁, Matrix.one_apply, -finSumFinEquiv_apply_left]`.

Use `show u • (d.1 - 1) = 0`. Use extensionality with `p q`. Use `hat (finSumFinEquiv (.inr p)) (finSumFinEquiv (.inr q)) u hu` as an intermediate fact. Rewrite using `[hd]`. Simplify `this` using `[hDd, Matrix.toBlocks₂₂, Matrix.one_apply, -finSumFinEquiv_apply_right]`.

Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mat k = mat (i _)`. Rewrite using `[hD.emb, hblk, ← ha, ← hd]`. Both sides reduce to the same expression.
-/
theorem exists_blocks_of_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' → min r s' = 0 →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ k ∈ KInf σ X₂ B.emb, ∃ k₁ ∈ KInf σ X B.emb, ∃ k₂ ∈ KInf σ X B.emb, k = i (k₁, k₂) := by
  intro F E _ _ _ _ _ σ B hB n r s' X hX hmin X₂ i K₂ hD k hk
  have hθ : ∀ w, X.θ w = 1 ∨ X.θ w = -1 := fun w => by
    rcases Nat.min_eq_zero_iff.1 hmin with rfl | rfl
    · exact Or.inr (GlobalTheory.DefiniteLevel.eq_neg_one_of_hasSig (hX.sig w) (hX.cartan w))
    · exact Or.inl (GlobalTheory.DefiniteCartan.eq_one_of_hasSig (hX.sig w) (hX.cartan w))
  have hat : ∀ p q, At (evI F) ((mat k - 1) p q) := fun p q u hu => by
    have := congrFun (congrFun (hk.1 u hu) p) q
    simpa using this
  have hoff : ∀ p q, p ≠ q → (∀ w, piInf (B.emb w) (mat k p q) = 0) → mat k p q = 0 := fun p q hpq h0 => by
    have h1 := hat p q
    rw [Matrix.sub_apply, Matrix.one_apply_ne hpq, sub_zero] at h1
    exact GlobalTheory.RealLift.OneParam.eq_zero_of_at hB.cm B.emb h1 h0
  have hc : ∀ w a b, _ := fun w => offDiag_eq_zero (hθ w) (hD.maj w ▸ hk.2 w)
  set A := ((mat k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ with hA
  set D := ((mat k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ with hDd
  have hblk : mat k = blkMat finSumFinEquiv A D := by
    apply submatrix_inj finSumFinEquiv
    rw [submatrix_blkMat, ← Matrix.fromBlocks_toBlocks ((mat k).submatrix finSumFinEquiv finSumFinEquiv)]
    congr 1
    · ext a b
      exact hoff _ _ (fun h => by simpa using finSumFinEquiv.injective h) fun w => (hc w a b).1
    · ext a b
      exact hoff _ _ (fun h => by simpa using finSumFinEquiv.injective h) fun w => (hc w a b).2
  have hdet : IsUnit (A.det * D.det) := by
    rw [← det_blkMat finSumFinEquiv, ← hblk]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.1.isUnit
  obtain ⟨a, ha⟩ := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_of_mul_isUnit_left hdet)
  obtain ⟨d, hd⟩ := (Matrix.isUnit_iff_isUnit_det D).2 (isUnit_of_mul_isUnit_right hdet)
  have hkv : k.1 = blkGL finSumFinEquiv (a, d) := Units.ext (by rw [val_blkGL, ha, hd]; exact hblk)
  have hU := (GlobalTheory.DefDoubling.blkGL_mem_UG σ X.J (x := a) (y := d)).1 (by rw [← hkv, ← hD.gram]; exact k.2)
  have hcm : ∀ w (M : Matrix (Fin n) (Fin n) ℂ), Commute M (X.θ w) := fun w M => by
    rcases hθ w with h | h <;> rw [h]
    · exact Commute.one_right _
    · exact Commute.neg_one_right _
  refine ⟨⟨a, hU.1⟩, ⟨fun u hu => ?_, fun w => hcm w _⟩, ⟨d, hU.2⟩, ⟨fun u hu => ?_, fun w => hcm w _⟩, ?_⟩
  · show u • (a.1 - 1) = 0
    ext p q
    have := hat (finSumFinEquiv (.inl p)) (finSumFinEquiv (.inl q)) u hu
    rw [ha]
    simpa [hA, Matrix.toBlocks₁₁, Matrix.one_apply, -finSumFinEquiv_apply_left] using this
  · show u • (d.1 - 1) = 0
    ext p q
    have := hat (finSumFinEquiv (.inr p)) (finSumFinEquiv (.inr q)) u hu
    rw [hd]
    simpa [hDd, Matrix.toBlocks₂₂, Matrix.one_apply, -finSumFinEquiv_apply_right] using this
  · refine Subtype.ext (Units.ext ?_)
    change mat k = mat (i _)
    rw [hD.emb, hblk, ← ha, ← hd]
    rfl

end GlobalTheory.DefDblCompact
