import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
private theorem gram_eq_lemma (τ' : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Y = Yᵀ * G.map τ' * Y.map (starRingEnd ℂ) := by
  ext a c
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Use extensionality with `a b`. Establish `hv : ∀ c : Fin r, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single c (1 : E) : Fin r → E) = fun p => (γ : Matrix (Fin r) (Fin r) E) p c`. Introduce `c`. Use extensionality with `p`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Establish `hcc : ∀ q : Fin r, ReciprocityTheory.ChartRestriction.G.FD.cc ((Pi.single b (1 : E) : Fin r → E) q) = (Pi.single b (1 : E) : Fin r → E) q`. Introduce `q`. Distinguish the cases in `hq : q = b`. Substitute `hq` using the available equality. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.cc]`.

Simplify using `[Pi.single_apply, hq, ReciprocityTheory.ChartRestriction.G.FD.cc]`. Establish `h` using `hγ (Pi.single a 1) (Pi.single b 1)`. Rewrite `h` using `[hv, hv]`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.herm at h`. Simplify using `only [hcc] at h`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `h.trans (by simp [Pi.single_apply])`.
-/
private theorem transpose_mul_mul_map_cc_eq_of_herm_mulVec (G : Matrix (Fin r) (Fin r) E) (γ : GL (Fin r) E)
    (hγ : ∀ v w : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc = G := by
  ext a b
  have hv : ∀ c : Fin r, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single c (1 : E) : Fin r → E) =
      fun p => (γ : Matrix (Fin r) (Fin r) E) p c := by
    intro c
    ext p
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcc : ∀ q : Fin r, ReciprocityTheory.ChartRestriction.G.FD.cc ((Pi.single b (1 : E) : Fin r → E) q) =
      (Pi.single b (1 : E) : Fin r → E) q := by
    intro q
    by_cases hq : q = b
    · subst hq
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Pi.single_apply, hq, ReciprocityTheory.ChartRestriction.G.FD.cc]
  have h := hγ (Pi.single a 1) (Pi.single b 1)
  rw [hv, hv] at h
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h
  simp only [hcc] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h.trans (by simp [Pi.single_apply])

/- English proof (translation)
Introduce `τ`. Take `⟨hxd, hxm⟩` from `hx τ`. Establish `hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ` using `rfl`. Establish `hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1`. Establish `h0` using `transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1`.

Establish `hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`. Conclude with `(ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm`. Rewrite using `[hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]`.

Establish `hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) = X.Gm.map τ.1 * Y`. Introduce `Y`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hmat, Matrix.det_mul]`.

Use `mul_ne_zero ?_ hxd` and prove the remaining obligations. Establish `hdet : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det` using `(RingHom.map_det _ _).symm`. Rewrite using `[hdet]`. Conclude with `(map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero`. Establish `hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) = ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ)`.

Rewrite using `[hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hU']`. Establish `hd : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (lact γ x) τ i = ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.dmin`.

Rewrite using `[hg]`. Rewrite using `[hd]`. Conclude with `hxm i`.
-/
private theorem lact_mem_dom' {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  intro τ
  obtain ⟨hxd, hxm⟩ := hx τ
  have hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl
  have hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    have h0 := transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1
    have hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
        ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1 := by
      ext a b
      simp only [Matrix.map_apply]
      exact (ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm
    rw [hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) =
      X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat, Matrix.det_mul]
    refine mul_ne_zero ?_ hxd
    have hdet : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
      (RingHom.map_det _ _).symm
    rw [hdet]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
      rw [hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [hU']
    have hd : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (lact γ x) τ i = ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.dmin
      rw [hg]
    rw [hd]
    exact hxm i

/- English proof (translation)
Establish `hout : ∀ d : Fin r, d ∉ Set.range (Fin.castLE h) → i ≤ (d : ℕ)`. Introduce `d hd`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `hd (Set.mem_range.2 ⟨⟨d, hlt⟩, Fin.ext rfl⟩)`.

Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `intro d hd try dsimp only`.

Establish `hlt : Fin.castLE h c < d` using `by show (c : ℕ) < d`. Conclude with `lt_of_lt_of_le c.isLt (hout d hd)`. Rewrite using `[hB d (Fin.castLE h c) hlt, map_zero, mul_zero]`. Apply the tactic sequence `intro d' try dsimp only`. Use `congr 1`.

Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `intro k hk try dsimp only`. Establish `hlt : Fin.castLE h a < k` using `by show (a : ℕ) < k`. Conclude with `lt_of_lt_of_le a.isLt (hout k hk)`. Rewrite using `[hB k (Fin.castLE h a) hlt, zero_mul]`.

Introduce `k'`. Both sides reduce to the same expression.
-/
private theorem submatrix_castLE_transpose_mul_mul_map_conj_of_upper {i : ℕ} (h : i ≤ r) (B M : Matrix (Fin r) (Fin r) ℂ)
    (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    (Bᵀ * M * B.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * M.submatrix (Fin.castLE h) (Fin.castLE h) *
        (B.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  have hout : ∀ d : Fin r, d ∉ Set.range (Fin.castLE h) → i ≤ (d : ℕ) := by
    intro d hd
    by_contra hlt
    push_neg at hlt
    exact hd (Set.mem_range.2 ⟨⟨d, hlt⟩, Fin.ext rfl⟩)
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro d hd
    try dsimp only
    have hlt : Fin.castLE h c < d := by
      show (c : ℕ) < d
      exact lt_of_lt_of_le c.isLt (hout d hd)
    rw [hB d (Fin.castLE h c) hlt, map_zero, mul_zero]
  · intro d'
    try dsimp only
    congr 1
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro k hk
      try dsimp only
      have hlt : Fin.castLE h a < k := by
        show (a : ℕ) < k
        exact lt_of_lt_of_le a.isLt (hout k hk)
      rw [hB k (Fin.castLE h a) hlt, zero_mul]
    · intro k'
      rfl

/- English proof (translation)
Establish `hi : (i : ℕ) ≤ r` using `Nat.le_of_lt_succ i.isLt`. Establish `hBs : (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det ≠ 0`. Rewrite using `[Matrix.det_of_upperTriangular (M := Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)) (fun a c hca => hB (Fin.castLE hi a) (Fin.castLE hi c) hca)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hdiag _`. Use `⟨Complex.normSq (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det, Complex.normSq_pos.2 hBs, ?_⟩` and prove the remaining obligations.

Establish `hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm) = Bmᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm * Bm.map (starRingEnd ℂ)`. Rewrite using `[gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hc : ((Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).map (starRingEnd ℂ)).det = starRingEnd ℂ (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det` using `(RingHom.map_det _ _).symm`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.lminor`.

Rewrite using `[hg, submatrix_castLE_transpose_mul_mul_map_conj_of_upper hi _ _ hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc, ← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_pos_lminor_gram_mul_eq (τ' : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Xm Bm : Matrix (Fin r) (Fin r) ℂ) (hB : ∀ a c : Fin r, c < a → Bm a c = 0)
    (hdiag : ∀ a, Bm a a ≠ 0) (i : Fin (r + 1)) :
    ∃ t : ℝ, 0 < t ∧ ReciprocityTheory.ChartRestriction.G.FD.lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm)) i =
      (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm) i := by
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hBs : (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (M := Bm.submatrix (Fin.castLE hi) (Fin.castLE hi))
      (fun a c hca => hB (Fin.castLE hi a) (Fin.castLE hi c) hca)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hdiag _
  refine ⟨Complex.normSq (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det,
    Complex.normSq_pos.2 hBs, ?_⟩
  have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm) =
      Bmᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm * Bm.map (starRingEnd ℂ) := by
    rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hc : ((Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det :=
    (RingHom.map_det _ _).symm
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [hg, submatrix_castLE_transpose_mul_mul_map_conj_of_upper hi _ _ hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc,
    ← Complex.mul_conj]
  ring

/- English proof (translation)
Introduce `τ`. Take `⟨hxd, hxm⟩` from `hx τ`. Take `⟨hbd, hbt⟩` from `hb τ`. Establish `hB : ∀ a c : Fin r, c < a → ReciprocityTheory.ChartRestriction.G.FD.mat b τ a c = 0` using `hbt`. Establish `hdiag : ∀ a : Fin r, ReciprocityTheory.ChartRestriction.G.FD.mat b τ a a ≠ 0`.

Establish `h1` using `Matrix.det_of_upperTriangular (M := ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB`. Rewrite `hbd` using `[h1]`. Conclude with `fun a => Finset.prod_ne_zero_iff.1 hbd a (Finset.mem_univ a)`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `show (ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0`.

Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hxd hbd`. Take `⟨t, ht, he⟩` from `exists_pos_lminor_gram_mul_eq τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB hdiag i`. Establish `he' : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (rmul x b) τ i = (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i` using `he`. Rewrite using `[he', Complex.re_ofReal_mul, mul_left_comm]`.

Conclude with `mul_pos ht (hxm i)`.
-/
private theorem rmul_mem_dom_of_mem_dom {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := by
  intro τ
  obtain ⟨hxd, hxm⟩ := hx τ
  obtain ⟨hbd, hbt⟩ := hb τ
  have hB : ∀ a c : Fin r, c < a → ReciprocityTheory.ChartRestriction.G.FD.mat b τ a c = 0 := hbt
  have hdiag : ∀ a : Fin r, ReciprocityTheory.ChartRestriction.G.FD.mat b τ a a ≠ 0 := by
    have h1 := Matrix.det_of_upperTriangular (M := ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB
    rw [h1] at hbd
    exact fun a => Finset.prod_ne_zero_iff.1 hbd a (Finset.mem_univ a)
  refine ⟨?_, fun i => ?_⟩
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hxd hbd
  · obtain ⟨t, ht, he⟩ := exists_pos_lminor_gram_mul_eq τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
      (ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB hdiag i
    have he' : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (rmul x b) τ i =
        (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := he
    rw [he', Complex.re_ofReal_mul, mul_left_comm]
    exact mul_pos ht (hxm i)

/- English proof (translation)
Introduce `τ`. Take `⟨hd, ht⟩` from `hb τ`. Take `⟨hd', ht'⟩` from `hb' τ`. Use `⟨?_, fun a c hca => ?_⟩` and prove the remaining obligations. Use `show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ).det ≠ 0`.

Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hd hd'`. Use `show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ) a c = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge k a with hk | hk` into its components or cases. Rewrite using `[show ReciprocityTheory.ChartRestriction.G.FD.mat b τ a k = 0 from ht a k hk, zero_mul]`. Rewrite using `[show ReciprocityTheory.ChartRestriction.G.FD.mat b' τ k c = 0 from ht' k c (lt_of_lt_of_le hca hk), mul_zero]`.
-/
private theorem mem_bor_rmul {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  intro τ
  obtain ⟨hd, ht⟩ := hb τ
  obtain ⟨hd', ht'⟩ := hb' τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hd hd'
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ) a c = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hk | hk
    · rw [show ReciprocityTheory.ChartRestriction.G.FD.mat b τ a k = 0 from ht a k hk, zero_mul]
    · rw [show ReciprocityTheory.ChartRestriction.G.FD.mat b' τ k c = 0 from ht' k c (lt_of_lt_of_le hca hk), mul_zero]

/- English proof (translation)
Introduce `τ`. Take `⟨hd, ht⟩` from `hb τ`. Use `⟨?_, fun a c hca => ?_⟩` and prove the remaining obligations. Use `show ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹).det ≠ 0 first`. Consider the case `exact (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hd)).ne_zero`.

Consider the case `(rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hd)`. Use `haveI := (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).invertibleOfIsUnitDet (Ne.isUnit hd)`. Establish `hT : (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id` using `fun a c h => ht a c h`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hT hca`.
-/
private theorem FD_mat_inv_mem_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  obtain ⟨hd, ht⟩ := hb τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹).det ≠ 0
    first
      | exact (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hd)).ne_zero
      | (rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hd)
  · haveI := (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    have hT : (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := fun a c h => ht a c h
    exact Matrix.blockTriangular_inv_of_blockTriangular hT hca

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Conclude with `Matrix.mul_assoc (ReciprocityTheory.ChartRestriction.G.FD.mat u τ) (ReciprocityTheory.ChartRestriction.G.FD.mat v τ) (ReciprocityTheory.ChartRestriction.G.FD.mat w τ)`.
-/
private theorem rmul_assoc_frame (u v w : Frame X.Ψ r) : rmul (rmul u v) w = rmul u (rmul v w) := by
  funext τ
  exact Matrix.mul_assoc (ReciprocityTheory.ChartRestriction.G.FD.mat u τ) (ReciprocityTheory.ChartRestriction.G.FD.mat v τ) (ReciprocityTheory.ChartRestriction.G.FD.mat w τ)

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ * (ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ = y τ`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit (hb τ).1)]`. Both sides reduce to the same expression.
-/
private theorem rmul_rmul_inv_mat_eq_self {y b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (rmul y b) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ * (ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ = y τ
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit (hb τ).1)]
  rfl

/- English proof (translation)
Establish `hyb : rmul y b ∈ X.dom` using `rmul_mem_dom_of_mem_dom hb hy`. Distinguish the cases in `hΔ : D.Δ y = 0`. Establish `hn : ¬ y ∈ T D FF` using `fun h => (show _ ∧ _ ∧ _ from h).2.1 hΔ`. Use `iff_of_false ?_ hn` and prove the remaining obligations. Introduce `h`.

Establish `hΔ' : D.Δ (rmul y b) ≠ 0` using `(show _ ∧ _ ∧ _ from h).2.1`. Take `⟨hz, hb', he⟩` from `D.split _ hyb hΔ'`. Establish `hy' : y = rmul (cpt X x0 (D.zOf (rmul y b))) (rmul (D.bOf (rmul y b)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `(D.uniq _ hz _ (mem_bor_rmul hb' (FD_mat_inv_mem_bor hb))).1`.

Rewrite `h2` using `[← hy']`. Conclude with `h2 hΔ`. Take `⟨hz, hb0, he⟩` from `D.split y hy hΔ`. Establish `hyb' : rmul y b = rmul (cpt X x0 (D.zOf y)) (rmul (D.bOf y) b)` using `(congrArg (fun w => rmul w b) he).trans (rmul_assoc_frame _ _ _)`. Take `⟨hΔ1, hz1, -⟩` from `D.uniq _ hz _ (mem_bor_rmul hb0 hb)`.

Rewrite `hΔ1`, `hz1` using `[← hyb']`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hF : D.zOf (rmul y b) ∈ FF` using `(show _ ∧ _ ∧ _ from h).2.2`. Rewrite `hF` using `[hz1]`.

Use `show _ ∧ _ ∧ _`. Conclude with `⟨hy, hΔ, hF⟩`. Introduce `h`. Establish `hF : D.zOf y ∈ FF` using `(show _ ∧ _ ∧ _ from h).2.2`. Use `show _ ∧ _ ∧ _`.

Use `⟨hyb, hΔ1, ?_⟩` and prove the remaining obligations. Rewrite using `[hz1]`. Conclude with `hF`.
-/
private theorem rmul_mem_T_iff {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul y b ∈ T D FF ↔ y ∈ T D FF := by
  have hyb : rmul y b ∈ X.dom := rmul_mem_dom_of_mem_dom hb hy
  by_cases hΔ : D.Δ y = 0
  · have hn : ¬ y ∈ T D FF := fun h => (show _ ∧ _ ∧ _ from h).2.1 hΔ
    refine iff_of_false ?_ hn
    intro h
    have hΔ' : D.Δ (rmul y b) ≠ 0 := (show _ ∧ _ ∧ _ from h).2.1
    obtain ⟨hz, hb', he⟩ := D.split _ hyb hΔ'
    have hy' : y = rmul (cpt X x0 (D.zOf (rmul y b)))
        (rmul (D.bOf (rmul y b)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
      calc y = rmul (rmul y b) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := (rmul_rmul_inv_mat_eq_self hb).symm
        _ = rmul (rmul (cpt X x0 (D.zOf (rmul y b))) (D.bOf (rmul y b))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) :=
          congrArg (fun w => rmul w (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) he
        _ = _ := rmul_assoc_frame _ _ _
    have h2 := (D.uniq _ hz _ (mem_bor_rmul hb' (FD_mat_inv_mem_bor hb))).1
    rw [← hy'] at h2
    exact h2 hΔ
  · obtain ⟨hz, hb0, he⟩ := D.split y hy hΔ
    have hyb' : rmul y b = rmul (cpt X x0 (D.zOf y)) (rmul (D.bOf y) b) :=
      (congrArg (fun w => rmul w b) he).trans (rmul_assoc_frame _ _ _)
    obtain ⟨hΔ1, hz1, -⟩ := D.uniq _ hz _ (mem_bor_rmul hb0 hb)
    rw [← hyb'] at hΔ1 hz1
    constructor
    · intro h
      have hF : D.zOf (rmul y b) ∈ FF := (show _ ∧ _ ∧ _ from h).2.2
      rw [hz1] at hF
      show _ ∧ _ ∧ _
      exact ⟨hy, hΔ, hF⟩
    · intro h
      have hF : D.zOf y ∈ FF := (show _ ∧ _ ∧ _ from h).2.2
      show _ ∧ _ ∧ _
      refine ⟨hyb, hΔ1, ?_⟩
      rw [hz1]
      exact hF

/- English proof (translation)
Establish `hγi : γ⁻¹ ∈ X.Γ` using `X.Γ.inv_mem hγ`. Establish `hy : lact γ⁻¹ x ∈ X.dom` using `lact_mem_dom' hγi hx`. Establish `hlr : lact γ⁻¹ (rmul x b) = rmul (lact γ⁻¹ x) b`. Use function extensionality and compare the values at `τ`. Simplify using `only [lact, rmul, mat]`.

Conclude with `(Matrix.mul_assoc (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ)) (Matrix.of (b τ))).symm`. Rewrite using `[hlr]`. Distinguish the cases in `h : lact γ⁻¹ x ∈ T D FF`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem ((rmul_mem_T_iff D FF hy hb).2 h)]`. Both sides reduce to the same expression.

Use `first`. Consider the case `rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]`. Consider the case `rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]`.
-/
theorem ind_rmul {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) {M : Type*} [One M] [Zero M] :
    (T D FF).indicator (1 : Frame X.Ψ r → M) (lact γ⁻¹ (rmul x b)) =
      (T D FF).indicator (1 : Frame X.Ψ r → M) (lact γ⁻¹ x) := by
  have hγi : γ⁻¹ ∈ X.Γ := X.Γ.inv_mem hγ
  have hy : lact γ⁻¹ x ∈ X.dom := lact_mem_dom' hγi hx
  have hlr : lact γ⁻¹ (rmul x b) = rmul (lact γ⁻¹ x) b := by
    funext τ
    dsimp only [lact, rmul, mat]
    exact (Matrix.mul_assoc (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1)
      (Matrix.of (x τ)) (Matrix.of (b τ))).symm
  rw [hlr]
  by_cases h : lact γ⁻¹ x ∈ T D FF
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((rmul_mem_T_iff D FF hy hb).2 h)]
    rfl
  · first
      | rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]
      | rw [Set.indicator_of_not_mem h,
          Set.indicator_of_not_mem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]

/- English proof (translation)
Establish `hb : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r`. Use `fun τ => ⟨?_, fun a c hca => ?_⟩` and prove the remaining obligations. Use `show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0`. Simplify using the standard rewrite rules. Conclude with `Matrix.one_apply_ne hca.ne'`.

Establish `h1 : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = cpt X x0 z`. Use function extensionality and compare the values at `τ`. Use `first`. Consider the case `exact Matrix.mul_one _`. Consider the case `simp [ReciprocityTheory.ChartRestriction.G.FD.rmul, ReciprocityTheory.ChartRestriction.G.FD.mat]`.

Take `⟨hΔ, hzz, -⟩` from `D.uniq z hz _ hb`. Rewrite `hΔ`, `hzz` using `[h1]`. Establish `hiff : cpt X x0 z ∈ T D FF ↔ z ∈ FF`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h' : D.zOf (cpt X x0 z) ∈ FF` using `h.2.2`. Rewrite `h'` using `[hzz]`. Conclude with `h'`. Introduce `h show _ ∧ _ ∧ _`. Use `⟨hz, hΔ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hzz]`. Conclude with `h`. Distinguish the cases in `hF : z ∈ FF`. Rewrite using `[Set.indicator_of_mem (hiff.2 hF), Set.indicator_of_mem hF]`. Both sides reduce to the same expression.

Use `first`. Consider the case `rw [Set.indicator_of_notMem (fun h => hF (hiff.1 h)), Set.indicator_of_notMem hF]`. Consider the case `rw [Set.indicator_of_not_mem (fun h => hF (hiff.1 h)), Set.indicator_of_not_mem hF]`.
-/
theorem ind_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) {M : Type*} [One M] [Zero M] :
    (T D FF).indicator (1 : Frame X.Ψ r → M) (cpt X x0 z) = FF.indicator 1 z := by
  have hb : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
    refine fun τ => ⟨?_, fun a c hca => ?_⟩
    · show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0
      simp
    · exact Matrix.one_apply_ne hca.ne'
  have h1 : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = cpt X x0 z := by
    funext τ
    first
      | exact Matrix.mul_one _
      | simp [ReciprocityTheory.ChartRestriction.G.FD.rmul, ReciprocityTheory.ChartRestriction.G.FD.mat]
  obtain ⟨hΔ, hzz, -⟩ := D.uniq z hz _ hb
  rw [h1] at hΔ hzz
  have hiff : cpt X x0 z ∈ T D FF ↔ z ∈ FF := by
    constructor
    · intro h
      have h' : D.zOf (cpt X x0 z) ∈ FF := h.2.2
      rw [hzz] at h'
      exact h'
    · intro h
      show _ ∧ _ ∧ _
      refine ⟨hz, hΔ, ?_⟩
      rw [hzz]
      exact h
  by_cases hF : z ∈ FF
  · rw [Set.indicator_of_mem (hiff.2 hF), Set.indicator_of_mem hF]
    rfl
  · first
      | rw [Set.indicator_of_notMem (fun h => hF (hiff.1 h)), Set.indicator_of_notMem hF]
      | rw [Set.indicator_of_not_mem (fun h => hF (hiff.1 h)), Set.indicator_of_not_mem hF]

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ReciprocityTheory.ChartRestriction.G.FD.rmul ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat ReciprocityTheory.ChartRestriction.G.FD.mat`. Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Use `Continuous.matrix_mul continuous_const ?_` and prove the remaining obligations. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`.

Use `split_ifs`. Use `first`. Consider the case `fun_prop`. Consider the case `exact (EuclideanSpace.proj _).continuous`. Conclude with `continuous_const`.

Conclude with `continuous_const`.
-/
private theorem continuous_cpt_apply (y0 : Frame X.Ψ r) : Continuous fun z => cpt X y0 z := by
  unfold ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ReciprocityTheory.ChartRestriction.G.FD.rmul ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat
    ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  refine Continuous.matrix_mul continuous_const ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · first
      | fun_prop
      | exact (EuclideanSpace.proj _).continuous
  · exact continuous_const
  · exact continuous_const

/- English proof (translation)
Use `show rmul (lact γ y0) (nmat X z) = lact γ (rmul y0 (nmat X z))`. Use function extensionality and compare the values at `τ`. Simplify using `only [lact, rmul, mat]`. Conclude with `Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y0 τ)) (Matrix.of (nmat X z τ))`.
-/
private theorem cpt_lact_upper_bounds (γ : GL (Fin r) E) (y0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ y0) z = lact γ (cpt X y0 z) := by
  show rmul (lact γ y0) (nmat X z) = lact γ (rmul y0 (nmat X z))
  funext τ
  dsimp only [lact, rmul, mat]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y0 τ))
    (Matrix.of (nmat X z τ))

/- English proof (translation)
Establish `hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ` using `rfl`. Establish `hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1`. Establish `h0` using `transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1`. Establish `hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply]`. Conclude with `(ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm`. Rewrite using `[hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]`. Establish `hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) = X.Gm.map τ.1 * Y`. Introduce `Y`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]`. Rewrite using `[hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hU']`.
-/
private theorem gram_mat_lact_of_mem_Γ {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) =
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
  have hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl
  have hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    have h0 := transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1
    have hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
        ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1 := by
      ext a b
      simp only [Matrix.map_apply]
      exact (ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm
    rw [hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) =
      X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  rw [hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [hU']

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (y τ)) = y τ`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Both sides reduce to the same expression.
-/
private theorem lact_inv_apply_lact (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  funext τ
  show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (y τ)) = y τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col ReciprocityTheory.ChartRestriction.G.FD.mat`. Use `Continuous.matrix_det ?_` and prove the remaining obligations. Use `Continuous.matrix_submatrix ?_ _ _` and prove the remaining obligations. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`.

Use `continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_` and prove the remaining obligations. Use `Continuous.mul (Continuous.mul ?_ continuous_const) ?_` and prove the remaining obligations. Conclude with `(continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ))`. Conclude with `Complex.continuous_conj.comp ((continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ)))`.
-/
private theorem continuous_FD_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.gram
    ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col ReciprocityTheory.ChartRestriction.G.FD.mat
  refine Continuous.matrix_det ?_
  refine Continuous.matrix_submatrix ?_ _ _
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
  refine Continuous.mul (Continuous.mul ?_ continuous_const) ?_
  · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ))
  · exact Complex.continuous_conj.comp
      ((continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ)))

/- English proof (translation)
Use `show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re}`. Simplify using `only [Set.setOf_forall, Set.setOf_and]`. Use `isOpen_iInter_of_finite fun τ => ?_` and prove the remaining obligations. Use `IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations. Use `isOpen_ne_fun (Continuous.matrix_det ?_) continuous_const` and prove the remaining obligations.

Unfold `ReciprocityTheory.ChartRestriction.G.FD.mat`. Conclude with `continuous_apply τ`. Conclude with `isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (continuous_FD_dmin X τ i)))`.
-/
private theorem isOpen_dom_of_data (X : Data E r) : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · refine isOpen_ne_fun (Continuous.matrix_det ?_) continuous_const
    unfold ReciprocityTheory.ChartRestriction.G.FD.mat
    exact continuous_apply τ
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (continuous_FD_dmin X τ i)))

/- English proof (translation)
Establish `hOm : OmF X (lact γ y0) = OmF X y0`. Use extensionality with `z`. Use `show cpt X (lact γ y0) z ∈ X.dom ↔ cpt X y0 z ∈ X.dom`. Rewrite using `[cpt_lact_upper_bounds]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h2` using `lact_mem_dom' (X.Γ.inv_mem hγ) h`. Rewrite `h2` using `[lact_inv_apply_lact]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `lact_mem_dom' hγ h`.

Establish `hd : ∀ z, ReciprocityTheory.ChartRestriction.G.AR.Up.densF X (lact γ y0) z = ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y0 z`. Introduce `z`. Unfold `ReciprocityTheory.ChartRestriction.G.AR.Up.densF`. Rewrite using `[cpt_lact_upper_bounds]`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_mat_lact_of_mem_Γ hγ]`.

Unfold `ReciprocityTheory.ChartRestriction.G.AR.Up.muF`. Rewrite using `[hOm]`. Simplify using `only [hd]`.
-/
private theorem muF_lact_upper_bounds {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y0 : Frame X.Ψ r) :
    muF X (lact γ y0) = muF X y0 := by
  have hOm : OmF X (lact γ y0) = OmF X y0 := by
    ext z
    show cpt X (lact γ y0) z ∈ X.dom ↔ cpt X y0 z ∈ X.dom
    rw [cpt_lact_upper_bounds]
    constructor
    · intro h
      have h2 := lact_mem_dom' (X.Γ.inv_mem hγ) h
      rwa [lact_inv_apply_lact] at h2
    · intro h
      exact lact_mem_dom' hγ h
  have hd : ∀ z, ReciprocityTheory.ChartRestriction.G.AR.Up.densF X (lact γ y0) z = ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y0 z := by
    intro z
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.densF
    rw [cpt_lact_upper_bounds]
    simp only [ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_mat_lact_of_mem_Γ hγ]
  unfold ReciprocityTheory.ChartRestriction.G.AR.Up.muF
  rw [hOm]
  simp only [hd]

/- English proof (translation)
Introduce `τ`. Rewrite using `[gram_mat_lact_of_mem_Γ hγ]`. Conclude with `h τ`.
-/
private theorem isOrth_lact' {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y0 : Frame X.Ψ r} (h : IsOrth X y0) :
    IsOrth X (lact γ y0) := by
  intro τ
  rw [gram_mat_lact_of_mem_Γ hγ]
  exact h τ

/- English proof (translation)
Establish `hUo : IsOpen {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}` using `(isOpen_dom_of_data X).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)`. Establish `hpw : Measurable ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0)` using `D.hz.continuousOn.measurable_piecewise continuousOn_const hUo.measurableSet`. Establish `hT : T D FF = {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} ∩ ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) ⁻¹' FF`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨h1, h2, h3⟩` from `(show _ ∧ _ ∧ _ from h)`. Use `⟨⟨h1, h2⟩, ?_⟩` and prove the remaining obligations. Use `show ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)]`.

Conclude with `h3`. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Establish `h3' : ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF` using `h3`. Rewrite `h3'` using `[Set.piecewise_eq_of_mem _ _ _ (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)]`. Use `show _ ∧ _ ∧ _`.

Conclude with `⟨h1, h2, h3'⟩`. Rewrite using `[hT]`. Conclude with `hUo.measurableSet.inter (hpw hF)`.
-/
private theorem measurableSet_T (hF : MeasurableSet FF) : MeasurableSet (T D FF) := by
  classical
  have hUo : IsOpen {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} :=
    (isOpen_dom_of_data X).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hpw : Measurable ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) :=
    D.hz.continuousOn.measurable_piecewise continuousOn_const hUo.measurableSet
  have hT : T D FF = {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} ∩
      ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) ⁻¹' FF := by
    ext x
    constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ := (show _ ∧ _ ∧ _ from h)
      refine ⟨⟨h1, h2⟩, ?_⟩
      show ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF
      rw [Set.piecewise_eq_of_mem _ _ _
        (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)]
      exact h3
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h3' : ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF := h3
      rw [Set.piecewise_eq_of_mem _ _ _
        (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)] at h3'
      show _ ∧ _ ∧ _
      exact ⟨h1, h2, h3'⟩
  rw [hT]
  exact hUo.measurableSet.inter (hpw hF)

/- English proof (translation)
Use `Continuous.measurable ?_` and prove the remaining obligations. Unfold `lact ReciprocityTheory.ChartRestriction.G.FD.mat`. Conclude with `continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)`.
-/
private theorem measurable_lact (γ : GL (Fin r) E) : Measurable fun x : Frame X.Ψ r => lact γ x := by
  refine Continuous.measurable ?_
  unfold lact ReciprocityTheory.ChartRestriction.G.FD.mat
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)

/- English proof (translation)
Establish `hOm : MeasurableSet (OmF X y0)` using `((isOpen_dom_of_data X).preimage (continuous_cpt_apply y0)).measurableSet`. Establish `hac : muF X y0 ≪ volume.restrict (OmF X y0)`. Unfold `ReciprocityTheory.ChartRestriction.G.AR.Up.muF`. Conclude with `withDensity_absolutelyContinuous _ _`. Conclude with `hac.ae_le (ae_restrict_mem hOm)`.
-/
private theorem ae_mem_omF (y0 : Frame X.Ψ r) : ∀ᵐ z ∂muF X y0, z ∈ OmF X y0 := by
  have hOm : MeasurableSet (OmF X y0) :=
    ((isOpen_dom_of_data X).preimage (continuous_cpt_apply y0)).measurableSet
  have hac : muF X y0 ≪ volume.restrict (OmF X y0) := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.muF
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le (ae_restrict_mem hOm)

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `only [lact, mat]`. Rewrite using `[Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`. Apply the tactic sequence `try rfl`.
-/
private theorem lact_mul_upper_bounds (a b : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  dsimp only [lact, mat]
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  try rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `only [lact, rmul, mat]`. Conclude with `(Matrix.mul_assoc ((g : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y τ)) (Matrix.of (c τ))).symm`.
-/
private theorem lact_rmul_eq_rmul_lact (g : GL (Fin r) E) (y c : Frame X.Ψ r) :
    lact g (rmul y c) = rmul (lact g y) c := by
  funext τ
  dsimp only [lact, rmul, mat]
  exact (Matrix.mul_assoc ((g : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y τ))
    (Matrix.of (c τ))).symm

/- English proof (translation)
Take `⟨y1, hy1⟩ : ∃ y, y = lact γ1⁻¹ (cpt X x0 z)` from `⟨_, rfl⟩`. Take `⟨y2, hy2⟩ : ∃ y, y = lact γ2⁻¹ (cpt X x0 z)` from `⟨_, rfl⟩`. Rewrite `hT1` using `[← hy1]`. Rewrite `hT2` using `[← hy2]`. Take `⟨hd1, hΔ1, hF1⟩` from `(show _ ∧ _ ∧ _ from hT1)`.

Take `⟨hd2, hΔ2, hF2⟩` from `(show _ ∧ _ ∧ _ from hT2)`. Take `⟨hO1, hB1, he1⟩` from `D.split y1 hd1 hΔ1`. Take `⟨hO2, hB2, he2⟩` from `D.split y2 hd2 hΔ2`. Establish `hx1 : lact γ1 y1 = cpt X x0 z`. Establish `h` using `lact_inv_apply_lact γ1⁻¹ (cpt X x0 z)`.

Rewrite `h` using `[inv_inv]`. Rewrite using `[hy1]`. Conclude with `h`. Establish `hg : (γ2⁻¹ * γ1) ∈ X.Γ` using `X.Γ.mul_mem (X.Γ.inv_mem h2) h1`. Establish `hEq : cpt X x0 (D.zOf y2) = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hw : D.zOf y1 = D.zOf y2` using `hFF.2.2.1 _ hF1 _ hF2 _ hg _ (mem_bor_rmul hB1 (FD_mat_inv_mem_bor hB2)) hEq`. Establish `hB' : lact (γ2⁻¹ * γ1) y1 = y2` using `by rw [lact_mul_upper_bounds, hx1, hy2]`. Establish `hfree : lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `rw [lact_rmul_eq_rmul_lact]`. Consider the case `exact congrArg (fun w => rmul w _) (lact_rmul_eq_rmul_lact _ _ _).symm`. Use `_ = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1, hB', ← he2]`. Use `_ = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by`. Rewrite using `[← hw]`.

Conclude with `rmul_assoc_frame _ _ _`. Establish `h1'` using `X.Γ_free _ hg _ hO1 _ (mem_bor_rmul hB2 (FD_mat_inv_mem_bor hB1)) hfree`. Conclude with `(inv_mul_eq_one.1 h1').symm`.
-/
private theorem eq_of_lact_inv_cpt_mem_T (hFF : IsFundSet X x0 FF) {z : V (nd X)} (hz : z ∈ OmF X x0)
    {γ1 γ2 : GL (Fin r) E} (h1 : γ1 ∈ X.Γ) (h2 : γ2 ∈ X.Γ)
    (hT1 : lact γ1⁻¹ (cpt X x0 z) ∈ T D FF) (hT2 : lact γ2⁻¹ (cpt X x0 z) ∈ T D FF) : γ1 = γ2 := by
  obtain ⟨y1, hy1⟩ : ∃ y, y = lact γ1⁻¹ (cpt X x0 z) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y, y = lact γ2⁻¹ (cpt X x0 z) := ⟨_, rfl⟩
  rw [← hy1] at hT1
  rw [← hy2] at hT2
  obtain ⟨hd1, hΔ1, hF1⟩ := (show _ ∧ _ ∧ _ from hT1)
  obtain ⟨hd2, hΔ2, hF2⟩ := (show _ ∧ _ ∧ _ from hT2)
  obtain ⟨hO1, hB1, he1⟩ := D.split y1 hd1 hΔ1
  obtain ⟨hO2, hB2, he2⟩ := D.split y2 hd2 hΔ2
  have hx1 : lact γ1 y1 = cpt X x0 z := by
    have h := lact_inv_apply_lact γ1⁻¹ (cpt X x0 z)
    rw [inv_inv] at h
    rw [hy1]
    exact h
  have hg : (γ2⁻¹ * γ1) ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem h2) h1
  have hEq : cpt X x0 (D.zOf y2) = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))) := by
    calc cpt X x0 (D.zOf y2) = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := (rmul_rmul_inv_mat_eq_self hB2).symm
      _ = rmul y2 (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he2]
      _ = rmul (lact γ2⁻¹ (lact γ1 y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [hx1, hy2]
      _ = rmul (lact (γ2⁻¹ * γ1) y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [lact_mul_upper_bounds]
      _ = rmul (lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1]
      _ = lact (γ2⁻¹ * γ1) (rmul (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := (lact_rmul_eq_rmul_lact _ _ _).symm
      _ = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))) :=
        congrArg (lact (γ2⁻¹ * γ1)) (rmul_assoc_frame _ _ _)
  have hw : D.zOf y1 = D.zOf y2 :=
    hFF.2.2.1 _ hF1 _ hF2 _ hg _ (mem_bor_rmul hB1 (FD_mat_inv_mem_bor hB2)) hEq
  have hB' : lact (γ2⁻¹ * γ1) y1 = y2 := by rw [lact_mul_upper_bounds, hx1, hy2]
  have hfree : lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
    calc lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (rmul (lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1))) (D.bOf y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) :=
          (rmul_rmul_inv_mat_eq_self hB1).symm
      _ = rmul (lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by
        first
          | rw [lact_rmul_eq_rmul_lact]
          | exact congrArg (fun w => rmul w _) (lact_rmul_eq_rmul_lact _ _ _).symm
      _ = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1, hB', ← he2]
      _ = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
        rw [← hw]
        exact rmul_assoc_frame _ _ _
  have h1' := X.Γ_free _ hg _ hO1 _ (mem_bor_rmul hB2 (FD_mat_inv_mem_bor hB1)) hfree
  exact (inv_mul_eq_one.1 h1').symm

/- English proof (translation)
Take `⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℝ≥0∞, Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ⁻¹ x) * φ x` from `⟨_, rfl⟩`. Establish `hFm : Measurable Fn`. Rewrite using `[hFn]`. Conclude with `((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hφ`. Establish `hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x`.

Introduce `x hx b hb`. Rewrite using `[hFn]`. Simplify using `only [ind_rmul D FF hγ hx hb (M := ℝ≥0∞), hB x hx b hb]`. Establish `hpt : ∀ z ∈ OmF X x0, FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z))`. Introduce `z hz`.

Rewrite using `[hFn]`. Simplify using `only`. Rewrite using `[lact_inv_apply_lact, ind_cpt D FF hz (M := ℝ≥0∞)]`. Distinguish the cases in `h : z ∈ FF`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]`.

Use `first`. Consider the case `rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]`. Consider the case `rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]`. Rewrite using `[← lintegral_indicator hFF.1]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[muF_lact_upper_bounds hγ]`. Simplify using `only [cpt_lact_upper_bounds]`. Use `_ = ∫⁻ z, Fn (cpt X x0 z) ∂muF X x0 := hM r X (lact γ x0) x0 (isOrth_lact' hγ hx0) hx0 Fn hFm hFB`. Use `_ = _ := by rw [hFn]`.
-/
theorem lunfold_one (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∫⁻ z in FF, φ (lact γ (cpt X x0 z)) ∂muF X x0 =
      ∫⁻ z, (T D FF).indicator 1 (lact γ⁻¹ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 := by
  classical
  obtain ⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℝ≥0∞,
      Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ⁻¹ x) * φ x := ⟨_, rfl⟩
  have hFm : Measurable Fn := by
    rw [hFn]
    exact ((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hφ
  have hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x := by
    intro x hx b hb
    rw [hFn]
    simp only [ind_rmul D FF hγ hx hb (M := ℝ≥0∞), hB x hx b hb]
  have hpt : ∀ z ∈ OmF X x0,
      FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z)) := by
    intro z hz
    rw [hFn]
    dsimp only
    rw [lact_inv_apply_lact, ind_cpt D FF hz (M := ℝ≥0∞)]
    by_cases h : z ∈ FF
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · first
        | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
        | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]
  rw [← lintegral_indicator hFF.1]
  calc ∫⁻ z, FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z ∂muF X x0
      = ∫⁻ z, Fn (lact γ (cpt X x0 z)) ∂muF X x0 :=
        lintegral_congr_ae ((ae_mem_omF x0).mono fun z hz => hpt z hz)
    _ = ∫⁻ z, Fn (cpt X (lact γ x0) z) ∂muF X (lact γ x0) := by
        rw [muF_lact_upper_bounds hγ]
        simp only [cpt_lact_upper_bounds]
    _ = ∫⁻ z, Fn (cpt X x0 z) ∂muF X x0 :=
        hM r X (lact γ x0) x0 (isOrth_lact' hγ hx0) hx0 Fn hFm hFB
    _ = _ := by rw [hFn]

include D in
/- English proof (translation)
Rewrite using `[tsum_congr fun γ : X.Γ => lunfold_one D FF hM hx0 hFF φ hφ hB γ.2]`. Rewrite using `[← lintegral_tsum]`. Use `swap`. Introduce `γ`. Conclude with `(((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp ((measurable_lact γ.1⁻¹).comp (continuous_cpt_apply x0).measurable)).mul (hφ.comp (continuous_cpt_apply x0).measurable)).aemeasurable`.

Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [ae_mem_omF x0, hFF.2.2.2] with z hz hcov`. Take `⟨z', hz'F, γ0, hγ0, b0, hb0, hx⟩` from `hcov`. Establish `hx' : lact γ0⁻¹ (cpt X x0 z) = rmul (cpt X x0 z') b0` using `by rw [hx, lact_inv_apply_lact]`. Establish `hz'O : z' ∈ OmF X x0` using `hFF.2.1 hz'F`.

Take `⟨hΔ', hzz', -⟩` from `D.uniq z' hz'O b0 hb0`. Establish `hxT : lact γ0⁻¹ (cpt X x0 z) ∈ T D FF`. Rewrite using `[hx']`. Use `show _ ∧ _ ∧ _`. Use `⟨rmul_mem_dom_of_mem_dom hb0 hz'O, hΔ', ?_⟩` and prove the remaining obligations.

Rewrite using `[hzz']`. Conclude with `hz'F`. Establish `hsum : ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) = 1`. Rewrite using `[tsum_eq_single ⟨γ0, hγ0⟩]`. Conclude with `Set.indicator_of_mem hxT 1`.

Introduce `γ hne`. Establish `hnT : lact γ.1⁻¹ (cpt X x0 z) ∉ T D FF` using `fun hγT => hne (Subtype.ext (eq_of_lact_inv_cpt_mem_T D FF hFF hz γ.2 hγ0 hγT hxT))`. Use `first`. Consider the case `exact Set.indicator_of_notMem hnT 1`. Consider the case `exact Set.indicator_of_not_mem hnT 1`.

Use `show ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) * φ (cpt X x0 z) = φ (cpt X x0 z)`. Rewrite using `[ENNReal.tsum_mul_right, hsum, one_mul]`.
-/
theorem lunfold (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∑' γ : X.Γ, ∫⁻ z in FF, φ (lact γ.1 (cpt X x0 z)) ∂muF X x0 = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 := by
  classical
  rw [tsum_congr fun γ : X.Γ => lunfold_one D FF hM hx0 hFF φ hφ hB γ.2]
  rw [← lintegral_tsum]
  swap
  · intro γ
    exact (((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp
      ((measurable_lact γ.1⁻¹).comp (continuous_cpt_apply x0).measurable)).mul
      (hφ.comp (continuous_cpt_apply x0).measurable)).aemeasurable
  apply lintegral_congr_ae
  filter_upwards [ae_mem_omF x0, hFF.2.2.2] with z hz hcov
  obtain ⟨z', hz'F, γ0, hγ0, b0, hb0, hx⟩ := hcov
  have hx' : lact γ0⁻¹ (cpt X x0 z) = rmul (cpt X x0 z') b0 := by rw [hx, lact_inv_apply_lact]
  have hz'O : z' ∈ OmF X x0 := hFF.2.1 hz'F
  obtain ⟨hΔ', hzz', -⟩ := D.uniq z' hz'O b0 hb0
  have hxT : lact γ0⁻¹ (cpt X x0 z) ∈ T D FF := by
    rw [hx']
    show _ ∧ _ ∧ _
    refine ⟨rmul_mem_dom_of_mem_dom hb0 hz'O, hΔ', ?_⟩
    rw [hzz']
    exact hz'F
  have hsum : ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) = 1 := by
    rw [tsum_eq_single ⟨γ0, hγ0⟩]
    · exact Set.indicator_of_mem hxT 1
    · intro γ hne
      have hnT : lact γ.1⁻¹ (cpt X x0 z) ∉ T D FF := fun hγT =>
        hne (Subtype.ext (eq_of_lact_inv_cpt_mem_T D FF hFF hz γ.2 hγ0 hγT hxT))
      first
        | exact Set.indicator_of_notMem hnT 1
        | exact Set.indicator_of_not_mem hnT 1
  show ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) *
    φ (cpt X x0 z) = φ (cpt X x0 z)
  rw [ENNReal.tsum_mul_right, hsum, one_mul]

/- English proof (translation)
Establish `hm0 : Measurable fun z => g (cpt X y0 z)` using `hg.comp (continuous_cpt_apply y0).measurable`. Establish `hm1 : Measurable fun z => g (cpt X y1 z)` using `hg.comp (continuous_cpt_apply y1).measurable`. Establish `hpos : ∫⁻ z, ENNReal.ofReal (g (cpt X y0 z)) ∂muF X y0 = ∫⁻ z, ENNReal.ofReal (g (cpt X y1 z)) ∂muF X y1` using `hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (g x)) (ENNReal.measurable_ofReal.comp hg) (fun x hx b hb => by simp only [hB x hx b hb])`. Establish `hneg : ∫⁻ z, ENNReal.ofReal (-g (cpt X y0 z)) ∂muF X y0 = ∫⁻ z, ENNReal.ofReal (-g (cpt X y1 z)) ∂muF X y1` using `hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (-g x)) (ENNReal.measurable_ofReal.comp hg.neg) (fun x hx b hb => by simp only [hB x hx b hb])`. Establish `hn : ∫⁻ z, ‖g (cpt X y0 z)‖ₑ ∂muF X y0 = ∫⁻ z, ‖g (cpt X y1 z)‖ₑ ∂muF X y1` using `hM r X y0 y1 h0 h1 (fun x => ‖g x‖ₑ) hg.enorm (fun x hx b hb => by simp only [hB x hx b hb])`.

Distinguish the cases in `hi : Integrable (fun z => g (cpt X y0 z)) (muF X y0)`. Establish `hi' : Integrable (fun z => g (cpt X y1 z)) (muF X y1)`. Use `⟨hm1.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `h2` using `hi.2`. Unfold `HasFiniteIntegral at h2 ⊢`.

Rewrite using `[← hn]` and apply the resulting hypothesis. Rewrite using `[integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi', hpos, hneg]`. Establish `hi' : ¬ Integrable (fun z => g (cpt X y1 z)) (muF X y1)`. Introduce `h`. Use `hi ⟨hm0.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Establish `h2` using `h.2`. Unfold `HasFiniteIntegral at h2 ⊢`. Rewrite using `[hn]` and apply the resulting hypothesis. Rewrite using `[integral_undef hi, integral_undef hi']`.
-/
private theorem real_invariance_of_measInvStatement (hM : MeasInvStatement (E := E)) {y0 y1 : Frame X.Ψ r}
    (h0 : IsOrth X y0) (h1 : IsOrth X y1) (g : Frame X.Ψ r → ℝ) (hg : Measurable g)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, g (rmul x b) = g x) :
    ∫ z, g (cpt X y0 z) ∂muF X y0 = ∫ z, g (cpt X y1 z) ∂muF X y1 := by
  have hm0 : Measurable fun z => g (cpt X y0 z) := hg.comp (continuous_cpt_apply y0).measurable
  have hm1 : Measurable fun z => g (cpt X y1 z) := hg.comp (continuous_cpt_apply y1).measurable
  have hpos : ∫⁻ z, ENNReal.ofReal (g (cpt X y0 z)) ∂muF X y0 =
      ∫⁻ z, ENNReal.ofReal (g (cpt X y1 z)) ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (g x)) (ENNReal.measurable_ofReal.comp hg)
      (fun x hx b hb => by simp only [hB x hx b hb])
  have hneg : ∫⁻ z, ENNReal.ofReal (-g (cpt X y0 z)) ∂muF X y0 =
      ∫⁻ z, ENNReal.ofReal (-g (cpt X y1 z)) ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (-g x)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun x hx b hb => by simp only [hB x hx b hb])
  have hn : ∫⁻ z, ‖g (cpt X y0 z)‖ₑ ∂muF X y0 = ∫⁻ z, ‖g (cpt X y1 z)‖ₑ ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ‖g x‖ₑ) hg.enorm (fun x hx b hb => by simp only [hB x hx b hb])
  by_cases hi : Integrable (fun z => g (cpt X y0 z)) (muF X y0)
  · have hi' : Integrable (fun z => g (cpt X y1 z)) (muF X y1) := by
      refine ⟨hm1.aestronglyMeasurable, ?_⟩
      have h2 := hi.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [← hn]
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi', hpos, hneg]
  · have hi' : ¬ Integrable (fun z => g (cpt X y1 z)) (muF X y1) := by
      intro h
      refine hi ⟨hm0.aestronglyMeasurable, ?_⟩
      have h2 := h.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [hn]
    rw [integral_undef hi, integral_undef hi']

/- English proof (translation)
Establish `hm0 : Measurable fun z => ψ (cpt X x0 z)` using `hψ.comp (continuous_cpt_apply x0).measurable`. Establish `hm1 : Measurable fun z => ψ (cpt X x0' z)` using `hψ.comp (continuous_cpt_apply x0').measurable`. Establish `hn : ∫⁻ z, ‖ψ (cpt X x0 z)‖ₑ ∂muF X x0 = ∫⁻ z, ‖ψ (cpt X x0' z)‖ₑ ∂muF X x0'` using `hM r X x0 x0' hx0 hx0' (fun x => ‖ψ x‖ₑ) hψ.enorm (fun x hx b hb => by simp only [hB x hx b hb])`. Distinguish the cases in `hi : Integrable (fun z => ψ (cpt X x0 z)) (muF X x0)`. Establish `hi' : Integrable (fun z => ψ (cpt X x0' z)) (muF X x0')`.

Use `⟨hm1.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `h2` using `hi.2`. Unfold `HasFiniteIntegral at h2 ⊢`. Rewrite using `[← hn]` and apply the resulting hypothesis. Apply `Complex.ext` to reduce the goal to its premises.

Establish `e0` using `Complex.reCLM.integral_comp_comm hi`. Establish `e1` using `Complex.reCLM.integral_comp_comm hi'`. Simplify using `only [Complex.reCLM_apply] at e0 e1`. Rewrite using `[← e0, ← e1]`. Conclude with `real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).re) (Complex.measurable_re.comp hψ) (fun x hx b hb => by simp only [hB x hx b hb])`.

Establish `e0` using `Complex.imCLM.integral_comp_comm hi`. Establish `e1` using `Complex.imCLM.integral_comp_comm hi'`. Simplify using `only [Complex.imCLM_apply] at e0 e1`. Rewrite using `[← e0, ← e1]`. Conclude with `real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).im) (Complex.measurable_im.comp hψ) (fun x hx b hb => by simp only [hB x hx b hb])`.

Establish `hi' : ¬ Integrable (fun z => ψ (cpt X x0' z)) (muF X x0')`. Introduce `h`. Use `hi ⟨hm0.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `h2` using `h.2`. Unfold `HasFiniteIntegral at h2 ⊢`.

Rewrite using `[hn]` and apply the resulting hypothesis. Rewrite using `[integral_undef hi, integral_undef hi']`.
-/
theorem cMeasInv (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) {x0' : Frame X.Ψ r}
    (hx0' : IsOrth X x0') (ψ : Frame X.Ψ r → ℂ) (hψ : Measurable ψ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫ z, ψ (cpt X x0 z) ∂muF X x0 = ∫ z, ψ (cpt X x0' z) ∂muF X x0' := by
  have hm0 : Measurable fun z => ψ (cpt X x0 z) := hψ.comp (continuous_cpt_apply x0).measurable
  have hm1 : Measurable fun z => ψ (cpt X x0' z) := hψ.comp (continuous_cpt_apply x0').measurable
  have hn : ∫⁻ z, ‖ψ (cpt X x0 z)‖ₑ ∂muF X x0 = ∫⁻ z, ‖ψ (cpt X x0' z)‖ₑ ∂muF X x0' :=
    hM r X x0 x0' hx0 hx0' (fun x => ‖ψ x‖ₑ) hψ.enorm (fun x hx b hb => by simp only [hB x hx b hb])
  by_cases hi : Integrable (fun z => ψ (cpt X x0 z)) (muF X x0)
  · have hi' : Integrable (fun z => ψ (cpt X x0' z)) (muF X x0') := by
      refine ⟨hm1.aestronglyMeasurable, ?_⟩
      have h2 := hi.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [← hn]
    apply Complex.ext
    · have e0 := Complex.reCLM.integral_comp_comm hi
      have e1 := Complex.reCLM.integral_comp_comm hi'
      simp only [Complex.reCLM_apply] at e0 e1
      rw [← e0, ← e1]
      exact real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).re) (Complex.measurable_re.comp hψ)
        (fun x hx b hb => by simp only [hB x hx b hb])
    · have e0 := Complex.imCLM.integral_comp_comm hi
      have e1 := Complex.imCLM.integral_comp_comm hi'
      simp only [Complex.imCLM_apply] at e0 e1
      rw [← e0, ← e1]
      exact real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).im) (Complex.measurable_im.comp hψ)
        (fun x hx b hb => by simp only [hB x hx b hb])
  · have hi' : ¬ Integrable (fun z => ψ (cpt X x0' z)) (muF X x0') := by
      intro h
      refine hi ⟨hm0.aestronglyMeasurable, ?_⟩
      have h2 := h.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [hn]
    rw [integral_undef hi, integral_undef hi']

/- English proof (translation)
Take `⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℂ, Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ⁻¹ x) * G x` from `⟨_, rfl⟩`. Establish `hFm : Measurable Fn`. Rewrite using `[hFn]`. Conclude with `((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hG`. Establish `hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x`.

Introduce `x hx b hb`. Rewrite using `[hFn]`. Simplify using `only [ind_rmul D FF hγ hx hb (M := ℂ), hB x hx b hb]`. Establish `hpt : ∀ z ∈ OmF X x0, FF.indicator (fun z => G (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z))`. Introduce `z hz`.

Rewrite using `[hFn]`. Simplify using `only`. Rewrite using `[lact_inv_apply_lact, ind_cpt D FF hz (M := ℂ)]`. Distinguish the cases in `h : z ∈ FF`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]`.

Use `first`. Consider the case `rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]`. Consider the case `rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]`. Rewrite using `[← integral_indicator hFF.1]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[muF_lact_upper_bounds hγ]`. Simplify using `only [cpt_lact_upper_bounds]`. Use `_ = ∫ z, Fn (cpt X x0 z) ∂muF X x0 := cMeasInv hM (isOrth_lact' hγ hx0) hx0 Fn hFm hFB`. Use `_ = _ := by rw [hFn]`.
-/
theorem cunfold_one (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (G : Frame X.Ψ r → ℂ) (hG : Measurable G)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∫ z in FF, G (lact γ (cpt X x0 z)) ∂muF X x0 =
      ∫ z, (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ⁻¹ (cpt X x0 z)) * G (cpt X x0 z) ∂muF X x0 := by
  classical
  obtain ⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℂ,
      Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ⁻¹ x) * G x := ⟨_, rfl⟩
  have hFm : Measurable Fn := by
    rw [hFn]
    exact ((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hG
  have hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x := by
    intro x hx b hb
    rw [hFn]
    simp only [ind_rmul D FF hγ hx hb (M := ℂ), hB x hx b hb]
  have hpt : ∀ z ∈ OmF X x0,
      FF.indicator (fun z => G (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z)) := by
    intro z hz
    rw [hFn]
    dsimp only
    rw [lact_inv_apply_lact, ind_cpt D FF hz (M := ℂ)]
    by_cases h : z ∈ FF
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · first
        | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
        | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]
  rw [← integral_indicator hFF.1]
  calc ∫ z, FF.indicator (fun z => G (lact γ (cpt X x0 z))) z ∂muF X x0
      = ∫ z, Fn (lact γ (cpt X x0 z)) ∂muF X x0 :=
        integral_congr_ae ((ae_mem_omF x0).mono fun z hz => hpt z hz)
    _ = ∫ z, Fn (cpt X (lact γ x0) z) ∂muF X (lact γ x0) := by
        rw [muF_lact_upper_bounds hγ]
        simp only [cpt_lact_upper_bounds]
    _ = ∫ z, Fn (cpt X x0 z) ∂muF X x0 :=
        cMeasInv hM (isOrth_lact' hγ hx0) hx0 Fn hFm hFB
    _ = _ := by rw [hFn]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
