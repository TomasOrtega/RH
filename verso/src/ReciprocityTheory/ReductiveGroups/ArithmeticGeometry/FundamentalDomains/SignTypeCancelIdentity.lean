import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PosDefOfBound

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Use `set z : Fin X.p0 → ℂ := fun c => if h' : (c : ℕ) < n then y ⟨c, h'⟩ else 0 with hz`. Establish `hinj : Function.Injective (Fin.castLE h)` using `Fin.castLE_injective h`. Establish `hzc : ∀ b : Fin n, z (Fin.castLE h b) = y b`. Introduce `b`. Simplify using `[hz, b.isLt]`.

Establish `hz0 : ∀ c ∉ Set.range (Fin.castLE h), z c = 0`. Introduce `c hc`. Simplify using `only [hz]`. Rewrite using `[dif_neg]`. Introduce `hcn`.

Conclude with `hc ⟨⟨c, hcn⟩, Fin.ext rfl⟩`. Establish `hvec : ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) = (Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ z`. Use function extensionality and compare the values at `m`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]`. Use `Fintype.sum_of_injective (M := ℂ) (Fin.castLE h) hinj _ _ ?_ ?_` and prove the remaining obligations.

Introduce `c hc`. Simplify using `[hz0 c hc]`. Introduce `b`. Simplify using `[hzc b]`. Establish `hnz : nsq z = nsq y`.

Unfold `nsq`. Conclude with `(Fintype.sum_of_injective (M := ℝ) (Fin.castLE h) hinj _ _ (fun c hc => by simp [hz0 c hc]) (fun b => by simp [hzc b])).symm`. Establish `hconj : ∀ {q : ℕ} (w : Fin q → ℂ), nsq (fun m => conj (w m)) = nsq w`. Introduce `q w`. Unfold `nsq`.

Simplify using the standard rewrite rules. Establish `hmap : ∀ w : Fin X.p0 → ℂ, nsq ((Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ w) = nsq (Matrix.of (Z τ) *ᵥ fun c => conj (w c))`. Introduce `w`. Rewrite using `[← hconj (Matrix.of (Z τ) *ᵥ fun c => conj (w c))]`. Use `congr 1`.

Use function extensionality and compare the values at `m`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Establish `hop0 : 0 ≤ Data.opN (Matrix.of (Z τ))`. Unfold `Data.opN`. Apply `Real.sSup_nonneg` to reduce the goal to its premises.

Introduce and unpack `t ⟨v, -, rfl⟩`. Check the signs of the components of the expression. Establish `hop : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z`. Unfold `Data.zN`. Conclude with `le_ciSup (f := fun τ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ`.

Rewrite using `[hvec, hmap, ← hnz, ← hconj z]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `nsq_nonneg _`.
-/
lemma bound_castLE {n : ℕ} (h : n ≤ X.p0) (Z : X.Coord) (τ : X.Ψ) (y : Fin n → ℂ) :
    nsq ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) ≤
      X.zN Z ^ 2 * nsq y := by
  classical
  set z : Fin X.p0 → ℂ := fun c => if h' : (c : ℕ) < n then y ⟨c, h'⟩ else 0 with hz
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hzc : ∀ b : Fin n, z (Fin.castLE h b) = y b := by
    intro b
    simp [hz, b.isLt]
  have hz0 : ∀ c ∉ Set.range (Fin.castLE h), z c = 0 := by
    intro c hc
    simp only [hz]
    rw [dif_neg]
    intro hcn
    exact hc ⟨⟨c, hcn⟩, Fin.ext rfl⟩
  have hvec : ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) =
      (Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ z := by
    funext m
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    refine Fintype.sum_of_injective (M := ℂ) (Fin.castLE h) hinj _ _ ?_ ?_
    · intro c hc
      simp [hz0 c hc]
    · intro b
      simp [hzc b]
  have hnz : nsq z = nsq y := by
    unfold nsq
    exact (Fintype.sum_of_injective (M := ℝ) (Fin.castLE h) hinj _ _ (fun c hc => by simp [hz0 c hc])
      (fun b => by simp [hzc b])).symm
  have hconj : ∀ {q : ℕ} (w : Fin q → ℂ), nsq (fun m => conj (w m)) = nsq w := by
    intro q w
    unfold nsq
    simp
  have hmap : ∀ w : Fin X.p0 → ℂ, nsq ((Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ w) =
      nsq (Matrix.of (Z τ) *ᵥ fun c => conj (w c)) := by
    intro w
    rw [← hconj (Matrix.of (Z τ) *ᵥ fun c => conj (w c))]
    congr 1
    funext m
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hop0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := by
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hop : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
    unfold Data.zN
    exact le_ciSup (f := fun τ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ
  rw [hvec, hmap, ← hnz, ← hconj z]
  calc nsq (Matrix.of (Z τ) *ᵥ fun c => conj (z c))
      ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq (fun c => conj (z c)) := nsq_mulVec_le_opN _ _
    _ ≤ X.zN Z ^ 2 * nsq (fun c => conj (z c)) := by
      gcongr
      exact nsq_nonneg _

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`. Simplify using `only [Data.lowBlock, Matrix.of_apply, if_true]`. Rewrite using `[dif_neg (by omega)]`.

Simplify using the standard rewrite rules. Introduce `a b hab`. Establish `hab' : a < b` using `hab`. Simplify using `only [Data.lowBlock, Matrix.of_apply]`. Rewrite using `[if_neg (ne_of_lt hab'), dif_neg]`.

Simplify using the standard rewrite rules. Introduce `hh`. Establish `: (a : ℕ) < b` using `hab'`. Use linear arithmetic over natural numbers and integers.
-/
lemma det_lowBlock (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp only [Data.lowBlock, Matrix.of_apply, if_true]
    rw [dif_neg (by omega)]
    simp
  · intro a b hab
    have hab' : a < b := hab
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab'), dif_neg]
    · simp
    · intro hh
      have : (a : ℕ) < b := hab'
      omega

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [psgn_eq_one le_rfl]`. Consider the case `succ k ih`. Rewrite using `[← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]`.
-/
lemma psgn_add (p0 k : ℕ) : psgn p0 (p0 + k) = (-1) ^ k := by
  induction k with
  | zero => simp [psgn_eq_one le_rfl]
  | succ k ih =>
    rw [← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]

/- English proof (translation)
Establish `h1 : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[h1, Complex.re_ofReal_mul, ← mul_assoc, ← mul_pow]`. Evaluate the numerical expressions. Conclude with `hD`.
-/
lemma signType_cancel_identity (k : ℕ) (D : ℂ) (hD : 0 < D.re) : 0 < (-1 : ℝ) ^ k * (((-1 : ℂ) ^ k) * D).re := by
  have h1 : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.re_ofReal_mul, ← mul_assoc, ← mul_pow]
  norm_num
  exact hD

/- English proof (translation)
Conclude with `(Complex.pos_iff.mp hM.det_pos).1`.
-/
lemma pos_re_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) : 0 < M.det.re := by
  exact (Complex.pos_iff.mp hM.det_pos).1

/- English proof (translation)
Rewrite using `[psgn_eq_one hip, one_mul]`. Use `set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ := Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA`. Use `set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB`. Establish `hs0 : 0 ≤ X.zN Z`. Unfold `Data.zN`.

Apply `Real.iSup_nonneg` to reduce the goal to its premises. Introduce `τ'`. Unfold `Data.opN`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `t ⟨v, -, rfl⟩`.

Check the signs of the components of the expression. Establish `hpd` using `posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0`. Establish `heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det`. Unfold `dmin lminor`. Rewrite using `[gram_xZ X ho Z τ]`.

Use `congr 1`. Use extensionality with `a b`. Establish `hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a)` using `Fin.ext rfl`. Establish `hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b)` using `Fin.ext rfl`. Rewrite using `[Matrix.submatrix_apply, hca, hcb, Gp_pp]`.

Simplify using `[hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]`. Rewrite using `[heq]`. Conclude with `pos_re_of_posDef hpd`.
-/
lemma minor_le {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (i : Fin (r + 1)) (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  rw [psgn_eq_one hip, one_mul]
  set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA
  set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0
  have heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ]
    congr 1
    ext a b
    have hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a) :=
      Fin.ext rfl
    have hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b) :=
      Fin.ext rfl
    rw [Matrix.submatrix_apply, hca, hcb, Gp_pp]
    simp [hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]
  rw [heq]
  exact pos_re_of_posDef hpd

/- English proof (translation)
Take `⟨i, hi⟩` from `i`. Simplify using `only at hik`. Substitute `hik` using the available equality. Rewrite using `[show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]`. Use `set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ := Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA`.

Use `set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB`. Establish `hs0 : 0 ≤ X.zN Z`. Unfold `Data.zN`. Apply `Real.iSup_nonneg` to reduce the goal to its premises. Introduce `τ'`.

Unfold `Data.opN`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `t ⟨v, -, rfl⟩`. Check the signs of the components of the expression. Establish `hpd` using `posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0`.

Use `haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne`. Use `haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1`. Establish `heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ = (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det`. Unfold `dmin lminor`. Rewrite using `[gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]`.

Establish `hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) = Fin.castLE X.p0_le a` using `fun a => Fin.ext (by simp)`. Establish `hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) = nI X (Fin.castLE hk m)` using `fun m => Fin.ext (by simp [nI])`. Establish `hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1)`. Use extensionality with `(a | m) (b | m')`. Simplify using `only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]`.

Simplify using `[hA, Matrix.one_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]`. Simplify using `[hB]`. Simplify using `only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]`. Simplify using `[hB]`.

Simplify using `only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]`. Simplify using `[Matrix.one_apply, Fin.castLE_inj]`. Rewrite using `[hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]`. Use `congr 2`. Simplify using `only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]`.

Rewrite using `[heq]`. Conclude with `signType_cancel_identity k _ (pos_re_of_posDef hpd)`.
-/
lemma minor_gt {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  obtain ⟨i, hi⟩ := i
  simp only at hik
  subst hik
  rw [show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]
  set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA
  set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0
  haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne
  haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1
  have heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ =
      (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) =
        Fin.castLE X.p0_le a := fun a => Fin.ext (by simp)
    have hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) =
        nI X (Fin.castLE hk m) := fun m => Fin.ext (by simp [nI])
    have hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1) := by
      ext (a | m) (b | m')
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]
        simp [hA, Matrix.one_apply, Matrix.mul_apply]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]
        simp [Matrix.one_apply, Fin.castLE_inj]
    rw [hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      mul_one]
    congr 2
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]
  rw [heq]
  exact signType_cancel_identity k _ (pos_re_of_posDef hpd)

/- English proof (translation)
Rewrite `hx`, the goal using `[Data.mem_dom_iff]`. Introduce `τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `show (mat x τ * X.lowBlock Z τ).det ≠ 0`. Rewrite using `[Matrix.det_mul, det_lowBlock, mul_one]`.

Conclude with `(hx τ).1`. Distinguish the cases in `hip : (i : ℕ) ≤ X.p0`. Conclude with `minor_le X ho hZ τ i hip`. Establish `hi` using `i.isLt`. Use `X.p0_le` as an intermediate fact.

Conclude with `minor_gt X ho hZ τ ((i : ℕ) - X.p0) (by omega) i (by omega)`.
-/
theorem xZ_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) :
    X.xZ x Z ∈ X.dom := by
  rw [Data.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * X.lowBlock Z τ).det ≠ 0
    rw [Matrix.det_mul, det_lowBlock, mul_one]
    exact (hx τ).1
  · by_cases hip : (i : ℕ) ≤ X.p0
    · exact minor_le X ho hZ τ i hip
    · have hi := i.isLt
      have := X.p0_le
      exact minor_gt X ho hZ τ ((i : ℕ) - X.p0) (by omega) i (by omega)

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
