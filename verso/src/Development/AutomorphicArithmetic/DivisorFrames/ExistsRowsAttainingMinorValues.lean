import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

/- English proof (translation)
Establish `hdet : (M.submatrix σ Fin.castSucc).det ≠ 0`. Introduce `h`. Rewrite `hσ` using `[h, map_zero]`. Conclude with `hm.ne hσ`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : Fin k → K, (M.submatrix σ Fin.castSucc) *ᵥ c = fun a => M (σ a) (Fin.last k) := by`.

Use `⟨(M.submatrix σ Fin.castSucc)⁻¹ *ᵥ fun a => M (σ a) (Fin.last k), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]`. Set `c' : Fin (k + 1) → K` to `Fin.snoc (α := fun _ => K) (fun l => - c l) 1`. Set `x : Fin n → K` to `fun ρ => ∑ i, c' i • M ρ i`. Establish `hx0 : ∀ a, x (σ a) = 0`.

Introduce `a`. Establish `h` using `congrFun hc a`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at h`. Simplify using `only [x, c', Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, smul_eq_mul, _root_.one_mul, ← h, neg_mul, Finset.sum_neg_distrib]`. Simplify using `only [mul_comm]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hexp : ∀ t : Fin (k + 1) → Fin n, (M.submatrix t id).det = ∑ i : Fin (k + 1), (-1) ^ ((i : ℕ) + k) * x (t i) * (M.submatrix (fun a => t (i.succAbove a)) Fin.castSucc).det`. Introduce `t`. Establish `h1` using `Matrix.det_updateCol_sum (M.submatrix t id) (Fin.last k) c'`. Establish `h2 : c' (Fin.last k) = 1` using `by simp [c']`.

Rewrite `h1` using `[h2, one_smul]`. Rewrite using `[← h1, Matrix.det_succ_column _ (Fin.last k)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `[x]`.

Use `congr 1`. Use extensionality with `a l`. Simplify using `[Matrix.updateCol_apply, Fin.castSucc_ne_last]`. Establish `hsn : ∀ ρ, w (M.submatrix (Fin.snoc (α` using `fun _ => Fin n) σ ρ) id).det = w (x ρ) * m := by`. Introduce `ρ`.

Rewrite using `[hexp, Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last, hx0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, _root_.one_mul]`. Rewrite using `[← hσ]`. Take `⟨i, -, hi⟩` from `IsNonarchimedean.finset_image_add_of_nonempty hw (fun i : Fin (k + 1) => (-1) ^ ((i : ℕ) + k) * x (τ i) * (M.submatrix (fun a => τ (i.succAbove a)) Fin.castSucc).det) (Finset.univ_nonempty)`. Use `⟨τ i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hsn, hexp]`. Use `hi.trans ?_` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, _root_.one_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hle _) (w.nonneg _)`.
-/
private theorem positionOne_invariantIntegral_exchange_step {K : Type} [Field K] (w : AbsoluteValue K ℝ) (hw : IsNonarchimedean w) {n k : ℕ}
    (M : Matrix (Fin n) (Fin (k + 1)) K) (m : ℝ) (hm : 0 < m)
    (hle : ∀ τ : Fin k → Fin n, w (M.submatrix τ Fin.castSucc).det ≤ m)
    (σ : Fin k → Fin n) (hσ : w (M.submatrix σ Fin.castSucc).det = m) (τ : Fin (k + 1) → Fin n) :
    ∃ ρ : Fin n, w (M.submatrix τ id).det ≤ w (M.submatrix (Fin.snoc (α := fun _ => Fin n) σ ρ) id).det := by
  classical
  have hdet : (M.submatrix σ Fin.castSucc).det ≠ 0 := by
    intro h
    rw [h, map_zero] at hσ
    exact hm.ne hσ
  obtain ⟨c, hc⟩ : ∃ c : Fin k → K, (M.submatrix σ Fin.castSucc) *ᵥ c = fun a => M (σ a) (Fin.last k) := by
    refine ⟨(M.submatrix σ Fin.castSucc)⁻¹ *ᵥ fun a => M (σ a) (Fin.last k), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  let c' : Fin (k + 1) → K := Fin.snoc (α := fun _ => K) (fun l => - c l) 1
  let x : Fin n → K := fun ρ => ∑ i, c' i • M ρ i
  have hx0 : ∀ a, x (σ a) = 0 := by
    intro a
    have h := congrFun hc a
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at h
    simp only [x, c', Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, smul_eq_mul, _root_.one_mul, ← h,
      neg_mul, Finset.sum_neg_distrib]
    simp only [mul_comm]
    ring
  have hexp : ∀ t : Fin (k + 1) → Fin n, (M.submatrix t id).det =
      ∑ i : Fin (k + 1), (-1) ^ ((i : ℕ) + k) * x (t i) *
        (M.submatrix (fun a => t (i.succAbove a)) Fin.castSucc).det := by
    intro t
    have h1 := Matrix.det_updateCol_sum (M.submatrix t id) (Fin.last k) c'
    have h2 : c' (Fin.last k) = 1 := by simp [c']
    rw [h2, one_smul] at h1
    rw [← h1, Matrix.det_succ_column _ (Fin.last k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · simp [x]
    · congr 1
      ext a l
      simp [Matrix.updateCol_apply, Fin.castSucc_ne_last]
  have hsn : ∀ ρ, w (M.submatrix (Fin.snoc (α := fun _ => Fin n) σ ρ) id).det = w (x ρ) * m := by
    intro ρ
    rw [hexp, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hx0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
      Fin.succAbove_last, map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, _root_.one_mul]
    rw [← hσ]
  obtain ⟨i, -, hi⟩ := IsNonarchimedean.finset_image_add_of_nonempty hw
    (fun i : Fin (k + 1) => (-1) ^ ((i : ℕ) + k) * x (τ i) *
        (M.submatrix (fun a => τ (i.succAbove a)) Fin.castSucc).det) (Finset.univ_nonempty)
  refine ⟨τ i, ?_⟩
  rw [hsn, hexp]
  refine hi.trans ?_
  simp only [map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, _root_.one_mul]
  exact mul_le_mul_of_nonneg_left (hle _) (w.nonneg _)

/- English proof (translation)
Introduce `K _ w hw n r X ν hpos hle hex`. Establish `key : ∀ k (hk : k ≤ r), ∃ σ : Fin k → Fin n, ∀ j (hj : j ≤ k), w (colMinor X j (hj.trans hk) fun a => σ (Fin.castLE hj a)) = ν j`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `hk`. Take `⟨σ, hσ⟩` from `hex 0 hk`. Use `⟨σ, fun j hj => ?_⟩` and prove the remaining obligations. Take `rfl : j = 0` from `by omega`. Conclude with `hσ`.

Consider the case `succ k ih`. Introduce `hk`. Establish `hk' : k ≤ r` using `by omega`. Take `⟨σ, hσ⟩` from `ih hk'`. Take `⟨τ, hτ⟩` from `hex (k + 1) hk`.

Take `⟨ρ, hρ⟩` from `positionOne_invariantIntegral_exchange_step w hw (X.submatrix id (Fin.castLE hk)) (ν k) (hpos k hk') (fun t => hle k hk' t) σ (hσ k le_rfl) τ`. Use `⟨Fin.snoc (α := fun _ => Fin n) σ ρ, fun j hj => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge j (k + 1) with h | h` into its components or cases. Establish `hj' : j ≤ k` using `by omega`. Rewrite using `[← hσ j hj']`.

Use `congr 2`. Use function extensionality and compare the values at `a`. Conclude with `Fin.snoc_castSucc (α := fun _ => Fin n) ρ σ (Fin.castLE hj' a)`. Take `rfl : j = k + 1` from `by omega`. Use `le_antisymm (hle _ _ _) ?_` and prove the remaining obligations.

Rewrite using `[← hτ]`. Conclude with `hρ`. Take `⟨σ, hσ⟩` from `key r le_rfl`. Conclude with `⟨σ, fun k hk => hσ k hk⟩`.
-/
theorem UpperTheory.exists_rows_attaining_minor_values :
    ∀ (K : Type) [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ (n r : ℕ) (X : Matrix (Fin n) (Fin r) K) (ν : ℕ → ℝ), (∀ k, k ≤ r → 0 < ν k) → (∀ k (hk : k ≤ r) σ, w (colMinor X k hk σ) ≤ ν k) → (∀ k (hk : k ≤ r), ∃ σ, w (colMinor X k hk σ) = ν k) → ∃ σ : Fin r → Fin n, ∀ k (hk : k ≤ r), w (lead X σ k hk) = ν k := by
  intro K _ w hw n r X ν hpos hle hex
  have key : ∀ k (hk : k ≤ r), ∃ σ : Fin k → Fin n, ∀ j (hj : j ≤ k),
      w (colMinor X j (hj.trans hk) fun a => σ (Fin.castLE hj a)) = ν j := by
    intro k
    induction k with
    | zero =>
      intro hk
      obtain ⟨σ, hσ⟩ := hex 0 hk
      refine ⟨σ, fun j hj => ?_⟩
      obtain rfl : j = 0 := by omega
      exact hσ
    | succ k ih =>
      intro hk
      have hk' : k ≤ r := by omega
      obtain ⟨σ, hσ⟩ := ih hk'
      obtain ⟨τ, hτ⟩ := hex (k + 1) hk
      obtain ⟨ρ, hρ⟩ := positionOne_invariantIntegral_exchange_step w hw (X.submatrix id (Fin.castLE hk)) (ν k) (hpos k hk')
        (fun t => hle k hk' t) σ (hσ k le_rfl) τ
      refine ⟨Fin.snoc (α := fun _ => Fin n) σ ρ, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · have hj' : j ≤ k := by omega
        rw [← hσ j hj']
        congr 2
        funext a
        exact Fin.snoc_castSucc (α := fun _ => Fin n) ρ σ (Fin.castLE hj' a)
      · obtain rfl : j = k + 1 := by omega
        refine le_antisymm (hle _ _ _) ?_
        rw [← hτ]
        exact hρ
  obtain ⟨σ, hσ⟩ := key r le_rfl
  exact ⟨σ, fun k hk => hσ k hk⟩
