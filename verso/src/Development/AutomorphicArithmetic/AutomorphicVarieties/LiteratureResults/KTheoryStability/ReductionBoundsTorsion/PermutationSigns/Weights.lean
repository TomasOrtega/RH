import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Kronecker

namespace PositivityTheory.KB.BlockInvariants

namespace AlternatingWeights

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Rewrite using `[tmC, if_pos hw]`. Simplify using `[ent]`. Both sides reduce to the same expression.
-/
theorem tmC_pos {N q : ℕ} {σ : Equiv.Perm (Fin q)} {w : Fin q → InfinitePlace L}
    (hw : ∀ i, w (σ i) = w i) (Y : Fin q → HS L N) :
    tmC σ w Y = ∑ a : Fin q → Fin N, ∏ i, mat (Y i) (w i) (a i) (a (σ i)) := by
  rw [tmC, if_pos hw]
  simp [ent]
  rfl

/- English proof (translation)
Rewrite using `[tmC, if_neg hw]`. Both sides reduce to the same expression.
-/
theorem tmC_neg {N q : ℕ} {σ : Equiv.Perm (Fin q)} {w : Fin q → InfinitePlace L}
    (hw : ¬ ∀ i, w (σ i) = w i) (Y : Fin q → HS L N) : tmC σ w Y = 0 := by
  rw [tmC, if_neg hw]; rfl

/- English proof (translation)
Simplify using `[ContinuousMultilinearMap.alternatization_apply_apply]`.
-/
theorem alt_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (v : Fin q → E) :
    ContinuousMultilinearMap.alternatization f v = ∑ π : Equiv.Perm (Fin q), Equiv.Perm.sign π • f (v ∘ π) := by
  simp [ContinuousMultilinearMap.alternatization_apply_apply]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, alt_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]`. Both sides reduce to the same expression.
-/
theorem alt_comp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {q : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => F) ℝ) (P : E →L[ℝ] F) :
    (ContinuousMultilinearMap.alternatization f).compContinuousLinearMap P =
      ContinuousMultilinearMap.alternatization (f.compContinuousLinearMap fun _ => P) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, alt_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [alt_apply, ContinuousAlternatingMap.smul_apply, _root_.smul_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.
-/
theorem alt_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (c : ℝ) :
    ContinuousMultilinearMap.alternatization (c • f) = c • ContinuousMultilinearMap.alternatization f := by
  ext v
  simp only [alt_apply, ContinuousAlternatingMap.smul_apply, _root_.smul_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [smul_comm]

/- English proof (translation)
Use extensionality with `v`. Establish `h1 : ContinuousMultilinearMap.alternatization f v = Equiv.Perm.sign σ • ContinuousMultilinearMap.alternatization f v` using `by conv_lhs => rw [alt_apply, ← Equiv.sum_comp (Equiv.mulRight σ)] conv_rhs => rw [alt_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Establish `: v ∘ ⇑(π * σ) = (v ∘ π) ∘ σ`. Use extensionality with `i`.

Simplify using `[Equiv.Perm.coe_mul]`. Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[this, hf, Equiv.Perm.sign_mul, mul_comm, mul_smul]`. Rewrite `h1` using `[hs]`. Establish `h2 : ContinuousMultilinearMap.alternatization f v = -ContinuousMultilinearMap.alternatization f v`.

Rewrite `h1` using `[Units.neg_smul, one_smul]`. Conclude with `h1`. Establish `h3 : ContinuousMultilinearMap.alternatization f v = 0` using `by linarith`. Simplify using `using h3`.
-/
theorem alt_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (σ : Equiv.Perm (Fin q))
    (hf : ∀ v, f (v ∘ σ) = f v) (hs : Equiv.Perm.sign σ = -1) :
    ContinuousMultilinearMap.alternatization f = 0 := by
  ext v
  have h1 : ContinuousMultilinearMap.alternatization f v =
      Equiv.Perm.sign σ • ContinuousMultilinearMap.alternatization f v := by
    conv_lhs => rw [alt_apply, ← Equiv.sum_comp (Equiv.mulRight σ)]
    conv_rhs => rw [alt_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have : v ∘ ⇑(π * σ) = (v ∘ π) ∘ σ := by
      ext i; simp [Equiv.Perm.coe_mul]
    simp only [Equiv.coe_mulRight]
    rw [this, hf, Equiv.Perm.sign_mul, mul_comm, mul_smul]
  rw [hs] at h1
  have h2 : ContinuousMultilinearMap.alternatization f v = -ContinuousMultilinearMap.alternatization f v := by
    rw [Units.neg_smul, one_smul] at h1
    exact h1
  have h3 : ContinuousMultilinearMap.alternatization f v = 0 := by linarith
  simpa using h3

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin N)))]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]`. Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `Fintype.prod_equiv σ _ _ (fun j => by simp)`.
-/
theorem cyc_move {N q : ℕ} (σ : Equiv.Perm (Fin q)) (X Z : Fin q → Matrix (Fin N) (Fin N) ℂ) :
    ∑ a : Fin q → Fin N, ∏ i, (X i * Z i) (a i) (a (σ i)) =
      ∑ a : Fin q → Fin N, ∏ i, (Z (σ⁻¹ i) * X i) (a i) (a (σ i)) := by
  simp only [Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin N)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
  rw [mul_comm]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun j => by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_padL (n M : ℕ) (h : HS L n) (w : InfinitePlace L) : mat (padL n M h) w = padM (mat h w) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_blkL (d n : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (blkL d n h) w = Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ mat h w) := rfl

/- English proof (translation)
Distinguish the cases in `hw : ∀ i, w (σ i) = w i`. Rewrite using `[tmC_pos hw, tmC_pos hw]`. Simplify using `only [mat_padL]`. Use `(Fintype.sum_of_injective (fun b : Fin q → Fin n => fun i => Fin.castLE hnm (b i)) ?_ _ _ ?_ ?_).symm` and prove the remaining obligations. Introduce `b b' hb`.

Use function extensionality and compare the values at `i`. Use `congrFun hb i` as an intermediate fact. Conclude with `Fin.castLE_injective hnm this`. Introduce `a ha`. Establish `: ∃ i, ¬ ((a i : ℕ) < n)`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `ha ⟨fun i => ⟨a i, hc i⟩, funext fun i => Fin.ext rfl⟩`. Take `⟨i, hi⟩` from `this`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [padM, hi])`.

Introduce `b`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[padM]`. Rewrite using `[tmC_neg hw, tmC_neg hw]`.
-/
theorem tmC_pad {n M q : ℕ} (hnm : n ≤ M) (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L)
    (Y : Fin q → HS L n) : tmC (N := M) σ w (fun i => padL n M (Y i)) = tmC σ w Y := by
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw]
    simp only [mat_padL]
    refine (Fintype.sum_of_injective (fun b : Fin q → Fin n => fun i => Fin.castLE hnm (b i)) ?_ _ _ ?_ ?_).symm
    · intro b b' hb
      funext i
      have := congrFun hb i
      exact Fin.castLE_injective hnm this
    · intro a ha
      have : ∃ i, ¬ ((a i : ℕ) < n) := by
        by_contra hc
        push Not at hc
        exact ha ⟨fun i => ⟨a i, hc i⟩, funext fun i => Fin.ext rfl⟩
      obtain ⟨i, hi⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [padM, hi])
    · intro b
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [padM]
  · rw [tmC_neg hw, tmC_neg hw]

/- English proof (translation)
Establish `key : ∀ β : Fin q → Fin d, (∀ i, β i = β (σ i)) → ∀ x y, σ.SameCycle x y → β x = β y`. Introduce `β hβ x y hxy`. Take `⟨k, -, rfl⟩` from `hxy.exists_pow_eq'`. Use `clear hxy`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ← hβ]`. Conclude with `ih`. Set `s` to `Equiv.Perm.SameCycle.setoid σ`. Set `e : {β : Fin q → Fin d // ∀ i, β i = β (σ i)} ≃ (Quotient s → Fin d)` to `{ toFun := fun β => Quotient.lift β.1 (fun x y hxy => key β.1 β.2 x y hxy) invFun := fun f => ⟨fun i => f (Quotient.mk s i), fun i => congrArg f (Quotient.sound (show σ.SameCycle i (σ i) from Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl σ i)))⟩ left_inv := fun β …`.

Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin]`. Both sides reduce to the same expression.
-/
theorem card_inv (d q : ℕ) (σ : Equiv.Perm (Fin q)) :
    Fintype.card {β : Fin q → Fin d // ∀ i, β i = β (σ i)} = d ^ ncyc σ := by
  classical
  have key : ∀ β : Fin q → Fin d, (∀ i, β i = β (σ i)) → ∀ x y, σ.SameCycle x y → β x = β y := by
    intro β hβ x y hxy
    obtain ⟨k, -, rfl⟩ := hxy.exists_pow_eq'
    clear hxy
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ← hβ]; exact ih
  let s := Equiv.Perm.SameCycle.setoid σ
  let e : {β : Fin q → Fin d // ∀ i, β i = β (σ i)} ≃ (Quotient s → Fin d) :=
    { toFun := fun β => Quotient.lift β.1 (fun x y hxy => key β.1 β.2 x y hxy)
      invFun := fun f => ⟨fun i => f (Quotient.mk s i), fun i => congrArg f (Quotient.sound
        (show σ.SameCycle i (σ i) from Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl σ i)))⟩
      left_inv := fun β => rfl
      right_inv := fun f => funext fun x => Quotient.inductionOn x fun i => rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin]
  rfl

/- English proof (translation)
Distinguish the cases in `hw : ∀ i, w (σ i) = w i`. Rewrite using `[tmC_pos hw, tmC_pos hw, ← card_inv d q σ]`. Simplify using `only [mat_blkL]`. Use `set A : Fin q → Matrix (Fin n) (Fin n) ℂ := fun i => mat (Y i) (w i)`. Set `E : (Fin q → Fin d) × (Fin q → Fin n) ≃ (Fin q → Fin (d * n))` to `(Equiv.arrowProdEquivProdArrow (Fin q) (fun _ => Fin d) (fun _ => Fin n)).symm.trans (Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv)`.

Establish `hE : ∀ p, E p = fun i => finProdFinEquiv (p.1 i, p.2 i)` using `fun p => rfl`. Rewrite using `[← Fintype.sum_equiv E (fun p => ∏ i, (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A i)) (E p i) (E p (σ i))) _ (fun p => rfl)]`. Establish `hA : ∀ p : (Fin q → Fin d) × (Fin q → Fin n), ∏ i, (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A i)) (E p i) (E p (σ i)) = (∏ i, if p.1 i = p.1 (σ i) then (1 : ℂ) else 0) * ∏ i, A i (p.2 i) (p.2 (σ i))`. Introduce `p`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[hE, reindex_apply, kroneckerMap_apply, one_apply]`. Simplify using `only [hA]`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[Fintype.card_subtype]`. Simplify using `[Finset.prod_boole, Finset.sum_boole]`. Rewrite using `[tmC_neg hw, tmC_neg hw, mul_zero]`.
-/
theorem tmC_blk {d n q : ℕ} (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (Y : Fin q → HS L n) :
    tmC (N := d * n) σ w (fun i => blkL d n (Y i)) = ((d ^ ncyc σ : ℕ) : ℂ) * tmC σ w Y := by
  classical
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw, ← card_inv d q σ]
    simp only [mat_blkL]
    set A : Fin q → Matrix (Fin n) (Fin n) ℂ := fun i => mat (Y i) (w i)
    let E : (Fin q → Fin d) × (Fin q → Fin n) ≃ (Fin q → Fin (d * n)) :=
      (Equiv.arrowProdEquivProdArrow (Fin q) (fun _ => Fin d) (fun _ => Fin n)).symm.trans
        (Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv)
    have hE : ∀ p, E p = fun i => finProdFinEquiv (p.1 i, p.2 i) := fun p => rfl
    rw [← Fintype.sum_equiv E (fun p => ∏ i, (Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A i)) (E p i) (E p (σ i))) _ (fun p => rfl)]
    have hA : ∀ p : (Fin q → Fin d) × (Fin q → Fin n),
        ∏ i, (Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A i)) (E p i) (E p (σ i)) =
        (∏ i, if p.1 i = p.1 (σ i) then (1 : ℂ) else 0) * ∏ i, A i (p.2 i) (p.2 (σ i)) := by
      intro p
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [hE, reindex_apply, kroneckerMap_apply, one_apply]
    simp only [hA]
    rw [Fintype.sum_prod_type]
    dsimp only
    calc _ = (∑ x : Fin q → Fin d, ∏ i, if x i = x (σ i) then (1 : ℂ) else 0) *
          ∑ y : Fin q → Fin n, ∏ i, A i (y i) (y (σ i)) := (Finset.sum_mul_sum _ _ _ _).symm
      _ = _ := by
        congr 1
        rw [Fintype.card_subtype]
        simp [Finset.prod_boole, Finset.sum_boole]
  · rw [tmC_neg hw, tmC_neg hw, mul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one (N : ℕ) (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

/- English proof (translation)
Distinguish the cases in `hw : ∀ i, w (σ i) = w i`. Rewrite using `[tmC_pos hw, tmC_pos hw]`. Simplify using `only [mat_actL]`. Use `set V : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun v => (((u v)⁻¹ : GL (Fin N) ℂ) : Matrix _ _ ℂ)`. Establish `hV : ∀ v, V v * (V v)ᴴ = 1`.

Introduce `v`. Establish `h2` using `congrArg (fun h => mat h v) hu`. Rewrite `h2` using `[mat_actL, mat_one, Matrix.mul_one]`. Conclude with `mul_eq_one_comm.1 h2`. Use `cyc_move σ (fun i => (V (w i))ᴴ * mat (Y i) (w i)) (fun i => V (w i))` as an intermediate fact.

Rewrite using `[this]`. Use `Finset.sum_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hwi : w (σ⁻¹ i) = w i`. Conclude with `(by simpa using hw (σ⁻¹ i) : w i = w (σ⁻¹ i)).symm`. Rewrite using `[hwi, ← Matrix.mul_assoc, hV, Matrix.one_mul]`.

Rewrite using `[tmC_neg hw, tmC_neg hw]`.
-/
theorem tmC_conj {N q : ℕ} (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (u : Gp L N)
    (hu : actL u (one L N).1 = (one L N).1) (Y : Fin q → HS L N) :
    tmC σ w (fun i => actL u (Y i)) = tmC σ w Y := by
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw]
    simp only [mat_actL]
    set V : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun v => (((u v)⁻¹ : GL (Fin N) ℂ) : Matrix _ _ ℂ)
    have hV : ∀ v, V v * (V v)ᴴ = 1 := by
      intro v
      have h2 := congrArg (fun h => mat h v) hu
      rw [mat_actL, mat_one, Matrix.mul_one] at h2
      exact mul_eq_one_comm.1 h2
    have := cyc_move σ (fun i => (V (w i))ᴴ * mat (Y i) (w i)) (fun i => V (w i))
    rw [this]
    refine Finset.sum_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
    have hwi : w (σ⁻¹ i) = w i := by
      exact (by simpa using hw (σ⁻¹ i) : w i = w (σ⁻¹ i)).symm
    rw [hwi, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  · rw [tmC_neg hw, tmC_neg hw]

/- English proof (translation)
Distinguish the cases in `hw : ∀ i, w (σ i) = w i`. Rewrite using `[tmC_pos hw, tmC_pos hw]`. Establish `h1 : ∀ a : Fin q → Fin N, ∏ i, mat ((Y ∘ σ) i) (w i) (a i) (a (σ i)) = ∏ j, mat (Y j) (w j) (a (σ⁻¹ j)) (a j)`. Introduce `a`. Rewrite using `[← Equiv.prod_comp σ (fun j => mat (Y j) (w j) (a (σ⁻¹ j)) (a j))]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[hw i]`. Simplify using `only [h1]`. Rewrite using `[← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin N)))]`. Use `Finset.sum_congr rfl fun b _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[tmC_neg hw, tmC_neg hw]`.
-/
theorem tmC_perm {N q : ℕ} (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (Y : Fin q → HS L N) :
    tmC σ w (Y ∘ σ) = tmC σ w Y := by
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [tmC_pos hw, tmC_pos hw]
    have h1 : ∀ a : Fin q → Fin N, ∏ i, mat ((Y ∘ σ) i) (w i) (a i) (a (σ i)) =
        ∏ j, mat (Y j) (w j) (a (σ⁻¹ j)) (a j) := by
      intro a
      rw [← Equiv.prod_comp σ (fun j => mat (Y j) (w j) (a (σ⁻¹ j)) (a j))]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [hw i]
    simp only [h1]
    rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin N)))]
    refine Finset.sum_congr rfl fun b _ => Finset.prod_congr rfl fun j _ => ?_
    simp
  · rw [tmC_neg hw, tmC_neg hw]

/- English proof (translation)
Establish `hsub : ∀ x y : Fin q, σ.SameCycle x y`. Establish `: Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = 1` using `h`. Take `⟨u⟩` from `Nat.card_eq_one_iff_unique.1 this`. Introduce `x y`. Conclude with `Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))`.

Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Establish `: Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = 0`. Rewrite using `[Nat.card_eq_zero]`. Use `left`.

Conclude with `⟨fun x => Quotient.inductionOn x fun i => i.elim0⟩`. Rewrite `h` using `[ncyc]`. Use linear arithmetic over natural numbers and integers. Establish `hq2 : 2 ≤ q`. Take `⟨r, hr⟩` from `hq`.

Use linear arithmetic over natural numbers and integers. Establish `hfix : ∀ x, σ x ≠ x`. Introduce `x hx`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : Fin q, y ≠ x := by`. Distinguish the cases in `h0 : (x : ℕ) = 0`.

Conclude with `⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩`. Conclude with `⟨⟨0, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩`. Take `⟨k, -, hk⟩` from `(hsub x y).exists_pow_eq'`. Rewrite `hk` using `[Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx]`. Conclude with `hy hk.symm`.

Establish `hcyc : σ.IsCycle` using `⟨⟨0, by omega⟩, hfix _, fun y _ => hsub _ y⟩`. Establish `hsupp : σ.support = Finset.univ`. Use extensionality with `x`. Simplify using `[hfix x]`. Rewrite using `[hcyc.sign, hsupp, Finset.card_univ, Fintype.card_fin, hq.neg_one_pow]`.
-/
theorem sign_of_ncyc {q : ℕ} (σ : Equiv.Perm (Fin q)) (hq : Even q) (h : ncyc σ = 1) :
    Equiv.Perm.sign σ = -1 := by
  classical
  have hsub : ∀ x y : Fin q, σ.SameCycle x y := by
    have : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = 1 := h
    obtain ⟨u⟩ := Nat.card_eq_one_iff_unique.1 this
    intro x y
    exact Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) = 0 := by
      rw [Nat.card_eq_zero]; left
      exact ⟨fun x => Quotient.inductionOn x fun i => i.elim0⟩
    rw [ncyc] at h; omega
  have hq2 : 2 ≤ q := by
    obtain ⟨r, hr⟩ := hq; omega
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : Fin q, y ≠ x := by
      by_cases h0 : (x : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
    obtain ⟨k, -, hk⟩ := (hsub x y).exists_pow_eq'
    rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx] at hk
    exact hy hk.symm
  have hcyc : σ.IsCycle := ⟨⟨0, by omega⟩, hfix _, fun y _ => hsub _ y⟩
  have hsupp : σ.support = Finset.univ := by
    ext x; simp [hfix x]
  rw [hcyc.sign, hsupp, Finset.card_univ, Fintype.card_fin, hq.neg_one_pow]

/- English proof (translation)
Use extensionality with `Y`. Apply the tactic sequence `cases h : x.2.2 <;> simp [tmR, tmC_pad hnm]`.
-/
theorem tmR_comp_pad {L : Type} [Field L] [NumberField L] {n M q : ℕ} (hnm : n ≤ M) (x : Pat L q) :
    (tmR (N := M) x.1 x.2.1 x.2.2).compContinuousLinearMap (fun _ => padL n M) = tmR (N := n) x.1 x.2.1 x.2.2 := by
  ext Y
  cases h : x.2.2 <;> simp [tmR, tmC_pad hnm]

/- English proof (translation)
Rewrite using `[← Nat.cast_pow, Complex.natCast_re, Nat.cast_pow]`.
-/
theorem natpow_re (d k : ℕ) : ((d : ℂ) ^ k).re = (d : ℝ) ^ k := by
  rw [← Nat.cast_pow, Complex.natCast_re, Nat.cast_pow]

/- English proof (translation)
Rewrite using `[← Nat.cast_pow, Complex.natCast_im]`.
-/
theorem natpow_im (d k : ℕ) : ((d : ℂ) ^ k).im = 0 := by
  rw [← Nat.cast_pow, Complex.natCast_im]

end AlternatingWeights

open AlternatingWeights

/- English proof (translation)
Introduce `L _ _ n M q hnm x`. Rewrite using `[AT, AT, alt_comp, tmR_comp_pad hnm]`.
-/
theorem wPad : WPad := by
  intro L _ _ n M q hnm x
  rw [AT, AT, alt_comp, tmR_comp_pad hnm]

/- English proof (translation)
Introduce `L _ _ d n q x`. Rewrite using `[AT, AT, alt_comp, ← alt_smul]`. Use `congr 1`. Use extensionality with `Y`. Apply the tactic sequence `cases h : x.2.2 <;> simp [tmR, tmC_blk, natpow_re, natpow_im]`.
-/
theorem weylTwoBlockMatrix : WBlk := by
  intro L _ _ d n q x
  rw [AT, AT, alt_comp, ← alt_smul]
  congr 1
  ext Y
  cases h : x.2.2 <;> simp [tmR, tmC_blk, natpow_re, natpow_im]

/- English proof (translation)
Introduce `L _ _ N q x u hu`. Rewrite using `[AT, alt_comp]`. Use `congr 1`. Use extensionality with `Y`. Apply the tactic sequence `cases h : x.2.2 <;> simp [tmR, tmC_conj _ _ u hu]`.
-/
theorem wInv : WInv := by
  intro L _ _ N q x u hu
  rw [AT, alt_comp]
  congr 1
  ext Y
  cases h : x.2.2 <;> simp [tmR, tmC_conj _ _ u hu]

/- English proof (translation)
Introduce `L _ _ N q x hq h1`. Rewrite using `[AT]`. Use `alt_zero _ x.1 (fun v => ?_) (sign_of_ncyc x.1 hq h1)` and prove the remaining obligations. Apply the tactic sequence `cases h : x.2.2 <;> simp [tmR, tmC_perm]`.
-/
theorem wOne : WOne := by
  intro L _ _ N q x hq h1
  rw [AT]
  refine alt_zero _ x.1 (fun v => ?_) (sign_of_ncyc x.1 hq h1)
  cases h : x.2.2 <;> simp [tmR, tmC_perm]

/- English proof (translation)
Introduce `q σ hq`. Prove the components needed by the constructor for the conclusion. Establish `: Nonempty (Quotient (Equiv.Perm.SameCycle.setoid σ))` using `⟨Quotient.mk _ ⟨0, hq⟩⟩`. Conclude with `Nat.card_pos`. Use `Nat.card_le_card_of_surjective (Quotient.mk (Equiv.Perm.SameCycle.setoid σ)) Quotient.mk_surjective` as an intermediate fact.

Simplify `this` using `[ncyc]`.
-/
theorem wCyc : WCyc := by
  intro q σ hq
  constructor
  · have : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid σ)) := ⟨Quotient.mk _ ⟨0, hq⟩⟩
    exact Nat.card_pos
  · have := Nat.card_le_card_of_surjective (Quotient.mk (Equiv.Perm.SameCycle.setoid σ))
      Quotient.mk_surjective
    simpa [ncyc] using this

end PositivityTheory.KB.BlockInvariants

end
