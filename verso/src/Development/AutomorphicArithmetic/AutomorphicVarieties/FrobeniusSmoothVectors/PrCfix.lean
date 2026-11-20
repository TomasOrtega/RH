import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, {i : Fin n // i < j}` using `{ toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩ invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩ left_inv := fun p => rfl right_inv := fun q => rfl }`. Establish `hc : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = j`. Introduce `j`. Rewrite using `[Fintype.card_subtype]`. Establish `: (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this, Fin.card_Iio]`. Rewrite using `[Fintype.card_congr e, Fintype.card_sigma]`. Simplify using `only [hc]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n]`. Establish `hs` using `Finset.sum_range_id_mul_two n`. Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ m`.

Simplify using `only [Nat.add_sub_cancel] at hs`. Use polynomial arithmetic with `[hs]`.
-/
private theorem card_pairs (n : ℕ) :
    2 * Fintype.card {p : Fin n × Fin n // p.1 < p.2} + n = n * n := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, {i : Fin n // i < j} :=
    { toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hc : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = j := by
    intro j
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j := by
      ext i; simp
    rw [this, Fin.card_Iio]
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  have hs := Finset.sum_range_id_mul_two n
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel] at hs
    nlinarith [hs]

/- English proof (translation)
Set `M : ({p : Fin n × Fin n // p.1 < p.2} → K) → Matrix (Fin n) (Fin n) K` to `fun f => Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0`. Establish `hskew : ∀ f, (M f)ᵀ = -(M f)`. Introduce `f`. Use extensionality with `i j`. Simplify using `only [M, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]`.

Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> first | simp | (exfalso; omega)`. Set `e : W ≃ₗ[K] ({p : Fin n × Fin n // p.1 < p.2} → K)` to `{ toFun := fun X p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2 map_add' := by`. Introduce `X Y`. Use function extensionality and compare the values at `p`. Simplify using `[Matrix.add_mul]`.

Use the proof step `map_smul' := by`. Introduce `c X`. Use function extensionality and compare the values at `p`. Simplify using `[Matrix.smul_mul]`. Use `invFun := fun f => ⟨M f * T, by`.

Rewrite using `[hW, Matrix.mul_assoc, hTS, Matrix.mul_one]`. Conclude with `hskew f⟩`. Use `left_inv := by`. Introduce `X`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hX : ((X : Matrix (Fin n) (Fin n) K) * S)ᵀ = -((X : Matrix (Fin n) (Fin n) K) * S)` using `(hW X).1 X.2`. Use `show M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2) * T = X`. Establish `hM : M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2) = (X : Matrix (Fin n) (Fin n) K) * S`. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hX i) j`.

Establish `hji` using `congrFun (congrFun hX j) i`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply] at hij hji`. Simplify using `only [M, Matrix.of_apply]`. Use `split_ifs with h1 h3`. Both sides reduce to the same expression.

Rewrite using `[hij, neg_neg]`. Establish `he : i = j` using `le_antisymm (not_lt.mp h3) (not_lt.mp h1)`. Substitute `he` using the available equality. Establish `h22 : 2 * ((X : Matrix (Fin n) (Fin n) K) * S) i i = 0`. Take the linear combination `hij`.

Conclude with `((mul_eq_zero.mp h22).resolve_left h2).symm`. Rewrite using `[hM, Matrix.mul_assoc, hST, Matrix.mul_one]`. Use `right_inv := by`. Introduce `f`. Use function extensionality and compare the values at `p`.

Take `⟨⟨i, j⟩, h⟩` from `p`. Use `show (M f * T * S) i j = f ⟨(i, j), h⟩`. Rewrite using `[Matrix.mul_assoc, hTS, Matrix.mul_one]`. Simplify using `[M, h] }`. Rewrite using `[e.finrank_eq, Module.finrank_fintype_fun_eq_card]`.
-/
private theorem finrank_skew {K : Type} [Field K] {n : ℕ} (h2 : (2 : K) ≠ 0)
    (W : Submodule K (Matrix (Fin n) (Fin n) K)) (S T : Matrix (Fin n) (Fin n) K)
    (hST : S * T = 1) (hTS : T * S = 1) (hW : ∀ X, X ∈ W ↔ (X * S)ᵀ = -(X * S)) :
    Module.finrank K W = Fintype.card {p : Fin n × Fin n // p.1 < p.2} := by
  classical
  let M : ({p : Fin n × Fin n // p.1 < p.2} → K) → Matrix (Fin n) (Fin n) K :=
    fun f => Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0
  have hskew : ∀ f, (M f)ᵀ = -(M f) := by
    intro f
    ext i j
    simp only [M, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    split_ifs with h1 h2 h3 h4 <;> first | simp | (exfalso; omega)
  let e : W ≃ₗ[K] ({p : Fin n × Fin n // p.1 < p.2} → K) :=
    { toFun := fun X p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2
      map_add' := by
        intro X Y
        funext p
        simp [Matrix.add_mul]
      map_smul' := by
        intro c X
        funext p
        simp [Matrix.smul_mul]
      invFun := fun f => ⟨M f * T, by
        rw [hW, Matrix.mul_assoc, hTS, Matrix.mul_one]
        exact hskew f⟩
      left_inv := by
        intro X
        apply Subtype.ext
        have hX : ((X : Matrix (Fin n) (Fin n) K) * S)ᵀ = -((X : Matrix (Fin n) (Fin n) K) * S) :=
          (hW X).1 X.2
        show M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2) * T = X
        have hM : M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2)
            = (X : Matrix (Fin n) (Fin n) K) * S := by
          ext i j
          have hij := congrFun (congrFun hX i) j
          have hji := congrFun (congrFun hX j) i
          simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij hji
          simp only [M, Matrix.of_apply]
          split_ifs with h1 h3
          · rfl
          · rw [hij, neg_neg]
          · have he : i = j := le_antisymm (not_lt.mp h3) (not_lt.mp h1)
            subst he
            have h22 : 2 * ((X : Matrix (Fin n) (Fin n) K) * S) i i = 0 := by
              linear_combination hij
            exact ((mul_eq_zero.mp h22).resolve_left h2).symm
        rw [hM, Matrix.mul_assoc, hST, Matrix.mul_one]
      right_inv := by
        intro f
        funext p
        obtain ⟨⟨i, j⟩, h⟩ := p
        show (M f * T * S) i j = f ⟨(i, j), h⟩
        rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
        simp [M, h] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]

/- English proof (translation)
Introduce `K _ n x h2 hx hr`. Establish `hg : x.left * theta x.left = 1`. Establish `h` using `congrArg SemidirectProduct.left hx`. Simplify `h` using `[SemidirectProduct.mul_left, hr, sgnAct_neg_one]`. Establish `hG : (x.left : Matrix (Fin n) (Fin n) K) = Jmat K n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ * Jmat K n`.

Rewrite using `[← theta_inv_val, inv_eq_of_mul_eq_one_left hg]`. Establish `hGJ : (x.left : Matrix (Fin n) (Fin n) K) * Jmat K n = Jmat K n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ` using `by nth_rewrite 1 [hG]`. Rewrite using `[Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]`. Establish `hST : ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n) * (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat K n), Jmat_mul_Jmat, Matrix.one_mul, Units.mul_inv]`.

Establish `hTS : (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat]`. Establish `hne : x.right ≠ 1`. Rewrite using `[hr]`. Evaluate the decidable proposition.

Establish `key : ∀ X : Matrix (Fin n) (Fin n) K, X ∈ LinearMap.ker (GG.ad n K x - 1) ↔ (X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))ᵀ = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))`. Introduce `X`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GG.ad_apply]`. Simplify using `only [Module.End.one_apply, GG.adFun, GG.mat, if_neg hne, thetaLie]`. Establish `hL : (x.left : Matrix (Fin n) (Fin n) K) * -(Jmat K n * Xᵀ * Jmat K n) * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n) = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))ᵀ`.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, ← hGJ]`. Simplify using `only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]`. Rewrite using `[← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat, Matrix.mul_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `hL` using `[h]`. Use `nth_rewrite 2 [hL]`. Rewrite using `[neg_neg]`. Introduce `h`. Rewrite `hL` using `[h, neg_neg]`.

Establish `h'` using `congrArg (· * (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hL`. Rewrite `h'` using `[Matrix.mul_assoc _ ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n), hST, Matrix.mul_one, Matrix.mul_assoc X, hST, Matrix.mul_one]`. Conclude with `h'`. Rewrite using `[finrank_skew h2 _ _ _ hST hTS key]`. Conclude with `card_pairs n`.
-/
theorem UpperTheory.V.Fr.pr_cfix :
    ∀ (K : Type) [Field K] (n : ℕ) (x : GG n K), (2 : K) ≠ 0 → x * x = 1 → x.right = -1 → 2 * Module.finrank K (LinearMap.ker (GG.ad n K x - 1)) + n = n * n := by
  intro K _ n x h2 hx hr
  have hg : x.left * theta x.left = 1 := by
    have h := congrArg SemidirectProduct.left hx
    simpa [SemidirectProduct.mul_left, hr, sgnAct_neg_one] using h
  have hG : (x.left : Matrix (Fin n) (Fin n) K)
      = Jmat K n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ * Jmat K n := by
    rw [← theta_inv_val, inv_eq_of_mul_eq_one_left hg]
  have hGJ : (x.left : Matrix (Fin n) (Fin n) K) * Jmat K n
      = Jmat K n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ := by
    nth_rewrite 1 [hG]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hST : ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n)
      * (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat K n), Jmat_mul_Jmat, Matrix.one_mul,
      Units.mul_inv]
  have hTS : (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat]
  have hne : x.right ≠ 1 := by
    rw [hr]; decide
  have key : ∀ X : Matrix (Fin n) (Fin n) K, X ∈ LinearMap.ker (GG.ad n K x - 1) ↔
      (X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))ᵀ
        = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n)) := by
    intro X
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GG.ad_apply]
    simp only [Module.End.one_apply, GG.adFun, GG.mat, if_neg hne, thetaLie]
    have hL : (x.left : Matrix (Fin n) (Fin n) K) * -(Jmat K n * Xᵀ * Jmat K n)
        * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n)
        = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, ← hGJ]
      simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      rw [← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat, Matrix.mul_one]
    constructor
    · intro h
      rw [h] at hL
      nth_rewrite 2 [hL]
      rw [neg_neg]
    · intro h
      rw [h, neg_neg] at hL
      have h' := congrArg (· * (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hL
      rw [Matrix.mul_assoc _ ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n), hST, Matrix.mul_one,
        Matrix.mul_assoc X, hST, Matrix.mul_one] at h'
      exact h'
  rw [finrank_skew h2 _ _ _ hST hTS key]
  exact card_pairs n
