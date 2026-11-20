import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `h1 : x.left * theta x.left = 1`. Use `congrArg SemidirectProduct.left hx` as an intermediate fact. Simplify `this` using `[hr, sgnAct_neg_one]`. Establish `hX' : x.mat * thetaLie X * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X`. Simplify `hX` using `[GG.adFun, hr]`.

Establish `h2 : (theta x.left)⁻¹ = x.left` using `inv_eq_of_mul_eq_one_left h1`. Establish `hg : x.mat = Jmat K 3 * x.matᵀ * Jmat K 3` using `by show ((x.left : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _ conv_lhs => rw [← h2]`. Rewrite using `[theta_inv_val]`. Both sides reduce to the same expression. Establish `hgJ : x.mat * Jmat K 3 = Jmat K 3 * x.matᵀ` using `by conv_lhs => rw [hg]`.

Rewrite using `[Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]`. Establish `hXg : X * x.mat = x.mat * thetaLie X` using `by conv_lhs => rw [← hX']`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc]`. Establish `: ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x.mat = 1` using `by show ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x.left : Matrix (Fin 3) (Fin 3) K) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Rewrite using `[this, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, Matrix.mul_assoc]`. Use `_ = x.mat * Jmat K 3 * Xᵀ := by rw [hgJ]`. Use `_ = -(X * x.mat * Jmat K 3) := by`.

Rewrite using `[hXg, thetaLie]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]`.
-/
private theorem cw_skew {K : Type} [CommRing K] (x : GG 3 K) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) :
    (X * x.mat * Jmat K 3)ᵀ = -(X * x.mat * Jmat K 3) := by
  have h1 : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    simpa [hr, sgnAct_neg_one] using this
  have hX' : x.mat * thetaLie X * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X := by
    simpa [GG.adFun, hr] using hX
  have h2 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left h1
  have hg : x.mat = Jmat K 3 * x.matᵀ * Jmat K 3 := by
    show ((x.left : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    conv_lhs => rw [← h2]
    rw [theta_inv_val]
    rfl
  have hgJ : x.mat * Jmat K 3 = Jmat K 3 * x.matᵀ := by
    conv_lhs => rw [hg]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hXg : X * x.mat = x.mat * thetaLie X := by
    conv_lhs => rw [← hX']
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    have : ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x.mat = 1 := by
      show ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x.left : Matrix (Fin 3) (Fin 3) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.mul_one]
  calc (X * x.mat * Jmat K 3)ᵀ = Jmat K 3 * x.matᵀ * Xᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, Matrix.mul_assoc]
    _ = x.mat * Jmat K 3 * Xᵀ := by rw [hgJ]
    _ = -(X * x.mat * Jmat K 3) := by
        rw [hXg, thetaLie]
        simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]

/- English proof (translation)
Establish `hs` using `cw_skew x hx hr X hX`. Establish `e : ∀ i j, (X * x.mat * Jmat K 3) i j = (X * x.mat) i (Fin.rev j)`. Introduce `i j`. Apply the tactic sequence `fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl`. Establish `sk : ∀ i j, (X * x.mat * Jmat K 3) j i = -(X * x.mat * Jmat K 3) i j`.

Introduce `i j`. Use `congrFun (congrFun hs i) j` as an intermediate fact. Simplify `this` using `[Matrix.transpose_apply]`. Establish `dg : ∀ i, (X * x.mat * Jmat K 3) i i = 0`. Introduce `i`.

Establish `h` using `sk i i`. Establish `h' : (2 : K) * (X * x.mat * Jmat K 3) i i = 0` using `by rw [two_mul]; nth_rewrite 1 [h]; ring`. Conclude with `(mul_eq_zero.mp h').resolve_left h2`. Establish `m01 : (X * x.mat * Jmat K 3) 0 1 = 0` using `by rw [e]; exact b`. Establish `m02 : (X * x.mat * Jmat K 3) 0 2 = 0` using `by rw [e]; exact a`.

Establish `m12 : (X * x.mat * Jmat K 3) 1 2 = 0` using `by rw [e]; exact c`. Establish `m10 : (X * x.mat * Jmat K 3) 1 0 = 0` using `by rw [sk, m01, neg_zero]`. Establish `m20 : (X * x.mat * Jmat K 3) 2 0 = 0` using `by rw [sk, m02, neg_zero]`. Establish `m21 : (X * x.mat * Jmat K 3) 2 1 = 0` using `by rw [sk, m12, neg_zero]`. Establish `hM : X * x.mat * Jmat K 3 = 0`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Apply the tactic sequence `all_goals simp only [Matrix.zero_apply]`. Apply the tactic sequence `all_goals first`. Consider the case `exact dg _`.

Consider the case `exact m01`. Consider the case `exact m02`. Consider the case `exact m12`. Consider the case `exact m10`. Consider the case `exact m20`.

Consider the case `exact m21`. Establish `hY : X * x.mat = 0`. Establish `: X * x.mat = X * x.mat * Jmat K 3 * Jmat K 3`. Rewrite using `[Matrix.mul_assoc (X * x.mat), Jmat_mul_Jmat, Matrix.mul_one]`. Rewrite using `[this, hM, Matrix.zero_mul]`.

Establish `hinv : x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1` using `by show (x.left : Matrix (Fin 3) (Fin 3) K) * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hinv, Matrix.mul_one]`. Use `_ = 0 := by rw [hY, Matrix.zero_mul]`.
-/
private theorem cw_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : GG 3 K) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) (a : (X * x.mat) 0 0 = 0) (b : (X * x.mat) 0 1 = 0)
    (c : (X * x.mat) 1 0 = 0) : X = 0 := by
  have hs := cw_skew x hx hr X hX
  have e : ∀ i j, (X * x.mat * Jmat K 3) i j = (X * x.mat) i (Fin.rev j) := by
    intro i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl
  have sk : ∀ i j, (X * x.mat * Jmat K 3) j i = -(X * x.mat * Jmat K 3) i j := by
    intro i j
    have := congrFun (congrFun hs i) j
    simpa [Matrix.transpose_apply] using this
  have dg : ∀ i, (X * x.mat * Jmat K 3) i i = 0 := by
    intro i
    have h := sk i i
    have h' : (2 : K) * (X * x.mat * Jmat K 3) i i = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
    exact (mul_eq_zero.mp h').resolve_left h2
  have m01 : (X * x.mat * Jmat K 3) 0 1 = 0 := by rw [e]; exact b
  have m02 : (X * x.mat * Jmat K 3) 0 2 = 0 := by rw [e]; exact a
  have m12 : (X * x.mat * Jmat K 3) 1 2 = 0 := by rw [e]; exact c
  have m10 : (X * x.mat * Jmat K 3) 1 0 = 0 := by rw [sk, m01, neg_zero]
  have m20 : (X * x.mat * Jmat K 3) 2 0 = 0 := by rw [sk, m02, neg_zero]
  have m21 : (X * x.mat * Jmat K 3) 2 1 = 0 := by rw [sk, m12, neg_zero]
  have hM : X * x.mat * Jmat K 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.zero_apply]
    all_goals first
      | exact dg _
      | exact m01
      | exact m02
      | exact m12
      | exact m10
      | exact m20
      | exact m21
  have hY : X * x.mat = 0 := by
    have : X * x.mat = X * x.mat * Jmat K 3 * Jmat K 3 := by
      rw [Matrix.mul_assoc (X * x.mat), Jmat_mul_Jmat, Matrix.mul_one]
    rw [this, hM, Matrix.zero_mul]
  have hinv : x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    show (x.left : Matrix (Fin 3) (Fin 3) K) * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc X = X * x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.zero_mul]

/- English proof (translation)
Introduce `l _ k _ F K _ h2 B π h c hc hd`. Establish `hx : B.r c * B.r c = 1` using `by rw [← map_mul, hc, map_one]`. Establish `hr : (B.r c).right = -1` using `by rw [B.nu, hd]`. Establish `hg : ∀ a b, pw a b ≠ 0 → (B.r c).mat a b = 0` using `fun a b hab => h.r c a b hab`. Establish `key : ∀ j (v : LinearMap.ker (h.ad j c - 1)), (B.r c).adFun ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) = ((v : adp K j) : Matrix (Fin 3) (Fin 3) K)`.

Introduce `j v`. Establish `hv` using `v.2`. Rewrite `hv` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Use `congrArg Subtype.val hv` as an intermediate fact. Simplify `this` using `[Box.Ev.ad, Box.ad, adRep, GG.ad_apply]`.

Prove the components needed by the constructor for the conclusion. Set `f : LinearMap.ker (h.ad 0 c - 1) →ₗ[K] K` to `{ toFun := fun v => (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0 map_add' := by intro v w; simp [Matrix.add_mul] map_smul' := by intro a v; simp [Matrix.smul_mul] }`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`.

Establish `hX : ∀ a b, pw a b ≠ 0 → ((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) a b = 0` using `fun a b hab => (v : adp K 0).2 a b hab`. Establish `e01 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1 = 0`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_three, hg 0 1 (by decide), hX 0 1 (by decide), hg 2 1 (by decide)]`. Expand and normalize the polynomial expressions, which then agree. Establish `e10 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0 = 0`.

Rewrite using `[Matrix.mul_apply, Fin.sum_univ_three, hX 1 0 (by decide), hg 1 0 (by decide), hX 1 2 (by decide)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `cw_zero h2 (B.r c) hx hr _ (key 0 v) hv e01 e10`. Conclude with `Subtype.ext (Subtype.ext h0)`. Use `LinearMap.finrank_le_finrank_of_injective hf` as an intermediate fact.

Simplify using `using this`. Set `f : LinearMap.ker (h.ad 1 c - 1) →ₗ[K] K × K` to `{ toFun := fun v => ((((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1, (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0) map_add' := by intro v w; simp [Matrix.add_mul] map_smul' := by intro a v; simp [Matrix.smul_mul] }`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`.

Establish `hX : ∀ a b, pw a b ≠ 1 → ((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) a b = 0` using `fun a b hab => (v : adp K 1).2 a b hab`. Establish `e00 : (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0 = 0`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_three, hX 0 0 (by decide), hg 1 0 (by decide), hX 0 2 (by decide)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv'` using `Prod.mk.inj hv`.

Establish `h0` using `cw_zero h2 (B.r c) hx hr _ (key 1 v) e00 hv'.1 hv'.2`. Conclude with `Subtype.ext (Subtype.ext h0)`. Use `LinearMap.finrank_le_finrank_of_injective hf` as an intermediate fact. Simplify using `using this`.
-/
theorem UpperTheory.V.Fr.ep_cw :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ c : F.Γ, c * c = 1 → F.del c = -1 → Module.finrank K (LinearMap.ker (h.ad 0 c - 1)) ≤ 1 ∧ Module.finrank K (LinearMap.ker (h.ad 1 c - 1)) ≤ 2 := by
  intro l _ k _ F K _ h2 B π h c hc hd
  have hx : B.r c * B.r c = 1 := by rw [← map_mul, hc, map_one]
  have hr : (B.r c).right = -1 := by rw [B.nu, hd]
  have hg : ∀ a b, pw a b ≠ 0 → (B.r c).mat a b = 0 := fun a b hab => h.r c a b hab
  have key : ∀ j (v : LinearMap.ker (h.ad j c - 1)),
      (B.r c).adFun ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) = ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) := by
    intro j v
    have hv := v.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
    have := congrArg Subtype.val hv
    simpa [Box.Ev.ad, Box.ad, adRep, GG.ad_apply] using this
  constructor
  · let f : LinearMap.ker (h.ad 0 c - 1) →ₗ[K] K :=
      { toFun := fun v => (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 0 → ((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 0).2 a b hab
      have e01 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hg 0 1 (by decide), hX 0 1 (by decide), hg 2 1 (by decide)]
        ring
      have e10 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 1 0 (by decide), hg 1 0 (by decide), hX 1 2 (by decide)]
        ring
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 0 v) hv e01 e10
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  · let f : LinearMap.ker (h.ad 1 c - 1) →ₗ[K] K × K :=
      { toFun := fun v => ((((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1,
          (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0)
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 1 → ((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 1).2 a b hab
      have e00 : (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 0 0 (by decide), hg 1 0 (by decide), hX 0 2 (by decide)]
        ring
      have hv' := Prod.mk.inj hv
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 1 v) e00 hv'.1 hv'.2
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
