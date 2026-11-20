import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

/- English proof (translation)
Rewrite using `[KType.op, map_inv, ← ContinuousLinearMap.star_eq_adjoint]`. Use `first`. Consider the case `rfl`. Consider the case `simp [Unitary.star_eq_inv]`. Consider the case `simp [unitary.star_eq_inv]`.
-/
theorem op_inv_eq_adjoint (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  rw [KType.op, map_inv, ← ContinuousLinearMap.star_eq_adjoint]
  first
  | rfl
  | simp [Unitary.star_eq_inv]
  | simp [unitary.star_eq_inv]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `h : ε a = ε b`. Rewrite using `[h, mul_comm]`. Simplify using `[hY a b h]`.
-/
private lemma commute_Jm_of_isBlock {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    Y * Jm ε = Jm ε * Y := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · simp [hY a b h]

/- English proof (translation)
Establish `hXH : IsBlock ε Xᴴ` using `fun a b h => by`. Rewrite using `[Matrix.conjTranspose_apply, hX b a (Ne.symm h), star_zero]`. Establish `hc1` using `commute_Jm_of_isBlock hX`. Establish `hc2` using `commute_Jm_of_isBlock hXH`. Establish `hI : Complex.I * (-Complex.I / 2) = 1 / 2`.

Rewrite using `[mul_div_assoc', mul_neg, Complex.I_mul_I]`. Evaluate the numerical expressions. Establish `hIB : Complex.I • ((-Complex.I / 2) • (X + Xᴴ)) = (1 / 2 : ℂ) • (X + Xᴴ)`. Rewrite using `[smul_smul, hI]`. Establish `hs1 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`.

Establish `hs2 : star (-Complex.I / 2) = Complex.I / 2` using `by simp`. Use `⟨(1 / 2 : ℂ) • (X - Xᴴ), (-Complex.I / 2) • (X + Xᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hs1, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]`. Use `module`.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]`. Unfold `inG`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, hs2, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]`. Use `module`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]`.

Rewrite using `[hIB] module`. Rewrite using `[hIB] module`.
-/
lemma block_decomp {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inK ε A ∧ inK ε B ∧ X = A + Complex.I • B ∧
      Xᴴ = -A + Complex.I • B := by
  have hXH : IsBlock ε Xᴴ := fun a b h => by
    rw [Matrix.conjTranspose_apply, hX b a (Ne.symm h), star_zero]
  have hc1 := commute_Jm_of_isBlock hX
  have hc2 := commute_Jm_of_isBlock hXH
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
    norm_num
  have hIB : Complex.I • ((-Complex.I / 2) • (X + Xᴴ)) = (1 / 2 : ℂ) • (X + Xᴴ) := by
    rw [smul_smul, hI]
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by simp
  refine ⟨(1 / 2 : ℂ) • (X - Xᴴ), (-Complex.I / 2) • (X + Xᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hs1, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hs2, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
  · rw [hIB]
    module
  · rw [hIB]
    module

/- English proof (translation)
Use `⟨?_, by rw [neg_mul, mul_neg, hA.2]⟩` and prove the remaining obligations. Establish `h` using `hA.1`. Unfold `inG at h ⊢`. Rewrite using `[Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, h, neg_zero]`.
-/
lemma inK_neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) : inK ε (-A) := by
  refine ⟨?_, by rw [neg_mul, mul_neg, hA.2]⟩
  have h := hA.1
  unfold inG at h ⊢
  rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, h, neg_zero]

/- English proof (translation)
Simplify using `using hmul 0 0`.
-/
lemma gamma_zero {γ : ℝ → KG ε} (hmul : ∀ s t, γ (s + t) = γ s * γ t) : γ 0 = 1 := by
  simpa using hmul 0 0

/- English proof (translation)
Take `⟨γ, -, hγ, hmul⟩` from `exists_oneParam ε hA`. Establish `h0` using `gamma_zero hmul`. Establish `hinv : ∀ t, γ (-t) = (γ t)⁻¹` using `fun t => eq_inv_of_mul_eq_one_left (by rw [← hmul, neg_add_cancel, h0])`. Establish `h1` using `T.hasDeriv A hA γ hγ`. Establish `h2` using `T.hasDeriv (-A) (inK_neg hA) (fun t => γ (-t)) (fun t => by`.

Rewrite using `[hγ]`. Use `congr 1`. Use `push_cast`. Rewrite using `[neg_smul, smul_neg])`. Establish `h3` using `h1.star`.

Simplify using `only [ContinuousLinearMap.star_eq_adjoint] at h3`. Establish `e : (fun t => ContinuousLinearMap.adjoint (T.op (γ t))) = fun t => T.op (γ (-t))`. Use function extensionality and compare the values at `fun t => by rw [← op_inv_eq_adjoint, hinv]`. Rewrite `h3` using `[e]`. Rewrite using `[h3.unique h2, map_neg]`.
-/
lemma dtau_skew (T : KType ε Λ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    ContinuousLinearMap.adjoint (T.dτ A) = -T.dτ A := by
  obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hA
  have h0 := gamma_zero hmul
  have hinv : ∀ t, γ (-t) = (γ t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_left (by rw [← hmul, neg_add_cancel, h0])
  have h1 := T.hasDeriv A hA γ hγ
  have h2 := T.hasDeriv (-A) (inK_neg hA) (fun t => γ (-t)) (fun t => by
    rw [hγ]; congr 1; push_cast; rw [neg_smul, smul_neg])
  have h3 := h1.star
  simp only [ContinuousLinearMap.star_eq_adjoint] at h3
  have e : (fun t => ContinuousLinearMap.adjoint (T.op (γ t))) = fun t => T.op (γ (-t)) :=
    funext fun t => by rw [← op_inv_eq_adjoint, hinv]
  rw [e] at h3
  rw [h3.unique h2, map_neg]

/- English proof (translation)
Take `⟨A, B, hA, hB, hX1, hX2⟩` from `block_decomp hX`. Rewrite using `[hX2, hX1]`. Simplify using `[map_add, map_neg, map_smul, LinearIsometryEquiv.map_smulₛₗ, dtau_skew T hA, dtau_skew T hB, Complex.conj_I]`.
-/
theorem dtau_adj (T : KType ε Λ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ContinuousLinearMap.adjoint (T.dτ X) = T.dτ Xᴴ := by
  obtain ⟨A, B, hA, hB, hX1, hX2⟩ := block_decomp hX
  rw [hX2, hX1]
  simp [map_add, map_neg, map_smul, LinearIsometryEquiv.map_smulₛₗ, dtau_skew T hA, dtau_skew T hB,
    Complex.conj_I]

/- English proof (translation)
Establish `hk : toMK k ∈ unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k` using `k.2`. Establish `hk' : toMK k⁻¹ ∈ unitaryGroup (Fin n) ℂ ∧ toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹` using `(k⁻¹).2`. Establish `e : toMK k * toMK k⁻¹ = 1`. Unfold `toMK toM`. Simplify using the standard rewrite rules.

Establish `hu : (toMK k)ᴴ * toMK k = 1`. Establish `h1` using `(Matrix.mem_unitaryGroup_iff').1 hk.1`. Simplify `h1` using `[Matrix.star_eq_conjTranspose]`. Establish `hUV : (toMK k)ᴴ = toMK k⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Establish `hV : (toMK k⁻¹)ᴴ = toMK k`. Rewrite using `[← hUV, Matrix.conjTranspose_conjTranspose]`. Establish `hUJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, toMK k * (Jm ε * Y) = Jm ε * (toMK k * Y)`. Introduce `Y`. Rewrite using `[← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]`.

Establish `hVJ : toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹` using `hk'.2`. Establish `hA1` using `hA.1`. Unfold `inG at hA1`. Establish `hAJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Aᴴ * (Jm ε * Y) = -(Jm ε * (A * Y))`. Introduce `Y`.

Rewrite using `[← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hA1, Matrix.neg_mul, Matrix.mul_assoc]`. Establish `hAc : ∀ Y : Matrix (Fin n) (Fin n) ℂ, A * (Jm ε * Y) = Jm ε * (A * Y)`. Introduce `Y`. Rewrite using `[← Matrix.mul_assoc, hA.2, Matrix.mul_assoc]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `inG`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hV, hUV]`. Simplify using `only [Matrix.mul_assoc, hVJ, hAJ, Matrix.mul_neg, hUJ, neg_add_cancel]`. Simplify using `only [Matrix.mul_assoc, hVJ, hAc, hUJ]`.
-/
lemma inK_conj (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    inK ε (toMK k * A * toMK k⁻¹) := by
  have hk : toMK k ∈ unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k := k.2
  have hk' : toMK k⁻¹ ∈ unitaryGroup (Fin n) ℂ ∧ toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := (k⁻¹).2
  have e : toMK k * toMK k⁻¹ = 1 := by
    unfold toMK toM
    simp
  have hu : (toMK k)ᴴ * toMK k = 1 := by
    have h1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    simpa [Matrix.star_eq_conjTranspose] using h1
  have hUV : (toMK k)ᴴ = toMK k⁻¹ := by
    calc (toMK k)ᴴ = (toMK k)ᴴ * (toMK k * toMK k⁻¹) := by rw [e, Matrix.mul_one]
      _ = toMK k⁻¹ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hV : (toMK k⁻¹)ᴴ = toMK k := by
    rw [← hUV, Matrix.conjTranspose_conjTranspose]
  have hUJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, toMK k * (Jm ε * Y) = Jm ε * (toMK k * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]
  have hVJ : toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := hk'.2
  have hA1 := hA.1
  unfold inG at hA1
  have hAJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Aᴴ * (Jm ε * Y) = -(Jm ε * (A * Y)) := by
    intro Y
    rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hA1, Matrix.neg_mul, Matrix.mul_assoc]
  have hAc : ∀ Y : Matrix (Fin n) (Fin n) ℂ, A * (Jm ε * Y) = Jm ε * (A * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, hA.2, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hV, hUV]
    simp only [Matrix.mul_assoc, hVJ, hAJ, Matrix.mul_neg, hUJ, neg_add_cancel]
  · simp only [Matrix.mul_assoc, hVJ, hAc, hUJ]

/- English proof (translation)
Take `⟨γ, -, hγ, -⟩` from `exists_oneParam ε hA`. Establish `h1` using `((T.hasDeriv A hA γ hγ).const_mul (T.op k)).mul_const (T.op k⁻¹)`. Establish `h2` using `T.hasDeriv _ (inK_conj k hA) (fun t => k * γ t * k⁻¹) (fun t => by`. Establish `e : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹` using `rfl`. Rewrite using `[e, hγ, show ((t : ℂ) • (toMK k * A * toMK k⁻¹)) = toMK k * ((t : ℂ) • A) * toMK k⁻¹ by`.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]]`. Conclude with `(Matrix.exp_units_conj ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).symm)`. Establish `e : (fun t => T.op (k * γ t * k⁻¹)) = fun t => T.op k * T.op (γ t) * T.op k⁻¹`. Use function extensionality and compare the values at `fun t => by simp only [KType.op, map_mul]; rfl`. Rewrite `h2` using `[e]`.

Conclude with `h1.unique h2`.
-/
lemma dtau_conj_inK (T : KType ε Λ) (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    T.op k * T.dτ A * T.op k⁻¹ = T.dτ (toMK k * A * toMK k⁻¹) := by
  obtain ⟨γ, -, hγ, -⟩ := exists_oneParam ε hA
  have h1 := ((T.hasDeriv A hA γ hγ).const_mul (T.op k)).mul_const (T.op k⁻¹)
  have h2 := T.hasDeriv _ (inK_conj k hA) (fun t => k * γ t * k⁻¹) (fun t => by
    have e : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e, hγ, show ((t : ℂ) • (toMK k * A * toMK k⁻¹)) = toMK k * ((t : ℂ) • A) * toMK k⁻¹ by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    exact (Matrix.exp_units_conj ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).symm)
  have e : (fun t => T.op (k * γ t * k⁻¹)) = fun t => T.op k * T.op (γ t) * T.op k⁻¹ :=
    funext fun t => by simp only [KType.op, map_mul]; rfl
  rw [e] at h2
  exact h1.unique h2

/- English proof (translation)
Take `⟨A, B, hA, hB, hX1, -⟩` from `block_decomp hX`. Substitute `hX1` using the available equality. Establish `e1 : toMK k * (A + Complex.I • B) * toMK k⁻¹ = toMK k * A * toMK k⁻¹ + Complex.I • (toMK k * B * toMK k⁻¹)`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[e1, map_add, map_smul, map_add, map_smul, ← dtau_conj_inK T k hA, ← dtau_conj_inK T k hB, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]`.
-/
theorem dtau_conj (T : KType ε Λ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    T.op k * T.dτ X * T.op k⁻¹ = T.dτ (toMK k * X * toMK k⁻¹) := by
  obtain ⟨A, B, hA, hB, hX1, -⟩ := block_decomp hX
  subst hX1
  have e1 : toMK k * (A + Complex.I • B) * toMK k⁻¹ =
      toMK k * A * toMK k⁻¹ + Complex.I • (toMK k * B * toMK k⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, map_add, map_smul, map_add, map_smul, ← dtau_conj_inK T k hA, ← dtau_conj_inK T k hB,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

/- English proof (translation)
Establish `h1` using `T.hasDeriv Y hY γ hγ`. Establish `e : (fun t => T.op (k * γ t)) = fun t => T.op k * T.op (γ t)`. Use function extensionality and compare the values at `t`. Conclude with `congrArg Subtype.val (map_mul T.τ k (γ t))`. Rewrite using `[e]`.

Conclude with `h1.const_mul (T.op k)`.
-/
theorem hasDerivAt_op (T : KType ε Λ) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => T.op (k * γ t)) (T.op k * T.dτ Y) 0 := by
  have h1 := T.hasDeriv Y hY γ hγ
  have e : (fun t => T.op (k * γ t)) = fun t => T.op k * T.op (γ t) := by
    funext t
    exact congrArg Subtype.val (map_mul T.τ k (γ t))
  rw [e]
  exact h1.const_mul (T.op k)

end ReciprocityTheory.ChartRestriction.DS.S7
