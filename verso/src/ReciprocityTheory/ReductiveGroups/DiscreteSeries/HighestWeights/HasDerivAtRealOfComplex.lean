import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OpEqExp
import Formalism.RealPlaceAnalysis.StatementKT

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def kunits {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : Fin n → Fin n → Module.End ℂ T.V :=
  fun a b => ((T.dτ (Matrix.single a b 1) : T.V →L[ℂ] T.V) : Module.End ℂ T.V)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hC⟩`. Use `⟨?_, hC⟩` and prove the remaining obligations. Establish `h1 : Xᴴ * Jm ε = -(X * Jm ε)`. Rewrite using `[hC]`.

Conclude with `eq_neg_of_add_eq_zero_left hG`. Establish `h2` using `congrArg (· * Jm ε) h1`. Simplify using `only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.neg_mul] at h2`. Conclude with `h2`. Introduce and unpack `⟨hH, hC⟩`.

Use `⟨?_, hC⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[hH, Matrix.neg_mul, hC, neg_add_cancel]`.
-/
theorem inK_iff' (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  constructor
  · rintro ⟨hG, hC⟩
    refine ⟨?_, hC⟩
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]; exact eq_neg_of_add_eq_zero_left hG
    have h2 := congrArg (· * Jm ε) h1
    simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.neg_mul] at h2
    exact h2
  · rintro ⟨hH, hC⟩
    refine ⟨?_, hC⟩
    unfold inG
    rw [hH, Matrix.neg_mul, hC, neg_add_cancel]

/- English proof (translation)
Use `show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _`. Rewrite using `[map_inv]`. Both sides reduce to the same expression.
-/
theorem KType.op_inv {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = star (T.op k) := by
  show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_inv]
  rfl

/- English proof (translation)
The claim follows from `Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem k.2.1)`.
-/
theorem toMK_inv' {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = star (toMK k) :=
  Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem k.2.1)

/- English proof (translation)
Use `h.scomp z Complex.ofRealCLM.hasDerivAt` as an intermediate fact. Simplify using `only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at this`. Conclude with `this`.
-/
theorem hasDerivAt_real_of_complex' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : ℂ → F} {g' : F} {z : ℝ} (h : HasDerivAt g g' (z : ℂ)) :
    HasDerivAt (fun y : ℝ => g (y : ℂ)) g' z := by
  have := h.scomp z Complex.ofRealCLM.hasDerivAt
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at this
  exact this

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve ε hX`. Use `set A := T.dτ X`. Establish `key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1`. Introduce `t`. Establish `h1` using `KType.op_curve T hX γ hγ t`.

Establish `h2 : star (T.op (γ t)) * T.op (γ t) = 1` using `Unitary.coe_star_mul_self _`. Rewrite `h2` using `[h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]`. Conclude with `h2`. Establish `hd0` using `(hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))`. Establish `hd2` using `hasDerivAt_real_of_complex' hd0`.

Establish `hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) * fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1` using `funext fun t => by`. Simplify using `using key t`. Rewrite `hd2` using `[hf]`. Use `hd2.unique (hasDerivAt_const _ _)` as an intermediate fact. Simplify using `at this`.

Conclude with `eq_neg_of_add_eq_zero_left this`.
-/
theorem KType.star_dτ {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (T.dτ X) = -T.dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := T.dτ X
  have key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    intro t
    have h1 := KType.op_curve T hX γ hγ t
    have h2 : star (T.op (γ t)) * T.op (γ t) = 1 := Unitary.coe_star_mul_self _
    rw [h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal] at h2
    exact h2
  have hd0 := (hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul
    (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))
  have hd2 := hasDerivAt_real_of_complex' hd0
  have hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) *
      fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1 := funext fun t => by
    simpa using key t
  rw [hf] at hd2
  have := hd2.unique (hasDerivAt_const _ _)
  simp at this
  exact eq_neg_of_add_eq_zero_left this

/- English proof (translation)
Rewrite `hY`, the goal using `[inK_iff']`. Establish `hK` using `k.2.2`. Establish `hK' : star (toMK k) * Jm ε = Jm ε * star (toMK k)` using `(Kset_star ε k.2).2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hY.1]`.

Simplify using `only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = toMK k * (Y * (Jm ε * star (toMK k))) := by rw [hK']`. Use `_ = toMK k * ((Y * Jm ε) * star (toMK k)) := by simp only [Matrix.mul_assoc]`.

Use `_ = toMK k * ((Jm ε * Y) * star (toMK k)) := by rw [hY.2]`. Use `_ = (toMK k * Jm ε) * Y * star (toMK k) := by simp only [Matrix.mul_assoc]`. Use `_ = Jm ε * toMK k * Y * star (toMK k) := by rw [hK]`. Use `_ = Jm ε * (toMK k * Y * star (toMK k)) := by simp only [Matrix.mul_assoc]`.
-/
theorem inK_conj' {ε : Fin n → Bool} (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    inK ε (toMK k * Y * star (toMK k)) := by
  rw [inK_iff'] at hY ⊢
  have hK := k.2.2
  have hK' : star (toMK k) * Jm ε = Jm ε * star (toMK k) := (Kset_star ε k.2).2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hY.1]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]
  · calc toMK k * Y * star (toMK k) * Jm ε = toMK k * (Y * (star (toMK k) * Jm ε)) := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * (Y * (Jm ε * star (toMK k))) := by rw [hK']
      _ = toMK k * ((Y * Jm ε) * star (toMK k)) := by simp only [Matrix.mul_assoc]
      _ = toMK k * ((Jm ε * Y) * star (toMK k)) := by rw [hY.2]
      _ = (toMK k * Jm ε) * Y * star (toMK k) := by simp only [Matrix.mul_assoc]
      _ = Jm ε * toMK k * Y * star (toMK k) := by rw [hK]
      _ = Jm ε * (toMK k * Y * star (toMK k)) := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve ε hY`. Establish `hY'` using `inK_conj' k hY`. Use `set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)`. Establish `hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK k)` using `toMK_inv' k`. Establish `hγ' : ∀ t : ℝ, toMK (k * γ t * k⁻¹) = NormedSpace.exp ((t : ℂ) • (toMK k * Y * star (toMK k)))`.

Introduce `t`. Establish `e1 : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹` using `rfl`. Rewrite using `[e1, toMK_inv', hγ t, ← hU]`. Establish `e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.

Rewrite using `[e2, Matrix.exp_units_conj]`. Use `set B := T.dτ Y`. Use `set C := T.dτ (toMK k * Y * star (toMK k))`. Establish `key : ∀ t : ℝ, T.op k * NormedSpace.exp ((t : ℂ) • B) * star (T.op k) = NormedSpace.exp ((t : ℂ) • C)`. Introduce `t`.

Rewrite using `[← KType.op_curve T hY γ hγ t, ← KType.op_curve T hY' _ hγ' t, ← KType.op_inv]`. Use `show _ = ((T.τ (k * γ t * k⁻¹) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)`. Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression. Establish `h1` using `hasDerivAt_real_of_complex' (z := 0) (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (T.op k)).mul_const (star (T.op k)))`.

Establish `h2` using `hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))`. Establish `hf : (fun y : ℝ => T.op k * NormedSpace.exp ((y : ℂ) • B) * star (T.op k)) = fun y : ℝ => NormedSpace.exp ((y : ℂ) • C)` using `funext key`. Simplify using `only [hf] at h1`. Use `h1.unique h2` as an intermediate fact. Simplify using `using this`.
-/
theorem KType.conj_dτ {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    T.op k * T.dτ Y * star (T.op k) = T.dτ (toMK k * Y * star (toMK k)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' k hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK k) :=
    toMK_inv' k
  have hγ' : ∀ t : ℝ, toMK (k * γ t * k⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK k * Y * star (toMK k))) := by
    intro t
    have e1 : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  set B := T.dτ Y
  set C := T.dτ (toMK k * Y * star (toMK k))
  have key : ∀ t : ℝ, T.op k * NormedSpace.exp ((t : ℂ) • B) * star (T.op k) =
      NormedSpace.exp ((t : ℂ) • C) := by
    intro t
    rw [← KType.op_curve T hY γ hγ t, ← KType.op_curve T hY' _ hγ' t, ← KType.op_inv]
    show _ = ((T.τ (k * γ t * k⁻¹) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)
    rw [map_mul, map_mul]
    rfl
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (T.op k)).mul_const (star (T.op k)))
  have h2 := hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))
  have hf : (fun y : ℝ => T.op k * NormedSpace.exp ((y : ℂ) • B) * star (T.op k)) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • C) := funext key
  simp only [hf] at h1
  have := h1.unique h2
  simpa using this

section MatDeriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `((hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ)).mul_const Y).mul (hasDerivAt_exp_smul_const (-X) ((0 : ℝ) : ℂ))` as an intermediate fact. Use `HasDerivAt.congr_deriv this ?_` and prove the remaining obligations. Simplify using `[sub_eq_add_neg]`.
-/
theorem mat_conj_hasDerivAt (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun z : ℂ => NormedSpace.exp (z • X) * Y * NormedSpace.exp (z • (-X)))
      (X * Y - Y * X) ((0 : ℝ) : ℂ) := by
  have := ((hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ)).mul_const Y).mul
    (hasDerivAt_exp_smul_const (-X) ((0 : ℝ) : ℂ))
  refine HasDerivAt.congr_deriv this ?_
  simp [sub_eq_add_neg]

/- English proof (translation)
Establish `h` using `((LinearMap.toContinuousLinearMap T.dτ).hasFDerivAt).comp_hasDerivAt _ (mat_conj_hasDerivAt X Y)`. Conclude with `hasDerivAt_real_of_complex' (z := 0) h`.
-/
theorem dτ_conj_hasDerivAt {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => T.dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (T.dτ (X * Y - Y * X)) 0 := by
  have h := ((LinearMap.toContinuousLinearMap T.dτ).hasFDerivAt).comp_hasDerivAt _
    (mat_conj_hasDerivAt X Y)
  exact hasDerivAt_real_of_complex' (z := 0) h

end MatDeriv

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve ε hX`. Use `set A := T.dτ X`. Use `set B := T.dτ Y`. Establish `hA` using `KType.star_dτ T hX`. Establish `hXs` using `((inK_iff' ε X).1 hX).1`.

Establish `key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) = T.dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))`. Introduce `s`. Establish `h` using `KType.conj_dτ T (γ s) hY`. Rewrite `h` using `[KType.op_curve T hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[h]`.

Use `congr 2`. Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs, Complex.star_def, Complex.conj_ofReal]`. Establish `h1` using `hasDerivAt_real_of_complex' (z := 0) (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))`. Establish `h2` using `dτ_conj_hasDerivAt T X Y`. Establish `h1'` using `h1.congr_of_eventuallyEq (f₁ := fun s : ℝ => T.dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))) (Filter.Eventually.of_forall fun s => (key s).symm)`.

Use `h1'.unique h2` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[sub_eq_add_neg]`.
-/
theorem KType.dτ_bracket {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    T.dτ X * T.dτ Y - T.dτ Y * T.dτ X = T.dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := T.dτ X
  set B := T.dτ Y
  have hA := KType.star_dτ T hX
  have hXs := ((inK_iff' ε X).1 hX).1
  have key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) =
      T.dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) := by
    intro s
    have h := KType.conj_dτ T (γ s) hY
    rw [KType.op_curve T hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA,
      Complex.star_def, Complex.conj_ofReal] at h
    rw [h]
    congr 2
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
      Complex.star_def, Complex.conj_ofReal]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul
      (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))
  have h2 := dτ_conj_hasDerivAt T X Y
  have h1' := h1.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => T.dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
    (Filter.Eventually.of_forall fun s => (key s).symm)
  have := h1'.unique h2
  rw [← this]
  simp [sub_eq_add_neg]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]`. Apply the tactic sequence `by_cases hi : a = i <;> by_cases hj : b = j`. Substitute `hi hj` using the available equality. Simplify using `[h, mul_comm]`.

Apply the tactic sequence `all_goals simp [hi, hj]`.
-/
theorem single_mul_Jm {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    Matrix.single a b c * Jm ε = Jm ε * Matrix.single a b c := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [h, mul_comm]
  all_goals simp [hi, hj]

def kp1 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - Matrix.single b a 1)

def kp2 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (Matrix.single a b 1 + Matrix.single b a 1)

/- English proof (translation)
Unfold `kp1 kp2`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]`. Establish `hI : Complex.I * -(Complex.I / 2) = 1 / 2` using `by ring_nf; rw [Complex.I_sq]; ring`. Rewrite using `[← mul_assoc, hI]`.

Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem single_eq_kp (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = kp1 a b + Complex.I • kp2 a b := by
  unfold kp1 kp2
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]
  have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [← mul_assoc, hI]
  split_ifs <;> ring

/- English proof (translation)
Unfold `kp1 kp2`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]`. Establish `hI : Complex.I * -(Complex.I / 2) = 1 / 2` using `by ring_nf; rw [Complex.I_sq]; ring`. Rewrite using `[← mul_assoc, hI]`.

Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem single_eq_kp' (a b : Fin n) :
    Matrix.single b a (1 : ℂ) = -kp1 a b + Complex.I • kp2 a b := by
  unfold kp1 kp2
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul]
  have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [← mul_assoc, hI]
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[inK_iff']`. Unfold `kp1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, ← neg_sub, smul_neg]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, single_mul_Jm h, single_mul_Jm h.symm]`.
-/
theorem inK_hermitian_unit {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) : inK ε (kp1 a b) := by
  rw [inK_iff']
  unfold kp1
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, ← neg_sub, smul_neg]
    simp
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, single_mul_Jm h,
      single_mul_Jm h.symm]

/- English proof (translation)
Rewrite using `[inK_iff']`. Unfold `kp2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single, add_comm, ← neg_smul]`. Apply the tactic sequence `congr 1 <;> simp [Complex.conj_I] <;> ring`.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, single_mul_Jm h, single_mul_Jm h.symm]`.
-/
theorem inK_skew_hermitian_unit {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) : inK ε (kp2 a b) := by
  rw [inK_iff']
  unfold kp2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, add_comm, ← neg_smul]
    congr 1 <;> simp [Complex.conj_I] <;> ring
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, single_mul_Jm h,
      single_mul_Jm h.symm]

/- English proof (translation)
Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem brk_expand {R : Type*} [Ring R] [Algebra ℂ R] (a1 a2 b1 b2 : R) :
    (a1 + Complex.I • a2) * (b1 + Complex.I • b2) - (b1 + Complex.I • b2) * (a1 + Complex.I • a2) =
      (a1 * b1 - b1 * a1) + Complex.I • (a1 * b2 - b2 * a1) + Complex.I • (a2 * b1 - b1 * a2) +
        (Complex.I * Complex.I) • (a2 * b2 - b2 * a2) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, smul_sub]
  abel

/- English proof (translation)
Rewrite using `[single_eq_kp a b, single_eq_kp c d, brk_expand, map_add, map_add, map_smul, map_smul, brk_expand, map_add, map_add, map_add, map_smul, map_smul, map_smul, KType.dτ_bracket T (inK_hermitian_unit hab) (inK_hermitian_unit hcd), KType.dτ_bracket T (inK_hermitian_unit hab) (inK_skew_ …`.
-/
theorem KType.dτ_bracket_single {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    T.dτ (Matrix.single a b 1) * T.dτ (Matrix.single c d 1) -
        T.dτ (Matrix.single c d 1) * T.dτ (Matrix.single a b 1) =
      T.dτ (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
  rw [single_eq_kp a b, single_eq_kp c d, brk_expand, map_add, map_add, map_smul, map_smul,
    brk_expand, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    KType.dτ_bracket T (inK_hermitian_unit hab) (inK_hermitian_unit hcd), KType.dτ_bracket T (inK_hermitian_unit hab) (inK_skew_hermitian_unit hcd),
    KType.dτ_bracket T (inK_skew_hermitian_unit hab) (inK_hermitian_unit hcd), KType.dτ_bracket T (inK_skew_hermitian_unit hab) (inK_skew_hermitian_unit hcd)]

/- English proof (translation)
Rewrite using `[single_eq_kp a b, single_eq_kp' a b, map_add, map_smul, map_add, map_smul, map_neg, star_add, star_smul, KType.star_dτ T (inK_hermitian_unit hab), KType.star_dτ T (inK_skew_hermitian_unit hab)]`. Simplify using `[Complex.conj_I]`.
-/
theorem KType.star_dτ_single {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {a b : Fin n} (hab : ε a = ε b) :
    star (T.dτ (Matrix.single a b 1)) = T.dτ (Matrix.single b a 1) := by
  rw [single_eq_kp a b, single_eq_kp' a b, map_add, map_smul, map_add, map_smul, map_neg, star_add,
    star_smul, KType.star_dτ T (inK_hermitian_unit hab), KType.star_dτ T (inK_skew_hermitian_unit hab)]
  simp [Complex.conj_I]

/- English proof (translation)
Introduce `a b hab x y`. Use `show ⟪T.dτ (Matrix.single a b 1) x, y⟫_ℂ = ⟪x, T.dτ (Matrix.single b a 1) y⟫_ℂ`. Rewrite using `[← KType.star_dτ_single T hab, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]`.
-/
theorem KType.kUnit {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KUnit ε (kunits T) := by
  intro a b hab x y
  show ⟪T.dτ (Matrix.single a b 1) x, y⟫_ℂ = ⟪x, T.dτ (Matrix.single b a 1) y⟫_ℂ
  rw [← KType.star_dτ_single T hab, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/- English proof (translation)
Introduce `a b c d hab hcd`. Establish `hbr` using `KType.dτ_bracket_single T hab hcd`. Establish `hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 = (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0)`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a`. Substitute `h1 h2` using the available equality.

Simplify using `[Matrix.single_mul_single_same]`. Substitute `h1` using the available equality. Simplify using `[Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]`. Substitute `h2` using the available equality. Simplify using `[Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]`.

Simplify using `[Matrix.single_mul_single_of_ne, Matrix.single_mul_single_of_ne, h1, h2]`. Rewrite `hbr` using `[hm]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Establish `hx` using `congrArg (fun F : T.V →L[ℂ] T.V => F x) hbr`.

Establish `e : ∀ A B : T.V →L[ℂ] T.V, (A * B) x = A (B x)` using `fun _ _ => rfl`. Simplify using `only [_root_.sub_apply, e, map_sub] at hx`. Simplify using `only [kunits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe]`. Rewrite using `[hx]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem KType.kRel {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KRel ε (kunits T) := by
  intro a b c d hab hcd
  have hbr := KType.dτ_bracket_single T hab hcd
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1 h2; simp [Matrix.single_mul_single_same]
    · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
    · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
    · simp [Matrix.single_mul_single_of_ne, Matrix.single_mul_single_of_ne, h1, h2]
  rw [hm] at hbr
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun F : T.V →L[ℂ] T.V => F x) hbr
  have e : ∀ A B : T.V →L[ℂ] T.V, (A * B) x = A (B x) := fun _ _ => rfl
  simp only [_root_.sub_apply, e, map_sub] at hx
  simp only [kunits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  rw [hx]
  split_ifs <;> simp

end ReciprocityTheory.ChartRestriction.DS.HW
