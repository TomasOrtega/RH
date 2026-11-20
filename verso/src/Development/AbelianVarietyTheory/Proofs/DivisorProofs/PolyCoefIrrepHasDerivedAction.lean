import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Matrix

namespace GlobalTheory.PsCo.PcEF.PolynomialCoefficientDerivedAction

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Introduce and unpack `⟨c, hc, he⟩`. Set `ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ` to `{ toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j map_add' := by`. Introduce `f g`. Simplify using `[mul_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`.

Introduce `r f`. Simplify using `[Finset.mul_sum, mul_left_comm] }`. Establish `hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ)`. Introduce `x`. Simplify using `[ψ, Pi.single_apply]`.

Establish `hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1`. Normalize the expressions using the abelian group laws. Rewrite `he` using `[hl]`. Establish `h` using `congrArg ψ he`. Simplify using `only [map_sum, map_smul, Formalism.REAL.root, map_sub, hψ, smul_eq_mul] at h`.

Establish `hr : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0`. Use `Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : c x y = 0`. Simplify using `[h0]`. Establish `hxy` using `(hc x y h0).1`.

Establish `: ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ)` using `by exact_mod_cast hxy`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)`. Establish `hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma not_cdom {Λ : Fin n → ℝ} {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + Pi.single a 1 - Pi.single b 1) Λ := by
  rintro ⟨c, hc, he⟩
  let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
      map_add' := by
        intro f g
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        simp [Finset.mul_sum, mul_left_comm] }
  have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
    intro x
    simp [ψ, Pi.single_apply]
  have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
    abel
  rw [hl] at he
  have h := congrArg ψ he
  simp only [map_sum, map_smul, Formalism.REAL.root, map_sub, hψ, smul_eq_mul] at h
  have hr : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy := (hc x y h0).1
      have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

section Der

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : KG ε →* unitary (H →L[ℂ] H))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0)
  (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
  (hσ : ∀ g : KG ε, σ (toMK g) = ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))

include hder in

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve ε hY`. Establish `hY'` using `inK_conj' g hY`. Use `set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((g : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)`. Establish `hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK g)` using `toMK_inv' g`. Establish `hγ' : ∀ t : ℝ, toMK (g * γ t * g⁻¹) = NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g)))`.

Introduce `t`. Establish `e1 : toMK (g * γ t * g⁻¹) = toMK g * toMK (γ t) * toMK g⁻¹` using `rfl`. Rewrite using `[e1, toMK_inv', hγ t, ← hU]`. Establish `e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.

Rewrite using `[e2, Matrix.exp_units_conj]`. Establish `h1` using `hder _ hY' _ hγ'`. Use `set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)`. Establish `h2` using `(((ContinuousLinearMap.mul ℂ (H →L[ℂ] H) A).comp ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip (star A))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder _ hY γ hγ)`. Establish `hf : (fun t => ((τ (g * γ t * g⁻¹) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) = fun t => A * ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * star A`.

Use function extensionality and compare the values at `t`. Rewrite using `[map_mul, map_mul, map_inv]`. Both sides reduce to the same expression. Rewrite `h1` using `[hf]`. Establish `h3` using `h2.unique (by simpa [Function.comp_def, mul_assoc] using h1)`.

Simplify `h3` using `[mul_assoc]`.
-/
lemma conj (g : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Y * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Y * star (toMK g)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' g hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((g : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK g) :=
    toMK_inv' g
  have hγ' : ∀ t : ℝ, toMK (g * γ t * g⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
    intro t
    have e1 : toMK (g * γ t * g⁻¹) = toMK g * toMK (γ t) * toMK g⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  have h1 := hder _ hY' _ hγ'
  set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have h2 := (((ContinuousLinearMap.mul ℂ (H →L[ℂ] H) A).comp
      ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip (star A))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hder _ hY γ hγ)
  have hf : (fun t => ((τ (g * γ t * g⁻¹) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) =
      fun t => A * ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * star A := by
    funext t
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [hf] at h1
  have h3 := h2.unique (by simpa [Function.comp_def, mul_assoc] using h1)
  simpa [mul_assoc] using h3

include hder in

/- English proof (translation)
Rewrite using `[single_eq_kp a b]`. Establish `e : toMK g * (kp1 a b + Complex.I • kp2 a b) * star (toMK g) = toMK g * kp1 a b * star (toMK g) + Complex.I • (toMK g * kp2 a b * star (toMK g))`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[e, map_add, map_smul, map_add, map_smul, ← conj τ dτ hder g (inK_hermitian_unit hab), ← conj τ dτ hder g (inK_skew_hermitian_unit hab), mul_add, add_mul, mul_smul_comm, smul_mul_assoc]`.
-/
lemma conj_single (g : KG ε) {a b : Fin n} (hab : ε a = ε b) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ (Matrix.single a b 1) *
      star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Matrix.single a b 1 * star (toMK g)) := by
  rw [single_eq_kp a b]
  have e : toMK g * (kp1 a b + Complex.I • kp2 a b) * star (toMK g) =
      toMK g * kp1 a b * star (toMK g) + Complex.I • (toMK g * kp2 a b * star (toMK g)) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, map_add, map_smul, map_add, map_smul, ← conj τ dτ hder g (inK_hermitian_unit hab),
    ← conj τ dτ hder g (inK_skew_hermitian_unit hab), mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

include hder hσ in

/- English proof (translation)
Use `set d : Fin n → ℂ := fun b => if b = a then Complex.I else 0 with hddef`. Establish `hd : ∀ b, star (d b) = -d b` using `fun b => by`. Apply the tactic sequence `simp only [d]; split_ifs <;> simp`. Establish `hX` using `torep_inK_diag ε d hd`. Use `set γ := onepCurve ε hX with hγdef`.

Establish `hD : ∀ t : ℝ, toMK (γ t) = Matrix.diagonal (fun b => Complex.exp (((if b = a then t else 0 : ℝ) : ℂ) * Complex.I))`. Introduce `t`. Rewrite using `[toMK_onepCurve, ← Matrix.diagonal_smul, torep_exp_diag]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Simplify using `only [d, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hval : ∀ t : ℝ, ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v = Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v`. Introduce `t`. Rewrite using `[← hσ, hD t, hv _ (by rw [← hD t]; exact (γ t).2)]`.

Establish `hs : (∑ b, μ b * (if b = a then t else 0)) = μ a * t`. Simplify using `[Finset.sum_ite_eq']`. Rewrite using `[hs]`. Establish `h1 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) (dτ (Matrix.diagonal d) v) 0`. Use `((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder _ hX γ (toMK_onepCurve _ hX))` as an intermediate fact.

Simplify `this` using `[Function.comp_def]`. Establish `h2 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) (((μ a : ℂ) * Complex.I) • v) 0`. Rewrite using `[show (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) = fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v from funext hval]`. Establish `h3 : HasDerivAt (fun t : ℝ => (((μ a * t : ℝ) : ℂ) * Complex.I)) ((μ a : ℂ) * Complex.I) 0`. Use `(((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp).mul_const Complex.I` as an intermediate fact.

Simplify using `using this`. Use `(h3.cexp).smul_const v` as an intermediate fact. Simplify using `using this`. Establish `heq` using `h1.unique h2`. Establish `hdX : dτ (Matrix.diagonal d) = Complex.I • dτ (Matrix.single a a 1)`.

Rewrite using `[torep_diag_sum, Finset.sum_eq_single a (fun b _ hb => by simp [d, hb]) (by simp), map_smul]`. Simplify using `[d]`. Rewrite `heq` using `[hdX, _root_.smul_apply, mul_comm, mul_smul]`. Conclude with `smul_right_injective _ Complex.I_ne_zero heq`.
-/
lemma dτ_of_wt {μ : Fin n → ℝ} {v : H}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a : Fin n) :
    dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  set d : Fin n → ℂ := fun b => if b = a then Complex.I else 0 with hddef
  have hd : ∀ b, star (d b) = -d b := fun b => by
    simp only [d]; split_ifs <;> simp
  have hX := torep_inK_diag ε d hd
  set γ := onepCurve ε hX with hγdef
  have hD : ∀ t : ℝ, toMK (γ t) =
      Matrix.diagonal (fun b => Complex.exp (((if b = a then t else 0 : ℝ) : ℂ) * Complex.I)) := by
    intro t
    rw [toMK_onepCurve, ← Matrix.diagonal_smul, torep_exp_diag]
    congr 1
    funext b
    simp only [d, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hval : ∀ t : ℝ, ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v =
      Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := by
    intro t
    rw [← hσ, hD t, hv _ (by rw [← hD t]; exact (γ t).2)]
    have hs : (∑ b, μ b * (if b = a then t else 0)) = μ a * t := by
      simp [Finset.sum_ite_eq']
    rw [hs]
  have h1 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v)
      (dτ (Matrix.diagonal d) v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hder _ hX γ (toMK_onepCurve _ hX))
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v)
      (((μ a : ℂ) * Complex.I) • v) 0 := by
    rw [show (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) =
      fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v from funext hval]
    have h3 : HasDerivAt (fun t : ℝ => (((μ a * t : ℝ) : ℂ) * Complex.I)) ((μ a : ℂ) * Complex.I) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp).mul_const Complex.I
      simpa using this
    have := (h3.cexp).smul_const v
    simpa using this
  have heq := h1.unique h2
  have hdX : dτ (Matrix.diagonal d) = Complex.I • dτ (Matrix.single a a 1) := by
    rw [torep_diag_sum, Finset.sum_eq_single a (fun b _ hb => by simp [d, hb]) (by simp), map_smul]
    simp [d]
  rw [hdX, _root_.smul_apply, mul_comm, mul_smul] at heq
  exact smul_right_injective _ Complex.I_ne_zero heq

include hder hσ in

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `not_cdom hab (hK5 _ _ Submodule.mem_top hx ?_)` and prove the remaining obligations. Introduce `θ hθ`. Use `set g := torepK ε hθ`. Use `set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)`.

Establish `hk : σ (Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I))) = A` using `hσ g`. Establish `hAA : star A * A = 1` using `Unitary.coe_star_mul_self _`. Establish `hwA : A w = Complex.exp (((∑ c, Λ c * θ c : ℝ) : ℂ) * Complex.I) • w`. Rewrite using `[← hk]`. Conclude with `hw θ hθ`.

Establish `key : A * dτ (Matrix.single a b 1) = (A * dτ (Matrix.single a b 1) * star A) * A`. Rewrite using `[mul_assoc (A * dτ (Matrix.single a b 1)), hAA, mul_one]`. Rewrite using `[hk, show A (dτ (Matrix.single a b 1) w) = (A * dτ (Matrix.single a b 1)) w from rfl, key, show (A * dτ (Matrix.single a b 1) * star A * A) w = (A * dτ (Matrix.single a b 1) * star A) (A w) from rfl, conj_single τ dτ hder g hε, hwA, show toMK g = Matrix.diagonal (fun c => Complex …`. Use `congr 1`. Establish `hs : (∑ c, (Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c * θ c) = (∑ c, Λ c * θ c) + θ a - θ b`.

Simplify using `[add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, ite_mul]`. Establish `hst : star (Complex.exp ((θ b : ℂ) * Complex.I)) = Complex.exp (-((θ b : ℂ) * Complex.I))`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]`. Rewrite using `[hs, hst, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hw {Λ : Fin n → ℝ}
    (hK5 : ∀ (μ : Fin n → ℝ) (v : H), v ∈ (⊤ : Submodule ℂ H) → v ≠ 0 →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ v → Formalism.MainNotions.S.CDom ε μ Λ)
    {w : H} (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ Λ w) (a b : Fin n) (hab : a < b)
    (hε : ε a = ε b) : dτ (Matrix.single a b 1) w = 0 := by
  by_contra hx
  refine not_cdom hab (hK5 _ _ Submodule.mem_top hx ?_)
  intro θ hθ
  set g := torepK ε hθ
  set A : H →L[ℂ] H := ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have hk : σ (Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I))) = A := hσ g
  have hAA : star A * A = 1 := Unitary.coe_star_mul_self _
  have hwA : A w = Complex.exp (((∑ c, Λ c * θ c : ℝ) : ℂ) * Complex.I) • w := by
    rw [← hk]
    exact hw θ hθ
  have key : A * dτ (Matrix.single a b 1) = (A * dτ (Matrix.single a b 1) * star A) * A := by
    rw [mul_assoc (A * dτ (Matrix.single a b 1)), hAA, mul_one]
  rw [hk, show A (dτ (Matrix.single a b 1) w) = (A * dτ (Matrix.single a b 1)) w from rfl, key,
    show (A * dτ (Matrix.single a b 1) * star A * A) w = (A * dτ (Matrix.single a b 1) * star A) (A w) from rfl,
    conj_single τ dτ hder g hε, hwA,
    show toMK g = Matrix.diagonal (fun c => Complex.exp ((θ c : ℂ) * Complex.I)) from rfl, fh_diag_conj,
    map_smul, map_smul, _root_.smul_apply, smul_smul]
  congr 1
  have hs : (∑ c, (Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c * θ c) = (∑ c, Λ c * θ c) + θ a - θ b := by
    simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, ite_mul]
  have hst : star (Complex.exp ((θ b : ℂ) * Complex.I)) = Complex.exp (-((θ b : ℂ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [hs, hst, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Der

end GlobalTheory.PsCo.PcEF.PolynomialCoefficientDerivedAction

namespace GlobalTheory.PsCo.PcEF

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

/- English proof (translation)
Introduce `n ε γ W _ _ _ T hT _`. Take `⟨-, hU, hK⟩` from `hT`. Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Take `⟨τ, hτc, hτ⟩` from `uRepHom n ε W T hU`. Take `⟨dτ, hder⟩` from `derivExists n ε W τ hτc`.

Establish `hσ : ∀ g : KG ε, T (toMK g) = ((τ g : unitary (W →L[ℂ] W)) : W →L[ℂ] W)` using `fun g => (hτ g).symm`. Take `⟨v0, -, hv0, hwt0⟩` from `hK.2.2.2.1`. Establish `hn : ‖v0‖ ≠ 0` using `norm_ne_zero_iff.2 hv0`. Use `set w : W := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hwdef`. Establish `hwn : ‖w‖ = 1`.

Rewrite using `[hwdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]`. Establish `hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T γ w`. Introduce `θ hθ`. Rewrite using `[hwdef, map_smul, hwt0 θ hθ, smul_comm]`. Use `⟨KType.mk (V := W) τ hτc ?_ dτ hder w hwn (fun a => PolynomialCoefficientDerivedAction.dτ_of_wt τ dτ hder T hσ hwt a) (fun a b hab he => PolynomialCoefficientDerivedAction.hw τ dτ hder T hσ hK.2.2.2.2 hwt a b hab he), fun k => ?_⟩` and prove the remaining obligations.

Introduce `S hS`. Use `hK.2.2.1 S le_top (fun g hg v hv => ?_)` and prove the remaining obligations. Establish `h` using `hS (torepK ε hg) v hv`. Rewrite `h` using `[← hσ]`. Conclude with `h`.

Use `show LinearMap.trace ℂ W ((((τ k : unitary (W →L[ℂ] W)) : W →L[ℂ] W)) : W →ₗ[ℂ] W) = trK T (toMK k)`. Rewrite using `[← hσ]`. Both sides reduce to the same expression.
-/
theorem polyCoefIrrep_hasDerivedAction : ToKType := by
  intro n ε γ W _ _ _ T hT _
  obtain ⟨-, hU, hK⟩ := hT
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨τ, hτc, hτ⟩ := uRepHom n ε W T hU
  obtain ⟨dτ, hder⟩ := derivExists n ε W τ hτc
  have hσ : ∀ g : KG ε, T (toMK g) = ((τ g : unitary (W →L[ℂ] W)) : W →L[ℂ] W) := fun g => (hτ g).symm
  obtain ⟨v0, -, hv0, hwt0⟩ := hK.2.2.2.1
  have hn : ‖v0‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  set w : W := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hwdef
  have hwn : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T γ w := by
    intro θ hθ
    rw [hwdef, map_smul, hwt0 θ hθ, smul_comm]
  refine ⟨KType.mk (V := W) τ hτc ?_ dτ hder w hwn
    (fun a => PolynomialCoefficientDerivedAction.dτ_of_wt τ dτ hder T hσ hwt a)
    (fun a b hab he => PolynomialCoefficientDerivedAction.hw τ dτ hder T hσ hK.2.2.2.2 hwt a b hab he), fun k => ?_⟩
  · intro S hS
    refine hK.2.2.1 S le_top (fun g hg v hv => ?_)
    have h := hS (torepK ε hg) v hv
    rw [← hσ] at h
    exact h
  · show LinearMap.trace ℂ W ((((τ k : unitary (W →L[ℂ] W)) : W →L[ℂ] W)) : W →ₗ[ℂ] W) = trK T (toMK k)
    rw [← hσ]
    rfl

end GlobalTheory.PsCo.PcEF

end
end
