import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.WUN

open Formalism.QuantumDeterminants
open Formalism.MainNotions.S (haarLie lieE lieOf unrealify realifyFun)

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0

section ExpD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at h`. Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)`. Use `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h` as an intermediate fact. Simplify using `only [Complex.coe_smul]`.

Conclude with `this`.
-/
theorem exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [Complex.coe_smul]
  exact this

/- English proof (translation)
Establish `: HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ)) (fun i j => X i j) 0`. Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Rewrite using `[hasDerivAt_pi]`. Introduce `j`.

Apply the tactic sequence `exact exp_entry X i j`. Conclude with `this`.
-/
theorem exp_deriv (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ)) (fun i j => X i j) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X i j
  exact this

def mulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

def mulR (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)

end ExpD

section Grp

variable {k r : ℕ}

/- English proof (translation)
Establish `h` using `(hpkFacts k r).2.1`. Establish `: (Hpk k r).det * (Hpk k r).det = 1` using `by rw [← Matrix.det_mul, h, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ this`.
-/
theorem Hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := (hpkFacts k r).2.1
  have : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ this

/- English proof (translation)
The claim follows from `(uHGroup _ _ (Hpk_unit k r)).2.1 a ha b hb`.
-/
theorem UH_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) :=
  (uHGroup _ _ (Hpk_unit k r)).2.1 a ha b hb
/- English proof (translation)
The claim follows from `((uHGroup _ _ (Hpk_unit k r)).2.2 a ha).2`.
-/
theorem UH_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) :=
  ((uHGroup _ _ (Hpk_unit k r)).2.2 a ha).2
/- English proof (translation)
The claim follows from `((uHGroup _ _ (Hpk_unit k r)).2.2 a ha).1`.
-/
theorem UH_det {a : Mx k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det :=
  ((uHGroup _ _ (Hpk_unit k r)).2.2 a ha).1

/- English proof (translation)
Establish `hH2` using `(hpkFacts k r).2.1`. Establish `hinv : (Hpk k r)⁻¹ = Hpk k r` using `Matrix.inv_eq_right_inv hH2`. Establish `hXs : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹`. Rewrite using `[hinv]`. Establish `h1 : Xᴴ * Hpk k r = -(Hpk k r * X)` using `eq_neg_of_add_eq_zero_left hX`.

Combine the equalities or inequalities in the displayed calculation. Use `show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs]`. Establish `hst : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`. Rewrite using `[hst]`.

Establish `e1 : (t : ℂ) • (Hpk k r * (-X) * (Hpk k r)⁻¹) = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹`. Simplify using the standard rewrite rules. Rewrite using `[e1, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (Hpk_unit k r)), hinv]`. Establish `e2 : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left)]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by`. Rewrite using `[hH2, Matrix.mul_one, Matrix.mul_assoc]`.

Use `_ = Hpk k r := by rw [e2, Matrix.mul_one]`.
-/
theorem exp_mem_UH {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  have hH2 := (hpkFacts k r).2.1
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv hH2
  have hXs : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [hinv]
    have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * (Hpk k r * Hpk k r) := by rw [hH2, Matrix.mul_one]
      _ = (Xᴴ * Hpk k r) * Hpk k r := by rw [Matrix.mul_assoc]
      _ = Hpk k r * (-X) * Hpk k r := by rw [h1]; simp
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs]
  have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [hst]
  have e1 : (t : ℂ) • (Hpk k r * (-X) * (Hpk k r)⁻¹) = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
    simp
  rw [e1, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (Hpk_unit k r)), hinv]
  have e2 : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left)]
    simp
  calc Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * Hpk k r * Hpk k r * NormedSpace.exp ((t : ℂ) • X)
      = Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r * Hpk k r) * NormedSpace.exp ((t : ℂ) • X) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [hH2, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hpk k r := by rw [e2, Matrix.mul_one]

end Grp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def InA (k r : ℕ) (X : Mx k r) : Prop :=
  (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (eI k r a) = 0) ∧
    ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → X i j = 0

def InLieN (k r : ℕ) (X : Mx k r) : Prop := InLieHpk k r X ∧ InA k r X

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a i hai`. Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`.

Distinguish the cases in `hl : a.val ≤ l.val`. Rewrite using `[hY.1 a l hl, mul_zero]`. Establish `hl' : l.val < r` using `by have := a.2; omega`. Establish `: l = eI k r ⟨l.val, hl'⟩` using `rfl`. Rewrite using `[this, hX.1 ⟨l.val, hl'⟩ i (by simp only; omega), zero_mul]`.

Introduce `i j h1 h2 h3`. Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : r ≤ l.val`.

Rewrite using `[hY.2 l j h1 h2 hl, mul_zero]`. Establish `hl' : l.val < r` using `by omega`. Establish `: l = eI k r ⟨l.val, hl'⟩` using `rfl`. Rewrite using `[this, hX.1 ⟨l.val, hl'⟩ i (by simp only; omega), zero_mul]`.
-/
theorem InA.mul {X Y : Mx k r} (hX : InA k r X) (hY : InA k r Y) : InA k r (X * Y) := by
  constructor
  · intro a i hai
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : a.val ≤ l.val
    · rw [hY.1 a l hl, mul_zero]
    · have hl' : l.val < r := by have := a.2; omega
      have : l = eI k r ⟨l.val, hl'⟩ := rfl
      rw [this, hX.1 ⟨l.val, hl'⟩ i (by simp only; omega), zero_mul]
  · intro i j h1 h2 h3
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : r ≤ l.val
    · rw [hY.2 l j h1 h2 hl, mul_zero]
    · have hl' : l.val < r := by omega
      have : l = eI k r ⟨l.val, hl'⟩ := rfl
      rw [this, hX.1 ⟨l.val, hl'⟩ i (by simp only; omega), zero_mul]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hX`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul hX`.
-/
theorem InA.pow {X : Mx k r} (hX : InA k r X) : ∀ n : ℕ, InA k r (X ^ (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [pow_succ]; exact ih.mul hX

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Establish `h` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X`. Set `L : Mx k r →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)`. Use `L.hasSum h` as an intermediate fact. Conclude with `this`.
-/
theorem exp_entry_hasSum (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) ((NormedSpace.exp X) i j) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  let L : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have := L.hasSum h
  exact this

/- English proof (translation)
Establish `h1` using `exp_entry_hasSum X i j`. Establish `h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) (((Nat.factorial 0 : ℂ)⁻¹) * (X ^ 0) i j)`. Apply `hasSum_single 0` to reduce the goal to its premises. Introduce `n hn`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn`.

Rewrite using `[h m, mul_zero]`. Rewrite using `[h1.unique h2]`. Simplify using `[Matrix.one_apply]`.
-/
theorem exp_entry_of_InA {X : Mx k r} (i j : Fin (2 * r + k + 1)) (h : ∀ n : ℕ, (X ^ (n + 1)) i j = 0) :
    (NormedSpace.exp X) i j = if i = j then 1 else 0 := by
  have h1 := exp_entry_hasSum X i j
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) (((Nat.factorial 0 : ℂ)⁻¹) * (X ^ 0) i j) := by
    apply hasSum_single 0
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [h m, mul_zero]
  rw [h1.unique h2]
  simp [Matrix.one_apply]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `exp_mem_UH hX.1 1` as an intermediate fact. Simplify using `using this`. Introduce `a i hai`. Conclude with `exp_entry_of_InA i _ (fun n => (hX.2.pow n).1 a i hai)`.

Introduce `i j h1 h2 h3`. Conclude with `exp_entry_of_InA i j (fun n => (hX.2.pow n).2 i j h1 h2 h3)`.
-/
theorem exp_mem_N {X : Mx k r} (hX : InLieN k r X) : NormedSpace.exp X ∈ Nset k r := by
  refine ⟨?_, ?_, ?_⟩
  · have := exp_mem_UH hX.1 1
    simpa using this
  · intro a i hai
    exact exp_entry_of_InA i _ (fun n => (hX.2.pow n).1 a i hai)
  · intro i j h1 h2 h3
    exact exp_entry_of_InA i j (fun n => (hX.2.pow n).2 i j h1 h2 h3)

/- English proof (translation)
Establish `hent : ∀ (i j : Fin (2 * r + k + 1)) (c : ℂ), (∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X)) i j = c) → X i j = 0`. Introduce `i j c hc`. Apply the tactic sequence `have h1 := exp_entry X i j`. Establish `h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) 0 0`. Establish `: (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun _ => c` using `funext hc`.

Rewrite using `[this]`. Conclude with `hasDerivAt_const _ _`. Conclude with `h1.unique h2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hH2` using `(hpkFacts k r).2.1`.

Establish `hf : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) Xᴴ 0` using `exp_deriv _`. Establish `hg : HasDerivAt (fun t : ℝ => Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r) (Hpk k r * (-X) * Hpk k r) 0` using `(mulR (Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((mulL (Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (exp_deriv (-X)))`. Establish `hfg : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) = fun t : ℝ => Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r`. Use function extensionality and compare the values at `t`. Establish `hU : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r` using `(hX t).1`.

Establish `hst : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`. Rewrite `hU` using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hst]`. Establish `e2 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1`. Rewrite using `[smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right)]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, Matrix.mul_one, Matrix.mul_assoc, hH2, Matrix.mul_one]`. Use `_ = (NormedSpace.exp ((t : ℂ) • Xᴴ) * Hpk k r * NormedSpace.exp ((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r := by simp only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hU]`. Rewrite `hf` using `[hfg]`.

Establish `e` using `hf.unique hg`. Use `show Xᴴ * Hpk k r + Hpk k r * X = 0`. Rewrite using `[e, Matrix.mul_assoc, hH2]`. Simplify using the standard rewrite rules. Introduce `a i hai`.

Conclude with `hent i _ _ (fun t => (hX t).2.1 a i hai)`. Introduce `i j h1 h2 h3`. Conclude with `hent i j _ (fun t => (hX t).2.2 i j h1 h2 h3)`.
-/
theorem lieN_of_lieOf {X : Mx k r} (hX : X ∈ lieOf (Nset k r)) : InLieN k r X := by
  have hent : ∀ (i j : Fin (2 * r + k + 1)) (c : ℂ), (∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X)) i j = c) → X i j = 0 := by
    intro i j c hc
    have h1 := exp_entry X i j
    have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) 0 0 := by
      have : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun _ => c := funext hc
      rw [this]; exact hasDerivAt_const _ _
    exact h1.unique h2
  refine ⟨?_, ?_, ?_⟩
  · have hH2 := (hpkFacts k r).2.1
    have hf : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) Xᴴ 0 := exp_deriv _
    have hg : HasDerivAt (fun t : ℝ => Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r)
        (Hpk k r * (-X) * Hpk k r) 0 :=
      (mulR (Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((mulL (Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (exp_deriv (-X)))
    have hfg : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) =
        fun t : ℝ => Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Hpk k r := by
      funext t
      have hU : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r := (hX t).1
      have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hst] at hU
      have e2 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1 := by
        rw [smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right)]
        simp
      calc NormedSpace.exp ((t : ℂ) • Xᴴ)
          = NormedSpace.exp ((t : ℂ) • Xᴴ) * Hpk k r * (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)))
              * Hpk k r := by
            rw [e2, Matrix.mul_one, Matrix.mul_assoc, hH2, Matrix.mul_one]
        _ = (NormedSpace.exp ((t : ℂ) • Xᴴ) * Hpk k r * NormedSpace.exp ((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • (-X))
              * Hpk k r := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU]
    rw [hfg] at hf
    have e := hf.unique hg
    show Xᴴ * Hpk k r + Hpk k r * X = 0
    rw [e, Matrix.mul_assoc, hH2]
    simp
  · intro a i hai
    exact hent i _ _ (fun t => (hX t).2.1 a i hai)
  · intro i j h1 h2 h3
    exact hent i j _ (fun t => (hX t).2.2 i j h1 h2 h3)

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0`. Establish `h1 : Xᴴ * Hpk k r + Hpk k r * X = 0` using `hX.1`. Establish `h2 : Yᴴ * Hpk k r + Hpk k r * Y = 0` using `hY.1`. Rewrite using `[Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `a i hai`. Rewrite using `[Matrix.add_apply, hX.2.1 a i hai, hY.2.1 a i hai, add_zero]`. Introduce `i j h1 h2 h3`. Rewrite using `[Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]`.
-/
theorem InLieN.add {X Y : Mx k r} (hX : InLieN k r X) (hY : InLieN k r Y) : InLieN k r (X + Y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    have h1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX.1
    have h2 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY.1
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · intro a i hai
    rw [Matrix.add_apply, hX.2.1 a i hai, hY.2.1 a i hai, add_zero]
  · intro i j h1 h2 h3
    rw [Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ((c : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((c : ℂ) • X) = 0`. Establish `h1 : Xᴴ * Hpk k r + Hpk k r * X = 0` using `hX.1`. Establish `hst : star (c : ℂ) = (c : ℂ)` using `Complex.conj_ofReal c`. Rewrite using `[Matrix.conjTranspose_smul, hst, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]`.

Introduce `a i hai`. Rewrite using `[Matrix.smul_apply, hX.2.1 a i hai, smul_zero]`. Introduce `i j h1 h2 h3`. Rewrite using `[Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]`.
-/
theorem InLieN.smul {X : Mx k r} (hX : InLieN k r X) (c : ℝ) : InLieN k r ((c : ℂ) • X) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((c : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((c : ℂ) • X) = 0
    have h1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX.1
    have hst : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    rw [Matrix.conjTranspose_smul, hst, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · intro a i hai
    rw [Matrix.smul_apply, hX.2.1 a i hai, smul_zero]
  · intro i j h1 h2 h3
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (0 : Mx k r)ᴴ * Hpk k r + Hpk k r * 0 = 0`. Simplify using the standard rewrite rules. Introduce `a i _`. Both sides reduce to the same expression.

Introduce `i j _ _ _`. Both sides reduce to the same expression.
-/
theorem InLieN.zero : InLieN k r (0 : Mx k r) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : Mx k r)ᴴ * Hpk k r + Hpk k r * 0 = 0
    simp
  · intro a i _; rfl
  · intro i j _ _ _; rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify, realifyFun]`.
-/
theorem unrealify_realify (X : Mx k r) : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
theorem unrealify_add (x y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Unfold `lieE at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨X, hX, rfl⟩` from `h`. Simplify using `only`.

Rewrite using `[unrealify_realify]`. Conclude with `lieN_of_lieOf hX`. Consider the case `zero`. Establish `: unrealify (0 : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) = (0 : Mx k r)`. Use extensionality with `i j`.

Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`. Rewrite using `[this]`. Conclude with `InLieN.zero`. Consider the case `add x y _ _ hx hy => rw [unrealify_add]`. Conclude with `hx.add hy`.

Consider the case `smul c x _ hx => rw [unrealify_smul]`. Conclude with `hx.smul c`.
-/
theorem lieN_of_lieE (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))
    (hx : x ∈ lieE (Nset k r)) : InLieN k r (unrealify x) := by
  unfold lieE at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨X, hX, rfl⟩ := h
    simp only
    rw [unrealify_realify]
    exact lieN_of_lieOf hX
  | zero =>
    have : unrealify (0 : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) = (0 : Mx k r) := by
      ext i j
      apply Complex.ext <;> simp [unrealify]
    rw [this]; exact InLieN.zero
  | add x y _ _ hx hy => rw [unrealify_add]; exact hx.add hy
  | smul c x _ hx => rw [unrealify_smul]; exact hx.smul c

/- English proof (translation)
Establish `hc : Continuous (fun x : Mx k r => xᴴ * Hpk k r * x)` using `by fun_prop`. Conclude with `isClosed_eq hc continuous_const`.
-/
theorem isClosed_UH (k r : ℕ) : IsClosed (UH (Hpk k r)) := by
  have hc : Continuous (fun x : Mx k r => xᴴ * Hpk k r * x) := by fun_prop
  exact isClosed_eq hc continuous_const

/- English proof (translation)
Establish `h1 : IsClosed {g : Mx k r | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}`. Simplify using `only [Set.ofPred_forall]`. Use `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_id.matrix_elem _ _) continuous_const`. Establish `h2 : IsClosed {g : Mx k r | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → g i j = if i = j then 1 else 0}`.

Simplify using `only [Set.ofPred_forall]`. Use `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_id.matrix_elem _ _) continuous_const`. Conclude with `(isClosed_UH k r).inter (h1.inter h2)`.
-/
theorem isClosed_N (k r : ℕ) : IsClosed (Nset k r) := by
  have h1 : IsClosed {g : Mx k r | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have h2 : IsClosed {g : Mx k r | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  exact (isClosed_UH k r).inter (h1.inter h2)

/- English proof (translation)
Establish `h1 : IsClosed {g : Mx k r | ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}`. Simplify using `only [Set.ofPred_forall, Set.ofPred_and]`. Use `isClosed_iInter fun a => IsClosed.inter ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`. Conclude with `isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`.

Establish `h2 : IsClosed {g : Mx k r | g *ᵥ z = z}` using `isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`. Conclude with `(isClosed_UH k r).inter (h1.inter h2)`.
-/
theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have h1 : IsClosed {g : Mx k r | ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    refine isClosed_iInter fun a => IsClosed.inter ?_ ?_
    · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  have h2 : IsClosed {g : Mx k r | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact (isClosed_UH k r).inter (h1.inter h2)

/- English proof (translation)
The claim follows from `continuous_id`.
-/
theorem continuous_of : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id

def unrealL (k r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) →ₗ[ℝ] Mx k r where
  toFun := unrealify
  map_add' := unrealify_add
  map_smul' := by
    intro c x
    rw [unrealify_smul]
    exact Complex.coe_smul c _

open scoped Matrix.Norms.Operator in
/- English proof (translation)
The claim follows from `NormedSpace.exp_continuous`.
-/
theorem continuous_expM : Continuous (fun X : Mx k r => NormedSpace.exp X) := NormedSpace.exp_continuous

/- English proof (translation)
Establish `h1 : Continuous (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x)` using `(unrealL k r).continuous_of_finiteDimensional`. Establish `h0 : Continuous (fun x : lieE S => (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)))` using `continuous_subtype_val`. Establish `h2 : Continuous (fun x : lieE S => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) : Mx k r))`. Establish `h3 : Continuous (fun x : lieE S => (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) : Mx k r))`. Conclude with `Continuous.comp (g := fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x) h1 h0`.

Conclude with `Continuous.comp (g := fun X : Mx k r => NormedSpace.exp X) continuous_expM h3`. Conclude with `h2`.
-/
theorem continuous_expLie (S : Set (Mx k r)) :
    Continuous (fun x : lieE S => (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) := by
  have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x) :=
    (unrealL k r).continuous_of_finiteDimensional
  have h0 : Continuous (fun x : lieE S =>
      (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) := continuous_subtype_val
  have h2 : Continuous (fun x : lieE S => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) : Mx k r)) :=
    by
      have h3 : Continuous (fun x : lieE S => (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) : Mx k r)) := by
        exact Continuous.comp (g := fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x) h1 h0
      exact Continuous.comp (g := fun X : Mx k r => NormedSpace.exp X) continuous_expM h3
  exact h2

/- English proof (translation)
Establish `hs : MeasurableSet {x : Mt k r | Matrix.of x ∉ Nset k r}` using `(((isClosed_N k r).preimage continuous_of).measurableSet).compl`. Unfold `haarLie`. Rewrite using `[Measure.smul_apply, Measure.map_apply (continuous_expLie _).measurable hs]`. Establish `: (fun x : lieE (Nset k r) => (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} = ∅`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]`. Conclude with `exp_mem_N (lieN_of_lieE _ x.2)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem muN_conc (κ : ENNReal) : (haarLie (Nset k r) κ) {x : Mt k r | Matrix.of x ∉ Nset k r} = 0 := by
  have hs : MeasurableSet {x : Mt k r | Matrix.of x ∉ Nset k r} :=
    (((isClosed_N k r).preimage continuous_of).measurableSet).compl
  unfold haarLie
  rw [Measure.smul_apply, Measure.map_apply (continuous_expLie _).measurable hs]
  have : (fun x : lieE (Nset k r) => (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) ⁻¹'
      {x : Mt k r | Matrix.of x ∉ Nset k r} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact exp_mem_N (lieN_of_lieE _ x.2)
  rw [this]
  simp

instance (S : Set (Mx k r)) (κ : ENNReal) : SFinite (haarLie S κ) := by
  unfold haarLie
  infer_instance

end PI.WUN
