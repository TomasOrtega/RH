import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RowSpan

open MvPolynomial Formalism.L2.Pj

variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

def rowAct (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => ∑ j, C (g ℓ.1 ℓ.2.1 j) * X ⟨ℓ.1, j, ℓ.2.2⟩

/- English proof (translation)
The claim follows from `aeval_X _ _`.
-/
theorem rowAct_X (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) (ℓ : Letter T r n) :
    rowAct g (X ℓ) = ∑ j, C (g ℓ.1 ℓ.2.1 j) * X ⟨ℓ.1, j, ℓ.2.2⟩ := aeval_X _ _

def RowStable (U : Submodule k (MvPolynomial (Letter T r n) k)) : Prop :=
  ∀ g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k, (∀ σ, IsUnit (g σ).det) → ∀ P ∈ U, rowAct g P ∈ U

/- English proof (translation)
Establish `hX : ∀ ℓ : Letter T r n, pderiv (⟨σ, j, b⟩ : Letter T r n) (rowAct g (X ℓ)) = ∑ i, g σ i j • rowAct g (pderiv (⟨σ, i, b⟩ : Letter T r n) (X ℓ))`. Introduce and unpack `⟨σ', i', b'⟩`. Rewrite using `[rowAct_X, map_sum]`. Simplify using `only [pderiv_C_mul, pderiv_X, Pi.single_apply]`. Distinguish the cases in `h : σ' = σ`.

Substitute `h` using the available equality. Distinguish the cases in `hb : b' = b`. Substitute `hb` using the available equality. Simplify using `[apply_ite, smul_eq_C_mul]`. Simplify using `[hb]`.

Simplify using `[h]`. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C c => simp [rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]`. Consider the case `mul_X p s hp`.

Rewrite using `[map_mul, pderiv_mul, hp, hX]`. Simplify using `only [pderiv_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]`.
-/
theorem pderiv_rowAct (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) (σ : T) (j : Fin (r σ)) (b : Fin n)
    (Q : MvPolynomial (Letter T r n) k) :
    pderiv (⟨σ, j, b⟩ : Letter T r n) (rowAct g Q) =
      ∑ i, g σ i j • rowAct g (pderiv (⟨σ, i, b⟩ : Letter T r n) Q) := by
  classical
  have hX : ∀ ℓ : Letter T r n, pderiv (⟨σ, j, b⟩ : Letter T r n) (rowAct g (X ℓ)) =
      ∑ i, g σ i j • rowAct g (pderiv (⟨σ, i, b⟩ : Letter T r n) (X ℓ)) := by
    rintro ⟨σ', i', b'⟩
    rw [rowAct_X, map_sum]
    simp only [pderiv_C_mul, pderiv_X, Pi.single_apply]
    by_cases h : σ' = σ
    · subst h
      by_cases hb : b' = b
      · subst hb
        simp [apply_ite, smul_eq_C_mul]
      · simp [hb]
    · simp [h]
  induction Q using MvPolynomial.induction_on with
  | C c => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p s hp =>
    rw [map_mul, pderiv_mul, hp, hX]
    simp only [pderiv_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]

/- English proof (translation)
Simplify using `only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Both sides reduce to the same expression.
-/
theorem mem_harmK_iff (cc : T → T) (isX : T → Prop) (P : MvPolynomial (Letter T r n) k) :
    P ∈ harmK r n k cc isX (fun _ => 1) ↔ ∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))),
      ∑ b : Fin n, pderiv (⟨τ, i, b⟩ : Letter T r n) (pderiv (⟨cc τ, i', b⟩ : Letter T r n) P) = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap,
    LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/- English proof (translation)
Introduce `g _ P hP`. Rewrite `hP`, the goal using `[mem_harmK_iff]`. Introduce `τ hτ i i'`. Simplify using `only [pderiv_rowAct, map_sum, Derivation.map_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun j' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum, Finset.sum_comm]`. Simplify using `only [← Finset.smul_sum, ← map_sum, hP τ hτ, map_zero, smul_zero, Finset.sum_const_zero]`.
-/
theorem rowStable_harmK (cc : T → T) (isX : T → Prop) : RowStable (harmK r n k cc isX (fun _ => 1)) := by
  intro g _ P hP
  rw [mem_harmK_iff] at hP ⊢
  intro τ hτ i i'
  simp only [pderiv_rowAct, map_sum, Derivation.map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j' _ => ?_
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.smul_sum, ← map_sum, hP τ hτ, map_zero, smul_zero, Finset.sum_const_zero]

/- English proof (translation)
Introduce `g _ P hP`. Rewrite using `[← sum_homogeneousComponent P, map_sum]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Rewrite `hP`, the goal using `[mem_restrictTotalDegree]`. Establish `h : (rowAct g (homogeneousComponent i P)).IsHomogeneous (1 * i)` using `(homogeneousComponent_isHomogeneous i P).aeval _ fun ℓ => IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k _).C_mul _`.

Use `h.totalDegree_le` as an intermediate fact. Rewrite `hi` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rowStable_degree (D : ℕ) : RowStable (restrictTotalDegree (Letter T r n) k D) := by
  intro g _ P hP
  rw [← sum_homogeneousComponent P, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [mem_restrictTotalDegree] at hP ⊢
  have h : (rowAct g (homogeneousComponent i P)).IsHomogeneous (1 * i) :=
    (homogeneousComponent_isHomogeneous i P).aeval _ fun ℓ =>
      IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k _).C_mul _
  have := h.totalDegree_le
  rw [Finset.mem_range] at hi
  omega

section Fischer

variable {σ : Type}

def fisch : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  (basisMonomials σ ℚ).constr ℚ fun m => ((m.prod fun _ e => e.factorial : ℕ) : ℚ) • lcoeff ℚ m

/- English proof (translation)
Establish `: (monomial m a : MvPolynomial σ ℚ) = a • basisMonomials σ ℚ m` using `by simp [smul_monomial]`. Rewrite using `[this, map_smul, fisch, Module.Basis.constr_basis]`. Simplify using the standard rewrite rules.
-/
theorem fisch_monomial (m : σ →₀ ℕ) (a : ℚ) (Q : MvPolynomial σ ℚ) :
    fisch (monomial m a) Q = a * (((m.prod fun _ e => e.factorial : ℕ) : ℚ) * Q.coeff m) := by
  have : (monomial m a : MvPolynomial σ ℚ) = a • basisMonomials σ ℚ m := by simp [smul_monomial]
  rw [this, map_smul, fisch, Module.Basis.constr_basis]
  simp

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [add_mul, map_add, LinearMap.add_apply, hp, hq]`. Consider the case `monomial m a`. Rewrite using `[X, monomial_mul, mul_one, fisch_monomial, fisch_monomial, coeff_pderiv]`. Establish `: ((m + Finsupp.single v 1).prod fun _ e => e.factorial : ℕ) = (m.prod fun _ e => e.factorial) * (m v + 1)`.

Rewrite using `[← Finsupp.mul_prod_erase' (m + Finsupp.single v 1) v _ (by simp), ← Finsupp.mul_prod_erase' m v _ (by simp), Finsupp.erase_add, Finsupp.erase_single, add_zero]`. Simplify using `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fisch_mul_X (P Q : MvPolynomial σ ℚ) (v : σ) : fisch (P * X v) Q = fisch P (pderiv v Q) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, LinearMap.add_apply, hp, hq]
  | monomial m a =>
    rw [X, monomial_mul, mul_one, fisch_monomial, fisch_monomial, coeff_pderiv]
    have : ((m + Finsupp.single v 1).prod fun _ e => e.factorial : ℕ) =
        (m.prod fun _ e => e.factorial) * (m v + 1) := by
      rw [← Finsupp.mul_prod_erase' (m + Finsupp.single v 1) v _ (by simp),
        ← Finsupp.mul_prod_erase' m v _ (by simp), Finsupp.erase_add, Finsupp.erase_single, add_zero]
      simp [Nat.factorial_succ]
      ring
    rw [this]
    push_cast
    ring

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `: 0 < fisch P P` using `by nth_rewrite 1 [P.as_sum]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_pos (fun m hm => ?_) (support_nonempty.2 h0)` and prove the remaining obligations. Rewrite using `[fisch_monomial, mul_left_comm]`.

Establish `hf : 0 < (m.prod fun _ e => e.factorial : ℕ)` using `Finset.prod_pos fun i _ => Nat.factorial_pos _`. Conclude with `mul_pos (by exact_mod_cast hf) (mul_self_pos.2 (mem_support_iff.1 hm))`. Conclude with `this.ne' h`.
-/
theorem eq_zero_of_fisch_self {P : MvPolynomial σ ℚ} (h : fisch P P = 0) : P = 0 := by
  by_contra h0
  have : 0 < fisch P P := by
    nth_rewrite 1 [P.as_sum]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_pos (fun m hm => ?_) (support_nonempty.2 h0)
    rw [fisch_monomial, mul_left_comm]
    have hf : 0 < (m.prod fun _ e => e.factorial : ℕ) := Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact mul_pos (by exact_mod_cast hf) (mul_self_pos.2 (mem_support_iff.1 hm))
  exact this.ne' h

end Fischer

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on generalizing Q with`. Consider the case `C c`. Establish `key : (constantCoeff : MvPolynomial (Letter T r n) ℚ →+* ℚ).comp (rowAct (fun σ => (g σ).transpose)).toRingHom = constantCoeff`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[rowAct]`. Introduce `i`. Simplify using `[rowAct_X, constantCoeff_X]`. Establish `e : rowAct g (C c : MvPolynomial (Letter T r n) ℚ) = C c` using `by simp [rowAct]`. Rewrite using `[e, C_apply, fisch_monomial, fisch_monomial]`.

Conclude with `congrArg (fun x => c * (_ * x)) (congrArg (fun f => f Q) key).symm`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]`. Consider the case `mul_X p s hp`. Take `⟨σ, i, b⟩` from `s`. Rewrite using `[map_mul, rowAct_X, Finset.mul_sum, map_sum, LinearMap.sum_apply, fisch_mul_X, pderiv_rowAct, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_C_mul, mul_smul_comm, map_smul, LinearMap.smul_apply, fisch_mul_X, hp, map_smul]`. Both sides reduce to the same expression.
-/
theorem fisch_rowAct (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) ℚ) (P Q : MvPolynomial (Letter T r n) ℚ) :
    fisch (rowAct g P) Q = fisch P (rowAct (fun σ => (g σ).transpose) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have key : (constantCoeff : MvPolynomial (Letter T r n) ℚ →+* ℚ).comp
        (rowAct (fun σ => (g σ).transpose)).toRingHom = constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [rowAct]
      · intro i
        simp [rowAct_X, constantCoeff_X]
    have e : rowAct g (C c : MvPolynomial (Letter T r n) ℚ) = C c := by simp [rowAct]
    rw [e, C_apply, fisch_monomial, fisch_monomial]
    exact congrArg (fun x => c * (_ * x)) (congrArg (fun f => f Q) key).symm
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p s hp =>
    obtain ⟨σ, i, b⟩ := s
    rw [map_mul, rowAct_X, Finset.mul_sum, map_sum, LinearMap.sum_apply, fisch_mul_X, pderiv_rowAct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_C_mul, mul_smul_comm, map_smul, LinearMap.smul_apply, fisch_mul_X, hp, map_smul]
    rfl

section Lower

variable {σ : Type} (w : σ → ℕ)

/- English proof (translation)
Introduce `m hm`. Take `⟨x, hx, y, hy, rfl⟩` from `Finset.mem_add.1 (support_mul p q hm)`. Use `hp x hx` as an intermediate fact. Use `hq y hy` as an intermediate fact. Rewrite using `[map_add]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem weight_lt_mul {p q : MvPolynomial σ k} {a b : ℕ} (hp : ∀ m ∈ p.support, Finsupp.weight w m < a)
    (hq : ∀ m ∈ q.support, Finsupp.weight w m ≤ b) : ∀ m ∈ (p * q).support, Finsupp.weight w m < a + b := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul p q hm)
  have := hp x hx
  have := hq y hy
  rw [map_add]
  omega

/- English proof (translation)
Establish `hmon : ∀ m : σ →₀ ℕ, ∀ m' ∈ (monomial m (1 : k)).support, Finsupp.weight w m' ≤ Finsupp.weight w m`. Introduce `m m' h`. Rewrite using `[Finset.mem_singleton.1 (support_monomial_subset h)]`. Establish `hadd : ∀ m₁ m₂ : σ →₀ ℕ, (∀ m' ∈ (f (monomial m₁ 1) - monomial m₁ 1).support, Finsupp.weight w m' < Finsupp.weight w m₁) → (∀ m' ∈ (f (monomial m₂ 1) - monomial m₂ 1).support, Finsupp.weight w m' < Finsupp.weight w m₂) → ∀ m' ∈ (f (monomial (m₁ + m₂) 1) - monomial (m₁ + m₂) 1).su …`. Introduce `m₁ m₂ h₁ h₂ m' hm'`.

Establish `e : f (monomial (m₁ + m₂) 1) - monomial (m₁ + m₂) 1 = (f (monomial m₁ 1) - monomial m₁ 1) * (f (monomial m₂ 1) - monomial m₂ 1) + ((f (monomial m₁ 1) - monomial m₁ 1) * monomial m₂ 1 + (f (monomial m₂ 1) - monomial m₂ 1) * monomial m₁ 1)`. Establish `: (monomial (m₁ + m₂) 1 : MvPolynomial σ k) = monomial m₁ 1 * monomial m₂ 1`. Rewrite using `[monomial_mul, mul_one]`. Rewrite using `[this, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hm'` using `[e]`. Rewrite using `[map_add]`. Break down `Finset.mem_union.1 (support_add hm') with h | h` into its components or cases. Conclude with `weight_lt_mul w h₁ (fun m hm => (h₂ m hm).le) _ h`. Break down `Finset.mem_union.1 (support_add h) with h | h` into its components or cases.

Conclude with `weight_lt_mul w h₁ (hmon _) _ h`. Rewrite using `[add_comm]`. Conclude with `weight_lt_mul w h₂ (hmon _) _ h`. Establish `hzero : ∀ m' ∈ (f (monomial 0 1) - monomial 0 1).support, Finsupp.weight w m' < Finsupp.weight w (0 : σ →₀ ℕ)`. Introduce `m' h`.

Simplify using `at h`. Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => exact hzero`. Consider the case `add m₁ m₂ h₁ h₂ => exact hadd _ _ h₁ h₂`. Consider the case `single a e`.

Proceed by induction on `e with`. Consider the case `zero => simpa using hzero`. Consider the case `succ e ih`. Rewrite using `[Finsupp.single_add]`. Use `hadd _ _ ih ?_` and prove the remaining obligations.

Use `hf a` as an intermediate fact. Rewrite using `[Finsupp.weight_single, one_smul]` and apply the resulting hypothesis.
-/
theorem weight_lt_monomial (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hf : ∀ ℓ, ∀ m ∈ (f (X ℓ) - X ℓ).support, Finsupp.weight w m < w ℓ) (m : σ →₀ ℕ) :
    ∀ m' ∈ (f (monomial m 1) - monomial m 1).support, Finsupp.weight w m' < Finsupp.weight w m := by
  classical
  have hmon : ∀ m : σ →₀ ℕ, ∀ m' ∈ (monomial m (1 : k)).support, Finsupp.weight w m' ≤ Finsupp.weight w m := by
    intro m m' h
    rw [Finset.mem_singleton.1 (support_monomial_subset h)]
  have hadd : ∀ m₁ m₂ : σ →₀ ℕ,
      (∀ m' ∈ (f (monomial m₁ 1) - monomial m₁ 1).support, Finsupp.weight w m' < Finsupp.weight w m₁) →
      (∀ m' ∈ (f (monomial m₂ 1) - monomial m₂ 1).support, Finsupp.weight w m' < Finsupp.weight w m₂) →
      ∀ m' ∈ (f (monomial (m₁ + m₂) 1) - monomial (m₁ + m₂) 1).support,
        Finsupp.weight w m' < Finsupp.weight w (m₁ + m₂) := by
    intro m₁ m₂ h₁ h₂ m' hm'
    have e : f (monomial (m₁ + m₂) 1) - monomial (m₁ + m₂) 1 =
        (f (monomial m₁ 1) - monomial m₁ 1) * (f (monomial m₂ 1) - monomial m₂ 1) +
          ((f (monomial m₁ 1) - monomial m₁ 1) * monomial m₂ 1 +
            (f (monomial m₂ 1) - monomial m₂ 1) * monomial m₁ 1) := by
      have : (monomial (m₁ + m₂) 1 : MvPolynomial σ k) = monomial m₁ 1 * monomial m₂ 1 := by
        rw [monomial_mul, mul_one]
      rw [this, map_mul]
      ring
    rw [e] at hm'
    rw [map_add]
    rcases Finset.mem_union.1 (support_add hm') with h | h
    · exact weight_lt_mul w h₁ (fun m hm => (h₂ m hm).le) _ h
    · rcases Finset.mem_union.1 (support_add h) with h | h
      · exact weight_lt_mul w h₁ (hmon _) _ h
      · rw [add_comm]
        exact weight_lt_mul w h₂ (hmon _) _ h
  have hzero : ∀ m' ∈ (f (monomial 0 1) - monomial 0 1).support,
      Finsupp.weight w m' < Finsupp.weight w (0 : σ →₀ ℕ) := by
    intro m' h
    simp at h
  induction m using Finsupp.induction_linear with
  | zero => exact hzero
  | add m₁ m₂ h₁ h₂ => exact hadd _ _ h₁ h₂
  | single a e =>
    induction e with
    | zero => simpa using hzero
    | succ e ih =>
      rw [Finsupp.single_add]
      refine hadd _ _ ih ?_
      have := hf a
      rwa [Finsupp.weight_single, one_smul]

/- English proof (translation)
Introduce `m' hm'`. Establish `e : f P - P = ∑ m ∈ P.support, P.coeff m • (f (monomial m 1) - monomial m 1)` using `by nth_rewrite 1 [P.as_sum] nth_rewrite 3 [P.as_sum]`. Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[smul_sub, ← map_smul, smul_monomial, smul_eq_mul, mul_one]`.

Rewrite `hm'` using `[e]`. Take `⟨m, hm, h⟩` from `Finset.mem_biUnion.1 (support_sum hm')`. Conclude with `⟨m, hm, weight_lt_monomial w f hf m m' (support_smul h)⟩`.
-/
theorem exists_weight_lt (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hf : ∀ ℓ, ∀ m ∈ (f (X ℓ) - X ℓ).support, Finsupp.weight w m < w ℓ) (P : MvPolynomial σ k) :
    ∀ m' ∈ (f P - P).support, ∃ m ∈ P.support, Finsupp.weight w m' < Finsupp.weight w m := by
  classical
  intro m' hm'
  have e : f P - P = ∑ m ∈ P.support, P.coeff m • (f (monomial m 1) - monomial m 1) := by
    nth_rewrite 1 [P.as_sum]
    nth_rewrite 3 [P.as_sum]
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_sub, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [e] at hm'
  obtain ⟨m, hm, h⟩ := Finset.mem_biUnion.1 (support_sum hm')
  exact ⟨m, hm, weight_lt_monomial w f hf m m' (support_smul h)⟩

end Lower

/- English proof (translation)
Establish `e : rowShift r n k σ i i' t = rowAct (Function.update (β` using `fun σ => Matrix (Fin (r σ)) (Fin (r σ)) k) (fun _ => 1) σ (Matrix.transvection i i' t)) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨σ', j, b⟩`. Rewrite using `[rowAct_X, rowShift, aeval_X]`. Distinguish the cases in `h : σ' = σ`.

Substitute `h` using the available equality. Simplify using `only [Function.update_self, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply, map_add, add_mul, Finset.sum_add_distrib]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[apply_ite, ite_mul]`.

Simplify using `[apply_ite, ite_mul, hj, Ne.symm hj]`. Simplify using `[h, Function.update_of_ne h, Matrix.one_apply, apply_ite, ite_mul]`. Rewrite using `[e]`. Use `hU _ (fun σ' => ?_) P hP` and prove the remaining obligations. Distinguish the cases in `h : σ' = σ`.

Substitute `h` using the available equality. Rewrite using `[Function.update_self, Matrix.det_transvection_of_ne _ _ hi.ne']`. Conclude with `isUnit_one`. Simplify using `[Function.update_of_ne h]`.
-/
theorem RowStable.rowShift_mem {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ U) :
    rowShift r n k σ i i' t P ∈ U := by
  classical
  have e : rowShift r n k σ i i' t =
      rowAct (Function.update (β := fun σ => Matrix (Fin (r σ)) (Fin (r σ)) k) (fun _ => 1) σ
        (Matrix.transvection i i' t)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ', j, b⟩
    rw [rowAct_X, rowShift, aeval_X]
    by_cases h : σ' = σ
    · subst h
      simp only [Function.update_self, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single,
        Matrix.of_apply, map_add, add_mul, Finset.sum_add_distrib]
      by_cases hj : j = i
      · subst hj
        simp [apply_ite, ite_mul]
      · simp [apply_ite, ite_mul, hj, Ne.symm hj]
    · simp [h, Function.update_of_ne h, Matrix.one_apply, apply_ite, ite_mul]
  rw [e]
  refine hU _ (fun σ' => ?_) P hP
  by_cases h : σ' = σ
  · subst h
    rw [Function.update_self, Matrix.det_transvection_of_ne _ _ hi.ne']
    exact isUnit_one
  · simp [Function.update_of_ne h]

def rowOf (ℓ : Letter T r n) : (Σ σ, Fin (r σ)) := ⟨ℓ.1, ℓ.2.1⟩

/- English proof (translation)
Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `φ hφ`. Rewrite `hφ` using `[Submodule.mem_dualAnnihilator]`. Set `w` to `fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1`. Set `Q : MvPolynomial (Σ σ, Fin (r σ)) k` to `∑ m ∈ P.support, monomial (Finsupp.weight w m) (φ (monomial m (P.coeff m)))`.

Establish `hQ : Q = 0`. Use `MvPolynomial.funext_set (fun _ => {0}ᶜ) (fun _ => (Set.finite_singleton 0).infinite_compl) fun x hx => ?_` and prove the remaining obligations. Set `g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k` to `fun σ => Matrix.diagonal fun i => x ⟨σ, i⟩`. Establish `hg : ∀ σ, IsUnit (g σ).det` using `fun σ => by`. Rewrite using `[Matrix.det_diagonal]`.

Conclude with `IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hx _ (Set.mem_univ _))`. Establish `hX : ∀ ℓ : Letter T r n, rowAct g (X ℓ) = C (x (rowOf ℓ)) * X ℓ`. Introduce and unpack `⟨σ, i, b⟩`. Simplify using `[rowAct_X, g, Matrix.diagonal_apply, apply_ite, ite_mul, rowOf]`. Establish `hm : ∀ (m : Letter T r n →₀ ℕ) (c : k), rowAct g (monomial m c) = eval x (monomial (Finsupp.weight w m) (1 : k)) • monomial m c`.

Introduce `m c`. Proceed by induction on `m using Finsupp.induction_linear generalizing c with`. Consider the case `zero => simp [rowAct]`. Consider the case `add m₁ m₂ h₁ h₂`. Establish `e1 : (monomial (m₁ + m₂) c : MvPolynomial (Letter T r n) k) = monomial m₁ c * monomial m₂ 1`.

Rewrite using `[monomial_mul, mul_one]`. Establish `e2 : (monomial (Finsupp.weight w (m₁ + m₂)) 1 : MvPolynomial (Σ σ, Fin (r σ)) k) = monomial (Finsupp.weight w m₁) 1 * monomial (Finsupp.weight w m₂) 1`. Rewrite using `[monomial_mul, mul_one, map_add]`. Rewrite using `[e1, e2, map_mul, map_mul, h₁, h₂, smul_mul_smul_comm]`. Consider the case `single ℓ e`.

Rewrite using `[← C_mul_X_pow_eq_monomial, map_mul, map_pow, hX, Finsupp.weight_single]`. Simplify using `[w, rowAct, smul_eq_C_mul, mul_pow, eval_monomial]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `hφ _ (hU g hg P hP)`. Rewrite `h0` using `[P.as_sum, map_sum, map_sum]`.

Rewrite using `[map_zero, ← h0, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hm, map_smul, smul_eq_mul, eval_monomial, eval_monomial, one_mul, mul_comm]`. Use `congrArg (coeff a) hQ` as an intermediate fact. Rewrite using `[weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]`.

Rewrite `this` using `[coeff_zero, coeff_sum]`. Conclude with `(Finset.sum_congr rfl fun m _ => by rw [coeff_monomial]).trans this`.
-/
theorem RowStable.component_mem [Infinite k] {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ U) (a : (Σ σ, Fin (r σ)) →₀ ℕ) :
    weightedHomogeneousComponent (fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1) a P ∈ U := by
  classical
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  let w := fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1
  let Q : MvPolynomial (Σ σ, Fin (r σ)) k :=
    ∑ m ∈ P.support, monomial (Finsupp.weight w m) (φ (monomial m (P.coeff m)))
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => {0}ᶜ) (fun _ => (Set.finite_singleton 0).infinite_compl) fun x hx => ?_
    let g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k := fun σ => Matrix.diagonal fun i => x ⟨σ, i⟩
    have hg : ∀ σ, IsUnit (g σ).det := fun σ => by
      rw [Matrix.det_diagonal]
      exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hx _ (Set.mem_univ _))
    have hX : ∀ ℓ : Letter T r n, rowAct g (X ℓ) = C (x (rowOf ℓ)) * X ℓ := by
      rintro ⟨σ, i, b⟩
      simp [rowAct_X, g, Matrix.diagonal_apply, apply_ite, ite_mul, rowOf]
    have hm : ∀ (m : Letter T r n →₀ ℕ) (c : k), rowAct g (monomial m c) =
        eval x (monomial (Finsupp.weight w m) (1 : k)) • monomial m c := by
      intro m c
      induction m using Finsupp.induction_linear generalizing c with
      | zero => simp [rowAct]
      | add m₁ m₂ h₁ h₂ =>
        have e1 : (monomial (m₁ + m₂) c : MvPolynomial (Letter T r n) k) = monomial m₁ c * monomial m₂ 1 := by
          rw [monomial_mul, mul_one]
        have e2 : (monomial (Finsupp.weight w (m₁ + m₂)) 1 : MvPolynomial (Σ σ, Fin (r σ)) k) =
            monomial (Finsupp.weight w m₁) 1 * monomial (Finsupp.weight w m₂) 1 := by
          rw [monomial_mul, mul_one, map_add]
        rw [e1, e2, map_mul, map_mul, h₁, h₂, smul_mul_smul_comm]
      | single ℓ e =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, hX, Finsupp.weight_single]
        simp [w, rowAct, smul_eq_C_mul, mul_pow, eval_monomial]
        ring
    have h0 := hφ _ (hU g hg P hP)
    rw [P.as_sum, map_sum, map_sum] at h0
    rw [map_zero, ← h0, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hm, map_smul, smul_eq_mul, eval_monomial, eval_monomial, one_mul, mul_comm]
  have := congrArg (coeff a) hQ
  rw [weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]
  rw [coeff_zero, coeff_sum] at this
  exact (Finset.sum_congr rfl fun m _ => by rw [coeff_monomial]).trans this

/- English proof (translation)
Set `h : Letter T r n → ℕ` to `fun ℓ => ℓ.2.1`. Set `w` to `fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1`. Establish `hex : ∃ d, ∃ P ∈ U, P ≠ 0 ∧ ∀ m ∈ P.support, Finsupp.weight h m < d`. Take `⟨P, hP, hP0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`. Conclude with `⟨P.support.sup (Finsupp.weight h) + 1, P, hP, hP0, fun m hm => Nat.lt_succ_of_le (Finset.le_sup hm)⟩`.

Take `⟨P, hP, hP0, hd⟩` from `Nat.find_spec hex`. Take `⟨m₀, hm₀⟩` from `support_nonempty.2 hP0`. Set `Q` to `weightedHomogeneousComponent w (Finsupp.weight w m₀) P`. Establish `hQU : Q ∈ U` using `hU.component_mem hP _`. Establish `hQs : ∀ m ∈ Q.support, m ∈ P.support ∧ Finsupp.weight w m = Finsupp.weight w m₀`.

Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, coeff_weightedHomogeneousComponent]`. Use `split_ifs at hm with h1`. Conclude with `⟨mem_support_iff.2 hm, h1⟩`. Conclude with `absurd rfl hm`.

Use `⟨Q, hQU, fun hQ => ?_, fun σ i i' hi t => ?_, fun σ i => if hi : i < r σ then Finsupp.weight w m₀ ⟨σ, ⟨i, hi⟩⟩ else 0, fun m hm σ i => ?_⟩` and prove the remaining obligations. Use `congrArg (coeff m₀) hQ` as an intermediate fact. Rewrite `this` using `[coeff_weightedHomogeneousComponent, if_pos rfl]`. Conclude with `mem_support_iff.1 hm₀ this`. Assume the negation of the conclusion as `hne`.

Establish `hlt` using `exists_weight_lt h (rowShift r n k σ i i' t) (fun ℓ m hm => by`. Rewrite `hm` using `[rowShift, aeval_X]`. Use `split_ifs at hm with hc`. Take `⟨b, rfl⟩` from `hc`. Rewrite `hm` using `[add_sub_cancel_left, ← smul_eq_C_mul]`.

Use `support_smul hm` as an intermediate fact. Rewrite `this` using `[support_X, Finset.mem_singleton]`. Rewrite using `[this, Finsupp.weight_single, one_smul]`. Conclude with `hi`. Simplify using `at hm) Q`.

Establish `hpos : 0 < Nat.find hex` using `lt_of_le_of_lt (Nat.zero_le _) (hd m₀ hm₀)`. Use `Nat.find_min hex (m := Nat.find hex - 1) (by omega) ⟨_, U.sub_mem (hU.rowShift_mem σ i i' hi t hQU) hQU, sub_ne_zero.2 hne, fun m' hm' => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, h1⟩` from `hlt m' hm'`. Use `hd m (hQs m hm).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [i.2, dif_pos, Fin.eta]`. Rewrite using `[← (hQs m hm).2, Finsupp.weight_apply, Finsupp.sum, Finsupp.finset_sum_apply]`. Simplify using `only [w, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[← Finset.sum_filter]`. Use `Finset.sum_bij_ne_zero (fun b _ _ => ⟨σ, i, b⟩) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `b _ hb`. Conclude with `Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hb, rfl⟩`. Introduce `b _ _ b' _ _ hb`. Consider the cases of `hb`. Both sides reduce to the same expression.

Introduce and unpack `⟨σ', i', b⟩ hl hb`. Use `(Finset.mem_filter.1 hl).2` as an intermediate fact. Consider the cases of `this`. Conclude with `⟨b, Finset.mem_univ _, hb, rfl⟩`. Introduce `b _ _`.

Both sides reduce to the same expression.
-/
theorem RowStable.exists_top [Infinite k] {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (h0 : U ≠ ⊥) : ∃ P ∈ U, P ≠ 0 ∧ RowInv r n k P ∧ ∃ a : T → ℕ → ℕ, RowDeg r n k a P := by
  classical
  let h : Letter T r n → ℕ := fun ℓ => ℓ.2.1
  let w := fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1
  have hex : ∃ d, ∃ P ∈ U, P ≠ 0 ∧ ∀ m ∈ P.support, Finsupp.weight h m < d := by
    obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact ⟨P.support.sup (Finsupp.weight h) + 1, P, hP, hP0, fun m hm => Nat.lt_succ_of_le (Finset.le_sup hm)⟩
  obtain ⟨P, hP, hP0, hd⟩ := Nat.find_spec hex
  obtain ⟨m₀, hm₀⟩ := support_nonempty.2 hP0
  let Q := weightedHomogeneousComponent w (Finsupp.weight w m₀) P
  have hQU : Q ∈ U := hU.component_mem hP _
  have hQs : ∀ m ∈ Q.support, m ∈ P.support ∧ Finsupp.weight w m = Finsupp.weight w m₀ := by
    intro m hm
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
    split_ifs at hm with h1
    · exact ⟨mem_support_iff.2 hm, h1⟩
    · exact absurd rfl hm
  refine ⟨Q, hQU, fun hQ => ?_, fun σ i i' hi t => ?_,
    fun σ i => if hi : i < r σ then Finsupp.weight w m₀ ⟨σ, ⟨i, hi⟩⟩ else 0, fun m hm σ i => ?_⟩
  · have := congrArg (coeff m₀) hQ
    rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
    exact mem_support_iff.1 hm₀ this
  · by_contra hne
    have hlt := exists_weight_lt h (rowShift r n k σ i i' t) (fun ℓ m hm => by
      rw [rowShift, aeval_X] at hm
      split_ifs at hm with hc
      · obtain ⟨b, rfl⟩ := hc
        rw [add_sub_cancel_left, ← smul_eq_C_mul] at hm
        have := support_smul hm
        rw [support_X, Finset.mem_singleton] at this
        rw [this, Finsupp.weight_single, one_smul]
        exact hi
      · simp at hm) Q
    have hpos : 0 < Nat.find hex := lt_of_le_of_lt (Nat.zero_le _) (hd m₀ hm₀)
    refine Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      ⟨_, U.sub_mem (hU.rowShift_mem σ i i' hi t hQU) hQU, sub_ne_zero.2 hne, fun m' hm' => ?_⟩
    obtain ⟨m, hm, h1⟩ := hlt m' hm'
    have := hd m (hQs m hm).1
    omega
  · simp only [i.2, dif_pos, Fin.eta]
    rw [← (hQs m hm).2, Finsupp.weight_apply, Finsupp.sum, Finsupp.finset_sum_apply]
    simp only [w, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij_ne_zero (fun b _ _ => ⟨σ, i, b⟩) ?_ ?_ ?_ ?_
    · intro b _ hb
      exact Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hb, rfl⟩
    · intro b _ _ b' _ _ hb
      cases hb
      rfl
    · rintro ⟨σ', i', b⟩ hl hb
      have := (Finset.mem_filter.1 hl).2
      cases this
      exact ⟨b, Finset.mem_univ _, hb, rfl⟩
    · intro b _ _
      rfl

/- English proof (translation)
Introduce `g hg P hP` and use `⟨hU g hg P hP.1, hV g hg P hP.2⟩`.
-/
theorem RowStable.inf {U V : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U) (hV : RowStable V) :
    RowStable (U ⊓ V) := fun g hg P hP => ⟨hU g hg P hP.1, hV g hg P hP.2⟩

/- English proof (translation)
Introduce `P hP`. Set `W` to `V ⊓ restrictTotalDegree (Letter T r n) ℚ P.totalDegree`. Establish `hW : RowStable W` using `hV.inf (rowStable_degree _)`. Establish `hPW : P ∈ W` using `⟨hP, (mem_restrictTotalDegree _ _ _).2 le_rfl⟩`. Establish `: FiniteDimensional ℚ W` using `Submodule.finiteDimensional_of_le (inf_le_right : W ≤ _)`.

Establish `: FiniteDimensional ℚ (U ⊓ W : Submodule ℚ _)` using `Submodule.finiteDimensional_of_le inf_le_right`. Assume the negation of the conclusion as `hPU`. Establish `hlt : U ⊓ W < W` using `lt_of_le_of_ne inf_le_right fun e => hPU (e.ge hPW).1`. Set `O : Submodule ℚ (MvPolynomial (Letter T r n) ℚ)` to `W ⊓ LinearMap.ker ((U ⊓ W).subtype.dualMap ∘ₗ fisch)`. Establish `hO : ∀ x, x ∈ O ↔ x ∈ W ∧ ∀ y ∈ U ⊓ W, fisch x y = 0` using `fun x => and_congr Iff.rfl ⟨fun h y hy => LinearMap.congr_fun h ⟨y, hy⟩, fun h => LinearMap.ext fun y => h y.1 y.2⟩`.

Establish `hOs : RowStable O`. Introduce `g hg x hx`. Rewrite `hx`, the goal using `[hO]`. Use `⟨hW g hg x hx.1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[fisch_rowAct]`.

Conclude with `hx.2 _ ((hU.inf hW) _ (fun σ => by rw [Matrix.det_transpose]; exact hg σ) y hy)`. Establish `hO0 : O ≠ ⊥`. Establish `hk` using `LinearMap.ker_ne_bot_of_finrank_lt (f := ((U ⊓ W).subtype.dualMap ∘ₗ fisch) ∘ₗ W.subtype) (by`. Rewrite using `[Subspace.dual_finrank_eq]`. Conclude with `Submodule.finrank_lt_finrank_of_lt hlt)`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hk`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨x.1, ⟨x.2, hx⟩, fun e => hx0 (Subtype.ext e)⟩`. Take `⟨Q, hQ, hQ0, h1, h2⟩` from `hOs.exists_top hO0`. Rewrite `hQ` using `[hO]`. Conclude with `hQ0 (eq_zero_of_fisch_self (hQ.2 Q ⟨h Q hQ.1.1 h1 h2, hQ.1⟩))`.
-/
theorem le_of_top_rat [Finite T] {U V : Submodule ℚ (MvPolynomial (Letter T r n) ℚ)} (hU : RowStable U)
    (hV : RowStable V) (h : ∀ P ∈ V, RowInv r n ℚ P → (∃ a : T → ℕ → ℕ, RowDeg r n ℚ a P) → P ∈ U) : V ≤ U := by
  intro P hP
  let W := V ⊓ restrictTotalDegree (Letter T r n) ℚ P.totalDegree
  have hW : RowStable W := hV.inf (rowStable_degree _)
  have hPW : P ∈ W := ⟨hP, (mem_restrictTotalDegree _ _ _).2 le_rfl⟩
  have : FiniteDimensional ℚ W := Submodule.finiteDimensional_of_le (inf_le_right : W ≤ _)
  have : FiniteDimensional ℚ (U ⊓ W : Submodule ℚ _) := Submodule.finiteDimensional_of_le inf_le_right
  by_contra hPU
  have hlt : U ⊓ W < W := lt_of_le_of_ne inf_le_right fun e => hPU (e.ge hPW).1
  let O : Submodule ℚ (MvPolynomial (Letter T r n) ℚ) :=
    W ⊓ LinearMap.ker ((U ⊓ W).subtype.dualMap ∘ₗ fisch)
  have hO : ∀ x, x ∈ O ↔ x ∈ W ∧ ∀ y ∈ U ⊓ W, fisch x y = 0 := fun x =>
    and_congr Iff.rfl ⟨fun h y hy => LinearMap.congr_fun h ⟨y, hy⟩, fun h => LinearMap.ext fun y => h y.1 y.2⟩
  have hOs : RowStable O := by
    intro g hg x hx
    rw [hO] at hx ⊢
    refine ⟨hW g hg x hx.1, fun y hy => ?_⟩
    rw [fisch_rowAct]
    exact hx.2 _ ((hU.inf hW) _ (fun σ => by rw [Matrix.det_transpose]; exact hg σ) y hy)
  have hO0 : O ≠ ⊥ := by
    have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := ((U ⊓ W).subtype.dualMap ∘ₗ fisch) ∘ₗ W.subtype) (by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt_finrank_of_lt hlt)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    exact (Submodule.ne_bot_iff _).2 ⟨x.1, ⟨x.2, hx⟩, fun e => hx0 (Subtype.ext e)⟩
  obtain ⟨Q, hQ, hQ0, h1, h2⟩ := hOs.exists_top hO0
  rw [hO] at hQ
  exact hQ0 (eq_zero_of_fisch_self (hQ.2 Q ⟨h Q hQ.1.1 h1 h2, hQ.1⟩))

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c => simp [rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p s hp => simp [hp, rowAct_X]`.
-/
theorem map_rowAct {K : Type} [Field K] (φ : k →+* K) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k)
    (P : MvPolynomial (Letter T r n) k) :
    map φ (rowAct g P) = rowAct (fun σ => φ.mapMatrix (g σ)) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp [hp, rowAct_X]

/- English proof (translation)
Introduce `σ i i' hi t`. Use `GlobalTheory.RowTriangular.eval₂_shift ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) hP σ i i' hi (C t) X (fun ℓ => rowShift r n K σ i i' t (X ℓ)) (fun b => by simp [rowShift]) (fun ℓ hℓ => by` as an intermediate fact. Rewrite using `[rowShift, aeval_X, if_neg hℓ])`. Establish `e : ∀ Q : MvPolynomial (Letter T r n) k, rowShift r n K σ i i' t (map φ Q) = eval₂Hom ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) (fun ℓ => rowShift r n K σ i i' t (X ℓ)) Q`. Introduce `Q`.

Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C c => simp [rowShift]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p s hp => simp only [map_mul, hp, map_X, eval₂Hom_X']`. Rewrite using `[e, this, map_eq_eval₂Hom_C_comp]`.
-/
theorem rowInv_map [Infinite k] {K : Type} [Field K] (φ : k →+* K) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n K (map φ P) := by
  classical
  intro σ i i' hi t
  have := GlobalTheory.RowTriangular.eval₂_shift ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) hP σ i i' hi (C t) X
    (fun ℓ => rowShift r n K σ i i' t (X ℓ)) (fun b => by simp [rowShift]) (fun ℓ hℓ => by
      rw [rowShift, aeval_X, if_neg hℓ])
  have e : ∀ Q : MvPolynomial (Letter T r n) k, rowShift r n K σ i i' t (map φ Q) =
      eval₂Hom ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) (fun ℓ => rowShift r n K σ i i' t (X ℓ)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp [rowShift]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p s hp => simp only [map_mul, hp, map_X, eval₂Hom_X']
  rw [e, this, map_eq_eval₂Hom_C_comp]

/- English proof (translation)
Introduce `P hP`. Set `B` to `Module.Basis.ofVectorSpace ℚ k`. Set `L : (k →ₗ[ℚ] ℚ) → MvPolynomial (Letter T r n) k → MvPolynomial (Letter T r n) ℚ` to `fun φ Q => ∑ m ∈ Q.support, monomial m (φ (coeff m Q))`. Establish `hL : ∀ φ Q m, coeff m (L φ Q) = φ (coeff m Q)`. Introduce `φ Q m`.

Simplify using `only [L, coeff_sum, coeff_monomial, Finset.sum_ite_eq']`. Use `split_ifs with hm`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.1 hm, map_zero]`. Establish `hLd : ∀ φ Q ℓ, pderiv ℓ (L φ Q) = L φ (pderiv ℓ Q)`.

Introduce `φ Q ℓ`. Use extensionality with `m`. Rewrite using `[coeff_pderiv, hL, hL, coeff_pderiv, mul_comm, ← smul_eq_mul, ← map_smul, mul_comm (coeff _ Q), Algebra.smul_def]`. Simplify using the standard rewrite rules. Set `s` to `P.support.biUnion fun m => (B.repr (coeff m P)).support`.

Establish `e : P = ∑ i ∈ s, B i • map (algebraMap ℚ k) (L (B.coord i) P)`. Use extensionality with `m`. Simplify using `only [coeff_sum, coeff_smul, coeff_map, hL, smul_eq_mul, Module.Basis.coord_apply]`. Use `nth_rewrite 1 [← B.linearCombination_repr (coeff m P)]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (s := s)]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]`. Distinguish the cases in `hm : m ∈ P.support`. Conclude with `Finset.subset_biUnion_of_mem (fun m => (B.repr (coeff m P)).support) hm`. Simplify using `[notMem_support_iff.1 hm]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)` and prove the remaining obligations. Rewrite `hP` using `[mem_harmK_iff]`. Use `(mem_harmK_iff _ _ _).2 fun τ hτ j j' => ?_` and prove the remaining obligations. Use extensionality with `m`.

Simplify using `only [hLd, coeff_sum, hL]`. Rewrite using `[← map_sum, ← coeff_sum, hP τ hτ j j']`. Simplify using the standard rewrite rules.
-/
theorem harmK_le_span [CharZero k] (cc : T → T) (isX : T → Prop) :
    harmK r n k cc isX (fun _ => 1) ≤
      Submodule.span k (map (algebraMap ℚ k) '' (harmK r n ℚ cc isX (fun _ => 1))) := by
  classical
  intro P hP
  let B := Module.Basis.ofVectorSpace ℚ k
  let L : (k →ₗ[ℚ] ℚ) → MvPolynomial (Letter T r n) k → MvPolynomial (Letter T r n) ℚ := fun φ Q =>
    ∑ m ∈ Q.support, monomial m (φ (coeff m Q))
  have hL : ∀ φ Q m, coeff m (L φ Q) = φ (coeff m Q) := by
    intro φ Q m
    simp only [L, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.1 hm, map_zero]
  have hLd : ∀ φ Q ℓ, pderiv ℓ (L φ Q) = L φ (pderiv ℓ Q) := by
    intro φ Q ℓ
    ext m
    rw [coeff_pderiv, hL, hL, coeff_pderiv, mul_comm, ← smul_eq_mul, ← map_smul, mul_comm (coeff _ Q), Algebra.smul_def]
    simp
  let s := P.support.biUnion fun m => (B.repr (coeff m P)).support
  have e : P = ∑ i ∈ s, B i • map (algebraMap ℚ k) (L (B.coord i) P) := by
    ext m
    simp only [coeff_sum, coeff_smul, coeff_map, hL, smul_eq_mul, Module.Basis.coord_apply]
    nth_rewrite 1 [← B.linearCombination_repr (coeff m P)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (s := s)]
    · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    · by_cases hm : m ∈ P.support
      · exact Finset.subset_biUnion_of_mem (fun m => (B.repr (coeff m P)).support) hm
      · simp [notMem_support_iff.1 hm]
    · simp
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
  rw [mem_harmK_iff] at hP
  refine (mem_harmK_iff _ _ _).2 fun τ hτ j j' => ?_
  ext m
  simp only [hLd, coeff_sum, hL]
  rw [← map_sum, ← coeff_sum, hP τ hτ j j']
  simp

/- English proof (translation)
Use `(harmK_le_span cc isX).trans (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨P, hP, rfl⟩`. Set `U₀ : Submodule ℚ (MvPolynomial (Letter T r n) ℚ)` to `(U.restrictScalars ℚ).comap (mapAlgHom (Algebra.ofId ℚ k)).toLinearMap`. Establish `hU₀ : ∀ Q, Q ∈ U₀ ↔ map (algebraMap ℚ k) Q ∈ U` using `fun _ => Iff.rfl`. Use `(hU₀ P).1 (le_of_top_rat (U := U₀) (fun g hg Q hQ => ?_) (rowStable_harmK cc isX) ?_ hP)` and prove the remaining obligations.

Rewrite using `[hU₀, map_rowAct]`. Use `hU _ (fun σ => ?_) _ hQ` and prove the remaining obligations. Rewrite using `[← RingHom.map_det]`. Conclude with `(hg σ).map _`. Introduce and unpack `Q hQ h1 ⟨a, h2⟩`.

Rewrite using `[hU₀]`. Use `h _ ?_ (rowInv_map _ h1) ⟨a, fun m hm => h2 m (support_map_subset _ _ hm)⟩` and prove the remaining obligations. Rewrite `hQ`, the goal using `[mem_harmK_iff]`. Introduce `τ hτ j j'`. Use `congrArg (map (algebraMap ℚ k)) (hQ τ hτ j j')` as an intermediate fact.

Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]`.
-/
theorem harmK_le_of_top [CharZero k] [Finite T] (cc : T → T) (isX : T → Prop)
    {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (h : ∀ P ∈ harmK r n k cc isX (fun _ => 1), RowInv r n k P → (∃ a : T → ℕ → ℕ, RowDeg r n k a P) → P ∈ U) :
    harmK r n k cc isX (fun _ => 1) ≤ U := by
  refine (harmK_le_span cc isX).trans (Submodule.span_le.2 ?_)
  rintro _ ⟨P, hP, rfl⟩
  let U₀ : Submodule ℚ (MvPolynomial (Letter T r n) ℚ) :=
    (U.restrictScalars ℚ).comap (mapAlgHom (Algebra.ofId ℚ k)).toLinearMap
  have hU₀ : ∀ Q, Q ∈ U₀ ↔ map (algebraMap ℚ k) Q ∈ U := fun _ => Iff.rfl
  refine (hU₀ P).1 (le_of_top_rat (U := U₀) (fun g hg Q hQ => ?_) (rowStable_harmK cc isX) ?_ hP)
  · rw [hU₀, map_rowAct]
    refine hU _ (fun σ => ?_) _ hQ
    rw [← RingHom.map_det]
    exact (hg σ).map _
  · rintro Q hQ h1 ⟨a, h2⟩
    rw [hU₀]
    refine h _ ?_ (rowInv_map _ h1) ⟨a, fun m hm => h2 m (support_map_subset _ _ hm)⟩
    rw [mem_harmK_iff] at hQ ⊢
    intro τ hτ j j'
    have := congrArg (map (algebraMap ℚ k)) (hQ τ hτ j j')
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]

end GlobalTheory.RowSpan
