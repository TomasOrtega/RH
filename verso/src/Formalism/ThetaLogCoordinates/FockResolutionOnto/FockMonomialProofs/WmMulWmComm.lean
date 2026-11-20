import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementG
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RaisingKeepsEarlyLetters
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames MvPolynomial Finset

section Gen
variable {p : ℕ} [Fact p.Prime] {σ : Type} {n : ℕ}

noncomputable def compW (p : ℕ) [Fact p.Prime] (w : (σ →₀ ℕ) → Fin n → ℤ) (μ : Fin n → ℤ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun x := compP (fun m => w m = μ) x
  map_add' x y := by
    ext m; simp only [coeff_compP, coeff_add]; split_ifs <;> simp
  map_smul' a x := by
    ext m; simp only [coeff_compP, coeff_smul, RingHom.id_apply]; split_ifs <;> simp

/- English proof (translation)
Use `show coeff m (compP _ x) = _`. Rewrite using `[coeff_compP]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem coeff_compW (w : (σ →₀ ℕ) → Fin n → ℤ) (μ : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    coeff m (compW p w μ x) = if w m = μ then coeff m x else 0 := by
  show coeff m (compP _ x) = _
  rw [coeff_compP]
  split_ifs <;> rfl

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_compW]`. Distinguish the cases in `h0 : coeff m x = 0`. Apply the tactic sequence `split_ifs <;> simp [h0]`. Apply the tactic sequence `rw [hx m h0] split_ifs <;> simp`.
-/
theorem compW_fix (w : (σ →₀ ℕ) → Fin n → ℤ) (μ ν : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p])
    (hx : ∀ m, coeff m x ≠ 0 → w m = ν) : compW p w μ x = if ν = μ then x else 0 := by
  ext m
  rw [coeff_compW]
  by_cases h0 : coeff m x = 0
  · split_ifs <;> simp [h0]
  · rw [hx m h0]
    split_ifs <;> simp

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[coeff_compW]`. Assume the negation of the conclusion as `h`. Conclude with `hm (if_neg h)`.
-/
theorem compW_isW (w : (σ →₀ ℕ) → Fin n → ℤ) (μ : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) :
    ∀ m, coeff m (compW p w μ x) ≠ 0 → w m = μ := by
  intro m hm
  rw [coeff_compW] at hm
  by_contra h
  exact hm (if_neg h)

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_compW]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Use `congrArg (coeff d) (hS _ h)` as an intermediate fact. Rewrite `this` using `[coeff_compW, if_pos rfl, coeff_zero]`. Conclude with `this.symm`.
-/
theorem sum_compW (w : (σ →₀ ℕ) → Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) (S : Finset (Fin n → ℤ))
    (hS : ∀ μ ∉ S, compW p w μ x = 0) : ∑ μ ∈ S, compW p w μ x = x := by
  ext d
  rw [coeff_sum]
  simp only [coeff_compW]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have := congrArg (coeff d) (hS _ h)
    rw [coeff_compW, if_pos rfl, coeff_zero] at this
    exact this.symm

/- English proof (translation)
Introduce `μ hμ`. Use extensionality with `m`. Rewrite using `[coeff_compW, coeff_zero]`. Use `split_ifs with h`. Assume the negation of the conclusion as `hne`.

Conclude with `hμ (Finset.mem_image.mpr ⟨m, mem_support_iff.mpr hne, h⟩)`. Both sides reduce to the same expression.
-/
theorem compW_dec (w : (σ →₀ ℕ) → Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) :
    ∀ μ ∉ x.support.image w, compW p w μ x = 0 := by
  intro μ hμ
  ext m
  rw [coeff_compW, coeff_zero]
  split_ifs with h
  · by_contra hne
    exact hμ (Finset.mem_image.mpr ⟨m, mem_support_iff.mpr hne, h⟩)
  · rfl

/- English proof (translation)
Introduce `m hm`. Use function extensionality and compare the values at `c`. Establish `h1 : E c c x = ((μ c : ℤ) : ℚ_[p]) • x`. Use extensionality with `m'`. Rewrite using `[hdiag, coeff_smul, smul_eq_mul]`.

Distinguish the cases in `h0 : coeff m' x = 0`. Rewrite using `[h0, mul_zero, mul_zero]`. Rewrite using `[hx m' h0]`. Establish `h2` using `congrArg (coeff m) (hcomm c c a b x)`. Rewrite `h2` using `[h1, map_smul, coeff_sub, hdiag, coeff_smul, smul_eq_mul, coeff_sub]`.

Establish `h3 : coeff m (if c = a then E c b x else 0) = (if c = a then 1 else 0) * coeff m (E a b x)` using `by split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[one_mul]`. Simplify using the standard rewrite rules. Establish `h4 : coeff m (if b = c then E a c x else 0) = (if c = b then 1 else 0) * coeff m (E a b x)`.

Distinguish the cases in `h : b = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[h3, h4, ← sub_mul, ← sub_mul]`. Establish `h5` using `mul_right_cancel₀ hm h2`. Rewrite using `[Pi.add_apply, dl_apply]`. Establish `h6 : ((w m c - μ c : ℤ) : ℚ_[p]) = (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℚ_[p])` using `by push_cast; exact h5`. Use `Int.cast_injective h6` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem isW_E (E : Fin n → Fin n → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (w : (σ →₀ ℕ) → Fin n → ℤ)
    (hcomm : ∀ a b c d x, E a b (E c d x) - E c d (E a b x) =
      (if b = c then E a d x else 0) - (if d = a then E c b x else 0))
    (hdiag : ∀ c x m, coeff m (E c c x) = ((w m c : ℤ) : ℚ_[p]) * coeff m x)
    (a b : Fin n) (μ : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) (hx : ∀ m, coeff m x ≠ 0 → w m = μ) :
    ∀ m, coeff m (E a b x) ≠ 0 → w m = μ + dl a b := by
  intro m hm
  funext c
  have h1 : E c c x = ((μ c : ℤ) : ℚ_[p]) • x := by
    ext m'
    rw [hdiag, coeff_smul, smul_eq_mul]
    by_cases h0 : coeff m' x = 0
    · rw [h0, mul_zero, mul_zero]
    · rw [hx m' h0]
  have h2 := congrArg (coeff m) (hcomm c c a b x)
  rw [h1, map_smul, coeff_sub, hdiag, coeff_smul, smul_eq_mul, coeff_sub] at h2
  have h3 : coeff m (if c = a then E c b x else 0) = (if c = a then 1 else 0) * coeff m (E a b x) := by
    split_ifs with h
    · subst h; rw [one_mul]
    · simp
  have h4 : coeff m (if b = c then E a c x else 0) = (if c = b then 1 else 0) * coeff m (E a b x) := by
    by_cases h : b = c
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  rw [h3, h4, ← sub_mul, ← sub_mul] at h2
  have h5 := mul_right_cancel₀ hm h2
  rw [Pi.add_apply, dl_apply]
  have h6 : ((w m c - μ c : ℤ) : ℚ_[p]) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℚ_[p]) := by
    push_cast; exact h5
  have := Int.cast_injective h6
  omega

noncomputable def mkGlW (E : Fin n → Fin n → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (w : (σ →₀ ℕ) → Fin n → ℤ)
    (hcomm : ∀ a b c d x, E a b (E c d x) - E c d (E a b x) =
      (if b = c then E a d x else 0) - (if d = a then E c b x else 0))
    (hdiag : ∀ c x m, coeff m (E c c x) = ((w m c : ℤ) : ℚ_[p]) * coeff m x) :
    GlW ℚ_[p] (MvPolynomial σ ℚ_[p]) n where
  E := E
  comm := hcomm
  comp := compW p w
  dec := fun x => ⟨x.support.image w, compW_dec w x⟩
  sum_comp := fun x S hS => sum_compW w x S hS
  idem := fun μ ν x => by
    rw [compW_fix w μ ν _ (compW_isW w ν x)]
    by_cases h : μ = ν
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  diag := fun c μ x => by
    ext m
    rw [hdiag, coeff_smul, smul_eq_mul, coeff_compW]
    split_ifs with h
    · rw [h]
    · simp
  shift := fun a b μ x => by
    conv_lhs => rw [← sum_compW w x _ (compW_dec w x)]
    rw [map_sum, map_sum]
    have e' : ∀ ν, compW p w μ (E a b (compW p w ν x)) =
        if ν = μ - dl a b then E a b (compW p w ν x) else 0 := by
      intro ν
      rw [compW_fix w μ (ν + dl a b) _ (isW_E E w hcomm hdiag a b ν _ (compW_isW w ν x))]
      congr 1
      apply propext; constructor <;> intro h <;> subst h <;> simp
    simp only [e', Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [compW_dec w x _ h, map_zero]

end Gen

section Rel
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

noncomputable def Aop (p : ℕ) [Fact p.Prime] (K r : ℕ) (c : ℤ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K r

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Aop_apply (c : ℤ) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Aop p K r c F = ((c : ℤ) : ℚ_[p]) • F - ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dW_apply (j : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    dW p K j F = pderiv (Fin.last K, j) F := rfl

/- English proof (translation)
Rewrite using `[pderiv_mul, pderiv_X]`. Distinguish the cases in `h : j = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : ((Fin.last K, b) : Fin (K + 1) × Fin r) ≠ (Fin.last K, j)` using `fun h' => h (Prod.mk.inj h').2.symm`.

Rewrite using `[Pi.single_apply, if_neg h', if_neg h, zero_mul]`.
-/
theorem pderiv_X_mul (j b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, j) (X (Fin.last K, b) * G) =
      (if j = b then G else 0) + X (Fin.last K, b) * pderiv (Fin.last K, j) G := by
  classical
  rw [pderiv_mul, pderiv_X]
  by_cases h : j = b
  · subst h; simp
  · have h' : ((Fin.last K, b) : Fin (K + 1) × Fin r) ≠ (Fin.last K, j) := fun h' => h (Prod.mk.inj h').2.symm
    rw [Pi.single_apply, if_neg h', if_neg h, zero_mul]

/- English proof (translation)
Establish `h2 : ¬ ((Fin.last K : Fin (K + 1)) : ℕ) < K` using `by simp`. Rewrite using `[glAct_mul, glAct_X, if_neg h2, zero_mul, zero_add]`.
-/
theorem glJ_X_mul (LL : Letters (K + 1)) (a b d : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL K a b (X (Fin.last K, d) * G) = X (Fin.last K, d) * glAct p LL K a b G := by
  have h2 : ¬ ((Fin.last K : Fin (K + 1)) : ℕ) < K := by simp
  rw [glAct_mul, glAct_X, if_neg h2, zero_mul, zero_add]

/- English proof (translation)
The claim follows from `FockB.ops_apply_comm disj_last (FockB.pderiv_mem (last_mem d)) (glAct_mem LL K a b) x`.
-/
theorem pderiv_glJ (LL : Letters (K + 1)) (a b d : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, d) (glAct p LL K a b x) = glAct p LL K a b (pderiv (Fin.last K, d) x) :=
  FockB.ops_apply_comm disj_last (FockB.pderiv_mem (last_mem d)) (glAct_mem LL K a b) x

/- English proof (translation)
Rewrite using `[ProjS.eulL_apply, ProjS.eulL_apply]`. Simplify using `only [pderiv_X_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_univ b), Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`.
-/
theorem eul_X_mul (b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (X (Fin.last K, b) * G) =
      X (Fin.last K, b) * G + X (Fin.last K, b) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G := by
  rw [ProjS.eulL_apply, ProjS.eulL_apply]
  simp only [pderiv_X_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ b), Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring

/- English proof (translation)
Rewrite using `[ProjS.eulL_apply, ProjS.eulL_apply, map_sum]`. Simplify using `only [pderiv_X_mul, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [ProjS.pderiv_comm]`.
-/
theorem pderiv_eul (j : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, j) (ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G) =
      pderiv (Fin.last K, j) G + ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (pderiv (Fin.last K, j) G) := by
  rw [ProjS.eulL_apply, ProjS.eulL_apply, map_sum]
  simp only [pderiv_X_mul, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [ProjS.pderiv_comm]

/- English proof (translation)
Rewrite using `[Uop_apply, Uop_apply, map_sub, map_sum]`. Simplify using `only [eul_X_mul, eul_glAct, map_sub, map_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem eul_Uop (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (Uop p LL c Cs i F) =
      Uop p LL c Cs i F + Uop p LL c Cs i (ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F) := by
  rw [Uop_apply, Uop_apply, map_sub, map_sum]
  simp only [eul_X_mul, eul_glAct, map_sub, map_smul, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Rewrite using `[Aop_apply, Aop_apply, eul_Uop, map_sub, map_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem A_U (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Aop p K r c (Uop p LL c Cs i F) - Uop p LL c Cs i (Aop p K r c F) = -Uop p LL c Cs i F := by
  rw [Aop_apply, Aop_apply, eul_Uop, map_sub, map_smul]
  abel

/- English proof (translation)
Rewrite using `[Aop_apply, Aop_apply, dW_apply, dW_apply, map_sub, Derivation.map_smul, pderiv_eul]`. Normalize the expressions using the abelian group laws.
-/
theorem A_d (c : ℤ) (j : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Aop p K r c (dW p K j F) - dW p K j (Aop p K r c F) = dW p K j F := by
  rw [Aop_apply, Aop_apply, dW_apply, dW_apply, map_sub, Derivation.map_smul, pderiv_eul]
  abel

/- English proof (translation)
Rewrite using `[Aop_apply, Aop_apply, eul_glAct, map_sub, map_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem e_A (LL : Letters (K + 1)) (c : ℤ) (a b : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) a b (Aop p K r c F) - Aop p K r c (glAct p LL (K + 1) a b F) = 0 := by
  rw [Aop_apply, Aop_apply, eul_glAct, map_sub, map_smul]
  abel

/- English proof (translation)
Rewrite using `[dW_apply, dW_apply, Uop_apply, Uop_apply, map_sub, map_sum, Aop_apply, glAct_succ LL hv]`. Simplify using `only [pderiv_X_mul, pderiv_glJ, map_sub, Derivation.map_smul, pderiv_eul, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_ite_eq, if_pos hj]`. Simplify using `only [mul_sub, mul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem d_U (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : ℤ) (Cs : Finset (Fin r)) (i j : Fin r)
    (hj : j ∈ Cs) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    dW p K j (Uop p LL c Cs i F) - Uop p LL c Cs i (dW p K j F) =
      (if j = i then Aop p K r c F else 0) - glAct p LL (K + 1) i j F := by
  rw [dW_apply, dW_apply, Uop_apply, Uop_apply, map_sub, map_sum, Aop_apply, glAct_succ LL hv]
  simp only [pderiv_X_mul, pderiv_glJ, map_sub, Derivation.map_smul, pderiv_eul, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, if_pos hj]
  simp only [mul_sub, mul_add]
  abel

noncomputable def Sop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r) :
    Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b

/- English proof (translation)
Simplify using `only [Sop, Wm, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply]`.
-/
theorem Sop_apply (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Sop p LL Cs a F = ∑ b ∈ Cs, X (Fin.last K, b) * glAct p LL K a b F := by
  simp only [Sop, Wm, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply]

/- English proof (translation)
Establish `e1 : Wi * A * (Wk * A) = Wi * Wk * A * A - Wi * Wk * A`. Rewrite using `[mul_assoc Wi A, ← mul_assoc A Wk A, h1']`. Use `noncomm_ring`. Establish `e1' : Wk * A * (Wi * A) = Wi * Wk * A * A - Wi * Wk * A`. Rewrite using `[mul_assoc Wk A, ← mul_assoc A Wi A, h1, h4]`.

Use `noncomm_ring`. Establish `e2 : Wi * A * Sk = Wi * Sk * A - Wi * Sk`. Rewrite using `[mul_assoc Wi A, h2']`. Use `noncomm_ring`. Establish `e2' : Wk * A * Si = Wk * Si * A - Wk * Si`.

Rewrite using `[mul_assoc Wk A, h2]`. Use `noncomm_ring`. Establish `e3 : Si * (Wk * A) = Wk * Si * A` using `by rw [← mul_assoc, h3]`. Establish `e3' : Sk * (Wi * A) = Wi * Sk * A` using `by rw [← mul_assoc, h3']`. Establish `e5 : Si * Sk = Sk * Si + (Wk * Si - Wi * Sk)` using `by rw [← h5]; abel`.

Rewrite using `[sub_mul, sub_mul, mul_sub, mul_sub, mul_sub, mul_sub, e1, e1', e2, e2', e3, e3', e5]`. Normalize the expressions using the abelian group laws.
-/
theorem ring_UU {R : Type} [Ring R] (Wi Wk A Si Sk : R) (h1 : A * Wi = Wi * A - Wi) (h1' : A * Wk = Wk * A - Wk)
    (h2 : A * Si = Si * A - Si) (h2' : A * Sk = Sk * A - Sk) (h3 : Si * Wk = Wk * Si) (h3' : Sk * Wi = Wi * Sk)
    (h4 : Wi * Wk = Wk * Wi) (h5 : Si * Sk - Sk * Si = Wk * Si - Wi * Sk) :
    (Wi * A - Si) * (Wk * A - Sk) = (Wk * A - Sk) * (Wi * A - Si) := by
  have e1 : Wi * A * (Wk * A) = Wi * Wk * A * A - Wi * Wk * A := by
    rw [mul_assoc Wi A, ← mul_assoc A Wk A, h1']; noncomm_ring
  have e1' : Wk * A * (Wi * A) = Wi * Wk * A * A - Wi * Wk * A := by
    rw [mul_assoc Wk A, ← mul_assoc A Wi A, h1, h4]; noncomm_ring
  have e2 : Wi * A * Sk = Wi * Sk * A - Wi * Sk := by
    rw [mul_assoc Wi A, h2']; noncomm_ring
  have e2' : Wk * A * Si = Wk * Si * A - Wk * Si := by
    rw [mul_assoc Wk A, h2]; noncomm_ring
  have e3 : Si * (Wk * A) = Wk * Si * A := by rw [← mul_assoc, h3]
  have e3' : Sk * (Wi * A) = Wi * Sk * A := by rw [← mul_assoc, h3']
  have e5 : Si * Sk = Sk * Si + (Wk * Si - Wi * Sk) := by rw [← h5]; abel
  rw [sub_mul, sub_mul, mul_sub, mul_sub, mul_sub, mul_sub, e1, e1', e2, e2', e3, e3', e5]
  abel

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Sop_apply, Wm, LinearMap.mulLeft_apply, map_sum, glJ_X_mul]`. Rewrite using `[Finset.sum_comm (s := Cs) (t := Cs) (f := fun b' b => X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F))), ← Finset.sum_sub_distrib]`. Establish `e : ∀ b ∈ Cs, (∑ b' ∈ Cs, X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F))) - ∑ b' ∈ Cs, X (Fin.last K, b') * (X (Fin.last K, b) * glAct p LL K k b' (glAct p LL K i b F)) = (if b = k then X (Fin.last K, k) * ∑ b' ∈ Cs, X (Fin.last K, b') * glAct p …`. Introduce `b _`.

Rewrite using `[← Finset.sum_sub_distrib]`. Establish `e2 : ∀ b' ∈ Cs, X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F)) - X (Fin.last K, b') * (X (Fin.last K, b) * glAct p LL K k b' (glAct p LL K i b F)) = (if b = k then X (Fin.last K, k) * (X (Fin.last K, b') * glAct p LL K i b' F) else 0) - (if b' = …`. Introduce `b' _`. Use `Formalism.CountingSumsFrames.glAct_comm (p := p) LL K i b k b' F` as an intermediate fact. Rewrite `this` using `[sub_eq_iff_eq_add]`.

Rewrite using `[this]`. Use `split_ifs with h1 h2 h2`. Substitute `h1` using the available equality. Substitute `h2` using the available equality. Expand and normalize the polynomial expressions, which then agree.

Substitute `h1` using the available equality. Expand and normalize the polynomial expressions, which then agree. Substitute `h2` using the available equality. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl e2, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hi]`. Use `congr 1`. Use `split_ifs`. Rewrite using `[Finset.mul_sum]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hk, Finset.mul_sum]`.
-/
theorem S_S (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (i k : Fin r) (hi : i ∈ Cs) (hk : k ∈ Cs) :
    Sop p LL Cs i * Sop p LL Cs k - Sop p LL Cs k * Sop p LL Cs i =
      (Wm p K k : Module.End ℚ_[p] _) * Sop p LL Cs i - (Wm p K i : Module.End ℚ_[p] _) * Sop p LL Cs k := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Sop_apply, Wm, LinearMap.mulLeft_apply, map_sum, glJ_X_mul]
  rw [Finset.sum_comm (s := Cs) (t := Cs)
    (f := fun b' b => X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F))),
    ← Finset.sum_sub_distrib]
  have e : ∀ b ∈ Cs, (∑ b' ∈ Cs, X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F))) -
      ∑ b' ∈ Cs, X (Fin.last K, b') * (X (Fin.last K, b) * glAct p LL K k b' (glAct p LL K i b F)) =
      (if b = k then X (Fin.last K, k) * ∑ b' ∈ Cs, X (Fin.last K, b') * glAct p LL K i b' F else 0) -
        X (Fin.last K, i) * (X (Fin.last K, b) * glAct p LL K k b F) := by
    intro b _
    rw [← Finset.sum_sub_distrib]
    have e2 : ∀ b' ∈ Cs, X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F)) -
        X (Fin.last K, b') * (X (Fin.last K, b) * glAct p LL K k b' (glAct p LL K i b F)) =
        (if b = k then X (Fin.last K, k) * (X (Fin.last K, b') * glAct p LL K i b' F) else 0) -
          (if b' = i then X (Fin.last K, i) * (X (Fin.last K, b) * glAct p LL K k b F) else 0) := by
      intro b' _
      have := Formalism.CountingSumsFrames.glAct_comm (p := p) LL K i b k b' F
      rw [sub_eq_iff_eq_add] at this
      rw [this]
      split_ifs with h1 h2 h2
      · subst h1; subst h2; ring
      · subst h1; ring
      · subst h2; ring
      · ring
    rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hi]
    congr 1
    split_ifs
    · rw [Finset.mul_sum]
    · simp
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hk, Finset.mul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Uop_eq_Wm_mul_Aop_sub_Sop (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r) :
    Uop p LL c Cs i = (Wm p K i : Module.End ℚ_[p] _) * Aop p K r c - Sop p LL Cs i := rfl

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Aop_apply, Wm, LinearMap.mulLeft_apply, eul_X_mul, mul_sub, mul_smul_comm]`. Normalize the expressions using the abelian group laws.
-/
theorem aop_weightMul_comm (c : ℤ) (i : Fin r) :
    (Aop p K r c : Module.End ℚ_[p] _) * Wm p K i = (Wm p K i : Module.End ℚ_[p] _) * Aop p K r c - Wm p K i := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Aop_apply, Wm, LinearMap.mulLeft_apply, eul_X_mul, mul_sub,
    mul_smul_comm]
  abel

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Aop_apply, Sop_apply, map_sum, eul_X_mul, eul_glAct, map_sub, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]`. Normalize the expressions using the abelian group laws.
-/
theorem A_S (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r) :
    (Aop p K r c : Module.End ℚ_[p] _) * Sop p LL Cs i = Sop p LL Cs i * Aop p K r c - Sop p LL Cs i := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Aop_apply, Sop_apply, map_sum, eul_X_mul, eul_glAct, map_sub,
    map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
  abel

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, Sop_apply, Wm, LinearMap.mulLeft_apply, glJ_X_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem sop_comm_weightMul (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (i k : Fin r) :
    Sop p LL Cs i * Wm p K k = (Wm p K k : Module.End ℚ_[p] _) * Sop p LL Cs i := by
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, Sop_apply, Wm, LinearMap.mulLeft_apply, glJ_X_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, Wm, LinearMap.mulLeft_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wm_mul_Wm_comm (i k : Fin r) :
    (Wm p K i : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) * Wm p K k = Wm p K k * Wm p K i := by
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, Wm, LinearMap.mulLeft_apply]
  ring

/- English proof (translation)
Use `ring_UU (Wm p K i : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) (Wm p K k) (Aop p K r c) (Sop p LL Cs i) (Sop p LL Cs k) (aop_weightMul_comm c i) (aop_weightMul_comm c k) (A_S LL c Cs i) (A_S LL c Cs k) (sop_comm_weightMul LL Cs i k) (sop_comm_weightMul LL Cs k i …` as an intermediate fact. Rewrite `this` using `[← Uop_eq_Wm_mul_Aop_sub_Sop, ← Uop_eq_Wm_mul_Aop_sub_Sop]`. Conclude with `LinearMap.congr_fun this F`.
-/
theorem U_U (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i k : Fin r) (hi : i ∈ Cs) (hk : k ∈ Cs)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL c Cs i (Uop p LL c Cs k F) = Uop p LL c Cs k (Uop p LL c Cs i F) := by
  have := ring_UU (Wm p K i : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) (Wm p K k) (Aop p K r c)
    (Sop p LL Cs i) (Sop p LL Cs k) (aop_weightMul_comm c i) (aop_weightMul_comm c k) (A_S LL c Cs i) (A_S LL c Cs k) (sop_comm_weightMul LL Cs i k)
    (sop_comm_weightMul LL Cs k i) (Wm_mul_Wm_comm i k) (S_S LL Cs i k hi hk)
  rw [← Uop_eq_Wm_mul_Aop_sub_Sop, ← Uop_eq_Wm_mul_Aop_sub_Sop] at this
  exact LinearMap.congr_fun this F

end Rel

section GX
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem extendedAction_zero_zero (LL : Letters (K + 1)) (c : ℤ) : EX p (s := s) LL c 0 0 = Aop p K (s + 1) c := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EX_zs (LL : Letters (K + 1)) (c : ℤ) (j : Fin s) :
    EX p (s := s) LL c 0 (Fin.succ j) = dW p K (Fin.castSucc j) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EX_sz (LL : Letters (K + 1)) (c : ℤ) (i : Fin s) :
    EX p (s := s) LL c (Fin.succ i) 0 = Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EX_ss (LL : Letters (K + 1)) (c : ℤ) (i j : Fin s) :
    EX p (s := s) LL c (Fin.succ i) (Fin.succ j) = glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j) := rfl

/- English proof (translation)
The claim follows from `Finset.mem_erase.mpr ⟨(Fin.castSucc_lt_last i).ne, Finset.mem_univ _⟩`.
-/
theorem castSucc_mem (i : Fin s) : Fin.castSucc i ∈ (univ : Finset (Fin (s + 1))).erase (Fin.last s) :=
  Finset.mem_erase.mpr ⟨(Fin.castSucc_lt_last i).ne, Finset.mem_univ _⟩

def RelX (p : ℕ) [Fact p.Prime] {K s : ℕ} (LL : Letters (K + 1)) (c0 : ℤ) (a b c d : Fin (s + 1)) : Prop :=
  ∀ x, EX p LL c0 a b (EX p LL c0 c d x) - EX p LL c0 c d (EX p LL c0 a b x) =
    (if b = c then EX p LL c0 a d x else 0) - (if d = a then EX p LL c0 c b x else 0)

/- English proof (translation)
Introduce `x`. Rewrite using `[← neg_sub, h x, neg_sub]`.
-/
theorem RelX.symm {LL : Letters (K + 1)} {c0 : ℤ} {a b c d : Fin (s + 1)} (h : RelX p LL c0 a b c d) :
    RelX p LL c0 c d a b := by
  intro x
  rw [← neg_sub, h x, neg_sub]

/- English proof (translation)
Establish `hAD : ∀ j : Fin s, RelX p LL c0 0 0 0 (Fin.succ j)`. Introduce `j x`. Rewrite using `[if_pos rfl, if_neg (Fin.succ_ne_zero j), extendedAction_zero_zero, EX_zs, A_d, sub_zero]`. Establish `hAU : ∀ i : Fin s, RelX p LL c0 0 0 (Fin.succ i) 0`. Introduce `i x`.

Rewrite using `[if_pos rfl, if_neg (Fin.succ_ne_zero i).symm, extendedAction_zero_zero, EX_sz, A_U, zero_sub]`. Establish `heA : ∀ i j : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) 0 0`. Introduce `i j x`. Rewrite using `[if_neg (Fin.succ_ne_zero j), if_neg (Fin.succ_ne_zero i).symm, extendedAction_zero_zero, EX_ss, e_A, sub_zero]`. Establish `hDU : ∀ j i : Fin s, RelX p LL c0 0 (Fin.succ j) (Fin.succ i) 0`.

Introduce `j i x`. Rewrite using `[if_pos rfl, extendedAction_zero_zero, EX_zs, EX_sz, EX_ss, d_U LL hv c0 _ _ _ (castSucc_mem j)]`. Simplify using `only [Fin.succ_inj, Fin.castSucc_inj]`. Establish `heD : ∀ i j k : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) 0 (Fin.succ k)`. Introduce `i j k x`.

Rewrite using `[if_neg (Fin.succ_ne_zero j), EX_zs, EX_zs, EX_ss, dW_apply, dW_apply, dW_apply, pderiv_glAct LL hv]`. Simplify using `only [Fin.succ_inj, Fin.castSucc_inj]`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Simplify using the standard rewrite rules. Establish `heU : ∀ i j k : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) (Fin.succ k) 0`. Introduce `i j k x`. Rewrite using `[if_neg (Fin.succ_ne_zero i).symm, EX_sz, EX_sz, EX_ss, raising_comm_holds p K (s + 1) LL c0 _ _ _ _ x hv (castSucc_mem i) (castSucc_mem j), sub_zero]`.

Simplify using `only [Fin.succ_inj, Fin.castSucc_inj]`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>`. Apply the tactic sequence `refine Fin.cases ?_ (fun k => ?_) c <;> refine Fin.cases ?_ (fun l => ?_) d`. Introduce `x`. Simplify using the standard rewrite rules.

Conclude with `hAD l`. Conclude with `hAU k`. Conclude with `(heA k l).symm`. Conclude with `(hAD j).symm`. Introduce `x`.

Rewrite using `[if_neg (Fin.succ_ne_zero j), if_neg (Fin.succ_ne_zero l), EX_zs, EX_zs, dW_apply, dW_apply, dW_apply, dW_apply, ProjS.pderiv_comm]`. Simplify using the standard rewrite rules. Conclude with `hDU j k`. Conclude with `(heD k l j).symm`. Conclude with `(hAU i).symm`.

Conclude with `(hDU l i).symm`. Introduce `x`. Rewrite using `[if_neg (Fin.succ_ne_zero k).symm, if_neg (Fin.succ_ne_zero i).symm, EX_sz, EX_sz, U_U LL c0 _ _ _ (castSucc_mem i) (castSucc_mem k)]`. Simplify using the standard rewrite rules. Conclude with `(heU k l i).symm`.

Conclude with `heA i j`. Conclude with `heD i j l`. Conclude with `heU i j k`. Introduce `x`. Rewrite using `[EX_ss, EX_ss, EX_ss, EX_ss, Formalism.CountingSumsFrames.glAct_comm]`.

Simplify using `only [Fin.succ_inj, Fin.castSucc_inj]`.
-/
theorem relX (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c0 : ℤ) (a b c d : Fin (s + 1)) :
    RelX p LL c0 a b c d := by
  have hAD : ∀ j : Fin s, RelX p LL c0 0 0 0 (Fin.succ j) := by
    intro j x
    rw [if_pos rfl, if_neg (Fin.succ_ne_zero j), extendedAction_zero_zero, EX_zs, A_d, sub_zero]
  have hAU : ∀ i : Fin s, RelX p LL c0 0 0 (Fin.succ i) 0 := by
    intro i x
    rw [if_pos rfl, if_neg (Fin.succ_ne_zero i).symm, extendedAction_zero_zero, EX_sz, A_U, zero_sub]
  have heA : ∀ i j : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) 0 0 := by
    intro i j x
    rw [if_neg (Fin.succ_ne_zero j), if_neg (Fin.succ_ne_zero i).symm, extendedAction_zero_zero, EX_ss, e_A, sub_zero]
  have hDU : ∀ j i : Fin s, RelX p LL c0 0 (Fin.succ j) (Fin.succ i) 0 := by
    intro j i x
    rw [if_pos rfl, extendedAction_zero_zero, EX_zs, EX_sz, EX_ss, d_U LL hv c0 _ _ _ (castSucc_mem j)]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
  have heD : ∀ i j k : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) 0 (Fin.succ k) := by
    intro i j k x
    rw [if_neg (Fin.succ_ne_zero j), EX_zs, EX_zs, EX_ss, dW_apply, dW_apply, dW_apply, pderiv_glAct LL hv]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  have heU : ∀ i j k : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) (Fin.succ k) 0 := by
    intro i j k x
    rw [if_neg (Fin.succ_ne_zero i).symm, EX_sz, EX_sz, EX_ss,
      raising_comm_holds p K (s + 1) LL c0 _ _ _ _ x hv (castSucc_mem i) (castSucc_mem j), sub_zero]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    refine Fin.cases ?_ (fun k => ?_) c <;> refine Fin.cases ?_ (fun l => ?_) d
  · intro x; simp
  · exact hAD l
  · exact hAU k
  · exact (heA k l).symm
  · exact (hAD j).symm
  · intro x
    rw [if_neg (Fin.succ_ne_zero j), if_neg (Fin.succ_ne_zero l), EX_zs, EX_zs, dW_apply, dW_apply, dW_apply, dW_apply,
      ProjS.pderiv_comm]
    simp
  · exact hDU j k
  · exact (heD k l j).symm
  · exact (hAU i).symm
  · exact (hDU l i).symm
  · intro x
    rw [if_neg (Fin.succ_ne_zero k).symm, if_neg (Fin.succ_ne_zero i).symm, EX_sz, EX_sz,
      U_U LL c0 _ _ _ (castSucc_mem i) (castSucc_mem k)]
    simp
  · exact (heU k l i).symm
  · exact heA i j
  · exact heD i j l
  · exact heU i j k
  · intro x
    rw [EX_ss, EX_ss, EX_ss, EX_ss, Formalism.CountingSumsFrames.glAct_comm]
    simp only [Fin.succ_inj, Fin.castSucc_inj]

/- English proof (translation)
Use `Fin.cases ?_ (fun i => ?_) a` and prove the remaining obligations. Use `show coeff m (Aop p K (s + 1) c x) = ((c - ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ) : ℤ) : ℚ_[p]) * coeff m x`. Rewrite using `[Aop_apply, coeff_sub, coeff_smul, ProjS.coeff_eulL, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `coeff_cartan LL (K + 1) _ x m`.
-/
theorem coeff_EX_diag (LL : Letters (K + 1)) (c : ℤ) (a : Fin (s + 1))
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) :
    coeff m (EX p LL c a a x) = ((wtX LL c m a : ℤ) : ℚ_[p]) * coeff m x := by
  refine Fin.cases ?_ (fun i => ?_) a
  · show coeff m (Aop p K (s + 1) c x) = ((c - ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ) : ℤ) : ℚ_[p]) * coeff m x
    rw [Aop_apply, coeff_sub, coeff_smul, ProjS.coeff_eulL, smul_eq_mul]
    push_cast; ring
  · exact coeff_cartan LL (K + 1) _ x m

noncomputable def GX (p : ℕ) [Fact p.Prime] {K s : ℕ} (LL : Letters (K + 1)) (c : ℤ)
    (hv : LL.vec (Fin.last K) = true) : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1) :=
  mkGlW (EX p LL c) (wtX LL c) (fun a b c' d x => relX LL hv c a b c' d x) (coeff_EX_diag LL c)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GX_E (LL : Letters (K + 1)) (c : ℤ) (hv : LL.vec (Fin.last K) = true) :
    (GX p (s := s) LL c hv).E = EX p LL c := rfl

/- English proof (translation)
The claim follows from `coeff_compW (wtX LL c) μ x m`.
-/
theorem coeff_GX_comp (LL : Letters (K + 1)) (c : ℤ) (hv : LL.vec (Fin.last K) = true) (μ : Fin (s + 1) → ℤ)
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) :
    coeff m ((GX p LL c hv).comp μ x) = if wtX LL c m = μ then coeff m x else 0 :=
  coeff_compW (wtX LL c) μ x m

end GX

/- English proof (translation)
Introduce `p _ K s LL c hv`. Conclude with `⟨GX p LL c hv, GX_E LL c hv, fun μ x m => coeff_GX_comp LL c hv μ x m⟩`.
-/
theorem gl_action_exists : GXExists := by
  intro p _ K s LL c hv
  exact ⟨GX p LL c hv, GX_E LL c hv, fun μ x m => coeff_GX_comp LL c hv μ x m⟩

end Formalism.InvariantFactorPaths.L4
