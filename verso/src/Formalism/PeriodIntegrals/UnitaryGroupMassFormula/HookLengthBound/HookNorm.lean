import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

def Pn {N : ℕ} (ν : Fin N → ℕ) : ℕ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (ν i - ν j + (j - i) : ℕ)

def Qn {N : ℕ} (ν : Fin N → ℕ) : ℕ := ∏ i : Fin N, (ν i + (N - 1 - i)).factorial

/- English proof (translation)
Unfold `Pn`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
theorem Pn_succ_shift {N : ℕ} (μ : Fin N → ℕ) : Pn (fun i => μ i + 1) = Pn μ := by
  unfold Pn
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only
  omega

/- English proof (translation)
Unfold `Qn`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`. Establish `e : μ i + 1 + (N - 1 - (i : ℕ)) = (μ i + (N - 1 - (i : ℕ))) + 1` using `by omega`.

Establish `e2 : μ i + N - (i : ℕ) = μ i + (N - 1 - (i : ℕ)) + 1` using `by omega`. Rewrite using `[e, e2, Nat.factorial_succ]`.
-/
theorem Qn_succ_shift {N : ℕ} (μ : Fin N → ℕ) :
    Qn (fun i => μ i + 1) = (∏ i : Fin N, (μ i + N - i)) * Qn μ := by
  unfold Qn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have e : μ i + 1 + (N - 1 - (i : ℕ)) = (μ i + (N - 1 - (i : ℕ))) + 1 := by omega
  have e2 : μ i + N - (i : ℕ) = μ i + (N - 1 - (i : ℕ)) + 1 := by omega
  rw [e, e2, Nat.factorial_succ]

/- English proof (translation)
Use extensionality with `j`. Simplify using the standard rewrite rules.
-/
theorem Ioi_eq_filter {m : ℕ} (x : Fin m) : Finset.Ioi x = Finset.univ.filter (fun j => x < j) := by
  ext j
  simp

/- English proof (translation)
Rewrite using `[Ioi_eq_filter, Ioi_eq_filter, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]`. Simplify using `only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true]`.
-/
theorem prod_Ioi_castSucc {M : Type*} [CommMonoid M] (n : ℕ) (i : Fin n) (g : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Ioi (Fin.castSucc i), g j = (∏ j ∈ Finset.Ioi i, g (Fin.castSucc j)) * g (Fin.last n) := by
  rw [Ioi_eq_filter, Ioi_eq_filter, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true]

/- English proof (translation)
Unfold `Pn`. Rewrite using `[Fin.prod_univ_castSucc]`. Establish `hlast : ∏ j ∈ Finset.Ioi (Fin.last n), (ν (Fin.last n) - ν j + ((j : ℕ) - ((Fin.last n : Fin (n + 1)) : ℕ))) = 1`. Rewrite using `[Finset.eq_empty_of_forall_notMem fun j hj => absurd (Finset.mem_Ioi.mp hj) (not_lt.mpr (Fin.le_last j)), Finset.prod_empty]`. Rewrite using `[hlast, mul_one, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[prod_Ioi_castSucc]`. Simplify using `only [Fin.coe_castSucc, Fin.val_last, h]`. Apply the tactic sequence `congr 1 <;> omega`.
-/
theorem Pn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Pn ν = Pn (fun i : Fin n => ν (Fin.castSucc i)) * ∏ i : Fin n, (ν (Fin.castSucc i) + (n - i)) := by
  unfold Pn
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n), (ν (Fin.last n) - ν j + ((j : ℕ) - ((Fin.last n : Fin (n + 1)) : ℕ))) = 1 := by
    rw [Finset.eq_empty_of_forall_notMem fun j hj => absurd (Finset.mem_Ioi.mp hj) (not_lt.mpr (Fin.le_last j)), Finset.prod_empty]
  rw [hlast, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_Ioi_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, h]
  congr 1 <;> omega

/- English proof (translation)
Unfold `Qn`. Rewrite using `[Fin.prod_univ_castSucc, h, ← Finset.prod_mul_distrib]`. Establish `hl : (0 + (n + 1 - 1 - ((Fin.last n : Fin (n + 1)) : ℕ))).factorial = 1`. Simplify using the standard rewrite rules. Rewrite using `[hl, mul_one]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`. Simplify using `only [Fin.coe_castSucc]`. Establish `e : ν (Fin.castSucc i) + (n + 1 - 1 - (i : ℕ)) = (ν (Fin.castSucc i) + (n - 1 - (i : ℕ))) + 1` using `by omega`. Rewrite using `[e, Nat.factorial_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem Qn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Qn ν = (∏ i : Fin n, (ν (Fin.castSucc i) + (n - i))) * Qn (fun i : Fin n => ν (Fin.castSucc i)) := by
  unfold Qn
  rw [Fin.prod_univ_castSucc, h, ← Finset.prod_mul_distrib]
  have hl : (0 + (n + 1 - 1 - ((Fin.last n : Fin (n + 1)) : ℕ))).factorial = 1 := by
    simp
  rw [hl, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [Fin.coe_castSucc]
  have e : ν (Fin.castSucc i) + (n + 1 - 1 - (i : ℕ)) = (ν (Fin.castSucc i) + (n - 1 - (i : ℕ))) + 1 := by omega
  rw [e, Nat.factorial_succ]
  congr 1
  omega

/- English proof (translation)
Introduce `a b h`. Simplify using `only [Prod.mk.injEq, Fin.castSucc_inj] at h`. Conclude with `Prod.ext h.1 h.2`.
-/
theorem castSucc2_injective (n : ℕ) :
    Function.Injective (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) := by
  intro a b h
  simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2

/- English proof (translation)
Introduce `hR hH hL hS`. It suffices to establish `key : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by`. Introduce `N ν hν`. Use `key N ν hν` as an intermediate fact. Unfold `Pn Qn at this`.

Simplify using `only [Nat.cast_prod] at this`. Conclude with `this`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro ν _`.

Simplify using `[Pn, Qn, hw, fockQ]`. Consider the case `succ n ih`. It suffices to establish `hk : ∀ (k : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = k → fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by`. Introduce `ν hν`. Conclude with `hk _ ν hν rfl`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `ν hν h0`. Establish `hν' : Antitone (fun i : Fin n => ν i.castSucc)` using `fun a b hab => hν (Fin.castSucc_le_castSucc_iff.2 hab)`.

Rewrite using `[hL n ν hν h0, hR _ _ _ (castSucc2_injective n), Pn_last_zero n ν h0, Qn_last_zero n ν h0, Nat.cast_mul, Nat.cast_mul, ← ih _ hν']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ k ihk`. Introduce `ν hν hk`. Establish `hge : ∀ i, 1 ≤ ν i` using `fun i => by have := hν (Fin.le_last i); omega`.

Take `⟨μ, rfl⟩ : ∃ μ : Fin (n + 1) → ℕ, ν = fun i => μ i + 1` from `⟨fun i => ν i - 1, funext fun i => by have := hge i; show ν i = ν i - 1 + 1; omega⟩`. Establish `hμ : Antitone μ` using `fun a b hab => by have := hν hab; simp only at this; omega`. Establish `hμk : μ (Fin.last n) = k` using `by simp only at hk; omega`. Rewrite using `[Pn_succ_shift, Qn_succ_shift, hH _ μ hμ, hS _ μ hμ, Nat.cast_mul, Nat.cast_prod, ← ihk μ hμ hμk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hook_norm : HookNormOf := by
  intro hR hH hL hS
  suffices key : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
    intro N ν hν
    have := key N ν hν
    unfold Pn Qn at this
    simp only [Nat.cast_prod] at this
    exact this
  intro N
  induction N with
  | zero => intro ν _; simp [Pn, Qn, hw, fockQ]
  | succ n ih =>
    suffices hk : ∀ (k : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = k →
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
      intro ν hν; exact hk _ ν hν rfl
    intro k
    induction k with
    | zero =>
      intro ν hν h0
      have hν' : Antitone (fun i : Fin n => ν i.castSucc) :=
        fun a b hab => hν (Fin.castSucc_le_castSucc_iff.2 hab)
      rw [hL n ν hν h0, hR _ _ _ (castSucc2_injective n), Pn_last_zero n ν h0, Qn_last_zero n ν h0,
        Nat.cast_mul, Nat.cast_mul, ← ih _ hν']
      ring
    | succ k ihk =>
      intro ν hν hk
      have hge : ∀ i, 1 ≤ ν i := fun i => by have := hν (Fin.le_last i); omega
      obtain ⟨μ, rfl⟩ : ∃ μ : Fin (n + 1) → ℕ, ν = fun i => μ i + 1 :=
        ⟨fun i => ν i - 1, funext fun i => by have := hge i; show ν i = ν i - 1 + 1; omega⟩
      have hμ : Antitone μ := fun a b hab => by have := hν hab; simp only at this; omega
      have hμk : μ (Fin.last n) = k := by simp only at hk; omega
      rw [Pn_succ_shift, Qn_succ_shift, hH _ μ hμ, hS _ μ hμ, Nat.cast_mul, Nat.cast_prod,
        ← ihk μ hμ hμk]
      ring

end PI.HookSteps
