import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Derivation.leibniz_pow]`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[smul_comm a, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]`.

Use `congr 1`. Take `⟨j, rfl⟩ : ∃ j, m = j + 1` from `⟨m - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kaehler_D_of_pow_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S) (m : ℕ) (h : a ^ m = b) :
    a • KaehlerDifferential.D R S b = ((m : S) * b) • KaehlerDifferential.D R S a := by
  subst h
  rw [Derivation.leibniz_pow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [smul_comm a, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : (zS T (n + (k + 1)) : Ω) ^ p = (zS T (n + k) : Ω)` using `T.ζpow (n + k)`.

Establish `h2 : (zS T (n + k) : Ω) ^ (p ^ k) = (zS T n : Ω)` using `congrArg Subtype.val ih`. Simplify using `only [SubmonoidClass.coe_pow]`. Rewrite using `[pow_succ', pow_mul, h1, h2]`.
-/
theorem zS_pow (T : Tower p Ω) (n k : ℕ) : zS T (n + k) ^ (p ^ k) = zS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (zS T (n + (k + 1)) : Ω) ^ p = (zS T (n + k) : Ω) := T.ζpow (n + k)
    have h2 : (zS T (n + k) : Ω) ^ (p ^ k) = (zS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : (qS T (n + (k + 1)) : Ω) ^ p = (qS T (n + k) : Ω)` using `T.qpow (n + k)`.

Establish `h2 : (qS T (n + k) : Ω) ^ (p ^ k) = (qS T n : Ω)` using `congrArg Subtype.val ih`. Simplify using `only [SubmonoidClass.coe_pow]`. Rewrite using `[pow_succ', pow_mul, h1, h2]`.
-/
theorem qS_pow (T : Tower p Ω) (n k : ℕ) : qS T (n + k) ^ (p ^ k) = qS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (qS T (n + (k + 1)) : Ω) ^ p = (qS T (n + k) : Ω) := T.qpow (n + k)
    have h2 : (qS T (n + k) : Ω) ^ (p ^ k) = (qS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

/- English proof (translation)
Introduce `p _ Ω _ _ T n k`. Prove the components needed by the constructor for the conclusion. Use `kaehler_D_of_pow_eq (R := O0 p) _ _ _ (zS_pow T n k)` as an intermediate fact. Simplify `this` using `[Nat.cast_pow]`. Use `kaehler_D_of_pow_eq (R := O0 p) _ _ _ (qS_pow T n k)` as an intermediate fact.

Simplify `this` using `[Nat.cast_pow]`.
-/
theorem dlog_transition : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (n k : ℕ), zS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * zS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T (n + k)) ∧ qS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * qS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T (n + k)) := by
  intro p _ Ω _ _ T n k
  constructor
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (zS_pow T n k)
    simpa [Nat.cast_pow] using this
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (qS_pow T n k)
    simpa [Nat.cast_pow] using this

end GlobalTheory.AlmostEt
