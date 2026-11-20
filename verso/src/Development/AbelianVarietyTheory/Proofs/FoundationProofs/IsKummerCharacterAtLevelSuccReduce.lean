import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Rewrite using `[← Complex.exp_nat_mul]`. Establish `hl' : (l : ℂ) ≠ 0` using `by exact_mod_cast hl`. Establish `hv : (v : ℂ) = ((v % l ^ n : ℕ) : ℂ) + (l : ℂ) ^ n * ((v / l ^ n : ℕ) : ℂ)`. Conclude with `(Nat.mod_add_div v (l ^ n)).symm` after adjusting the coercions. Establish `e : (l : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) = 2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n) + ((v / l ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I)`.

Rewrite using `[hv]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]`.
-/
theorem exp_pow_reduce (l n v : ℕ) (hl : l ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) ^ l =
      Complex.exp (2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  rw [← Complex.exp_nat_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hv : (v : ℂ) = ((v % l ^ n : ℕ) : ℂ) + (l : ℂ) ^ n * ((v / l ^ n : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mod_add_div v (l ^ n)).symm
  have e : (l : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) =
      2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n) +
        ((v / l ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hv]; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Introduce `Ω _ _ ε X l _ n x χ ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Use `haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩`. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl0⟩`. Use `⟨f, fun z => a z ^ l, fun z => b z ^ l, M, hM, ?_, ⟨ha.pow l, hb.pow l, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `h` using `AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x`. Express the relevant statement in the definitionally equal form `x.val n = _`. Rewrite using `[← h]`. Express the relevant statement in the definitionally equal form `AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n) (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x) = _`. Rewrite using `[hx]`.

Both sides reduce to the same expression. Introduce `h`. Apply `hb0` to reduce the goal to its premises. Rewrite `h`, the goal using `[← Filter.Germ.coe_zero, Filter.Germ.coe_eq]`. Conclude with `h.mono fun z hz => (pow_eq_zero_iff hl0).1 hz`.

Establish `e1 : ((fun z => b z ^ l : ℂ → ℂ) : Mero) = (b : Mero) ^ l` using `Filter.Germ.coe_pow b l`. Establish `e2 : ((fun z => a z ^ l : ℂ → ℂ) : Mero) = (a : Mero) ^ l` using `Filter.Germ.coe_pow a l`. Rewrite using `[e1, e2, ← pow_mul, ← pow_mul, ← pow_succ', hab]`. Introduce `δ hδ z hz`. Establish `h1` using `congrArg (fun t : ℂ => t ^ l) (hrel δ hδ z hz)`.

Simplify using `only [mul_pow] at h1`. Rewrite `h1` using `[exp_pow_reduce l n _ hl0]`. Establish `hv : (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)).val = (χ δ).val % l ^ n`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]`. Rewrite using `[hv]`.

Simplify `h1` using `only [mul_pow, mul_assoc]`.
-/
theorem kum_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ →
      Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  intro Ω _ _ ε X l _ n x χ ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl0⟩
  refine ⟨f, fun z => a z ^ l, fun z => b z ^ l, M, hM, ?_, ⟨ha.pow l, hb.pow l, ?_, ?_⟩, ?_⟩
  · have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x
    change x.val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n) (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x) = _
    rw [hx]
    rfl
  · intro h
    apply hb0
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at h ⊢
    exact h.mono fun z hz => (pow_eq_zero_iff hl0).1 hz
  · have e1 : ((fun z => b z ^ l : ℂ → ℂ) : Mero) = (b : Mero) ^ l := Filter.Germ.coe_pow b l
    have e2 : ((fun z => a z ^ l : ℂ → ℂ) : Mero) = (a : Mero) ^ l := Filter.Germ.coe_pow a l
    rw [e1, e2, ← pow_mul, ← pow_mul, ← pow_succ', hab]
  · intro δ hδ z hz
    have h1 := congrArg (fun t : ℂ => t ^ l) (hrel δ hδ z hz)
    simp only [mul_pow] at h1
    rw [exp_pow_reduce l n _ hl0] at h1
    have hv : (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)).val = (χ δ).val % l ^ n := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [hv]
    simpa only [mul_pow, mul_assoc] using h1

end GlobalTheory.KZ.H3
