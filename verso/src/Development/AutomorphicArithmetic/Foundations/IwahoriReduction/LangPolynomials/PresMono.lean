import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih => rw [pow_succ', pow_mul, ← add_assoc, (h (n + d)).2, ih]`.
-/
private theorem roots_pow {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : Roots l ζ) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, (h (n + d)).2, ih]

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a`.
-/
private theorem nat_le_one {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)`.
-/
private theorem add_le {l : ℕ} [Fact l.Prime] {a b : Qbar l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)

/- English proof (translation)
Introduce `l _ hl Ω _ _ _ A hA c β ζ hζ Z Z' m n n' P hn hZ hP`. Take `⟨h1, h2, h3, h4, h5⟩` from `hP`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Establish `hlp : l.Prime` using `Fact.out`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`.

Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hlp.pos i).ne'⟩ infer_instance`. Use `haveI : NeZero (l ^ n') := ⟨(pow_pos hlp.pos n').ne'⟩`. Use `⟨(hζ n').1, hn.trans h2, h3, h4, fun s hs hc _ => ?_⟩` and prove the remaining obligations. Take `⟨k, hk, hcg⟩` from `h5 s hs hc (fix_of_cycMod h2 hc h1.pow_eq_one)`.

Use `⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩` and prove the remaining obligations. Take `⟨v, hv, hsv⟩` from `hk i`. Use `⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm d n', hv], ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, roots_pow hζ, ZMod.val_natCast]`. Use `congr 1`.

Use `conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n'), pow_add, pow_mul, (hζ n').1.pow_eq_one, one_pow, one_mul]`. Establish `hz` using `hZ s ⟨hs, hc⟩`. Unfold `Cg at hz hcg ⊢`. Establish `e1 : ‖Z m s 1 - ∑ i, β.val i * (((k i).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖`. Use `hcg.trans ?_` and prove the remaining obligations.

Rewrite using `[pow_add, norm_mul]`. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations. Conclude with `nat_le_one (l := l) (l ^ d)` after adjusting the coercions. Establish `e2 : ‖∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ 1`. Use `Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ 1) (fun a b => add_le) (by simp) (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (h4 i) (norm_nonneg _) (nat_le_one _)`. Establish `e3 : ‖((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖`. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) e2`.

Rewrite `hz` using `[norm_sub_rev]`. Establish `e4 : ∑ i, β.val i * (((k i).val : ℕ) : Qbar l) = ((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l)) + ∑ i, β.val i * (((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ZMod.val_natCast]`.

Use `conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n')]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `add_le (add_le hz e1) e3` as an intermediate fact. Rewrite `this` using `[e4]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pPresMono : SPresMono := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z Z' m n n' P hn hZ hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hlp.pos i).ne'⟩
    infer_instance
  haveI : NeZero (l ^ n') := ⟨(pow_pos hlp.pos n').ne'⟩
  refine ⟨(hζ n').1, hn.trans h2, h3, h4, fun s hs hc _ => ?_⟩
  obtain ⟨k, hk, hcg⟩ := h5 s hs hc (fix_of_cycMod h2 hc h1.pow_eq_one)
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hk i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm d n', hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, roots_pow hζ, ZMod.val_natCast]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n'), pow_add, pow_mul, (hζ n').1.pow_eq_one, one_pow, one_mul]
  · have hz := hZ s ⟨hs, hc⟩
    unfold Cg at hz hcg ⊢
    have e1 : ‖Z m s 1 - ∑ i, β.val i * (((k i).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine hcg.trans ?_
      rw [pow_add, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      exact_mod_cast nat_le_one (l := l) (l ^ d)
    have e2 : ‖∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ 1 := by
      refine Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ 1) (fun a b => add_le) (by simp) (fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (h4 i) (norm_nonneg _) (nat_le_one _)
    have e3 : ‖((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) e2
    rw [norm_sub_rev] at hz
    have e4 : ∑ i, β.val i * (((k i).val : ℕ) : Qbar l) =
        ((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l)) +
        ∑ i, β.val i * (((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZMod.val_natCast]
      conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n')]
      push_cast
      ring
    have := add_le (add_le hz e1) e3
    rw [e4] at this
    convert this using 2
    ring

end UpperTheory.Kd.C7
