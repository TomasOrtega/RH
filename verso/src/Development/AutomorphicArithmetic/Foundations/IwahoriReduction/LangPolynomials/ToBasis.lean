import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.ToBasisLogarithm

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`. Conclude with `z.2`.
-/
private theorem norm_alg_le (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact z.2

/- English proof (translation)
Simplify using `using norm_alg_le (l := l) (a : ℤ_[l])`.
-/
private theorem norm_nat_le (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 := by
  simpa using norm_alg_le (l := l) (a : ℤ_[l])

/- English proof (translation)
Unfold `Cg`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => h i`.
-/
private theorem cg_sum {ι : Type} [Fintype ι] (n : ℕ) (f g : ι → Qbar l) (h : ∀ i, Cg n (f i) (g i)) :
    Cg n (∑ i, f i) (∑ i, g i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => h i

/- English proof (translation)
Unfold `Cg at *`. Rewrite using `[← sub_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) hy).trans h`.
-/
private theorem cg_mul {n : ℕ} {a b y : Qbar l} (h : Cg n a b) (hy : ‖y‖ ≤ 1) : Cg n (a * y) (b * y) := by
  unfold Cg at *
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans h

/- English proof (translation)
Unfold `Cg at *`. Rewrite using `[show a - c = (a - b) + (b - c) by ring]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')`.
-/
private theorem cg_trans {n : ℕ} {a b c : Qbar l} (h : Cg n a b) (h' : Cg n b c) : Cg n a c := by
  unfold Cg at *
  rw [show a - c = (a - b) + (b - c) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

/- English proof (translation)
Take `⟨e, he⟩` from `(Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm)`. Establish `he' : (x : Qbar l) - y = (l : Qbar l) ^ n * (e : Qbar l)` using `by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) he`. Establish `hn : ‖(e : Qbar l)‖ ≤ 1` using `by simpa using norm_alg_le (l := l) (e : ℤ_[l])`. Unfold `Cg`. Rewrite using `[he', norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) hn`.
-/
private theorem cg_nat {n x y : ℕ} (h : (x : ZMod (l ^ n)) = y) : Cg n (x : Qbar l) y := by
  obtain ⟨e, he⟩ := (Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm)
  have he' : (x : Qbar l) - y = (l : Qbar l) ^ n * (e : Qbar l) := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) he
  have hn : ‖(e : Qbar l)‖ ≤ 1 := by simpa using norm_alg_le (l := l) (e : ℤ_[l])
  unfold Cg
  rw [he', norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hn

/- English proof (translation)
Use `⟨fun i => (β.e.repr ⟨o, ho⟩ i).appr n, ?_⟩` and prove the remaining obligations. Establish `h1 : o = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)`. Use `congrArg (fun x : c.O => (x : PadicAlgCl l)) (β.e.sum_repr ⟨o, ho⟩)` as an intermediate fact. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul] at this`. Use `this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression. Use `cg_trans (b := ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)) ?_ (cg_sum n _ _ fun i => ?_)` and prove the remaining obligations. Unfold `Cg`. Rewrite using `[← h1, sub_self, norm_zero]`.

Conclude with `norm_nonneg _`. Rewrite using `[mul_comm (β.val i), mul_comm (β.val i)]`. Use `cg_mul ?_ (hβ i)` and prove the remaining obligations. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n (β.e.repr ⟨o, ho⟩ i))`. Use `congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he` as an intermediate fact.

Rewrite `this` using `[map_mul, map_pow, map_natCast, map_sub, map_natCast]`. Unfold `Cg`. Rewrite using `[← this, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le e)`.
-/
private theorem coords {c : Coef l} (β : Bas c) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (n : ℕ) (o : Qbar l) (ho : o ∈ c.O) :
    ∃ a : Fin β.d → ℕ, Cg n o (∑ i, β.val i * (a i : Qbar l)) := by
  refine ⟨fun i => (β.e.repr ⟨o, ho⟩ i).appr n, ?_⟩
  have h1 : o = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i) := by
    have := congrArg (fun x : c.O => (x : PadicAlgCl l)) (β.e.sum_repr ⟨o, ho⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]; rfl
  refine cg_trans (b := ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)) ?_ (cg_sum n _ _ fun i => ?_)
  · unfold Cg; rw [← h1, sub_self, norm_zero]; exact norm_nonneg _
  · rw [mul_comm (β.val i), mul_comm (β.val i)]
    refine cg_mul ?_ (hβ i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n (β.e.repr ⟨o, ho⟩ i))
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    unfold Cg
    rw [← this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le e)

/- English proof (translation)
Establish `e : ∑ i, b i * ∑ k, (a k i : Qbar l) * y k = ∑ k, (∑ i, b i * (a k i : Qbar l)) * y k`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`. Rewrite using `[e]`. Conclude with `cg_sum n _ _ fun k => cg_mul (h k) (hy k)`.
-/
private theorem cg_swap {ι : Type} [Fintype ι] {d n : ℕ} (b : Fin d → Qbar l) (o y : ι → Qbar l) (a : ι → Fin d → ℕ)
    (h : ∀ k, Cg n (o k) (∑ i, b i * (a k i : Qbar l))) (hy : ∀ k, ‖y k‖ ≤ 1) :
    Cg n (∑ k, o k * y k) (∑ i, b i * ∑ k, (a k i : Qbar l) * y k) := by
  have e : ∑ i, b i * ∑ k, (a k i : Qbar l) * y k = ∑ k, (∑ i, b i * (a k i : Qbar l)) * y k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e]
  exact cg_sum n _ _ fun k => cg_mul (h k) (hy k)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert k S hk ih`. Establish `h0 : (∏ k ∈ S, P k ^ a k).eval z ≠ 0`. Rewrite using `[Polynomial.eval_prod]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => by rw [Polynomial.eval_pow]; exact pow_ne_zero _ (hP k)`. Establish `hk0` using `hP k`. Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk, ← ih, Polynomial.derivative_mul, Polynomial.derivative_pow]`. Simplify using `only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]`. Break down `a k with _ | r` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel, pow_succ]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem logd {Ω : Type} [Field Ω] {ι : Type} (S : Finset ι) (P : ι → Polynomial Ω) (a : ι → ℕ) (z : Ω)
    (hP : ∀ k, (P k).eval z ≠ 0) :
    z * (Polynomial.derivative (∏ k ∈ S, P k ^ a k)).eval z / (∏ k ∈ S, P k ^ a k).eval z =
      ∑ k ∈ S, (a k : Ω) * (z * (Polynomial.derivative (P k)).eval z / (P k).eval z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h0 : (∏ k ∈ S, P k ^ a k).eval z ≠ 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [Polynomial.eval_pow]; exact pow_ne_zero _ (hP k)
    have hk0 := hP k
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ← ih, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rcases a k with _ | r
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [Polynomial.map_add, Polynomial.eval_add]`. Conclude with `A.add_mem _ _ hp hq`. Consider the case `monomial n a`. Rewrite using `[Polynomial.map_monomial, Polynomial.eval_monomial]`.

Conclude with `A.mul_mem _ _ a.2.1 (A.toSubring.pow_mem hz n)`.
-/
private theorem pv_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) {z : Ω} (hz : z ∈ A) :
    (P.map (R0 A).subtype).eval z ∈ A := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, Polynomial.eval_add]; exact A.add_mem _ _ hp hq
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    exact A.mul_mem _ _ a.2.1 (A.toSubring.pow_mem hz n)

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add, map_add, hp, hq]`. Consider the case `monomial n a`. Rewrite using `[Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow]`. Use `congr 1`.

Conclude with `(a.2.2 s hs).symm`.
-/
private theorem pv_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    (P.map (R0 A).subtype).eval (s z) = s ((P.map (R0 A).subtype).eval z) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add, map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow]
    congr 1
    exact (a.2.2 s hs).symm

/- English proof (translation)
Break down `A.mem_or_inv_mem z with h | h` into its components or cases. Conclude with `h`. Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hN.ne'`. Establish `e : z = (z⁻¹) ^ k`. Rewrite using `[inv_pow]; exact eq_inv_of_mul_eq_one_right (by rw [← hz, pow_succ])`.

Rewrite using `[e]`. Conclude with `A.toSubring.pow_mem h k`.
-/
private theorem root_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {z : Ω} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with h | h
  · exact h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right (by rw [← hz, pow_succ])
    rw [e]; exact A.toSubring.pow_mem h k

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hc : ((b : ZMod (l ^ m)).val).Coprime l` using `Nat.Coprime.coprime_dvd_right (dvd_pow_self l (by omega)) (ZMod.val_coe_unit_coprime b)`. Establish `hu : IsUnit (((b : ZMod (l ^ m)).val : ℕ) : ℤ_[l])`.

Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `PadicInt.norm_natCast_eq_one_iff.2 hc.symm`. Take `⟨s, hs, hs'⟩` from `h hu.unit`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `h1` using `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) z hz`.

Establish `h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)) = hu.unit` using `hs'`. Rewrite `h1` using `[h2, IsUnit.unit_spec, map_natCast, ZMod.natCast_zmod_val]`. Conclude with `h1`.
-/
private theorem ex_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}
    (h : ∀ u : ℤ_[l]ˣ, ∃ s ∈ Ine (F := ℚ) A, cycZ ℚ Ω l s = u) {m : ℕ} (hm : 1 ≤ m) {z : Ω} (hz : z ^ l ^ m = 1)
    (b : (ZMod (l ^ m))ˣ) : ∃ s ∈ Ine (F := ℚ) A, s z = z ^ (b : ZMod (l ^ m)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hc : ((b : ZMod (l ^ m)).val).Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self l (by omega)) (ZMod.val_coe_unit_coprime b)
  have hu : IsUnit (((b : ZMod (l ^ m)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 hc.symm
  obtain ⟨s, hs, hs'⟩ := h hu.unit
  refine ⟨s, hs, ?_⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) z hz
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)) = hu.unit := hs'
  rw [h2, IsUnit.unit_spec, map_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

end UpperTheory.Kd.C7.ToBasisLogarithm

open UpperTheory.Kd.C7.ToBasisLogarithm in
/- English proof (translation)
Introduce `l _ hl Ω _ _ _ A hA c β ζ hζ j hj Z m n ι _ P o hm hP ho hK`. Take `⟨hprim, hnm, hu, ho1, hpres⟩` from `hK`. Establish `hβ` using `((pBasEx l c).2 β).1`. Establish `hfr` using `(pFrobEx l hl Ω A hA).2.2`. Use `choose a ha using fun k => coords β hβ n (o k) (ho k)`.

Establish `hQ : ∀ k, ∃ Q : Polynomial (R0 A), Q.map (R0 A).subtype = P k` using `fun k => ⟨(P k).toSubring (R0 A) (fun x hx => hP k x hx), Polynomial.map_toSubring _ _ _⟩`. Use `choose Q hQ using hQ`. Establish `hmap : ∀ i, (∏ k, Q k ^ a k i).map (R0 A).subtype = ∏ k, P k ^ a k i` using `fun i => by`. Simplify using `only [Polynomial.map_prod, Polynomial.map_pow, hQ]`. Establish `hpv : ∀ i, pv (∏ k, Q k ^ a k i) (ζ m) = ∏ k, (P k).eval (ζ m) ^ a k i` using `fun i => by`.

Rewrite using `[pv, Polynomial.eval₂_eq_eval_map, hmap, Polynomial.eval_prod]`. Simplify using `only [Polynomial.eval_pow]`. Use `⟨fun i => ∏ k, Q k ^ a k i, ⟨hprim, hnm, fun i => ?_, hβ, fun s hs hc hz => ?_⟩, fun b => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hpv]`.

Use `⟨A.toSubring.prod_mem fun k _ => A.toSubring.pow_mem (hu k).1 _, Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hu k).2.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_inv_distrib]`. Conclude with `A.toSubring.prod_mem fun k _ => by rw [← inv_pow]; exact A.toSubring.pow_mem (hu k).2.2 _`. Take `⟨κ, hκ, hcg⟩` from `hpres s hs hc hz`. Establish `hKA` using `(pKumAlg l hl Ω A hA ζ hζ m n hnm s ⟨hs, hc⟩).1`.

Use `⟨fun i => ∑ k, (a k i : ZMod (l ^ n)) * κ k, fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hpv]`. Generalize the expression as in `(Finset.univ : Finset ι) = S`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => simpa using kumVal_one (l := l) n (ζ n) s`. Consider the case `insert k S hk ih`. Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk]`. Conclude with `(hKA _ _ _ _ ((hKA _ _ _ _ (hκ k) (hκ k)).2.2 (a k i)) ih).1`. Use `cg_trans hcg (cg_trans (cg_swap β.val o _ a ha fun k => norm_nat_le _) (cg_sum n _ _ fun i => ?_))` and prove the remaining obligations.

Rewrite using `[mul_comm (β.val i), mul_comm (β.val i)]`. Use `cg_mul ?_ (hβ i)` and prove the remaining obligations. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `cg_nat (l := l) (n := n) (x := ∑ k, a k i * (κ k).val) (y := (∑ k, (a k i : ZMod (l ^ n)) * κ k).val) (by simp)` as an intermediate fact. Simplify using `using this`.

Take `⟨s, hs, hsz⟩` from `ex_conj hfr hm (hζ m).1.pow_eq_one b`. Establish `hzA : ζ m ∈ A` using `root_mem A (pow_pos (Fact.out : l.Prime).pos m) (hζ m).1.pow_eq_one`. Establish `hz : ζ m ^ (b : ZMod (l ^ m)).val ∈ A` using `A.toSubring.pow_mem hzA _`. Establish `hev : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) = s ((P k).eval (ζ m))` using `fun k => by`. Rewrite using `[← hsz, ← hQ, pv_conj _ _ hs]`.

Establish `hne : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) ≠ 0` using `fun k => by`. Rewrite using `[hev]`. Conclude with `(map_ne_zero s).2 (hu k).2.1`. Unfold `htv`. Simplify using `only [hmap, logd _ P _ _ hne, map_sum, map_mul j, map_natCast]`.

Use `cg_swap β.val o _ a ha fun k => hj _ ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Use `A.mul_mem _ _ (A.mul_mem _ _ hz ?_) ?_` and prove the remaining obligations. Rewrite using `[← hQ, Polynomial.derivative_map]`. Conclude with `pv_mem _ hz`.

Rewrite using `[hev, ← map_inv₀, apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs)]`. Conclude with `(hu k).2.2`.
-/
theorem UpperTheory.Kd.C7.pToBasis :
    UpperTheory.Kd.C7.SToBasis := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ j hj Z m n ι _ P o hm hP ho hK
  classical
  obtain ⟨hprim, hnm, hu, ho1, hpres⟩ := hK
  have hβ := ((pBasEx l c).2 β).1
  have hfr := (pFrobEx l hl Ω A hA).2.2
  choose a ha using fun k => coords β hβ n (o k) (ho k)
  have hQ : ∀ k, ∃ Q : Polynomial (R0 A), Q.map (R0 A).subtype = P k := fun k =>
    ⟨(P k).toSubring (R0 A) (fun x hx => hP k x hx), Polynomial.map_toSubring _ _ _⟩
  choose Q hQ using hQ
  have hmap : ∀ i, (∏ k, Q k ^ a k i).map (R0 A).subtype = ∏ k, P k ^ a k i := fun i => by
    simp only [Polynomial.map_prod, Polynomial.map_pow, hQ]
  have hpv : ∀ i, pv (∏ k, Q k ^ a k i) (ζ m) = ∏ k, (P k).eval (ζ m) ^ a k i := fun i => by
    rw [pv, Polynomial.eval₂_eq_eval_map, hmap, Polynomial.eval_prod]
    simp only [Polynomial.eval_pow]
  refine ⟨fun i => ∏ k, Q k ^ a k i, ⟨hprim, hnm, fun i => ?_, hβ, fun s hs hc hz => ?_⟩, fun b => ?_⟩
  · dsimp only
    rw [hpv]
    refine ⟨A.toSubring.prod_mem fun k _ => A.toSubring.pow_mem (hu k).1 _,
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hu k).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact A.toSubring.prod_mem fun k _ => by rw [← inv_pow]; exact A.toSubring.pow_mem (hu k).2.2 _
  · obtain ⟨κ, hκ, hcg⟩ := hpres s hs hc hz
    have hKA := (pKumAlg l hl Ω A hA ζ hζ m n hnm s ⟨hs, hc⟩).1
    refine ⟨fun i => ∑ k, (a k i : ZMod (l ^ n)) * κ k, fun i => ?_, ?_⟩
    · dsimp only
      rw [hpv]
      generalize (Finset.univ : Finset ι) = S
      induction S using Finset.induction_on with
      | empty => simpa using kumVal_one (l := l) n (ζ n) s
      | insert k S hk ih =>
        rw [Finset.prod_insert hk, Finset.sum_insert hk]
        exact (hKA _ _ _ _ ((hKA _ _ _ _ (hκ k) (hκ k)).2.2 (a k i)) ih).1
    · refine cg_trans hcg (cg_trans (cg_swap β.val o _ a ha fun k => norm_nat_le _) (cg_sum n _ _ fun i => ?_))
      rw [mul_comm (β.val i), mul_comm (β.val i)]
      refine cg_mul ?_ (hβ i)
      haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      have := cg_nat (l := l) (n := n) (x := ∑ k, a k i * (κ k).val) (y := (∑ k, (a k i : ZMod (l ^ n)) * κ k).val)
        (by simp)
      simpa using this
  · obtain ⟨s, hs, hsz⟩ := ex_conj hfr hm (hζ m).1.pow_eq_one b
    have hzA : ζ m ∈ A := root_mem A (pow_pos (Fact.out : l.Prime).pos m) (hζ m).1.pow_eq_one
    have hz : ζ m ^ (b : ZMod (l ^ m)).val ∈ A := A.toSubring.pow_mem hzA _
    have hev : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) = s ((P k).eval (ζ m)) := fun k => by
      rw [← hsz, ← hQ, pv_conj _ _ hs]
    have hne : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) ≠ 0 := fun k => by
      rw [hev]; exact (map_ne_zero s).2 (hu k).2.1
    unfold htv
    simp only [hmap, logd _ P _ _ hne, map_sum, map_mul j, map_natCast]
    refine cg_swap β.val o _ a ha fun k => hj _ ?_
    rw [div_eq_mul_inv]
    refine A.mul_mem _ _ (A.mul_mem _ _ hz ?_) ?_
    · rw [← hQ, Polynomial.derivative_map]; exact pv_mem _ hz
    · rw [hev, ← map_inv₀, apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs)]; exact (hu k).2.2
