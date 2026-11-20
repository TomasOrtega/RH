import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

noncomputable section

namespace GlobalTheory

open MvPowerSeries

section Eval

variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]

/- English proof (translation)
Establish `h : (MvPolynomial.idealOfVars σ A).map (MvPolynomial.aeval x : _ →ₐ[A] S) ≤ J`. Rewrite using `[MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Simplify using `using hx i`. Use `Ideal.mem_map_of_mem (MvPolynomial.aeval x : _ →ₐ[A] S) hp` as an intermediate fact.

Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h n this`.
-/
theorem aeval_mem_pow_of_mem_idealOfVars {J : Ideal S} {x : σ → S} (hx : ∀ i, x i ∈ J) {n : ℕ}
    {p : MvPolynomial σ A} (hp : p ∈ MvPolynomial.idealOfVars σ A ^ n) :
    MvPolynomial.aeval x p ∈ J ^ n := by
  have h : (MvPolynomial.idealOfVars σ A).map (MvPolynomial.aeval x : _ →ₐ[A] S) ≤ J := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa using hx i
  have := Ideal.mem_map_of_mem (MvPolynomial.aeval x : _ →ₐ[A] S) hp
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := J) _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero]`. Simplify using `using h n`.
-/
theorem eq_of_forall_sub_mem_ideal_pow (J : Ideal S) [IsHausdorff J S] {x y : S}
    (h : ∀ n, x - y ∈ J ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  simpa using h n

variable [Finite σ]

def mvEvalMod (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) : MvPowerSeries σ A →ₐ[A] S ⧸ J ^ n :=
  (Ideal.Quotient.liftₐ (MvPolynomial.idealOfVars σ A ^ n)
    ((Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval x)) fun _ hp =>
      Ideal.Quotient.eq_zero_iff_mem.2 (aeval_mem_pow_of_mem_idealOfVars hx hp)).comp
    ((truncTotalAlgHom σ A n).restrictScalars A)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mvEvalMod_apply (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) (n : ℕ)
    (f : MvPowerSeries σ A) :
    mvEvalMod A J x hx n f = Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) := rfl

/- English proof (translation)
Use `AlgHom.ext fun f => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) = Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal m f))`. Rewrite using `[Ideal.Quotient.eq, ← map_sub]`. Conclude with `aeval_mem_pow_of_mem_idealOfVars hx (truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl f)`.
-/
theorem factor_comp_mvEvalMod (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (mvEvalMod A J x hx n) =
      mvEvalMod A J x hx m := by
  refine AlgHom.ext fun f => ?_
  change Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) =
    Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal m f))
  rw [Ideal.Quotient.eq, ← map_sub]
  exact aeval_mem_pow_of_mem_idealOfVars hx
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl f)

def mvEvalAdic (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) [IsAdicComplete J S]
    (x : σ → S) (hx : ∀ i, x i ∈ J) : MvPowerSeries σ A →ₐ[A] S :=
  IsAdicComplete.liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx)

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `IsAdicComplete.mk_liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx) n f`.
-/
theorem mvEvalAdic_sub_aeval_truncTotal_mem (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) (f : MvPowerSeries σ A) :
    mvEvalAdic A J x hx f - MvPolynomial.aeval x (truncTotal n f) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq]
  exact IsAdicComplete.mk_liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx) n f

/- English proof (translation)
Use `eq_of_forall_sub_mem_ideal_pow J fun n => ?_` and prove the remaining obligations. Establish `h1` using `mvEvalAdic_sub_aeval_truncTotal_mem J x hx n (p : MvPowerSeries σ A)`. Establish `h2 : MvPolynomial.aeval x (truncTotal n (p : MvPowerSeries σ A) - p) ∈ J ^ n`. Use `aeval_mem_pow_of_mem_idealOfVars hx ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_pow_idealOfVars_iff']`.

Introduce `d hd`. Rewrite using `[MvPolynomial.coeff_sub, coeff_truncTotal _ hd, MvPolynomial.coeff_coe, sub_self]`. Simplify using `using add_mem h1 h2`.
-/
@[simp] theorem mvEvalAdic_coe (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (p : MvPolynomial σ A) :
    mvEvalAdic A J x hx p = MvPolynomial.aeval x p := by
  refine eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  have h1 := mvEvalAdic_sub_aeval_truncTotal_mem J x hx n (p : MvPowerSeries σ A)
  have h2 : MvPolynomial.aeval x (truncTotal n (p : MvPowerSeries σ A) - p) ∈ J ^ n := by
    refine aeval_mem_pow_of_mem_idealOfVars hx ?_
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hd, MvPolynomial.coeff_coe, sub_self]
  simpa using add_mem h1 h2

/- English proof (translation)
Simplify using `using mvEvalAdic_coe (A := A) J x hx (MvPolynomial.X i)`.
-/
@[simp] theorem mvEvalAdic_X (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (i : σ) : mvEvalAdic A J x hx (X i) = x i := by
  simpa using mvEvalAdic_coe (A := A) J x hx (MvPolynomial.X i)

/- English proof (translation)
The claim follows from `(mvEvalAdic A J x hx).commutes a`.
-/
@[simp] theorem mvEvalAdic_C (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (a : A) : mvEvalAdic A J x hx (C a) = algebraMap A S a :=
  (mvEvalAdic A J x hx).commutes a

/- English proof (translation)
Establish `h : (germIdeal σ A).map φ ≤ K`. Rewrite using `[germIdeal_eq_span, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `hφ i`. Use `Ideal.mem_map_of_mem φ (mem_germIdeal_pow_iff_le_order.2 hg)` as an intermediate fact.

Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h n this`.
-/
theorem algHom_mem_pow_of_le_order (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) {n : ℕ} {g : MvPowerSeries σ A} (hg : (n : ℕ∞) ≤ g.order) :
    φ g ∈ K ^ n := by
  have h : (germIdeal σ A).map φ ≤ K := by
    rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hφ i
  have := Ideal.mem_map_of_mem φ (mem_germIdeal_pow_iff_le_order.2 hg)
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this

/- English proof (translation)
Establish `h : φ (g - C (constantCoeff g)) ∈ K ^ 1` using `algHom_mem_pow_of_le_order φ hφ (mem_germIdeal_pow_iff_le_order.1 (by simp [RingHom.mem_ker]))`. Rewrite `h` using `[pow_one, map_sub]`. Rewrite using `[← φ.commutes]` and apply the resulting hypothesis.
-/
theorem algHom_sub_constantCoeff_mem (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) (g : MvPowerSeries σ A) :
    φ g - algebraMap A S (constantCoeff g) ∈ K := by
  have h : φ (g - C (constantCoeff g)) ∈ K ^ 1 :=
    algHom_mem_pow_of_le_order φ hφ (mem_germIdeal_pow_iff_le_order.1 (by simp [RingHom.mem_ker]))
  rw [pow_one, map_sub] at h
  rwa [← φ.commutes]

omit [Finite σ] in
/- English proof (translation)
Establish `: φ.comp (MvPolynomial.coeToMvPowerSeries.algHom A) = MvPolynomial.aeval (fun i => φ (X i))` using `by ext; simp`. Simplify using `using DFunLike.congr_fun this p`.
-/
theorem algHom_coe_mvPolynomial (φ : MvPowerSeries σ A →ₐ[A] S) (p : MvPolynomial σ A) :
    φ p = MvPolynomial.aeval (fun i => φ (X i)) p := by
  have : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom A) =
      MvPolynomial.aeval (fun i => φ (X i)) := by
    ext; simp
  simpa using DFunLike.congr_fun this p

/- English proof (translation)
Rewrite using `[← algHom_coe_mvPolynomial, ← map_sub]`. Use `algHom_mem_pow_of_le_order φ hφ (nat_le_order fun d hd => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]`.
-/
theorem algHom_sub_aeval_truncTotal_mem (φ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (n : ℕ) (g : MvPowerSeries σ A) :
    φ g - MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) ∈ J ^ n := by
  rw [← algHom_coe_mvPolynomial, ← map_sub]
  refine algHom_mem_pow_of_le_order φ hφ (nat_le_order fun d hd => ?_)
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]

/- English proof (translation)
Establish `h1` using `algHom_sub_aeval_truncTotal_mem φ hφ n g`. Establish `h2` using `algHom_sub_aeval_truncTotal_mem ψ hψ n g`. Establish `h3 : MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) - MvPolynomial.aeval (fun i => ψ (X i)) (truncTotal n g) ∈ J ^ n`. Establish `: (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => φ (X i))) = (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => ψ (X i)))`. Use extensionality with `i`.

Simplify `h i` using `[Ideal.Quotient.eq]`. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `DFunLike.congr_fun this _`. Use `sub_mem (add_mem h1 h3) h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem algHom_sub_mem_pow (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (hψ : ∀ i, ψ (X i) ∈ J) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ J ^ n) (g : MvPowerSeries σ A) : φ g - ψ g ∈ J ^ n := by
  have h1 := algHom_sub_aeval_truncTotal_mem φ hφ n g
  have h2 := algHom_sub_aeval_truncTotal_mem ψ hψ n g
  have h3 : MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) -
      MvPolynomial.aeval (fun i => ψ (X i)) (truncTotal n g) ∈ J ^ n := by
    have : (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => φ (X i))) =
        (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => ψ (X i))) := by
      ext i
      simpa [Ideal.Quotient.eq] using h i
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun this _
  have := sub_mem (add_mem h1 h3) h2
  convert this using 1
  ring

/- English proof (translation)
The claim follows from `AlgHom.ext fun g => eq_of_forall_sub_mem_ideal_pow J fun n => algHom_sub_mem_pow φ ψ hφ (fun i => h i ▸ hφ i) (fun i => by simp [h i]) g`.
-/
theorem mvPowerSeries_algHom_ext_of_isHausdorff (J : Ideal S) [IsHausdorff J S]
    {φ ψ : MvPowerSeries σ A →ₐ[A] S} (hφ : ∀ i, φ (X i) ∈ J) (h : ∀ i, φ (X i) = ψ (X i)) :
    φ = ψ :=
  AlgHom.ext fun g => eq_of_forall_sub_mem_ideal_pow J fun n =>
    algHom_sub_mem_pow φ ψ hφ (fun i => h i ▸ hφ i) (fun i => by simp [h i]) g

/- English proof (translation)
The claim follows from `mvPowerSeries_algHom_ext_of_isHausdorff J (fun i => h i ▸ hx i) (by simp [h])`.
-/
theorem eq_mvEvalAdic (J : Ideal S) [IsAdicComplete J S] (x : σ → S) (hx : ∀ i, x i ∈ J)
    (φ : MvPowerSeries σ A →ₐ[A] S) (h : ∀ i, φ (X i) = x i) : φ = mvEvalAdic A J x hx :=
  mvPowerSeries_algHom_ext_of_isHausdorff J (fun i => h i ▸ hx i) (by simp [h])

/- English proof (translation)
Consider the cases of `nonempty_fintype σ`. Establish `key : ∀ g : MvPowerSeries σ A, 1 ≤ g.order → φ g - ψ g ∈ B * J ^ n`. Introduce `g hg`. Take `⟨k, -, rfl⟩` from `exists_eq_sum_X_mul (n := 0) (g := g) fun d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)`. Rewrite using `[map_sum, map_sum, ← Finset.sum_sub_distrib]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `e : φ (X i * k i) - ψ (X i * k i) = φ (X i) * (φ (k i) - ψ (k i)) + (φ (X i) - ψ (X i)) * ψ (k i)`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `add_mem (Ideal.mul_mem_mul (hφ i) ?_) (Ideal.mul_mem_right _ _ (h i))` and prove the remaining obligations. Conclude with `algHom_sub_mem_pow φ ψ (fun i => hB (hφ i)) (fun i => hB (hψ i)) (fun i => (Ideal.mul_le_inf (I := B) (J := J ^ n) (h i)).2) _`. Take `⟨k, hk, rfl⟩` from `exists_eq_sum_X_mul (n := 1) (g := g) fun d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)`. Establish `hk' : ∀ i, ((1 : ℕ) : ℕ∞) ≤ (k i).order` using `fun i => nat_le_order (hk i)`. Rewrite using `[map_sum, map_sum, ← Finset.sum_sub_distrib]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `e : φ (X i * k i) - ψ (X i * k i) = φ (X i) * (φ (k i) - ψ (k i)) + ψ (k i) * (φ (X i) - ψ (X i))`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, sq, mul_assoc]`.

Use `add_mem (Ideal.mul_mem_mul (hφ i) (key _ (by exact_mod_cast hk' i))) (Ideal.mul_mem_mul ?_ (h i))` and prove the remaining obligations. Simplify using `using algHom_mem_pow_of_le_order ψ hψ (hk' i)`.
-/
theorem algHom_sub_mem_of_two_le_order (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J B : Ideal S}
    (hB : B ≤ J) (hφ : ∀ i, φ (X i) ∈ B) (hψ : ∀ i, ψ (X i) ∈ B) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ B * J ^ n) {g : MvPowerSeries σ A} (hg : 2 ≤ g.order) :
    φ g - ψ g ∈ B ^ 2 * J ^ n := by
  cases nonempty_fintype σ
  have key : ∀ g : MvPowerSeries σ A, 1 ≤ g.order → φ g - ψ g ∈ B * J ^ n := by
    intro g hg
    obtain ⟨k, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    have e : φ (X i * k i) - ψ (X i * k i) =
        φ (X i) * (φ (k i) - ψ (k i)) + (φ (X i) - ψ (X i)) * ψ (k i) := by
      simp only [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_mul (hφ i) ?_) (Ideal.mul_mem_right _ _ (h i))
    exact algHom_sub_mem_pow φ ψ (fun i => hB (hφ i)) (fun i => hB (hψ i))
      (fun i => (Ideal.mul_le_inf (I := B) (J := J ^ n) (h i)).2) _
  obtain ⟨k, hk, rfl⟩ := exists_eq_sum_X_mul (n := 1) (g := g) fun d hd =>
    coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hg)
  have hk' : ∀ i, ((1 : ℕ) : ℕ∞) ≤ (k i).order := fun i => nat_le_order (hk i)
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  have e : φ (X i * k i) - ψ (X i * k i) =
      φ (X i) * (φ (k i) - ψ (k i)) + ψ (k i) * (φ (X i) - ψ (X i)) := by
    simp only [map_mul]; ring
  rw [e, sq, mul_assoc]
  refine add_mem (Ideal.mul_mem_mul (hφ i) (key _ (by exact_mod_cast hk' i)))
    (Ideal.mul_mem_mul ?_ (h i))
  simpa using algHom_mem_pow_of_le_order ψ hψ (hk' i)

end Eval

section Contraction

variable {A S τ ι : Type*} [CommRing A] [CommRing S] [Algebra A S]

/- English proof (translation)
Establish `hit : ∀ n x y i, T^[n] x i - T^[n] y i ∈ J ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Introduce `x y i`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Conclude with `hT n _ _ (ih x y) i`. Establish `hc : ∀ i, ∃ L : S, ∀ n, T^[n] 0 i - L ∈ J ^ n`. Introduce `i`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := J) (fun n => T^[n] 0 i) fun {m n} hmn => by`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Rewrite using `[SModEq.sub_mem, Function.iterate_add_apply]`. Simplify using `using hit m 0 _ i`. Conclude with `⟨L, fun n => by simpa [SModEq.sub_mem] using hL n⟩`.

Use `choose L hL using hc`. Use `⟨L, funext fun i => eq_of_forall_sub_mem_ideal_pow J fun n => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hT n _ _ (fun i => hL i n) i`. Establish `h2` using `hL i (n + 1)`. Rewrite `h2` using `[Function.iterate_succ_apply']`.

Use `sub_mem h2 h1` as an intermediate fact. Use `Ideal.pow_le_pow_right n.le_succ ?_` and prove the remaining obligations. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `funext fun i => eq_of_forall_sub_mem_ideal_pow J fun n => ?_` and prove the remaining obligations.

Establish `h1` using `hit n y 0 i`. Rewrite `h1` using `[Function.iterate_fixed hy]`. Simplify using `using add_mem h1 (hL i n)`.
-/
theorem existsUnique_fixedPoint_of_adic_contraction (J : Ideal S) [IsAdicComplete J S]
    (T : (ι → S) → ι → S)
    (hT : ∀ n x y, (∀ i, x i - y i ∈ J ^ n) → ∀ i, T x i - T y i ∈ J ^ (n + 1)) :
    ∃! x, T x = x := by
  have hit : ∀ n x y i, T^[n] x i - T^[n] y i ∈ J ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y) i
  have hc : ∀ i, ∃ L : S, ∀ n, T^[n] 0 i - L ∈ J ^ n := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => T^[n] 0 i) fun {m n} hmn => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [SModEq.sub_mem, Function.iterate_add_apply]
      simpa using hit m 0 _ i
    exact ⟨L, fun n => by simpa [SModEq.sub_mem] using hL n⟩
  choose L hL using hc
  refine ⟨L, funext fun i => eq_of_forall_sub_mem_ideal_pow J fun n => ?_, fun y hy => ?_⟩
  · have h1 := hT n _ _ (fun i => hL i n) i
    have h2 := hL i (n + 1)
    rw [Function.iterate_succ_apply'] at h2
    have := sub_mem h2 h1
    refine Ideal.pow_le_pow_right n.le_succ ?_
    convert this using 1
    ring
  · refine funext fun i => eq_of_forall_sub_mem_ideal_pow J fun n => ?_
    have h1 := hit n y 0 i
    rw [Function.iterate_fixed hy] at h1
    simpa using add_mem h1 (hL i n)

/- English proof (translation)
Introduce and unpack `(k | i)`. Use `exacts [hu k, hs i]`.
-/
theorem sumElim_mem {K : Ideal S} {u : τ → S} {s : ι → S} (hu : ∀ k, u k ∈ K)
    (hs : ∀ i, s i ∈ K) : ∀ v, Sum.elim u s v ∈ K := by
  rintro (k | i)
  exacts [hu k, hs i]

/- English proof (translation)
Use `choose e he hbe using hc`. Establish `hB : Ideal.span {b} ≤ J` using `(Ideal.span_singleton_le_iff_mem _).2 hbJ`. Establish `hpt : ∀ t : ι → S, ∀ v, Sum.elim u (fun i => b * t i) v ∈ Ideal.span {b}` using `fun t => sumElim_mem hu fun i => Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)`. Set `ev : (ι → S) → (MvPowerSeries (τ ⊕ ι) A →ₐ[A] S)` to `fun t => mvEvalAdic A J (Sum.elim u fun i => b * t i) fun v => hB (hpt t v)`. Establish `hev : ∀ t v, ev t (X v) = Sum.elim u (fun i => b * t i) v` using `fun t v => by simp [ev]`.

Establish `hr : ∀ t i, ∃ r, ev t (Q i) = b ^ 2 * r` using `fun t i => by`. Use `algHom_mem_pow_of_le_order (ev t) (fun v => hev t v ▸ hpt t v) (n := 2) (by exact_mod_cast hQ i)` as an intermediate fact. Rewrite `this` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Use `choose r hr using hr`. Establish `hcb : ∀ i, algebraMap A S (c i) * b ∈ nonZeroDivisors S` using `fun i => mul_mem (mul_mem_nonZeroDivisors.1 (hbe i ▸ hb)).1 hb`.

Establish `hiff : ∀ t, (fun i => -(e i * r t i)) = t ↔ ∀ i, ev t (c i • X (Sum.inr i) + Q i) = 0`. Introduce `t`. Rewrite using `[funext_iff]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `: ev t (c i • X (Sum.inr i) + Q i) = algebraMap A S (c i) * b * (t i + e i * r t i)`.

Rewrite using `[map_add, map_smul, hev, hr, Algebra.smul_def, Sum.elim_inr]`. Take the linear combination `(b * r t i) * hbe i`. Rewrite using `[this, mul_left_mem_nonZeroDivisors_eq_zero_iff (hcb i), neg_eq_iff_add_eq_zero, add_comm]`. Take `⟨t, ht, huniq⟩` from `existsUnique_fixedPoint_of_adic_contraction J (fun t i => -(e i * r t i)) fun n x y hxy i => by`. Establish `h1` using `algHom_sub_mem_of_two_le_order (ev x) (ev y) hB (fun v => hev x v ▸ hpt x v) (fun v => hev y v ▸ hpt y v) (n := n) (fun v => by`.

Rewrite using `[hev, hev]`. Break down `v with k | i` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Sum.elim_inr, ← mul_sub]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) (hxy i)) (hQ i)`.

Rewrite `h1` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul]`. Take `⟨w, hw, hw'⟩` from `h1`. Rewrite `hw'` using `[hr, hr, ← mul_sub]`. Establish `h2 : w = r x i - r y i` using `(mul_cancel_left_mem_nonZeroDivisors (pow_mem hb 2)).1 hw'`. Establish `h3 : -(e i * r x i) - -(e i * r y i) = e i * -w` using `by rw [h2]; ring`.

Rewrite using `[h3, pow_succ']`. Conclude with `Ideal.mul_mem_mul (he i) (neg_mem hw)`. Use `⟨ev t, ⟨fun k => hev t _, fun i => hev t _ ▸ hpt t _, (hiff t).1 ht⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `φ ⟨h1, h2, h3⟩`. Use `choose t' ht' using fun i => Ideal.mem_span_singleton.1 (h2 i)`.

Establish `hφ : φ = ev t'` using `eq_mvEvalAdic J _ _ φ (by`. Introduce and unpack `(k | i)`. Use `exacts [h1 k, ht' i])`. Rewrite `h3`, the goal using `[hφ]`. Rewrite using `[huniq t' ((hiff t').2 h3)]`.
-/
theorem existsUnique_algHom_implicit [Finite τ] [Finite ι] (J : Ideal S) [IsAdicComplete J S]
    {b : S} (hb : b ∈ nonZeroDivisors S) (hbJ : b ∈ J) (c : ι → A)
    (hc : ∀ i, ∃ e ∈ J, b = algebraMap A S (c i) * e)
    (Q : ι → MvPowerSeries (τ ⊕ ι) A) (hQ : ∀ i, 2 ≤ (Q i).order)
    (u : τ → S) (hu : ∀ k, u k ∈ Ideal.span {b}) :
    ∃! φ : MvPowerSeries (τ ⊕ ι) A →ₐ[A] S, (∀ k, φ (X (Sum.inl k)) = u k) ∧
      (∀ i, φ (X (Sum.inr i)) ∈ Ideal.span {b}) ∧ ∀ i, φ (c i • X (Sum.inr i) + Q i) = 0 := by
  choose e he hbe using hc
  have hB : Ideal.span {b} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hbJ
  have hpt : ∀ t : ι → S, ∀ v, Sum.elim u (fun i => b * t i) v ∈ Ideal.span {b} := fun t =>
    sumElim_mem hu fun i => Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)
  let ev : (ι → S) → (MvPowerSeries (τ ⊕ ι) A →ₐ[A] S) := fun t =>
    mvEvalAdic A J (Sum.elim u fun i => b * t i) fun v => hB (hpt t v)
  have hev : ∀ t v, ev t (X v) = Sum.elim u (fun i => b * t i) v := fun t v => by simp [ev]
  have hr : ∀ t i, ∃ r, ev t (Q i) = b ^ 2 * r := fun t i => by
    have := algHom_mem_pow_of_le_order (ev t) (fun v => hev t v ▸ hpt t v) (n := 2)
      (by exact_mod_cast hQ i)
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  choose r hr using hr
  have hcb : ∀ i, algebraMap A S (c i) * b ∈ nonZeroDivisors S := fun i =>
    mul_mem (mul_mem_nonZeroDivisors.1 (hbe i ▸ hb)).1 hb
  have hiff : ∀ t, (fun i => -(e i * r t i)) = t ↔ ∀ i, ev t (c i • X (Sum.inr i) + Q i) = 0 := by
    intro t
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have : ev t (c i • X (Sum.inr i) + Q i) = algebraMap A S (c i) * b * (t i + e i * r t i) := by
      rw [map_add, map_smul, hev, hr, Algebra.smul_def, Sum.elim_inr]
      linear_combination (b * r t i) * hbe i
    rw [this, mul_left_mem_nonZeroDivisors_eq_zero_iff (hcb i), neg_eq_iff_add_eq_zero, add_comm]
  obtain ⟨t, ht, huniq⟩ := existsUnique_fixedPoint_of_adic_contraction J
    (fun t i => -(e i * r t i)) fun n x y hxy i => by
      have h1 := algHom_sub_mem_of_two_le_order (ev x) (ev y) hB (fun v => hev x v ▸ hpt x v)
        (fun v => hev y v ▸ hpt y v) (n := n) (fun v => by
          rw [hev, hev]
          rcases v with k | i
          · simp
          · simp only [Sum.elim_inr, ← mul_sub]
            exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) (hxy i)) (hQ i)
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul] at h1
      obtain ⟨w, hw, hw'⟩ := h1
      rw [hr, hr, ← mul_sub] at hw'
      have h2 : w = r x i - r y i :=
        (mul_cancel_left_mem_nonZeroDivisors (pow_mem hb 2)).1 hw'
      have h3 : -(e i * r x i) - -(e i * r y i) = e i * -w := by rw [h2]; ring
      rw [h3, pow_succ']
      exact Ideal.mul_mem_mul (he i) (neg_mem hw)
  refine ⟨ev t, ⟨fun k => hev t _, fun i => hev t _ ▸ hpt t _, (hiff t).1 ht⟩, ?_⟩
  rintro φ ⟨h1, h2, h3⟩
  choose t' ht' using fun i => Ideal.mem_span_singleton.1 (h2 i)
  have hφ : φ = ev t' := eq_mvEvalAdic J _ _ φ (by
    rintro (k | i)
    exacts [h1 k, ht' i])
  rw [hφ] at h3 ⊢
  rw [huniq t' ((hiff t').2 h3)]

end Contraction

end GlobalTheory
