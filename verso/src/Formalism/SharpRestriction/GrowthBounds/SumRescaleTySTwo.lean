import Formalism.SharpRestriction.GrowthBounds.CoeffOneAlongCvLg

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

/- English proof (translation)
Establish `hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l)` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])`. Rewrite using `[PowerSeries.subst_comp_subst_apply hS hS]`. Use `congr 1`. Rewrite using `[← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]`.
-/
theorem subst_X_pow_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) f := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  rw [PowerSeries.subst_comp_subst_apply hS hS]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]

/- English proof (translation)
Establish `e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2)`. Use function extensionality and compare the values at `s`. Consider the cases of `s with`. Consider the case `zero => simp [ha]`. Consider the case `succ s => simp`.

Rewrite using `[← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]`. Use `congr 1`. Rewrite using `[← tyS_Vpow hl, e]`.
-/
theorem sum_rescale_tyS_two {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) (ha : a 1 = 0) :
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (tyS l fun s => (l : C) * a (s + 2)) := by
  have e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2) := by
    funext s
    cases s with
    | zero => simp [ha]
    | succ s => simp
  rw [← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]
  congr 1
  rw [← tyS_Vpow hl, e]

/- English proof (translation)
Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1`. Introduce `k`. Rewrite using `[← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]`. Simplify using `[h1]`.
-/
theorem sum_root_pow {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range l, (ζ ^ k) ^ (l ^ j) = (l : C) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  simp [h1]

/- English proof (translation)
Rewrite using `[map_sum]`. Simplify using `only [PowerSeries.coeff_rescale]`. Rewrite using `[← Finset.sum_mul, sum_root_pow hζ j hj]`.
-/
theorem coeff_sum_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) (f : PowerSeries C) :
    PowerSeries.coeff (l ^ j) (∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) f) =
      (l : C) * PowerSeries.coeff (l ^ j) f := by
  rw [map_sum]
  simp only [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_root_pow hζ j hj]

section MM

variable {V : VF C}

/- English proof (translation)
Unfold `VF.MM at *`. Conclude with `lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)`.
-/
theorem mmA_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

/- English proof (translation)
Unfold `VF.MM`. Simplify using the standard rewrite rules.
-/
theorem mmA_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

/- English proof (translation)
The claim follows from `Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h`.
-/
theorem mmA_sum {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `MaximalIdealCongruence.mm_mul_ge' hb ha`.
-/
theorem mmA_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' hb ha

end MM

end SelfConjCharts

open SelfConjCharts in
/- English proof (translation)
Introduce `C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2`. Establish `hl2` using `V.l_prime.two_le`. Establish `hl0 : 0 < V.l` using `by omega`. Establish `hxT : x ∈ X.TySet V g` using `hG.1.1`. Establish `hx1 : ∀ c, x 1 (Sum.inl c) = 0` using `hG.2`.

Establish `hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g`. Establish `hF` using `(H g).Fm x hxT`. Establish `h3` using `(H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)`. Establish `hsub` using `(H g).add _ _ hF ((H g).neg _ h3)`. Use `hsub using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i n`. Consider the cases of `i with`. Consider the case `zero`. Consider the cases of `n with`. Consider the case `inl c => simp [Vpow, Fs, const0, hx1 c]`.

Consider the case `inr q => simp [Vpow, Fs, const0, Cart.c0']`. Consider the case `succ i => simp [Vpow, Fs, const0]`. Establish `hyT'` using `X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT`. Take `⟨γ, lam, hγ, hlam, hγ1, hγ2⟩` from `id hxT`. Take `⟨δ, -, hδ, -, hδ1, -⟩` from `hyT'`.

Use `⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]`. Simplify using `only [rescale_sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]`. Introduce `i`. Rewrite using `[coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]`. Conclude with `mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)`.

Introduce `q`. Establish `hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) = PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) + ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum …`. Introduce `n`. Establish `e` using `congrArg (PowerSeries.coeff n) (hγ2 q)`. Simplify using `only [map_add, map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero, smul_eq_mul] at e`.

Take the linear combination `e`. Establish `hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1` using `fun b => by`. Simplify using `using coeff_tyS_pow hl2 b 1`. Establish `hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2` using `fun b => coeff_tyS_pow hl2 b 2`. Establish `hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) = (V.l : C) * PowerSeries.coeff V.l f` using `fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f`.

Establish `hN2 : ∀ f : PowerSeries C, PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) = (V.l : C) * PowerSeries.coeff (V.l ^ 2) f` using `fun f => coeff_sum_rescale hζ 2 (by norm_num) f`. Establish `hl2pos : 0 < V.l ^ 2` using `by positivity`. Establish `hS1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0` using `fun f => coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by`. Use `Nat.le_of_dvd hl0 h` as an intermediate fact. Use the proof step `nlinarith)`.

Establish `hS2 : ∀ f : PowerSeries C, PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = PowerSeries.coeff 1 f` using `fun f => by simpa using coeff_subst_X_pow hl2pos f 1`. Use `⟨hG.c0'_int q, ?_, ?_⟩` and prove the remaining obligations. Establish `e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q = -((V.l : C) * PowerSeries.coeff V.l (lam q))`. Unfold `phi`. Rewrite using `[map_sub, hS1, hN1, hA]`.

Simplify using `only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))`. Establish `hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) = ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)`.

Rewrite using `[coeff_alongCv_low le_rfl (fun j m hm => by`. Take `rfl : m = 0` from `by omega`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]`. Simplify using `only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1, RawChart.sg1, Finset.mul_sum, zero_add]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) - (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) = ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else ((V.l : C) * x 2 (Sum.in …`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> ring`. Establish `e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) = (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) + -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q))`. Unfold `phi`. Rewrite using `[map_sub, hS2, hN2, hA, hB1]`. Simplify using `only [hT2]`.

Take the linear combination `key`. Rewrite using `[e]`. Use `mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))` and prove the remaining obligations. Use `split_ifs with hm`. Conclude with `mmA_zero`.

Conclude with `mmA_mul_int (hV2 c) (hB.hmis g c q hm)`.
-/
theorem good_curve_closed : GoodCurveClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hxT : x ∈ X.TySet V g := hG.1.1
  have hx1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2

  have hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g := by
    have hF := (H g).Fm x hxT
    have h3 := (H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)
    have hsub := (H g).add _ _ hF ((H g).neg _ h3)
    convert hsub using 1
    funext i n
    cases i with
    | zero =>
      cases n with
      | inl c => simp [Vpow, Fs, const0, hx1 c]
      | inr q => simp [Vpow, Fs, const0, Cart.c0']
    | succ i => simp [Vpow, Fs, const0]
  have hyT' := X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT
  obtain ⟨γ, lam, hγ, hlam, hγ1, hγ2⟩ := id hxT
  obtain ⟨δ, -, hδ, -, hδ1, -⟩ := hyT'
  refine ⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]
  · intro i
    rw [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]
    exact mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)
  · intro q
    have hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) =
        PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) +
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inl c)) else 0) := by
      intro n
      have e := congrArg (PowerSeries.coeff n) (hγ2 q)
      simp only [map_add, map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero,
        smul_eq_mul] at e
      linear_combination e
    have hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1 := fun b => by
      simpa using coeff_tyS_pow hl2 b 1
    have hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2 := fun b => coeff_tyS_pow hl2 b 2
    have hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
        (V.l : C) * PowerSeries.coeff V.l f := fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f
    have hN2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
          (V.l : C) * PowerSeries.coeff (V.l ^ 2) f := fun f => coeff_sum_rescale hζ 2 (by norm_num) f
    have hl2pos : 0 < V.l ^ 2 := by positivity
    have hS1 : ∀ f : PowerSeries C,
        PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0 := fun f =>
      coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by
        have := Nat.le_of_dvd hl0 h
        nlinarith)
    have hS2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) =
          PowerSeries.coeff 1 f := fun f => by simpa using coeff_subst_X_pow hl2pos f 1
    refine ⟨hG.c0'_int q, ?_, ?_⟩
    · have e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q =
          -((V.l : C) * PowerSeries.coeff V.l (lam q)) := by
        unfold phi
        rw [map_sub, hS1, hN1, hA]
        simp only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']
        ring
      rw [e]
      exact MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))
    · have hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) =
          ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q) := by
        rw [coeff_alongCv_low le_rfl (fun j m hm => by
            obtain rfl : m = 0 := by omega
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]
        simp only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1,
          RawChart.sg1, Finset.mul_sum, zero_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) -
          (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) =
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> ring
      have e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) =
          (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) +
            -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q)) := by
        unfold phi
        rw [map_sub, hS2, hN2, hA, hB1]
        simp only [hT2]
        linear_combination key
      rw [e]
      refine mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))
      split_ifs with hm
      · exact mmA_zero
      · exact mmA_mul_int (hV2 c) (hB.hmis g c q hm)

end Formalism.L2.FormalSeriesBounds
