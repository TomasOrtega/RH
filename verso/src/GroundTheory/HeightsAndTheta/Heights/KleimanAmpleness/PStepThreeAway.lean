import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThree.Away

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]`. Rewrite using `[map_sum]`. Establish `hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) = if d = l + i then P * homogeneousComponent i G else 0` using `fun i => homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))`. Repeatedly rewrite using `[hterm]`. Distinguish the cases in `h : l ≤ d`.

Rewrite using `[if_pos h]`. Apply the tactic sequence `have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) = if d - l = i then P * homogeneousComponent i G else 0 := fun i => by split_ifs <;> first | rfl | (exfalso; omega)`. Repeatedly rewrite using `[h2]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hm`.

Both sides reduce to the same expression. Rewrite using `[homogeneousComponent_eq_zero, mul_zero]`. Simplify using `only [Finset.mem_range] at hm`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h]`.

Conclude with `Finset.sum_eq_zero fun i _ => if_neg (by omega)`.
-/
theorem homogeneousComponent_homog_mul {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]`. Consider the case `succ n ih => rw [pow_succ, ih, Submodule.span_mul_span, Set.singleton_mul_singleton, pow_succ]`.
-/
theorem span_singleton_pow_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (a : A)
    (n : ℕ) : Submodule.span R {a} ^ n = Submodule.span R {a ^ n} := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih => rw [pow_succ, ih, Submodule.span_mul_span, Set.singleton_mul_singleton, pow_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twistSys_sub (c : ℤ) (I : Chart x) : (twistSys S x c).sub I = twistMod S x c I := rfl

/- English proof (translation)
Rewrite using `[Submodule.mul_eq_span_mul_set]`. Express the relevant statement in the definitionally equal form `Submodule.span _ {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _`. Use `congr 1`. Use extensionality with `z`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, y, hy, rfl⟩`. Conclude with `⟨q, hq, y, hy, rfl⟩`. Introduce and unpack `⟨q, hq, y, hy, rfl⟩`. Conclude with `⟨q, hq, y, hy, rfl⟩`.
-/
theorem twist_sub (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Rewrite using `[twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]`.
-/
theorem twistMod_zero (I : Chart x) : twistMod S x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Rewrite using `[twistMod_eq_span a I hi, twistMod_eq_span a' I hi, twistMod_eq_span (a + a') I hi, Submodule.span_mul_span, Set.singleton_mul_singleton, zpow_add₀ hxi]`.
-/
theorem twistMod_mul (a a' : ℤ) (I : Chart x) :
    twistMod S x a I * twistMod S x a' I = twistMod S x (a + a') I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twistMod_eq_span a I hi, twistMod_eq_span a' I hi, twistMod_eq_span (a + a') I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, zpow_add₀ hxi]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih, twistMod_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twistMod_pow (a : ℤ) (I : Chart x) (n : ℕ) :
    twistMod S x a I ^ n = twistMod S x (n * a) I := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero]
  | succ n ih =>
    rw [pow_succ, ih, twistMod_mul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact (twistMod_zero I).trans (pow_zero _).symm`. Consider the case `succ n ih`. Express the relevant statement in the definitionally equal form `((Q.pow n).twist Q).sub I = _`. Rewrite using `[twist_sub, ih, pow_succ']`.
-/
theorem pow_sub (Q : SubSystem S x Ω) (I : Chart x) (n : ℕ) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => exact (twistMod_zero I).trans (pow_zero _).symm
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub, ih, pow_succ']

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, X i ^ d, d, pow_mem (X_mem_monos hi) d, hh, isHomogeneous_X_pow i d, by rw [map_pow, aeval_X]⟩`.
-/
theorem div_pow_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) {h : Poly S N} {d : ℕ}
    (hh : h.IsHomogeneous d) : aeval x h / x i ^ d ∈ chartRing S x I :=
  ⟨h, X i ^ d, d, pow_mem (X_mem_monos hi) d, hh, isHomogeneous_X_pow i d, by rw [map_pow, aeval_X]⟩

/- English proof (translation)
Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Rewrite `hf` using `[zeroIdeal, Ideal.span]`. Proceed by induction on `hf using Submodule.span_induction generalizing e with`. Consider the case `mem g hg`. Take `⟨c, hgc, hg⟩` from `hg`.

Introduce `δ hδ`. Rewrite using `[homogeneousComponent_of_mem hgc]`. Use `split_ifs with hce`. Substitute `hce` using the available equality. Take `⟨o, ho, heq⟩` from `hg I δ hδ`.

Rewrite `ho` using `[twistMod_eq_span _ I hi, Submodule.mem_span_singleton]`. Take `⟨t, rfl⟩` from `ho`. Rewrite using `[heq, Submodule.mem_span_singleton]`. Conclude with `⟨t, by rw [chartRing_smul_def, chartRing_smul_def, zpow_natCast]; ring⟩`. Rewrite using `[map_zero, zero_mul]`.

Conclude with `Submodule.zero_mem _`. Consider the case `zero => intro δ _`. Rewrite using `[map_zero, map_zero, zero_mul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add f g _ _ hf hg`.

Introduce `δ hδ`. Rewrite using `[map_add, map_add, add_mul]`. Conclude with `Submodule.add_mem _ (hf e δ hδ) (hg e δ hδ)`. Consider the case `smul r f _ hf`. Introduce `δ hδ`.

Establish `hsum : r * f = ∑ d ∈ Finset.range (r.totalDegree + 1), homogeneousComponent d r * f`. Rewrite using `[← Finset.sum_mul, sum_homogeneousComponent]`. Rewrite using `[smul_eq_mul, hsum, map_sum, map_sum, Finset.sum_mul]`. Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Rewrite using `[homogeneousComponent_homog_mul (homogeneousComponent_isHomogeneous d r) f e]`.

Use `split_ifs with hde`. Take `⟨t, ht⟩` from `Submodule.mem_span_singleton.mp (hf (e - d) δ hδ)`. Rewrite using `[map_mul, mul_assoc, ← ht, Submodule.mem_span_singleton]`. Use `⟨⟨_, div_pow_mem_chartRing I hi (homogeneousComponent_isHomogeneous d r)⟩ * t, ?_⟩` and prove the remaining obligations. Establish `hpow : x i ^ e = x i ^ d * x i ^ (e - d)` using `by rw [← pow_add, Nat.add_sub_cancel' hde]`.

Establish `hxd : x i ^ d ≠ 0` using `pow_ne_zero _ hxi`. Rewrite using `[chartRing_smul_def, chartRing_smul_def, Subalgebra.coe_mul, hpow]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[map_zero, zero_mul]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem homogeneousComponent_mul_mem (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) {f : Poly S N} (hf : f ∈ zeroIdeal D σ) (e : ℕ) :
    ∀ δ ∈ D.sub I, aeval x (homogeneousComponent e f) * δ ∈
      Submodule.span (chartRing S x I) {σ * x i ^ e} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [zeroIdeal, Ideal.span] at hf
  induction hf using Submodule.span_induction generalizing e with
  | mem g hg =>
    obtain ⟨c, hgc, hg⟩ := hg
    intro δ hδ
    rw [homogeneousComponent_of_mem hgc]
    split_ifs with hce
    · subst hce
      obtain ⟨o, ho, heq⟩ := hg I δ hδ
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
      obtain ⟨t, rfl⟩ := ho
      rw [heq, Submodule.mem_span_singleton]
      exact ⟨t, by rw [chartRing_smul_def, chartRing_smul_def, zpow_natCast]; ring⟩
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | zero => intro δ _; rw [map_zero, map_zero, zero_mul]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    intro δ hδ
    rw [map_add, map_add, add_mul]
    exact Submodule.add_mem _ (hf e δ hδ) (hg e δ hδ)
  | smul r f _ hf =>
    intro δ hδ
    have hsum : r * f = ∑ d ∈ Finset.range (r.totalDegree + 1), homogeneousComponent d r * f := by
      rw [← Finset.sum_mul, sum_homogeneousComponent]
    rw [smul_eq_mul, hsum, map_sum, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [homogeneousComponent_homog_mul (homogeneousComponent_isHomogeneous d r) f e]
    split_ifs with hde
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hf (e - d) δ hδ)
      rw [map_mul, mul_assoc, ← ht, Submodule.mem_span_singleton]
      refine ⟨⟨_, div_pow_mem_chartRing I hi (homogeneousComponent_isHomogeneous d r)⟩ * t, ?_⟩
      have hpow : x i ^ e = x i ^ d * x i ^ (e - d) := by rw [← pow_add, Nat.add_sub_cancel' hde]
      have hxd : x i ^ d ≠ 0 := pow_ne_zero _ hxi
      rw [chartRing_smul_def, chartRing_smul_def, Subalgebra.coe_mul, hpow]
      field_simp
      try ring
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Rewrite using `[Submodule.mul_le]`. Introduce `a ha δ hδ`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem a ha`. Take `⟨f, s, e, hf, hs, hfe, hse, rfl⟩` from `ha`. Establish `h` using `homogeneousComponent_mul_mem D σ I hi hf e δ hδ`. Rewrite `h` using `[homogeneousComponent_of_mem hfe, if_pos rfl]`. Take `⟨t, ht⟩` from `Submodule.mem_span_singleton.mp h`.

Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, by rw [map_pow, aeval_X]⟩ * t, ?_⟩` and prove the remaining obligations. Rewrite using `[chartRing_smul_def, Subalgebra.coe_mul, show aeval x f / aeval x s * δ = aeval x f * δ / aeval x s by ring, ← ht, chartRing_smul_def]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Consider the case `zero => rw [zero_mul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [add_mul]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul r a _ ha => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ r ha`.
-/
theorem idealMod_zeroIdeal_mul_le (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) :
    idealMod (x := x) (zeroIdeal D σ) I * D.sub I ≤ Submodule.span (chartRing S x I) {σ} := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [Submodule.mul_le]
  intro a ha δ hδ
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, s, e, hf, hs, hfe, hse, rfl⟩ := ha
    have h := homogeneousComponent_mul_mem D σ I hi hf e δ hδ
    rw [homogeneousComponent_of_mem hfe, if_pos rfl] at h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse,
      by rw [map_pow, aeval_X]⟩ * t, ?_⟩
    rw [chartRing_smul_def, Subalgebra.coe_mul,
      show aeval x f / aeval x s * δ = aeval x f * δ / aeval x s by ring, ← ht, chartRing_smul_def]
    field_simp
    try ring
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

end Lemmas

/- English proof (translation)
Introduce `k _ Ω _ _ N x T b c hc I`. Take `⟨i, hi⟩` from `I.2.1`. Establish `hL : ∀ I' : Chart x, T.L.sub I' = twistMod k x T.c₁ I' * T.D.sub I'`. Introduce `I'`. Express the relevant statement in the definitionally equal form `((T.M.toSubSystem.pow T.p).twist (twistSys k x T.m)).sub I' = _ * ((T.M.toSubSystem.pow T.p).twist (twistSys k x (T.m - T.c₁))).sub I'`.

Rewrite using `[twist_sub, twist_sub, twistSys_sub, twistSys_sub, ← mul_assoc, twistMod_mul, add_sub_cancel]`. Establish `hF : ∀ I' : Chart x, ((T.L.pow b).twist (twistSys k x c)).sub I' = twistMod k x (c + b * T.c₁) I' * T.D.sub I' ^ b`. Introduce `I'`. Rewrite using `[twist_sub, twistSys_sub, pow_sub, hL, mul_pow, twistMod_pow, ← mul_assoc, twistMod_mul]`. Establish `hn : 0 ≤ c + b * T.c₁` using `add_nonneg hc (mul_nonneg (Nat.cast_nonneg b) (by linarith [T.c₁_pos]))`.

Take `⟨n, hnn⟩` from `Int.eq_ofNat_of_zero_le hn`. Establish `hy : x i ^ n * T.si ^ b ∈ ((T.L.pow b).twist (twistSys k x c)).secs`. Use `(Submodule.mem_iInf _).mpr fun I' => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ ((T.L.pow b).twist (twistSys k x c)).sub I'`. Rewrite using `[hF I', hnn]`.

Use `Submodule.mul_mem_mul (Submodule.subset_span ⟨X i ^ n, 1, 0, n, one_mem _, isHomogeneous_X_pow i n, isHomogeneous_one _ _, by simp, by simp⟩) (Submodule.pow_mem_pow _ ?_ b)` and prove the remaining obligations. Conclude with `(Submodule.mem_iInf _).mp T.si_mem I'`. Establish `hbound : idealMod (x` using `x) T.J I ^ b * ((T.L.pow b).twist (twistSys k x c)).sub I ≤ Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by`. Rewrite using `[hF I, mul_left_comm, ← mul_pow]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `idealMod_zeroIdeal_mul_le T.D T.si I`. Use `_ = Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by`. Rewrite using `[twistMod_eq_span _ I hi, span_singleton_pow_eq, Submodule.span_mul_span, Set.singleton_mul_singleton, hnn, zpow_natCast]`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr z hz`.

Establish `hr' : (r : Ω) ∈ idealMod (x` using `x) T.J I ^ b := by`. Establish `hm` using `Submodule.mem_map_of_mem (f := (Algebra.ofId (chartRing k x I) Ω).toLinearMap) hr`. Rewrite `hm` using `[Submodule.map_pow]`. Establish `hle : Submodule.map (Algebra.ofId (chartRing k x I) Ω).toLinearMap ((idealMod (x` using `x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ≤ idealMod (x := x) T.J I := by`. Introduce and unpack `y ⟨a, ha, rfl⟩`.

Conclude with `ha`. Conclude with `pow_le_pow_left' hle b hm`. Establish `hrz` using `hbound (Submodule.mul_mem_mul hr' hz)`. Rewrite using `[chartRing_smul_def]`. Conclude with `Submodule.span_mono (Set.singleton_subset_iff.mpr hy) hrz`.
-/
theorem proof : StepThree.Away.Statement.{u, w} := by
  intro k _ Ω _ _ N x T b c hc I
  obtain ⟨i, hi⟩ := I.2.1
  have hL : ∀ I' : Chart x, T.L.sub I' = twistMod k x T.c₁ I' * T.D.sub I' := by
    intro I'
    change ((T.M.toSubSystem.pow T.p).twist (twistSys k x T.m)).sub I' =
      _ * ((T.M.toSubSystem.pow T.p).twist (twistSys k x (T.m - T.c₁))).sub I'
    rw [twist_sub, twist_sub, twistSys_sub, twistSys_sub, ← mul_assoc, twistMod_mul,
      add_sub_cancel]
  have hF : ∀ I' : Chart x, ((T.L.pow b).twist (twistSys k x c)).sub I' =
      twistMod k x (c + b * T.c₁) I' * T.D.sub I' ^ b := by
    intro I'
    rw [twist_sub, twistSys_sub, pow_sub, hL, mul_pow, twistMod_pow, ← mul_assoc, twistMod_mul]
  have hn : 0 ≤ c + b * T.c₁ :=
    add_nonneg hc (mul_nonneg (Nat.cast_nonneg b) (by linarith [T.c₁_pos]))
  obtain ⟨n, hnn⟩ := Int.eq_ofNat_of_zero_le hn

  have hy : x i ^ n * T.si ^ b ∈ ((T.L.pow b).twist (twistSys k x c)).secs := by
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    change _ ∈ ((T.L.pow b).twist (twistSys k x c)).sub I'
    rw [hF I', hnn]
    refine Submodule.mul_mem_mul (Submodule.subset_span ⟨X i ^ n, 1, 0, n, one_mem _,
      isHomogeneous_X_pow i n, isHomogeneous_one _ _, by simp, by simp⟩)
      (Submodule.pow_mem_pow _ ?_ b)
    exact (Submodule.mem_iInf _).mp T.si_mem I'

  have hbound : idealMod (x := x) T.J I ^ b * ((T.L.pow b).twist (twistSys k x c)).sub I ≤
      Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
    rw [hF I, mul_left_comm, ← mul_pow]
    calc twistMod k x (c + b * T.c₁) I * (idealMod (x := x) T.J I * T.D.sub I) ^ b
        ≤ twistMod k x (c + b * T.c₁) I * Submodule.span (chartRing k x I) {T.si} ^ b := by
          gcongr
          exact idealMod_zeroIdeal_mul_le T.D T.si I
      _ = Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
          rw [twistMod_eq_span _ I hi, span_singleton_pow_eq, Submodule.span_mul_span,
            Set.singleton_mul_singleton, hnn, zpow_natCast]
  rw [Submodule.smul_le]
  intro r hr z hz
  have hr' : (r : Ω) ∈ idealMod (x := x) T.J I ^ b := by
    have hm := Submodule.mem_map_of_mem (f := (Algebra.ofId (chartRing k x I) Ω).toLinearMap) hr
    rw [Submodule.map_pow] at hm
    have hle : Submodule.map (Algebra.ofId (chartRing k x I) Ω).toLinearMap
        ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ≤
          idealMod (x := x) T.J I := by
      rintro y ⟨a, ha, rfl⟩
      exact ha
    exact pow_le_pow_left' hle b hm
  have hrz := hbound (Submodule.mul_mem_mul hr' hz)
  rw [chartRing_smul_def]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr hy) hrz

end StepThree.Away

end

end GroundTheory.Heights₂.Heights.Kleiman
