import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

/- English proof (translation)
Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg c`.

Use `Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse, M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [map_pow, aeval_X, smul_eq_mul, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n), hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, aeval_X, smul_eq_mul, zpow_neg, zpow_natCast, mul_inv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[mul_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Introduce `a y _ hy`. Establish `: x i ^ c * (a • y) = a • (x i ^ c * y)`. Rewrite using `[chartRing_smul_def, chartRing_smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ a hy`.
-/
theorem zpow_mul_mem_tilde (M : FinGradedSub (S := S) (x := x) Ω) {I : Chart x} {i : Fin (N + 1)}
    (hi : i ∈ I.1) (c d : ℤ) {y : Ω} (hy : y ∈ M.tilde d I) : x i ^ c * y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      simp only [map_pow, aeval_X, smul_eq_mul, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      simp only [map_mul, map_pow, aeval_X, smul_eq_mul, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c * (a • y) = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def]; ring
    rw [this]
    exact Submodule.smul_mem _ a hy

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Establish `h0 : x i ^ (-c) * y ∈ M.tilde 0 I`.

Simplify using `using zpow_mul_mem_tilde M hi (-c) c hy`. Use `Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) * y, h0, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x i ^ c ∈ twistMod S x c I`. Rewrite using `[twistMod_eq_span c I hi]`. Conclude with `Submodule.mem_span_singleton_self _`.

Rewrite using `[smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_mul]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `q ∈ twistMod S x c I at hq`. Rewrite `hq` using `[twistMod_eq_span c I hi, Submodule.mem_span_singleton]`.

Take `⟨a, rfl⟩` from `hq`. Establish `hy' : x i ^ c * y ∈ M.tilde c I`. Simplify using `using zpow_mul_mem_tilde M hi c 0 hy`. Establish `: (a • x i ^ c) • y = a • (x i ^ c * y)`. Rewrite using `[chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]`.

Rewrite using `[SetLike.mem_coe, this]`. Conclude with `Submodule.smul_mem _ a hy'`.
-/
theorem tilde_eq_twist (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) (I : Chart x) :
    M.tilde c I = ((M.tildeSys 0).twist (twistSys S x c)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) * y ∈ M.tilde 0 I := by
      simpa using zpow_mul_mem_tilde M hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) * y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_mul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c * y ∈ M.tilde c I := by
      simpa using zpow_mul_mem_tilde M hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

section Generic

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]

omit [IsFractionRing S F] in

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Conclude with `⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩`. Consider the case `one => exact ⟨1, one_mem _, map_one _⟩`.

Consider the case `mul a b _ _ ha hb`. Take `⟨a', ha', rfl⟩` from `ha`. Take `⟨b', hb', rfl⟩` from `hb`. Conclude with `⟨a' * b', mul_mem ha' hb', map_mul _ _ _⟩`.
-/
theorem exists_monos_map {I : Finset (Fin (N + 1))} {s : Poly F N} (hs : s ∈ monos I) :
    ∃ s' : Poly S N, s' ∈ monos I ∧ map (algebraMap S F) s' = s := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩
  | one => exact ⟨1, one_mem _, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', mul_mem ha' hb', map_mul _ _ _⟩

/- English proof (translation)
Establish `: Nontrivial S` using `(algebraMap S F).domain_nontrivial`. Rewrite using `[IsScalarTower.algebraMap_apply S F Ω]`. Conclude with `(map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht)`.
-/
theorem algebraMap_ne_zero_of_mem (F : Type u) [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] [IsFractionRing S F] {t : S} (ht : t ∈ nonZeroDivisors S) : algebraMap S Ω t ≠ 0 := by
  have : Nontrivial S := (algebraMap S F).domain_nontrivial
  rw [IsScalarTower.algebraMap_apply S F Ω]
  exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht)

/- English proof (translation)
Take `⟨f, s, e, hs, hf, hse, rfl⟩` from `ha`. Take `⟨s', hs', rfl⟩` from `exists_monos_map (S := S) hs`. Establish `hinj : Function.Injective (algebraMap S F)` using `IsFractionRing.injective S F`. Establish `hse' : s'.IsHomogeneous e` using `fun d hd => hse (by`. Rewrite using `[coeff_map]`.

Conclude with `fun h => hd (hinj (h.trans (map_zero _).symm)))`. Establish `hsum : aeval x f / aeval x (map (algebraMap S F) s') = ∑ d ∈ f.support, coeff d f • (aeval x (monomial d (1 : S)) / aeval x s')`. Rewrite using `[aeval_map_algebraMap]`. Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, map_one, one_mul, Algebra.smul_def, mul_div_assoc]`. Rewrite using `[hsum]`. Use `Finset.sum_induction _ (fun a => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I) ?_ ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩ ?_` and prove the remaining obligations. Introduce and unpack `a b ⟨t, ht, hta⟩ ⟨t', ht', htb⟩`.

Use `⟨t * t', mul_mem ht ht', ?_⟩` and prove the remaining obligations. Establish `: algebraMap S Ω (t * t') * (a + b) = algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hta) (mul_mem (Subalgebra.algebraMap_mem _ _) htb)`. Introduce `d hd`. Establish `hmem : aeval x (monomial d (1 : S)) / aeval x s' ∈ chartRing S x I` using `⟨monomial d 1, s', e, hs', isHomogeneous_monomial _ (by`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hf (mem_support_iff.mp hd)), hse', rfl⟩`.

Take `⟨u, v, hv, huv⟩` from `IsFractionRing.div_surjective (A := S) (coeff d f)`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Establish `hv0 : algebraMap S Ω v ≠ 0` using `algebraMap_ne_zero_of_mem F hv`. Establish `: algebraMap S Ω v * (coeff d f • (aeval x (monomial d (1 : S)) / aeval x s')) = algebraMap S Ω u * (aeval x (monomial d (1 : S)) / aeval x s')`. Rewrite using `[Algebra.smul_def, ← huv, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ _) hmem`.
-/
theorem exists_mul_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing F x I) :
    ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨s', hs', rfl⟩ := exists_monos_map (S := S) hs
  have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hse' : s'.IsHomogeneous e := fun d hd => hse (by
    rw [coeff_map]; exact fun h => hd (hinj (h.trans (map_zero _).symm)))
  have hsum : aeval x f / aeval x (map (algebraMap S F) s') =
      ∑ d ∈ f.support, coeff d f • (aeval x (monomial d (1 : S)) / aeval x s') := by
    rw [aeval_map_algebraMap]
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [aeval_monomial, aeval_monomial, map_one, one_mul, Algebra.smul_def, mul_div_assoc]
  rw [hsum]
  refine Finset.sum_induction _ (fun a => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I)
    ?_ ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩ ?_
  · rintro a b ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hta)
      (mul_mem (Subalgebra.algebraMap_mem _ _) htb)
  · intro d hd
    have hmem : aeval x (monomial d (1 : S)) / aeval x s' ∈ chartRing S x I :=
      ⟨monomial d 1, s', e, hs', isHomogeneous_monomial _ (by
        rw [Finsupp.degree_eq_weight_one]; exact hf (mem_support_iff.mp hd)), hse', rfl⟩
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := S) (coeff d f)
    refine ⟨v, hv, ?_⟩
    have hv0 : algebraMap S Ω v ≠ 0 := algebraMap_ne_zero_of_mem F hv
    have : algebraMap S Ω v * (coeff d f • (aeval x (monomial d (1 : S)) / aeval x s')) =
        algebraMap S Ω u * (aeval x (monomial d (1 : S)) / aeval x s') := by
      rw [Algebra.smul_def, ← huv, map_div₀, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      field_simp
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hmem

/- English proof (translation)
Establish `hS : ∀ (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I` using `fun t y hy => by`. Rewrite using `[← Algebra.smul_def]`. Conclude with `(Q.sub I).smul_of_tower_mem t hy`. Use `Submodule.span_induction (p := fun z _ => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce `z hz`.

Conclude with `⟨1, one_mem _, by rw [map_one, one_mul]; exact hz⟩`. Conclude with `⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩`. Introduce and unpack `a b _ _ ⟨t, ht, hta⟩ ⟨t', ht', htb⟩`. Use `⟨t * t', mul_mem ht ht', ?_⟩` and prove the remaining obligations. Establish `: algebraMap S Ω (t * t') * (a + b) = algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b)`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (hS t' hta) (hS t htb)`. Introduce and unpack `a z _ ⟨t, ht, htz⟩`.

Take `⟨u, hu, hua⟩` from `exists_mul_mem_chartRing (S := S) a.2`. Use `⟨u * t, mul_mem hu ht, ?_⟩` and prove the remaining obligations. Establish `: algebraMap S Ω (u * t) * (a • z) = (⟨_, hua⟩ : chartRing S x I) • (algebraMap S Ω t * z)`. Rewrite using `[chartRing_smul_def, chartRing_smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ htz`.
-/
theorem exists_mul_mem_of_mem_extend (Q : SubSystem S x Ω) (I : Chart x) {z : Ω}
    (hz : z ∈ (Q.extend F).sub I) : ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I := by
  have hS : ∀ (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I := fun t y hy => by
    rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
  refine Submodule.span_induction
    (p := fun z _ => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I) ?_ ?_ ?_ ?_ hz
  · intro z hz
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact hz⟩
  · exact ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩
  · rintro a b _ _ ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (hS t' hta) (hS t htb)
  · rintro a z _ ⟨t, ht, htz⟩
    obtain ⟨u, hu, hua⟩ := exists_mul_mem_chartRing (S := S) a.2
    refine ⟨u * t, mul_mem hu ht, ?_⟩
    have : algebraMap S Ω (u * t) * (a • z) =
        (⟨_, hua⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ _ htz

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr fun z hz => ?_` and prove the remaining obligations. Rewrite `hz`, the goal using `[SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf]`. Introduce `I`. Conclude with `Submodule.subset_span (hz I)`.

Introduce `z hz`. Rewrite `hz` using `[SubSystem.secs, Submodule.mem_iInf]`. Use `choose t ht htz using fun I => exists_mul_mem_of_mem_extend Q I (hz I)`. Establish `hS : ∀ (I : Chart x) (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I` using `fun I t y hy => by rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy`. Use `set t₀ := ∏ I, t I with ht₀`.

Establish `ht₀m : t₀ ∈ nonZeroDivisors S` using `prod_mem fun I _ => ht I`. Establish `hmem : algebraMap S Ω t₀ * z ∈ Q.secs`. Rewrite using `[SubSystem.secs, Submodule.mem_iInf]`. Introduce `I`. Rewrite using `[ht₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)), mul_assoc]`.

Conclude with `hS I _ (htz I)`. Establish `h0 : algebraMap S F t₀ ≠ 0`. Establish `: Nontrivial S` using `(algebraMap S F).domain_nontrivial`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht₀m`. Establish `: z = (algebraMap S F t₀)⁻¹ • (algebraMap S Ω t₀ * z)`.

Rewrite using `[Algebra.smul_def, map_inv₀, IsScalarTower.algebraMap_apply S F Ω, inv_mul_cancel_left₀ ((map_ne_zero _).mpr h0)]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem span_secs_eq_secs_extend (Q : SubSystem S x Ω) :
    Submodule.span F (Q.secs : Set Ω) = (Q.extend F).secs := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf] at hz ⊢
    intro I
    exact Submodule.subset_span (hz I)
  · intro z hz
    rw [SubSystem.secs, Submodule.mem_iInf] at hz
    choose t ht htz using fun I => exists_mul_mem_of_mem_extend Q I (hz I)
    have hS : ∀ (I : Chart x) (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I :=
      fun I t y hy => by rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
    set t₀ := ∏ I, t I with ht₀
    have ht₀m : t₀ ∈ nonZeroDivisors S := prod_mem fun I _ => ht I
    have hmem : algebraMap S Ω t₀ * z ∈ Q.secs := by
      rw [SubSystem.secs, Submodule.mem_iInf]
      intro I
      rw [ht₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
        mul_assoc]
      exact hS I _ (htz I)
    have h0 : algebraMap S F t₀ ≠ 0 := by
      have : Nontrivial S := (algebraMap S F).domain_nontrivial
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht₀m
    have : z = (algebraMap S F t₀)⁻¹ • (algebraMap S Ω t₀ * z) := by
      rw [Algebra.smul_def, map_inv₀, IsScalarTower.algebraMap_apply S F Ω,
        inv_mul_cancel_left₀ ((map_ne_zero _).mpr h0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Generic

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x Q hx`. Establish `tail : ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω), (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧ ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j …`. Introduce `c₁`. Take `⟨M, -, hM⟩` from `hE S Ω N x Ω Q.toSubFamily Q.fg`. Establish `h0 : M.tildeSys 0 = Q.toSubSystem` using `SubSystem.ext_sub hM`.

Establish `hc : ∀ c : ℤ, M.tildeSys c = Q.twist (twistSys S x c)` using `fun c => SubSystem.ext_sub fun I => by rw [← h0]; exact tilde_eq_twist M c I`. Take `⟨n, deg, gen, hgen, hspan⟩` from `hT S Ω N x M hx c₁`. Use `⟨n, deg, gen, fun j => ⟨(hgen j).1, ?_⟩, fun c hc₁ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `(hgen j).2`.

Rewrite using `[← hc]`. Conclude with `hspan c hc₁`. Use `⟨?_, tail, fun F _ _ _ _ _ => span_secs_eq_secs_extend Q.toSubSystem⟩` and prove the remaining obligations. Take `⟨n, deg, gen, hgen, hspan⟩` from `tail 0`. Establish `hle : Q.secs ≤ Submodule.span S (Set.range gen)`.

Establish `h` using `hspan 0 le_rfl`. Rewrite `h` using `[SubSystem.twist_twistSys_zero]`. Use `h.trans (Submodule.span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, f, e, hf, hej, rfl⟩`. Establish `he : e = 0` using `by have := (hgen j).1; omega`.

Substitute `he` using the available equality. Establish `hfC : f = C (coeff 0 f)` using `totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hf.totalDegree_le)`. Rewrite using `[hfC, aeval_C, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `isNoetherian_span_of_finite S (Set.finite_range gen)` as an intermediate fact.

Conclude with `Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)`.
-/
theorem FiniteSections.proof (hE : Extension.Statement.{u, w, w}) (hT : TildeTail.Statement.{u, w}) :
    FiniteSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q hx

  have tail : ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j} := by
    intro c₁
    obtain ⟨M, -, hM⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
    have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
    have hc : ∀ c : ℤ, M.tildeSys c = Q.twist (twistSys S x c) := fun c =>
      SubSystem.ext_sub fun I => by rw [← h0]; exact tilde_eq_twist M c I
    obtain ⟨n, deg, gen, hgen, hspan⟩ := hT S Ω N x M hx c₁
    refine ⟨n, deg, gen, fun j => ⟨(hgen j).1, ?_⟩, fun c hc₁ => ?_⟩
    · rw [← hc]; exact (hgen j).2
    · rw [← hc]; exact hspan c hc₁
  refine ⟨?_, tail, fun F _ _ _ _ _ => span_secs_eq_secs_extend Q.toSubSystem⟩

  obtain ⟨n, deg, gen, hgen, hspan⟩ := tail 0
  have hle : Q.secs ≤ Submodule.span S (Set.range gen) := by
    have h := hspan 0 le_rfl
    rw [SubSystem.twist_twistSys_zero] at h
    refine h.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨j, f, e, hf, hej, rfl⟩
    have he : e = 0 := by have := (hgen j).1; omega
    subst he
    have hfC : f = C (coeff 0 f) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hf.totalDegree_le)
    rw [hfC, aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := isNoetherian_span_of_finite S (Set.finite_range gen)
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

end

end GroundTheory.Heights₂.Heights.Kleiman
