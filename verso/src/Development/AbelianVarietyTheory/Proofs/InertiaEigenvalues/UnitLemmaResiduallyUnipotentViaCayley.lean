import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftSeparableOfAdjoinEqTopStatement

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CayleyCase

/- English proof (translation)
Take `⟨u, hu⟩` from `hc`. Establish `hd : (X - C c) ∣ p - C (p.eval c)`. Rewrite using `[dvd_iff_isRoot]`. Simplify using the standard rewrite rules. Take `⟨h, hh⟩` from `hd`.

Use `⟨-algebraMap O A (↑u⁻¹ : O) * aeval a h, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) (aeval_mem_adjoin_singleton _ _)`. Establish `e` using `congrArg (aeval a) hh`. Simplify using `only [map_sub, hp, aeval_C, map_mul, aeval_X] at e`. Rewrite `e` using `[← hu]`.

Establish `: algebraMap O A (↑u⁻¹ : O) * algebraMap O A (u : O) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Take the linear combination `(algebraMap O A (↑u⁻¹ : O)) * e + this`.
-/
theorem sub_inv_mem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a : A) (c : O) (p : O[X])
    (hp : aeval a p = 0) (hc : IsUnit (p.eval c)) :
    ∃ w ∈ Algebra.adjoin O ({a} : Set A), (a - algebraMap O A c) * w = 1 := by
  obtain ⟨u, hu⟩ := hc
  have hd : (X - C c) ∣ p - C (p.eval c) := by
    rw [dvd_iff_isRoot]; simp
  obtain ⟨h, hh⟩ := hd
  refine ⟨-algebraMap O A (↑u⁻¹ : O) * aeval a h, ?_, ?_⟩
  · exact mul_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) (aeval_mem_adjoin_singleton _ _)
  · have e := congrArg (aeval a) hh
    simp only [map_sub, hp, aeval_C, map_mul, aeval_X] at e
    rw [← hu] at e
    have : algebraMap O A (↑u⁻¹ : O) * algebraMap O A (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (algebraMap O A (↑u⁻¹ : O)) * e + this

/- English proof (translation)
Introduce `z hz`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `hL`. Consider the case `algebraMap r => intro y hy`.

Rewrite using `[← Algebra.smul_def]`. Conclude with `L.smul_mem r hy`. Consider the case `add x y _ _ hx hy => intro w hw`. Rewrite using `[add_mul]`. Conclude with `L.add_mem (hx w hw) (hy w hw)`.

Consider the case `mul x y _ _ hx hy => intro w hw`. Rewrite using `[mul_assoc]`. Conclude with `hx _ (hy w hw)`.
-/
theorem adjoin_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a : A) (L : Submodule O A)
    (hL : ∀ y ∈ L, a * y ∈ L) : ∀ z ∈ Algebra.adjoin O ({a} : Set A), ∀ y ∈ L, z * y ∈ L := by
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hL
  | algebraMap r => intro y hy; rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x y _ _ hx hy => intro w hw; rw [add_mul]; exact L.add_mem (hx w hw) (hy w hw)
  | mul x y _ _ hx hy => intro w hw; rw [mul_assoc]; exact hx _ (hy w hw)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨w, hw, hgw⟩` from `sub_inv_mem g (-s) Q hQ hQs`. Rewrite `hgw` using `[map_neg, sub_neg_eq_add]`. Establish `e : Y = algebraMap O A ε * (g - algebraMap O A s) * w`. Take the linear combination `(-Y) * hgw + w * hY`.

Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _))) hw`. Use `set n := Q.natDegree`. Set `R : O[X]` to `∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C s * (C ε + X)) ^ i * (C ε - X) ^ (n - i)`. Establish `hgY : g * (algebraMap O A ε - Y) = algebraMap O A s * (algebraMap O A ε + Y)`.

Take the linear combination `(-1 : A) * hY`. Establish `hR : aeval Y R = 0`. Establish `: aeval Y R = (algebraMap O A ε - Y) ^ n * aeval g Q` using `by conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]`. Simplify using `only [R, map_sum, map_mul, map_pow, aeval_C, map_add, map_sub, aeval_X]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hin : i ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[← hgY, mul_pow, Algebra.smul_def]`. Establish `: (algebraMap O A ε - Y) ^ n = (algebraMap O A ε - Y) ^ i * (algebraMap O A ε - Y) ^ (n - i)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hin]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hQ, mul_zero]`. Establish `hRe : R.eval ε = (s * (ε + ε)) ^ n`. Simplify using `only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_sub, eval_X, sub_self]`. Rewrite using `[Finset.sum_eq_single n]`.

Simplify using `[n, hQm.coeff_natDegree]`. Introduce `i hi hin`. Establish `: 0 < n - i` using `Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)`. Rewrite using `[zero_pow this.ne', mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h`. Establish `hRu : IsUnit (R.eval ε)`. Rewrite using `[hRe, ← two_mul]`. Conclude with `(hs.mul (h2.mul hε)).pow _`. Take `⟨v, hv, hYv⟩` from `sub_inv_mem Y ε R hR hRu`.

Establish `e : g = -(algebraMap O A s * (algebraMap O A ε + Y)) * v`. Take the linear combination `(-g) * hYv - v * hgY`. Rewrite using `[e]`. Conclude with `mul_mem (neg_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (add_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)))) hv`.
-/
theorem mem_adjoin_both {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (s ε : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval (-s))) (hs : IsUnit s) (hε : IsUnit ε)
    (h2 : IsUnit (2 : O))
    (hY : Y * (g + algebraMap O A s) = algebraMap O A ε * (g - algebraMap O A s)) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  constructor
  · obtain ⟨w, hw, hgw⟩ := sub_inv_mem g (-s) Q hQ hQs
    rw [map_neg, sub_neg_eq_add] at hgw
    have e : Y = algebraMap O A ε * (g - algebraMap O A s) * w := by
      linear_combination (-Y) * hgw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
      (sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _))) hw
  · set n := Q.natDegree
    let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C s * (C ε + X)) ^ i * (C ε - X) ^ (n - i)
    have hgY : g * (algebraMap O A ε - Y) = algebraMap O A s * (algebraMap O A ε + Y) := by
      linear_combination (-1 : A) * hY
    have hR : aeval Y R = 0 := by
      have : aeval Y R = (algebraMap O A ε - Y) ^ n * aeval g Q := by
        conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
        simp only [R, map_sum, map_mul, map_pow, aeval_C, map_add, map_sub, aeval_X]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [← hgY, mul_pow, Algebra.smul_def]
        have : (algebraMap O A ε - Y) ^ n = (algebraMap O A ε - Y) ^ i * (algebraMap O A ε - Y) ^ (n - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hin]
        rw [this]; ring
      rw [this, hQ, mul_zero]
    have hRe : R.eval ε = (s * (ε + ε)) ^ n := by
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_sub, eval_X, sub_self]
      rw [Finset.sum_eq_single n]
      · simp [n, hQm.coeff_natDegree]
      · intro i hi hin
        have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
        rw [zero_pow this.ne', mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    have hRu : IsUnit (R.eval ε) := by
      rw [hRe, ← two_mul]
      exact (hs.mul (h2.mul hε)).pow _
    obtain ⟨v, hv, hYv⟩ := sub_inv_mem Y ε R hR hRu
    have e : g = -(algebraMap O A s * (algebraMap O A ε + Y)) * v := by
      linear_combination (-g) * hYv - v * hgY
    rw [e]
    exact mul_mem (neg_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
      (add_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)))) hv

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hL => adjoin_stable g L hL Y h.1, fun hL => adjoin_stable Y L hL g h.2⟩`.
-/
theorem stable_iff {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A)
    (h : Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A)) (L : Submodule O A) :
    (∀ y ∈ L, g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L) :=
  ⟨fun hL => adjoin_stable g L hL Y h.1, fun hL => adjoin_stable Y L hL g h.2⟩

/- English proof (translation)
Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin hx`. Consider the case `algebraMap r => rw [IsScalarTower.algebraMap_apply O E A]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`.
-/
theorem mem_adjoin_of_mem {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O E] [Algebra E A]
    [Algebra O A] [IsScalarTower O E A] {a z : A} (h : z ∈ Algebra.adjoin O ({a} : Set A)) :
    z ∈ Algebra.adjoin E ({a} : Set A) := by
  induction h using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r => rw [IsScalarTower.algebraMap_apply O E A]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/- English proof (translation)
Use `set b := Module.finBasis E A`. Set `M` to `Subalgebra.toSubmodule (Algebra.adjoin O ({g} : Set A)) * Submodule.span O (Set.range b)`. Establish `hb : ∀ i, b i ∈ M` using `fun i => by`. Establish `h1 : (1 : A) ∈ Subalgebra.toSubmodule (Algebra.adjoin O ({g} : Set A))` using `(Algebra.adjoin O ({g} : Set A)).one_mem`. Establish `h2 : b i ∈ Submodule.span O (Set.range b)` using `Submodule.subset_span ⟨i, rfl⟩`.

Use `Submodule.mul_mem_mul h1 h2` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Use `⟨M, ⟨hg.fg_adjoin_singleton.mul (Submodule.fg_span (Set.finite_range _)), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Submodule.subset_span (hb i)`. Establish `: M ≤ M.comap (LinearMap.mulLeft O g)`. Rewrite using `[Submodule.mul_le]`. Introduce `a ha m hm`. Use `show g * (a * m) ∈ M`.

Rewrite using `[← mul_assoc]`. Conclude with `Submodule.mul_mem_mul (Subalgebra.mul_mem _ (Algebra.subset_adjoin rfl) ha) hm`. Conclude with `fun y hy => this hy`.
-/
theorem exists_stable_lat {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O E] [Algebra E A]
    [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] (g : A) (hg : IsIntegral O g) :
    ∃ M : Submodule O A, IsLat O E M ∧ ∀ y ∈ M, g * y ∈ M := by
  set b := Module.finBasis E A
  let M := Subalgebra.toSubmodule (Algebra.adjoin O ({g} : Set A)) * Submodule.span O (Set.range b)
  have hb : ∀ i, b i ∈ M := fun i => by
    have h1 : (1 : A) ∈ Subalgebra.toSubmodule (Algebra.adjoin O ({g} : Set A)) :=
      (Algebra.adjoin O ({g} : Set A)).one_mem
    have h2 : b i ∈ Submodule.span O (Set.range b) := Submodule.subset_span ⟨i, rfl⟩
    have := Submodule.mul_mem_mul h1 h2
    rwa [one_mul] at this
  refine ⟨M, ⟨hg.fg_adjoin_singleton.mul (Submodule.fg_span (Set.finite_range _)), ?_⟩, ?_⟩
  · rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hb i)
  · have : M ≤ M.comap (LinearMap.mulLeft O g) := by
      rw [Submodule.mul_le]
      intro a ha m hm
      show g * (a * m) ∈ M
      rw [← mul_assoc]
      exact Submodule.mul_mem_mul (Subalgebra.mul_mem _ (Algebra.subset_adjoin rfl) ha) hm
    exact fun y hy => this hy

/- English proof (translation)
Establish `c1` using `GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ g₁ g₂ hr M₁ M₂ l₁ l₂ s₁ s₂`. Establish `c2` using `GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ Y₁ Y₂ hr' M₁ M₂ l₁ l₂ ((h₁ M₁).1 s₁) ((h₂ M₂).1 s₂)`. Establish `hc : Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} = Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (Y₁, Y₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd …` using `Nat.card_congr (Equiv.subtypeEquivRight fun M => by rw [h M])`. Rewrite `c1` using `[hc, c2]`. Establish `hq : (1 : ℚ) < Nat.card (IsLocalRing.ResidueField O)`.

Conclude with `(Finite.one_lt_card (α := IsLocalRing.ResidueField O))` after adjusting the coercions. Conclude with `(zpow_right_injective₀ (by linarith) hq.ne' c1).symm`.
-/
theorem val_res_eq {O E A₁ A₂ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ Y₁ : A₁) (g₂ Y₂ : A₂)
    (hr : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0)
    (hr' : resultant (LinearMap.mulLeft E Y₁).charpoly (LinearMap.mulLeft E Y₂).charpoly ≠ 0)
    (h₁ : ∀ L : Submodule O A₁, (∀ y ∈ L, g₁ * y ∈ L) ↔ (∀ y ∈ L, Y₁ * y ∈ L))
    (h₂ : ∀ L : Submodule O A₂, (∀ y ∈ L, g₂ * y ∈ L) ↔ (∀ y ∈ L, Y₂ * y ∈ L))
    (h : ∀ L : Submodule O (A₁ × A₂), (∀ y ∈ L, (g₁, g₂) * y ∈ L) ↔ (∀ y ∈ L, (Y₁, Y₂) * y ∈ L))
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) (l₁ : IsLat O E M₁) (l₂ : IsLat O E M₂)
    (s₁ : ∀ y ∈ M₁, g₁ * y ∈ M₁) (s₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) =
      val O (resultant (LinearMap.mulLeft E Y₁).charpoly (LinearMap.mulLeft E Y₂).charpoly) := by
  have c1 := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ g₁ g₂ hr M₁ M₂ l₁ l₂ s₁ s₂
  have c2 := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ Y₁ Y₂ hr' M₁ M₂ l₁ l₂ ((h₁ M₁).1 s₁) ((h₂ M₂).1 s₂)
  have hc : Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧
      M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} =
      Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (Y₁, Y₂) * y ∈ M) ∧
      M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M => by rw [h M])
  rw [hc, c2] at c1
  have hq : (1 : ℚ) < Nat.card (IsLocalRing.ResidueField O) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField O))
  exact (zpow_right_injective₀ (by linarith) hq.ne' c1).symm

/- English proof (translation)
Take `⟨ht, hr⟩` from `GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable E A g hg`. Use `GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced E A Y (eq_top_iff.2 ?_) hr` and prove the remaining obligations. Rewrite using `[← ht]`. Conclude with `Algebra.adjoin_le (Set.singleton_subset_iff.2 h₂)`.
-/
theorem separable_of_adjoin {E A : Type} [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A]
    (g Y : A) (h₁ : Y ∈ Algebra.adjoin E ({g} : Set A)) (h₂ : g ∈ Algebra.adjoin E ({Y} : Set A))
    (hg : (LinearMap.mulLeft E g).charpoly.Separable) : (LinearMap.mulLeft E Y).charpoly.Separable := by
  obtain ⟨ht, hr⟩ := GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable E A g hg
  refine GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced E A Y (eq_top_iff.2 ?_) hr
  rw [← ht]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 h₂)

variable {K : UQ}

/- English proof (translation)
Take `⟨x, y, hxy, hm⟩` from `K.c_res`. Use `⟨x - y, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hm ((IsLocalRing.mem_maximalIdeal _).2 h)`. Establish `: K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x` using `by rw [← hxy, K.c_c]`.

Simplify using `only [map_sub, hxy, this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eps (K : UQ) : ∃ ε : K.O, IsUnit ε ∧ K.c (algebraMap K.O K.E ε) = -algebraMap K.O K.E ε := by
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  refine ⟨x - y, ?_, ?_⟩
  · by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  · have : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
    simp only [map_sub, hxy, this]; ring

def withG (B : InvAlg K) (Y : B.A) : InvAlg K := { B with g := Y }

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg]`.
-/
theorem σ_algebraMap (B : InvAlg K) (a : K.O) :
    B.σ (algebraMap K.O B.A a) = algebraMap K.E B.A (K.c (algebraMap K.O K.E a)) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg]

/- English proof (translation)
Establish `h1` using `congrArg B.σ hY`. Simplify using `only [map_mul, map_add, map_sub, σ_algebraMap, hε, map_neg] at h1`. Establish `he : algebraMap K.E B.A (algebraMap K.O K.E ε) = algebraMap K.O B.A ε` using `(IsScalarTower.algebraMap_apply _ _ _ _).symm`. Rewrite `h1` using `[he]`. Establish `hs0 : algebraMap K.O B.A s * algebraMap K.E B.A (K.c (algebraMap K.O K.E s)) = 1`.

Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A s, ← map_mul, hs, map_one]`. Use `set s' := algebraMap K.O B.A s`. Use `set t := algebraMap K.E B.A (K.c (algebraMap K.O K.E s))`. Establish `hs' : s' * t = 1` using `hs0`. Use `set ε' := algebraMap K.O B.A ε`.

Establish `key : (B.σ Y - Y) * (B.g + s') = 0`. Take the linear combination `(B.g * s') * h1 - hY - (s' * B.σ Y + s' * ε') * hu - (B.g * B.σ Y - B.g * ε') * hs'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cayley_selfadj (B : InvAlg K) (s ε : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hs : algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1)
    (hε : K.c (algebraMap K.O K.E ε) = -algebraMap K.O K.E ε)
    (w : B.A) (hw : (B.g + algebraMap K.O B.A s) * w = 1)
    (hY : Y * (B.g + algebraMap K.O B.A s) = algebraMap K.O B.A ε * (B.g - algebraMap K.O B.A s)) :
    B.σ Y = Y := by
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_add, map_sub, σ_algebraMap, hε, map_neg] at h1
  have he : algebraMap K.E B.A (algebraMap K.O K.E ε) = algebraMap K.O B.A ε :=
    (IsScalarTower.algebraMap_apply _ _ _ _).symm
  rw [he] at h1
  have hs0 : algebraMap K.O B.A s * algebraMap K.E B.A (K.c (algebraMap K.O K.E s)) = 1 := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A s, ← map_mul, hs, map_one]
  set s' := algebraMap K.O B.A s
  set t := algebraMap K.E B.A (K.c (algebraMap K.O K.E s))
  have hs' : s' * t = 1 := hs0
  set ε' := algebraMap K.O B.A ε
  have key : (B.σ Y - Y) * (B.g + s') = 0 := by
    linear_combination (B.g * s') * h1 - hY - (s' * B.σ Y + s' * ε') * hu - (B.g * B.σ Y - B.g * ε') * hs'
  calc B.σ Y = B.σ Y * ((B.g + s') * w) := by rw [hw, mul_one]
    _ = Y * ((B.g + s') * w) + (B.σ Y - Y) * (B.g + s') * w := by ring
    _ = Y := by rw [key, hw]; ring

/- English proof (translation)
Establish `h` using `LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)`. Establish `h2` using `Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g B.P`. Establish `h3 : (Algebra.lmul K.E B.A) (aeval B.g B.P) = 0` using `by rw [← h2]; exact h`. Simplify using `using congrArg (fun f => f 1) h3`.
-/
theorem aeval_P (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
  have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g B.P
  have h3 : (Algebra.lmul K.E B.A) (aeval B.g B.P) = 0 := by rw [← h2]; exact h
  simpa using congrArg (fun f => f 1) h3

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective K.O K.E`. Establish `hm : Q.Monic` using `monic_of_injective hinj (hQ ▸ ((LinearMap.charpoly_monic _).mul (LinearMap.charpoly_monic _)))`. Establish `i1 : IsIntegral K.O B₁.g` using `⟨Q, hm, by rw [← aeval_def, ← aeval_map_algebraMap K.E, hQ, map_mul, aeval_P, zero_mul]⟩`. Establish `i2 : IsIntegral K.O B₂.g` using `⟨Q, hm, by rw [← aeval_def, ← aeval_map_algebraMap K.E, hQ, map_mul, aeval_P, mul_zero]⟩`. Take `⟨Q₁, -, e₁⟩` from `Orbit.exists_monic_map_eq_charpoly₂ B₁ hsep.of_mul_left i1`.

Take `⟨Q₂, -, e₂⟩` from `Orbit.exists_monic_map_eq_charpoly₂ B₂ hsep.of_mul_right i2`. Use `⟨Q₁, Q₂, map_injective _ hinj (by rw [Polynomial.map_mul, e₁, e₂, hQ]), e₁, e₂, ?_, ?_, hm⟩` and prove the remaining obligations. Rewrite using `[← aeval_map_algebraMap K.E, e₁, aeval_P]`. Rewrite using `[← aeval_map_algebraMap K.E, e₂, aeval_P]`.
-/
theorem lift_factor (B₁ B₂ : InvAlg K) (hsep : (B₁.P * B₂.P).Separable) (Q : K.O[X])
    (hQ : Q.map (algebraMap K.O K.E) = B₁.P * B₂.P) :
    ∃ Q₁ Q₂ : K.O[X], Q = Q₁ * Q₂ ∧ Q₁.map (algebraMap K.O K.E) = B₁.P ∧ Q₂.map (algebraMap K.O K.E) = B₂.P ∧
      aeval B₁.g Q₁ = 0 ∧ aeval B₂.g Q₂ = 0 ∧ Q.Monic := by
  have hinj := IsFractionRing.injective K.O K.E
  have hm : Q.Monic := monic_of_injective hinj
    (hQ ▸ ((LinearMap.charpoly_monic _).mul (LinearMap.charpoly_monic _)))
  have i1 : IsIntegral K.O B₁.g :=
    ⟨Q, hm, by rw [← aeval_def, ← aeval_map_algebraMap K.E, hQ, map_mul, aeval_P, zero_mul]⟩
  have i2 : IsIntegral K.O B₂.g :=
    ⟨Q, hm, by rw [← aeval_def, ← aeval_map_algebraMap K.E, hQ, map_mul, aeval_P, mul_zero]⟩
  obtain ⟨Q₁, -, e₁⟩ := Orbit.exists_monic_map_eq_charpoly₂ B₁ hsep.of_mul_left i1
  obtain ⟨Q₂, -, e₂⟩ := Orbit.exists_monic_map_eq_charpoly₂ B₂ hsep.of_mul_right i2
  refine ⟨Q₁, Q₂, map_injective _ hinj (by rw [Polynomial.map_mul, e₁, e₂, hQ]), e₁, e₂, ?_, ?_, hm⟩
  · rw [← aeval_map_algebraMap K.E, e₁, aeval_P]
  · rw [← aeval_map_algebraMap K.E, e₂, aeval_P]

/- English proof (translation)
Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]`. Simplify using `only [eval_pow, eval_sub, eval_X, eval_C, map_neg]`. Apply `pow_ne_zero` to reduce the goal to its premises. Establish `h2 : IsLocalRing.residue K.O 2 ≠ 0` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).2 hodd`. Establish `hs : IsLocalRing.residue K.O s ≠ 0` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit`.

Rewrite using `[show -(IsLocalRing.residue K.O s) - IsLocalRing.residue K.O s = -(IsLocalRing.residue K.O 2 * IsLocalRing.residue K.O s) by rw [map_ofNat]; ring]`. Conclude with `neg_ne_zero.2 (mul_ne_zero h2 hs)`.
-/
theorem eval_neg_isUnit (hodd : K.Odd) (Q : K.O[X]) (s : K.Oˣ)
    (hQr : Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) :
    IsUnit (Q.eval (-(s : K.O))) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]
  simp only [eval_pow, eval_sub, eval_X, eval_C, map_neg]
  apply pow_ne_zero
  have h2 : IsLocalRing.residue K.O 2 ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hodd
  have hs : IsLocalRing.residue K.O s ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit
  rw [show -(IsLocalRing.residue K.O s) - IsLocalRing.residue K.O s =
    -(IsLocalRing.residue K.O 2 * IsLocalRing.residue K.O s) by rw [map_ofNat]; ring]
  exact neg_ne_zero.2 (mul_ne_zero h2 hs)

/- English proof (translation)
The claim follows from `Set.ext fun L => and_congr_right fun _ => and_congr_left fun _ => (h L).symm`.
-/
theorem X_withG (B : InvAlg K) (Y : B.A)
    (h : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L)) (x : B.A) :
    (withG B Y).X x = B.X x :=
  Set.ext fun L => and_congr_right fun _ => and_congr_left fun _ => (h L).symm

/- English proof (translation)
Unfold `InvAlg.N`. Rewrite using `[X_withG B Y h]`. Both sides reduce to the same expression.
-/
theorem N_withG (B : InvAlg K) (Y : B.A)
    (h : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L)) (x : B.A) :
    (withG B Y).N x = B.N x := by
  unfold InvAlg.N
  rw [X_withG B Y h]
  rfl

/- English proof (translation)
Use `show ∑ᶠ k : B.Cl, (withG B Y).N k.rep = ∑ᶠ k : B.Cl, B.N k.rep`. Conclude with `finsum_congr fun k => N_withG B Y h _`.
-/
theorem stSum_withG (B : InvAlg K) (Y : B.A)
    (h : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L)) :
    (withG B Y).stSum = B.stSum := by
  show ∑ᶠ k : B.Cl, (withG B Y).N k.rep = ∑ᶠ k : B.Cl, B.N k.rep
  exact finsum_congr fun k => N_withG B Y h _

/- English proof (translation)
Use `show ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (InvAlg.Cl.rep k).1) * (withG (B₁.prod B₂) (Y₁, Y₂)).N k.rep = ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep`. Conclude with `finsum_congr fun k => by rw [N_withG (B₁.prod B₂) (Y₁, Y₂) h]`.
-/
theorem kapSum_withG (B₁ B₂ : InvAlg K) (Y₁ : B₁.A) (Y₂ : B₂.A)
    (h : ∀ L : Submodule K.O (B₁.A × B₂.A), (∀ y ∈ L, (B₁.g, B₂.g) * y ∈ L) ↔ (∀ y ∈ L, (Y₁, Y₂) * y ∈ L)) :
    InvAlg.kapSum (withG B₁ Y₁) (withG B₂ Y₂) = InvAlg.kapSum B₁ B₂ := by
  show ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (InvAlg.Cl.rep k).1) * (withG (B₁.prod B₂) (Y₁, Y₂)).N k.rep =
    ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep
  exact finsum_congr fun k => by rw [N_withG (B₁.prod B₂) (Y₁, Y₂) h]

/- English proof (translation)
Introduce `hL K hodd B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩`. Establish `hinj` using `IsFractionRing.injective K.O K.E`. Take `⟨ε, hεu, hεc⟩` from `exists_eps K`. Take `⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hm⟩` from `lift_factor B₁ B₂ hsep Q hQ`. Establish `hQs` using `eval_neg_isUnit hodd Q s hQr`.

Establish `hQs₁ : IsUnit (Q₁.eval (-(s : K.O)))`. Rewrite `hQs` using `[hQQ, eval_mul]`. Conclude with `isUnit_of_mul_isUnit_left hQs`. Establish `hQs₂ : IsUnit (Q₂.eval (-(s : K.O)))`. Rewrite `hQs` using `[hQQ, eval_mul]`.

Conclude with `isUnit_of_mul_isUnit_right hQs`. Establish `hm₁ : Q₁.Monic` using `monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)`. Establish `hm₂ : Q₂.Monic` using `monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)`. Take `⟨w₁, -, hw₁⟩` from `sub_inv_mem B₁.g (-(s : K.O)) Q₁ a₁ hQs₁`. Take `⟨w₂, -, hw₂⟩` from `sub_inv_mem B₂.g (-(s : K.O)) Q₂ a₂ hQs₂`.

Rewrite `hw₁`, `hw₂` using `[map_neg, sub_neg_eq_add]`. Use `set Y₁ := algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s) * w₁ with hY₁d`. Use `set Y₂ := algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s) * w₂ with hY₂d`. Establish `hY₁ : Y₁ * (B₁.g + algebraMap K.O B₁.A s) = algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s)`. Rewrite using `[hY₁d]`.

Take the linear combination `(algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s)) * hw₁`. Establish `hY₂ : Y₂ * (B₂.g + algebraMap K.O B₂.A s) = algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s)`. Rewrite using `[hY₂d]`. Take the linear combination `(algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s)) * hw₂`. Establish `adj₁` using `mem_adjoin_both B₁.g Y₁ (s : K.O) ε Q₁ hm₁ a₁ hQs₁ s.isUnit hεu hodd hY₁`.

Establish `adj₂` using `mem_adjoin_both B₂.g Y₂ (s : K.O) ε Q₂ hm₂ a₂ hQs₂ s.isUnit hεu hodd hY₂`. Establish `aQ : aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) Q = 0`. Establish `f1` using `aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q`. Establish `f2` using `aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `AlgHom.fst K.O B₁.A B₂.A _ = 0`. Rewrite using `[← f1]`. Express the relevant statement in the definitionally equal form `aeval B₁.g Q = 0`. Rewrite using `[hQQ, map_mul, a₁, zero_mul]`. Express the relevant statement in the definitionally equal form `AlgHom.snd K.O B₁.A B₂.A _ = 0`.

Rewrite using `[← f2]`. Express the relevant statement in the definitionally equal form `aeval B₂.g Q = 0`. Rewrite using `[hQQ, map_mul, a₂, mul_zero]`. Establish `hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) + algebraMap K.O (B₁.A × B₂.A) s) = algebraMap K.O (B₁.A × B₂.A) ε * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) s)` using `Prod.ext hY₁ hY₂`. Establish `adjP` using `mem_adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (s : K.O) ε Q hm aQ hQs s.isUnit hεu hodd hYp`.

Establish `st₁` using `stable_iff B₁.g Y₁ adj₁`. Establish `st₂` using `stable_iff B₂.g Y₂ adj₂`. Establish `stP` using `stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP`. Establish `sa₁` using `cayley_selfadj B₁ (s : K.O) ε Y₁ hu₁ hs hεc w₁ hw₁ hY₁`. Establish `sa₂` using `cayley_selfadj B₂ (s : K.O) ε Y₂ hu₂ hs hεc w₂ hw₂ hY₂`.

Establish `hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable`. Use `Orbit.prod_P B₁ B₂` as an intermediate fact. Rewrite `hsep` using `[← this]`. Conclude with `hsep`. Establish `hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable`.

Rewrite using `[← Orbit.prod_P]`. Use `separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂) (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP` as an intermediate fact. Conclude with `this`. Establish `hId` using `hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC`. Establish `hr : resultant B₁.P B₂.P ≠ 0` using `((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero`.

Establish `hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0` using `((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero`. Take `⟨M₁, l₁, s₁⟩` from `exists_stable_lat (E := K.E) B₁.g ⟨Q₁, hm₁, a₁⟩`. Take `⟨M₂, l₂, s₂⟩` from `exists_stable_lat (E := K.E) B₂.g ⟨Q₂, hm₂, a₂⟩`. Establish `hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P)` using `val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂`. Unfold `InvAlg.Identity at hId ⊢`.

Rewrite `hId` using `[kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂]`. Express the relevant statement in the definitionally equal form `(-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _`. Rewrite using `[hv]`. Conclude with `hId`.
-/
theorem identity_of_residually_unipotent : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K,
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by
  intro hL K hodd B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩
  have hinj := IsFractionRing.injective K.O K.E
  obtain ⟨ε, hεu, hεc⟩ := exists_eps K
  obtain ⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hm⟩ := lift_factor B₁ B₂ hsep Q hQ
  have hQs := eval_neg_isUnit hodd Q s hQr
  have hQs₁ : IsUnit (Q₁.eval (-(s : K.O))) := by
    rw [hQQ, eval_mul] at hQs; exact isUnit_of_mul_isUnit_left hQs
  have hQs₂ : IsUnit (Q₂.eval (-(s : K.O))) := by
    rw [hQQ, eval_mul] at hQs; exact isUnit_of_mul_isUnit_right hQs
  have hm₁ : Q₁.Monic := monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)
  have hm₂ : Q₂.Monic := monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)
  obtain ⟨w₁, -, hw₁⟩ := sub_inv_mem B₁.g (-(s : K.O)) Q₁ a₁ hQs₁
  obtain ⟨w₂, -, hw₂⟩ := sub_inv_mem B₂.g (-(s : K.O)) Q₂ a₂ hQs₂
  rw [map_neg, sub_neg_eq_add] at hw₁ hw₂
  set Y₁ := algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s) * w₁ with hY₁d
  set Y₂ := algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s) * w₂ with hY₂d
  have hY₁ : Y₁ * (B₁.g + algebraMap K.O B₁.A s) = algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s) := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A ε * (B₁.g - algebraMap K.O B₁.A s)) * hw₁
  have hY₂ : Y₂ * (B₂.g + algebraMap K.O B₂.A s) = algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s) := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A ε * (B₂.g - algebraMap K.O B₂.A s)) * hw₂
  have adj₁ := mem_adjoin_both B₁.g Y₁ (s : K.O) ε Q₁ hm₁ a₁ hQs₁ s.isUnit hεu hodd hY₁
  have adj₂ := mem_adjoin_both B₂.g Y₂ (s : K.O) ε Q₂ hm₂ a₂ hQs₂ s.isUnit hεu hodd hY₂
  have aQ : aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) Q = 0 := by
    have f1 := aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    have f2 := aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    refine Prod.ext ?_ ?_
    · change AlgHom.fst K.O B₁.A B₂.A _ = 0
      rw [← f1]; change aeval B₁.g Q = 0
      rw [hQQ, map_mul, a₁, zero_mul]
    · change AlgHom.snd K.O B₁.A B₂.A _ = 0
      rw [← f2]; change aeval B₂.g Q = 0
      rw [hQQ, map_mul, a₂, mul_zero]
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) + algebraMap K.O (B₁.A × B₂.A) s) =
      algebraMap K.O (B₁.A × B₂.A) ε * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) s) :=
    Prod.ext hY₁ hY₂
  have adjP := mem_adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (s : K.O) ε Q hm aQ hQs s.isUnit hεu hodd hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := cayley_selfadj B₁ (s : K.O) ε Y₁ hu₁ hs hεc w₁ hw₁ hY₁
  have sa₂ := cayley_selfadj B₂ (s : K.O) ε Y₂ hu₂ hs hεc w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g ⟨Q₁, hm₁, a₁⟩
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g ⟨Q₂, hm₂, a₂⟩
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CayleyCase
