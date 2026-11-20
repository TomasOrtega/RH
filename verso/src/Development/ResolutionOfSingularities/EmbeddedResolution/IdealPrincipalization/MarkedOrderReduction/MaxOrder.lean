import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Scheme.{u}}

/- English proof (authored)
A natural number in the set is bounded by the order at some point. That order is at most B, so the same inequality holds between the natural number and B. Thus B bounds the entire set.
-/
theorem bddAbove_setOf_le_orderAt (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) :
    BddAbove {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := by
  refine ⟨B, ?_⟩
  intro n hn
  obtain ⟨x, hx⟩ := hn
  have hnB : (n : ℕ∞) ≤ (B : ℕ∞) := le_trans hx (hB x)
  exact_mod_cast hnB

/- English proof (authored)
The finite bound makes the order at x a natural number, say m. The point x witnesses that m belongs to the set defining the maximum order, and the set is bounded. Its supremum is therefore at least m.
-/
theorem orderAt_le_maxOrder (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (x : ↥X) :
    orderAt N x ≤ ((maxOrder N : ℕ) : ℕ∞) := by
  have hxB : orderAt N x ≤ (B : ℕ∞) := hB x
  have hBtop : (B : ℕ∞) ≠ ⊤ := by simp
  have hne : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hxB
    exact hBtop (top_le_iff.mp hxB)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hmem : ∃ y : ↥X, (m : ℕ∞) ≤ orderAt N y := ⟨x, hm.le⟩
  have hle : m ≤ maxOrder N := le_csSup (bddAbove_setOf_le_orderAt N hB) hmem
  rw [← hm]
  exact_mod_cast hle

/- English proof (authored)
Since the scheme is nonempty, zero lies in the set of attained lower bounds for the orders. The given bound makes this a bounded set of natural numbers, so its supremum belongs to the set. Choose a point witnessing that membership. Its order is at least the supremum, while its finite order is itself in the set and is therefore at most the supremum.
-/
theorem exists_orderAt_eq_maxOrder [Nonempty ↥X] (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) :
    ∃ x : ↥X, orderAt N x = ((maxOrder N : ℕ) : ℕ∞) := by
  have hbdd : BddAbove {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := bddAbove_setOf_le_orderAt N hB
  have hnonempty : {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x}.Nonempty := by
    obtain ⟨x₀⟩ := ‹Nonempty ↥X›
    exact ⟨0, x₀, by simp⟩
  obtain ⟨x, hx⟩ := Nat.sSup_mem hnonempty hbdd
  have hdef : maxOrder N = sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := rfl
  refine ⟨x, ?_⟩
  rw [hdef]
  refine le_antisymm ?_ hx
  have hordle : orderAt N x ≤ (B : ℕ∞) := hB x
  have hne_top : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hordle
    simp at hordle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
  have hmemn : n ∈ {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := ⟨x, le_of_eq hn⟩
  have hle : n ≤ sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} := le_csSup hbdd hmemn
  calc orderAt N x = (n : ℕ∞) := hn.symm
    _ ≤ ((sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} : ℕ) : ℕ∞) := by exact_mod_cast hle

/- English proof (authored)
Choose a point attaining the maximum order, which exists by boundedness and nonemptiness. Its order is at least the threshold defining the locus, so it belongs to that locus.
-/
theorem orderAtLeastLocus_maxOrder_nonempty [Nonempty ↥X] (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) :
    (orderAtLeastLocus N (maxOrder N)).Nonempty := by
  obtain ⟨x, hx⟩ := exists_orderAt_eq_maxOrder N hB
  exact ⟨x, (mem_orderAtLeastLocus_iff N (maxOrder N) x).mpr hx.ge⟩

/- English proof (authored)
The order at the given point is at most the maximum order, and the maximum order is strictly below c. The asserted strict inequality follows.
-/
theorem orderAt_lt_of_maxOrder_lt (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) {c : ℕ} (hc : maxOrder N < c) (x : ↥X) :
    orderAt N x < (c : ℕ∞) := by
  have h1 : orderAt N x ≤ ((maxOrder N : ℕ) : ℕ∞) := orderAt_le_maxOrder N hB x
  have h2 : ((maxOrder N : ℕ) : ℕ∞) < (c : ℕ∞) := by exact_mod_cast hc
  exact lt_of_le_of_lt h1 h2

/- English proof (authored)
Any natural number in the set defining the maximum is at most the order of some point. If that number were at least c, the point would belong to the empty order locus at c. Therefore every number in the set is at most c−1. The supremum is at most c−1 as well, which is strictly below c by positivity.
-/
theorem maxOrder_lt_of_orderAtLeastLocus_eq_empty (N : X.IdealSheafData) {B : ℕ}
    (_hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) {c : ℕ} (hc : 1 ≤ c)
    (h : orderAtLeastLocus N c = ∅) :
    maxOrder N < c := by
  have key : maxOrder N ≤ c - 1 := by
    show sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x} ≤ c - 1
    refine csSup_le' ?_
    intro n hn
    obtain ⟨x, hx⟩ := hn
    have hlt : ¬ ((c : ℕ∞) ≤ orderAt N x) := by
      intro hcon
      have hmem : x ∈ orderAtLeastLocus N c := (mem_orderAtLeastLocus_iff N c x).mpr hcon
      rw [h] at hmem
      simp at hmem
    have hnc : n < c := by
      by_contra hcon
      have hcon' : c ≤ n := Nat.le_of_not_lt hcon
      have hcast : (c : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hcon'
      exact hlt (le_trans hcast hx)
    omega
  omega

end

section

variable {X : Scheme.{u}}

/- English proof (authored)
For each number in the set there is a point of S where the order is at least that number. The global bound B also holds at this point. Consequently B is an upper bound for these natural numbers.
-/
theorem bddAbove_setOf_le_orderAt_of_mem (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X) :
    BddAbove {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} := by
  refine ⟨B, ?_⟩
  intro n hn
  obtain ⟨x, _, hx⟩ := hn
  have hnB : (n : ℕ∞) ≤ (B : ℕ∞) := le_trans hx (hB x)
  exact_mod_cast hnB

/- English proof (authored)
By the finite bound, the order at x is a natural number. Since x lies in S, this number is a member of the bounded set used to define the maximum order on S. It is at most the supremum of that set.
-/
theorem orderAt_le_maxOrderOn (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X) {x : ↥X} (hx : x ∈ S) :
    orderAt N x ≤ ((maxOrderOn N S : ℕ) : ℕ∞) := by
  have hxB : orderAt N x ≤ (B : ℕ∞) := hB x
  have hne : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hxB
    simp at hxB
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hmem : m ∈ {n : ℕ | ∃ y ∈ S, (n : ℕ∞) ≤ orderAt N y} := ⟨x, hx, hm.le⟩
  have hle : m ≤ maxOrderOn N S := le_csSup (bddAbove_setOf_le_orderAt_of_mem N hB S) hmem
  rw [← hm]
  exact_mod_cast hle

/- English proof (authored)
Every number in the defining set is at most the order of a point of S and hence strictly less than c. Because c is positive and the numbers are natural, c−1 bounds the set. Its supremum is therefore less than c.
-/
theorem maxOrderOn_lt_of_forall_lt (N : X.IdealSheafData) {B : ℕ}
    (_hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X) {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ x ∈ S, orderAt N x < (c : ℕ∞)) :
    maxOrderOn N S < c := by
  have key : maxOrderOn N S ≤ c - 1 := by
    show sSup {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} ≤ c - 1
    refine csSup_le' ?_
    intro n hn
    obtain ⟨x, hxS, hx⟩ := hn
    have hlt : (n : ℕ∞) < (c : ℕ∞) := lt_of_le_of_lt hx (h x hxS)
    have hnc : n < c := by exact_mod_cast hlt
    omega
  omega

/- English proof (authored)
If the maximum on S is zero, the inequality with the maximum gives that every order on S is at most zero, hence is zero. Conversely, if every order on S is zero, then every natural number witnessed by a point of S is at most zero. The supremum is bounded by zero and, being a natural number, equals zero.
-/
theorem maxOrderOn_eq_zero_iff (N : X.IdealSheafData) {B : ℕ}
    (hB : ∀ x : ↥X, orderAt N x ≤ (B : ℕ∞)) (S : Set ↥X) :
    maxOrderOn N S = 0 ↔ ∀ x ∈ S, orderAt N x = 0 := by
  constructor
  · intro h x hx
    have h1 : orderAt N x ≤ ((maxOrderOn N S : ℕ) : ℕ∞) :=
      orderAt_le_maxOrderOn N hB S hx
    rw [h] at h1
    have h2 : orderAt N x ≤ (0 : ℕ∞) := by exact_mod_cast h1
    exact nonpos_iff_eq_zero.mp h2
  · intro h
    have hub : (0 : ℕ) ∈ upperBounds {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} := by
      intro n hn
      obtain ⟨x, hxS, hx⟩ := hn
      rw [h x hxS] at hx
      have hn0 : (n : ℕ∞) = 0 := nonpos_iff_eq_zero.mp hx
      have hn1 : n = 0 := by exact_mod_cast hn0
      omega
    have key : maxOrderOn N S ≤ 0 := by
      show sSup {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x} ≤ 0
      exact csSup_le' hub
    omega

end

section

variable {X : Scheme.{u}}

/- English proof (authored)
The order of the sum of two ideals is the minimum of their orders. A point has that minimum at least c exactly when both individual orders are at least c. This is membership in the intersection.
-/
theorem orderAtLeastLocus_sup (A J : X.IdealSheafData) (c : ℕ) :
    orderAtLeastLocus (A ⊔ J) c = orderAtLeastLocus A c ∩ orderAtLeastLocus J c := by
  ext x
  simp only [Set.mem_inter_iff, mem_orderAtLeastLocus_iff, orderAt_sup, le_min_iff]

/- English proof (authored)
The order of the sum is the minimum of the two summand orders. The order of each power is its exponent times the order of its base ideal. Substituting both power formulas gives the stated minimum.
-/
theorem orderAt_pow_sup_pow (k : Type u) [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (N I : X.IdealSheafData) (m s : ℕ) (x : ↥X) :
    orderAt (N ^ m ⊔ I ^ s) x
      = min ((m : ℕ∞) * orderAt N x) ((s : ℕ∞) * orderAt I x) := by
  rw [orderAt_sup, orderAt_pow k p, orderAt_pow k p]

/- English proof (authored)
The order locus of the sum is the intersection of the order loci of the two powers. The positive exponent m cancels from both sides of the first threshold inequality, leaving order at least s for N. For the other summand, the positive exponent s cancels and leaves order at least m for I.
-/
theorem orderAtLeastLocus_pow_sup_pow (k : Type u) [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (N I : X.IdealSheafData) {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    orderAtLeastLocus (N ^ m ⊔ I ^ s) (m * s) = orderAtLeastLocus N s ∩ orderAtLeastLocus I m := by
  rw [orderAtLeastLocus_sup, orderAtLeastLocus_pow_mul k p N hm s, mul_comm m s,
    orderAtLeastLocus_pow_mul k p I hs m]

/- English proof (authored)
Use the expression as the minimum of the two weighted orders. On the order locus of I at m, the bound on N makes the first weighted order at most ms. Off that locus, the order of I is below m, so the second weighted order is at most sm. In either case the minimum is at most ms.
-/
theorem orderAt_pow_sup_pow_le (k : Type u) [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (N I : X.IdealSheafData) (m s : ℕ)
    (h : ∀ x ∈ orderAtLeastLocus I m, orderAt N x ≤ (s : ℕ∞)) (x : ↥X) :
    orderAt (N ^ m ⊔ I ^ s) x ≤ ((m * s : ℕ) : ℕ∞) := by
  rw [orderAt_pow_sup_pow k p N I m s x]
  by_cases hx : x ∈ orderAtLeastLocus I m
  · refine le_trans (min_le_left _ _) ?_
    have h1 : orderAt N x ≤ (s : ℕ∞) := h x hx
    calc (m : ℕ∞) * orderAt N x ≤ (m : ℕ∞) * (s : ℕ∞) := by gcongr
      _ = ((m * s : ℕ) : ℕ∞) := by rw [Nat.cast_mul]
  · refine le_trans (min_le_right _ _) ?_
    have hle : orderAt I x ≤ (m : ℕ∞) :=
      le_of_lt (not_le.mp (fun hc => hx ((mem_orderAtLeastLocus_iff I m x).mpr hc)))
    calc (s : ℕ∞) * orderAt I x ≤ (s : ℕ∞) * (m : ℕ∞) := by gcongr
      _ = ((m * s : ℕ) : ℕ∞) := by rw [Nat.cast_mul]; exact mul_comm _ _

/- English proof (authored)
The locus of the sum of powers is the intersection of the order locus of I at m and that of N at s. If this intersection is empty, each point in the first locus has order for N less than s. Conversely, that strict bound at every point of the first locus leaves no point in both loci.
-/
theorem orderAtLeastLocus_pow_sup_pow_eq_empty_iff (k : Type u) [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (N I : X.IdealSheafData) {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    orderAtLeastLocus (N ^ m ⊔ I ^ s) (m * s) = ∅ ↔ ∀ x ∈ orderAtLeastLocus I m, orderAt N x < (s : ℕ∞) := by
  rw [orderAtLeastLocus_pow_sup_pow k p N I hm hs]
  constructor
  · intro h x hx
    by_contra hcon
    have hcon' : (s : ℕ∞) ≤ orderAt N x := not_lt.mp hcon
    have hmem : x ∈ orderAtLeastLocus N s ∩ orderAtLeastLocus I m :=
      ⟨(mem_orderAtLeastLocus_iff N s x).mpr hcon', hx⟩
    rw [h] at hmem
    exact hmem.elim
  · intro h
    ext x
    constructor
    · intro hx
      exact absurd ((mem_orderAtLeastLocus_iff N s x).mp hx.1) (not_le.mpr (h x hx.2))
    · intro hx
      exact hx.elim

end

section

variable {X Y : Scheme.{u}}

/- English proof (authored)
Smooth pullback makes the order locus of the pulled back ideal the inverse image of the original order locus. The image of this inverse image lies in the original locus.
-/
theorem image_orderAtLeastLocus_comap_subset (k : Type u) [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (N : X.IdealSheafData) (c : ℕ) :
    ⇑h.base '' orderAtLeastLocus (N.comap h) c ⊆ orderAtLeastLocus N c := by
  rw [orderAtLeastLocus_comap k p h N c]
  exact Set.image_preimage_subset _ _

end

end FunctorialResolution.EmbeddedResolution

end
