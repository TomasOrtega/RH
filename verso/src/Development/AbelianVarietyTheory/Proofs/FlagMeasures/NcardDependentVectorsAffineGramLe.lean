import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {B : Type} [CommRing B]

def depSet (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B) (a : B) :
    Set (Fin n → B) :=
  {y | (∀ i, ip c y (x i) = g i) ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i}

/- English proof (translation)
Introduce and unpack `y ⟨h, s, hs⟩`. Use `⟨h, fun i => b * s i, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, hs, Finset.smul_sum]`. Simplify using `[mul_smul]`.
-/
theorem depSet_subset_mul (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B)
    (a b : B) : depSet c x g a ⊆ depSet c x g (b * a) := by
  rintro y ⟨h, s, hs⟩
  refine ⟨h, fun i => b * s i, ?_⟩
  rw [mul_smul, hs, Finset.smul_sum]
  simp [mul_smul]

/- English proof (translation)
Take `⟨θ, e, -, he, hce⟩` from `exists_trace_one c hc hω`. Use `isUnit_of_mul_isUnit_left (y := e) (hf _ ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hu, hce]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Conclude with `h0 (he.mul_left_eq_zero.1 h)`.
-/
theorem dep_isUnit_of_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {u : B} (hu : c u = -u) (h0 : u ≠ 0) : IsUnit u := by
  obtain ⟨θ, e, -, he, hce⟩ := exists_trace_one c hc hω
  refine isUnit_of_mul_isUnit_left (y := e) (hf _ ?_ ?_)
  · rw [map_mul, hu, hce]; ring
  · intro h
    exact h0 (he.mul_left_eq_zero.1 h)

/- English proof (translation)
Distinguish the cases in `hu : IsUnit a`. Conclude with `Or.inl hu.exists_left_inv`. Use `right`. Establish `h1 : a * c a = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hu (isUnit_of_mul_isUnit_left (hf _ (by rw [map_mul, hc, mul_comm]) h))`. Establish `h2 : a + c a ≠ 0` using `fun h => hu (dep_isUnit_of_skew c hc hω hf (by linear_combination h) h0)`. Establish `h3 : c (a + c a) = a + c a` using `by rw [map_add, hc, add_comm]`. Take `⟨b, hb⟩` from `(hf _ h3 h2).exists_left_inv`. Establish `hb' : c b * (a + c a) = 1`.

Use `congrArg c hb` as an intermediate fact. Rewrite `this` using `[map_mul, h3, map_one]`. Then use the resulting hypothesis. Establish `hcb : c b = b` using `by linear_combination b * hb' - c b * hb`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hcb]`.

Take the linear combination `hb`. Rewrite using `[map_mul, hcb]`. Take the linear combination `b * b * h1`.
-/
theorem dep_unit_or_idem (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {a : B} (h0 : a ≠ 0) :
    (∃ b, b * a = 1) ∨ ∃ b, (b * a) + c (b * a) = 1 ∧ (b * a) * c (b * a) = 0 := by
  by_cases hu : IsUnit a
  · exact Or.inl hu.exists_left_inv
  right
  have h1 : a * c a = 0 := by
    by_contra h
    exact hu (isUnit_of_mul_isUnit_left (hf _ (by rw [map_mul, hc, mul_comm]) h))
  have h2 : a + c a ≠ 0 := fun h =>
    hu (dep_isUnit_of_skew c hc hω hf (by linear_combination h) h0)
  have h3 : c (a + c a) = a + c a := by rw [map_add, hc, add_comm]
  obtain ⟨b, hb⟩ := (hf _ h3 h2).exists_left_inv
  have hb' : c b * (a + c a) = 1 := by
    have := congrArg c hb
    rwa [map_mul, h3, map_one] at this
  have hcb : c b = b := by linear_combination b * hb' - c b * hb
  refine ⟨b, ?_, ?_⟩
  · rw [map_mul, hcb]; linear_combination hb
  · rw [map_mul, hcb]; linear_combination b * b * h1

/- English proof (translation)
Distinguish the cases in `h : ε' = ε`. Conclude with `Or.inl h`. Use `right`. Establish `hu : IsUnit (ε' - ε)` using `dep_isUnit_of_skew c hc hω hf (by rw [map_sub]; linear_combination h1' - h1) (sub_ne_zero.2 h)`. Establish `: (ε' - ε) * (ε' - c ε) = 0`.

Take the linear combination `h2 - h2' + ε' * h1' - ε' * h1`. Conclude with `sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)`.
-/
theorem dep_idem_eq (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {ε ε' : B} (h1 : ε + c ε = 1) (h2 : ε * c ε = 0)
    (h1' : ε' + c ε' = 1) (h2' : ε' * c ε' = 0) : ε' = ε ∨ ε' = c ε := by
  by_cases h : ε' = ε
  · exact Or.inl h
  right
  have hu : IsUnit (ε' - ε) := dep_isUnit_of_skew c hc hω hf
    (by rw [map_sub]; linear_combination h1' - h1) (sub_ne_zero.2 h)
  have : (ε' - ε) * (ε' - c ε) = 0 := by
    linear_combination h2 - h2' + ε' * h1' - ε' * h1
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

/- English proof (translation)
Establish `hw : c ε • z + ∑ j, (c ε * ρ j) • d j = c ε • (z + ∑ j, ρ j • d j)`. Simplify using `only [smul_add, Finset.smul_sum, mul_smul]`. Establish `hw0 : c ε • z + ∑ j, (c ε * ρ j) • d j = 0`. Use function extensionality and compare the values at `l`. Use `hB l` as an intermediate fact.

Rewrite `this`, the goal using `[hw]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Pi.zero_apply] at this ⊢`. Use `set u := (z + ∑ j, ρ j • d j) l`. Take the linear combination `c ε * this - c u * h2 + u * h2 - c ε * u * h1`. Establish `hd' : ∀ a b, ip c (d b) (x a) = if a = b then 1 else 0` using `fun a b => by`.

Apply the tactic sequence `rw [← cj_ip c hc, hd]; split_ifs <;> simp`. Establish `hη : ∀ i, c ε * ρ i = 0` using `fun i => by`. Use `congrArg (fun v => ip c v (x i)) hw0` as an intermediate fact. Simplify `this` using `[ip_add_left, ip_sum_left, ip_smul_left, hd', hz, ip_zero_left]`. Establish `hε : ∀ i, ε * ρ i = 0` using `fun i => by`.

Use `hA i` as an intermediate fact. Rewrite `this` using `[map_mul]`. Take the linear combination `ε * this - c (ip c z (d i)) * h2 + ρ i * h2 - ε * ρ i * h1`. Establish `hs0 : ∀ i, s i = 0` using `fun i => by`. Establish `h3` using `hA i`.

Rewrite `h3` using `[hε, add_zero]`. Establish `h4` using `congrArg c h3`. Rewrite `h4` using `[hc, map_zero]`. Use `congrArg (fun v => ip c v (d i)) hs` as an intermediate fact. Simplify `this.symm` using `[ip_sum_left, ip_smul_left, hd, h4]`.

Use `⟨?_, funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [hη, zero_smul, Finset.sum_const_zero, add_zero] at hw0`. Simplify using `only [hs0, zero_smul, Finset.sum_const_zero] at hs`. Rewrite using `[← one_smul B z, ← h1, add_smul, hs, hw0, add_zero]`. Use `hε i` as an intermediate fact.

Use `hη i` as an intermediate fact. Simplify using `only [Pi.zero_apply]`. Take the linear combination `hε i + hη i - ρ i * h1`.
-/
theorem dep_kernel (c : B →+* B) (hc : ∀ u, c (c u) = u) {k n : ℕ} (x d : Fin k → Fin n → B)
    (hd : ∀ a b, ip c (x a) (d b) = if a = b then 1 else 0) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) (z : Fin n → B) (ρ s : Fin k → B) (hz : ∀ i, ip c z (x i) = 0)
    (hs : ε • z = ∑ i, s i • x i) (hA : ∀ i, c (ε * ip c z (d i)) + ε * ρ i = 0)
    (hB : ∀ l, (c ε • z + ∑ j, (c ε * ρ j) • d j) l +
      c ((c ε • z + ∑ j, (c ε * ρ j) • d j) l) = 0) : z = 0 ∧ ρ = 0 := by
  have hw : c ε • z + ∑ j, (c ε * ρ j) • d j = c ε • (z + ∑ j, ρ j • d j) := by
    simp only [smul_add, Finset.smul_sum, mul_smul]
  have hw0 : c ε • z + ∑ j, (c ε * ρ j) • d j = 0 := by
    funext l
    have := hB l
    rw [hw] at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Pi.zero_apply] at this ⊢
    set u := (z + ∑ j, ρ j • d j) l
    linear_combination c ε * this - c u * h2 + u * h2 - c ε * u * h1
  have hd' : ∀ a b, ip c (d b) (x a) = if a = b then 1 else 0 := fun a b => by
    rw [← cj_ip c hc, hd]; split_ifs <;> simp
  have hη : ∀ i, c ε * ρ i = 0 := fun i => by
    have := congrArg (fun v => ip c v (x i)) hw0
    simpa [ip_add_left, ip_sum_left, ip_smul_left, hd', hz, ip_zero_left] using this
  have hε : ∀ i, ε * ρ i = 0 := fun i => by
    have := hA i
    rw [map_mul] at this
    linear_combination ε * this - c (ip c z (d i)) * h2 + ρ i * h2 - ε * ρ i * h1
  have hs0 : ∀ i, s i = 0 := fun i => by
    have h3 := hA i
    rw [hε, add_zero] at h3
    have h4 := congrArg c h3
    rw [hc, map_zero] at h4
    have := congrArg (fun v => ip c v (d i)) hs
    simpa [ip_sum_left, ip_smul_left, hd, h4] using this.symm
  refine ⟨?_, funext fun i => ?_⟩
  · simp only [hη, zero_smul, Finset.sum_const_zero, add_zero] at hw0
    simp only [hs0, zero_smul, Finset.sum_const_zero] at hs
    rw [← one_smul B z, ← h1, add_smul, hs, hw0, add_zero]
  · have := hε i
    have := hη i
    simp only [Pi.zero_apply]
    linear_combination hε i + hη i - ρ i * h1

/- English proof (translation)
Take `⟨d, hd⟩` from `hx`. Establish `hK : Nat.card {t : B // c t = t} = q`. Use `(card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc (fun a y => by simp)).1` as an intermediate fact. Rewrite `this` using `[Nat.card_eq_fintype_card (α := B), hq]`. Conclude with `Nat.pow_left_injective two_ne_zero this`.

Set `F : depSet c x g ε × (Fin k → B) → (Fin k → B) × (Fin n → {t : B // c t = t})` to `fun p => (fun i => c (ε * ip c p.1.1 (d i)) + ε * p.2 i, fun l => ⟨(c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l + c ((c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l), by rw [map_add, hc, add_comm]⟩)`. Establish `hF : Function.Injective F`. Introduce and unpack `⟨⟨y, hy, s, hs⟩, r⟩ ⟨⟨y', hy', s', hs'⟩, r'⟩ h`. Take `⟨hA, hB⟩` from `Prod.ext_iff.1 h`. Establish `key` using `dep_kernel c hc x d hd h1 h2 (y - y') (r - r') (s - s') (fun i => by rw [ip_sub_left, hy, hy', sub_self]) (by simp only [smul_sub, hs, hs', Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]) (fun i => by`.

Use `congrFun hA i` as an intermediate fact. Simplify using `only [F, map_mul] at this`. Simplify using `only [ip_sub_left, map_mul, map_sub, Pi.sub_apply]`. Take the linear combination `this)`. Use the proof step `(fun l => by`.

Use `congrArg Subtype.val (congrFun hB l)` as an intermediate fact. Simplify using `only [F, Pi.add_apply, map_add] at this`. Simplify using `only [smul_sub, mul_sub, sub_smul, Finset.sum_sub_distrib, Pi.add_apply, Pi.sub_apply, map_add, map_sub]`. Take the linear combination `this)`. Conclude with `Prod.ext (Subtype.ext (sub_eq_zero.1 key.1)) (sub_eq_zero.1 key.2)`.

Establish `h3` using `Nat.card_le_card_of_injective F hF`. Rewrite `h3` using `[Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun (α := Fin n), hK, mul_comm]`. Establish `h4 : 0 < Nat.card (Fin k → B)` using `Nat.card_pos`. Simplify using `using Nat.le_of_mul_le_mul_left h3 h4`.
-/
theorem ncard_depSet_idem_le [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B}
    (hω : IsUnit (ω - c ω)) {q : ℕ} (hq : Fintype.card B = q ^ 2) {k n : ℕ}
    (x : Fin k → Fin n → B) (hx : Prim c x) (g : Fin k → B) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) : (depSet c x g ε).ncard ≤ q ^ n := by
  obtain ⟨d, hd⟩ := hx
  have hK : Nat.card {t : B // c t = t} = q := by
    have := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc (fun a y => by simp)).1
    rw [Nat.card_eq_fintype_card (α := B), hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  let F : depSet c x g ε × (Fin k → B) → (Fin k → B) × (Fin n → {t : B // c t = t}) :=
    fun p => (fun i => c (ε * ip c p.1.1 (d i)) + ε * p.2 i,
      fun l => ⟨(c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l +
        c ((c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l), by rw [map_add, hc, add_comm]⟩)
  have hF : Function.Injective F := by
    rintro ⟨⟨y, hy, s, hs⟩, r⟩ ⟨⟨y', hy', s', hs'⟩, r'⟩ h
    obtain ⟨hA, hB⟩ := Prod.ext_iff.1 h
    have key := dep_kernel c hc x d hd h1 h2 (y - y') (r - r') (s - s')
      (fun i => by rw [ip_sub_left, hy, hy', sub_self])
      (by simp only [smul_sub, hs, hs', Pi.sub_apply, sub_smul, Finset.sum_sub_distrib])
      (fun i => by
        have := congrFun hA i
        simp only [F, map_mul] at this
        simp only [ip_sub_left, map_mul, map_sub, Pi.sub_apply]
        linear_combination this)
      (fun l => by
        have := congrArg Subtype.val (congrFun hB l)
        simp only [F, Pi.add_apply, map_add] at this
        simp only [smul_sub, mul_sub, sub_smul, Finset.sum_sub_distrib, Pi.add_apply,
          Pi.sub_apply, map_add, map_sub]
        linear_combination this)
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 key.1)) (sub_eq_zero.1 key.2)
  have h3 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun (α := Fin n), hK,
    mul_comm] at h3
  have h4 : 0 < Nat.card (Fin k → B) := Nat.card_pos
  simpa using Nat.le_of_mul_le_mul_left h3 h4

/- English proof (translation)
Introduce `B _ _ c hc ω hω hf q hq2 hq k n hkn x hx g`. Distinguish the cases in `hex : ∃ ε : B, ε + c ε = 1 ∧ ε * c ε = 0`. Take `⟨ε, h1, h2⟩` from `hex`. Establish `hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆ depSet c x g ε ∪ depSet c x g (c ε)`. Introduce and unpack `y ⟨hy, a, ha, hs⟩`.

Establish `hy' : y ∈ depSet c x g a` using `⟨hy, hs⟩`. Break down `dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb1, hb2⟩` into its components or cases. Use `left`. Use `depSet_subset_mul c x g a (ε * b) hy'` as an intermediate fact. Rewrite `this` using `[mul_assoc, hb, mul_one]`. Then use the resulting hypothesis.

Use `depSet_subset_mul c x g a b hy'` as an intermediate fact. Break down `dep_idem_eq c hc hω hf h1 h2 hb1 hb2 with h | h` into its components or cases. Use `left`. Rewrite `this` using `[h]`. Then use the resulting hypothesis. Use `right`.

Rewrite `this` using `[h]`. Then use the resulting hypothesis. Establish `hA` using `ncard_depSet_idem_le c hc hω hq x hx g h1 h2`. Establish `hB` using `ncard_depSet_idem_le c hc hω hq x hx g (ε := c ε) (by rw [hc, add_comm, h1]) (by rw [hc, mul_comm, h2])`. Use `(Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆ (fun s : Fin k → B => ∑ i, s i • x i) '' Set.univ`. Introduce and unpack `y ⟨hy, a, ha, hs⟩`. Establish `hy' : y ∈ depSet c x g a` using `⟨hy, hs⟩`. Break down `dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb⟩` into its components or cases. Take `⟨-, s, hs⟩` from `depSet_subset_mul c x g a b hy'`.

Rewrite `hs` using `[hb, one_smul]`. Conclude with `⟨s, trivial, hs.symm⟩`. Conclude with `absurd ⟨_, hb⟩ hex`. Establish `h1` using `(Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))`. Rewrite `h1` using `[Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, hq, Fintype.card_fin, ← pow_mul]`.

Establish `h2 : q ^ (2 * k) ≤ q ^ n` using `Nat.pow_le_pow_right (by omega) hkn`. Use linear arithmetic over natural numbers and integers.
-/
theorem ncard_dependent_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) →
    ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n →
    ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B),
    Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
      ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  intro B _ _ c hc ω hω hf q hq2 hq k n hkn x hx g
  by_cases hex : ∃ ε : B, ε + c ε = 1 ∧ ε * c ε = 0
  · obtain ⟨ε, h1, h2⟩ := hex
    have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        depSet c x g ε ∪ depSet c x g (c ε) := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb1, hb2⟩
      · left
        have := depSet_subset_mul c x g a (ε * b) hy'
        rwa [mul_assoc, hb, mul_one] at this
      · have := depSet_subset_mul c x g a b hy'
        rcases dep_idem_eq c hc hω hf h1 h2 hb1 hb2 with h | h
        · left; rwa [h] at this
        · right; rwa [h] at this
    have hA := ncard_depSet_idem_le c hc hω hq x hx g h1 h2
    have hB := ncard_depSet_idem_le c hc hω hq x hx g (ε := c ε) (by rw [hc, add_comm, h1])
      (by rw [hc, mul_comm, h2])
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    omega
  · have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        (fun s : Fin k → B => ∑ i, s i • x i) '' Set.univ := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb⟩
      · obtain ⟨-, s, hs⟩ := depSet_subset_mul c x g a b hy'
        rw [hb, one_smul] at hs
        exact ⟨s, trivial, hs.symm⟩
      · exact absurd ⟨_, hb⟩ hex
    have h1 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, hq, Fintype.card_fin,
      ← pow_mul] at h1
    have h2 : q ^ (2 * k) ≤ q ^ n := Nat.pow_le_pow_right (by omega) hkn
    omega

end GlobalTheory.GramCount
