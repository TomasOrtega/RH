import Formalism.SharpRestriction.GrowthBounds.RootWeights.FockLatticeFiniteSpanning

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def dvrOrderNat (x : O) : ℕ := (IsDiscreteValuationRing.addVal O x).toNat

/- English proof (translation)
Unfold `dvrOrderNat`. Use `first`. Consider the case `exact ENat.coe_toNat (by rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff])`. Consider the case `exact ENat.coe_toNat ((AddValuation.top_iff _).not.mpr ha)`.
-/
theorem dvr_order_coe_addVal {a : O} (ha : a ≠ 0) : ((dvrOrderNat a : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O a := by
  unfold dvrOrderNat
  first
    | exact ENat.coe_toNat (by rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff])
    | exact ENat.coe_toNat ((AddValuation.top_iff _).not.mpr ha)

/- English proof (translation)
Establish `h1` using `dvr_order_coe_addVal (mul_ne_zero ha hb)`. Rewrite `h1` using `[(IsDiscreteValuationRing.addVal O).map_mul, ← dvr_order_coe_addVal ha, ← dvr_order_coe_addVal hb]`. Conclude with `h1` after adjusting the coercions.
-/
theorem dvr_order_mul {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) : dvrOrderNat (a * b) = dvrOrderNat a + dvrOrderNat b := by
  have h1 := dvr_order_coe_addVal (mul_ne_zero ha hb)
  rw [(IsDiscreteValuationRing.addVal O).map_mul, ← dvr_order_coe_addVal ha, ← dvr_order_coe_addVal hb] at h1
  exact_mod_cast h1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Unfold `dvrOrderNat`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Rewrite using `[pow_succ, dvr_order_mul (pow_ne_zero n ha) ha, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dvr_order_pow {a : O} (ha : a ≠ 0) (k : ℕ) : dvrOrderNat (a ^ k) = k * dvrOrderNat a := by
  induction k with
  | zero =>
    unfold dvrOrderNat
    simp
  | succ n ih =>
    rw [pow_succ, dvr_order_mul (pow_ne_zero n ha) ha, ih]
    ring

/- English proof (translation)
Establish `h` using `(IsDiscreteValuationRing.addVal O).map_add a b`. Rewrite `h` using `[← dvr_order_coe_addVal ha, ← dvr_order_coe_addVal hb, ← dvr_order_coe_addVal hab]`. Break down `le_total (dvrOrderNat a) (dvrOrderNat b) with hle | hle` into its components or cases. Rewrite `h` using `[min_eq_left (ENat.coe_le_coe.mpr hle)]`. Rewrite using `[min_eq_left hle]`.

Conclude with `ENat.coe_le_coe.mp h`. Rewrite `h` using `[min_eq_right (ENat.coe_le_coe.mpr hle)]`. Rewrite using `[min_eq_right hle]`. Conclude with `ENat.coe_le_coe.mp h`.
-/
theorem dvr_order_add_ge_min {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (dvrOrderNat a) (dvrOrderNat b) ≤ dvrOrderNat (a + b) := by
  have h := (IsDiscreteValuationRing.addVal O).map_add a b
  rw [← dvr_order_coe_addVal ha, ← dvr_order_coe_addVal hb, ← dvr_order_coe_addVal hab] at h
  rcases le_total (dvrOrderNat a) (dvrOrderNat b) with hle | hle
  · rw [min_eq_left (ENat.coe_le_coe.mpr hle)] at h
    rw [min_eq_left hle]
    exact ENat.coe_le_coe.mp h
  · rw [min_eq_right (ENat.coe_le_coe.mpr hle)] at h
    rw [min_eq_right hle]
    exact ENat.coe_le_coe.mp h

/- English proof (translation)
Unfold `dvrOrderNat`. Rewrite using `[(IsDiscreteValuationRing.addVal O).map_neg]`.
-/
theorem dvr_order_neg (a : O) : dvrOrderNat (-a) = dvrOrderNat a := by
  unfold dvrOrderNat
  rw [(IsDiscreteValuationRing.addVal O).map_neg]

/- English proof (translation)
Unfold `dvrOrderNat`. Use `first`. Consider the case `rw [IsDiscreteValuationRing.addVal_eq_zero_iff.2 ha]`. Both sides reduce to the same expression. Consider the case `(obtain ⟨u, rfl⟩ := ha; simp [IsDiscreteValuationRing.addVal_eq_zero_of_unit])`.
-/
theorem dvr_order_unit_eq_zero {a : O} (ha : IsUnit a) : dvrOrderNat a = 0 := by
  unfold dvrOrderNat
  first
    | rw [IsDiscreteValuationRing.addVal_eq_zero_iff.2 ha]; rfl
    | (obtain ⟨u, rfl⟩ := ha; simp [IsDiscreteValuationRing.addVal_eq_zero_of_unit])

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective O (KK O)`. Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zero_mul]`. Conclude with `ha (hinj (by rw [← h, map_zero]))`.

Unfold `ordW`. Simplify using `only [if_neg hx]`. Use `generalize_proofs hp`. Establish `hs` using `Classical.choose_spec hp`. Generalize the expression as in `Classical.choose hp = ab at hs ⊢`.

Establish `hb2 : (ab.2 : O) ≠ 0` using `nonZeroDivisors.ne_zero ab.2.2`. Establish `key : a * (ab.2 : O) = ab.1 * b` using `hinj (by rw [map_mul, map_mul, ← h, ← hs]; ring)`. Establish `h1 : ab.1 ≠ 0`. Introduce `h0`. Rewrite `key` using `[h0, zero_mul]`.

Conclude with `mul_ne_zero ha hb2 key`. Establish `e` using `dvr_order_mul ha hb2`. Rewrite `e` using `[key, dvr_order_mul h1 hb]`. Unfold `dvrOrderNat at e ⊢`. Conclude with `congrArg _ (by omega)`.
-/
theorem ord_eq_order_sub_of_fraction (x : KK O) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x * algebraMap O (KK O) b = algebraMap O (KK O) a) :
    ordW x = (((dvrOrderNat a : ℤ) - (dvrOrderNat b : ℤ) : ℤ) : WithTop ℤ) := by
  have hinj := IsFractionRing.injective O (KK O)
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact ha (hinj (by rw [← h, map_zero]))
  unfold ordW
  simp only [if_neg hx]
  generalize_proofs hp
  have hs := Classical.choose_spec hp
  generalize Classical.choose hp = ab at hs ⊢
  have hb2 : (ab.2 : O) ≠ 0 := nonZeroDivisors.ne_zero ab.2.2
  have key : a * (ab.2 : O) = ab.1 * b := hinj (by rw [map_mul, map_mul, ← h, ← hs]; ring)
  have h1 : ab.1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact mul_ne_zero ha hb2 key
  have e := dvr_order_mul ha hb2
  rw [key, dvr_order_mul h1 hb] at e
  unfold dvrOrderNat at e ⊢
  exact congrArg _ (by omega)

/- English proof (translation)
Take `⟨w, hw, hpm, hp0, _⟩` from `S`. Unfold `ramE`. Establish `hnu : ¬ IsUnit (p : O)` using `(IsLocalRing.mem_maximalIdeal _).1 hpm`. Establish `h0 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0` using `fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)`. Establish `htop : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤`.

Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Introduce `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← ENat.coe_toNat htop, h]`. Simplify using the standard rewrite rules.
-/
theorem ramification_index_ne_zero {p : ℕ} (S : UniformizedDVR p O) : ramE p O ≠ 0 := by
  obtain ⟨w, hw, hpm, hp0, _⟩ := S
  unfold ramE
  have hnu : ¬ IsUnit (p : O) := (IsLocalRing.mem_maximalIdeal _).1 hpm
  have h0 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0 :=
    fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  have htop : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  intro h
  apply h0
  rw [← ENat.coe_toNat htop, h]
  simp

/- English proof (translation)
Unfold `vK ordW`. Simplify using the standard rewrite rules.
-/
theorem valuation_zero_alt (p : ℕ) : vK p (0 : KK O) = ⊤ := by
  unfold vK ordW
  simp

/- English proof (translation)
Unfold `vK`. Rewrite using `[ord_eq_order_sub_of_fraction x a b ha hb h, WithTop.map_coe]`.
-/
theorem valuation_eq_of_fraction (p : ℕ) (x : KK O) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x * algebraMap O (KK O) b = algebraMap O (KK O) a) :
    vK p x = (((((dvrOrderNat a : ℤ) - (dvrOrderNat b : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  unfold vK
  rw [ord_eq_order_sub_of_fraction x a b ha hb h, WithTop.map_coe]

/- English proof (translation)
Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors O) x`. Establish `hb0 : (b : O) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Use `⟨a, b, ?_, hb0, hab⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hab` using `[map_zero]`.

Establish `hb' : algebraMap O (KK O) b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hb0`. Conclude with `hx ((mul_eq_zero.1 hab).resolve_right hb')`.
-/
theorem exists_fraction_of_ne_zero (x : KK O) (hx : x ≠ 0) : ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
    x * algebraMap O (KK O) b = algebraMap O (KK O) a := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  refine ⟨a, b, ?_, hb0, hab⟩
  rintro rfl
  rw [map_zero] at hab
  have hb' : algebraMap O (KK O) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hb0
  exact hx ((mul_eq_zero.1 hab).resolve_right hb')

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, zero_mul, valuation_zero_alt, top_add]`. Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, mul_zero, valuation_zero_alt, add_top]`. Take `⟨a, b, ha, hb, hab⟩` from `exists_fraction_of_ne_zero x hx`.

Take `⟨c, d, hc, hd, hcd⟩` from `exists_fraction_of_ne_zero y hy`. Establish `hxy : x * y * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (a * c)`. Rewrite using `[map_mul, map_mul, ← hab, ← hcd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[valuation_eq_of_fraction p x a b ha hb hab, valuation_eq_of_fraction p y c d hc hd hcd, valuation_eq_of_fraction p (x * y) (a * c) (b * d) (mul_ne_zero ha hc) (mul_ne_zero hb hd) hxy, dvr_order_mul ha hc, dvr_order_mul hb hd, ← WithTop.coe_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valuation_mul_alt (p : ℕ) (x y : KK O) : vK p (x * y) = vK p x + vK p y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, valuation_zero_alt, top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, valuation_zero_alt, add_top]
  obtain ⟨a, b, ha, hb, hab⟩ := exists_fraction_of_ne_zero x hx
  obtain ⟨c, d, hc, hd, hcd⟩ := exists_fraction_of_ne_zero y hy
  have hxy : x * y * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (a * c) := by
    rw [map_mul, map_mul, ← hab, ← hcd]; ring
  rw [valuation_eq_of_fraction p x a b ha hb hab, valuation_eq_of_fraction p y c d hc hd hcd,
    valuation_eq_of_fraction p (x * y) (a * c) (b * d) (mul_ne_zero ha hc) (mul_ne_zero hb hd) hxy,
    dvr_order_mul ha hc, dvr_order_mul hb hd, ← WithTop.coe_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, neg_zero]`. Take `⟨a, b, ha, hb, hab⟩` from `exists_fraction_of_ne_zero x hx`. Rewrite using `[valuation_eq_of_fraction p x a b ha hb hab, valuation_eq_of_fraction p (-x) (-a) b (neg_ne_zero.2 ha) hb (by rw [map_neg, ← hab]; ring), dvr_order_neg]`.
-/
theorem valuation_neg (p : ℕ) (x : KK O) : vK p (-x) = vK p x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  obtain ⟨a, b, ha, hb, hab⟩ := exists_fraction_of_ne_zero x hx
  rw [valuation_eq_of_fraction p x a b ha hb hab,
    valuation_eq_of_fraction p (-x) (-a) b (neg_ne_zero.2 ha) hb (by rw [map_neg, ← hab]; ring), dvr_order_neg]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, zero_add, valuation_zero_alt]`. Conclude with `min_le_right _ _`. Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, add_zero, valuation_zero_alt]`.

Conclude with `min_le_left _ _`. Distinguish the cases in `hxy : x + y = 0`. Rewrite using `[hxy, valuation_zero_alt]`. Conclude with `le_top`. Take `⟨a, b, ha, hb, hab⟩` from `exists_fraction_of_ne_zero x hx`.

Take `⟨c, d, hc, hd, hcd⟩` from `exists_fraction_of_ne_zero y hy`. Establish `hinj` using `IsFractionRing.injective O (KK O)`. Establish `hbd : b * d ≠ 0` using `mul_ne_zero hb hd`. Establish `hbd' : algebraMap O (KK O) (b * d) ≠ 0` using `(map_ne_zero_iff _ hinj).2 hbd`. Establish `e1 : x * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (a * d)`.

Rewrite using `[map_mul, map_mul, ← hab]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : y * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (c * b)`. Rewrite using `[map_mul, map_mul, ← hcd]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e3 : (x + y) * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (a * d + c * b)`. Rewrite using `[map_add, ← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs0 : a * d + c * b ≠ 0`. Introduce `h0`.

Rewrite `e3` using `[h0, map_zero]`. Conclude with `hxy ((mul_eq_zero.1 e3).resolve_right hbd')`. Establish `hA` using `mul_ne_zero ha hd`. Establish `hC` using `mul_ne_zero hc hb`. Establish `hS` using `dvr_order_add_ge_min hA hC hs0`.

Rewrite using `[valuation_eq_of_fraction p x _ _ hA hbd e1, valuation_eq_of_fraction p y _ _ hC hbd e2, valuation_eq_of_fraction p (x + y) _ _ hs0 hbd e3]`. Establish `hmono : ∀ m : ℕ, m ≤ dvrOrderNat (a * d + c * b) → (((((m : ℤ) - (dvrOrderNat (b * d) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) ≤ (((((dvrOrderNat (a * d + c * b) : ℤ) - (dvrOrderNat (b * d) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ)`. Introduce `m hm`. Rewrite using `[WithTop.coe_le_coe]`. Apply `div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)` to reduce the goal to its premises.

Conclude with `Int.cast_le.mpr (by omega)`. Break down `le_total (dvrOrderNat (a * d)) (dvrOrderNat (c * b)) with hle | hle` into its components or cases. Rewrite `hS` using `[min_eq_left hle]`. Conclude with `min_le_of_left_le (hmono _ hS)`. Rewrite `hS` using `[min_eq_right hle]`.

Conclude with `min_le_of_right_le (hmono _ hS)`.
-/
theorem valuation_add_ge_min (p : ℕ) (x y : KK O) : min (vK p x) (vK p y) ≤ vK p (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add, valuation_zero_alt]
    exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero, valuation_zero_alt]
    exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, valuation_zero_alt]
    exact le_top
  obtain ⟨a, b, ha, hb, hab⟩ := exists_fraction_of_ne_zero x hx
  obtain ⟨c, d, hc, hd, hcd⟩ := exists_fraction_of_ne_zero y hy
  have hinj := IsFractionRing.injective O (KK O)
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  have hbd' : algebraMap O (KK O) (b * d) ≠ 0 := (map_ne_zero_iff _ hinj).2 hbd
  have e1 : x * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (a * d) := by
    rw [map_mul, map_mul, ← hab]; ring
  have e2 : y * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (c * b) := by
    rw [map_mul, map_mul, ← hcd]; ring
  have e3 : (x + y) * algebraMap O (KK O) (b * d) = algebraMap O (KK O) (a * d + c * b) := by
    rw [map_add, ← e1, ← e2]; ring
  have hs0 : a * d + c * b ≠ 0 := by
    intro h0
    rw [h0, map_zero] at e3
    exact hxy ((mul_eq_zero.1 e3).resolve_right hbd')
  have hA := mul_ne_zero ha hd
  have hC := mul_ne_zero hc hb
  have hS := dvr_order_add_ge_min hA hC hs0
  rw [valuation_eq_of_fraction p x _ _ hA hbd e1, valuation_eq_of_fraction p y _ _ hC hbd e2, valuation_eq_of_fraction p (x + y) _ _ hs0 hbd e3]
  have hmono : ∀ m : ℕ, m ≤ dvrOrderNat (a * d + c * b) →
      (((((m : ℤ) - (dvrOrderNat (b * d) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) ≤
      (((((dvrOrderNat (a * d + c * b) : ℤ) - (dvrOrderNat (b * d) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
    intro m hm
    rw [WithTop.coe_le_coe]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Int.cast_le.mpr (by omega)
  rcases le_total (dvrOrderNat (a * d)) (dvrOrderNat (c * b)) with hle | hle
  · rw [min_eq_left hle] at hS
    exact min_le_of_left_le (hmono _ hS)
  · rw [min_eq_right hle] at hS
    exact min_le_of_right_le (hmono _ hS)

/- English proof (translation)
Rewrite using `[valuation_eq_of_fraction p _ o 1 ho one_ne_zero (by rw [map_one, mul_one]), dvr_order_unit_eq_zero isUnit_one]`. Use `congr 1`. Apply the tactic sequence `all_goals push_cast`. Apply the tactic sequence `all_goals ring`.
-/
theorem valuation_algebraMap_eq_alt (p : ℕ) (o : O) (ho : o ≠ 0) :
    vK p (algebraMap O (KK O) o) = ((((dvrOrderNat o : ℕ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  rw [valuation_eq_of_fraction p _ o 1 ho one_ne_zero (by rw [map_one, mul_one]), dvr_order_unit_eq_zero isUnit_one]
  congr 1
  all_goals push_cast
  all_goals ring

/- English proof (translation)
Establish `hpm` using `S.p_mem`. Assume the negation of the conclusion as `hnu`. Establish `hn' : (n : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Establish `hcop : Nat.Coprime p n` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hn`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hcop`.

Establish `h1 : (u : O) * (p : O) + (v : O) * (n : O) = 1`. Use `congrArg (Int.cast : ℤ → O) huv` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O`.

Rewrite using `[← h1]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hn')`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)`.
-/
theorem natCast_isUnit_of_coprime {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) (n : ℕ) (hn : ¬ p ∣ n) :
    IsUnit (n : O) := by
  have hpm := S.p_mem
  by_contra hnu
  have hn' : (n : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (u : O) * (p : O) + (v : O) * (n : O) = 1 := by
    have := congrArg (Int.cast : ℤ → O) huv
    push_cast at this
    exact this
  have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hn')
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)

/- English proof (translation)
Take `⟨k, n, hn, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one`. Use `push_cast`. Conclude with `mul_ne_zero (pow_ne_zero _ S.p_ne) (natCast_isUnit_of_coprime hp S n hn).ne_zero`.
-/
theorem natCast_ne_zero_in_dvr {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) (m : ℕ) (hm : m ≠ 0) : (m : O) ≠ 0 := by
  obtain ⟨k, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  push_cast
  exact mul_ne_zero (pow_ne_zero _ S.p_ne) (natCast_isUnit_of_coprime hp S n hn).ne_zero

/- English proof (translation)
Use `charZero_of_inj_zero fun m hm => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `natCast_ne_zero_in_dvr hp S m h hm`.
-/
theorem dvr_ring_charZero {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) : CharZero O := by
  refine charZero_of_inj_zero fun m hm => ?_
  by_contra h
  exact natCast_ne_zero_in_dvr hp S m h hm

/- English proof (translation)
Use `haveI := dvr_ring_charZero hp S`. Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `h' : algebraMap O (KK O) (n : O) = 0` using `by rw [map_natCast]; exact hn`. Establish `h'' : (n : O) = 0` using `IsFractionRing.injective O (KK O) (by rw [h', map_zero])`. Conclude with `h''` after adjusting the coercions.
-/
theorem dvr_fraction_field_char_zero {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) : CharZero (KK O) := by
  haveI := dvr_ring_charZero hp S
  refine charZero_of_inj_zero fun n hn => ?_
  have h' : algebraMap O (KK O) (n : O) = 0 := by rw [map_natCast]; exact hn
  have h'' : (n : O) = 0 := IsFractionRing.injective O (KK O) (by rw [h', map_zero])
  exact_mod_cast h''

/- English proof (translation)
Take `⟨k, n, hn, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn (dvd_zero p)`. Establish `hpO : (p : O) ≠ 0` using `S.p_ne`.

Establish `hnU` using `natCast_isUnit_of_coprime hp S n hn`. Establish `hcast : ((p ^ k * n : ℕ) : KK O) = algebraMap O (KK O) ((p : O) ^ k * (n : O))` using `by simp`. Rewrite using `[hcast, valuation_algebraMap_eq_alt p _ (mul_ne_zero (pow_ne_zero _ hpO) hnU.ne_zero), dvr_order_mul (pow_ne_zero _ hpO) hnU.ne_zero, dvr_order_pow hpO, dvr_order_unit_eq_zero hnU]`. Establish `hval : padicValNat p (p ^ k * n) = k` using `by haveI := Fact.mk hp`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hp.ne_zero) hn0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hn, add_zero]`.

Establish `hr : dvrOrderNat (p : O) = ramE p O` using `rfl`. Establish `he : (ramE p O : ℚ) ≠ 0` using `by exact_mod_cast ramification_index_ne_zero S`. Rewrite using `[hval, hr, add_zero]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem valuation_natCast_padicVal {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) (m : ℕ) (hm : m ≠ 0) :
    vK p (m : KK O) = ((padicValNat p m : ℚ) : WithTop ℚ) := by
  obtain ⟨k, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero p)
  have hpO : (p : O) ≠ 0 := S.p_ne
  have hnU := natCast_isUnit_of_coprime hp S n hn
  have hcast : ((p ^ k * n : ℕ) : KK O) = algebraMap O (KK O) ((p : O) ^ k * (n : O)) := by simp
  rw [hcast, valuation_algebraMap_eq_alt p _ (mul_ne_zero (pow_ne_zero _ hpO) hnU.ne_zero),
    dvr_order_mul (pow_ne_zero _ hpO) hnU.ne_zero, dvr_order_pow hpO, dvr_order_unit_eq_zero hnU]
  have hval : padicValNat p (p ^ k * n) = k := by
    haveI := Fact.mk hp
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hn0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hn, add_zero]
  have hr : dvrOrderNat (p : O) = ramE p O := rfl
  have he : (ramE p O : ℚ) ≠ 0 := by exact_mod_cast ramification_index_ne_zero S
  rw [hval, hr, add_zero]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h0`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by rw [hx, map_zero]⟩`. Take `⟨a, b, ha, hb, hab⟩` from `exists_fraction_of_ne_zero x hx`.

Rewrite `h0` using `[valuation_eq_of_fraction p x a b ha hb hab]`. Establish `he : (0 : ℚ) < ramE p O` using `by exact_mod_cast Nat.pos_of_ne_zero (ramification_index_ne_zero S)`. Establish `h1` using `WithTop.coe_nonneg.1 h0`. Rewrite `h1` using `[le_div_iff₀ he, zero_mul]`. Establish `h3 : (0 : ℤ) ≤ (dvrOrderNat a : ℤ) - (dvrOrderNat b : ℤ)` using `by exact_mod_cast h1`.

Establish `h2 : dvrOrderNat b ≤ dvrOrderNat a` using `by omega`. Establish `hdvd : b ∣ a` using `IsDiscreteValuationRing.addVal_le_iff_dvd.1 (by rw [← dvr_order_coe_addVal hb, ← dvr_order_coe_addVal ha]; exact ENat.coe_le_coe.2 h2)`. Take `⟨c, rfl⟩` from `hdvd`. Establish `hb' : algebraMap O (KK O) b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hb`. Conclude with `⟨c, mul_right_cancel₀ hb' (by rw [hab, map_mul, mul_comm])⟩`.

Introduce and unpack `⟨o, rfl⟩`. Distinguish the cases in `ho : o = 0`. Rewrite using `[ho, map_zero, valuation_zero_alt]`. Conclude with `le_top`. Rewrite using `[valuation_algebraMap_eq_alt p o ho]`.

Conclude with `WithTop.coe_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))`.
-/
theorem valuation_nonneg_iff_integral {p : ℕ} (S : UniformizedDVR p O) (x : KK O) :
    0 ≤ vK p x ↔ ∃ o : O, x = algebraMap O (KK O) o := by
  constructor
  · intro h0
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    obtain ⟨a, b, ha, hb, hab⟩ := exists_fraction_of_ne_zero x hx
    rw [valuation_eq_of_fraction p x a b ha hb hab] at h0
    have he : (0 : ℚ) < ramE p O := by exact_mod_cast Nat.pos_of_ne_zero (ramification_index_ne_zero S)
    have h1 := WithTop.coe_nonneg.1 h0
    rw [le_div_iff₀ he, zero_mul] at h1
    have h3 : (0 : ℤ) ≤ (dvrOrderNat a : ℤ) - (dvrOrderNat b : ℤ) := by exact_mod_cast h1
    have h2 : dvrOrderNat b ≤ dvrOrderNat a := by omega
    have hdvd : b ∣ a := IsDiscreteValuationRing.addVal_le_iff_dvd.1
      (by rw [← dvr_order_coe_addVal hb, ← dvr_order_coe_addVal ha]; exact ENat.coe_le_coe.2 h2)
    obtain ⟨c, rfl⟩ := hdvd
    have hb' : algebraMap O (KK O) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hb
    exact ⟨c, mul_right_cancel₀ hb' (by rw [hab, map_mul, mul_comm])⟩
  · rintro ⟨o, rfl⟩
    by_cases ho : o = 0
    · rw [ho, map_zero, valuation_zero_alt]
      exact le_top
    rw [valuation_algebraMap_eq_alt p o ho]
    exact WithTop.coe_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/- English proof (translation)
Unfold `ValuationProperties`. Conclude with `⟨valuation_zero_alt p, valuation_mul_alt p, valuation_add_ge_min p, fun m hm => valuation_natCast_padicVal hp S m hm, valuation_neg p, valuation_nonneg_iff_integral S⟩`.
-/
theorem valuation_properties_hold {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) : ValuationProperties p O := by
  unfold ValuationProperties
  exact ⟨valuation_zero_alt p, valuation_mul_alt p, valuation_add_ge_min p, fun m hm => valuation_natCast_padicVal hp S m hm, valuation_neg p,
    valuation_nonneg_iff_integral S⟩

end Formalism.MainNotions.G.GLWeightTheory
