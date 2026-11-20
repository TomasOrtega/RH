import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain WithZero IsLocalRing

/- English proof (translation)
Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => simp at h`. Consider the case `coe a`. Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => simp at h`.

Consider the case `coe b`. Establish `ha' : (0 : ℤ) ≤ a` using `by exact_mod_cast ha`. Establish `hb' : (0 : ℤ) ≤ b` using `by exact_mod_cast hb`. Establish `h' : a + b = 0` using `by exact_mod_cast h`. Establish `ha0 : a = 0` using `by omega`.

Rewrite using `[ha0]`. Apply the tactic sequence `first | rfl | exact WithTop.coe_zero | simp`.
-/
theorem wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe b =>
      have ha' : (0 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (0 : ℤ) ≤ b := by exact_mod_cast hb
      have h' : a + b = 0 := by exact_mod_cast h
      have ha0 : a = 0 := by omega
      rw [ha0]
      first | rfl | exact WithTop.coe_zero | simp

section
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)

variable (L) in
open Classical in

noncomputable def addv : AddValuation L (WithTop ℤ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else (((-log (v.valuation L x) : ℤ)) : WithTop ℤ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      rw [← WithTop.coe_min, WithTop.coe_le_coe]
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      have hxy' : v.valuation L (x + y) ≠ 0 := by simpa using hxy
      have h := (v.valuation L).map_add x y
      rcases le_max_iff.mp h with h | h
      · have := (log_le_log hxy' hx').mpr h
        rw [min_le_iff]; left; omega
      · have := (log_le_log hxy' hy').mpr h
        rw [min_le_iff]; right; omega)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      simp only [hx, hy, mul_eq_zero, or_self, ite_false, map_mul, log_mul hx' hy']
      rw [← WithTop.coe_add]; congr 1; ring)

/- English proof (translation)
Use `first`. Consider the case `(unfold addv; rw [AddValuation.of_apply, if_neg hx])`. Consider the case `simp [addv, AddValuation.of_apply, hx]`.
-/
theorem addv_apply {x : L} (hx : x ≠ 0) :
    addv L v x = (((-log (v.valuation L x) : ℤ)) : WithTop ℤ) := by
  first
  | (unfold addv; rw [AddValuation.of_apply, if_neg hx])
  | simp [addv, AddValuation.of_apply, hx]

/- English proof (translation)
Distinguish the cases in `hs : s = 0`. Substitute `hs` using the available equality. Simplify using the standard rewrite rules. Establish `hx : algebraMap S L s ≠ 0`. Introduce `h`.

Apply `hs` to reduce the goal to its premises. Apply `IsFractionRing.injective S L` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Establish `hv : v.valuation L (algebraMap S L s) ≠ 0` using `by simpa using hx`. Rewrite using `[addv_apply v hx]`.

Establish `h1` using `(log_le_log hv one_ne_zero).mpr (v.valuation_le_one s)`. Rewrite `h1` using `[log_one]`. Establish `h2 : (0 : ℤ) ≤ -log (v.valuation L (algebraMap S L s))` using `by omega`. Conclude with `h2` after adjusting the coercions.
-/
theorem addv_nonneg (s : S) : 0 ≤ addv L v (algebraMap S L s) := by
  by_cases hs : s = 0
  · subst hs
    simp
  have hx : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S L
    rw [h, map_zero]
  have hv : v.valuation L (algebraMap S L s) ≠ 0 := by simpa using hx
  rw [addv_apply v hx]
  have h1 := (log_le_log hv one_ne_zero).mpr (v.valuation_le_one s)
  rw [log_one] at h1
  have h2 : (0 : ℤ) ≤ -log (v.valuation L (algebraMap S L s)) := by omega
  exact_mod_cast h2

/- English proof (translation)
Distinguish the cases in `hs : s = 0`. Substitute `hs` using the available equality. Rewrite using `[map_zero, AddValuation.map_zero]`. Conclude with `iff_of_true (WithTop.coe_lt_top 0) (Submodule.zero_mem _)`. Establish `hx : algebraMap S L s ≠ 0`.

Introduce `h`. Apply `hs` to reduce the goal to its premises. Apply `IsFractionRing.injective S L` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Establish `hv : v.valuation L (algebraMap S L s) ≠ 0` using `by simpa using hx`.

Rewrite using `[addv_apply v hx, ← v.valuation_lt_one_iff_mem (K := L) s]`. Establish `h1 : v.valuation L (algebraMap S L s) < 1 ↔ ¬ (log (1 : WithZero (Multiplicative ℤ)) ≤ log (v.valuation L (algebraMap S L s)))`. Rewrite using `[log_le_log one_ne_zero hv, not_le]`. Rewrite using `[h1, log_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]`. Apply the tactic sequence `constructor <;> intro h <;> omega`.
-/
theorem addv_pos_iff (s : S) : 0 < addv L v (algebraMap S L s) ↔ s ∈ v.asIdeal := by
  by_cases hs : s = 0
  · subst hs
    rw [map_zero, AddValuation.map_zero]
    exact iff_of_true (WithTop.coe_lt_top 0) (Submodule.zero_mem _)
  have hx : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S L
    rw [h, map_zero]
  have hv : v.valuation L (algebraMap S L s) ≠ 0 := by simpa using hx
  rw [addv_apply v hx, ← v.valuation_lt_one_iff_mem (K := L) s]
  have h1 : v.valuation L (algebraMap S L s) < 1 ↔
      ¬ (log (1 : WithZero (Multiplicative ℤ)) ≤ log (v.valuation L (algebraMap S L s))) := by
    rw [log_le_log one_ne_zero hv, not_le]
  rw [h1, log_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  constructor <;> intro h <;> omega

/- English proof (translation)
Establish `hunit : ∀ d : S, d ∉ v.asIdeal → w (algebraMap S L d) = 0` using `fun d hd => le_antisymm (not_lt.1 (mt (hQ d).1 hd)) (h0 d)`. Establish `hint : ∀ x : L, v.valuation L x ≤ 1 → 0 ≤ w x`. Introduce `x hx`. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) x hx`. Establish `h` using `congrArg w hnd`.

Rewrite `h` using `[AddValuation.map_mul, hunit d d.2, add_zero]`. Rewrite using `[h]`. Conclude with `h0 n`. Establish `heq1 : ∀ x : L, x ≠ 0 → v.valuation L x = 1 → w x = 0`. Introduce `x hx h1`.

Establish `h2 : v.valuation L x⁻¹ = 1` using `by rw [map_inv₀, h1, inv_one]`. Establish `hs : w x + w x⁻¹ = 0`. Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]`. Conclude with `wt_add_eq_zero (hint x h1.le) (hint _ h2.le) hs`. Take `⟨π, hπ⟩` from `v.intValuation_exists_uniformizer`.

Use `set p := algebraMap S L π with hp_def`. Establish `hp : v.valuation L p = exp (-1 : ℤ)` using `by rw [hp_def, HeightOneSpectrum.valuation_of_algebraMap, hπ]`. Establish `hp0 : p ≠ 0`. Introduce `h`. Rewrite `hp` using `[h, map_zero]`.

Conclude with `exp_ne_zero hp.symm`. Establish `hπQ : π ∈ v.asIdeal`. Rewrite using `[← v.intValuation_lt_one_iff_mem, hπ, ← exp_zero, exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Take `⟨a0, ha0⟩ : ∃ a0 : ℤ, w p = a0` from `WithTop.ne_top_iff_exists.mp (hw.1 p hp0) |>.imp fun _ h => h.symm`.

Establish `hpinv : w p⁻¹ = ((-a0 : ℤ) : WithTop ℤ)`. Establish `hs : w p + w p⁻¹ = 0`. Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ hp0, AddValuation.map_one]`. Establish `hne : w p⁻¹ ≠ ⊤` using `hw.1 _ (inv_ne_zero hp0)`. Take `⟨b, hb⟩` from `WithTop.ne_top_iff_exists.mp hne`.

Rewrite `hs`, the goal using `[← hb]`. Rewrite `hs` using `[ha0]`. Establish `: a0 + b = 0` using `by exact_mod_cast hs`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `hzpow : ∀ n : ℤ, w (p ^ n) = ((n * a0 : ℤ) : WithTop ℤ)`. Introduce `n`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[zpow_add_one₀ hp0, AddValuation.map_mul, ih, ha0, ← WithTop.coe_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `pred n ih`. Rewrite using `[zpow_sub_one₀ hp0, AddValuation.map_mul, ih, hpinv, ← WithTop.coe_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hform : ∀ x : L, x ≠ 0 → w x = (((-log (v.valuation L x)) * a0 : ℤ) : WithTop ℤ)`. Introduce `x hx`. Establish `hvx : v.valuation L x ≠ 0` using `by simpa using hx`.

Use `set k := log (v.valuation L x)`. Establish `hy : v.valuation L (x * p ^ k) = 1`. Rewrite using `[map_mul, map_zpow₀, hp, ← exp_log hvx, ← exp_zsmul, ← exp_add]`. Simplify using `[k]`. Establish `hy0 : x * p ^ k ≠ 0` using `mul_ne_zero hx (zpow_ne_zero _ hp0)`.

Establish `h` using `heq1 _ hy0 hy`. Rewrite `h` using `[AddValuation.map_mul, hzpow]`. Establish `hne : w x ≠ ⊤` using `hw.1 x hx`. Take `⟨b, hb⟩` from `WithTop.ne_top_iff_exists.mp hne`. Rewrite `h`, the goal using `[← hb]`.

Establish `: b + k * a0 = 0` using `by exact_mod_cast h`. Use `congr 1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha1 : a0 = 1`. Take `⟨z, hz⟩` from `hw.2`.

Establish `hz0 : z ≠ 0`. Introduce `h`. Rewrite `hz` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe hz`. Rewrite `hz` using `[hform z hz0]`.

Establish `h1 : (-log (v.valuation L z)) * a0 = 1` using `by exact_mod_cast hz`. Establish `hpos : 0 < a0`. Use `(hQ π).mpr hπQ` as an intermediate fact. Rewrite `this` using `[← hp_def, ha0]`. Conclude with `this` after adjusting the coercions.

Apply the tactic sequence `rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega`. Apply `AddValuation.ext` to reduce the goal to its premises. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[hform x hx, addv_apply v hx, ha1, mul_one]`.
-/
theorem eq_addv (w : AddValuation L (WithTop ℤ)) (hw : IsNormDiscrete w)
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) : w = addv L v := by
  have hunit : ∀ d : S, d ∉ v.asIdeal → w (algebraMap S L d) = 0 := fun d hd =>
    le_antisymm (not_lt.1 (mt (hQ d).1 hd)) (h0 d)
  have hint : ∀ x : L, v.valuation L x ≤ 1 → 0 ≤ w x := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) x hx
    have h := congrArg w hnd
    rw [AddValuation.map_mul, hunit d d.2, add_zero] at h
    rw [h]; exact h0 n
  have heq1 : ∀ x : L, x ≠ 0 → v.valuation L x = 1 → w x = 0 := by
    intro x hx h1
    have h2 : v.valuation L x⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
    have hs : w x + w x⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
    exact wt_add_eq_zero (hint x h1.le) (hint _ h2.le) hs
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  set p := algebraMap S L π with hp_def
  have hp : v.valuation L p = exp (-1 : ℤ) := by rw [hp_def, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hp; exact exp_ne_zero hp.symm
  have hπQ : π ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hπ, ← exp_zero, exp_lt_exp]; omega
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℤ, w p = a0 := WithTop.ne_top_iff_exists.mp (hw.1 p hp0) |>.imp
    fun _ h => h.symm
  have hpinv : w p⁻¹ = ((-a0 : ℤ) : WithTop ℤ) := by
    have hs : w p + w p⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hp0, AddValuation.map_one]
    have hne : w p⁻¹ ≠ ⊤ := hw.1 _ (inv_ne_zero hp0)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hb] at hs ⊢
    rw [ha0] at hs
    have : a0 + b = 0 := by exact_mod_cast hs
    congr 1; omega
  have hzpow : ∀ n : ℤ, w (p ^ n) = ((n * a0 : ℤ) : WithTop ℤ) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one₀ hp0, AddValuation.map_mul, ih, ha0, ← WithTop.coe_add]; congr 1; ring
    | pred n ih =>
      rw [zpow_sub_one₀ hp0, AddValuation.map_mul, ih, hpinv, ← WithTop.coe_add]; congr 1; ring
  have hform : ∀ x : L, x ≠ 0 → w x = (((-log (v.valuation L x)) * a0 : ℤ) : WithTop ℤ) := by
    intro x hx
    have hvx : v.valuation L x ≠ 0 := by simpa using hx
    set k := log (v.valuation L x)
    have hy : v.valuation L (x * p ^ k) = 1 := by
      rw [map_mul, map_zpow₀, hp, ← exp_log hvx, ← exp_zsmul, ← exp_add]
      simp [k]
    have hy0 : x * p ^ k ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hp0)
    have h := heq1 _ hy0 hy
    rw [AddValuation.map_mul, hzpow] at h
    have hne : w x ≠ ⊤ := hw.1 x hx
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hb] at h ⊢
    have : b + k * a0 = 0 := by exact_mod_cast h
    congr 1; linarith
  have ha1 : a0 = 1 := by
    obtain ⟨z, hz⟩ := hw.2
    have hz0 : z ≠ 0 := by
      intro h; rw [h, AddValuation.map_zero] at hz; exact WithTop.top_ne_coe hz
    rw [hform z hz0] at hz
    have h1 : (-log (v.valuation L z)) * a0 = 1 := by exact_mod_cast hz
    have hpos : 0 < a0 := by
      have := (hQ π).mpr hπQ
      rw [← hp_def, ha0] at this; exact_mod_cast this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · subst hx; simp
  rw [hform x hx, addv_apply v hx, ha1, mul_one]

end

def PlacesOver (O L : Type*) [CommRing O] [IsLocalRing O] [Field L] [Algebra O L] :
    Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : O, 0 ≤ w (algebraMap O L x) ∧
    (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl x`. Establish `hsP : (s : R) ∉ P` using `s.2`. Establish `hs0 : w (algebraMap R L s) = 0`.

Take `⟨h1, h2⟩` from `h s`. Conclude with `le_antisymm (not_lt.mp fun hp => hsP (h2.mp hp)) h1`. Establish `hspec : algebraMap O L (IsLocalization.mk' O r s) * algebraMap R L s = algebraMap R L r`. Rewrite using `[IsScalarTower.algebraMap_apply R O L (s : R), IsScalarTower.algebraMap_apply R O L r, ← map_mul, IsLocalization.mk'_spec]`. Establish `hw : w (algebraMap O L (IsLocalization.mk' O r s)) = w (algebraMap R L r)`.

Rewrite using `[← hspec, AddValuation.map_mul, hs0, add_zero]`. Rewrite using `[hw]`. Use `first`. Consider the case `(rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O P]; exact h r)`. Consider the case `(rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (S := O) (I := P)]; exact h r)`.

Consider the case `(rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O]; exact h r)`. Introduce `h x`. Establish `hx` using `h (algebraMap R O x)`. Rewrite `hx` using `[← IsScalarTower.algebraMap_apply R O L x]`. Use `first`.

Consider the case `rwa [IsLocalization.AtPrime.to_map_mem_maximal_iff (S := O) (I := P)] at hx`. Consider the case `(rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O P] at hx; exact hx)`.
-/
theorem placesOver_iff_loc {R O L : Type*} [CommRing R] [CommRing O] [IsLocalRing O] [Field L]
    [Algebra R O] [Algebra R L] [Algebra O L] [IsScalarTower R O L] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime O P] (w : AddValuation L (WithTop ℤ)) :
    (∀ x : R, 0 ≤ w (algebraMap R L x) ∧ (0 < w (algebraMap R L x) ↔ x ∈ P)) ↔
      (∀ x : O, 0 ≤ w (algebraMap O L x) ∧ (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)) := by
  constructor
  · intro h x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hsP : (s : R) ∉ P := s.2
    have hs0 : w (algebraMap R L s) = 0 := by
      obtain ⟨h1, h2⟩ := h s
      exact le_antisymm (not_lt.mp fun hp => hsP (h2.mp hp)) h1
    have hspec : algebraMap O L (IsLocalization.mk' O r s) * algebraMap R L s =
        algebraMap R L r := by
      rw [IsScalarTower.algebraMap_apply R O L (s : R), IsScalarTower.algebraMap_apply R O L r,
        ← map_mul, IsLocalization.mk'_spec]
    have hw : w (algebraMap O L (IsLocalization.mk' O r s)) = w (algebraMap R L r) := by
      rw [← hspec, AddValuation.map_mul, hs0, add_zero]
    rw [hw]
    first
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O P]; exact h r)
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (S := O) (I := P)]; exact h r)
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O]; exact h r)
  · intro h x
    have hx := h (algebraMap R O x)
    rw [← IsScalarTower.algebraMap_apply R O L x] at hx
    first
    | rwa [IsLocalization.AtPrime.to_map_mem_maximal_iff (S := O) (I := P)] at hx
    | (rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O P] at hx; exact hx)

section DVR

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

include F in
/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_eq O F L]`. Use `first`. Consider the case `exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)`. Consider the case `(rw [RingHom.coe_comp]; exact (algebraMap F L).injective.comp (IsFractionRing.injective O F))`.
-/
theorem algebraMap_OL_injective : Function.Injective (algebraMap O L) := by
  rw [IsScalarTower.algebraMap_eq O F L]
  first
  | exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  | (rw [RingHom.coe_comp]; exact (algebraMap F L).injective.comp (IsFractionRing.injective O F))

variable (O F L) in
include F in

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O (integralClosure O L))`. Introduce `a b hab`. Use `first`. Consider the case `exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)`. Consider the case `(apply algebraMap_OL_injective (F := F)`.

Rewrite using `[IsScalarTower.algebraMap_apply O (integralClosure O L) L a, IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])`. Establish `hne : Q ≠ ⊥`. Introduce and unpack `rfl`. Establish `hB : IsField (integralClosure O L)` using `Ring.isField_iff_maximal_bot.mpr hQ`. Establish `hO : IsField O` using `isField_of_isIntegral_of_isField hinj hB`.

Establish `hmax : (⊥ : Ideal O).IsMaximal` using `Ring.isField_iff_maximal_bot.mp hO`. Conclude with `absurd (IsLocalRing.eq_maximalIdeal hmax).symm IsDiscreteValuationRing.not_a_field'`. Conclude with `⟨⟨Q, hQ.isPrime, hne⟩, rfl⟩`.
-/
theorem exists_heightOne (Q : Ideal (integralClosure O L)) (hQ : Q.IsMaximal) :
    ∃ v : HeightOneSpectrum (integralClosure O L), v.asIdeal = Q := by
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b hab
    first
    | exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)
    | (apply algebraMap_OL_injective (F := F)
       rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a,
         IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hB : IsField (integralClosure O L) := Ring.isField_iff_maximal_bot.mpr hQ
    have hO : IsField O := isField_of_isIntegral_of_isField hinj hB
    have hmax : (⊥ : Ideal O).IsMaximal := Ring.isField_iff_maximal_bot.mp hO
    exact absurd (IsLocalRing.eq_maximalIdeal hmax).symm IsDiscreteValuationRing.not_a_field'
  exact ⟨⟨Q, hQ.isPrime, hne⟩, rfl⟩

/- English proof (translation)
Rewrite using `[PlacesOver, Set.mem_setOf_eq, IsNormDiscrete]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[addv_apply v ha]`. Conclude with `WithTop.coe_ne_top`.

Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer L`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `absurd hπ.symm (by simp)`.

Use `⟨π, ?_⟩` and prove the remaining obligations. Rewrite using `[addv_apply v hπ0, hπ, log_exp]`. Simplify using the standard rewrite rules. Introduce `x haveI := v.isMaximal`. Establish `hcomap : v.asIdeal.comap (algebraMap O (integralClosure O L)) = maximalIdeal O`.

Apply `IsLocalRing.eq_maximalIdeal` to reduce the goal to its premises. Use `first`. Consider the case `exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal`. Consider the case `exact Ideal.IsMaximal.under O v.asIdeal`. Consider the case `infer_instance`.

Rewrite using `[IsScalarTower.algebraMap_apply O (integralClosure O L) L x, ← hcomap, Ideal.mem_comap]`. Conclude with `⟨addv_nonneg v _, addv_pos_iff v _⟩`.
-/
theorem addv_mem_placesOver (v : HeightOneSpectrum (integralClosure O L)) :
    addv L v ∈ PlacesOver O L := by
  rw [PlacesOver, Set.mem_setOf_eq, IsNormDiscrete]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [addv_apply v ha]
    exact WithTop.coe_ne_top
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact absurd hπ.symm (by simp)
    refine ⟨π, ?_⟩
    rw [addv_apply v hπ0, hπ, log_exp]
    simp
  · intro x
    haveI := v.isMaximal
    have hcomap : v.asIdeal.comap (algebraMap O (integralClosure O L)) = maximalIdeal O := by
      apply IsLocalRing.eq_maximalIdeal
      first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      | exact Ideal.IsMaximal.under O v.asIdeal
      | infer_instance
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x, ← hcomap, Ideal.mem_comap]
    exact ⟨addv_nonneg v _, addv_pos_iff v _⟩

variable (O F L) in
include F in

/- English proof (translation)
Set `f : HeightOneSpectrum (integralClosure O L) → PlacesOver O L` to `fun v => ⟨addv L v, addv_mem_placesOver v⟩`. Establish `hinj : Function.Injective f`. Introduce `v v' hvv`. Establish `h : addv L v = addv L v'` using `congrArg Subtype.val hvv`. Use extensionality with `b`.

Rewrite using `[← addv_pos_iff (L := L) v, ← addv_pos_iff (L := L) v', h]`. Establish `hsurj : Function.Surjective f`. Introduce and unpack `⟨w, hw⟩`. Establish `h0 : ∀ b : integralClosure O L, 0 ≤ w (algebraMap (integralClosure O L) L b)`. Introduce `b`.

Establish `hb : IsIntegral O (algebraMap (integralClosure O L) L b)` using `b.2`. Use `letI : Algebra O (vRing w) := ((algebraMap O L).codRestrict (vRing w) (fun x => (hw.2 x).1)).toAlgebra`. Use `haveI : IsScalarTower O (vRing w) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hb' : IsIntegral (vRing w) (algebraMap (integralClosure O L) L b)` using `hb.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hb'`.

Rewrite using `[← hy]`. Conclude with `y.2`. Set `Qw : Ideal (integralClosure O L)` to `{ carrier := {b | 0 < w (algebraMap (integralClosure O L) L b)} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at ha hb ⊢`. Conclude with `lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun c b hb => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢`. Conclude with `lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }`. Establish `hprime : Qw.IsPrime`.

Use `⟨fun htop => ?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : integralClosure O L) ∈ Qw` using `htop ▸ Submodule.mem_top`. Simplify using `[Qw] at h1`. Express the relevant statement in the definitionally equal form `0 < w (algebraMap _ L (a * b)) at hab`. Rewrite `hab` using `[map_mul, AddValuation.map_mul]`.

Assume the negation of the conclusion as `hno`. Rewrite `hno` using `[not_or]`. Establish `ha : w (algebraMap _ L a) = 0` using `le_antisymm (not_lt.1 (hno.1 : ¬ 0 < w (algebraMap _ L a))) (h0 a)`. Establish `hb : w (algebraMap _ L b) = 0` using `le_antisymm (not_lt.1 (hno.2 : ¬ 0 < w (algebraMap _ L b))) (h0 b)`. Rewrite `hab` using `[ha, hb, add_zero]`.

Conclude with `lt_irrefl _ hab`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hne : Qw ≠ ⊥`. Introduce `hbot`. Establish `hmem : algebraMap O (integralClosure O L) ϖ ∈ Qw` using `by show 0 < w (algebraMap (integralClosure O L) L (algebraMap O _ ϖ))`.

Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `((hw.2 ϖ).2).2 hϖ.not_isUnit`. Rewrite `hmem` using `[hbot, Ideal.mem_bot]`. Establish `: (algebraMap O L) ϖ = 0`. Rewrite using `[IsScalarTower.algebraMap_apply O (integralClosure O L) L, hmem, map_zero]`.

Conclude with `hϖ.ne_zero (algebraMap_OL_injective (F := F) (by rw [this, map_zero]))`. Use `⟨⟨Qw, hprime, hne⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `(eq_addv _ w hw.1 h0 (fun s => Iff.rfl)).symm`. Conclude with `⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun v => rfl⟩`.
-/
theorem placesOver_bij : ∃ e : HeightOneSpectrum (integralClosure O L) ≃ PlacesOver O L,
    ∀ v, (e v : AddValuation L (WithTop ℤ)) = addv L v := by
  classical
  let f : HeightOneSpectrum (integralClosure O L) → PlacesOver O L :=
    fun v => ⟨addv L v, addv_mem_placesOver v⟩
  have hinj : Function.Injective f := by
    intro v v' hvv
    have h : addv L v = addv L v' := congrArg Subtype.val hvv
    ext b
    rw [← addv_pos_iff (L := L) v, ← addv_pos_iff (L := L) v', h]
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    have h0 : ∀ b : integralClosure O L, 0 ≤ w (algebraMap (integralClosure O L) L b) := by
      intro b
      have hb : IsIntegral O (algebraMap (integralClosure O L) L b) := b.2
      letI : Algebra O (vRing w) :=
        ((algebraMap O L).codRestrict (vRing w) (fun x => (hw.2 x).1)).toAlgebra
      haveI : IsScalarTower O (vRing w) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hb' : IsIntegral (vRing w) (algebraMap (integralClosure O L) L b) := hb.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
      rw [← hy]
      exact y.2
    let Qw : Ideal (integralClosure O L) :=
      { carrier := {b | 0 < w (algebraMap (integralClosure O L) L b)}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
          exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
        zero_mem' := by simp
        smul_mem' := fun c b hb => by
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
          exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
    have hprime : Qw.IsPrime := by
      refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
      · have h1 : (1 : integralClosure O L) ∈ Qw := htop ▸ Submodule.mem_top
        simp [Qw] at h1
      · change 0 < w (algebraMap _ L (a * b)) at hab
        rw [map_mul, AddValuation.map_mul] at hab
        by_contra hno
        rw [not_or] at hno
        have ha : w (algebraMap _ L a) = 0 :=
          le_antisymm (not_lt.1 (hno.1 : ¬ 0 < w (algebraMap _ L a))) (h0 a)
        have hb : w (algebraMap _ L b) = 0 :=
          le_antisymm (not_lt.1 (hno.2 : ¬ 0 < w (algebraMap _ L b))) (h0 b)
        rw [ha, hb, add_zero] at hab
        exact lt_irrefl _ hab
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hne : Qw ≠ ⊥ := by
      intro hbot
      have hmem : algebraMap O (integralClosure O L) ϖ ∈ Qw := by
        show 0 < w (algebraMap (integralClosure O L) L (algebraMap O _ ϖ))
        rw [← IsScalarTower.algebraMap_apply]
        exact ((hw.2 ϖ).2).2 hϖ.not_isUnit
      rw [hbot, Ideal.mem_bot] at hmem
      have : (algebraMap O L) ϖ = 0 := by
        rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L, hmem, map_zero]
      exact hϖ.ne_zero (algebraMap_OL_injective (F := F) (by rw [this, map_zero]))
    refine ⟨⟨Qw, hprime, hne⟩, Subtype.ext ?_⟩
    exact (eq_addv _ w hw.1 h0 (fun s => Iff.rfl)).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun v => rfl⟩

/- English proof (translation)
Establish `hx : algebraMap (integralClosure O L) L b ≠ 0`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Apply `IsFractionRing.injective (integralClosure O L) L` to reduce the goal to its premises. Rewrite using `[h, map_zero]`.

Establish `hI : Ideal.span {b} ≠ 0` using `by first`. Consider the case `(rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb)`. Consider the case `simpa using hb`. Establish `hc` using `Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot`. Establish `hval : v.valuation L (algebraMap (integralClosure O L) L b) = v.intValuation b` using `by first`.

Consider the case `exact v.valuation_of_algebraMap b`. Consider the case `exact HeightOneSpectrum.valuation_of_algebraMap v b`. Consider the case `simp`. Rewrite using `[addv_apply v hx, hval, v.intValuation_if_neg hb, log_exp, neg_neg, hc]`. Use `first`.

Consider the case `(norm_cast; done)`. Consider the case `(norm_cast; convert rfl; done)`. Consider the case `(push_cast; convert rfl; done)`. Consider the case `(congr 1; convert rfl)`.
-/
theorem addv_count (v : HeightOneSpectrum (integralClosure O L)) (b : integralClosure O L)
    (hb : b ≠ 0) :
    addv L v (algebraMap (integralClosure O L) L b) =
      ((Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) : ℕ) : WithTop ℤ) := by
  have hx : algebraMap (integralClosure O L) L b ≠ 0 := by
    intro h
    apply hb
    apply IsFractionRing.injective (integralClosure O L) L
    rw [h, map_zero]
  have hI : Ideal.span {b} ≠ 0 := by
    first
    | (rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb)
    | simpa using hb
  have hc := Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot
  have hval : v.valuation L (algebraMap (integralClosure O L) L b) = v.intValuation b := by
    first
    | exact v.valuation_of_algebraMap b
    | exact HeightOneSpectrum.valuation_of_algebraMap v b
    | simp
  rw [addv_apply v hx, hval, v.intValuation_if_neg hb, log_exp, neg_neg, hc]
  first
  | (norm_cast; done)
  | (norm_cast; convert rfl; done)
  | (push_cast; convert rfl; done)
  | (congr 1; convert rfl)

include F in

/- English proof (translation)
Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hinj : Function.Injective (algebraMap O (integralClosure O L))`. Introduce `a b hab`. Use `first`. Consider the case `exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)`.

Consider the case `(apply algebraMap_OL_injective (F := F)`. Rewrite using `[IsScalarTower.algebraMap_apply O (integralClosure O L) L a, IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])`. Establish `hb : algebraMap O (integralClosure O L) ϖ ≠ 0`. Introduce `h`. Apply `hϖ0` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Rewrite using `[IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ, addv_count v _ hb]`. Establish `hmax : maximalIdeal O = Ideal.span {ϖ}` using `by first`. Consider the case `exact hϖ.maximalIdeal_eq`.

Consider the case `exact IsDiscreteValuationRing.Irreducible.maximalIdeal_eq hϖ`. Consider the case `exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Establish `hspan : Ideal.span {algebraMap O (integralClosure O L) ϖ} = (maximalIdeal O).map (algebraMap O (integralClosure O L))`. Rewrite using `[hmax, Ideal.map_span, Set.image_singleton]`. Establish `hund : v.asIdeal.under O = maximalIdeal O` using `by haveI := v.isMaximal`.

Apply `IsLocalRing.eq_maximalIdeal` to reduce the goal to its premises. Use `first`. Consider the case `exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal`. Consider the case `exact Ideal.IsMaximal.under O v.asIdeal`. Consider the case `infer_instance`.

Establish `hmap : Ideal.map (algebraMap O (integralClosure O L)) (v.asIdeal.under O) ≠ ⊥`. Rewrite using `[hund, ← hspan, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hb`. Rewrite using `[hspan]`. Use `norm_cast`.

Rewrite using `[← hund]`. Use `first`. Consider the case `(rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(simp [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)`.

Consider the case `(rw [Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(simp [Ideal.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)`. Consider the case `(rw [Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`.

Consider the case `(simp [Ideal.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)`. Consider the case `(rw [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(simp [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)`. Consider the case `(rw [Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`.

Consider the case `(rw [← Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(simp [Ideal.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)`. Consider the case `(rw [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(simp [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)`.

Consider the case `(rw [Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(simp [Ideal.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)`. Consider the case `(rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`. Consider the case `(rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done`.

Consider the case `(simp [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)`. Consider the case `skip`. Use `done`.
-/
theorem addv_uniformizer (v : HeightOneSpectrum (integralClosure O L)) {ϖ : O}
    (hϖ : Irreducible ϖ) :
    addv L v (algebraMap O L ϖ) = ((v.asIdeal.ramificationIdx O : ℕ) : WithTop ℤ) := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b hab
    first
    | exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)
    | (apply algebraMap_OL_injective (F := F)
       rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a,
         IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])
  have hb : algebraMap O (integralClosure O L) ϖ ≠ 0 := by
    intro h
    apply hϖ0
    apply hinj
    rw [h, map_zero]
  rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ, addv_count v _ hb]
  have hmax : maximalIdeal O = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact IsDiscreteValuationRing.Irreducible.maximalIdeal_eq hϖ
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {algebraMap O (integralClosure O L) ϖ} =
      (maximalIdeal O).map (algebraMap O (integralClosure O L)) := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hund : v.asIdeal.under O = maximalIdeal O := by
    haveI := v.isMaximal
    apply IsLocalRing.eq_maximalIdeal
    first
    | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
    | exact Ideal.IsMaximal.under O v.asIdeal
    | infer_instance
  have hmap : Ideal.map (algebraMap O (integralClosure O L)) (v.asIdeal.under O) ≠ ⊥ := by
    rw [hund, ← hspan, Ne, Ideal.span_singleton_eq_bot]
    exact hb
  rw [hspan]
  norm_cast
  rw [← hund]
  first
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)
  | (rw [Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)
  | skip
  done

end DVR

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
