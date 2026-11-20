import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Polynomial
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField nonZeroDivisors in
/- English proof (translation)
Establish `hint : IsIntegral (𝓞 K) β` using `Algebra.IsIntegral.isIntegral β`. Take `⟨h, hh⟩` from `minpoly.isIntegrallyClosed_dvd hint (p := X ^ k - C r) (by simp [hβ])`. Establish `hmem` using `aeval_derivative_mem_differentIdeal (𝓞 K) K L β hgen`. Establish `hder : aeval β (derivative (X ^ k - C r : (𝓞 K)[X])) = (k : 𝓞 L) * β ^ (k - 1)`. Simplify using `[derivative_X_pow]`.

Rewrite using `[← hder, hh, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.
-/
private theorem natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] (k : ℕ) (β : 𝓞 L) (r : 𝓞 K)
    (hβ : β ^ k = algebraMap (𝓞 K) (𝓞 L) r)
    (hgen : Algebra.adjoin K {algebraMap (𝓞 L) L β} = ⊤) :
    (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hint : IsIntegral (𝓞 K) β := Algebra.IsIntegral.isIntegral β
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ k - C r) (by simp [hβ])
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K L β hgen
  have hder : aeval β (derivative (X ^ k - C r : (𝓞 K)[X])) = (k : 𝓞 L) * β ^ (k - 1) := by
    simp [derivative_X_pow]
  rw [← hder, hh, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  exact Ideal.mul_mem_right _ _ hmem

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField nonZeroDivisors in

/- English proof (translation)
Establish `hy' : algebraMap K L y ≠ 0` using `(_root_.map_ne_zero _).mpr hy`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hk.ne']`. Conclude with `hy' hz.symm`.

Establish `hzk : z ^ k ≠ 0` using `pow_ne_zero k hz0`. Establish `htop : K⟮z⟯ = ⊤`. Rewrite using `[← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]`. Conclude with `IntermediateField.algebra_adjoin_le_adjoin K {z}`. Establish `hpow : ∀ b ∈ I, ∃ r : 𝓞 K, b ^ k = algebraMap (𝓞 K) K r * y`.

Introduce `b hb`. Establish `hbk : b ^ k ∈ Submodule.span (𝓞 K) {y}`. Rewrite using `[← hI]`. Conclude with `Submodule.pow_mem_pow I hb k`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp hbk`.

Conclude with `⟨r, by rw [← hr, Algebra.smul_def]⟩`. Establish `hquot : ∀ b ∈ I, ∃ β : 𝓞 L, algebraMap (𝓞 L) L β * z = algebraMap K L b`. Introduce `b hb`. Take `⟨r, hr⟩` from `hpow b hb`. Establish `hint : IsIntegral ℤ (algebraMap K L b / z)`.

Use `IsIntegral.of_pow hk ?_` and prove the remaining obligations. Establish `hq : (algebraMap K L b / z) ^ k = algebraMap K L (algebraMap (𝓞 K) K r)`. Rewrite using `[div_pow, ← map_pow, hr, map_mul, hz, mul_div_cancel_right₀ _ hy']`. Rewrite using `[hq]`. Conclude with `(RingOfIntegers.isIntegral_coe r).algebraMap`.

Conclude with `⟨⟨_, hint⟩, div_mul_cancel₀ _ hz0⟩`. Use `set S : Set (𝓞 L) := {β | ∃ b ∈ I, b ≠ 0 ∧ algebraMap (𝓞 L) L β * z = algebraMap K L b} with hS`. Establish `hmemS : ∀ β ∈ S, (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L)`. Introduce and unpack `β ⟨b, hb, hb0, hβb⟩`. Take `⟨r, hr⟩` from `hpow b hb`.

Establish `hβ0 : algebraMap (𝓞 L) L β ≠ 0`. Introduce `h0`. Rewrite `hβb` using `[h0, zero_mul]`. Conclude with `hb0 ((map_eq_zero _).mp hβb.symm)`. Use `natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq k β r ?_ ?_` and prove the remaining obligations.

Apply `FaithfulSMul.algebraMap_injective (𝓞 L) L` to reduce the goal to its premises. Rewrite using `[map_pow, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 K) K L]`. Use `mul_right_cancel₀ hzk ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, hβb, ← map_pow, hr, map_mul, hz]`. Establish `hK : K⟮algebraMap (𝓞 L) L β⟯ = ⊤`.

Rewrite using `[eq_top_iff, ← htop, IntermediateField.adjoin_simple_le_iff]`. Establish `hzeq : z = algebraMap K L b / algebraMap (𝓞 L) L β`. Rewrite using `[← hβb, mul_div_cancel_left₀ _ hβ0]`. Rewrite using `[hzeq]`. Conclude with `div_mem (IntermediateField.algebraMap_mem _ b) (IntermediateField.mem_adjoin_simple_self K _)`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _), hK, IntermediateField.top_toSubalgebra]`. Establish `key : ∀ n : ℕ, ∀ w ∈ I ^ n, ∃ t ∈ Ideal.span S ^ n, algebraMap (𝓞 L) L t * z ^ n = algebraMap K L w`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `w hw`. Rewrite `hw` using `[pow_zero, Submodule.mem_one]`. Take `⟨r, rfl⟩` from `hw`. Use `⟨algebraMap (𝓞 K) (𝓞 L) r, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, mul_one, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, ← IsScalarTower.algebraMap_apply (𝓞 K) K L]`.

Consider the case `succ n ih`. Introduce `w hw`. Rewrite `hw` using `[pow_succ]`. Use `Submodule.mul_induction_on (C := fun w => ∃ t ∈ Ideal.span S ^ (n + 1), algebraMap (𝓞 L) L t * z ^ (n + 1) = algebraMap K L w) hw ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Take `⟨t, ht, hta⟩` from `ih a ha`. Distinguish the cases in `hb0 : b = 0`. Conclude with `⟨0, zero_mem _, by simp [hb0]⟩`. Take `⟨β, hβ⟩` from `hquot b hb`. Use `⟨t * β, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul ht (Ideal.subset_span ⟨b, hb, hb0, hβ⟩)`. Rewrite using `[map_mul, map_mul, pow_succ, ← hta, ← hβ]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `x x' ⟨t, ht, htx⟩ ⟨t', ht', htx'⟩`.

Conclude with `⟨t + t', add_mem ht ht', by rw [map_add, add_mul, htx, htx', map_add]⟩`. Establish `hspan : Ideal.span S = ⊤`. Establish `hyk : y ∈ I ^ k`. Rewrite using `[hI]`. Conclude with `Submodule.mem_span_singleton_self y`.

Take `⟨t, ht, htz⟩` from `key k y hyk`. Establish `ht1 : t = 1`. Apply `FaithfulSMul.algebraMap_injective (𝓞 L) L` to reduce the goal to its premises. Rewrite using `[map_one]`. Use `mul_right_cancel₀ hzk ?_` and prove the remaining obligations.

Rewrite using `[htz, hz, one_mul]`. Rewrite using `[Ideal.eq_top_iff_one]`. Conclude with `Ideal.pow_le_self hk.ne' (by rw [← ht1]; exact ht)`. Establish `h1 : (1 : 𝓞 L) ∈ Ideal.span ((fun x => x ^ (k - 1)) '' S)`. Rewrite using `[Ideal.span_pow_eq_top S hspan]`.

Conclude with `Submodule.mem_top`. Establish `hfin` using `Submodule.span_induction (p := fun x _ => (k : 𝓞 L) * x ∈ differentIdeal (𝓞 K) (𝓞 L)) (by rintro _ ⟨β, hβ, rfl⟩; exact hmemS β hβ) (by simp) (fun x x' _ _ hx hx' => by rw [mul_add]; exact add_mem hx hx') (fun a x _ hx => by rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_lef …`. Simplify using `using hfin`.
-/
theorem _root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (k : ℕ) (hk : 0 < k) (y : K) (hy : y ≠ 0) (I : Submodule (𝓞 K) K)
    (hI : I ^ k = Submodule.span (𝓞 K) {y}) (z : L) (hz : z ^ k = algebraMap K L y)
    (hL : Algebra.adjoin K {z} = ⊤) : (k : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hy' : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr hy
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hy' hz.symm
  have hzk : z ^ k ≠ 0 := pow_ne_zero k hz0
  have htop : K⟮z⟯ = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]
    exact IntermediateField.algebra_adjoin_le_adjoin K {z}
  have hpow : ∀ b ∈ I, ∃ r : 𝓞 K, b ^ k = algebraMap (𝓞 K) K r * y := by
    intro b hb
    have hbk : b ^ k ∈ Submodule.span (𝓞 K) {y} := by
      rw [← hI]
      exact Submodule.pow_mem_pow I hb k
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hbk
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  have hquot : ∀ b ∈ I, ∃ β : 𝓞 L, algebraMap (𝓞 L) L β * z = algebraMap K L b := by
    intro b hb
    obtain ⟨r, hr⟩ := hpow b hb
    have hint : IsIntegral ℤ (algebraMap K L b / z) := by
      refine IsIntegral.of_pow hk ?_
      have hq : (algebraMap K L b / z) ^ k = algebraMap K L (algebraMap (𝓞 K) K r) := by
        rw [div_pow, ← map_pow, hr, map_mul, hz, mul_div_cancel_right₀ _ hy']
      rw [hq]
      exact (RingOfIntegers.isIntegral_coe r).algebraMap
    exact ⟨⟨_, hint⟩, div_mul_cancel₀ _ hz0⟩
  set S : Set (𝓞 L) :=
    {β | ∃ b ∈ I, b ≠ 0 ∧ algebraMap (𝓞 L) L β * z = algebraMap K L b} with hS
  have hmemS : ∀ β ∈ S, (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    rintro β ⟨b, hb, hb0, hβb⟩
    obtain ⟨r, hr⟩ := hpow b hb
    have hβ0 : algebraMap (𝓞 L) L β ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hβb
      exact hb0 ((map_eq_zero _).mp hβb.symm)
    refine natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq k β r ?_ ?_
    · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_pow, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L]
      refine mul_right_cancel₀ hzk ?_
      rw [← mul_pow, hβb, ← map_pow, hr, map_mul, hz]
    · have hK : K⟮algebraMap (𝓞 L) L β⟯ = ⊤ := by
        rw [eq_top_iff, ← htop, IntermediateField.adjoin_simple_le_iff]
        have hzeq : z = algebraMap K L b / algebraMap (𝓞 L) L β := by
          rw [← hβb, mul_div_cancel_left₀ _ hβ0]
        rw [hzeq]
        exact div_mem (IntermediateField.algebraMap_mem _ b)
          (IntermediateField.mem_adjoin_simple_self K _)
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic _), hK, IntermediateField.top_toSubalgebra]
  have key : ∀ n : ℕ, ∀ w ∈ I ^ n, ∃ t ∈ Ideal.span S ^ n,
      algebraMap (𝓞 L) L t * z ^ n = algebraMap K L w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [pow_zero, Submodule.mem_one] at hw
      obtain ⟨r, rfl⟩ := hw
      refine ⟨algebraMap (𝓞 K) (𝓞 L) r, by simp, ?_⟩
      rw [pow_zero, mul_one, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    | succ n ih =>
      intro w hw
      rw [pow_succ] at hw
      refine Submodule.mul_induction_on (C := fun w => ∃ t ∈ Ideal.span S ^ (n + 1),
        algebraMap (𝓞 L) L t * z ^ (n + 1) = algebraMap K L w) hw ?_ ?_
      · intro a ha b hb
        obtain ⟨t, ht, hta⟩ := ih a ha
        by_cases hb0 : b = 0
        · exact ⟨0, zero_mem _, by simp [hb0]⟩
        obtain ⟨β, hβ⟩ := hquot b hb
        refine ⟨t * β, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul ht (Ideal.subset_span ⟨b, hb, hb0, hβ⟩)
        · rw [map_mul, map_mul, pow_succ, ← hta, ← hβ]
          ring
      · rintro x x' ⟨t, ht, htx⟩ ⟨t', ht', htx'⟩
        exact ⟨t + t', add_mem ht ht', by rw [map_add, add_mul, htx, htx', map_add]⟩
  have hspan : Ideal.span S = ⊤ := by
    have hyk : y ∈ I ^ k := by
      rw [hI]
      exact Submodule.mem_span_singleton_self y
    obtain ⟨t, ht, htz⟩ := key k y hyk
    have ht1 : t = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_one]
      refine mul_right_cancel₀ hzk ?_
      rw [htz, hz, one_mul]
    rw [Ideal.eq_top_iff_one]
    exact Ideal.pow_le_self hk.ne' (by rw [← ht1]; exact ht)
  have h1 : (1 : 𝓞 L) ∈ Ideal.span ((fun x => x ^ (k - 1)) '' S) := by
    rw [Ideal.span_pow_eq_top S hspan]
    exact Submodule.mem_top
  have hfin := Submodule.span_induction
    (p := fun x _ => (k : 𝓞 L) * x ∈ differentIdeal (𝓞 K) (𝓞 L))
    (by rintro _ ⟨β, hβ, rfl⟩; exact hmemS β hβ) (by simp)
    (fun x x' _ _ hx hx' => by rw [mul_add]; exact add_mem hx hx')
    (fun a x _ hx => by rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ a hx) h1
  simpa using hfin

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField nonZeroDivisors in

/- English proof (translation)
Introduce `F a b k y I z hF hk hy hI hz`. Unfold `_root_.GlobalTheory.FieldSize.Sz at hF ⊢`. Take `⟨hfd, hdeg, hdisc⟩` from `hF`. Establish `hyint : IsIntegral ℚ (y : ℂ)` using `(Algebra.IsIntegral.isIntegral y).map F.val`. Establish `hzint : IsIntegral ℚ z` using `IsIntegral.of_pow hk (by rw [hz]; exact hyint)`.

Use `haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzint`. Use `haveI hEfd : FiniteDimensional ℚ ↥(F ⊔ ℚ⟮z⟯) := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯`. Use `set E := F ⊔ ℚ⟮z⟯ with hE`. Use `haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfd }`. Use `haveI : NumberField E := { to_charZero := inferInstance, to_finiteDimensional := hEfd }`.

Establish `hle : F ≤ E` using `le_sup_left`. Use `letI : Algebra F E := (IntermediateField.inclusion hle).toAlgebra`. Set `z' : E` to `⟨z, (le_sup_right : ℚ⟮z⟯ ≤ E) (IntermediateField.mem_adjoin_simple_self ℚ z)⟩`. Establish `hz' : z' ^ k = algebraMap F E y` using `Subtype.ext (by rw [IntermediateField.coe_pow]; exact hz)`. Establish `hzF : IsIntegral F z` using `IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap)`.

Set `φ : E →ₐ[F] ℂ` to `{ E.val with commutes' := fun _ => rfl }`. Establish `hL : Algebra.adjoin F {z'} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `hw : (w : ℂ) ∈ Algebra.adjoin F {z}`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzF.isAlgebraic]`. Establish `hwr : (w : ℂ) ∈ (IntermediateField.adjoin F {z}).restrictScalars ℚ`. Establish `h` using `IntermediateField.restrictScalars_adjoin_eq_sup ℚ F {z}`. Rewrite `h` using `[SetLike.ext_iff]`. Conclude with `(h _).mpr w.2`.

Conclude with `hwr`. Establish `hmap : Algebra.adjoin F {z} = (Algebra.adjoin F {z'}).map φ`. Rewrite using `[AlgHom.map_adjoin, Set.image_singleton]`. Both sides reduce to the same expression. Rewrite `hw` using `[hmap]`.

Take `⟨w', hw', hww⟩` from `hw`. Establish `hw'w : w' = w` using `Subtype.val_injective hww`. Conclude with `hw'w ▸ hw'`. Establish `hdiff` using `_root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy I hI z' hz' hL`. Establish `hroot` using `_root_.GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal F E k hk hdiff`.

Establish `hFE : IntermediateField.adjoin F {z'} = ⊤`. Rewrite using `[← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]`. Conclude with `IntermediateField.algebra_adjoin_le_adjoin F {z'}`. Establish `hz'int : IsIntegral F z'` using `IsIntegral.of_pow hk (by rw [hz']; exact isIntegral_algebraMap)`. Establish `hdegFE : Module.finrank F E ≤ k`.

Establish `h1` using `IntermediateField.adjoin.finrank hz'int`. Rewrite `h1` using `[hFE, IntermediateField.finrank_top']`. Rewrite using `[h1]`. Establish `hp : (X ^ k - C y : F[X]) ≠ 0` using `X_pow_sub_C_ne_zero hk y`. Combine the equalities or inequalities in the displayed calculation.

Use `haveI : FiniteDimensional F E := FiniteDimensional.right ℚ F E`. Establish `hdF : 0 < Module.finrank ℚ F` using `Module.finrank_pos`. Establish `hdFE : 0 < Module.finrank F E` using `Module.finrank_pos`. Establish `htower : Module.finrank ℚ E = Module.finrank ℚ F * Module.finrank F E` using `(Module.finrank_mul_finrank ℚ F E).symm`. Use `⟨hEfd, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[htower, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]`. Conclude with `add_le_add hdeg (Real.log_le_log (by positivity) (by exact_mod_cast hdegFE))`. Conclude with `hroot.trans (add_le_add hdisc le_rfl)`.
-/
theorem _root_.GlobalTheory.FieldSize.sz_sup_adjoin_root : ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ) (k : ℕ) (y : F) (I : Submodule (𝓞 F) F) (z : ℂ), _root_.GlobalTheory.FieldSize.Sz F a b → 0 < k → y ≠ 0 → I ^ k = Submodule.span (𝓞 F) {y} → z ^ k = (y : ℂ) → _root_.GlobalTheory.FieldSize.Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  intro F a b k y I z hF hk hy hI hz
  unfold _root_.GlobalTheory.FieldSize.Sz at hF ⊢
  obtain ⟨hfd, hdeg, hdisc⟩ := hF
  have hyint : IsIntegral ℚ (y : ℂ) := (Algebra.IsIntegral.isIntegral y).map F.val
  have hzint : IsIntegral ℚ z := IsIntegral.of_pow hk (by rw [hz]; exact hyint)
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzint
  haveI hEfd : FiniteDimensional ℚ ↥(F ⊔ ℚ⟮z⟯) := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  set E := F ⊔ ℚ⟮z⟯ with hE
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  haveI : NumberField E := { to_charZero := inferInstance, to_finiteDimensional := hEfd }
  have hle : F ≤ E := le_sup_left
  letI : Algebra F E := (IntermediateField.inclusion hle).toAlgebra
  let z' : E := ⟨z, (le_sup_right : ℚ⟮z⟯ ≤ E) (IntermediateField.mem_adjoin_simple_self ℚ z)⟩
  have hz' : z' ^ k = algebraMap F E y :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hz)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap)
  let φ : E →ₐ[F] ℂ := { E.val with commutes' := fun _ => rfl }
  have hL : Algebra.adjoin F {z'} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : (w : ℂ) ∈ Algebra.adjoin F {z} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzF.isAlgebraic]
      have hwr : (w : ℂ) ∈ (IntermediateField.adjoin F {z}).restrictScalars ℚ := by
        have h := IntermediateField.restrictScalars_adjoin_eq_sup ℚ F {z}
        rw [SetLike.ext_iff] at h
        exact (h _).mpr w.2
      exact hwr
    have hmap : Algebra.adjoin F {z} = (Algebra.adjoin F {z'}).map φ := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [hmap] at hw
    obtain ⟨w', hw', hww⟩ := hw
    have hw'w : w' = w := Subtype.val_injective hww
    exact hw'w ▸ hw'
  have hdiff := _root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy I hI z' hz' hL
  have hroot := _root_.GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal F E k hk hdiff
  have hFE : IntermediateField.adjoin F {z'} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]
    exact IntermediateField.algebra_adjoin_le_adjoin F {z'}
  have hz'int : IsIntegral F z' := IsIntegral.of_pow hk (by rw [hz']; exact isIntegral_algebraMap)
  have hdegFE : Module.finrank F E ≤ k := by
    have h1 := IntermediateField.adjoin.finrank hz'int
    rw [hFE, IntermediateField.finrank_top'] at h1
    rw [h1]
    have hp : (X ^ k - C y : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hk y
    calc (minpoly F z').natDegree ≤ (X ^ k - C y : F[X]).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd F z' (by simp [hz'])) hp
      _ = k := natDegree_X_pow_sub_C
  haveI : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  have hdF : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hdFE : 0 < Module.finrank F E := Module.finrank_pos
  have htower : Module.finrank ℚ E = Module.finrank ℚ F * Module.finrank F E :=
    (Module.finrank_mul_finrank ℚ F E).symm
  refine ⟨hEfd, ?_, ?_⟩
  · rw [htower, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    exact add_le_add hdeg (Real.log_le_log (by positivity) (by exact_mod_cast hdegFE))
  · exact hroot.trans (add_le_add hdisc le_rfl)

end GlobalTheory.FieldSize
