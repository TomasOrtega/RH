import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHomStatement

set_option autoImplicit false
open NumberField

namespace GlobalTheory.PicDom

/- English proof (translation)
Establish `h` using `Ideal.comap_ne_bot_of_integral_mem hd (Ideal.mem_span_singleton_self d) (Algebra.IsIntegral.isIntegral (R := ℤ) d)`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Conclude with `⟨a, ha0, by simpa using ha⟩`.
-/
theorem exists_int_mem_span {B : Type} [CommRing B] [IsDomain B] [Algebra.IsIntegral ℤ B] {d : B} (hd : d ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : B) ∈ Ideal.span {d} := by
  have h := Ideal.comap_ne_bot_of_integral_mem hd (Ideal.mem_span_singleton_self d)
    (Algebra.IsIntegral.isIntegral (R := ℤ) d)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨a, ha0, by simpa using ha⟩

/- English proof (translation)
Establish `hp : ringChar B ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises. Establish `: CharP B 0` using `h ▸ ringChar.charP B`. Conclude with `CharP.charP_to_charZero B`.

Establish `hfin : Finite B` using `Module.finite_of_fg_torsion B fun x => ⟨⟨(ringChar B : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, by`. Express the relevant statement in the definitionally equal form `((ringChar B : ℤ)) • x = 0`. Rewrite using `[zsmul_eq_mul, Int.cast_natCast, ringChar.Nat.cast_ringChar, zero_mul]⟩`. Conclude with `isOfFinOrder_of_finite M`.
-/
theorem isOfFinOrder_of_not_charZero (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (hc : ¬ CharZero B) (M : CommRing.Pic B) : IsOfFinOrder M := by
  have hp : ringChar B ≠ 0 := by
    intro h
    apply hc
    have : CharP B 0 := h ▸ ringChar.charP B
    exact CharP.charP_to_charZero B
  have hfin : Finite B := Module.finite_of_fg_torsion B fun x =>
    ⟨⟨(ringChar B : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, by
      change ((ringChar B : ℤ)) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, ringChar.Nat.cast_ringChar, zero_mul]⟩
  exact isOfFinOrder_of_finite M

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := B)`. Establish `key : ∀ y : B, algebraMap B K y ∈ Submodule.span ℚ (algebraMap B K '' (s : Set B))` using `fun y => by`. Establish `hy : y ∈ Submodule.span ℤ (s : Set B)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_zsmul]`. Conclude with `zsmul_mem hx a`.

Use `Module.finite_def.2 ⟨s.image (algebraMap B K), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, eq_top_iff]`. Introduce `x _`. Take `⟨b, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := B) x`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`.

Take `⟨a, ha0, ha⟩` from `exists_int_mem_span hd0`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 ha`. Establish `hdK : algebraMap B K d ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]` and apply the resulting hypothesis. Establish `haK : (a : K) ≠ 0` using `by exact_mod_cast ha0`.

Establish `: algebraMap B K b / algebraMap B K d = ((a : ℚ)⁻¹) • algebraMap B K (c * b)`. Rewrite using `[Rat.smul_def, map_mul, Rat.cast_inv, Rat.cast_intCast]`. Establish `h2 : (a : K) = algebraMap B K c * algebraMap B K d`. Rewrite using `[← map_mul, hc, map_intCast]`. Establish `hcK : algebraMap B K c ≠ 0`.

Introduce `h`. Apply `haK` to reduce the goal to its premises. Rewrite using `[h2, h, zero_mul]`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (key _)`.
-/
theorem finiteDimensional_of_isFractionRing (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K] :
    FiniteDimensional ℚ K := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have key : ∀ y : B, algebraMap B K y ∈
      Submodule.span ℚ (algebraMap B K '' (s : Set B)) := fun y => by
    have hy : y ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
  classical
  refine Module.finite_def.2 ⟨s.image (algebraMap B K), ?_⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  have hdK : algebraMap B K d ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
  have : algebraMap B K b / algebraMap B K d =
      ((a : ℚ)⁻¹) • algebraMap B K (c * b) := by
    rw [Rat.smul_def, map_mul, Rat.cast_inv, Rat.cast_intCast]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    have hcK : algebraMap B K c ≠ 0 := by
      intro h; apply haK; rw [h2, h, zero_mul]
    rw [h2]
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (key _)

end GlobalTheory.PicDom

namespace GlobalTheory.PicDom

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

/- English proof (translation)
Set `φ : B →+* 𝓞 K` to `{ toFun := fun b => ⟨algebraMap B K b, (Algebra.IsIntegral.isIntegral (R := ℤ) b).algebraMap⟩ map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero] map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one] map_add' := fun x y => by ext; simp only [RingOfIntegers.m …`. Establish `hφ : ∀ b, ((φ b : 𝓞 K) : K) = algebraMap B K b` using `fun b => rfl`. Establish `hinj : Function.Injective φ` using `fun x y h => IsFractionRing.injective B K (by`. Rewrite using `[← hφ, ← hφ, h])`. Establish `hmul : ∀ ω : 𝓞 K, ∃ a : ℤ, a ≠ 0 ∧ (a : 𝓞 K) * ω ∈ φ.range` using `fun ω => by`.

Take `⟨b, d, hd, hbd⟩` from `IsFractionRing.div_surjective (A := B) (ω : K)`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Take `⟨a, ha0, ha⟩` from `exists_int_mem_span hd0`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 ha`. Establish `hdK : algebraMap B K d ≠ 0`.

Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]` and apply the resulting hypothesis. Use `⟨a, ha0, c * b, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hφ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, ← hbd]`. Establish `h2 : (a : K) = algebraMap B K c * algebraMap B K d`.

Rewrite using `[← map_mul, hc, map_intCast]`. Rewrite using `[h2, mul_assoc]`. Use `congr 1`. Conclude with `(mul_div_cancel₀ _ hdK).symm`. Use `choose a ha0 ha using hmul`.

Take `⟨t, ht⟩` from `Module.Finite.fg_top (R := ℤ) (M := 𝓞 K)`. Use `set N : ℤ := ∏ ω ∈ t, a ω`. Establish `hN0 : N ≠ 0` using `Finset.prod_ne_zero_iff.2 fun ω _ => ha0 ω`. Establish `hNmem : ∀ x : 𝓞 K, (N : 𝓞 K) * x ∈ φ.range` using `fun x => by`. Establish `hx : x ∈ Submodule.span ℤ (t : Set (𝓞 K))` using `ht ▸ Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem ω hω => show ((∏ ω ∈ t, a ω : ℤ) : 𝓞 K) * ω ∈ φ.range`. Rewrite using `[← Finset.mul_prod_erase t a (Finset.mem_coe.1 hω), Int.cast_mul, mul_comm (a ω : 𝓞 K), mul_assoc]`. Conclude with `mul_mem (intCast_mem _ _) (ha ω)`. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul k x _ hx => rw [mul_smul_comm]`. Conclude with `zsmul_mem hx k`.

Establish `hn0 : N.natAbs ≠ 0` using `Int.natAbs_ne_zero.2 hN0`. Establish `hcond : ∀ x : 𝓞 K, ((N.natAbs : ℕ) : 𝓞 K) * x ∈ φ.range` using `fun x => by`. Break down `Int.natAbs_eq N with h | h` into its components or cases. Use `hNmem x` as an intermediate fact. Rewrite `this` using `[h, Int.cast_natCast]`. Then use the resulting hypothesis.

Use `neg_mem (hNmem x)` as an intermediate fact. Rewrite `this` using `[h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]`. Then use the resulting hypothesis. Use `haveI : Finite (CommRing.Pic (𝓞 K)) := Finite.of_equiv _ (ClassGroup.equivPic (𝓞 K)).toEquiv`. Conclude with `GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B (𝓞 K) φ N.natAbs hinj hn0 hcond M (isOfFinOrder_of_finite _)`.
-/
theorem isOfFinOrder_of_numberField (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [NumberField K]
    (M : CommRing.Pic B) : IsOfFinOrder M := by
  let φ : B →+* 𝓞 K :=
    { toFun := fun b => ⟨algebraMap B K b, (Algebra.IsIntegral.isIntegral (R := ℤ) b).algebraMap⟩
      map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
      map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
      map_add' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_add]; rfl
      map_mul' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_mul]; rfl }
  have hφ : ∀ b, ((φ b : 𝓞 K) : K) = algebraMap B K b := fun b => rfl
  have hinj : Function.Injective φ := fun x y h => IsFractionRing.injective B K (by
    rw [← hφ, ← hφ, h])

  have hmul : ∀ ω : 𝓞 K, ∃ a : ℤ, a ≠ 0 ∧ (a : 𝓞 K) * ω ∈ φ.range := fun ω => by
    obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := B) (ω : K)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have hdK : algebraMap B K d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
    refine ⟨a, ha0, c * b, ?_⟩
    apply RingOfIntegers.ext
    rw [hφ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, ← hbd]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    rw [h2, mul_assoc]
    congr 1
    exact (mul_div_cancel₀ _ hdK).symm
  classical
  choose a ha0 ha using hmul
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 K)
  set N : ℤ := ∏ ω ∈ t, a ω
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun ω _ => ha0 ω
  have hNmem : ∀ x : 𝓞 K, (N : 𝓞 K) * x ∈ φ.range := fun x => by
    have hx : x ∈ Submodule.span ℤ (t : Set (𝓞 K)) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem ω hω =>
      show ((∏ ω ∈ t, a ω : ℤ) : 𝓞 K) * ω ∈ φ.range
      rw [← Finset.mul_prod_erase t a (Finset.mem_coe.1 hω), Int.cast_mul, mul_comm (a ω : 𝓞 K), mul_assoc]
      exact mul_mem (intCast_mem _ _) (ha ω)
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact zsmul_mem hx k
  have hn0 : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN0
  have hcond : ∀ x : 𝓞 K, ((N.natAbs : ℕ) : 𝓞 K) * x ∈ φ.range := fun x => by
    rcases Int.natAbs_eq N with h | h
    · have := hNmem x
      rwa [h, Int.cast_natCast] at this
    · have := neg_mem (hNmem x)
      rwa [h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
  haveI : Finite (CommRing.Pic (𝓞 K)) := Finite.of_equiv _ (ClassGroup.equivPic (𝓞 K)).toEquiv
  exact GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B (𝓞 K) φ N.natAbs hinj hn0 hcond M (isOfFinOrder_of_finite _)

/- English proof (translation)
Use `haveI : CharZero (FractionRing B) := IsFractionRing.charZero_of_isFractionRing B`. Use `haveI : FiniteDimensional ℚ (FractionRing B) := finiteDimensional_of_isFractionRing B (FractionRing B)`. Use `haveI : NumberField (FractionRing B) := ⟨⟩`. Conclude with `isOfFinOrder_of_numberField B (FractionRing B) M`.
-/
theorem isOfFinOrder_of_charZero (M : CommRing.Pic B) : IsOfFinOrder M := by
  haveI : CharZero (FractionRing B) := IsFractionRing.charZero_of_isFractionRing B
  haveI : FiniteDimensional ℚ (FractionRing B) := finiteDimensional_of_isFractionRing B (FractionRing B)
  haveI : NumberField (FractionRing B) := ⟨⟩
  exact isOfFinOrder_of_numberField B (FractionRing B) M

end GlobalTheory.PicDom

/- English proof (translation)
Introduce `B _ _ _ M`. Distinguish the cases in `hc : CharZero B`. Conclude with `GlobalTheory.PicDom.isOfFinOrder_of_charZero B M`. Conclude with `GlobalTheory.PicDom.isOfFinOrder_of_not_charZero B hc M`.
-/
theorem GlobalTheory.pic_isOfFinOrder_of_finite_int : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (M : CommRing.Pic B), IsOfFinOrder M := by
  intro B _ _ _ M
  by_cases hc : CharZero B
  · exact GlobalTheory.PicDom.isOfFinOrder_of_charZero B M
  · exact GlobalTheory.PicDom.isOfFinOrder_of_not_charZero B hc M
