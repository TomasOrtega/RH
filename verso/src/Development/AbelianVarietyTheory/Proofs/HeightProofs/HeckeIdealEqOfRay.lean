import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize.RayDegree

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R}

/- English proof (translation)
The claim follows from `Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩`.
-/
theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m :=
  Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩

/- English proof (translation)
Distinguish the cases in `ht : m = ⊤`. Take `⟨a, haI, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI0`. Conclude with `⟨a, haI, ha0, by simp [ht]⟩`. Take `⟨a, ha, b, hb, hab⟩` from `Ideal.isCoprime_iff_exists.mp h`. Establish `h1 : a - 1 ∈ m`.

Establish `: a - 1 = -b` using `by rw [← hab]; ring`. Rewrite using `[this]`. Conclude with `m.neg_mem hb`. Use `⟨a, ha, ?_, h1⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Apply `ht` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using m.neg_mem h1`.
-/
theorem exists_mem_sub_one {I : Ideal R} (hI0 : I ≠ ⊥) (h : IsCoprime I m) : ∃ a ∈ I, a ≠ 0 ∧ a - 1 ∈ m := by
  by_cases ht : m = ⊤
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    exact ⟨a, haI, ha0, by simp [ht]⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  have h1 : a - 1 ∈ m := by
    have : a - 1 = -b := by rw [← hab]; ring
    rw [this]
    exact m.neg_mem hb
  refine ⟨a, ha, ?_, h1⟩
  rintro rfl
  apply ht
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem h1

/- English proof (translation)
Take `⟨a, haJ, ha0, ha⟩` from `exists_mem_sub_one hJ0 hJ`. Establish `h1 : y * a ∈ Ideal.span {x} * I`. Rewrite using `[h]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ`. Take `⟨b, -, hb⟩` from `Ideal.mem_span_singleton_mul.mp h1`.

Establish `h2 : Ideal.span {a} * I = Ideal.span {b} * J`. Establish `hy' : (Ideal.span {y} : Ideal R) ≠ 0` using `by simpa using hy`. Apply `mul_left_cancel₀ hy'` to reduce the goal to its premises. Rewrite using `[← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm b x]`. Use `⟨a, b, ha0, ?_, ha, ?_, h2⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Simplify using `[ha0, hI0] at h2`. Use `(isCoprime_span ha).mul_left hI` as an intermediate fact. Rewrite `this` using `[h2]`. Conclude with `this.of_mul_left_left`.
-/
theorem exists_good {I J : Ideal R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : IsCoprime I m) (hJ : IsCoprime J m)
    {x y : R} (hy : y ≠ 0) (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ m ∧ IsCoprime (Ideal.span {b}) m ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have h1 : y * a ∈ Ideal.span {x} * I := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ
  obtain ⟨b, -, hb⟩ := Ideal.mem_span_singleton_mul.mp h1
  have h2 : Ideal.span {a} * I = Ideal.span {b} * J := by
    have hy' : (Ideal.span {y} : Ideal R) ≠ 0 := by simpa using hy
    apply mul_left_cancel₀ hy'
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, mul_comm b x]
  refine ⟨a, b, ha0, ?_, ha, ?_, h2⟩
  · rintro rfl
    simp [ha0, hI0] at h2
  · have := (isCoprime_span ha).mul_left hI
    rw [h2] at this
    exact this.of_mul_left_left

end General

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

/- English proof (translation)
Simplify using `using ha`.
-/
theorem emb_ne_zero (φ : K →+* ℝ) {a : 𝓞 K} (ha : a ≠ 0) : φ (a : K) ≠ 0 := by
  simpa using ha

/- English proof (translation)
Take `⟨a, haJ, ha0, ha⟩` from `exists_mem_sub_one hJ0 hJ`. Establish `ha2 : a * a - 1 ∈ 𝔮`. Establish `: a * a - 1 = (a + 1) * (a - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `𝔮.mul_mem_left _ ha`.

Take `⟨M, hM⟩ : J ∣ Ideal.span {a * a}` from `Ideal.dvd_span_singleton.mpr (J.mul_mem_left _ haJ)`. Establish `hM' : IsCoprime M 𝔮`. Use `isCoprime_span ha2` as an intermediate fact. Rewrite `this` using `[hM]`. Conclude with `this.of_mul_left_right`.

Establish `hM0 : M ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `[ha0] at hM`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hp`. Establish `e1 : heckeIdeal L χ (J * M) = 1`.

Use `(hR.2.2 _ (mul_ne_zero hJ0 hM0) (hJ.mul_left hM')).2 ⟨a * a, 1, ⟨mul_ne_zero ha0 ha0, one_ne_zero, isCoprime_span ha2, isCoprime_span (by simp), ha2, fun φ => ?_⟩, by simp [hM]⟩ χ` and prove the remaining obligations. Use `mul_self_pos.2 (emb_ne_zero φ ha0)` as an intermediate fact. Simplify using `using this`. Establish `e2 : heckeIdeal L χ (I * M) = 1`. Use `(hR.2.2 _ (mul_ne_zero hI0 hM0) (hI.mul_left hM')).2 ⟨a * a * α, β, ⟨mul_ne_zero (mul_ne_zero ha0 ha0) h1, h2, ?_, h4, ?_, fun φ => ?_⟩, ?_⟩ χ` and prove the remaining obligations.

Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`. Conclude with `(isCoprime_span ha2).mul_left h3`. Establish `: a * a * α - β = α * (a * a - 1) + (α - β)` using `by ring`. Rewrite using `[this]`. Conclude with `𝔮.add_mem (𝔮.mul_mem_left _ ha2) h5`.

Use `mul_pos (mul_self_pos.2 (emb_ne_zero φ ha0)) (h6 φ)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[mul_right_comm, h, mul_right_comm, ← hM, Ideal.span_singleton_mul_span_singleton]`. Rewrite `e1` using `[GlobalTheory.NT.Model.heckeIdeal_mul L χ hJ0 hM0]`. Rewrite `e2` using `[GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hM0]`.

Conclude with `mul_right_cancel₀ (right_ne_zero_of_mul_eq_one e1) (e2.trans e1.symm)`.
-/
theorem heckeIdeal_eq_of_ray (hR : IsRay L 𝔮) {I J : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : IsCoprime I 𝔮) (hJ : IsCoprime J 𝔮) {α β : 𝓞 K} (hp : RayPair 𝔮 α β)
    (h : I * Ideal.span {β} = J * Ideal.span {α}) (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    heckeIdeal L χ I = heckeIdeal L χ J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have ha2 : a * a - 1 ∈ 𝔮 := by
    have : a * a - 1 = (a + 1) * (a - 1) := by ring
    rw [this]; exact 𝔮.mul_mem_left _ ha
  obtain ⟨M, hM⟩ : J ∣ Ideal.span {a * a} := Ideal.dvd_span_singleton.mpr (J.mul_mem_left _ haJ)
  have hM' : IsCoprime M 𝔮 := by
    have := isCoprime_span ha2
    rw [hM] at this
    exact this.of_mul_left_right
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    simp [ha0] at hM
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  have e1 : heckeIdeal L χ (J * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hJ0 hM0) (hJ.mul_left hM')).2 ⟨a * a, 1, ⟨mul_ne_zero ha0 ha0, one_ne_zero,
      isCoprime_span ha2, isCoprime_span (by simp), ha2, fun φ => ?_⟩, by simp [hM]⟩ χ
    have := mul_self_pos.2 (emb_ne_zero φ ha0)
    simpa using this
  have e2 : heckeIdeal L χ (I * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hI0 hM0) (hI.mul_left hM')).2 ⟨a * a * α, β,
      ⟨mul_ne_zero (mul_ne_zero ha0 ha0) h1, h2, ?_, h4, ?_, fun φ => ?_⟩, ?_⟩ χ
    · rw [← Ideal.span_singleton_mul_span_singleton]
      exact (isCoprime_span ha2).mul_left h3
    · have : a * a * α - β = α * (a * a - 1) + (α - β) := by ring
      rw [this]
      exact 𝔮.add_mem (𝔮.mul_mem_left _ ha2) h5
    · have := mul_pos (mul_self_pos.2 (emb_ne_zero φ ha0)) (h6 φ)
      simpa [mul_assoc] using this
    · rw [mul_right_comm, h, mul_right_comm, ← hM, Ideal.span_singleton_mul_span_singleton]
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hJ0 hM0] at e1
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hM0] at e2
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one e1) (e2.trans e1.symm)

/- English proof (translation)
Set `S : Submonoid (L ≃ₐ[K] L)` to `{ carrier := {σ | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧ ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ)} one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩ mul_mem' := by`. Introduce and unpack `x y ⟨I, hI0, hI, hx⟩ ⟨J, hJ0, hJ, hy⟩`. Use `⟨I * J, mul_ne_zero hI0 hJ0, hI.mul_left hJ, fun χ => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hJ0, hx, hy]`. Simplify using `}`.

Establish `hσ : σ ∈ Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ}`. Rewrite using `[hR.2.1]`. Discharge the goal by the elementary cases of `trivial`. Express the relevant statement in the definitionally equal form `σ ∈ S`. Proceed by induction on `hσ using Subgroup.closure_induction with`.

Consider the case `mem x hx`. Take `⟨v, hv, hx⟩` from `hx`. Use `⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`.

Conclude with `hv (Ideal.dvd_iff_le.2 (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge))`. Rewrite using `[GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hR.1 v hv) hx]`. Consider the case `one => exact S.one_mem`. Consider the case `mul x y _ _ hx hy => exact S.mul_mem hx hy`. Consider the case `inv x _ hx`.

Establish `: x⁻¹ = x ^ (orderOf x - 1)`. Rewrite using `[inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]`. Rewrite using `[this]`. Conclude with `S.pow_mem hx _`.
-/
theorem exists_ideal [IsGalois K L] (hR : IsRay L 𝔮) (σ : L ≃ₐ[K] L) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧ ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  let S : Submonoid (L ≃ₐ[K] L) :=
    { carrier := {σ | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ)}
      one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI0, hI, hx⟩ ⟨J, hJ0, hJ, hy⟩
        refine ⟨I * J, mul_ne_zero hI0 hJ0, hI.mul_left hJ, fun χ => ?_⟩
        rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hJ0, hx, hy]; simp }
  have hσ : σ ∈ Subgroup.closure
      {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ} := by
    rw [hR.2.1]; trivial
  change σ ∈ S
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, hx⟩ := hx
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hv (Ideal.dvd_iff_le.2 (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge))
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hR.1 v hv) hx]
  | one => exact S.one_mem
  | mul x y _ _ hx hy => exact S.mul_mem hx hy
  | inv x _ hx =>
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [this]
    exact S.pow_mem hx _

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ 𝔮 h𝔮 hR`. Use `choose s hs0 hs hsx using exists_ideal hR`. Set `cl : (L ≃ₐ[K] L) → ClassGroup (𝓞 K)` to `fun x => ClassGroup.mk0 ⟨s x, mem_nonZeroDivisors_of_ne_zero (hs0 x)⟩`. Establish `key : ∀ x, ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ 𝔮 ∧ IsCoprime (Ideal.span {b}) 𝔮 ∧ Ideal.span {a} * s x = Ideal.span {b} * s (Function.invFun cl (cl x))`. Introduce `x`.

Establish `h : cl x = cl (Function.invFun cl (cl x))` using `(Function.invFun_eq ⟨x, rfl⟩).symm`. Take `⟨a, b, -, hb, hxy⟩` from `ClassGroup.mk0_eq_mk0_iff.mp h`. Conclude with `exists_good (hs0 x) (hs0 _) (hs x) (hs _) hb hxy`. Use `choose a b ha0 hb0 ha hb hab using key`. Set `F : (L ≃ₐ[K] L) → (ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮)) × ((K →+* ℝ) → Prop)` to `fun x => ((cl x, Ideal.Quotient.mk 𝔮 (b x)), fun φ => 0 < φ (a x : K) * φ (b x : K))`.

Establish `hF : Function.Injective F`. Introduce `x y hxy`. Take `⟨h12, h3⟩` from `Prod.mk.inj hxy`. Take `⟨h1, h2⟩` from `Prod.mk.inj h12`. Rewrite `h2` using `[Ideal.Quotient.eq]`.

Establish `hp : RayPair 𝔮 (b x * a y) (a x * b y)`. Use `⟨mul_ne_zero (hb0 x) (ha0 y), mul_ne_zero (ha0 x) (hb0 y), ?_, ?_, ?_, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`. Conclude with `(hb x).mul_left (isCoprime_span (ha y))`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`.

Conclude with `(isCoprime_span (ha x)).mul_left (hb y)`. Establish `: b x * a y - a x * b y = b x * (a y - 1) - b y * (a x - 1) + (b x - b y)` using `by ring`. Rewrite using `[this]`. Conclude with `𝔮.add_mem (𝔮.sub_mem (𝔮.mul_mem_left _ (ha y)) (𝔮.mul_mem_left _ (ha x))) h2`. Establish `h4 : 0 < φ (a x : K) * φ (b x : K) ↔ 0 < φ (a y : K) * φ (b y : K)` using `(congrFun h3 φ).to_iff`.

Establish `h5` using `mul_ne_zero (emb_ne_zero φ (ha0 x)) (emb_ne_zero φ (hb0 x))`. Establish `h6` using `mul_ne_zero (emb_ne_zero φ (ha0 y)) (emb_ne_zero φ (hb0 y))`. Establish `h7 : 0 < (φ (a x : K) * φ (b x : K)) * (φ (a y : K) * φ (b y : K))`. Distinguish the cases in `h : 0 < φ (a x : K) * φ (b x : K)`. Conclude with `mul_pos h (h4.1 h)`.

Conclude with `mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 h) h5) (lt_of_le_of_ne (not_lt.1 fun h' => h (h4.2 h')) h6)`. Use `h7 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `he : s x * Ideal.span {a x * b y} = s y * Ideal.span {b x * a y}`. Establish `e1` using `hab x`. Establish `e2` using `hab y`. Rewrite `e2` using `[← h1]`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, ← mul_assoc, mul_comm (s x), e1, mul_comm (s y), mul_assoc _ _ (s y), e2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ x = χ y` using `fun χ => by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hsx, ← hsx]`. Conclude with `heckeIdeal_eq_of_ray hR (hs0 x) (hs0 y) (hs x) (hs y) hp he χ`.

Assume the negation of the conclusion as `hne`. Use `letI : CommGroup (L ≃ₐ[K] L) := IsMulCommutative.instCommGroup`. Take `⟨χ, h⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ (a := x * y⁻¹) (by rwa [ne_eq, mul_inv_eq_one])`. Apply `h` to reduce the goal to its premises. Rewrite using `[map_mul, map_inv, hχ χ, mul_inv_cancel]`.

Use `haveI : Finite (𝓞 K ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h𝔮`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Use `(Nat.card_le_card_of_injective F hF).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Nat.card_prod, Nat.card_prod, Ideal.absNorm_apply, Submodule.cardQuot_apply, classNumber, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := _ → Prop)]`. Simplify using the standard rewrite rules.
-/
theorem finrank_le : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRay L 𝔮 →
    Module.finrank K L ≤ classNumber K * Ideal.absNorm 𝔮 * 2 ^ Fintype.card (K →+* ℝ) := by
  intro K L _ _ _ _ _ _ 𝔮 h𝔮 hR
  classical
  choose s hs0 hs hsx using exists_ideal hR
  let cl : (L ≃ₐ[K] L) → ClassGroup (𝓞 K) := fun x =>
    ClassGroup.mk0 ⟨s x, mem_nonZeroDivisors_of_ne_zero (hs0 x)⟩
  have key : ∀ x, ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ 𝔮 ∧ IsCoprime (Ideal.span {b}) 𝔮 ∧
      Ideal.span {a} * s x = Ideal.span {b} * s (Function.invFun cl (cl x)) := by
    intro x
    have h : cl x = cl (Function.invFun cl (cl x)) := (Function.invFun_eq ⟨x, rfl⟩).symm
    obtain ⟨a, b, -, hb, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good (hs0 x) (hs0 _) (hs x) (hs _) hb hxy
  choose a b ha0 hb0 ha hb hab using key
  let F : (L ≃ₐ[K] L) → (ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮)) × ((K →+* ℝ) → Prop) := fun x =>
    ((cl x, Ideal.Quotient.mk 𝔮 (b x)), fun φ => 0 < φ (a x : K) * φ (b x : K))
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨h12, h3⟩ := Prod.mk.inj hxy
    obtain ⟨h1, h2⟩ := Prod.mk.inj h12
    rw [Ideal.Quotient.eq] at h2
    have hp : RayPair 𝔮 (b x * a y) (a x * b y) := by
      refine ⟨mul_ne_zero (hb0 x) (ha0 y), mul_ne_zero (ha0 x) (hb0 y), ?_, ?_, ?_, fun φ => ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (hb x).mul_left (isCoprime_span (ha y))
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (isCoprime_span (ha x)).mul_left (hb y)
      · have : b x * a y - a x * b y = b x * (a y - 1) - b y * (a x - 1) + (b x - b y) := by ring
        rw [this]
        exact 𝔮.add_mem (𝔮.sub_mem (𝔮.mul_mem_left _ (ha y)) (𝔮.mul_mem_left _ (ha x))) h2
      · have h4 : 0 < φ (a x : K) * φ (b x : K) ↔ 0 < φ (a y : K) * φ (b y : K) := (congrFun h3 φ).to_iff
        have h5 := mul_ne_zero (emb_ne_zero φ (ha0 x)) (emb_ne_zero φ (hb0 x))
        have h6 := mul_ne_zero (emb_ne_zero φ (ha0 y)) (emb_ne_zero φ (hb0 y))
        have h7 : 0 < (φ (a x : K) * φ (b x : K)) * (φ (a y : K) * φ (b y : K)) := by
          by_cases h : 0 < φ (a x : K) * φ (b x : K)
          · exact mul_pos h (h4.1 h)
          · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 h) h5)
              (lt_of_le_of_ne (not_lt.1 fun h' => h (h4.2 h')) h6)
        convert h7 using 1
        push_cast
        simp only [map_mul]
        ring
    have he : s x * Ideal.span {a x * b y} = s y * Ideal.span {b x * a y} := by
      have e1 := hab x
      have e2 := hab y
      rw [← h1] at e2
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        ← mul_assoc, mul_comm (s x), e1, mul_comm (s y), mul_assoc _ _ (s y), e2]
      ring
    have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ x = χ y := fun χ => by
      apply Units.ext
      rw [← hsx, ← hsx]
      exact heckeIdeal_eq_of_ray hR (hs0 x) (hs0 y) (hs x) (hs y) hp he χ
    by_contra hne
    letI : CommGroup (L ≃ₐ[K] L) := IsMulCommutative.instCommGroup
    obtain ⟨χ, h⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ
      (a := x * y⁻¹) (by rwa [ne_eq, mul_inv_eq_one])
    apply h
    rw [map_mul, map_inv, hχ χ, mul_inv_cancel]
  haveI : Finite (𝓞 K ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h𝔮
  rw [← IsGalois.card_aut_eq_finrank]
  refine (Nat.card_le_card_of_injective F hF).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_prod, Ideal.absNorm_apply, Submodule.cardQuot_apply, classNumber,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := _ → Prop)]
  simp

end GlobalTheory.FieldSize.RayDegree
