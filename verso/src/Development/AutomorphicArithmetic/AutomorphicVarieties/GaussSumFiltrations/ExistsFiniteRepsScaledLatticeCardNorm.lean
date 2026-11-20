import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.RepsLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`. Use `⟨fun i => ⟨l i, (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ _)⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Both sides reduce to the same expression.

Introduce and unpack `⟨m, rfl⟩`. Use `⟨fun i => (m i : F), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(AddSubgroup.mem_pi _).2 fun i _ => (m i).2`. Use function extensionality and compare the values at `i`. Both sides reduce to the same expression.
-/
theorem mem_aL_iff (a : F) (x : κ → F) :
    x ∈ aL κ a ↔ ∃ m : κ → 𝓞 F, x = fun i => a * (m i : F) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => ⟨l i, (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ _)⟩, ?_⟩
    funext i
    rfl
  · rintro ⟨m, rfl⟩
    refine ⟨fun i => (m i : F), ?_, ?_⟩
    · exact (AddSubgroup.mem_pi _).2 fun i _ => (m i).2
    · funext i
      rfl

end GlobalTheory.HilbertThetaSeries.RepsLat

namespace GlobalTheory.HilbertThetaSeries

open GlobalTheory.HilbertThetaSeries.RepsLat in

/- English proof (translation)
Introduce `F _ _ κ _ _ a b ha hb hc`. Take `⟨c, hcF⟩ : ∃ c : 𝓞 F, (c : F) = a / b` from `⟨⟨a / b, hc⟩, rfl⟩`. Establish `hab : a = b * (c : F)` using `by rw [hcF]; field_simp`. Establish `hc0 : c ≠ 0`. Introduce `h`.

Apply `ha` to reduce the goal to its premises. Establish `h0 : (c : F) = 0` using `by rw [h]; rfl`. Rewrite `h0` using `[hcF, div_eq_zero_iff]`. The claim follows by propositional logic. Set `I : Ideal (𝓞 F)` to `Ideal.span {c}`.

Establish `hcard : Nat.card (𝓞 F ⧸ I) = (Algebra.norm ℤ c).natAbs`. Rewrite using `[← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hne : (Algebra.norm ℤ c).natAbs ≠ 0`. Rewrite using `[Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]`. Conclude with `hc0`.

Use `haveI : Finite (𝓞 F ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)`. Use `letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _`. Set `s : 𝓞 F ⧸ I → 𝓞 F` to `fun q => if q = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective q)`. Establish `hs : ∀ q, Ideal.Quotient.mk I (s q) = q`. Introduce `q`.

Distinguish the cases in `h : q = 0`. Simplify using `[s, h]`. Simplify using `only [s, if_neg h]`. Conclude with `Classical.choose_spec (Ideal.Quotient.mk_surjective q)`. Establish `hs0 : s 0 = 0` using `by simp [s]`.

Set `e : (κ → 𝓞 F ⧸ I) → (κ → F)` to `fun q i => b * (s (q i) : F)`. Establish `he : Function.Injective e`. Introduce `q q' h`. Use function extensionality and compare the values at `i`. Establish `h1` using `mul_left_cancel₀ hb (congrFun h i)`.

Establish `h3 : s (q i) = s (q' i)` using `RingOfIntegers.ext h1`. Rewrite using `[← hs (q i), ← hs (q' i), h3]`. Use `⟨Finset.univ.image e, ⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hy`.

Conclude with `(mem_aL_iff b _).2 ⟨fun i => s (q i), rfl⟩`. Introduce `x hx`. Take `⟨m, rfl⟩` from `(mem_aL_iff b x).1 hx`. Use `⟨e (fun i => Ideal.Quotient.mk I (m i)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hI : ∀ i, m i - s (Ideal.Quotient.mk I (m i)) ∈ I` using `fun i => by`.

Rewrite using `[← Ideal.Quotient.eq, hs]`. Use `choose r hr using fun i => Ideal.mem_span_singleton'.1 (hI i)`. Use `(mem_aL_iff a _).2 ⟨r, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (fun z : 𝓞 F => (z : F)) (hr i)`.

Simplify using `only [map_mul, map_sub] at h1`. Simplify using `only [e, Pi.sub_apply]`. Rewrite using `[hab]`. Take the linear combination `-b * h1`. Introduce and unpack `y ⟨hyT, hy⟩`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hyT`. Establish `hq : q = fun i => Ideal.Quotient.mk I (m i)`. Use function extensionality and compare the values at `i`. Take `⟨r, hr⟩` from `(mem_aL_iff a _).1 hy`. Establish `h1` using `congrFun hr i`.

Simplify using `only [e, Pi.sub_apply] at h1`. Establish `h2 : ((m i - s (q i) : 𝓞 F) : F) = ((r i * c : 𝓞 F) : F)`. Simplify using `only [map_mul, map_sub]`. Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Rewrite `h1` using `[hab]`.

Take the linear combination `h1`. Establish `h3 : m i - s (q i) ∈ I` using `Ideal.mem_span_singleton'.2 ⟨r i, (RingOfIntegers.ext h2).symm⟩`. Rewrite using `[← hs (q i)]`. Conclude with `(Ideal.Quotient.eq.2 h3).symm`. Rewrite using `[hq]`.

Use `Finset.mem_image.2 ⟨0, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[e, hs0]`. Introduce `x hx`. Take `⟨m, rfl⟩` from `(mem_aL_iff a x).1 hx`.

Use `(mem_aL_iff b _).2 ⟨fun i => c * m i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [map_mul]`. Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fun, ← Nat.card_eq_fintype_card, hcard, ← hcF, Nat.cast_pow, Nat.cast_natAbs, ← Algebra.coe_norm_int, Int.cast_abs]`.
-/
theorem exists_isReps_aL : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F),
    a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧
      aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  intro F _ _ κ _ _ a b ha hb hc
  obtain ⟨c, hcF⟩ : ∃ c : 𝓞 F, (c : F) = a / b := ⟨⟨a / b, hc⟩, rfl⟩
  have hab : a = b * (c : F) := by rw [hcF]; field_simp
  have hc0 : c ≠ 0 := by
    intro h
    apply ha
    have h0 : (c : F) = 0 := by rw [h]; rfl
    rw [hcF, div_eq_zero_iff] at h0
    tauto
  let I : Ideal (𝓞 F) := Ideal.span {c}
  have hcard : Nat.card (𝓞 F ⧸ I) = (Algebra.norm ℤ c).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : (Algebra.norm ℤ c).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hc0
  haveI : Finite (𝓞 F ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  classical
  let s : 𝓞 F ⧸ I → 𝓞 F := fun q => if q = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective q)
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := by
    intro q
    by_cases h : q = 0
    · simp [s, h]
    · simp only [s, if_neg h]
      exact Classical.choose_spec (Ideal.Quotient.mk_surjective q)
  have hs0 : s 0 = 0 := by simp [s]
  let e : (κ → 𝓞 F ⧸ I) → (κ → F) := fun q i => b * (s (q i) : F)
  have he : Function.Injective e := by
    intro q q' h
    funext i
    have h1 := mul_left_cancel₀ hb (congrFun h i)
    have h3 : s (q i) = s (q' i) := RingOfIntegers.ext h1
    rw [← hs (q i), ← hs (q' i), h3]
  refine ⟨Finset.univ.image e, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (mem_aL_iff b _).2 ⟨fun i => s (q i), rfl⟩
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff b x).1 hx
    refine ⟨e (fun i => Ideal.Quotient.mk I (m i)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have hI : ∀ i, m i - s (Ideal.Quotient.mk I (m i)) ∈ I := fun i => by
        rw [← Ideal.Quotient.eq, hs]
      choose r hr using fun i => Ideal.mem_span_singleton'.1 (hI i)
      refine (mem_aL_iff a _).2 ⟨r, ?_⟩
      funext i
      have h1 := congrArg (fun z : 𝓞 F => (z : F)) (hr i)
      simp only [map_mul, map_sub] at h1
      simp only [e, Pi.sub_apply]
      rw [hab]
      linear_combination -b * h1
    · rintro y ⟨hyT, hy⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyT
      have hq : q = fun i => Ideal.Quotient.mk I (m i) := by
        funext i
        obtain ⟨r, hr⟩ := (mem_aL_iff a _).1 hy
        have h1 := congrFun hr i
        simp only [e, Pi.sub_apply] at h1
        have h2 : ((m i - s (q i) : 𝓞 F) : F) = ((r i * c : 𝓞 F) : F) := by
          simp only [map_mul, map_sub]
          apply mul_left_cancel₀ hb
          rw [hab] at h1
          linear_combination h1
        have h3 : m i - s (q i) ∈ I := Ideal.mem_span_singleton'.2 ⟨r i, (RingOfIntegers.ext h2).symm⟩
        rw [← hs (q i)]
        exact (Ideal.Quotient.eq.2 h3).symm
      rw [hq]
  · refine Finset.mem_image.2 ⟨0, Finset.mem_univ _, ?_⟩
    funext i
    simp [e, hs0]
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff a x).1 hx
    refine (mem_aL_iff b _).2 ⟨fun i => c * m i, ?_⟩
    funext i
    simp only [map_mul]
    rw [hab]
    ring
  · rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fun, ← Nat.card_eq_fintype_card,
      hcard, ← hcF, Nat.cast_pow, Nat.cast_natAbs, ← Algebra.coe_norm_int, Int.cast_abs]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.exists_isReps_aL | exact GlobalTheory.HilbertThetaSeries.exists_isReps_aL | (intros; apply GlobalTheory.HilbertThetaSeries.exists_isReps_aL <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F), a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧ aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  first | exact @GlobalTheory.HilbertThetaSeries.exists_isReps_aL | exact GlobalTheory.HilbertThetaSeries.exists_isReps_aL | (intros; apply GlobalTheory.HilbertThetaSeries.exists_isReps_aL <;> assumption)
