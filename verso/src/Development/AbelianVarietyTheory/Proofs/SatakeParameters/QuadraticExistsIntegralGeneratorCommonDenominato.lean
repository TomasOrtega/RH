import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGen
open NumberField

namespace GlobalTheory

open NumberField in
/- English proof (translation)
Take `⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E)` from `by by_contra! hx`. Establish `htop : (⊤ : IntermediateField F E) = ⊥`. Use extensionality with `x`. Simplify using `only [IntermediateField.mem_top, true_iff]`. Conclude with `IntermediateField.mem_bot.mpr (hx x)`.

Establish `h1` using `IntermediateField.finrank_eq_one_iff.mpr htop`. Rewrite `h1` using `[IntermediateField.finrank_top']`. Use linear arithmetic over natural numbers and integers. Take `⟨n, hn, hnx⟩` from `exists_integral_multiples ℤ ℚ ({x} : Finset E)`. Establish `hint : IsIntegral ℤ (n • x)` using `hnx x (Finset.mem_singleton_self x)`.

Take `⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x` from `⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩`. Establish `hθ : (θ : E) ∉ Set.range (algebraMap F E)`. Introduce and unpack `⟨a, ha⟩`. Apply `hx` to reduce the goal to its premises. Use `⟨a / n, ?_⟩` and prove the remaining obligations.

Establish `hnE : (n : E) ≠ 0` using `by exact_mod_cast hn`. Rewrite using `[map_div₀, map_intCast, ha, hθx]`. Clear the denominators using the available nonvanishing facts. Establish `hli : LinearIndependent F ![(1 : E), (θ : E)]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero] at hst`. Conclude with `⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩`.

It suffices to derive a contradiction. Apply `hθ` to reduce the goal to its premises. Use `⟨-s / t, ?_⟩` and prove the remaining obligations. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `htE : algebraMap F E t ≠ 0` using `(map_ne_zero _).mpr ht`.

Rewrite using `[map_div₀, map_neg]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hst`. Take `⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)]` from `⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]), coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩`. Establish `hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ`.

Introduce `z`. Use `conv_lhs => rw [← b.sum_repr z]`. Rewrite using `[Fin.sum_univ_two, hb1]`. Simplify using `[Algebra.smul_def]`. Use `set B := RingOfIntegers.basis E`.

Take `⟨d, hd, hdint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 => b.repr (B p.1 : E) p.2)`. Establish `hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k)` using `fun i k => hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))`. Use `⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩` and prove the remaining obligations. Set `M : Submodule ℤ (𝓞 E)` to `{ carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ} add_mem' := by`. Introduce and unpack `_ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩`.

Conclude with `⟨u + u', v + v', by simp only [map_add]; ring⟩`. Use the proof step `zero_mem' := ⟨0, 0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨u, v, rfl⟩`. Conclude with `⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }`.

Establish `hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M`. Introduce `y`. Establish `hspan : y ∈ Submodule.span ℤ (Set.range B)` using `by rw [B.span_eq]; trivial`. Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨i, rfl⟩` from `hz`. Use `⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[RingOfIntegers.ext_iff]`. Establish `e` using `hb (B i : E)`. Establish `key : algebraMap F E (d : F) * (B i : E) = algebraMap F E (d • b.repr (B i : E) 0) + algebraMap F E (d • b.repr (B i : E) 1) * θ`.

Simplify using `only [zsmul_eq_mul, map_mul, map_intCast]`. Take the linear combination `(d : E) * e`. Conclude with `key`. Consider the case `zero => simpa using M.zero_mem`. Consider the case `add z w _ _ hz hw => rw [mul_add]`.

Conclude with `M.add_mem hz hw`. Consider the case `smul c z _ hz => rw [mul_smul_comm]`. Conclude with `M.smul_mem c hz`. Introduce `y`. Take `⟨u, v, huv⟩` from `hall y`.

Conclude with `⟨u, v, huv⟩`.
-/
private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩

open NumberField in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _`. Conclude with `exists_integral_generator_common_denom_of_finrank_two F E (Algebra.IsQuadraticExtension.finrank_eq_two F E)`.
-/
theorem _root_.GlobalTheory.quadratic_exists_integral_generator_common_denominator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ _
  exact exists_integral_generator_common_denom_of_finrank_two F E
    (Algebra.IsQuadraticExtension.finrank_eq_two F E)

end GlobalTheory
