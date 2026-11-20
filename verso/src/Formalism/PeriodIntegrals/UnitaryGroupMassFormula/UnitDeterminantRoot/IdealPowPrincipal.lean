import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot

noncomputable section
open scoped NumberField nonZeroDivisors

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI Submodule NumberField

def volSet {m : Type} [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) : Set ℂ :=
  {z | ∃ v : m → m → ℂ, (∀ j, v j ∈ Λ) ∧ z = (Matrix.of v).det}

def vol (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) :
    Submodule (𝓞 F) ℂ :=
  Submodule.span (𝓞 F) (volSet Λ)

section Princ

variable (F : IntermediateField ℚ ℂ)

/- English proof (translation)
Rewrite using `[span_pow, Set.singleton_pow]`.
-/
lemma span_single_pow (x : ℂ) (n : ℕ) : span (𝓞 F) {x} ^ n = span (𝓞 F) {x ^ n} := by
  rw [span_pow, Set.singleton_pow]

/- English proof (translation)
Rewrite using `[span_mul_span, Set.singleton_mul_singleton]`.
-/
lemma span_single_mul (x y : ℂ) : span (𝓞 F) {x} * span (𝓞 F) {y} = span (𝓞 F) {x * y} := by
  rw [span_mul_span, Set.singleton_mul_singleton]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `mul_le_mul' ih h`.
-/
lemma sub_pow_le {S T : Submodule (𝓞 F) ℂ} (h : S ≤ T) (n : ℕ) : S ^ n ≤ T ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_le_mul' ih h

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F ℂ]`. Both sides reduce to the same expression.
-/
lemma algebraMap_O_apply (o : 𝓞 F) : algebraMap (𝓞 F) ℂ o = ((algebraMap (𝓞 F) F o : F) : ℂ) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F ℂ]; rfl

variable [NumberField F]

abbrev hF : ℕ := Fintype.card (ClassGroup (𝓞 F))

/- English proof (translation)
Establish `hI' : I ∈ (Ideal (𝓞 F))⁰` using `mem_nonZeroDivisors_of_ne_zero hI`. Establish `hIh : I ^ hF F ∈ (Ideal (𝓞 F))⁰` using `pow_mem hI' _`. Establish `h1 : ClassGroup.mk0 ⟨I ^ hF F, hIh⟩ = 1`. Establish `e : (⟨I ^ hF F, hIh⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI'⟩ ^ hF F` using `Subtype.ext (by simp)`. Rewrite using `[e, map_pow, pow_card_eq_one]`.

Rewrite `h1` using `[ClassGroup.mk0_eq_one_iff]`. Take `⟨⟨a, ha⟩⟩` from `h1`. Use `⟨a, ?_, ha⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `h0 : I ^ hF F = 0` using `by rw [ha]; simp`.

Conclude with `zero_notMem_nonZeroDivisors (h0 ▸ hIh)`.
-/
lemma ideal_pow_principal (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ I ^ hF F = span (𝓞 F) {a} := by
  have hI' : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have hIh : I ^ hF F ∈ (Ideal (𝓞 F))⁰ := pow_mem hI' _
  have h1 : ClassGroup.mk0 ⟨I ^ hF F, hIh⟩ = 1 := by
    have e : (⟨I ^ hF F, hIh⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI'⟩ ^ hF F := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  rw [ClassGroup.mk0_eq_one_iff] at h1
  obtain ⟨⟨a, ha⟩⟩ := h1
  refine ⟨a, ?_, ha⟩
  rintro rfl
  have h0 : I ^ hF F = 0 := by rw [ha]; simp
  exact zero_notMem_nonZeroDivisors (h0 ▸ hIh)

/- English proof (translation)
Use `set S0 := span (𝓞 F) {t⁻¹} * S with hS0def`. Establish `hS0 : S0 ≤ LinearMap.range (Algebra.linearMap (𝓞 F) ℂ)`. Rewrite using `[← Submodule.one_eq_range, Submodule.one_eq_span]`. Combine the equalities or inequalities in the displayed calculation. Establish `hSS0 : S = span (𝓞 F) {t} * S0`.

Rewrite using `[hS0def, ← mul_assoc, span_single_mul, mul_inv_cancel₀ ht, ← Submodule.one_eq_span, one_mul]`. Use `set I : Ideal (𝓞 F) := Submodule.comap (Algebra.linearMap (𝓞 F) ℂ) S0 with hIdef`. Establish `hI : Submodule.map (Algebra.linearMap (𝓞 F) ℂ) I = S0` using `Submodule.map_comap_eq_of_le hS0`. Establish `hI0 : I ≠ ⊥`. Introduce `h`.

Apply `hS` to reduce the goal to its premises. Rewrite using `[hSS0, ← hI, h, Submodule.map_bot, Submodule.mul_bot]`. Take `⟨a, ha0, ha⟩` from `ideal_pow_principal F I hI0`. Use `⟨algebraMap (𝓞 F) F a, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `ha0` to reduce the goal to its premises. Conclude with `RingOfIntegers.ext (by simpa using h)`. Establish `hmap : S0 ^ hF F = span (𝓞 F) {algebraMap (𝓞 F) ℂ a}`. Establish `hp : Submodule.map (Algebra.linearMap (𝓞 F) ℂ) (I ^ hF F) = S0 ^ hF F`. Rewrite using `[← hI]`.

Conclude with `Submodule.map_pow (M := I) (f := Algebra.ofId (𝓞 F) ℂ) (n := hF F)`. Rewrite using `[← hp, ha, Submodule.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Rewrite using `[hSS0, mul_pow, hmap, span_single_pow, span_single_mul, algebraMap_O_apply]`.
-/
lemma sub_pow_principal (S : Submodule (𝓞 F) ℂ) (hS : S ≠ ⊥) (t : ℂ) (ht : t ≠ 0)
    (hle : S ≤ span (𝓞 F) {t}) :
    ∃ y : F, y ≠ 0 ∧ S ^ hF F = span (𝓞 F) {t ^ hF F * (y : ℂ)} := by
  set S0 := span (𝓞 F) {t⁻¹} * S with hS0def
  have hS0 : S0 ≤ LinearMap.range (Algebra.linearMap (𝓞 F) ℂ) := by
    rw [← Submodule.one_eq_range, Submodule.one_eq_span]
    calc S0 ≤ span (𝓞 F) {t⁻¹} * span (𝓞 F) {t} := mul_le_mul' le_rfl hle
      _ = span (𝓞 F) {1} := by rw [span_single_mul, inv_mul_cancel₀ ht]
  have hSS0 : S = span (𝓞 F) {t} * S0 := by
    rw [hS0def, ← mul_assoc, span_single_mul, mul_inv_cancel₀ ht, ← Submodule.one_eq_span, one_mul]
  set I : Ideal (𝓞 F) := Submodule.comap (Algebra.linearMap (𝓞 F) ℂ) S0 with hIdef
  have hI : Submodule.map (Algebra.linearMap (𝓞 F) ℂ) I = S0 := Submodule.map_comap_eq_of_le hS0
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hS
    rw [hSS0, ← hI, h, Submodule.map_bot, Submodule.mul_bot]
  obtain ⟨a, ha0, ha⟩ := ideal_pow_principal F I hI0
  refine ⟨algebraMap (𝓞 F) F a, ?_, ?_⟩
  · intro h
    apply ha0
    exact RingOfIntegers.ext (by simpa using h)
  have hmap : S0 ^ hF F = span (𝓞 F) {algebraMap (𝓞 F) ℂ a} := by
    have hp : Submodule.map (Algebra.linearMap (𝓞 F) ℂ) (I ^ hF F) = S0 ^ hF F := by
      rw [← hI]; exact Submodule.map_pow (M := I) (f := Algebra.ofId (𝓞 F) ℂ) (n := hF F)
    rw [← hp, ha, Submodule.map_span, Set.image_singleton]
    rfl
  rw [hSS0, mul_pow, hmap, span_single_pow, span_single_mul, algebraMap_O_apply]

end Princ

end PI.UnitaryGroupMassFormula.UnitDetRoot
