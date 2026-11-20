import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

noncomputable section

namespace PI.SelfDualLoc.W.ND

open PI.SelfDualLoc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Unfold `intOE`. Conclude with `RingHom.mem_range`.
-/
lemma mem_intOE_iff (x : E) : x ∈ intOE E ↔ ∃ a : 𝓞 E, (a : E) = x := by
  unfold intOE
  exact RingHom.mem_range

/- English proof (translation)
The claim follows from `(mem_intOE_iff _).2 ⟨a, rfl⟩`.
-/
lemma coe_mem_intOE (a : 𝓞 E) : (a : E) ∈ intOE E :=
  (mem_intOE_iff _).2 ⟨a, rfl⟩

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (𝓞 E)⁰ (S.biUnion fun s => Finset.univ.image fun j => s j)`. Use `⟨(b : 𝓞 E), nonZeroDivisors.ne_zero b.2, ?_⟩` and prove the remaining obligations. Establish `hgen : ∀ s ∈ S, ∀ j, ((b : 𝓞 E) : E) * s j ∈ intOE E`. Introduce `s hs j`.

Take `⟨a, ha⟩` from `hb (s j) (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)`. Use `(mem_intOE_iff _).2 ⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[show ((b : 𝓞 E) : E) * s j = b • s j from by rw [Submonoid.smul_def, Algebra.smul_def]]`. Conclude with `ha`. Introduce `z hz`.

Rewrite `hz` using `[← hS]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact hgen x hx`. Consider the case `zero`. Introduce `j`.

Simplify using `only [Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Introduce `j`. Rewrite using `[Pi.add_apply, mul_add]`.

Conclude with `add_mem (hx j) (hy j)`. Consider the case `smul a x _ hx`. Introduce `j`. Establish `e : ((b : 𝓞 E) : E) * (a • x) j = (a : E) * (((b : 𝓞 E) : E) * x j)`. Express the relevant statement in the definitionally equal form `((b : 𝓞 E) : E) * ((a : E) * x j) = _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem (coe_mem_intOE a) (hx j)`.
-/
lemma exists_den (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ z ∈ L, ∀ j, (d : E) * z j ∈ intOE E := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 E)⁰
    (S.biUnion fun s => Finset.univ.image fun j => s j)
  refine ⟨(b : 𝓞 E), nonZeroDivisors.ne_zero b.2, ?_⟩
  have hgen : ∀ s ∈ S, ∀ j, ((b : 𝓞 E) : E) * s j ∈ intOE E := by
    intro s hs j
    obtain ⟨a, ha⟩ := hb (s j)
      (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    refine (mem_intOE_iff _).2 ⟨a, ?_⟩
    rw [show ((b : 𝓞 E) : E) * s j = b • s j from by rw [Submonoid.smul_def, Algebra.smul_def]]
    exact ha
  intro z hz
  rw [← hS] at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero =>
    intro j
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro j
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx j) (hy j)
  | smul a x _ hx =>
    intro j
    have e : ((b : 𝓞 E) : E) * (a • x) j = (a : E) * (((b : 𝓞 E) : E) * x j) := by
      change ((b : 𝓞 E) : E) * ((a : E) * x j) = _
      ring
    rw [e]
    exact mul_mem (coe_mem_intOE a) (hx j)

/- English proof (translation)
Use `⟨(2 : E)⁻¹, fun h => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(mem_intOE_iff _).1 h`. Establish `h1 : IsIntegral ℤ ((2 : E)⁻¹)` using `ha ▸ RingOfIntegers.isIntegral_coe a`. Establish `h2 : algebraMap ℚ E ((2 : ℚ)⁻¹) = (2 : E)⁻¹` using `by simp`. Rewrite `h1` using `[← h2]`.

Establish `h3 : IsIntegral ℤ ((2 : ℚ)⁻¹)` using `(isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 h1`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h3`. Establish `h4 : (2 : ℚ) * (z : ℚ) = 1`. Rewrite using `[show (z : ℚ) = (2 : ℚ)⁻¹ by simpa using hz]`. Evaluate the numerical expressions.

Establish `h5 : (2 : ℤ) * z = 1` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers.
-/
lemma exists_not_mem_intOE : ∃ t : E, t ∉ intOE E := by
  refine ⟨(2 : E)⁻¹, fun h => ?_⟩
  obtain ⟨a, ha⟩ := (mem_intOE_iff _).1 h
  have h1 : IsIntegral ℤ ((2 : E)⁻¹) := ha ▸ RingOfIntegers.isIntegral_coe a
  have h2 : algebraMap ℚ E ((2 : ℚ)⁻¹) = (2 : E)⁻¹ := by simp
  rw [← h2] at h1
  have h3 : IsIntegral ℤ ((2 : ℚ)⁻¹) := (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 h1
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (2 : ℚ) * (z : ℚ) = 1 := by
    rw [show (z : ℚ) = (2 : ℚ)⁻¹ by simpa using hz]
    norm_num
  have h5 : (2 : ℤ) * z = 1 := by exact_mod_cast h4
  omega

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end PI.SelfDualLoc.W.ND

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc ND

/- English proof (translation)
Introduce `F E _ _ _ _ _ n σ J Lb T hfin hT hT0 y hy`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, y j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne (funext h)`. Take `⟨d, hd0, hd⟩` from `exists_den Lb (Module.Finite.iff_fg.1 hfin)`. Take `⟨t, ht⟩` from `exists_not_mem_intOE (E := E)`. Establish `hd' : (d : E) ≠ 0` using `by exact_mod_cast hd0`. Establish `hT' : (T : E) ≠ 0` using `by exact_mod_cast hT0`.

Establish `hmem : (T : E) • ((t / ((d : E) * (T : E) * y j)) • y) ∈ Lb`. Apply `hT` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[hform_smul_right, hy x hx, mul_zero]`. Conclude with `zero_mem _`.

Use `hd _ hmem j` as an intermediate fact. Apply `ht` to reduce the goal to its premises. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem nondeg : Nondeg := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hT hT0 y hy
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨d, hd0, hd⟩ := exists_den Lb (Module.Finite.iff_fg.1 hfin)
  obtain ⟨t, ht⟩ := exists_not_mem_intOE (E := E)
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hT' : (T : E) ≠ 0 := by exact_mod_cast hT0
  have hmem : (T : E) • ((t / ((d : E) * (T : E) * y j)) • y) ∈ Lb := by
    apply hT
    intro x hx
    rw [hform_smul_right, hy x hx, mul_zero]
    exact zero_mem _
  have := hd _ hmem j
  apply ht
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end PI.SelfDualLoc.W
