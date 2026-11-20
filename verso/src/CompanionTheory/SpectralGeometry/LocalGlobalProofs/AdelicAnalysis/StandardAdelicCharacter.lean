import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.StdChar

variable (F : Type) [Field F] [NumberField F]

def fieldChar (b : F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ))

/- English proof (translation)
Simplify using `only [fieldChar, map_add, Rat.cast_add, mul_add, Complex.exp_add]`.
-/
lemma fieldChar_add (a b : F) : fieldChar F (a + b) = fieldChar F a * fieldChar F b := by
  simp only [fieldChar, map_add, Rat.cast_add, mul_add, Complex.exp_add]

/- English proof (translation)
Simplify using `[fieldChar]`.
-/
lemma fieldChar_zero : fieldChar F 0 = 1 := by simp [fieldChar]

/- English proof (translation)
Establish `: -(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ) = ((-(2 * Real.pi * (Algebra.trace ℚ F b : ℚ)) : ℝ) : ℂ) * Complex.I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[fieldChar, this, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_fieldChar (b : F) : ‖fieldChar F b‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ) =
      ((-(2 * Real.pi * (Algebra.trace ℚ F b : ℚ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fieldChar, this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Establish `h : IsIntegral ℤ (Algebra.trace ℚ F (r : F))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Conclude with `⟨n, by rw [← hn, eq_intCast]⟩`.
-/
lemma trace_integer (r : 𝓞 F) : ∃ n : ℤ, Algebra.trace ℚ F (r : F) = n := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn, eq_intCast]⟩

/- English proof (translation)
Rewrite using `[fieldChar, Complex.exp_eq_one_iff]`. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`.

Use `⟨-n, ?_⟩` and prove the remaining obligations. Establish `h3 : -((Algebra.trace ℚ F b : ℚ) : ℂ) = (n : ℂ)` using `mul_right_cancel₀ h2 (by rw [← hn]; ring)`. Establish `h4 : ((Algebra.trace ℚ F b : ℚ) : ℂ) = ((-n : ℤ) : ℂ)`. Rewrite using `[Int.cast_neg, ← h3]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h4` after adjusting the coercions. Introduce and unpack `⟨n, hn⟩`. Use `⟨-n, ?_⟩` and prove the remaining obligations. Rewrite using `[hn]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma fieldChar_eq_one_iff (b : F) :
    fieldChar F b = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F b = n := by
  rw [fieldChar, Complex.exp_eq_one_iff]
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h3 : -((Algebra.trace ℚ F b : ℚ) : ℂ) = (n : ℂ) :=
      mul_right_cancel₀ h2 (by rw [← hn]; ring)
    have h4 : ((Algebra.trace ℚ F b : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
      rw [Int.cast_neg, ← h3]
      ring
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [hn]
    push_cast
    ring

/- English proof (translation)
Introduce `v`. Conclude with `(HeightOneSpectrum.adicCompletionIntegers F v).zero_mem`.
-/
lemma zero_mem_Oh : (0 : A F) ∈ Oh F := by
  intro v
  exact (HeightOneSpectrum.adicCompletionIntegers F v).zero_mem

variable {F} in
/- English proof (translation)
Introduce `v`. Conclude with `add_mem (hx v) (hy v)`.
-/
lemma add_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F := by
  intro v
  exact add_mem (hx v) (hy v)

variable {F} in
/- English proof (translation)
Introduce `v`. Conclude with `sub_mem (hx v) (hy v)`.
-/
lemma sub_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := by
  intro v
  exact sub_mem (hx v) (hy v)

/- English proof (translation)
Take `⟨-, -, -, -, hOpen, hDense, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hW : IsOpen {y : A F | x - y ∈ Oh F}` using `hOpen.preimage (continuous_const.sub continuous_id)`. Take `⟨b, hb⟩` from `hDense.exists_mem_open hW ⟨x, by simpa using zero_mem_Oh F⟩`. Conclude with `⟨b, hb⟩`.
-/
lemma exists_rep (x : A F) : ∃ b : F, x - algebraMap F (A F) b ∈ Oh F := by
  obtain ⟨-, -, -, -, hOpen, hDense, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hW : IsOpen {y : A F | x - y ∈ Oh F} := hOpen.preimage (continuous_const.sub continuous_id)
  obtain ⟨b, hb⟩ := hDense.exists_mem_open hW ⟨x, by simpa using zero_mem_Oh F⟩
  exact ⟨b, hb⟩

def charFun (x : A F) : ℂ := fieldChar F (Classical.choose (exists_rep F x))

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hint, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hc` using `Classical.choose_spec (exists_rep F x)`. Use `set c := Classical.choose (exists_rep F x) with hcdef`. Establish `hbc : algebraMap F (A F) (b - c) ∈ Oh F`. Use `sub_mem_Oh hc h` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Take `⟨r, hr⟩` from `(hint (b - c)).1 hbc`. Establish `h1 : fieldChar F (b - c) = 1`.

Rewrite using `[← hr]`. Conclude with `(fieldChar_eq_one_iff F _).2 (trace_integer F r)`. Establish `hb : b = (b - c) + c` using `by ring`. Rewrite using `[show charFun F x = fieldChar F c from rfl, hb, fieldChar_add, h1, one_mul]`.
-/
lemma charFun_eq (x : A F) (b : F) (h : x - algebraMap F (A F) b ∈ Oh F) :
    charFun F x = fieldChar F b := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hc := Classical.choose_spec (exists_rep F x)
  set c := Classical.choose (exists_rep F x) with hcdef
  have hbc : algebraMap F (A F) (b - c) ∈ Oh F := by
    have := sub_mem_Oh hc h
    convert this using 1
    rw [map_sub]
    abel
  obtain ⟨r, hr⟩ := (hint (b - c)).1 hbc
  have h1 : fieldChar F (b - c) = 1 := by
    rw [← hr]
    exact (fieldChar_eq_one_iff F _).2 (trace_integer F r)
  have hb : b = (b - c) + c := by ring
  rw [show charFun F x = fieldChar F c from rfl, hb, fieldChar_add, h1, one_mul]

def stdChar : AddChar (A F) ℂ where
  toFun := charFun F
  map_zero_eq_one' := by
    rw [charFun_eq F 0 0 (by simpa using zero_mem_Oh F), fieldChar_zero]
  map_add_eq_mul' x y := by
    obtain ⟨a, ha⟩ := exists_rep F x
    obtain ⟨b, hb⟩ := exists_rep F y
    have h : x + y - algebraMap F (A F) (a + b) ∈ Oh F := by
      have := add_mem_Oh ha hb
      rw [map_add]
      convert this using 1
      ring
    rw [charFun_eq F _ _ h, charFun_eq F _ _ ha, charFun_eq F _ _ hb, fieldChar_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma stdChar_apply (x : A F) : stdChar F x = charFun F x := rfl

/- English proof (translation)
Take `⟨-, -, -, -, hOpen, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `exists_rep F x`. Establish `hW : IsOpen {y : A F | y - x ∈ Oh F}` using `hOpen.preimage (continuous_id.sub continuous_const)`. Establish `hxW : x ∈ {y : A F | y - x ∈ Oh F}` using `by simpa using zero_mem_Oh F`.

Establish `hev : ∀ᶠ y in 𝓝 x, stdChar F x = stdChar F y` using `by filter_upwards [hW.mem_nhds hxW] with y hy`. Establish `hy' : y - algebraMap F (A F) b ∈ Oh F`. Use `add_mem_Oh hy hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Rewrite using `[stdChar_apply, stdChar_apply, charFun_eq F x b hb, charFun_eq F y b hy']`. Conclude with `(continuousAt_const : ContinuousAt (fun _ : A F => stdChar F x) x).congr hev`.
-/
lemma continuous_stdChar : Continuous (stdChar F) := by
  obtain ⟨-, -, -, -, hOpen, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨b, hb⟩ := exists_rep F x
  have hW : IsOpen {y : A F | y - x ∈ Oh F} := hOpen.preimage (continuous_id.sub continuous_const)
  have hxW : x ∈ {y : A F | y - x ∈ Oh F} := by simpa using zero_mem_Oh F
  have hev : ∀ᶠ y in 𝓝 x, stdChar F x = stdChar F y := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    have hy' : y - algebraMap F (A F) b ∈ Oh F := by
      have := add_mem_Oh hy hb
      convert this using 1
      abel
    rw [stdChar_apply, stdChar_apply, charFun_eq F x b hb, charFun_eq F y b hy']
  exact (continuousAt_const : ContinuousAt (fun _ : A F => stdChar F x) x).congr hev

/- English proof (translation)
Take `⟨-, -, -, -, hOpen, hDense, hint, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Introduce `x hx`. Rewrite using `[← hS.closure_eq, mem_closure_iff]`. Introduce `o ho hxo`. Take `⟨b, hb⟩` from `hDense.exists_mem_open (ho.inter hOpen) ⟨x, hxo, hx⟩`.

Take `⟨r, hr⟩` from `(hint b).1 hb.2`. Conclude with `⟨algebraMap F (A F) b, hb.1, hr ▸ h r⟩`.
-/
lemma Oh_subset_of_isClosed {S : Set (A F)} (hS : IsClosed S)
    (h : ∀ r : 𝓞 F, algebraMap F (A F) (r : F) ∈ S) : Oh F ⊆ S := by
  obtain ⟨-, -, -, -, hOpen, hDense, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  intro x hx
  rw [← hS.closure_eq, mem_closure_iff]
  intro o ho hxo
  obtain ⟨b, hb⟩ := hDense.exists_mem_open (ho.inter hOpen) ⟨x, hxo, hx⟩
  obtain ⟨r, hr⟩ := (hint b).1 hb.2
  exact ⟨algebraMap F (A F) b, hb.1, hr ▸ h r⟩

/- English proof (translation)
Introduce `F _ _`. Take `⟨-, -, -, -, -, -, hint, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hψ1 : ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ x ∈ Oh F, ψ x = 1`. Introduce `ψ hψ x hx`. Use `Oh_subset_of_isClosed F (S := {y | ψ y = 1}) (isClosed_eq hψ.1 continuous_const) (fun r => ?_) hx` and prove the remaining obligations.

Use `show ψ (algebraMap F (A F) (r : F)) = 1`. Rewrite using `[hψ.2]`. Conclude with `(fieldChar_eq_one_iff F _).2 (trace_integer F r)`. Use `⟨⟨stdChar F, continuous_stdChar F, fun b => ?_⟩, fun ψ hψ => ⟨fun x => ?_, hψ1 ψ hψ, fun b => ⟨fun h r => ?_, fun h => ?_⟩⟩⟩` and prove the remaining obligations. Rewrite using `[stdChar_apply, charFun_eq F _ b (by simp [zero_mem_Oh F])]`.

Both sides reduce to the same expression. Take `⟨b, hb⟩` from `exists_rep F x`. Establish `hx : x = algebraMap F (A F) b + (x - algebraMap F (A F) b)` using `by abel`. Rewrite using `[hx, AddChar.map_add_eq_mul, hψ1 ψ hψ _ hb, mul_one, hψ.2]`. Conclude with `norm_fieldChar F b`.

Establish `h1` using `h (algebraMap F (A F) (r : F)) ((hint _).2 ⟨r, rfl⟩)`. Rewrite `h1` using `[← map_mul, hψ.2]`. Conclude with `(fieldChar_eq_one_iff F (b * (r : F))).1 h1`. Introduce `x hx`. Use `Oh_subset_of_isClosed F (S := {y | ψ (algebraMap F (A F) b * y) = 1}) (isClosed_eq (hψ.1.comp (continuous_const.mul continuous_id)) continuous_const) (fun r => ?_) hx` and prove the remaining obligations.

Use `show ψ (algebraMap F (A F) b * algebraMap F (A F) (r : F)) = 1`. Rewrite using `[← map_mul, hψ.2]`. Conclude with `(fieldChar_eq_one_iff F _).2 (h r)`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  intro F _ _
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hψ1 : ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ x ∈ Oh F, ψ x = 1 := by
    intro ψ hψ x hx
    refine Oh_subset_of_isClosed F (S := {y | ψ y = 1}) (isClosed_eq hψ.1 continuous_const) (fun r => ?_) hx
    show ψ (algebraMap F (A F) (r : F)) = 1
    rw [hψ.2]
    exact (fieldChar_eq_one_iff F _).2 (trace_integer F r)
  refine ⟨⟨stdChar F, continuous_stdChar F, fun b => ?_⟩, fun ψ hψ => ⟨fun x => ?_, hψ1 ψ hψ, fun b => ⟨fun h r => ?_, fun h => ?_⟩⟩⟩
  · rw [stdChar_apply, charFun_eq F _ b (by simp [zero_mem_Oh F])]
    rfl
  · obtain ⟨b, hb⟩ := exists_rep F x
    have hx : x = algebraMap F (A F) b + (x - algebraMap F (A F) b) := by abel
    rw [hx, AddChar.map_add_eq_mul, hψ1 ψ hψ _ hb, mul_one, hψ.2]
    exact norm_fieldChar F b
  · have h1 := h (algebraMap F (A F) (r : F)) ((hint _).2 ⟨r, rfl⟩)
    rw [← map_mul, hψ.2] at h1
    exact (fieldChar_eq_one_iff F (b * (r : F))).1 h1
  · intro x hx
    refine Oh_subset_of_isClosed F (S := {y | ψ (algebraMap F (A F) b * y) = 1})
      (isClosed_eq (hψ.1.comp (continuous_const.mul continuous_id)) continuous_const) (fun r => ?_) hx
    show ψ (algebraMap F (A F) b * algebraMap F (A F) (r : F)) = 1
    rw [← map_mul, hψ.2]
    exact (fieldChar_eq_one_iff F _).2 (h r)

end GlobalTheory.CompanionTheory.SW.Core.StdChar
