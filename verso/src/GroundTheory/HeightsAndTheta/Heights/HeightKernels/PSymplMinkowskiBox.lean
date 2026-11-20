import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory

namespace PSymplMinkowskiBox

/- English proof (translation)
Introduce `i`. Rewrite using `[mulVec_neg, Pi.neg_apply, abs_neg]`. Conclude with `hx i`.
-/
theorem box_neg {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, |(A *ᵥ x) i| < a i) : ∀ i, |(A *ᵥ (-x)) i| < a i := by
  intro i
  rw [mulVec_neg, Pi.neg_apply, abs_neg]
  exact hx i

/- English proof (translation)
Introduce `x hx y hy s t hs ht hst i`. Establish `hlt : s • |(A *ᵥ x) i| + t • |(A *ᵥ y) i| ∈ Set.Iio (a i)` using `convex_Iio (a i) (hx i) (hy i) hs ht hst`. Rewrite `hlt` using `[Set.mem_Iio, smul_eq_mul, smul_eq_mul]`. Rewrite using `[mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]`. Use `_ < a i := hlt`.
-/
theorem box_convex {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Convex ℝ {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} := by
  intro x hx y hy s t hs ht hst i
  have hlt : s • |(A *ᵥ x) i| + t • |(A *ᵥ y) i| ∈ Set.Iio (a i) :=
    convex_Iio (a i) (hx i) (hy i) hs ht hst
  rw [Set.mem_Iio, smul_eq_mul, smul_eq_mul] at hlt
  rw [mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  calc |s * (A *ᵥ x) i + t * (A *ᵥ y) i| ≤ |s * (A *ᵥ x) i| + |t * (A *ᵥ y) i| := abs_add_le _ _
    _ = s * |(A *ᵥ x) i| + t * |(A *ᵥ y) i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ < a i := hlt

/- English proof (translation)
Rewrite using `[ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]`. Simplify using `[Real.volume_Ico]`.
-/
theorem volume_fundamentalDomain_basisFun (ι : Type) [Fintype ι] :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

end PSymplMinkowskiBox

open PSymplMinkowskiBox in

/- English proof (translation)
Introduce `ι _ _ A a hdet ha hprod`. Establish `hdet0 : A.det ≠ 0`. Introduce `h`. Rewrite `hdet` using `[h, abs_zero]`. Conclude with `zero_ne_one hdet`.

Use `set s : Set (ι → ℝ) := {x | ∀ i, |(A *ᵥ x) i| < a i} with hs`. Establish `hvol : volume s = ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, a i)`. Rewrite using `[hs, h1 ι A a hdet0 ha, hdet, div_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Establish `hP : (0 : ℝ) < 2 ^ Fintype.card ι` using `by positivity`. Establish `hbig : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s`.

Rewrite using `[volume_fundamentalDomain_basisFun, one_mul, Module.finrank_fintype_fun_eq_card, hvol, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_lt_ofReal_iff (by positivity)]`. Conclude with `lt_mul_of_one_lt_right hP hprod`. Establish `: Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup`. Express the relevant statement in the definitionally equal form `Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))`. Use `infer_instance`.

Take `⟨x, hx0, hxs⟩` from `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup) (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume) (fun y hy => box_neg A a y hy) (box_convex A a) hbig`. Establish `hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : ι → ℝ) i`. Introduce `i`. Take `⟨z, hz⟩` from `((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (x : ι → ℝ)).mp x.2 i`. Conclude with `⟨z, by simpa using hz⟩`.

Use `choose v hv using hint`. Establish `hxv : intVec v = (x : ι → ℝ)` using `funext hv`. Use `⟨v, ?_, fun i => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hx0` to reduce the goal to its premises.

Use extensionality with `i`. Rewrite using `[← hv i]`. Simplify using the standard rewrite rules. Rewrite using `[hxv]`. Conclude with `hxs i`.
-/
theorem SymplMinkowskiBox.proof (h1 : SymplBoxVolume.Statement) : SymplMinkowskiBox.Statement := by
  intro ι _ _ A a hdet ha hprod
  have hdet0 : A.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    exact zero_ne_one hdet
  set s : Set (ι → ℝ) := {x | ∀ i, |(A *ᵥ x) i| < a i} with hs
  have hvol : volume s = ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, a i) := by
    rw [hs, h1 ι A a hdet0 ha, hdet, div_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hP : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hbig : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) * 2 ^ Module.finrank ℝ (ι → ℝ) <
      volume s := by
    rw [volume_fundamentalDomain_basisFun, one_mul, Module.finrank_fintype_fun_eq_card, hvol,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact lt_mul_of_one_lt_right hP hprod
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))
    infer_instance
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup)
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume)
    (fun y hy => box_neg A a y hy) (box_convex A a) hbig
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : ι → ℝ) i := by
    intro i
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (x : ι → ℝ)).mp x.2 i
    exact ⟨z, by simpa using hz⟩
  choose v hv using hint
  have hxv : intVec v = (x : ι → ℝ) := funext hv
  refine ⟨v, ?_, fun i => ?_⟩
  · rintro rfl
    apply hx0
    ext i
    rw [← hv i]
    simp
  · rw [hxv]
    exact hxs i

end GroundTheory.Heights₂.Heights
