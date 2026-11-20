import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StExtensionQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `R B _ _ _ r hinj hr hfin`. Use `set a := Algebra.linearMap R B`. Use `set P : Submodule R B := LinearMap.range a`. Use `set rP : Submodule R B := Submodule.map a (Ideal.span {r})`. Use `set rB : Submodule R B := (Ideal.span {algebraMap R B r}).restrictScalars R`.

Establish `hrPP : rP ≤ P`. Introduce and unpack `_ ⟨y, -, rfl⟩`. Conclude with `⟨y, rfl⟩`. Establish `hrPrB : rP ≤ rB`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Conclude with `Ideal.mem_span_singleton'.2 ⟨algebraMap R B c, by simp [a]⟩`. Establish `hPr : P ≤ rP.comap (r • LinearMap.id)`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨r * x, Ideal.mem_span_singleton'.2 ⟨x, mul_comm _ _⟩, by simp [a, Algebra.smul_def]⟩`.

Set `f₁` to `(Ideal.span {r}).mapQ rP a (Submodule.le_comap_map _ _)`. Set `g₁` to `rP.mapQ P LinearMap.id hrPP`. Establish `hf₁ : Function.Injective f₁`. Use `(injective_iff_map_eq_zero _).2 fun q hq ↦ ?_` and prove the remaining obligations. Proceed by induction on `q using Submodule.Quotient.induction_on with | _ x => ?_`.

Simplify using `only [f₁, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢`. Take `⟨y, hy, hyx⟩` from `hq`. Rewrite using `[← hinj hyx]` and apply the resulting hypothesis. Establish `hg₁ : Function.Surjective g₁` using `fun q ↦ by`. Proceed by induction on `q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩`.

Establish `he₁ : Function.Exact f₁ g₁`. Introduce `q`. Proceed by induction on `q using Submodule.Quotient.induction_on with | _ b => ?_`. Simplify using `only [g₁, f₁, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨Submodule.Quotient.mk x, rfl⟩`. Introduce and unpack `⟨q, hq⟩`. Proceed by induction on `q using Submodule.Quotient.induction_on with | _ x => ?_`. Rewrite `hq` using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`.

Simplify using `using P.sub_mem (hrPP hq) ⟨x, rfl⟩`. Set `f₂` to `P.mapQ rP (r • LinearMap.id) hPr`. Set `g₂` to `rP.mapQ rB LinearMap.id hrPrB`. Establish `hf₂ : Function.Injective f₂`. Use `(injective_iff_map_eq_zero _).2 fun q hq ↦ ?_` and prove the remaining obligations.

Proceed by induction on `q using Submodule.Quotient.induction_on with | _ b => ?_`. Simplify using `only [f₂, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply, LinearMap.id_apply] at hq ⊢`. Take `⟨y, hy, hyb⟩` from `hq`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Use `⟨c, (mul_cancel_left_mem_nonZeroDivisors hr).1 ?_⟩` and prove the remaining obligations.

Simplify `hyb` using `[a, Algebra.smul_def, mul_comm]`. Establish `hg₂ : Function.Surjective g₂` using `fun q ↦ by`. Proceed by induction on `q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩`. Establish `he₂ : Function.Exact f₂ g₂`. Introduce `q`.

Proceed by induction on `q using Submodule.Quotient.induction_on with | _ b => ?_`. Simplify using `only [g₂, f₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 (show b ∈ Ideal.span {algebraMap R B r} from hb)`.

Conclude with `⟨Submodule.Quotient.mk c, by simp [Algebra.smul_def, mul_comm]⟩`. Introduce and unpack `⟨q, hq⟩`. Proceed by induction on `q using Submodule.Quotient.induction_on with | _ c => ?_`. Rewrite `hq` using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`. Establish `hc : r • c ∈ rB` using `Ideal.mem_span_singleton'.2 ⟨c, by simp [Algebra.smul_def, mul_comm]⟩`.

Simplify using `using rB.sub_mem hc (hrPrB hq)`. Establish `h₁` using `Module.length_eq_add_of_exact f₁ g₁ hf₁ hg₁ he₁`. Establish `h₂` using `Module.length_eq_add_of_exact f₂ g₂ hf₂ hg₂ he₂`. Rewrite using `[← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B r})).length_eq]`. Rewrite `h₂` using `[h₁, add_comm]`.

Conclude with `(WithTop.add_left_inj hfin).1 h₂`.
-/
theorem ExtensionQuotientLength.proof : ExtensionQuotientLength.Statement := by
  intro R B _ _ _ r hinj hr hfin
  set a := Algebra.linearMap R B
  set P : Submodule R B := LinearMap.range a
  set rP : Submodule R B := Submodule.map a (Ideal.span {r})
  set rB : Submodule R B := (Ideal.span {algebraMap R B r}).restrictScalars R
  have hrPP : rP ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hrPrB : rP ≤ rB := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact Ideal.mem_span_singleton'.2 ⟨algebraMap R B c, by simp [a]⟩
  have hPr : P ≤ rP.comap (r • LinearMap.id) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r * x, Ideal.mem_span_singleton'.2 ⟨x, mul_comm _ _⟩, by simp [a, Algebra.smul_def]⟩

  let f₁ := (Ideal.span {r}).mapQ rP a (Submodule.le_comap_map _ _)
  let g₁ := rP.mapQ P LinearMap.id hrPP
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    simp only [f₁, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨y, hy, hyx⟩ := hq
    rwa [← hinj hyx]
  have hg₁ : Function.Surjective g₁ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₁ : Function.Exact f₁ g₁ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₁, f₁, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ x => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      simpa using P.sub_mem (hrPP hq) ⟨x, rfl⟩

  let f₂ := P.mapQ rP (r • LinearMap.id) hPr
  let g₂ := rP.mapQ rB LinearMap.id hrPrB
  have hf₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [f₂, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at hq ⊢
    obtain ⟨y, hy, hyb⟩ := hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors hr).1 ?_⟩
    simpa [a, Algebra.smul_def, mul_comm] using hyb
  have hg₂ : Function.Surjective g₂ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₂ : Function.Exact f₂ g₂ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₂, f₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (show b ∈ Ideal.span {algebraMap R B r} from hb)
      exact ⟨Submodule.Quotient.mk c, by simp [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ c => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      have hc : r • c ∈ rB := Ideal.mem_span_singleton'.2 ⟨c, by simp [Algebra.smul_def, mul_comm]⟩
      simpa using rB.sub_mem hc (hrPrB hq)
  have h₁ := Module.length_eq_add_of_exact f₁ g₁ hf₁ hg₁ he₁
  have h₂ := Module.length_eq_add_of_exact f₂ g₂ hf₂ hg₂ he₂
  rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B r})).length_eq]
  rw [h₁, add_comm] at h₂
  exact (WithTop.add_left_inj hfin).1 h₂

end GroundTheory.Heights₂.Heights
