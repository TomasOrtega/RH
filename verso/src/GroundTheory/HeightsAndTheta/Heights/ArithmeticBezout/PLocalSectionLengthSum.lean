import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLocalSectionLengthSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPiQuotCokerFiniteLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Submodule
open scoped Pointwise

namespace LocalSectionLengthSum

/- English proof (translation)
Set `g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))` to `(f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ`. Establish `hg : Function.Surjective g` using `(Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)`. Establish `hker : LinearMap.ker g = I ⊔ Ideal.span {f}`. Use extensionality with `x`. Simplify using `only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply, Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite `hy` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]`. Establish `hx : x = f * b - (f * b - x)` using `by ring`.

Rewrite using `[hx]`. Conclude with `sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))) (mem_sup_left hy)`. Introduce `hx`. Take `⟨y, hy, z, hz, rfl⟩` from `mem_sup.mp hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hz`.

Use `⟨Submodule.Quotient.mk a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]`. Establish `h : f * a - (y + a * f) = -y` using `by ring`. Rewrite using `[h]`. Conclude with `neg_mem hy`.

Rewrite using `[← hker, (g.quotKerEquivOfSurjective hg).length_eq]`.
-/
theorem length_quot_smul_top_eq {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  let g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I)) :=
    (f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = I ⊔ Ideal.span {f} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul] at hy
      have hx : x = f * b - (f * b - x) := by ring
      rw [hx]
      exact sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
        (mem_sup_left hy)
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have h : f * a - (y + a * f) = -y := by ring
      rw [h]
      exact neg_mem hy
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq]

/- English proof (translation)
Set `g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i)))` to `LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i`. Establish `hg : Function.Surjective g`. Introduce `y`. Use `choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)`. Conclude with `⟨x, funext fun i => by simp [g, hx i]⟩`.

Establish `hker : LinearMap.ker g = f • ⊤`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hx : ∀ i, ∃ y : M i, f • y = x i` using `fun i => by`. Establish `h'` using `congrFun h i`. Simplify `h'` using `[g, mem_smul_pointwise_iff_exists]`. Use `choose y hy using hx`. Conclude with `⟨y, funext hy⟩`.

Introduce and unpack `⟨y, rfl⟩`. Use function extensionality and compare the values at `i`. Conclude with `(Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)`. Rewrite using `[← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]`.
-/
theorem length_pi_quot_smul_top_eq {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by
  let g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i))) :=
    LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by simp [g, hx i]⟩
  have hker : LinearMap.ker g = f • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · intro h
      have hx : ∀ i, ∃ y : M i, f • y = x i := fun i => by
        have h' := congrFun h i
        simpa [g, mem_smul_pointwise_iff_exists] using h'
      choose y hy using hx
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      exact (Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]

end LocalSectionLengthSum

/- English proof (translation)
Introduce `B _ _ _ J f hJ hf hQ`. Take `⟨hinj, hfin⟩` from `hPi B J hJ hQ`. Establish `hfinite` using `J.finite_minimalPrimes_of_isNoetherianRing B`. Set `_ : Fintype J.minimalPrimes` to `hfinite.fintype`. Establish `hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x`.

Introduce `x y hxy`. Use function extensionality and compare the values at `P`. Establish `: (P : Ideal B).IsPrime` using `P.2.1.1`. Establish `h : f • x P = f • y P` using `congrFun hxy P`. Rewrite `h` using `[Algebra.smul_def, Algebra.smul_def]`.

Use `mul_left_cancel₀ ?_ h` and prove the remaining obligations. Rewrite using `[Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hf P P.2`. Establish `e1` using `Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj hreg hfin`. Rewrite using `[← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1, LocalSectionLengthSum.length_pi_quot_smul_top_eq]`.

Repeatedly rewrite using `[LocalSectionLengthSum.length_quot_smul_top_eq]`. Conclude with `(Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset (fun P => hfinite.mem_toFinset) (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm`.
-/
theorem LocalSectionLengthSum.proof (hPi : PiQuotCokerFiniteLength.Statement) :
    LocalSectionLengthSum.Statement := by
  intro B _ _ _ J f hJ hf hQ
  obtain ⟨hinj, hfin⟩ := hPi B J hJ hQ
  have hfinite := J.finite_minimalPrimes_of_isNoetherianRing B
  let _ : Fintype J.minimalPrimes := hfinite.fintype
  have hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x := by
    intro x y hxy
    funext P
    have : (P : Ideal B).IsPrime := P.2.1.1
    have h : f • x P = f • y P := congrFun hxy P
    rw [Algebra.smul_def, Algebra.smul_def] at h
    refine mul_left_cancel₀ ?_ h
    rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf P P.2
  have e1 := Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj
    hreg hfin
  rw [← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1,
    LocalSectionLengthSum.length_pi_quot_smul_top_eq]
  simp_rw [LocalSectionLengthSum.length_quot_smul_top_eq]
  exact (Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset
    (fun P => hfinite.mem_toFinset)
    (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm

end GroundTheory.Heights₂.Heights
