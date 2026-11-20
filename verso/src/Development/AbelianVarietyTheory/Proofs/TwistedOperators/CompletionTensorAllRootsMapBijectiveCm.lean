import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

/- English proof (translation)
Establish `hp : ∀ p : ℂ[X], (fun i => p.eval (a i)) ∈ R`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Use `R.add_mem hp hq` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using the standard rewrite rules. Consider the case `monomial n c`. Use `R.mul_mem (hc c) (R.pow_mem haR n)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[eval_monomial]`. Use `hp (Lagrange.interpolate Finset.univ a x)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Conclude with `(Lagrange.eval_interpolate_at_node x ha.injOn (Finset.mem_univ i)).symm`.
-/
theorem subring_pi_mem_of_const_of_injective {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring (ι → ℂ))
    (hc : ∀ c : ℂ, (fun _ => c) ∈ R) (a : ι → ℂ) (ha : Function.Injective a) (haR : a ∈ R) (x : ι → ℂ) :
    x ∈ R := by
  have hp : ∀ p : ℂ[X], (fun i => p.eval (a i)) ∈ R := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have := R.add_mem hp hq
      convert this using 1
      ext i; simp
    | monomial n c =>
      have := R.mul_mem (hc c) (R.pow_mem haR n)
      convert this using 1
      ext i; simp [eval_monomial]
  have := hp (Lagrange.interpolate Finset.univ a x)
  convert this using 1
  ext i
  exact (Lagrange.eval_interpolate_at_node x ha.injOn (Finset.mem_univ i)).symm

/- English proof (translation)
Use `⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t, ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]`.
-/
theorem exists_extensionEmbedding_eq_ofReal {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) (t : ℝ) : ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = (t : ℂ) := by
  refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t, ?_⟩
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `x`. Establish `hτ : ¬ ComplexEmbedding.IsReal τ.1` using `IsTotallyComplex.complexEmbedding_not_isReal τ.1`. Establish `: ∃ e : E, (τ.1 e).im ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hτ` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `e`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.2 (h e)`.

Take `⟨e, he⟩` from `this`. Use `subring_pi_mem_of_const_of_injective (PsiAll P τ).range ?_ (cxRoots τ.1 P) (cxRoots_injective P τ) ?_ x` and prove the remaining obligations. Introduce `c`. Take `⟨a, ha⟩` from `exists_extensionEmbedding_eq_ofReal hw (c.re - c.im / (τ.1 e).im * (τ.1 e).re)`. Take `⟨b, hb⟩` from `exists_extensionEmbedding_eq_ofReal hw (c.im / (τ.1 e).im)`.

Use `⟨a ⊗ₜ[F] 1 + b ⊗ₜ[F] algebraMap E (Fld P) e, ?_⟩` and prove the remaining obligations. Use extensionality with `i : 1`. Rewrite using `[PsiAll_apply, map_add, Psi_tmul, Psi_tmul, psiL_algebraMap, map_one, ha, hb, mul_one]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨1 ⊗ₜ[F] alpha P, ?_⟩` and prove the remaining obligations.

Use extensionality with `i : 1`. Rewrite using `[PsiAll_apply, Psi_tmul, psiL_alpha, map_one, one_mul]`.
-/
theorem PsiAll_surjective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} [IsTotallyComplex E] {r : ℕ} (P : PPol σ r) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) : Function.Surjective (PsiAll P τ) := by
  intro x
  have hτ : ¬ ComplexEmbedding.IsReal τ.1 := IsTotallyComplex.complexEmbedding_not_isReal τ.1
  have : ∃ e : E, (τ.1 e).im ≠ 0 := by
    by_contra h
    push_neg at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext e
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (h e)
  obtain ⟨e, he⟩ := this
  refine subring_pi_mem_of_const_of_injective (PsiAll P τ).range ?_ (cxRoots τ.1 P) (cxRoots_injective P τ) ?_ x
  · intro c
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal hw (c.re - c.im / (τ.1 e).im * (τ.1 e).re)
    obtain ⟨b, hb⟩ := exists_extensionEmbedding_eq_ofReal hw (c.im / (τ.1 e).im)
    refine ⟨a ⊗ₜ[F] 1 + b ⊗ₜ[F] algebraMap E (Fld P) e, ?_⟩
    ext i : 1
    rw [PsiAll_apply, map_add, Psi_tmul, Psi_tmul, psiL_algebraMap, map_one, ha, hb, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  · refine ⟨1 ⊗ₜ[F] alpha P, ?_⟩
    ext i : 1
    rw [PsiAll_apply, Psi_tmul, psiL_alpha, map_one, one_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM r P w τ`. Use `haveI : IsTotallyReal F := hCM.1`. Use `haveI : IsTotallyComplex E := hCM.2.1`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`.

Establish `hs` using `PsiAll_surjective P hw τ`. Use `⟨?_, hs⟩` and prove the remaining obligations. Use `letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra`. Set `f : w.Completion ⊗[F] Fld P →ₗ[w.Completion] (Fin r → ℂ)` to `{ toFun := PsiAll P τ map_add' := map_add _ map_smul' := fun a y => by`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]`.

Use extensionality with `i`. Rewrite using `[Pi.mul_apply, PsiAll_apply, Psi_tmul, map_one, mul_one, Pi.smul_apply, Algebra.smul_def]`. Use `rfl }`. Establish `hk : Module.finrank w.Completion ℂ = 2`. Rewrite using `[Algebra.finrank_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (RingEquiv.refl ℂ) ?_, Complex.finrank_real_complex]`.

Use extensionality with `x`. Conclude with `InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x`. Use `haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite`.

Use `haveI : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)`. Establish `hd : Module.finrank w.Completion (w.Completion ⊗[F] Fld P) = Module.finrank w.Completion (Fin r → ℂ)`. Rewrite using `[Module.finrank_baseChange, ← Module.finrank_mul_finrank F E (Fld P), h2, finrank_Fld, Module.finrank_pi_fintype]`. Simplify using `[hk, mul_comm]`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) hd).2 hs`.
-/
theorem PsiAll_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  intro F E _ _ _ _ _ σ hCM r P w τ
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hs := PsiAll_surjective P hw τ
  refine ⟨?_, hs⟩
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  let f : w.Completion ⊗[F] Fld P →ₗ[w.Completion] (Fin r → ℂ) :=
    { toFun := PsiAll P τ
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
        ext i
        rw [Pi.mul_apply, PsiAll_apply, Psi_tmul, map_one, mul_one, Pi.smul_apply, Algebra.smul_def]
        rfl }
  have hk : Module.finrank w.Completion ℂ = 2 := by
    rw [Algebra.finrank_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (RingEquiv.refl ℂ) ?_,
      Complex.finrank_real_complex]
    ext x
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite
  haveI : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)
  have hd : Module.finrank w.Completion (w.Completion ⊗[F] Fld P) = Module.finrank w.Completion (Fin r → ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank F E (Fld P), h2, finrank_Fld,
      Module.finrank_pi_fintype]
    simp [hk, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) hd).2 hs

end GlobalTheory.TrEll.RealTorus
