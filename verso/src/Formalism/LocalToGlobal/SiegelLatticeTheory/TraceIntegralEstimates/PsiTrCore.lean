import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PsiTrCoreApprox
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PsiTrCoreTrace

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.S.Pv.PsiTrCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `show _ ∈ Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)`. Unfold `Formalism.UG.tensInt`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Use `⟨⟨(o : E), o, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[Formalism.UG.inclE]`.
-/
theorem incl_mem (o : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) (o : E) ∈ IntAf F E := by
  show _ ∈ Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)
  unfold Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(o : E), o, rfl⟩, ?_⟩
  simp [Formalism.UG.inclE]

/- English proof (translation)
Use `show _ ∈ Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)`. Unfold `Formalism.UG.tensInt`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `right`. Conclude with `⟨⟨c, hc⟩, rfl⟩`.
-/
theorem one_tmul_mem (c : Af F) (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] c ∈ IntAf F E := by
  show _ ∈ Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)
  unfold Formalism.UG.tensInt
  apply Subring.subset_closure
  right
  exact ⟨⟨c, hc⟩, rfl⟩

def congSub (n : ℤ) : Subring (E ⊗[F] Af F) where
  carrier := {t | ∃ o : 𝓞 E, ∃ s ∈ IntAf F E,
    t = Formalism.UG.inclE (F := F) (Af F) (o : E) + (n : E ⊗[F] Af F) * s}
  zero_mem' := ⟨0, 0, zero_mem _, by simp [RingOfIntegers.coe_eq_algebraMap]⟩
  one_mem' := ⟨1, 0, zero_mem _, by simp [RingOfIntegers.coe_eq_algebraMap]⟩
  add_mem' := by
    rintro _ _ ⟨o, s, hs, rfl⟩ ⟨o', s', hs', rfl⟩
    refine ⟨o + o', s + s', add_mem hs hs', ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add]
    ring
  neg_mem' := by
    rintro _ ⟨o, s, hs, rfl⟩
    refine ⟨-o, -s, neg_mem hs, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_neg]
    ring
  mul_mem' := by
    rintro _ _ ⟨o, s, hs, rfl⟩ ⟨o', s', hs', rfl⟩
    refine ⟨o * o', Formalism.UG.inclE (F := F) (Af F) (o : E) * s' + s * Formalism.UG.inclE (F := F) (Af F) (o' : E) +
      (n : E ⊗[F] Af F) * s * s', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem (incl_mem o) hs') (mul_mem hs (incl_mem o')))
        (mul_mem (mul_mem (intCast_mem _ n) hs) hs')
    · simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring

/- English proof (translation)
Use `show Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) ≤ congSub n`. Unfold `Formalism.UG.tensInt`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)`. Take `⟨o, rfl⟩` from `hx`.

Use `⟨o, 0, zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.UG.inclE]`. Establish `hc' : ∀ v, c v ∈ v.adicCompletionIntegers F` using `hc`. Establish `hnF : (n : F) ≠ 0` using `by exact_mod_cast hn`. Take `⟨b, hb⟩` from `exists_approx c hc' (n : 𝓞 F) (by exact_mod_cast hn)`.

Use `set c' : Af F := (c - algebraMap F (Af F) (b : F)) * algebraMap F (Af F) ((n : F)⁻¹) with hc'def`. Establish `h1 : (n : Af F) * algebraMap F (Af F) ((n : F)⁻¹) = 1`. Rewrite using `[← map_intCast (algebraMap F (Af F)) n, ← map_mul, mul_inv_cancel₀ hnF, map_one]`. Establish `key : (n : Af F) * c' = c - algebraMap F (Af F) (b : F)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hc'def]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = c - algebraMap F (Af F) (b : F) := by rw [h1, mul_one]`. Establish `hc'int : ∀ v, c' v ∈ v.adicCompletionIntegers F`. Introduce `v`.

Establish `e : c' v = (c v - algebraMap F (v.adicCompletion F) (b : F)) * algebraMap F (v.adicCompletion F) ((n : F)⁻¹)`. Rewrite using `[hc'def]`. Both sides reduce to the same expression. Establish `hnv : Valued.v (algebraMap F (v.adicCompletion F) (n : F)) = v.intValuation (n : 𝓞 F)`. Rewrite using `[← map_intCast (algebraMap (𝓞 F) F) n]`.

Conclude with `(v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap _)`. Establish `hn0 : v.intValuation (n : 𝓞 F) ≠ 0`. Rewrite using `[← hnv, Valuation.ne_zero_iff]`. Conclude with `(map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hnF`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, e, map_mul, map_inv₀, map_inv₀, hnv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hB : Formalism.UG.inclE (F` using `F) (Af F) ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = (1 : E) ⊗ₜ[F] algebraMap F (Af F) (b : F) := by`. Establish `hcoe : ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = algebraMap F E (b : F)` using `by first`. Consider the case `rfl`. Consider the case `simp [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply]`.

Rewrite using `[hcoe]`. Simplify using `only [Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply]`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Establish `hn' : ((n : ℤ) : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (n : Af F)`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply, map_intCast]`.

Use `⟨algebraMap (𝓞 F) (𝓞 E) b, (1 : E) ⊗ₜ[F] c', one_tmul_mem c' hc'int, ?_⟩` and prove the remaining obligations. Rewrite using `[hB, hn', Algebra.TensorProduct.tmul_mul_tmul, one_mul, key, ← TensorProduct.tmul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem intAf_le_congSub (n : ℤ) (hn : n ≠ 0) : IntAf F E ≤ congSub n := by
  show Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) ≤ congSub n
  unfold Formalism.UG.tensInt
  rw [Subring.closure_le]
  rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
  · obtain ⟨o, rfl⟩ := hx
    refine ⟨o, 0, zero_mem _, ?_⟩
    simp [Formalism.UG.inclE]
  · have hc' : ∀ v, c v ∈ v.adicCompletionIntegers F := hc
    have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
    obtain ⟨b, hb⟩ := exists_approx c hc' (n : 𝓞 F) (by exact_mod_cast hn)
    set c' : Af F := (c - algebraMap F (Af F) (b : F)) * algebraMap F (Af F) ((n : F)⁻¹) with hc'def
    have h1 : (n : Af F) * algebraMap F (Af F) ((n : F)⁻¹) = 1 := by
      rw [← map_intCast (algebraMap F (Af F)) n, ← map_mul, mul_inv_cancel₀ hnF, map_one]
    have key : (n : Af F) * c' = c - algebraMap F (Af F) (b : F) := by
      calc (n : Af F) * c'
          = (c - algebraMap F (Af F) (b : F)) * ((n : Af F) * algebraMap F (Af F) ((n : F)⁻¹)) := by
            rw [hc'def]; ring
        _ = c - algebraMap F (Af F) (b : F) := by rw [h1, mul_one]
    have hc'int : ∀ v, c' v ∈ v.adicCompletionIntegers F := by
      intro v
      have e : c' v = (c v - algebraMap F (v.adicCompletion F) (b : F)) *
          algebraMap F (v.adicCompletion F) ((n : F)⁻¹) := by
        rw [hc'def]; rfl
      have hnv : Valued.v (algebraMap F (v.adicCompletion F) (n : F)) = v.intValuation (n : 𝓞 F) := by
        rw [← map_intCast (algebraMap (𝓞 F) F) n]
        exact (v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap _)
      have hn0 : v.intValuation (n : 𝓞 F) ≠ 0 := by
        rw [← hnv, Valuation.ne_zero_iff]
        exact (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hnF
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, e, map_mul, map_inv₀, map_inv₀, hnv]
      calc Valued.v (c v - algebraMap F (v.adicCompletion F) (b : F)) * (v.intValuation (n : 𝓞 F))⁻¹
          ≤ v.intValuation (n : 𝓞 F) * (v.intValuation (n : 𝓞 F))⁻¹ := by gcongr; exact hb v
        _ = 1 := mul_inv_cancel₀ hn0
    have hB : Formalism.UG.inclE (F := F) (Af F) ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) =
        (1 : E) ⊗ₜ[F] algebraMap F (Af F) (b : F) := by
      have hcoe : ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = algebraMap F E (b : F) := by
        first
        | rfl
        | simp [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
      rw [hcoe]
      simp only [Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have hn' : ((n : ℤ) : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (n : Af F) := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
    refine ⟨algebraMap (𝓞 F) (𝓞 E) b, (1 : E) ⊗ₜ[F] c', one_tmul_mem c' hc'int, ?_⟩
    rw [hB, hn', Algebra.TensorProduct.tmul_mul_tmul, one_mul, key, ← TensorProduct.tmul_add]
    congr 1
    abel

/- English proof (translation)
Establish `h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ a`. Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings]`. Establish `h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ a = ∑ φ : K →+* ℂ, φ a` using `(Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ a) (fun σ : K →ₐ[ℚ] ℂ => σ a) (fun φ => rfl)).symm`. Establish `h3 : ∑ v : InfinitePlace K, v.embedding a = ∑ φ : K →+* ℂ, φ a`. Use `Fintype.sum_bijective (fun v : InfinitePlace K => v.embedding) ⟨fun v w h => ?_, fun φ => ?_⟩ _ _ (fun v => rfl)` and prove the remaining obligations.

Simplify `congrArg InfinitePlace.mk h` using `[InfinitePlace.mk_embedding]`. Conclude with `⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp (hK.isReal _))⟩`. Rewrite using `[h3, h1]`. Conclude with `h2.symm`.
-/
private lemma sum_embedding_eq_trace_of_totallyReal {K : Type} [Field K] [NumberField K]
    (hK : NumberField.IsTotallyReal K) (a : K) :
    ∑ v : InfinitePlace K, v.embedding a = ((Algebra.trace ℚ K a : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ a := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings]
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ a = ∑ φ : K →+* ℂ, φ a :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ a) (fun σ : K →ₐ[ℚ] ℂ => σ a)
      (fun φ => rfl)).symm
  have h3 : ∑ v : InfinitePlace K, v.embedding a = ∑ φ : K →+* ℂ, φ a := by
    refine Fintype.sum_bijective (fun v : InfinitePlace K => v.embedding) ⟨fun v w h => ?_, fun φ => ?_⟩
      _ _ (fun v => rfl)
    · simpa [InfinitePlace.mk_embedding] using congrArg InfinitePlace.mk h
    · exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.mp (hK.isReal _))⟩
  rw [h3, h1]
  exact h2.symm

/- English proof (translation)
Take `⟨a, ha⟩` from `(I.cm.fixed (z + star z)).mp (by rw [star_add, star_star, add_comm])`. Establish `hφ : ∀ v, I.φ v z + star (I.φ v z) = v.embedding a`. Introduce `v`. Establish `hs : star (I.φ v z) = I.φ v (star z)`. Rewrite using `[I.cm.cmUnram.2.1, starRingEnd_apply]`.

Rewrite using `[hs, ← map_add, ← ha, I.φ_over]`. Establish `hTr : Algebra.trace I.F I.E z = a`. Set `e : I.E ≃ₐ[I.F] I.E` to `AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => by`. Rewrite using `[starRingAut_apply]`. Conclude with `(I.cm.fixed _).mpr ⟨x, rfl⟩)`.

Establish `e1 : Algebra.trace I.F I.E (star z) = Algebra.trace I.F I.E z` using `by first`. Consider the case `exact Algebra.trace_eq_of_algEquiv e z`. Consider the case `exact (Algebra.trace_eq_of_algEquiv e z).symm`. Establish `e2 : Algebra.trace I.F I.E (z + star z) = 2 • a`. Rewrite using `[← ha, Algebra.trace_algebraMap, I.cm.deg2]`.

Rewrite `e2` using `[map_add, e1, two_nsmul]`. Establish `e3 : (2 : I.F) * Algebra.trace I.F I.E z = 2 * a` using `by rw [two_mul, two_mul, e2]`. Conclude with `mul_left_cancel₀ two_ne_zero e3`. Rewrite using `[Finset.sum_congr rfl (fun v _ => hφ v), sum_embedding_eq_trace_of_totallyReal I.cm.totReal a, ← Algebra.trace_trace (S := I.F) (T := I.E), hTr]`.
-/
private lemma sum_phi_add_star_eq_trace (I : AutInst) (z : I.E) :
    ∑ v, (I.φ v z + star (I.φ v z)) = ((Algebra.trace ℚ I.E z : ℚ) : ℂ) := by
  obtain ⟨a, ha⟩ := (I.cm.fixed (z + star z)).mp (by rw [star_add, star_star, add_comm])
  have hφ : ∀ v, I.φ v z + star (I.φ v z) = v.embedding a := by
    intro v
    have hs : star (I.φ v z) = I.φ v (star z) := by
      rw [I.cm.cmUnram.2.1, starRingEnd_apply]
    rw [hs, ← map_add, ← ha, I.φ_over]
  have hTr : Algebra.trace I.F I.E z = a := by
    let e : I.E ≃ₐ[I.F] I.E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => by
      rw [starRingAut_apply]; exact (I.cm.fixed _).mpr ⟨x, rfl⟩)
    have e1 : Algebra.trace I.F I.E (star z) = Algebra.trace I.F I.E z := by
      first
      | exact Algebra.trace_eq_of_algEquiv e z
      | exact (Algebra.trace_eq_of_algEquiv e z).symm
    have e2 : Algebra.trace I.F I.E (z + star z) = 2 • a := by
      rw [← ha, Algebra.trace_algebraMap, I.cm.deg2]
    rw [map_add, e1, two_nsmul] at e2
    have e3 : (2 : I.F) * Algebra.trace I.F I.E z = 2 * a := by rw [two_mul, two_mul, e2]
    exact mul_left_cancel₀ two_ne_zero e3
  rw [Finset.sum_congr rfl (fun v _ => hφ v), sum_embedding_eq_trace_of_totallyReal I.cm.totReal a,
    ← Algebra.trace_trace (S := I.F) (T := I.E), hTr]

/- English proof (translation)
Introduce `I ψ hadd hint hprod y hy t ht`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN, hNy⟩ : ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : I.E) * y) := by`. Take `⟨⟨N, hN⟩, h⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) y (Algebra.IsIntegral.isIntegral (R := ℚ) y)`. Use `⟨N, nonZeroDivisors.ne_zero hN, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[Submonoid.smul_def, zsmul_eq_mul]`.

Conclude with `h`. Set `o₀ : 𝓞 I.E` to `⟨(N : I.E) * y, hNy⟩`. Take `⟨o, s, hs, rfl⟩` from `intAf_le_congSub (F := I.F) (E := I.E) N hN ht`. Establish `hsplit : (Formalism.UG.inclE (F` using `I.F) (Af I.F) (o : I.E) + (N : I.E ⊗[I.F] Af I.F) * s) * Formalism.UG.inclE (F := I.F) (Af I.F) y = Formalism.UG.inclE (F := I.F) (Af I.F) ((o : I.E) * y) + s * Formalism.UG.inclE (F := I.F) (Af I.F) (o₀ : I.E) := by`. Establish `h0 : (o₀ : I.E) = (N : I.E) * y` using `rfl`.

Rewrite using `[h0, map_mul, map_mul, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, hadd, hint _ (mul_mem hs (incl_mem o₀)), mul_one]`. Take `⟨m, hm⟩` from `hy o`. Establish `hP` using `hprod ((o : I.E) * y)`.

Establish `hexp : ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v ((o : I.E) * y) + star (I.φ v ((o : I.E) * y)))) = 1`. Rewrite using `[← Complex.exp_sum, ← Finset.mul_sum, sum_phi_add_star_eq_trace I, hm]`. Use `push_cast`. Rewrite using `[mul_comm]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`.

Rewrite `hP` using `[hexp, mul_one]`. Conclude with `hP`.
-/
theorem psiTrCore_holds : Formalism.L2.SG.Pf.PsiTrCore := by
  intro I ψ hadd hint hprod y hy t ht
  obtain ⟨N, hN, hNy⟩ : ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : I.E) * y) := by
    obtain ⟨⟨N, hN⟩, h⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) y (Algebra.IsIntegral.isIntegral (R := ℚ) y)
    refine ⟨N, nonZeroDivisors.ne_zero hN, ?_⟩
    rw [Submonoid.smul_def, zsmul_eq_mul] at h
    exact h
  let o₀ : 𝓞 I.E := ⟨(N : I.E) * y, hNy⟩
  obtain ⟨o, s, hs, rfl⟩ := intAf_le_congSub (F := I.F) (E := I.E) N hN ht
  have hsplit : (Formalism.UG.inclE (F := I.F) (Af I.F) (o : I.E) + (N : I.E ⊗[I.F] Af I.F) * s) *
      Formalism.UG.inclE (F := I.F) (Af I.F) y =
      Formalism.UG.inclE (F := I.F) (Af I.F) ((o : I.E) * y) +
        s * Formalism.UG.inclE (F := I.F) (Af I.F) (o₀ : I.E) := by
    have h0 : (o₀ : I.E) = (N : I.E) * y := rfl
    rw [h0, map_mul, map_mul, map_intCast]
    ring
  rw [hsplit, hadd, hint _ (mul_mem hs (incl_mem o₀)), mul_one]
  obtain ⟨m, hm⟩ := hy o
  have hP := hprod ((o : I.E) * y)
  have hexp : ∏ v, Complex.exp (2 * Real.pi * Complex.I *
      (I.φ v ((o : I.E) * y) + star (I.φ v ((o : I.E) * y)))) = 1 := by
    rw [← Complex.exp_sum, ← Finset.mul_sum, sum_phi_add_star_eq_trace I, hm]
    push_cast
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [hexp, mul_one] at hP
  exact hP

end Formalism.L2.S.Pv.PsiTrCore
