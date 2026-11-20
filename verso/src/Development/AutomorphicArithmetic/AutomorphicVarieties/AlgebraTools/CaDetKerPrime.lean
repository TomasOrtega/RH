import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartPrime

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `P _ _ ι _ _ z m hind c`. Use `haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime := isPrime_map_C _`. Use `haveI hJ := chartIdeal_localization_isPrime P ι z m hind c (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)) le_rfl`. Establish `key : genKer z m c = Ideal.comap ((algebraMap (MvPolynomial ι P) (Localization.AtPrime (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))).comp MvPolynomial.C) (Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime (Ideal.map (MvPolynomial.C : P →+* …`. Use extensionality with `f`.

Rewrite using `[Ideal.mem_comap, RingHom.comp_apply, IsLocalization.algebraMap_mem_map_algebraMap_iff (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).primeCompl]`. Conclude with `Iff.rfl`. Establish `sub : ∀ f : P, MvPolynomial.C f ∈ chartIdeal z m c → f ∈ genKer z m c`. Introduce `f hf`. Rewrite using `[key, Ideal.mem_comap, RingHom.comp_apply]`.

Conclude with `Ideal.mem_map_of_mem _ hf`. Establish `gen : ∀ k, chartGen z m c k ∈ chartIdeal z m c`. Introduce `k`. Unfold `chartIdeal`. Conclude with `Ideal.subset_span ⟨k, rfl⟩`.

Establish `hinl : ∀ i, ((z.map MvPolynomial.C).mulVec (lam P c)) i ∈ chartIdeal z m c` using `fun i => gen (Sum.inl i)`. Establish `hinr : ∀ j (h : j ≠ c), MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c) ∈ chartIdeal z m c` using `fun j h => gen (Sum.inr ⟨j, h⟩)`. Establish `hdet : MvPolynomial.C z.det ∈ chartIdeal z m c`. Establish `e : ((z.map MvPolynomial.C).adjugate.mulVec ((z.map MvPolynomial.C).mulVec (lam P c))) c = MvPolynomial.C z.det`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, RingHom.map_det]`.

Simplify using `[lam]`. Rewrite using `[← e]`. Use `show (∑ i, (z.map MvPolynomial.C).adjugate c i * ((z.map MvPolynomial.C).mulVec (lam P c)) i) ∈ _`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hinl i)`. Use `⟨by rw [key]; infer_instance, ?_⟩` and prove the remaining obligations.

Unfold `detIdeal relIdeal`. Use `sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (sub _ hdet)))` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Apply `sub` to reduce the goal to its premises. Establish `e : MvPolynomial.C ((z.mulVec m) i) = ((z.map MvPolynomial.C).mulVec (lam P c)) i * MvPolynomial.C (m c) + ∑ j, MvPolynomial.C (z i j) * (MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c))`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `add_mem (Ideal.mul_mem_right _ _ (hinl i)) (Ideal.sum_mem _ fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h : j = c`.

Simplify using `[h, lam]`. Conclude with `Ideal.mul_mem_left _ _ (hinr j h)`.
-/
theorem UpperTheory.V.AlgebraTools.genKer_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c : ι, (genKer z m c).IsPrime ∧ detIdeal z m ≤ genKer z m c := by
  intro P _ _ ι _ _ z m hind c
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C _
  haveI hJ := chartIdeal_localization_isPrime P ι z m hind c
    (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)) le_rfl
  have key : genKer z m c = Ideal.comap
      ((algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))).comp MvPolynomial.C)
      (Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))) (chartIdeal z m c)) := by
    ext f
    rw [Ideal.mem_comap, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).primeCompl]
    exact Iff.rfl
  have sub : ∀ f : P, MvPolynomial.C f ∈ chartIdeal z m c → f ∈ genKer z m c := by
    intro f hf
    rw [key, Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_map_of_mem _ hf
  have gen : ∀ k, chartGen z m c k ∈ chartIdeal z m c := by
    intro k
    unfold chartIdeal
    exact Ideal.subset_span ⟨k, rfl⟩
  have hinl : ∀ i, ((z.map MvPolynomial.C).mulVec (lam P c)) i ∈ chartIdeal z m c :=
    fun i => gen (Sum.inl i)
  have hinr : ∀ j (h : j ≠ c),
      MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c) ∈ chartIdeal z m c :=
    fun j h => gen (Sum.inr ⟨j, h⟩)
  have hdet : MvPolynomial.C z.det ∈ chartIdeal z m c := by
    have e : ((z.map MvPolynomial.C).adjugate.mulVec
        ((z.map MvPolynomial.C).mulVec (lam P c))) c = MvPolynomial.C z.det := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        RingHom.map_det]
      simp [lam]
    rw [← e]
    show (∑ i, (z.map MvPolynomial.C).adjugate c i *
      ((z.map MvPolynomial.C).mulVec (lam P c)) i) ∈ _
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hinl i)
  refine ⟨by rw [key]; infer_instance, ?_⟩
  unfold detIdeal relIdeal
  refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (sub _ hdet)))
  rintro _ ⟨i, rfl⟩
  apply sub
  have e : MvPolynomial.C ((z.mulVec m) i) =
      ((z.map MvPolynomial.C).mulVec (lam P c)) i * MvPolynomial.C (m c) +
        ∑ j, MvPolynomial.C (z i j) * (MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
      mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [e]
  refine add_mem (Ideal.mul_mem_right _ _ (hinl i)) (Ideal.sum_mem _ fun j _ => ?_)
  by_cases h : j = c
  · simp [h, lam]
  · exact Ideal.mul_mem_left _ _ (hinr j h)
