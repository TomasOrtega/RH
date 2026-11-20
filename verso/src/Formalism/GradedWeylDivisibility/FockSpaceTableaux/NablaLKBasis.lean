import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hi : b i ∈ dualWeyl R k n ν` using `hb.2.1 ▸ Submodule.subset_span ⟨i, rfl⟩`. Conclude with `dualWeylMap R K (algebraMap R K) k n ν (b i) hi`.

Rewrite using `[standardMonomialSpanDomain K k n ν, Submodule.span_le]`. Introduce and unpack `f ⟨K', sz, hsz, I, hsh, rfl⟩`. Rewrite using `[← ldlat_map_bidet (algebraMap R K)]`. Establish `hmem : bideterminant R sz hsz I ∈ Submodule.span R (Set.range b)`. Rewrite using `[hb.2.1, ← hsh]`.

Conclude with `bidetMem R k n K' sz hsz I`. Establish `h1` using `Submodule.mem_map_of_mem (f := (mapAlgHom (Algebra.ofId R K)).toLinearMap) hmem`. Rewrite `h1` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `Submodule.span_le_restrictScalars R K _ h1`.
-/
lemma span_map_weightBasis_eq_dualWeyl {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {k n : ℕ}
    {ν : Fin n → ℕ} {ι : Type} {b : ι → MvPolynomial (Fin k × Fin n) R} {μ : ι → (Fin k → ℕ)}
    (hb : IsWeightBasis R k n ν b μ) :
    Submodule.span K (Set.range fun i => map (algebraMap R K) (b i)) = dualWeyl K k n ν := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b i ∈ dualWeyl R k n ν := hb.2.1 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact dualWeylMap R K (algebraMap R K) k n ν (b i) hi
  · rw [standardMonomialSpanDomain K k n ν, Submodule.span_le]
    rintro f ⟨K', sz, hsz, I, hsh, rfl⟩
    rw [← ldlat_map_bidet (algebraMap R K)]
    have hmem : bideterminant R sz hsz I ∈ Submodule.span R (Set.range b) := by
      rw [hb.2.1, ← hsh]
      exact bidetMem R k n K' sz hsz I
    have h1 := Submodule.mem_map_of_mem (f := (mapAlgHom (Algebra.ofId R K)).toLinearMap) hmem
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_le_restrictScalars R K _ h1

/- English proof (translation)
Introduce `R K _ _ _ _ hinj k n ν ι b μ hb g hg`. Establish `hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K), P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν`. Introduce `A P hP`. Unfold `dualWeyl at hP ⊢`. Rewrite `hP`, the goal using `[Submodule.mem_inf]`.

Take `⟨hP1, hP2⟩` from `hP`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hP1`, the goal using `[mem_weightedHomogeneousSubmodule]`. Establish `hXw : ∀ v : Fin k × Fin n, IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v)`. Introduce `v`.

Simplify using `only [rowAct, aeval_X]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `b _`. Establish `h` using `(isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul (isWeightedHomogeneous_X K (colW k n) (b, v.2))`. Simplify `h` using `[colW]`.

Rewrite using `[P.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `d hd`. Rewrite using `[← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]`. Simplify using `only [map_pow]`.

Establish `hC : rowAct K A (C (coeff d P) : MvPolynomial (Fin k × Fin n) K) = C (coeff d P)`. Simplify using `[rowAct]`. Rewrite using `[hC]`. Establish `h` using `(isWeightedHomogeneous_C (colW k n) (coeff d P)).mul (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))`. Simplify `h` using `[Finsupp.prod, Finsupp.sum]`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢`. Introduce `l j hlj`. Establish `e` using `hP2 l j hlj`. Simplify using `only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢`. Set `A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K` to `aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))`.

Establish `h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r` using `k) l j) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Distinguish the cases in `hv : v.2 = j`. Simplify using `[A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]`.

Simplify using `[A', colAddGen, rowAct, hv]`. Establish `h2 : (rename (R` using `K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) = A'.comp (rename some) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[A', rowAct]`.

Establish `e1` using `congrArg (fun Φ => Φ P) h1`. Establish `e2` using `congrArg (fun Φ => Φ P) h2`. Simplify using `only [AlgHom.comp_apply] at e1 e2`. Rewrite using `[e1, e2, ← map_sub, e, map_zero]`. Establish `hli` using `ldlat_linInd_base (K := K) hinj hb.1`.

Use `⟨hli.map' (rowAct K g⁻¹).toLinearMap (LinearMap.ker_eq_bot.mpr fun x y hxy => ?_), ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (rowAct K g) hxy`. Simplify `e` using `[ldlat_rowAct_inv_left h1 g hg]`. Establish `e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = (rowAct K g⁻¹).toLinearMap '' Set.range (fun i => map (algebraMap R K) (b i))`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[e1, ← Submodule.map_span, span_map_weightBasis_eq_dualWeyl hb]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_map]`.

Take `⟨P, hP, rfl⟩` from `hx`. Conclude with `hinv g⁻¹ P hP`. Introduce `P hP`. Rewrite using `[Submodule.mem_map]`. Conclude with `⟨rowAct K g P, hinv g P hP, ldlat_rowAct_inv_right h1 g hg P⟩`.
-/
theorem nablaLKBasis_of (h1 : RowActMul) (_h2 : SSBasis) : NablaLKBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K),
      P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν := by
    intro A P hP
    unfold dualWeyl at hP ⊢
    rw [Submodule.mem_inf] at hP ⊢
    obtain ⟨hP1, hP2⟩ := hP
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hP1 ⊢
      have hXw : ∀ v : Fin k × Fin n,
          IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v) := by
        intro v
        simp only [rowAct, aeval_X]
        apply IsWeightedHomogeneous.sum
        intro b _
        have h := (isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul
          (isWeightedHomogeneous_X K (colW k n) (b, v.2))
        simpa [colW] using h
      rw [P.as_sum, map_sum]
      apply IsWeightedHomogeneous.sum
      intro d hd
      rw [← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]
      simp only [map_pow]
      have hC : rowAct K A (C (coeff d P) : MvPolynomial (Fin k × Fin n) K) = C (coeff d P) := by
        simp [rowAct]
      rw [hC]
      have h := (isWeightedHomogeneous_C (colW k n) (coeff d P)).mul
        (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))
      simpa [Finsupp.prod, Finsupp.sum] using h
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢
      intro l j hlj
      have e := hP2 l j hlj
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      let A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K :=
        aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))
      have h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r := k) l j) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = j
        · simp [A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
            mul_left_comm]
        · simp [A', colAddGen, rowAct, hv]
      have h2 : (rename (R := K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) =
          A'.comp (rename some) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [A', rowAct]
      have e1 := congrArg (fun Φ => Φ P) h1
      have e2 := congrArg (fun Φ => Φ P) h2
      simp only [AlgHom.comp_apply] at e1 e2
      rw [e1, e2, ← map_sub, e, map_zero]
  have hli := ldlat_linInd_base (K := K) hinj hb.1
  refine ⟨hli.map' (rowAct K g⁻¹).toLinearMap (LinearMap.ker_eq_bot.mpr fun x y hxy => ?_), ?_⟩
  · have e := congrArg (rowAct K g) hxy
    simpa [ldlat_rowAct_inv_left h1 g hg] using e
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) =
        (rowAct K g⁻¹).toLinearMap '' Set.range (fun i => map (algebraMap R K) (b i)) := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, span_map_weightBasis_eq_dualWeyl hb]
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      exact hinv g⁻¹ P hP
    · intro P hP
      rw [Submodule.mem_map]
      exact ⟨rowAct K g P, hinv g P hP, ldlat_rowAct_inv_right h1 g hg P⟩

end Formalism.GradedWeylDivisibility
