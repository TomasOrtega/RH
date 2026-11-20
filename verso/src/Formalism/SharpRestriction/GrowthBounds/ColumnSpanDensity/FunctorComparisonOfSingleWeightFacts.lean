import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP

namespace Formalism.MainNotions.flipOneThree.Pf

/- English proof (translation)
Set `Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K` to `(MvPolynomial.basisMonomials (I × β) K).constr K (fun m => ∏ i, MvPolynomial.rename (fun v : γ => (i, v)) (f i (MvPolynomial.monomial (m.curry i) 1)))`. Establish `hΦb : ∀ m, Φ (MvPolynomial.basisMonomials (I × β) K m) = ∏ i, MvPolynomial.rename (fun v : γ => (i, v)) (f i (MvPolynomial.monomial (m.curry i) 1))` using `fun m => Module.Basis.constr_basis _ _ _ _`. Establish `hcur : ∀ (g : I → β →₀ ℕ) (i : I), (∑ j, Finsupp.mapDomain (fun v : β => (j, v)) (g j)).curry i = g i`. Introduce `g i`. Use extensionality with `b`.

Rewrite using `[Finsupp.curry_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single i]`. Conclude with `Finsupp.mapDomain_apply (fun a c h => (Prod.ext_iff.1 h).2) _ _`. Introduce `j _ hj`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨c, hc⟩`.

Conclude with `hj (congrArg Prod.fst hc)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Use `⟨Φ, fun P => ?_⟩` and prove the remaining obligations. Set `L : MultilinearMap K (fun _ : I => MvPolynomial β K) (MvPolynomial (I × γ) K)` to `Φ.compMultilinearMap ((MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × β) K)).compLinearMap (fun i => (MvPolynomial.rename (fun v : β => (i, v))).toLinearMap))`.

Set `M : MultilinearMap K (fun _ : I => MvPolynomial β K) (MvPolynomial (I × γ) K)` to `(MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × γ) K)).compLinearMap (fun i => (MvPolynomial.rename (fun v : γ => (i, v))).toLinearMap ∘ₗ f i)`. Establish `hLM : L = M`. Use `Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials β K) fun g => ?_` and prove the remaining obligations. Simplify using `only [L, M, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply, LinearMap.comp_apply, MvPolynomial.rename_monomial]`. Rewrite using `[← MvPolynomial.monomial_sum_one]`.

Establish `hb : (MvPolynomial.monomial (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) (1 : K)) = MvPolynomial.basisMonomials (I × β) K (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i))`. Rewrite using `[MvPolynomial.coe_basisMonomials]`. Rewrite using `[hb, hΦb]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcur]`.

Establish `h` using `congrArg (fun F => F P) hLM`. Simplify `h` using `[L, M]`.
-/
private theorem exists_linearMap_prod_rename_eq {K : Type} [Field K] (I β γ : Type) [Fintype I] [DecidableEq I]
    (f : I → MvPolynomial β K →ₗ[K] MvPolynomial γ K) :
    ∃ Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K,
      ∀ P : I → MvPolynomial β K,
        Φ (∏ i, MvPolynomial.rename (fun v : β => (i, v)) (P i)) =
          ∏ i, MvPolynomial.rename (fun v : γ => (i, v)) (f i (P i)) := by
  classical
  let Φ : MvPolynomial (I × β) K →ₗ[K] MvPolynomial (I × γ) K :=
    (MvPolynomial.basisMonomials (I × β) K).constr K
      (fun m => ∏ i, MvPolynomial.rename (fun v : γ => (i, v))
        (f i (MvPolynomial.monomial (m.curry i) 1)))
  have hΦb : ∀ m, Φ (MvPolynomial.basisMonomials (I × β) K m) =
      ∏ i, MvPolynomial.rename (fun v : γ => (i, v))
        (f i (MvPolynomial.monomial (m.curry i) 1)) :=
    fun m => Module.Basis.constr_basis _ _ _ _
  have hcur : ∀ (g : I → β →₀ ℕ) (i : I),
      (∑ j, Finsupp.mapDomain (fun v : β => (j, v)) (g j)).curry i = g i := by
    intro g i
    ext b
    rw [Finsupp.curry_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · exact Finsupp.mapDomain_apply (fun a c h => (Prod.ext_iff.1 h).2) _ _
    · intro j _ hj
      apply Finsupp.mapDomain_notin_range
      rintro ⟨c, hc⟩
      exact hj (congrArg Prod.fst hc)
    · intro h
      exact absurd (Finset.mem_univ i) h
  refine ⟨Φ, fun P => ?_⟩
  let L : MultilinearMap K (fun _ : I => MvPolynomial β K) (MvPolynomial (I × γ) K) :=
    Φ.compMultilinearMap ((MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × β) K)).compLinearMap
      (fun i => (MvPolynomial.rename (fun v : β => (i, v))).toLinearMap))
  let M : MultilinearMap K (fun _ : I => MvPolynomial β K) (MvPolynomial (I × γ) K) :=
    (MultilinearMap.mkPiAlgebra K I (MvPolynomial (I × γ) K)).compLinearMap
      (fun i => (MvPolynomial.rename (fun v : γ => (i, v))).toLinearMap ∘ₗ f i)
  have hLM : L = M := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials β K) fun g => ?_
    simp only [L, M, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      LinearMap.comp_apply, MvPolynomial.rename_monomial]
    rw [← MvPolynomial.monomial_sum_one]
    have hb : (MvPolynomial.monomial (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) (1 : K)) =
        MvPolynomial.basisMonomials (I × β) K (∑ i, Finsupp.mapDomain (fun v : β => (i, v)) (g i)) := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [hb, hΦb]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcur]
  have h := congrArg (fun F => F P) hLM
  simpa [L, M] using h

/- English proof (translation)
Introduce `K _ S α _ _ TT i`. Set `f : S → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K` to `fun s => if h : s ∈ TT then i ⟨s, h⟩ else (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap`. Take `⟨Φ, hΦ⟩` from `exists_linearMap_prod_rename_eq (K := K) S α (Bool × α) f`. Set `ψ : MvPolynomial (S × (Bool × α)) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K` to `MvPolynomial.aeval (fun x : S × (Bool × α) => if h : x.1 ∈ TT then (MvPolynomial.X ((⟨x.1, h⟩, x.2.1), x.2.2) : MvPolynomial ((TT × Bool) × α) K) else 0)`. Use `⟨ψ.toLinearMap ∘ₗ Φ, fun P hP => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, hΦ, AlgHom.toLinearMap_apply, map_prod]`. Establish `key : ∀ s : S, ψ (MvPolynomial.rename (fun v : Bool × α => (s, v)) (f s (P s))) = if h : s ∈ TT then MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) (i ⟨s, h⟩ (P s)) else 1`. Introduce `s`. Distinguish the cases in `h : s ∈ TT`. Rewrite using `[dif_pos h]`.

Establish `hf : f s = i ⟨s, h⟩` using `by simp only [f, dif_pos h]`. Rewrite using `[hf]`. Establish `hc : ψ.comp (MvPolynomial.rename (fun v : Bool × α => (s, v))) = MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `[ψ, h]`. Conclude with `congrArg (fun F : MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K => F (i ⟨s, h⟩ (P s))) hc`. Rewrite using `[dif_neg h]`. Establish `hf : f s = (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap`. Simplify using `only [f, dif_neg h]`.

Rewrite using `[hf, hP s h]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl fun s _ => key s]`. Rewrite using `[← Finset.prod_subset (Finset.subset_univ TT) (fun s _ hs => dif_neg hs)]`. Rewrite using `[← Finset.prod_coe_sort TT]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos s.2]`.
-/
theorem existsIO' : ExistsIO := by
  intro K _ S α _ _ TT i
  classical
  let f : S → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K := fun s =>
    if h : s ∈ TT then i ⟨s, h⟩
    else (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_prod_rename_eq (K := K) S α (Bool × α) f
  let ψ : MvPolynomial (S × (Bool × α)) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K :=
    MvPolynomial.aeval (fun x : S × (Bool × α) =>
      if h : x.1 ∈ TT then (MvPolynomial.X ((⟨x.1, h⟩, x.2.1), x.2.2) : MvPolynomial ((TT × Bool) × α) K)
      else 0)
  refine ⟨ψ.toLinearMap ∘ₗ Φ, fun P hP => ?_⟩
  rw [LinearMap.comp_apply, hΦ, AlgHom.toLinearMap_apply, map_prod]
  have key : ∀ s : S, ψ (MvPolynomial.rename (fun v : Bool × α => (s, v)) (f s (P s))) =
      if h : s ∈ TT then
        MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) (i ⟨s, h⟩ (P s))
      else 1 := by
    intro s
    by_cases h : s ∈ TT
    · rw [dif_pos h]
      have hf : f s = i ⟨s, h⟩ := by simp only [f, dif_pos h]
      rw [hf]
      have hc : ψ.comp (MvPolynomial.rename (fun v : Bool × α => (s, v))) =
          MvPolynomial.rename (fun v : Bool × α => (((⟨s, h⟩ : TT), v.1), v.2)) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [ψ, h]
      exact congrArg (fun F : MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((TT × Bool) × α) K =>
        F (i ⟨s, h⟩ (P s))) hc
    · rw [dif_neg h]
      have hf : f s = (MvPolynomial.aeval (fun _ : α => (0 : MvPolynomial (Bool × α) K))).toLinearMap := by
        simp only [f, dif_neg h]
      rw [hf, hP s h]
      simp
  rw [Finset.prod_congr rfl fun s _ => key s]
  rw [← Finset.prod_subset (Finset.subset_univ TT) (fun s _ hs => dif_neg hs)]
  rw [← Finset.prod_coe_sort TT]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [dif_pos s.2]

/- English proof (translation)
Introduce `K _ S α _ _ TT pr`. Take `⟨Φ, hΦ⟩` from `exists_linearMap_prod_rename_eq (K := K) TT (Bool × α) α pr`. Use `⟨(MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))).toLinearMap ∘ₗ Φ ∘ₗ (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2)))).toLinearMap, fun Y => ?_⟩` and prove the remaining obligations. Establish `h1 : (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2)))) (∏ s : TT, MvPolynomial.rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) = ∏ s : TT, MvPolynomial.rename (fun v : Bool × α => (s, v)) (Y s)`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_congr rfl fun s _ => (MvPolynomial.rename_rename _ _ _).trans rfl`. Establish `h2 : ∀ s : TT, MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2)) (MvPolynomial.rename (fun v : α => (s, v)) (pr s (Y s))) = MvPolynomial.rename (fun v : α => ((s : S), v)) (pr s (Y s))` using `fun s => (MvPolynomial.rename_rename _ _ _).trans rfl`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[h1, hΦ, map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => h2 s`.
-/
theorem existsPR' : ExistsPR := by
  intro K _ S α _ _ TT pr
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_prod_rename_eq (K := K) TT (Bool × α) α pr
  refine ⟨(MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))).toLinearMap ∘ₗ Φ ∘ₗ
    (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2)))).toLinearMap, fun Y => ?_⟩
  have h1 : (MvPolynomial.rename (fun x : (TT × Bool) × α => (x.1.1, (x.1.2, x.2))))
      (∏ s : TT, MvPolynomial.rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) =
      ∏ s : TT, MvPolynomial.rename (fun v : Bool × α => (s, v)) (Y s) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => (MvPolynomial.rename_rename _ _ _).trans rfl
  have h2 : ∀ s : TT, MvPolynomial.rename (fun x : TT × α => ((x.1 : S), x.2))
      (MvPolynomial.rename (fun v : α => (s, v)) (pr s (Y s))) =
      MvPolynomial.rename (fun v : α => ((s : S), v)) (pr s (Y s)) :=
    fun s => (MvPolynomial.rename_rename _ _ _).trans rfl
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [h1, hΦ, map_prod]
  exact Finset.prod_congr rfl fun s _ => h2 s

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ N y hy` and use `KP.regroup N y hy`.
-/
theorem regroupP : RegroupP := fun _ _ _ _ _ _ _ _ _ N y hy => KP.regroup N y hy

/- English proof (translation)
The claim follows from `functor_comparison_of_single_weight existsIO' existsPR' regroupP h`.
-/
theorem functor_comparison_of_single_weight_facts (h : SingleWeightLatticeComparison) : LatticeFunctorComparison := functor_comparison_of_single_weight existsIO' existsPR' regroupP h

end Formalism.MainNotions.flipOneThree.Pf
