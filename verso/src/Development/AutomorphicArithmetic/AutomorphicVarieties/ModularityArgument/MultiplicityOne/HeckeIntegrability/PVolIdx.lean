import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

/- English proof (translation)
Establish `hopen : ∀ g : Γ, IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K' : Set Γ))` using `fun g => hK'.preimage (continuous_const.mul continuous_id)`. Establish `hcov : (K : Set Γ) ⊆ ⋃ k : K, (fun x => (k : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ)`. Introduce `x hx`. Use `Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Simplify using `[K'.one_mem]`.

Take `⟨t, ht⟩` from `hK.elim_finite_subcover _ (fun k : K => hopen (k : Γ)) hcov`. Establish `hmem : ∀ a b : K, ((a : Γ)⁻¹ * (b : Γ) ∈ K') ↔ (QuotientGroup.mk a : K ⧸ K'.subgroupOf K) = QuotientGroup.mk b`. Introduce `a b`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using the standard rewrite rules.

Establish `hfin : Finite (K ⧸ K'.subgroupOf K)`. Use `Finite.of_surjective (fun k : t => (QuotientGroup.mk (k : K) : K ⧸ K'.subgroupOf K)) ?_` and prove the remaining obligations. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`.

Take `⟨k, hk, hx⟩` from `Set.mem_iUnion₂.1 (ht x.2)`. Conclude with `⟨⟨k, hk⟩, (hmem k x).1 hx⟩`. Use `haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)`. Set `s : K ⧸ K'.subgroupOf K → K` to `Quotient.out`. Establish `hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ K'.subgroupOf K) = q` using `fun q => QuotientGroup.out_eq' q`.

Set `f : K ⧸ K'.subgroupOf K → Set Γ` to `fun q => (fun x => ((s q : K) : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ)`. Establish `hU : (K : Set Γ) = ⋃ q, f q`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `Set.mem_iUnion.2 ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hmem _ ⟨x, hx⟩).2 (hs _)`. Introduce `hx`. Take `⟨q, hq⟩` from `Set.mem_iUnion.1 hx`. Establish `h1 : ((s q : K) : Γ)⁻¹ * x ∈ K` using `hle hq`.

Establish `h2` using `K.mul_mem (s q).2 h1`. Simplify using `using h2`. Establish `hdisj : Pairwise (Function.onFun Disjoint f)`. Introduce `p q hpq`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations.

Introduce `x hp hq`. Apply `hpq` to reduce the goal to its premises. Establish `hp' : ((s p : K) : Γ)⁻¹ * x ∈ K'` using `hp`. Establish `hq' : ((s q : K) : Γ)⁻¹ * x ∈ K'` using `hq`. Establish `h3 : ((s p : K) : Γ)⁻¹ * (s q : K) ∈ K'`.

Use `K'.mul_mem hp' (K'.inv_mem hq')` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[← hs p, ← hs q]`. Conclude with `(hmem _ _).1 h3`. Establish `hμ : ∀ q, μ (f q) = μ K'` using `fun q => MeasureTheory.measure_preimage_mul μ _ _`.

Establish `hsum` using `MeasureTheory.measure_iUnion (μ := μ) hdisj (fun q => (hopen _).measurableSet)`. Rewrite `hsum` using `[← hU, tsum_fintype]`. Simplify using `only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum`. Rewrite using `[hsum, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]`. Simplify using `only [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]`.
-/
private theorem haar_measure_rel_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : MeasureTheory.Measure Γ) [μ.IsHaarMeasure]
    (K K' : Subgroup Γ) (hK' : IsOpen (K' : Set Γ)) (hK : IsCompact (K : Set Γ)) (hle : K' ≤ K) :
    (μ K').toReal * (K'.relIndex K : ℕ) = (μ K).toReal := by
  classical
  have hopen : ∀ g : Γ, IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K' : Set Γ)) := fun g =>
    hK'.preimage (continuous_const.mul continuous_id)
  have hcov : (K : Set Γ) ⊆ ⋃ k : K, (fun x => (k : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    simp [K'.one_mem]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun k : K => hopen (k : Γ)) hcov
  have hmem : ∀ a b : K, ((a : Γ)⁻¹ * (b : Γ) ∈ K') ↔
      (QuotientGroup.mk a : K ⧸ K'.subgroupOf K) = QuotientGroup.mk b := by
    intro a b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hfin : Finite (K ⧸ K'.subgroupOf K) := by
    refine Finite.of_surjective
      (fun k : t => (QuotientGroup.mk (k : K) : K ⧸ K'.subgroupOf K)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (ht x.2)
      exact ⟨⟨k, hk⟩, (hmem k x).1 hx⟩
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let s : K ⧸ K'.subgroupOf K → K := Quotient.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ K'.subgroupOf K) = q := fun q =>
    QuotientGroup.out_eq' q
  let f : K ⧸ K'.subgroupOf K → Set Γ := fun q =>
    (fun x => ((s q : K) : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ)
  have hU : (K : Set Γ) = ⋃ q, f q := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      exact (hmem _ ⟨x, hx⟩).2 (hs _)
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
      have h1 : ((s q : K) : Γ)⁻¹ * x ∈ K := hle hq
      have h2 := K.mul_mem (s q).2 h1
      simpa using h2
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro p q hpq
    refine Set.disjoint_left.2 ?_
    intro x hp hq
    apply hpq
    have hp' : ((s p : K) : Γ)⁻¹ * x ∈ K' := hp
    have hq' : ((s q : K) : Γ)⁻¹ * x ∈ K' := hq
    have h3 : ((s p : K) : Γ)⁻¹ * (s q : K) ∈ K' := by
      have := K'.mul_mem hp' (K'.inv_mem hq')
      simpa [mul_assoc] using this
    rw [← hs p, ← hs q]
    exact (hmem _ _).1 h3
  have hμ : ∀ q, μ (f q) = μ K' := fun q =>
    MeasureTheory.measure_preimage_mul μ _ _
  have hsum := MeasureTheory.measure_iUnion (μ := μ) hdisj (fun q => (hopen _).measurableSet)
  rw [← hU, tsum_fintype] at hsum
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]
  simp only [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/- English proof (translation)
Introduce `Γ _ _ _ _ _ μ _ K K' hK' hK hle`. Conclude with `haar_measure_rel_index μ K K' hK' hK hle`.
-/
theorem UpperTheory.V.Z.Mult.Pi.volIdx_pf :
    VolIdx := by
  intro Γ _ _ _ _ _ μ _ K K' hK' hK hle
  exact haar_measure_rel_index μ K K' hK' hK hle
