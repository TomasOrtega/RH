import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LatPair.VolStep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨g, rfl⟩` from `exists_smul_lat (stdLat k n) L`. Establish `h0 : IsCompact (stdLat k n : Set (n → k))`. Use `isCompact_univ_pi fun _ : n => isCompact_int k` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using `only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]`. Establish `h1` using `h0.image (f := fun x : n → k => g.val *ᵥ x) (continuous_const.matrix_mulVec continuous_id)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, mem_smul_iff, Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨_, hx, ?_⟩` and prove the remaining obligations. Use `show g • (g⁻¹ • x) = x`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨y, hy, rfl⟩ show g⁻¹ • (g • y) ∈ _`. Simplify using `using hy`.
-/
theorem isCompact_lat {n : Type} [Fintype n] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsCompact (L : Set (n → k)) := by
  classical
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h0 : IsCompact (stdLat k n : Set (n → k)) := by
    have := isCompact_univ_pi fun _ : n => isCompact_int k
    convert this using 1
    ext x
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have h1 := h0.image (f := fun x : n → k => g.val *ᵥ x) (continuous_const.matrix_mulVec continuous_id)
  convert h1 using 1
  ext x
  simp only [SetLike.mem_coe, mem_smul_iff, Set.mem_image]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    show g • (g⁻¹ • x) = x
    simp
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ • (g • y) ∈ _
    simpa using hy

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use `continuous_pi fun j => ?_` and prove the remaining obligations. Break down `j with r | l` into its components or cases. Conclude with `continuous_apply _`. Distinguish the cases in `h : l.val < i`. Simplify using `only [flagIn, Sum.elim_inr, dif_pos h]`.

Conclude with `continuous_apply _`. Simplify using `only [flagIn, Sum.elim_inr, dif_neg h]`. Conclude with `continuous_const`.
-/
theorem continuous_flagIn {n : Type} (c i : ℕ) : Continuous (flagIn (k := k) (n := n) c i) := by
  refine continuous_pi fun j => ?_
  rcases j with r | l
  · exact continuous_apply _
  · by_cases h : l.val < i
    · simp only [flagIn, Sum.elim_inr, dif_pos h]
      exact continuous_apply _
    · simp only [flagIn, Sum.elim_inr, dif_neg h]
      exact continuous_const

/- English proof (translation)
Use extensionality with `y`. Use `⟨fun h => h.1, fun h => ⟨h, fun l hl => ?_⟩⟩` and prove the remaining obligations. Simplify using `[flagIn, not_lt.2 hl]`.
-/
theorem region_eq {n : Type} (c : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) :
    {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} =
      (fun y : n ⊕ Fin i → k => q.inv • flagIn c i y) ⁻¹' (L : Set (n ⊕ Fin c → k)) := by
  ext y
  refine ⟨fun h => h.1, fun h => ⟨h, fun l hl => ?_⟩⟩
  simp [flagIn, not_lt.2 hl]

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c q ν _ L _ i hi`. Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Establish `ho : IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i}`. Rewrite using `[region_eq]`.

Conclude with `(isClopen_lattice L).2.preimage ((continuous_flagIn c i).const_smul q.inv)`. Use `⟨ho, ?_, ?_⟩` and prove the remaining obligations. Use `ho.measure_ne_zero _ ⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[region_eq]`. Establish `: flagIn (k` using `k) (n := n) c i 0 = 0 := by`.

Use function extensionality and compare the values at `j`. Apply the tactic sequence `rcases j with r | l <;> simp [flagIn]`. Simplify using `[this]`. Establish `hK` using `(isCompact_lat L).image (f := fun (z : n ⊕ Fin c → k) (j : n ⊕ Fin i) => ((q.1 : 𝒪[k]) : k) * z (Sum.map id (Fin.castLE hi) j)) (by fun_prop)`. Use `ne_top_of_le_ne_top (hK.measure_lt_top (μ := Measure.pi fun _ : n ⊕ Fin i => ν)).ne (measure_mono ?_)` and prove the remaining obligations.

Rewrite using `[region_eq]`. Introduce `y hy`. Use `⟨_, hy, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Break down `j with r | l` into its components or cases.

Simplify using `[flagIn, Unif.inv, q.ne_zero]`. Simplify using `[flagIn, Unif.inv, q.ne_zero]`.
-/
theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (q : Unif k) (ν : Measure k) [ν.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k] (i : ℕ), i ≤ c → IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} ∧ volStep ν q L i ≠ 0 ∧ volStep ν q L i ≠ ⊤ := by
  intro k _ _ _ _ _ _ n _ _ c q ν _ L _ i hi
  haveI := secondCountable k
  haveI := t2Space k
  have ho : IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} := by
    rw [region_eq]
    exact (isClopen_lattice L).2.preimage ((continuous_flagIn c i).const_smul q.inv)
  refine ⟨ho, ?_, ?_⟩
  · refine ho.measure_ne_zero _ ⟨0, ?_⟩
    rw [region_eq]
    have : flagIn (k := k) (n := n) c i 0 = 0 := by
      funext j
      rcases j with r | l <;> simp [flagIn]
    simp [this]
  · have hK := (isCompact_lat L).image
      (f := fun (z : n ⊕ Fin c → k) (j : n ⊕ Fin i) => ((q.1 : 𝒪[k]) : k) * z (Sum.map id (Fin.castLE hi) j)) (by fun_prop)
    refine ne_top_of_le_ne_top (hK.measure_lt_top (μ := Measure.pi fun _ : n ⊕ Fin i => ν)).ne (measure_mono ?_)
    rw [region_eq]
    intro y hy
    refine ⟨_, hy, ?_⟩
    funext j
    rcases j with r | l
    · simp [flagIn, Unif.inv, q.ne_zero]
    · simp [flagIn, Unif.inv, q.ne_zero]

end GlobalTheory.LatPair.VolStep
