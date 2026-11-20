import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ n T hT U hU`. Establish `hι : Topology.IsInducing (fun x : finU E n => ((x : UA E n) : GA E n))` using `Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal`. Rewrite `hU` using `[hι.nhds_eq_comap, Filter.mem_comap]`. Take `⟨V, hV, hVU⟩` from `hU`. Establish `hV' : finGL E n ⁻¹' V ∈ nhds (1 : GL (Fin n) (Af E))` using `GlobalTheory.DefU.LocAdm.continuous_finGL.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hV)`.

Take `⟨S, hS⟩` from `UpperTheory.V.Af.GlobalFixedVectors.exists_KAway_subset (M := 1) hV'`. Use `⟨S ∪ hT.toFinset, fun k hk hk1 => hVU ?_⟩` and prove the remaining obligations. Establish `hall : ∀ u, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u n` using `fun u => by`. Distinguish the cases in `hu : u ∈ T`. Rewrite using `[hk1 u (Finset.mem_union_right _ (hT.mem_toFinset.2 hu))]`.

Conclude with `one_mem _`. Conclude with `hk u hu`. Establish `ent : ∀ (x : UA E n), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u n) → ∀ a b, Matrix.GeneralLinearGroup.map (pFin E) (x : GA E n) a b ∈ UpperTheory.V.Af.Ohat E` using `fun x hx a b => UpperTheory.V.Af.GlobalFixedVectors.mem_Ohat.2 fun u => by`. Take `⟨Q, hQ⟩` from `hx u`. Establish `e : (cLoc u x).val a b ∈ u.adicCompletionIntegers E`.

Rewrite using `[← hQ]`. Conclude with `(Q.val a b).2`. Conclude with `e`. Establish `h1` using `ent _ hall`. Establish `hmem : Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n) ∈ UpperTheory.V.Af.GlobalFixedVectors.KAway n 1 S`.

Use `UpperTheory.V.Af.GlobalFixedVectors.mem_KAway.2 ⟨UpperTheory.V.Af.mem_KLev.2 ⟨h1, fun a b => ?_, fun a b => ?_⟩, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `ent (k : UA E n)⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hall u)) a b`. Use `⟨_, sub_mem (h1 a b) ?_, by rw [Nat.cast_one, one_mul]⟩` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Conclude with `hk1 w (Finset.mem_union_left _ hw)`. Establish `hk2 : Matrix.GeneralLinearGroup.map (pInf E) ((k : UA E n) : GA E n) = 1` using `k.2`.

Establish `e : finGL E n (Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n)) = ((k : UA E n) : GA E n)` using `ga_ext (by rw [pInf_finGL, hk2]) (by rw [pFin_finGL])`. Use `hS hmem` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, e]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → ∀ U ∈ nhds (1 : finU E n), ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : finU E n, (∀ u ∉ T, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u n) → (∀ u ∈ S, cLoc u (k : UA E n) = 1) → k ∈ U := by
  classical
  intro E _ _ _ n T hT U hU
  have hι : Topology.IsInducing (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [hι.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hV' : finGL E n ⁻¹' V ∈ nhds (1 : GL (Fin n) (Af E)) :=
    GlobalTheory.DefU.LocAdm.continuous_finGL.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hV)
  obtain ⟨S, hS⟩ := UpperTheory.V.Af.GlobalFixedVectors.exists_KAway_subset (M := 1) hV'
  refine ⟨S ∪ hT.toFinset, fun k hk hk1 => hVU ?_⟩
  have hall : ∀ u, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u n := fun u => by
    by_cases hu : u ∈ T
    · rw [hk1 u (Finset.mem_union_right _ (hT.mem_toFinset.2 hu))]; exact one_mem _
    · exact hk u hu
  have ent : ∀ (x : UA E n), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u n) → ∀ a b,
      Matrix.GeneralLinearGroup.map (pFin E) (x : GA E n) a b ∈ UpperTheory.V.Af.Ohat E := fun x hx a b =>
    UpperTheory.V.Af.GlobalFixedVectors.mem_Ohat.2 fun u => by
      obtain ⟨Q, hQ⟩ := hx u
      have e : (cLoc u x).val a b ∈ u.adicCompletionIntegers E := by
        rw [← hQ]; exact (Q.val a b).2
      exact e
  have h1 := ent _ hall
  have hmem : Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n) ∈
      UpperTheory.V.Af.GlobalFixedVectors.KAway n 1 S := by
    refine UpperTheory.V.Af.GlobalFixedVectors.mem_KAway.2 ⟨UpperTheory.V.Af.mem_KLev.2 ⟨h1, fun a b => ?_, fun a b => ?_⟩, fun w hw => ?_⟩
    · rw [← map_inv]
      exact ent (k : UA E n)⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hall u)) a b
    · refine ⟨_, sub_mem (h1 a b) ?_, by rw [Nat.cast_one, one_mul]⟩
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact hk1 w (Finset.mem_union_left _ hw)
  have hk2 : Matrix.GeneralLinearGroup.map (pInf E) ((k : UA E n) : GA E n) = 1 := k.2
  have e : finGL E n (Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n)) = ((k : UA E n) : GA E n) :=
    ga_ext (by rw [pInf_finGL, hk2]) (by rw [pFin_finGL])
  have := hS hmem
  rwa [Set.mem_preimage, e] at this
