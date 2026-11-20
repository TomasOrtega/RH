import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SplitCpt

/- English proof (translation)
Rewrite using `[cptPart, Subgroup.closure_le]`. Introduce and unpack `t ⟨ht, -⟩`. Conclude with `ht`.
-/
theorem cptPart_le_self' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, -⟩
  exact ht

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Simplify `hk` using `[mul_assoc]`. Introduce `h`. Use `⟨_, h, ?_⟩` and prove the remaining obligations.

Simplify using `[mul_assoc]`.
-/
theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (x c : G) :
    c ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * c * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

/- English proof (translation)
Introduce `H _ _ _ _ σ K d d' _hσc hσ hKo hKc hσK hG y`. Use `set T := twCent (swTw σ) (d, d') with hT`. Use `set Cn := twCent (MonoidHom.id H) (d * σ d') with hCn`. Establish `hKKc : IsCompact (((K.prod K).map (MulAut.conj y).toMonoidHom : Subgroup (H × H)) : Set (H × H))`. Rewrite using `[Subgroup.coe_map, Subgroup.coe_prod]`.

Conclude with `(hKc.prod hKc).image (by show Continuous fun z : H × H => y * z * y⁻¹ fun_prop)`. Establish `hKKcl` using `hKKc.isClosed`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Apply `Subgroup.subset_closure` to reduce the goal to its premises.

Use `⟨ht.1, hKKc.of_isClosed_subset isClosed_closure ?_⟩` and prove the remaining obligations. Conclude with `closure_minimal (fun z hz => (Subgroup.zpowers_le.2 ht.2) hz) hKKcl`. Establish `hmapC : (cptPart T).map (MonoidHom.fst H H) ≤ cptPart Cn`. Rewrite using `[Subgroup.map_le_iff_le_comap, cptPart, Subgroup.closure_le]`. Introduce and unpack `t ⟨htT, htc⟩`.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨((mem_twCent_swTw σ hσ d d' t).1 htT).1, ?_⟩` and prove the remaining obligations. Establish `hC` using `htc.image continuous_fst`. Use `hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩`. Use `set x₃ : H := σ (d'⁻¹ * y.2) with hx₃`. Use `set B : Subgroup H := (Cn ⊓ K.map (MulAut.conj y.1).toMonoidHom) ⊓ (Cn ⊓ K.map (MulAut.conj x₃).toMonoidHom) with hB`. Establish `hB0 : B.relIndex (cptPart Cn) ≠ 0` using `Subgroup.relIndex_inf_ne_zero (hG.2 y.1).2 (hG.2 x₃).2`. Establish `hB1 : B.relIndex ((cptPart T).map (MonoidHom.fst H H)) ≠ 0` using `mt (Subgroup.relIndex_eq_zero_of_le_right hmapC) hB0`.

Establish `hB2 : (B.comap (MonoidHom.fst H H)).relIndex (cptPart T) ≠ 0`. Rewrite using `[Subgroup.relIndex_comap]` and apply the resulting hypothesis. Establish `hB3 : (B.comap (MonoidHom.fst H H) ⊓ cptPart T).relIndex (cptPart T) ≠ 0`. Rewrite using `[Subgroup.inf_relIndex_right]` and apply the resulting hypothesis. Establish `hle : B.comap (MonoidHom.fst H H) ⊓ cptPart T ≤ T ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom`.

Introduce and unpack `c ⟨hcB, hcC⟩`. Establish `hcT : c ∈ T` using `cptPart_le_self' T hcC`. Use `⟨hcT, ?_⟩` and prove the remaining obligations. Establish `h2` using `((mem_twCent_swTw σ hσ d d' c).1 hcT).2`. Establish `hm1 : y.1⁻¹ * c.1 * y.1 ∈ K` using `(mem_map_conj K _ _).1 hcB.1.2`.

Establish `hm3 : x₃⁻¹ * c.1 * x₃ ∈ K` using `(mem_map_conj K _ _).1 hcB.2.2`. Use `(mem_map_conj _ _ _).2 (Subgroup.mem_prod.2 ⟨hm1, ?_⟩)` and prove the remaining obligations. Establish `hs` using `hσK _ hm3`. Establish `e : (y⁻¹ * c * y).2 = σ (x₃⁻¹ * c.1 * x₃)`. Simplify using `only [Prod.snd_mul, Prod.snd_inv, h2, hx₃, map_mul, map_inv, hσ]`.

Use `group`. Use `show (y⁻¹ * c * y).2 ∈ K`. Rewrite using `[e]`. Conclude with `hs`. Conclude with `fun h0 => hB3 (Subgroup.relIndex_eq_zero_of_le_left hle h0)`.
-/
theorem split_cpt : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  intro H _ _ _ _ σ K d d' _hσc hσ hKo hKc hσK hG y
  set T := twCent (swTw σ) (d, d') with hT
  set Cn := twCent (MonoidHom.id H) (d * σ d') with hCn
  have hKKc : IsCompact (((K.prod K).map (MulAut.conj y).toMonoidHom : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    exact (hKc.prod hKc).image (by
      show Continuous fun z : H × H => y * z * y⁻¹
      fun_prop)
  have hKKcl := hKKc.isClosed
  refine ⟨?_, ?_⟩
  · intro t ht
    apply Subgroup.subset_closure
    refine ⟨ht.1, hKKc.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun z hz => (Subgroup.zpowers_le.2 ht.2) hz) hKKcl
  · have hmapC : (cptPart T).map (MonoidHom.fst H H) ≤ cptPart Cn := by
      rw [Subgroup.map_le_iff_le_comap, cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      apply Subgroup.subset_closure
      refine ⟨((mem_twCent_swTw σ hσ d d' t).1 htT).1, ?_⟩
      have hC := htc.image continuous_fst
      refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    set x₃ : H := σ (d'⁻¹ * y.2) with hx₃
    set B : Subgroup H := (Cn ⊓ K.map (MulAut.conj y.1).toMonoidHom) ⊓ (Cn ⊓ K.map (MulAut.conj x₃).toMonoidHom) with hB
    have hB0 : B.relIndex (cptPart Cn) ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero (hG.2 y.1).2 (hG.2 x₃).2
    have hB1 : B.relIndex ((cptPart T).map (MonoidHom.fst H H)) ≠ 0 :=
      mt (Subgroup.relIndex_eq_zero_of_le_right hmapC) hB0
    have hB2 : (B.comap (MonoidHom.fst H H)).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.relIndex_comap]
    have hB3 : (B.comap (MonoidHom.fst H H) ⊓ cptPart T).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.inf_relIndex_right]
    have hle : B.comap (MonoidHom.fst H H) ⊓ cptPart T ≤
        T ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom := by
      rintro c ⟨hcB, hcC⟩
      have hcT : c ∈ T := cptPart_le_self' T hcC
      refine ⟨hcT, ?_⟩
      have h2 := ((mem_twCent_swTw σ hσ d d' c).1 hcT).2
      have hm1 : y.1⁻¹ * c.1 * y.1 ∈ K := (mem_map_conj K _ _).1 hcB.1.2
      have hm3 : x₃⁻¹ * c.1 * x₃ ∈ K := (mem_map_conj K _ _).1 hcB.2.2
      refine (mem_map_conj _ _ _).2 (Subgroup.mem_prod.2 ⟨hm1, ?_⟩)
      have hs := hσK _ hm3
      have e : (y⁻¹ * c * y).2 = σ (x₃⁻¹ * c.1 * x₃) := by
        simp only [Prod.snd_mul, Prod.snd_inv, h2, hx₃, map_mul, map_inv, hσ]
        group
      show (y⁻¹ * c * y).2 ∈ K
      rw [e]
      exact hs
    exact fun h0 => hB3 (Subgroup.relIndex_eq_zero_of_le_left hle h0)

end GlobalTheory.CompanionTheory.SplitCpt
