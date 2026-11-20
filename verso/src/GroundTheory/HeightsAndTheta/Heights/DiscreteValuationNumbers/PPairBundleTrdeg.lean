import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsAdjoinTrdegAdd
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht`. Take `⟨l, m', hl, hm', hal⟩` from `halg O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht`. Set `gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ` to `fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))`. Set `gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ` to `fun p => C (pairProjCoord y e φ φ' t p) * X p.1`. Set `x : Fin N ⊕ Unit → MvPolynomial (Option (Option K)) Φ` to `Sum.elim (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none)) (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none)`.

Establish `hOΩ : Function.Injective (algebraMap O Ω)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`. Rewrite using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha, map_zero]`.

Rewrite `hmem` using `[hV.noTorsion]`. Simplify using `using hmem`. Establish `hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ))`. Rewrite using `[IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ, MvPolynomial.algebraMap_eq]`. Conclude with `(C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)`.

Establish `hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) = Algebra.trdeg O (Algebra.adjoin O (Set.range gZ))`. Establish `e1` using `(Ideal.quotientKerEquivRange (pointConeMap O (pairProjCoord y e φ φ' t))).trdeg_eq`. Establish `e2 : (pointConeMap O (pairProjCoord y e φ φ' t)).range = Algebra.adjoin O (Set.range gZ)` using `aeval_range _`. Rewrite `e1` using `[e2]`. Conclude with `e1`.

Establish `hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))` using `((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _ ((Option.some_injective _).comp (Option.some_injective _))`. Set `j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ` to `(aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O`. Establish `hjc : j.comp (pointConeMap O y) = aeval gV`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `q`.

Simplify using `[j, gV, pointConeMap, MvPolynomial.algebraMap_apply]`. Establish `hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV))`. Establish `e1` using `(Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq`. Establish `e2` using `((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq`. Rewrite `e2` using `[← AlgHom.range_comp, hjc, aeval_range]`.

Conclude with `e1.trans e2`. Establish `hVZ : Set.range gV ⊆ Set.range gZ`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `⟨⟨some (some q.1), q.2⟩, rfl⟩`. Establish `hxZ : Set.range x ⊆ Set.range gZ`.

Introduce and unpack `_ ⟨i | _, rfl⟩`. Conclude with `⟨⟨some none, l i⟩, rfl⟩`. Conclude with `⟨⟨none, m'⟩, rfl⟩`. Establish `hind'` using `hind Ω Φ K N E e (φ ∘ l) hl t ht _ hm'`. Establish `hle : ∀ a ∈ Algebra.adjoin O (Set.range gV), a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))`.

Introduce `a ha`. Use `Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_restrictScalars]`. Establish `hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))`.

Rewrite using `[← MvPolynomial.algebraMap_apply]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Conclude with `Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)`. Set `f : Algebra.adjoin O (Set.range gV) →+* Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))` to `{ toFun := fun a => ⟨a, hle a a.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Set `_ : Algebra (Algebra.adjoin O (Set.range gV)) (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))` to `f.toAlgebra`.

Establish `: IsScalarTower (Algebra.adjoin O (Set.range gV)) (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) (MvPolynomial (Option (Option K)) Φ)` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) x` using `hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)`. Establish `key` using `hadd O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ) (Fin N ⊕ Unit) x hxZ hxind (by rintro _ ⟨p, rfl⟩; exact hal p)`. Rewrite `key` using `[Set.union_eq_right.mpr hVZ]`. Rewrite using `[hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]`.
-/
theorem PairBundleTrdeg.proof (hadd : AdjoinTrdegAdd.Statement) (hind : PairConeLinesIndep.Statement)
    (halg : PairConeAlg.Statement) : PairBundleTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht

  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (pairProjCoord y e φ φ' t p) * X p.1
  let x : Fin N ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none)

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)

  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O (pairProjCoord y e φ φ' t))).trdeg_eq
    have e2 : (pointConeMap O (pairProjCoord y e φ φ' t)).range = Algebra.adjoin O (Set.range gZ) :=
      aeval_range _
    rw [e2] at e1
    exact e1

  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2

  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, rfl⟩
  have hxZ : Set.range x ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩

  have hind' := hind Ω Φ K N E e (φ ∘ l) hl t ht _ hm'
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let f : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    f.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) x :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)

  have key := hadd O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ) (Fin N ⊕ Unit) x hxZ
    hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
