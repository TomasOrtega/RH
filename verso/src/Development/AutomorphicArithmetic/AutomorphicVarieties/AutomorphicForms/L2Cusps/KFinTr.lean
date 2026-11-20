import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

/- English proof (translation)
Introduce `E _ _ _ a μ _ _ μ₁ _ hp v h`. Establish `hi : Function.Injective (cmp hp)` using `(cmp hp).injective`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `h.1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`.

Establish `e` using `cmpEquiv_holds E a μ μ₁ hp (finGL E a k) v`. Rewrite using `[Set.mem_setOf_eq, Set.mem_setOf_eq, e, hi.eq_iff, Fb.finEmb_eq]`. Use `h.2` as an intermediate fact. Establish `hle : (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v)).map (cmp hp).toLinearMap ≤ Submodule.span ℂ (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (cmp hp v))`. Rewrite using `[Submodule.map_span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨y, hy⟩` from `(Cm.grpEq E a).surjective (k : archGroup E a)`. Establish `hu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)` using `(Cm.grpEq_mem_archCompact y).1 (hy ▸ k.2)`. Use `Submodule.subset_span ⟨⟨y.val, hu⟩, ?_⟩` and prove the remaining obligations. Establish `ey : Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a) = y` using `Units.ext rfl`.

Establish `e` using `cmpEquiv_holds E a μ μ₁ hp (infGL E a y) v`. Simplify using `only [ey]`. Rewrite using `[e, ← Cm.infEmb_grpEq, hy, archRepT_apply, retract_infEmb]`. Both sides reduce to the same expression. Use `Submodule.finiteDimensional_of_le hle` as an intermediate fact.

Conclude with `(Submodule.equivMapOfInjective (cmp hp).toLinearMap hi _).symm.finiteDimensional`.
-/
theorem UpperTheory.V.KernelIndexFullLattice.kFinTr_holds :
    UpperTheory.V.KernelIndexFullLattice.KFinTr := by
  intro E _ _ _ a μ _ _ μ₁ _ hp v h
  have hi : Function.Injective (cmp hp) := (cmp hp).injective
  refine ⟨?_, ?_⟩
  · convert h.1 using 1
    ext k
    have e := cmpEquiv_holds E a μ μ₁ hp (finGL E a k) v
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, e, hi.eq_iff, Fb.finEmb_eq]
  · have := h.2
    have hle : (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v)).map
        (cmp hp).toLinearMap ≤ Submodule.span ℂ
        (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (cmp hp v)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := (Cm.grpEq E a).surjective (k : archGroup E a)
      have hu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := (Cm.grpEq_mem_archCompact y).1 (hy ▸ k.2)
      refine Submodule.subset_span ⟨⟨y.val, hu⟩, ?_⟩
      have ey : Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a) = y := Units.ext rfl
      have e := cmpEquiv_holds E a μ μ₁ hp (infGL E a y) v
      simp only [ey]
      rw [e, ← Cm.infEmb_grpEq, hy, archRepT_apply, retract_infEmb]
      rfl
    have := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective (cmp hp).toLinearMap hi _).symm.finiteDimensional
