import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

noncomputable section

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `n ε S hSf hSD hSK N _ _ e he`. Establish `hσ` using `rreg_isURepOn ε`. Establish `hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε))` using `isDerivedOn_smE hσ`. Establish `hE : IsGlRep (smE ε (rreg ε))` using `hD.glRep`. Establish `hKU : IsKUnitary ε (smE ε (rreg ε))` using `isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)`.

Establish `hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, rreg ε k x ∈ S` using `hSK`. Use `haveI := hSf`. Use `haveI hS'f : FiniteDimensional ℂ (S.comap (smD ε (rreg ε)).subtype) := LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm`. Establish `hS'k : IsKStableSub ε (smE ε (rreg ε)) (S.comap (smD ε (rreg ε)).subtype)` using `isKStableSub_of_kStable hσ hD _ hS'f fun k hk v hv => ⟨⟨rreg ε k v, hD.kStable k hk _ v.2⟩, hSK' k hk _ hv, rfl⟩`. Set `T : Fin n → Module.End ℂ (S.comap (smD ε (rreg ε)).subtype)` to `fun c => (smE ε (rreg ε) c c).restrict (hS'k c c rfl)`.

Establish `hTs : ∀ c, (T c).IsSymmetric` using `fun c x z => hKU c c rfl (x : smD ε (rreg ε)) (z : smD ε (rreg ε))`. Establish `hcomm : Pairwise (Function.onFun Commute T)` using `fun a c _ => LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : smD ε (rreg ε)))`. Establish `htop` using `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm`. Set `e' : (S.comap (smD ε (rreg ε)).subtype) →ₗ[ℂ] N` to `e.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap`. Assume the negation of the conclusion as `hno`.

Use `push_neg at hno`. Establish `hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)) ≤ LinearMap.ker e'`. Introduce `χ x hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`.

Conclude with `Submodule.zero_mem _`. Establish `hxc : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = χ c • (x : smD ε (rreg ε))` using `fun c => congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c))`. Establish `hx0' : (x : smD ε (rreg ε)) ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Establish `hxν : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = (((χ c).re : ℝ) : ℂ) • (x : smD ε (rreg ε))` using `fun c => (hxc c).trans (congrArg (· • (x : smD ε (rreg ε))) (kUnit_eig_real hKU hx0' (hxc c)))`. Conclude with `hno (fun c => (χ c).re) (Submodule.comapSubtypeEquivOfLe hSD x) ((isWtOn_iff hσ hD (x : smD ε (rreg ε)) _).2 hxν)`.

Establish `hker : LinearMap.ker e' = ⊤` using `top_le_iff.mp (htop ▸ iSup_le hle)`. Use `he (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Establish `hy : (Submodule.comapSubtypeEquivOfLe hSD).symm y ∈ LinearMap.ker e'` using `hker ▸ Submodule.mem_top`. Establish `h2 : e' ((Submodule.comapSubtypeEquivOfLe hSD).symm y) = 0` using `hy`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `_ = 0 := h2`.
-/
theorem stepWtSpan : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  intro n ε S hSf hSD hSK N _ _ e he
  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hE : IsGlRep (smE ε (rreg ε)) := hD.glRep
  have hKU : IsKUnitary ε (smE ε (rreg ε)) :=
    isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, rreg ε k x ∈ S := hSK
  haveI := hSf
  haveI hS'f : FiniteDimensional ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hS'k : IsKStableSub ε (smE ε (rreg ε)) (S.comap (smD ε (rreg ε)).subtype) :=
    isKStableSub_of_kStable hσ hD _ hS'f fun k hk v hv =>
      ⟨⟨rreg ε k v, hD.kStable k hk _ v.2⟩, hSK' k hk _ hv, rfl⟩
  let T : Fin n → Module.End ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    fun c => (smE ε (rreg ε) c c).restrict (hS'k c c rfl)
  have hTs : ∀ c, (T c).IsSymmetric := fun c x z => hKU c c rfl (x : smD ε (rreg ε)) (z : smD ε (rreg ε))
  have hcomm : Pairwise (Function.onFun Commute T) := fun a c _ =>
    LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : smD ε (rreg ε)))
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm
  let e' : (S.comap (smD ε (rreg ε)).subtype) →ₗ[ℂ] N :=
    e.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap
  by_contra hno
  push_neg at hno
  have hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)) ≤ LinearMap.ker e' := by
    intro χ x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hxc : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = χ c • (x : smD ε (rreg ε)) := fun c =>
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c))
    have hx0' : (x : smD ε (rreg ε)) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxν : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) =
        (((χ c).re : ℝ) : ℂ) • (x : smD ε (rreg ε)) := fun c =>
      (hxc c).trans (congrArg (· • (x : smD ε (rreg ε))) (kUnit_eig_real hKU hx0' (hxc c)))
    exact hno (fun c => (χ c).re) (Submodule.comapSubtypeEquivOfLe hSD x)
      ((isWtOn_iff hσ hD (x : smD ε (rreg ε)) _).2 hxν)
  have hker : LinearMap.ker e' = ⊤ := top_le_iff.mp (htop ▸ iSup_le hle)
  refine he (LinearMap.ext fun y => ?_)
  have hy : (Submodule.comapSubtypeEquivOfLe hSD).symm y ∈ LinearMap.ker e' := hker ▸ Submodule.mem_top
  have h2 : e' ((Submodule.comapSubtypeEquivOfLe hSD).symm y) = 0 := hy
  calc e y = e (Submodule.comapSubtypeEquivOfLe hSD ((Submodule.comapSubtypeEquivOfLe hSD).symm y)) := by
        rw [LinearEquiv.apply_symm_apply]
    _ = 0 := h2

end GlobalTheory.CompanionTheory.RgDsHilb
