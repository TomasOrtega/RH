import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology

namespace GlobalTheory.RationalDiscrete

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨U, hU, h⟩` from `GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop (F := F) (E := E)` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)` as an intermediate fact. Set `b` to `Module.finBasis F E`. Set `B` to `Algebra.TensorProduct.basis (AF F) b`.

Establish `hc : ∀ k, Continuous (B.coord k)` using `fun k => IsModuleTopology.continuous_of_linearMap _`. Use `⟨⋂ k, B.coord k ⁻¹' U, Filter.iInter_mem.2 fun k => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `(hc k).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)`. Use `b.ext_elem fun k => ?_` and prove the remaining obligations. Rewrite using `[map_zero, Finsupp.zero_apply]`.

Use `h _ ?_` and prove the remaining obligations. Establish `hk : B.repr ((1 : AF F) ⊗ₜ[F] x) k ∈ U` using `Set.mem_iInter.1 hx k`. Rewrite `hk` using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `using hk`.
-/
theorem exists_nhds_zero_inclR :
    ∃ U ∈ 𝓝 (0 : AF F ⊗[F] E), ∀ x : E, inclR (F := F) (AF F) x ∈ U → x = 0 := by
  obtain ⟨U, hU, h⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop (F := F) (E := E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
  refine ⟨⋂ k, B.coord k ⁻¹' U, Filter.iInter_mem.2 fun k => ?_, fun x hx => ?_⟩
  · exact (hc k).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
  · refine b.ext_elem fun k => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine h _ ?_
    have hk : B.repr ((1 : AF F) ⊗ₜ[F] x) k ∈ U := Set.mem_iInter.1 hx k
    rw [Algebra.TensorProduct.basis_repr_tmul] at hk
    simpa using hk

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)` as an intermediate fact. Take `⟨U, hU, h⟩` from `exists_nhds_zero_inclR (F := F) (E := E)`. Use `discreteTopology_of_isOpen_singleton_one ?_` and prove the remaining obligations. Set `f : HFinIn (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E)` to `fun g => ((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1`. Establish `hf : Continuous f` using `(Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const`.

Establish `hf1 : f 1 = 0` using `sub_self _`. Rewrite using `[isOpen_singleton_iff_nhds_eq_pure]`. Use `le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)` and prove the remaining obligations. Establish `hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : HFinIn (AF F) σ J)` using `Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by show U ∈ 𝓝 (f 1 i j)`. Rewrite using `[hf1]`.

Conclude with `hU)`. Use `Filter.mem_of_superset hW fun g hg => ?_` and prove the remaining obligations. Take `⟨γ, -, hγ⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)`. Establish `hfg : ∀ i j, f g i j = inclR (F` using `F) (AF F) (((γ : Matrix (Fin M) (Fin M) E) - 1 : Matrix (Fin M) (Fin M) E) i j) := by`. Introduce `i j`.

Use `show (((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j = _`. Rewrite using `[← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply, apply_ite (inclR (F := F) (AF F)), map_one, map_zero]`. Both sides reduce to the same expression. Establish `hγ1 : γ = 1`. Use `Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))` and prove the remaining obligations.

Rewrite using `[Units.val_one, ← hfg]`. Conclude with `Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j`. Use `Subtype.ext (Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[← hγ, hγ1, map_one]`. Both sides reduce to the same expression.
-/
theorem discreteTopology_HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    DiscreteTopology (HFinIn (AF F) σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : HFinIn (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : HFinIn (AF F) σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin M) (Fin M) E) - 1 : Matrix (Fin M) (Fin M) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D V` and use `discreteTopology_HFinIn D.sp.cm.sig V.gram`.
-/
theorem discreteTopology_GQ : ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) :=
  fun D V => discreteTopology_HFinIn D.sp.cm.sig V.gram

end GlobalTheory.RationalDiscrete
