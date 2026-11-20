import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnBasicOpenLocalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}

noncomputable def SecOn.chartBasicOpen (hM : M.IsLB) (i : M.ι) (a : Γ(Y, V))
    (h : Y.basicOpen a ≤ M.U i) : SecOn M V →ₗ[Γ(Y, V)] Γ(Y, Y.basicOpen a) where
  toFun s := SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul, RingHom.id_apply, Algebra.smul_def r]
    rfl

/- English proof (translation)
Use `hV.isLocalization_basicOpen a` as an intermediate fact. Take `⟨h₁, h₂⟩` from `secOn_basicOpen_localization Y M V _ a (Y.basicOpen_le a) hM hV.isCompact hV.isQuasiSeparated rfl`. Use `⟨fun x => IsLocalizedModule.map_units (Algebra.linearMap Γ(Y, V) Γ(Y, Y.basicOpen a)) x, fun y => ?_, fun {x₁ x₂} e => ?_⟩` and prove the remaining obligations. Take `⟨k, x, e⟩` from `h₂ ((SecOn.chart hM i h).symm y)`. Use `⟨⟨x, ⟨a ^ k, k, rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `a ^ k • y = SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) x)`. Rewrite using `[e, map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, map_pow]`. Both sides reduce to the same expression. Take `⟨k, hk⟩` from `h₁ (x₁ - x₂) (by`. Rewrite using `[map_sub, sub_eq_zero]`.

Conclude with `(SecOn.chart hM i h).injective e)`. Use `⟨⟨a ^ k, k, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a ^ k • x₁ = a ^ k • x₂`. Rewrite `hk` using `[smul_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem SecOn.isLocalizedModule_chartBasicOpen (hM : M.IsLB) (hV : IsAffineOpen V) (i : M.ι)
    (a : Γ(Y, V)) (h : Y.basicOpen a ≤ M.U i) :
    IsLocalizedModule (Submonoid.powers a) (SecOn.chartBasicOpen hM i a h) := by
  have := hV.isLocalization_basicOpen a
  obtain ⟨h₁, h₂⟩ := secOn_basicOpen_localization Y M V _ a (Y.basicOpen_le a) hM hV.isCompact
    hV.isQuasiSeparated rfl
  refine ⟨fun x => IsLocalizedModule.map_units
    (Algebra.linearMap Γ(Y, V) Γ(Y, Y.basicOpen a)) x, fun y => ?_, fun {x₁ x₂} e => ?_⟩
  · obtain ⟨k, x, e⟩ := h₂ ((SecOn.chart hM i h).symm y)
    refine ⟨⟨x, ⟨a ^ k, k, rfl⟩⟩, ?_⟩
    change a ^ k • y = SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) x)
    rw [e, map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, map_pow]
    rfl
  · obtain ⟨k, hk⟩ := h₁ (x₁ - x₂) (by
      rw [map_sub, sub_eq_zero]
      exact (SecOn.chart hM i h).injective e)
    refine ⟨⟨a ^ k, k, rfl⟩, ?_⟩
    change a ^ k • x₁ = a ^ k • x₂
    rwa [smul_sub, sub_eq_zero] at hk

/- English proof (translation)
Introduce `Y M V hM hV`. Set `s : Set Γ(Y, V)` to `{a | ∃ i, Y.basicOpen a ≤ M.U i}`. Establish `hs : Ideal.span s = ⊤`. Rewrite using `[← hV.self_le_iSup_basicOpen_iff]`. Introduce `x hx`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))`. Take `⟨f, hf, hxf⟩` from `hV.exists_basicOpen_le ⟨x, hi⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩`. Use `choose c hc using fun g : s => g.2`. Establish `hl (g : s)` using `hV.isLocalization_basicOpen g.1`.

Establish `hm (g : s)` using `SecOn.isLocalizedModule_chartBasicOpen hM hV (c g) g.1 (hc g)`. Establish `hfp : Module.FinitePresentation Γ(Y, V) (SecOn M V)` using `Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := fun g => Γ(Y, Y.basicOpen g.1)) (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g)) fun _ => inferInstance`. Establish `hfl : Module.Flat Γ(Y, V) (SecOn M V)` using `Module.flat_of_isLocalized_span Γ(Y, V) (SecOn M V) s hs (fun g => Γ(Y, Y.basicOpen g.1)) (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g)) fun g => IsLocalization.flat _ (Submonoid.powers g.1)`. Conclude with `⟨hfp, Module.Flat.projective_of_finitePresentation⟩`.
-/
theorem secOn_finitePresentation_projective :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V : Y.Opens), M.IsLB → IsAffineOpen V → Module.FinitePresentation Γ(Y, V) (SecOn M V) ∧ Module.Projective Γ(Y, V) (SecOn M V) := by
  intro Y M V hM hV
  let s : Set Γ(Y, V) := {a | ∃ i, Y.basicOpen a ≤ M.U i}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩
  choose c hc using fun g : s => g.2
  have hl (g : s) := hV.isLocalization_basicOpen g.1
  have hm (g : s) := SecOn.isLocalizedModule_chartBasicOpen hM hV (c g) g.1 (hc g)
  have hfp : Module.FinitePresentation Γ(Y, V) (SecOn M V) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g)) fun _ => inferInstance
  have hfl : Module.Flat Γ(Y, V) (SecOn M V) :=
    Module.flat_of_isLocalized_span Γ(Y, V) (SecOn M V) s hs (fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g))
      fun g => IsLocalization.flat _ (Submonoid.powers g.1)
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.AbLaw
