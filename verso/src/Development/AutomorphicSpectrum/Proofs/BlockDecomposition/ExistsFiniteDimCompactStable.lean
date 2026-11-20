import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscKfin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

/- English proof (translation)
Establish `h : finRep E M u * cptRep E M k = cptRep E M k * finRep E M u`. Express the relevant statement in the definitionally equal form `rt E M (finGL E M u) * rt E M (infGL E M (Unitary.toUnits k)) = rt E M (infGL E M (Unitary.toUnits k)) * rt E M (finGL E M u)`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Conclude with `LinearMap.congr_fun h a`.
-/
theorem fin_cpt_apply (u : GL (Fin M) (Af E)) (k : Kinf E M) (a : Sm E M) :
    finRep E M u (cptRep E M k a) = cptRep E M k (finRep E M u a) := by
  have h : finRep E M u * cptRep E M k = cptRep E M k * finRep E M u := by
    change rt E M (finGL E M u) * rt E M (infGL E M (Unitary.toUnits k)) =
      rt E M (infGL E M (Unitary.toUnits k)) * rt E M (finGL E M u)
    rw [← map_mul, ← map_mul, infGL_comm]
  exact LinearMap.congr_fun h a

/- English proof (translation)
Set `ev : GA E M → Module.Dual ℂ A` to `fun g => (LinearMap.proj g).comp ((Sm E M).subtype.comp A.subtype)`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Establish `h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`.

Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Establish `h2 : ∀ g, v.1.1 g = 0` using `fun g => hv _ (Submodule.subset_span ⟨g, rfl⟩)`. Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext (Subtype.ext (funext h2))`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0, Submodule.dualAnnihilator_bot]`.

Establish `key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev), Continuous fun k => ξ ⟨cptRep E M k a, hA k a ha⟩`. Introduce `ξ hξ`. Proceed by induction on `hξ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`.

Conclude with `GlobalTheory.CompanionTheory.AdmDiscFin.continuous_slice a g`. Consider the case `zero => exact continuous_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `smul r x _ hx => exact hx.const_smul r`. Conclude with `key (ℓ.comp A.subtype) (hspan ▸ Submodule.mem_top)`.
-/
theorem continuous_coeff (A : Submodule ℂ (Sm E M)) [FiniteDimensional ℂ A]
    (hA : ∀ k, ∀ a ∈ A, cptRep E M k a ∈ A) (ℓ : Sm E M →ₗ[ℂ] ℂ) (a : Sm E M) (ha : a ∈ A) :
    Continuous fun k => ℓ (cptRep E M k a) := by
  let ev : GA E M → Module.Dual ℂ A := fun g =>
    (LinearMap.proj g).comp ((Sm E M).subtype.comp A.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ g, v.1.1 g = 0 := fun g => hv _ (Submodule.subset_span ⟨g, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev),
      Continuous fun k => ξ ⟨cptRep E M k a, hA k a ha⟩ := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact GlobalTheory.CompanionTheory.AdmDiscFin.continuous_slice a g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key (ℓ.comp A.subtype) (hspan ▸ Submodule.mem_top)

end GlobalTheory.CompanionTheory.FinDiscKfin

/- English proof (translation)
Introduce `E _ _ _ N V hV L x hx hL`. Use `haveI hfin : FiniteDimensional ℂ (GlobalTheory.AutGrowth.spanK E N x) := (hV.aut x hx).kfin`. Use `⟨GlobalTheory.AutGrowth.spanK E N x, hfin, GlobalTheory.AutGrowth.self_mem_spanK x, ?_, GlobalTheory.AutGrowth.spanK_stable x, fun ℓ a ha => GlobalTheory.CompanionTheory.FinDiscKfin.continuous_coeff _ (GlobalTheory.AutGrowth.spanK_stable x) ℓ a ha⟩` and prove the remaining obligations. Introduce `a ha`. Use `⟨?_, fun u hu => ?_⟩` and prove the remaining obligations.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`. Conclude with `hV.stable (.cpt k) x hx`. Consider the case `zero => exact V.zero_mem`.

Consider the case `add y z _ _ hy hz => exact V.add_mem hy hz`. Consider the case `smul c y _ hy => exact V.smul_mem c hy`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`.

Express the relevant statement in the definitionally equal form `finRep E N u (cptRep E N k x) = cptRep E N k x`. Rewrite using `[GlobalTheory.CompanionTheory.FinDiscKfin.fin_cpt_apply, hL u hu]`. Consider the case `zero => exact map_zero _`. Consider the case `add y z _ _ hy hz => rw [map_add, hy, hz]`. Consider the case `smul c y _ hy => rw [map_smul, hy]`.
-/
theorem GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V →
      ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) →
      ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧
        (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧
        ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  intro E _ _ _ N V hV L x hx hL
  haveI hfin : FiniteDimensional ℂ (GlobalTheory.AutGrowth.spanK E N x) := (hV.aut x hx).kfin
  refine ⟨GlobalTheory.AutGrowth.spanK E N x, hfin, GlobalTheory.AutGrowth.self_mem_spanK x, ?_,
    GlobalTheory.AutGrowth.spanK_stable x, fun ℓ a ha =>
      GlobalTheory.CompanionTheory.FinDiscKfin.continuous_coeff _ (GlobalTheory.AutGrowth.spanK_stable x) ℓ a ha⟩
  intro a ha
  refine ⟨?_, fun u hu => ?_⟩
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hV.stable (.cpt k) x hx
    | zero => exact V.zero_mem
    | add y z _ _ hy hz => exact V.add_mem hy hz
    | smul c y _ hy => exact V.smul_mem c hy
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      change finRep E N u (cptRep E N k x) = cptRep E N k x
      rw [GlobalTheory.CompanionTheory.FinDiscKfin.fin_cpt_apply, hL u hu]
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, hy]

end
