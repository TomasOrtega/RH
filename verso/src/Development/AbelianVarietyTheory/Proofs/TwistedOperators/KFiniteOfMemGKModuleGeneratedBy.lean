import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKGenKFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def kGrp : Subgroup (GA D V) :=
  Subgroup.closure {k | ∃ τ g, GlobalTheory.CuspGK.InK M τ g ∧ k = atTau θ V τ g}

/- English proof (translation)
The claim follows from `(Subgroup.closure_le _).2 fun _ ⟨τ, g, _, e⟩ => e ▸ GlobalTheory.FinTranslate.atTau_mem θ V τ g`.
-/
theorem kGrp_le : kGrp θ M ≤ GinfC V :=
  (Subgroup.closure_le _).2 fun _ ⟨τ, g, _, e⟩ => e ▸ GlobalTheory.FinTranslate.atTau_mem θ V τ g

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [rTr, mul_assoc]`.
-/
theorem rTr_mul (x y : GA D V) (f : GA D V → ℂ) : rTr V (x * y) f = rTr V x (rTr V y f) := by
  funext g
  simp only [rTr, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [rTr, inv_mul_cancel_right]`.
-/
theorem rTr_inv_rTr (x : GA D V) (f : GA D V → ℂ) : rTr V x⁻¹ (rTr V x f) = f := by
  funext g
  simp only [rTr, inv_mul_cancel_right]

/- English proof (translation)
Use `Subgroup.closure_induction (p := fun k _ => ∀ f ∈ W, rTr V k f ∈ W) (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hk` and prove the remaining obligations. Take `⟨τ, g, hg, rfl⟩` from `hx`. Conclude with `hK τ g hg`. Introduce `f hf`. Establish `e : rTr V 1 f = f` using `funext fun g => by simp [rTr]`.

Rewrite using `[e]`. Conclude with `hf`. Introduce `f hf`. Rewrite using `[rTr_mul]`. Conclude with `hx _ (hy f hf)`.

Set `T : W →ₗ[ℂ] W` to `((GlobalTheory.KTypeProj.rTrL x).restrict (p := W) (q := W) fun f hf => hx f hf)`. Establish `hinj : Function.Injective T`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : rTr V x a.1 = rTr V x b.1` using `congrArg Subtype.val hab`.

Establish `h2` using `congrArg (rTr V x⁻¹) h1`. Rewrite `h2` using `[rTr_inv_rTr, rTr_inv_rTr]`. Then use the resulting hypothesis. Establish `hsurj` using `LinearMap.injective_iff_surjective.1 hinj`. Introduce `f hf`. Take `⟨h, hh⟩` from `hsurj ⟨f, hf⟩`.

Establish `e : rTr V x h.1 = f` using `congrArg Subtype.val hh`. Rewrite using `[← e, rTr_inv_rTr]`. Conclude with `h.2`.
-/
theorem rTr_mem_of_kStable {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W)
    (hK : GlobalTheory.KTypeProj.KStable θ M W) {k : GA D V} (hk : k ∈ kGrp θ M) : ∀ f ∈ W, rTr V k f ∈ W := by
  refine Subgroup.closure_induction (p := fun k _ => ∀ f ∈ W, rTr V k f ∈ W) (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hk
  · obtain ⟨τ, g, hg, rfl⟩ := hx
    exact hK τ g hg
  · intro f hf
    have e : rTr V 1 f = f := funext fun g => by simp [rTr]
    rw [e]
    exact hf
  · intro f hf
    rw [rTr_mul]
    exact hx _ (hy f hf)
  · let T : W →ₗ[ℂ] W := ((GlobalTheory.KTypeProj.rTrL x).restrict (p := W) (q := W) fun f hf => hx f hf)
    have hinj : Function.Injective T := by
      intro a b hab
      apply Subtype.ext
      have h1 : rTr V x a.1 = rTr V x b.1 := congrArg Subtype.val hab
      have h2 := congrArg (rTr V x⁻¹) h1
      rwa [rTr_inv_rTr, rTr_inv_rTr] at h2
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    intro f hf
    obtain ⟨h, hh⟩ := hsurj ⟨f, hf⟩
    have e : rTr V x h.1 = f := congrArg Subtype.val hh
    rw [← e, rTr_inv_rTr]
    exact h.2

/- English proof (translation)
Take `⟨W, hW, hm⟩` from `GlobalTheory.Doubling.isKFinite_iff.1 h`. Conclude with `GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => by`. Conclude with `W.smul_mem c (hm k hk)⟩`.
-/
theorem isKFinite_smul {Φ : GA D V → ℂ} {K : Subgroup (GA D V)} (h : GlobalTheory.Doubling.IsKFinite K Φ) (c : ℂ) :
    GlobalTheory.Doubling.IsKFinite K (c • Φ) := by
  obtain ⟨W, hW, hm⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => by
    exact W.smul_mem c (hm k hk)⟩

def kfinSm (hθ : IsInfFam θ) : Submodule ℂ (GA D V → ℂ) where
  carrier := {x | IsAutFunSm θ V x ∧ GlobalTheory.Doubling.IsKFinite (kGrp θ M) x}
  zero_mem' := ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add h.1 h'.1, h.2.add h'.2⟩
  smul_mem' := fun c _ h => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c h.1, isKFinite_smul h.2 c⟩

/- English proof (translation)
Use `⟨GlobalTheory.Doubling.kSpan (kGrp θ M) x, h, Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp⟩, ?_⟩` and prove the remaining obligations. Introduce `τ g hg f hf`. Establish `ha : atTau θ V τ g ∈ kGrp θ M` using `Subgroup.subset_closure ⟨τ, g, hg, rfl⟩`. Establish `hle : GlobalTheory.Doubling.kSpan (kGrp θ M) x ≤ (GlobalTheory.Doubling.kSpan (kGrp θ M) x).comap (GlobalTheory.KTypeProj.rTrL (atTau θ V τ g))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Use `Submodule.subset_span ⟨atTau θ V τ g * k, mul_mem ha hk, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `only [GlobalTheory.KTypeProj.rTrL_apply, rTr, mul_assoc]`. Conclude with `hle hf`.
-/
theorem exists_kStable {x : GA D V → ℂ} (h : GlobalTheory.Doubling.IsKFinite (kGrp θ M) x) :
    ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧ GlobalTheory.KTypeProj.KStable θ M Y := by
  refine ⟨GlobalTheory.Doubling.kSpan (kGrp θ M) x, h, Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp⟩, ?_⟩
  intro τ g hg f hf
  have ha : atTau θ V τ g ∈ kGrp θ M := Subgroup.subset_closure ⟨τ, g, hg, rfl⟩
  have hle : GlobalTheory.Doubling.kSpan (kGrp θ M) x ≤
      (GlobalTheory.Doubling.kSpan (kGrp θ M) x).comap (GlobalTheory.KTypeProj.rTrL (atTau θ V τ g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.subset_span ⟨atTau θ V τ g * k, mul_mem ha hk, ?_⟩
    funext y
    simp only [GlobalTheory.KTypeProj.rTrL_apply, rTr, mul_assoc]
  exact hle hf

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf.1 τ g hg.1, hf.2.translate (Subgroup.subset_closure ⟨τ, g, hg, rfl⟩)⟩ lie τ X hX f hf := ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf.1, GlobalTheory.CuspLie.isKFinite_Rder hθ hX (kGrp_le θ M) hf.1.smooth hf.2⟩`.
-/
theorem isGKSub_kfinSm (hθ : IsInfFam θ) : GlobalTheory.CuspGK.IsGKSub θ M (kfinSm θ M hθ) where
  k τ g hg f hf := ⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf.1 τ g hg.1,
    hf.2.translate (Subgroup.subset_closure ⟨τ, g, hg, rfl⟩)⟩
  lie τ X hX f hf := ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf.1,
    GlobalTheory.CuspLie.isKFinite_Rder hθ hX (kGrp_le θ M) hf.1.smooth hf.2⟩

/- English proof (translation)
Introduce `D θ V S M hθ ψ hψ ⟨W, hW, hψW, hK⟩ x hx`. Establish `hm : ψ ∈ kfinSm θ M hθ` using `⟨hψ, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => rTr_mem_of_kStable θ M hW hK hk ψ hψW⟩⟩`. Conclude with `exists_kStable θ M (GlobalTheory.CuspGK.gkGen_le θ M hm (isGKSub_kfinSm θ M hθ) hx).2`.
-/
theorem kFinite_of_mem_gkGen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ,
    IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  intro D θ V S M hθ ψ hψ ⟨W, hW, hψW, hK⟩ x hx
  have hm : ψ ∈ kfinSm θ M hθ :=
    ⟨hψ, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => rTr_mem_of_kStable θ M hW hK hk ψ hψW⟩⟩
  exact exists_kStable θ M (GlobalTheory.CuspGK.gkGen_le θ M hm (isGKSub_kfinSm θ M hθ) hx).2

end GlobalTheory.GKGenKFin

end
