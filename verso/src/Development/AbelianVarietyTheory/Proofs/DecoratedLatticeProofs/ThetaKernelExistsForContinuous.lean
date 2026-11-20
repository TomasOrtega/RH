import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteTranslatesFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Collect

variable {D : D7}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `GlobalTheory.LocMod.LinSpace.isThetaFunO_add (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) ih`.
-/
theorem theta_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) : IsThetaFunO ψ S T (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `h` using `hsmul 0 f₀ h₀`. Simplify using `using h`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, hadd _ _ (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) (theta_sum s c f hf), hsmul _ _ (hf i), ih]`.
-/
theorem lin_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (Λ : (WO S T → ℂ) → ℂ) (f₀ : WO S T → ℂ)
    (h₀ : IsThetaFunO ψ S T f₀)
    (hadd : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Λ (f + f') = Λ f + Λ f')
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → Λ (c • f) = c * Λ f)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) :
    Λ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Λ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hsmul 0 f₀ h₀
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hadd _ _ (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) (theta_sum s c f hf), hsmul _ _ (hf i), ih]

/- English proof (translation)
Use `set V := Submodule.span ℂ {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ} with hV`. Establish `hmem : ∀ x ∈ K ×ˢ K, omh (io A x, 1) φ ∈ V` using `fun x hx => Submodule.subset_span ⟨x.1, hx.1, x.2, hx.2, rfl⟩`. Establish `hth : ∀ f ∈ V, IsThetaFunO ψ (dblSp A) W f`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem f hf => obtain ⟨g₁, -, g₂, -, rfl⟩ := hf`. Conclude with `hW.om_pres _ _ hφ`. Consider the case `zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ _ _`. Consider the case `add f g _ _ hf hg => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf hg`. Consider the case `smul c f _ hf => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf`.

Set `b` to `Module.finBasis ℂ V`. Use `⟨Module.finrank ℂ V, fun j => (b j : WO (dblSp A) W → ℂ), fun j x => if h : omh (io A x, 1) φ ∈ V then b.coord j ⟨_, h⟩ else 0, fun j => hth _ (b j).2, fun j => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `hQ : Continuous fun y : K ×ˢ K => (⟨omh (io A y.1, 1) φ, hmem y.1 y.2⟩ : V)`. Use `Continuous.subtype_mk (continuous_pi fun w => ?_) _` and prove the remaining obligations.

Conclude with `((hW.om_cont φ hφ w).comp ((continuous_io A).prodMk continuous_const)).comp continuous_subtype_val`. Establish `hcoord : Continuous (b.coord j)` using `LinearMap.continuous_of_finiteDimensional _`. Use `(hcoord.comp hQ).congr fun y => ?_` and prove the remaining obligations. Simplify using `only [Set.restrict_apply, Function.comp_apply, dif_pos (hmem y.1 y.2)]`. Establish `e` using `congrArg Subtype.val (b.sum_repr ⟨_, hmem x hx⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at e`. Use `conv_lhs => rw [← e]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [dif_pos (hmem x hx), Module.Basis.coord_apply]`.
-/
theorem local_rep {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χS χT : (AE D)ˣ →* Circle} {omh : WRep (dblSp A) W}
    (hW : IsWeilDatumO ψ (dblSp A) W χS χT omh) {φ : WO (dblSp A) W → ℂ} (hφ : IsThetaFunO ψ (dblSp A) W φ)
    {K : Set (GA D A)}
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ
      {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ})) :
    ∃ (n : ℕ) (b : Fin n → WO (dblSp A) W → ℂ) (c : Fin n → GA D A × GA D A → ℂ),
      (∀ j, IsThetaFunO ψ (dblSp A) W (b j)) ∧ (∀ j, ContinuousOn (c j) (K ×ˢ K)) ∧
      ∀ x ∈ K ×ˢ K, omh (io A x, 1) φ = ∑ j, c j x • b j := by
  classical
  set V := Submodule.span ℂ {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ} with hV
  have hmem : ∀ x ∈ K ×ˢ K, omh (io A x, 1) φ ∈ V := fun x hx =>
    Submodule.subset_span ⟨x.1, hx.1, x.2, hx.2, rfl⟩
  have hth : ∀ f ∈ V, IsThetaFunO ψ (dblSp A) W f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨g₁, -, g₂, -, rfl⟩ := hf; exact hW.om_pres _ _ hφ
    | zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ _ _
    | add f g _ _ hf hg => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf hg
    | smul c f _ hf => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun j => (b j : WO (dblSp A) W → ℂ),
    fun j x => if h : omh (io A x, 1) φ ∈ V then b.coord j ⟨_, h⟩ else 0, fun j => hth _ (b j).2,
    fun j => ?_, fun x hx => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hQ : Continuous fun y : K ×ˢ K => (⟨omh (io A y.1, 1) φ, hmem y.1 y.2⟩ : V) := by
      refine Continuous.subtype_mk (continuous_pi fun w => ?_) _
      exact ((hW.om_cont φ hφ w).comp ((continuous_io A).prodMk continuous_const)).comp continuous_subtype_val
    have hcoord : Continuous (b.coord j) := LinearMap.continuous_of_finiteDimensional _
    refine (hcoord.comp hQ).congr fun y => ?_
    simp only [Set.restrict_apply, Function.comp_apply, dif_pos (hmem y.1 y.2)]
  · have e := congrArg Subtype.val (b.sum_repr ⟨_, hmem x hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    conv_lhs => rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dif_pos (hmem x hx), Module.Basis.coord_apply]

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨N₁, hc₁, hN₁⟩` from `exists_compact_mem_nhds x.1`. Take `⟨N₂, hc₂, hN₂⟩` from `exists_compact_mem_nhds x.2`. Conclude with `(h _ (hc₁.union hc₂)).continuousAt (prod_mem_nhds (Filter.mem_of_superset hN₁ Set.subset_union_left) (Filter.mem_of_superset hN₂ Set.subset_union_right))`.
-/
theorem continuous_of_compact_sq {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (G : X × X → Y) (h : ∀ K : Set X, IsCompact K → ContinuousOn G (K ×ˢ K)) : Continuous G := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨N₁, hc₁, hN₁⟩ := exists_compact_mem_nhds x.1
  obtain ⟨N₂, hc₂, hN₂⟩ := exists_compact_mem_nhds x.2
  exact (h _ (hc₁.union hc₂)).continuousAt
    (prod_mem_nhds (Filter.mem_of_superset hN₁ Set.subset_union_left)
      (Filter.mem_of_superset hN₂ Set.subset_union_right))

end GlobalTheory.Core.Rk.Collect

namespace GlobalTheory.Core.Rk.Collect

/- English proof (translation)
Introduce `D ψ θ A cA a hDef W χ omh hW φ hφ hK m hm u hu huinv`. Use `haveI := hm`. Take `⟨-, X, K, hXm, hX, hKc, hXK⟩` from `GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hDef.sig hDef.pos m hm`. Establish `hloc` using `fun (K' : Set (GA D A)) (hK' : IsCompact K') => local_rep hW hφ (GlobalTheory.T.K_finite_translates_finite_dimensional D ψ θ A cA a hDef W χ omh hW φ hK K' hK')`. Take `⟨n, b, c, hb, hc, hrep⟩` from `hloc K hKc`.

Establish `hχ : IsHeckeChar D χ⁻¹`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Establish `e : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹` using `rfl`. Rewrite using `[e]`. Conclude with `hW.hecT.1.inv`.

Rewrite using `[MonoidHom.inv_apply, hW.hecT.2 x, inv_one]`. Use `set w : GA D A × GA D A → ℂ := fun x => conj (conj (u x.1)) * conj (u x.2) * (((χ⁻¹ (detA A x.2) : Circle) : ℂ))⁻¹ with hw`. Establish `hdet : Continuous fun g : GA D A => ((χ⁻¹ (detA A g) : Circle) : ℂ)` using `continuous_subtype_val.comp (hχ.1.comp GlobalTheory.Eis.continuous_detA)`. Establish `hwc : Continuous w` using `((Complex.continuous_conj.comp (Complex.continuous_conj.comp (hu.comp continuous_fst))).mul (Complex.continuous_conj.comp (hu.comp continuous_snd))).mul ((hdet.comp continuous_snd).inv₀ fun _ => Circle.coe_ne_zero _)`. Use `⟨∑ j, (∫ x in X ×ˢ X, c j x * w x ∂m.prod m) • b j, theta_sum _ _ _ hb, fun Λ hadd hsmul hΛ => ?_⟩` and prove the remaining obligations.

Establish `hG : ∀ x ∈ K ×ˢ K, Λ (omh (io A x, 1) φ) = ∑ j, c j x * Λ (b j)` using `fun x hx => by`. Rewrite using `[hrep x hx]`. Conclude with `lin_sum Λ φ hφ hadd hsmul _ _ _ hb`. Establish `hGc : Continuous fun x : GA D A × GA D A => Λ (omh (io A x, 1) φ)`. Use `continuous_of_compact_sq _ fun K' hK' => ?_` and prove the remaining obligations.

Take `⟨n', b', c', hb', hc', hrep'⟩` from `hloc K' hK'`. Establish `hs : ContinuousOn (fun x => ∑ j, c' j x * Λ (b' j)) (K' ×ˢ K')` using `continuousOn_finset_sum _ fun j _ => (hc' j).mul continuousOn_const`. Use `hs.congr fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hrep' x hx]`. Conclude with `lin_sum Λ φ hφ hadd hsmul _ _ _ hb'`.

Establish `hEq : GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)) = fun x => Λ (omh (io A x, 1) φ) * w x`. Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.Eis.dblIntegrand, hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcont : Continuous (GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)))` using `hEq ▸ hGc.mul hwc`.

Establish `hli` using `GlobalTheory.Eis.leftInv_dblIntegrand (V := A) (f₁ := fun g => conj (u g)) (f₂ := fun g => conj (u g)) hχ (E := fun g => Λ (omh (g, 1) φ)) (fun γ hγ g => hΛ γ hγ g) (fun γ hγ g => congrArg (starRingEnd ℂ) (huinv γ hγ g)) (fun γ hγ g => congrArg (starRingEnd ℂ) (huinv γ hγ g))`. Establish `hcomp : IsCompact (K ×ˢ K)` using `hKc.prod hKc`. Establish `hsub : X ×ˢ X ⊆ K ×ˢ K` using `Set.prod_mono hXK hXK`. Establish `hint : IntegrableOn (GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g))) (X ×ˢ X) (m.prod m)` using `(hcont.continuousOn.integrableOn_compact hcomp).mono_set hsub`. Establish `hconv` using `(GlobalTheory.Eis.dblConv_iff hli hcont.measurable hX).2 hint`.

Rewrite using `[(hconv.dblInt_eq hX).2, hEq]`. Establish `hXXm : MeasurableSet (X ×ˢ X)` using `hXm.prod hXm`. Rewrite using `[setIntegral_congr_fun hXXm (g := fun x => ∑ j, (c j x * w x) * Λ (b j)) fun x hx => ?_]`. Rewrite using `[integral_finset_sum _ fun j _ => ?_]`. Rewrite using `[lin_sum Λ φ hφ hadd hsmul _ _ _ hb]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_mul_const]`. Conclude with `((((hc j).mul hwc.continuousOn).mul continuousOn_const).integrableOn_compact hcomp).mono_set hsub`. Simplify using `only`. Rewrite using `[hG x (hsub hx), Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem dblInt_collect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → ∃ φ', IsThetaFunO ψ (dblSp A) W φ' ∧ ∀ Λ : (WO (dblSp A) W → ℂ) → ℂ, (∀ f f', IsThetaFunO ψ (dblSp A) W f → IsThetaFunO ψ (dblSp A) W f' → Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ) f, IsThetaFunO ψ (dblSp A) W f → Λ (c • f) = c * Λ f) → (∀ γ ∈ GQ (dblSp A), ∀ g, Λ (omh (γ * g, 1) φ) = Λ (omh (g, 1) φ)) → GlobalTheory.Eis.dblInt A χ⁻¹ m (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)) = Λ φ' := by
  intro D ψ θ A cA a hDef W χ omh hW φ hφ hK m hm u hu huinv
  haveI := hm
  obtain ⟨-, X, K, hXm, hX, hKc, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hDef.sig hDef.pos m hm
  have hloc := fun (K' : Set (GA D A)) (hK' : IsCompact K') =>
    local_rep hW hφ (GlobalTheory.T.K_finite_translates_finite_dimensional D ψ θ A cA a hDef W χ omh hW φ hK K' hK')
  obtain ⟨n, b, c, hb, hc, hrep⟩ := hloc K hKc
  have hχ : IsHeckeChar D χ⁻¹ := by
    refine ⟨?_, fun x => ?_⟩
    · have e : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
      rw [e]; exact hW.hecT.1.inv
    · rw [MonoidHom.inv_apply, hW.hecT.2 x, inv_one]
  set w : GA D A × GA D A → ℂ :=
    fun x => conj (conj (u x.1)) * conj (u x.2) * (((χ⁻¹ (detA A x.2) : Circle) : ℂ))⁻¹ with hw
  have hdet : Continuous fun g : GA D A => ((χ⁻¹ (detA A g) : Circle) : ℂ) :=
    continuous_subtype_val.comp (hχ.1.comp GlobalTheory.Eis.continuous_detA)
  have hwc : Continuous w :=
    ((Complex.continuous_conj.comp (Complex.continuous_conj.comp (hu.comp continuous_fst))).mul
      (Complex.continuous_conj.comp (hu.comp continuous_snd))).mul
      ((hdet.comp continuous_snd).inv₀ fun _ => Circle.coe_ne_zero _)
  refine ⟨∑ j, (∫ x in X ×ˢ X, c j x * w x ∂m.prod m) • b j, theta_sum _ _ _ hb, fun Λ hadd hsmul hΛ => ?_⟩
  have hG : ∀ x ∈ K ×ˢ K, Λ (omh (io A x, 1) φ) = ∑ j, c j x * Λ (b j) := fun x hx => by
    rw [hrep x hx]; exact lin_sum Λ φ hφ hadd hsmul _ _ _ hb
  have hGc : Continuous fun x : GA D A × GA D A => Λ (omh (io A x, 1) φ) := by
    refine continuous_of_compact_sq _ fun K' hK' => ?_
    obtain ⟨n', b', c', hb', hc', hrep'⟩ := hloc K' hK'
    have hs : ContinuousOn (fun x => ∑ j, c' j x * Λ (b' j)) (K' ×ˢ K') :=
      continuousOn_finset_sum _ fun j _ => (hc' j).mul continuousOn_const
    refine hs.congr fun x hx => ?_
    rw [hrep' x hx]; exact lin_sum Λ φ hφ hadd hsmul _ _ _ hb'
  have hEq : GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)) =
      fun x => Λ (omh (io A x, 1) φ) * w x := by
    funext x; simp only [GlobalTheory.Eis.dblIntegrand, hw]; ring
  have hcont : Continuous (GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g))
      (fun g => conj (u g))) := hEq ▸ hGc.mul hwc
  have hli := GlobalTheory.Eis.leftInv_dblIntegrand (V := A) (f₁ := fun g => conj (u g)) (f₂ := fun g => conj (u g)) hχ
    (E := fun g => Λ (omh (g, 1) φ)) (fun γ hγ g => hΛ γ hγ g)
    (fun γ hγ g => congrArg (starRingEnd ℂ) (huinv γ hγ g)) (fun γ hγ g => congrArg (starRingEnd ℂ) (huinv γ hγ g))
  have hcomp : IsCompact (K ×ˢ K) := hKc.prod hKc
  have hsub : X ×ˢ X ⊆ K ×ˢ K := Set.prod_mono hXK hXK
  have hint : IntegrableOn (GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g))
      (fun g => conj (u g))) (X ×ˢ X) (m.prod m) := (hcont.continuousOn.integrableOn_compact hcomp).mono_set hsub
  have hconv := (GlobalTheory.Eis.dblConv_iff hli hcont.measurable hX).2 hint
  rw [(hconv.dblInt_eq hX).2, hEq]
  have hXXm : MeasurableSet (X ×ˢ X) := hXm.prod hXm
  rw [setIntegral_congr_fun hXXm (g := fun x => ∑ j, (c j x * w x) * Λ (b j)) fun x hx => ?_]
  · rw [integral_finset_sum _ fun j _ => ?_]
    · rw [lin_sum Λ φ hφ hadd hsmul _ _ _ hb]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
    · exact ((((hc j).mul hwc.continuousOn).mul continuousOn_const).integrableOn_compact hcomp).mono_set hsub
  · simp only
    rw [hG x (hsub hx), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Core.Rk.Collect
