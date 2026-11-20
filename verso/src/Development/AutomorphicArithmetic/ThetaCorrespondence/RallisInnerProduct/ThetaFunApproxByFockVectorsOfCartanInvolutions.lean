import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RallisInnerProduct.ExistsCommonLevelSobolevBoundWeilCompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsONBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis
open GlobalTheory

/- English proof (translation)
Introduce `X R hR X₀ hX₀ a b a' b' hab ha hb`. Use `set R0 : Submodule ℂ ((X → ℂ) × (X → ℂ)) := R ⊓ (X₀.prod ⊤) with hR0`. Establish `hmem : ∀ p : R0, p.1.1 ∈ X₀` using `fun p => (Submodule.mem_prod.mp (Submodule.mem_inf.mp p.2).2).1`. Set `f : R0 →ₗ[ℂ] X₀` to `LinearMap.codRestrict X₀ ((LinearMap.fst ℂ _ _).comp R0.subtype) hmem`. Establish `hinj : Function.Injective f`.

Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `p hp`. Rewrite `hp` using `[LinearMap.mem_ker]`. Establish `h1 : p.1.1 = 0`. Conclude with `congrArg Subtype.val hp`.

Establish `hpR : p.1 ∈ R` using `(Submodule.mem_inf.mp p.2).1`. Establish `h2 : p.1.2 = 0`. Apply `hR` to reduce the goal to its premises. Establish `: ((p.1.1, p.1.2) : (X → ℂ) × (X → ℂ)) = p.1` using `rfl`. Rewrite using `[← h1]`.

Simplify using `using hpR`. Use `ext1`. Conclude with `Prod.ext h1 h2`. Use `haveI : FiniteDimensional ℂ R0 := Module.Finite.of_injective f hinj`. Establish `hclosed : IsClosed (R0 : Set ((X → ℂ) × (X → ℂ)))` using `Submodule.closed_of_finiteDimensional R0`.

Establish `ht : Filter.Tendsto (fun j => (a j, b j)) Filter.atTop (nhds (a', b'))` using `(tendsto_pi_nhds.mpr ha).prodMk_nhds (tendsto_pi_nhds.mpr hb)`. Establish `hin : ∀ j, (a j, b j) ∈ R0` using `fun j => Submodule.mem_inf.mpr ⟨(hab j).2, Submodule.mem_prod.mpr ⟨(hab j).1, Submodule.mem_top⟩⟩`. Use `hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall hin)` as an intermediate fact. Conclude with `(Submodule.mem_inf.mp this).1`.
-/
theorem graph_finDim_mem_of_pointwise_tendsto : ∀ (X : Type) (R : Submodule ℂ ((X → ℂ) × (X → ℂ))), (∀ E, (0, E) ∈ R → E = 0) → ∀ X₀ : Submodule ℂ (X → ℂ), FiniteDimensional ℂ X₀ → ∀ (a b : ℕ → X → ℂ) (a' b' : X → ℂ), (∀ j, a j ∈ X₀ ∧ (a j, b j) ∈ R) → (∀ x, Filter.Tendsto (fun j => a j x) Filter.atTop (nhds (a' x))) → (∀ x, Filter.Tendsto (fun j => b j x) Filter.atTop (nhds (b' x))) → (a', b') ∈ R := by
  intro X R hR X₀ hX₀ a b a' b' hab ha hb
  set R0 : Submodule ℂ ((X → ℂ) × (X → ℂ)) := R ⊓ (X₀.prod ⊤) with hR0
  have hmem : ∀ p : R0, p.1.1 ∈ X₀ := fun p => (Submodule.mem_prod.mp (Submodule.mem_inf.mp p.2).2).1
  let f : R0 →ₗ[ℂ] X₀ := LinearMap.codRestrict X₀ ((LinearMap.fst ℂ _ _).comp R0.subtype) hmem
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    rw [LinearMap.mem_ker] at hp
    have h1 : p.1.1 = 0 := by
      exact congrArg Subtype.val hp
    have hpR : p.1 ∈ R := (Submodule.mem_inf.mp p.2).1
    have h2 : p.1.2 = 0 := by
      apply hR
      have : ((p.1.1, p.1.2) : (X → ℂ) × (X → ℂ)) = p.1 := rfl
      rw [← h1]; simpa using hpR
    ext1
    exact Prod.ext h1 h2
  haveI : FiniteDimensional ℂ R0 := Module.Finite.of_injective f hinj
  have hclosed : IsClosed (R0 : Set ((X → ℂ) × (X → ℂ))) := Submodule.closed_of_finiteDimensional R0
  have ht : Filter.Tendsto (fun j => (a j, b j)) Filter.atTop (nhds (a', b')) :=
    (tendsto_pi_nhds.mpr ha).prodMk_nhds (tendsto_pi_nhds.mpr hb)
  have hin : ∀ j, (a j, b j) ∈ R0 := fun j =>
    Submodule.mem_inf.mpr ⟨(hab j).2, Submodule.mem_prod.mpr ⟨(hab j).1, Submodule.mem_top⟩⟩
  have := hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall hin)
  exact (Submodule.mem_inf.mp this).1

end UpperTheory.Lit.Rallis
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto | exact UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto | (intros; apply UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.pointwise_limit_mem_graphRelation_of_finiteDimensional : ∀ (X : Type) (R : Submodule ℂ ((X → ℂ) × (X → ℂ))), (∀ E, (0, E) ∈ R → E = 0) → ∀ X₀ : Submodule ℂ (X → ℂ), FiniteDimensional ℂ X₀ → ∀ (a b : ℕ → X → ℂ) (a' b' : X → ℂ), (∀ j, a j ∈ X₀ ∧ (a j, b j) ∈ R) → (∀ x, Filter.Tendsto (fun j => a j x) Filter.atTop (nhds (a' x))) → (∀ x, Filter.Tendsto (fun j => b j x) Filter.atTop (nhds (b' x))) → (a', b') ∈ R := by
  first | exact @UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto | exact UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto | (intros; apply UpperTheory.Lit.Rallis.graph_finDim_mem_of_pointwise_tendsto <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.FinVecKernel
open GlobalTheory

open Module

/- English proof (translation)
Introduce `K _ _ _ _ _ _ ν _ Y ρ f hW hcont`. Use `set W := Submodule.span ℂ (Set.range fun k => ρ k f) with hWdef`. Use `haveI : FiniteDimensional ℂ W := hW`. Establish `hmem : ∀ k, ρ k f ∈ W` using `fun k => Submodule.subset_span ⟨k, rfl⟩`. Set `o : K → W` to `fun k => ⟨ρ k f, hmem k⟩`.

Establish `ho : Continuous o` using `(continuous_pi hcont).subtype_mk _`. Establish `hlc : ∀ l : Dual ℂ W, Continuous fun k => l (o k)` using `fun l => (LinearMap.continuous_of_finiteDimensional l).comp ho`. Establish `hint : ∀ l m : Dual ℂ W, Integrable (fun k => conj (l (o k)) * m (o k)) ν` using `fun l m => ((Complex.continuous_conj.comp (hlc l)).mul (hlc m)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Set `Ψ : Dual ℂ W → Dual ℂ (Dual ℂ W)` to `fun l => { toFun := fun m => ∫ k, conj (l (o k)) * m (o k) ∂ν map_add' := fun m m' => by`. Simplify using `only [LinearMap.add_apply, mul_add]`.

Conclude with `integral_add (hint l m) (hint l m')`. Use the proof step `map_smul' := fun c m => by`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Use `ring }`. Establish `hΨ : ∀ l m, Ψ l m = ∫ k, conj (l (o k)) * m (o k) ∂ν` using `fun _ _ => rfl`. Set `P : Submodule ℂ (Dual ℂ (Dual ℂ W))` to `{ carrier := {φ | ∃ l, φ = Ψ l} add_mem' := by`. Introduce and unpack `_ _ ⟨l, rfl⟩ ⟨l', rfl⟩`.

Use `⟨l + l', ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Simplify using `only [LinearMap.add_apply, hΨ, map_add, add_mul]`. Conclude with `(integral_add (hint l m) (hint l' m)).symm`. Use the proof step `zero_mem' := ⟨0, by ext m; simp [hΨ]⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨l, rfl⟩`. Use `⟨(starRingEnd ℂ c) • l, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, hΨ, map_mul, Complex.conj_conj]`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Use `ring }`. Establish `hev : Module.Dual.eval ℂ W (o 1) ∈ P`.

Assume the negation of the conclusion as `hne`. Take `⟨Λ, hΛ, hmap⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance`. Use `set m₀ := (Module.evalEquiv ℂ (Dual ℂ W)).symm Λ`. Establish `hΛm : ∀ φ, Λ φ = φ m₀` using `fun φ => (Module.apply_evalEquiv_symm_apply (R := ℂ) (M := Dual ℂ W) φ Λ).symm`. Establish `h0 : Λ (Ψ m₀) = 0`.

Establish `h1 : Λ (Ψ m₀) ∈ P.map Λ` using `Submodule.mem_map_of_mem ⟨m₀, rfl⟩`. Conclude with `(Submodule.mem_bot ℂ).1 (hmap ▸ h1)`. Rewrite `h0` using `[hΛm, hΨ]`. Establish `hg` using `hlc m₀`. Establish `hre : ∫ k, Complex.normSq (m₀ (o k)) ∂ν = 0`.

Establish `: ((∫ k, Complex.normSq (m₀ (o k)) ∂ν : ℝ) : ℂ) = 0`. Rewrite using `[← integral_complex_ofReal]`. Rewrite using `[← h0]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `this` after adjusting the coercions. Establish `hcn : Continuous fun k => Complex.normSq (m₀ (o k))` using `Complex.continuous_normSq.comp hg`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _) (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hre`. Establish `hz` using `(hcn.ae_eq_iff_eq ν continuous_const).1 hae`.

Establish `h1 : Complex.normSq (m₀ (o 1)) = 0` using `congrFun hz 1`. Rewrite `h1` using `[Complex.normSq_eq_zero]`. Apply `hΛ` to reduce the goal to its premises. Rewrite using `[hΛm]`. Simplify using `using h1`.

Take `⟨l, hl⟩` from `hev`. Establish `hl' : ∀ m : Dual ℂ W, m (o 1) = ∫ k, conj (l (o k)) * m (o k) ∂ν` using `fun m => by`. Rewrite using `[← hΨ, ← hl]`. Both sides reduce to the same expression. Establish `hinv : ∀ a : K, ∀ x ∈ W, ρ a x ∈ W` using `fun a => by`.

Establish `: W ≤ W.comap (ρ a)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `hmem (a * k)` as an intermediate fact. Rewrite using `[map_mul, Module.End.mul_apply] at this)` and apply the resulting hypothesis. Conclude with `fun x hx => this hx`.

Set `R : K → W →ₗ[ℂ] W` to `fun a => (ρ a).restrict (hinv a)`. Establish `hR : ∀ k₀ k, o (k₀⁻¹ * k) = R k₀⁻¹ (o k)` using `fun k₀ k => by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[o, R, LinearMap.restrict_apply, map_mul, Module.End.mul_apply]`. Set `B` to `Module.finBasis ℂ W`.

Establish `hexp : ∀ a (w : W), l (R a w) = ∑ i, B.repr w i * l (R a (B i))` using `fun a w => by`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun k => conj (l (o k)), Module.finrank ℂ W, fun i k₀ => conj (l (R k₀⁻¹ (B i))), fun i k => conj (B.repr (o k) i), Complex.continuous_conj.comp (hlc l), fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Complex.continuous_conj.comp (hlc (B.coord i))` as an intermediate fact. Simplify `this` using `[Basis.coord_apply, Function.comp_def]`.

Introduce `k₀ k`. Simplify using `only`. Rewrite using `[hR, hexp, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_comm]`.

Introduce `y`. Use `hl' ((LinearMap.proj y).comp W.subtype)` as an intermediate fact. Simplify `this` using `[o, map_one]`.
-/
theorem exists_reproducing_kernel : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] (Y : Type) (ρ : K →* Module.End ℂ (Y → ℂ)) (f : Y → ℂ), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k f)) → (∀ y, Continuous fun k => ρ k f y) → ∃ (e : K → ℂ) (n : ℕ) (a b : Fin n → K → ℂ), Continuous e ∧ (∀ i, Continuous (b i)) ∧ (∀ k₀ k, e (k₀⁻¹ * k) = ∑ i, a i k₀ * b i k) ∧ ∀ y, f y = ∫ k, e k * ρ k f y ∂ν := by
  intro K _ _ _ _ _ _ ν _ Y ρ f hW hcont
  set W := Submodule.span ℂ (Set.range fun k => ρ k f) with hWdef
  haveI : FiniteDimensional ℂ W := hW
  have hmem : ∀ k, ρ k f ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  let o : K → W := fun k => ⟨ρ k f, hmem k⟩
  have ho : Continuous o := (continuous_pi hcont).subtype_mk _
  have hlc : ∀ l : Dual ℂ W, Continuous fun k => l (o k) := fun l =>
    (LinearMap.continuous_of_finiteDimensional l).comp ho
  have hint : ∀ l m : Dual ℂ W, Integrable (fun k => conj (l (o k)) * m (o k)) ν := fun l m =>
    ((Complex.continuous_conj.comp (hlc l)).mul (hlc m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let Ψ : Dual ℂ W → Dual ℂ (Dual ℂ W) := fun l =>
    { toFun := fun m => ∫ k, conj (l (o k)) * m (o k) ∂ν
      map_add' := fun m m' => by
        simp only [LinearMap.add_apply, mul_add]
        exact integral_add (hint l m) (hint l m')
      map_smul' := fun c m => by
        simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]; congr 1; funext k; ring }
  have hΨ : ∀ l m, Ψ l m = ∫ k, conj (l (o k)) * m (o k) ∂ν := fun _ _ => rfl
  let P : Submodule ℂ (Dual ℂ (Dual ℂ W)) :=
    { carrier := {φ | ∃ l, φ = Ψ l}
      add_mem' := by
        rintro _ _ ⟨l, rfl⟩ ⟨l', rfl⟩
        refine ⟨l + l', ?_⟩
        ext m
        simp only [LinearMap.add_apply, hΨ, map_add, add_mul]
        exact (integral_add (hint l m) (hint l' m)).symm
      zero_mem' := ⟨0, by ext m; simp [hΨ]⟩
      smul_mem' := by
        rintro c _ ⟨l, rfl⟩
        refine ⟨(starRingEnd ℂ c) • l, ?_⟩
        ext m
        simp only [LinearMap.smul_apply, smul_eq_mul, hΨ, map_mul, Complex.conj_conj]
        rw [← integral_const_mul]; congr 1; funext k; ring }
  have hev : Module.Dual.eval ℂ W (o 1) ∈ P := by
    by_contra hne
    obtain ⟨Λ, hΛ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
    set m₀ := (Module.evalEquiv ℂ (Dual ℂ W)).symm Λ
    have hΛm : ∀ φ, Λ φ = φ m₀ := fun φ =>
      (Module.apply_evalEquiv_symm_apply (R := ℂ) (M := Dual ℂ W) φ Λ).symm
    have h0 : Λ (Ψ m₀) = 0 := by
      have h1 : Λ (Ψ m₀) ∈ P.map Λ := Submodule.mem_map_of_mem ⟨m₀, rfl⟩
      exact (Submodule.mem_bot ℂ).1 (hmap ▸ h1)
    rw [hΛm, hΨ] at h0
    have hg := hlc m₀
    have hre : ∫ k, Complex.normSq (m₀ (o k)) ∂ν = 0 := by
      have : ((∫ k, Complex.normSq (m₀ (o k)) ∂ν : ℝ) : ℂ) = 0 := by
        rw [← integral_complex_ofReal]; rw [← h0]; congr 1; funext k
        rw [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast this
    have hcn : Continuous fun k => Complex.normSq (m₀ (o k)) := Complex.continuous_normSq.comp hg
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hre
    have hz := (hcn.ae_eq_iff_eq ν continuous_const).1 hae
    have h1 : Complex.normSq (m₀ (o 1)) = 0 := congrFun hz 1
    rw [Complex.normSq_eq_zero] at h1
    apply hΛ; rw [hΛm]; simpa using h1
  obtain ⟨l, hl⟩ := hev
  have hl' : ∀ m : Dual ℂ W, m (o 1) = ∫ k, conj (l (o k)) * m (o k) ∂ν := fun m => by
    rw [← hΨ, ← hl]; rfl
  have hinv : ∀ a : K, ∀ x ∈ W, ρ a x ∈ W := fun a => by
    have : W ≤ W.comap (ρ a) := Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      have := hmem (a * k)
      rwa [map_mul, Module.End.mul_apply] at this)
    exact fun x hx => this hx
  let R : K → W →ₗ[ℂ] W := fun a => (ρ a).restrict (hinv a)
  have hR : ∀ k₀ k, o (k₀⁻¹ * k) = R k₀⁻¹ (o k) := fun k₀ k => by
    apply Subtype.ext
    simp [o, R, LinearMap.restrict_apply, map_mul, Module.End.mul_apply]
  let B := Module.finBasis ℂ W
  have hexp : ∀ a (w : W), l (R a w) = ∑ i, B.repr w i * l (R a (B i)) := fun a w => by
    calc l (R a w) = l (R a (∑ i, B.repr w i • B i)) := by rw [B.sum_repr]
      _ = _ := by rw [map_sum, map_sum]; simp only [map_smul, smul_eq_mul]
  refine ⟨fun k => conj (l (o k)), Module.finrank ℂ W, fun i k₀ => conj (l (R k₀⁻¹ (B i))),
    fun i k => conj (B.repr (o k) i), Complex.continuous_conj.comp (hlc l), fun i => ?_, ?_, ?_⟩
  · have := Complex.continuous_conj.comp (hlc (B.coord i))
    simpa [Basis.coord_apply, Function.comp_def] using this
  · intro k₀ k
    simp only
    rw [hR, hexp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]
  · intro y
    have := hl' ((LinearMap.proj y).comp W.subtype)
    simpa [o, map_one] using this

end UpperTheory.Lit.Rallis.FinVecKernel
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel | exact UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel | (intros; apply UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.exists_continuous_kernel_reproducing_finite_vector : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] (Y : Type) (ρ : K →* Module.End ℂ (Y → ℂ)) (f : Y → ℂ), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k f)) → (∀ y, Continuous fun k => ρ k f y) → ∃ (e : K → ℂ) (n : ℕ) (a b : Fin n → K → ℂ), Continuous e ∧ (∀ i, Continuous (b i)) ∧ (∀ k₀ k, e (k₀⁻¹ * k) = ∑ i, a i k₀ * b i k) ∧ ∀ y, f y = ∫ k, e k * ρ k f y ∂ν := by
  first | exact @UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel | exact UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel | (intros; apply UpperTheory.Lit.Rallis.FinVecKernel.exists_reproducing_kernel <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace UpperTheory.Lit.Rallis.FockDensCart
open GlobalTheory

/- English proof (translation)
Establish `key : ∀ τ, ∃ (ε : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit B.det ∧ Bᴴ * gramAt D V τ * B = Formalism.REAL.Jm ε ∧ s τ * B = B * Formalism.REAL.Jm ε`. Introduce `τ`. Take `⟨p, B, ε, h1, h2, h3⟩` from `GlobalTheory.FrameLawsTheta.exists_isONBasis (hs τ)`. Establish `hJ : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (fun a => decide (a.val < p))`. Unfold `Formalism.REAL.Jm`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Break down `h1 a with ⟨e, ha⟩ | ⟨e, ha⟩` into its components or cases. Simplify using `[e, ha]`. Simplify using `[e, show ¬ a.val < p by omega]`.

Rewrite `h2`, `h3` using `[hJ]`. Use `⟨_, B, ?_, h2, h3⟩` and prove the remaining obligations. Establish `hd` using `congrArg Matrix.det h2`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul]`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations.

Rewrite `hd` using `[h0, mul_zero]`. Establish `hJd : (Formalism.REAL.Jm (fun a : Fin V.rank => decide (a.val < p))).det ≠ 0`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.det_diagonal]`. Apply the tactic sequence `exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num`.

Conclude with `hJd hd.symm`. Use `choose ε B hu hg hc using key`. Use `⟨⟨ε, fun τ => (B τ)⁻¹, fun τ => ?_, fun τ => ?_⟩, funext fun τ => ?_⟩` and prove the remaining obligations. Conclude with `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hu τ))`. Use `show ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) * (B τ)⁻¹ = gramAt D V τ`.

Rewrite using `[← hg τ]`. Establish `h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ (hu τ), Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Use `show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (B τ)⁻¹ = s τ`.

Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]`.
-/
theorem exists_fr_of_cartanInv {D : D7} (V : HSp D) (s : RealMat V) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    ∃ A : GlobalTheory.ChainFr.Fr V, A.cart = s := by
  have key : ∀ τ, ∃ (ε : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit B.det ∧
      Bᴴ * gramAt D V τ * B = Formalism.REAL.Jm ε ∧ s τ * B = B * Formalism.REAL.Jm ε := by
    intro τ
    obtain ⟨p, B, ε, h1, h2, h3⟩ := GlobalTheory.FrameLawsTheta.exists_isONBasis (hs τ)
    have hJ : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (fun a => decide (a.val < p)) := by
      unfold Formalism.REAL.Jm
      congr 1
      funext a
      rcases h1 a with ⟨e, ha⟩ | ⟨e, ha⟩
      · simp [e, ha]
      · simp [e, show ¬ a.val < p by omega]
    rw [hJ] at h2 h3
    refine ⟨_, B, ?_, h2, h3⟩
    have hd := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_mul] at hd
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hd
    have hJd : (Formalism.REAL.Jm (fun a : Fin V.rank => decide (a.val < p))).det ≠ 0 := by
      unfold Formalism.REAL.Jm
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
    exact hJd hd.symm
  choose ε B hu hg hc using key
  refine ⟨⟨ε, fun τ => (B τ)⁻¹, fun τ => ?_, fun τ => ?_⟩, funext fun τ => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hu τ))
  · show ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) * (B τ)⁻¹ = gramAt D V τ
    rw [← hg τ]
    have h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ (hu τ), Matrix.conjTranspose_one]
    calc _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul, Matrix.mul_one]
  · show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (B τ)⁻¹ = s τ
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]

section Fock

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.ChainFr

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

/- English proof (translation)
Establish `hS : ∀ τ, IsCartanInv (gramAt D S τ) (A.cart τ)` using `GlobalTheory.ChainFr.Model.isCartanInv_cart A`. Establish `hT : ∀ τ, IsCartanInv (gramAt D T τ) (B.cart τ)` using `GlobalTheory.ChainFr.Model.isCartanInv_cart B`. Use `set Ap := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAdef`. Establish `hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g')` using `fun _ _ => theta_add`. Establish `hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g)` using `fun a _ => theta_smul a`.

Establish `hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ap k g)` using `fun _ _ h => aPlus_theta hψ hθ _ _ _ h`. Establish `hc : ∀ i j g, IsThetaFunO ψ S T g → Ap i (Ap j g) = Ap j (Ap i g)` using `fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h`. Establish `Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → Ap i (g + g') = Ap i g + Ap i g'` using `fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'`. Establish `Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → Ap i (a • g) = a • Ap i g` using `fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h`. Establish `hpt : ∀ Q, ptF ψ θ A B f Q = pureTensorL Ap f Q` using `fun _ => rfl`.

Establish `hm : ∀ Q, IsThetaFunO ψ S T (pureTensorL Ap f Q)` using `pure_mem hadd hsm hA hf.1`. Establish `hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ c : FVar D T.rank S.rank → ℂ, ∀ Q, annih (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ)) z (pureTensorL Ap f Q) = pureTensorL Ap f (∑ i, c i • MvPolynomial.pderiv i Q)`. Introduce `τ z`. Use `⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) * ((omDir S T τ z k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) : ℝ) + Complex.I * (omDir S T τ (cplxO (A.cart τ) (B.cart τ) z) k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h) (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.1 (hf.2 τ z) Q`.

Use `⟨by rw [hpt]; exact hm P, fun l hl => ?_⟩` and prove the remaining obligations. Establish `key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 g) (pureTensorL Ap f P) = pureTensorL Ap f Q ∧ ∀ m : FVar D T.rank S.rank →₀ ℕ, P. …`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`.

Use `⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩` and prove the remaining obligations. Establish `h' : P.totalDegree < m.degree` using `by simpa using hm'`. Conclude with `h'`. Consider the case `cons p l ih`. Take `⟨Q, hQ, hQc⟩` from `ih`.

Take `⟨c, hc'⟩` from `hder p.1 p.2`. Use `⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩` and prove the remaining obligations. Rewrite using `[List.foldr_cons, hQ, hc']`. Use `GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length) (fun m' hm'' => hQc m' (by omega)) m ?_` and prove the remaining obligations. Simplify using `only [List.length_cons] at hm'`.

Use linear arithmetic over natural numbers and integers. Take `⟨Q, hQ, hQc⟩` from `key l`. Establish `hQ0 : Q = 0` using `MvPolynomial.ext _ _ fun m => by`. Rewrite using `[hQc m (by omega), MvPolynomial.coeff_zero]`. Rewrite using `[hpt, hQ, hQ0, map_zero]`.
-/
theorem ptF_fock (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (ptF ψ θ A B f P) ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      P.totalDegree < l.length →
        l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 g) (ptF ψ θ A B f P) = 0 := by
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) (A.cart τ) := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT : ∀ τ, IsCartanInv (gramAt D T τ) (B.cart τ) := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  set Ap := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAdef
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) := fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ap k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → Ap i (Ap j g) = Ap j (Ap i g) :=
    fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → Ap i (g + g') = Ap i g + Ap i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → Ap i (a • g) = a • Ap i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hpt : ∀ Q, ptF ψ θ A B f Q = pureTensorL Ap f Q := fun _ => rfl
  have hm : ∀ Q, IsThetaFunO ψ S T (pureTensorL Ap f Q) := pure_mem hadd hsm hA hf.1
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ c : FVar D T.rank S.rank → ℂ, ∀ Q,
      annih (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ)) z (pureTensorL Ap f Q) =
        pureTensorL Ap f (∑ i, c i • MvPolynomial.pderiv i Q) := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir S T τ z k.1 (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir S T τ (cplxO (A.cart τ) (B.cart τ) z) k.1
          (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.1 (hf.2 τ z) Q
  refine ⟨by rw [hpt]; exact hm P, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ Q : MvPolynomial (FVar D T.rank S.rank) ℂ,
      l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 g) (pureTensorL Ap f P) =
        pureTensorL Ap f Q ∧ ∀ m : FVar D T.rank S.rank →₀ ℕ, P.totalDegree < m.degree + l.length → Q.coeff m = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h' : P.totalDegree < m.degree := by simpa using hm'
      exact h'
    | cons p l ih =>
      obtain ⟨Q, hQ, hQc⟩ := ih
      obtain ⟨c, hc'⟩ := hder p.1 p.2
      refine ⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩
      · rw [List.foldr_cons, hQ, hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length)
          (fun m' hm'' => hQc m' (by omega)) m ?_
        simp only [List.length_cons] at hm'
        omega
  obtain ⟨Q, hQ, hQc⟩ := key l
  have hQ0 : Q = 0 := MvPolynomial.ext _ _ fun m => by
    rw [hQc m (by omega), MvPolynomial.coeff_zero]
  rw [hpt, hQ, hQ0, map_zero]

end Fock

section Span

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.ChainFr

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨fun g h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩`. Consider the case `cons p l ih`. Take `⟨h1, h2, h3⟩` from `ih`. Use `⟨fun g h => annih_theta hψ hθ _ _ _ (h1 g h), fun g g' h h' => ?_, fun a g h => ?_⟩` and prove the remaining obligations.

Simplify using `only [List.foldr_cons]`. Rewrite using `[h2 g g' h h', annih_add hψ hθ _ _ _ (h1 g h) (h1 g' h')]`. Simplify using `only [List.foldr_cons]`. Rewrite using `[h3 a g h, annih_smul hψ hθ _ _ _ a (h1 g h)]`.
-/
theorem fold_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : RealMat S) (sT : RealMat T)
    (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) :
    (∀ g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g)) ∧
    (∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) (g + g') =
        l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g +
          l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g') ∧
    (∀ (a : ℂ) g, IsThetaFunO ψ S T g →
      l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) (a • g) =
        a • l.foldr (fun p g => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 g) g) := by
  induction l with
  | nil => exact ⟨fun g h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | cons p l ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨fun g h => annih_theta hψ hθ _ _ _ (h1 g h), fun g g' h h' => ?_, fun a g h => ?_⟩
    · simp only [List.foldr_cons]
      rw [h2 g g' h h', annih_add hψ hθ _ _ _ (h1 g h) (h1 g' h')]
    · simp only [List.foldr_cons]
      rw [h3 a g h, annih_smul hψ hθ _ _ _ a (h1 g h)]

/- English proof (translation)
Establish `L` using `fun l => fold_laws hψ hθ A.cart B.cart (θ := θ) l`. It suffices to establish `H : IsThetaFunO ψ S T g ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), N ≤ l.length → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 f) g = 0 by`. Take `⟨h1, N, h2⟩` from `H`. Conclude with `⟨h1, N, fun l hl => h2 l hl.ge⟩`. Proceed by induction on `hg using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨f₀, P, hv, -, rfl⟩` from `hx`. Take `⟨h1, h2⟩` from `ptF_fock hψ hθ A B hv P`. Conclude with `⟨h1, P.totalDegree + 1, fun l hl => h2 l (by omega)⟩`. Consider the case `zero`.

Use `⟨theta_zero, 0, fun l _ => ?_⟩` and prove the remaining obligations. Use `(L l).2.2 0 0 theta_zero` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis. Consider the case `add x y _ _ hx hy`. Take `⟨hx1, N, hx2⟩` from `hx`.

Take `⟨hy1, M, hy2⟩` from `hy`. Use `⟨theta_add hx1 hy1, max N M, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[(L l).2.1 x y hx1 hy1, hx2 l (le_of_max_le_left hl), hy2 l (le_of_max_le_right hl), add_zero]`. Consider the case `smul a x _ hx`. Take `⟨hx1, N, hx2⟩` from `hx`.

Use `⟨theta_smul a hx1, N, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[(L l).2.2 a x hx1, hx2 l hl, smul_zero]`.
-/
theorem isFockVec_of_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) (U : AddSubgroup (WO S T))
    {g : WO S T → ℂ} (hg : g ∈ fockSpan ψ θ A B U) : IsFockVec ψ θ S T A.cart B.cart g := by
  have L := fun l => fold_laws hψ hθ A.cart B.cart (θ := θ) l
  suffices H : IsThetaFunO ψ S T g ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      N ≤ l.length → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (A.cart p.1) (B.cart p.1)) p.2 f) g = 0 by
    obtain ⟨h1, N, h2⟩ := H
    exact ⟨h1, N, fun l hl => h2 l hl.ge⟩
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, P, hv, -, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := ptF_fock hψ hθ A B hv P
    exact ⟨h1, P.totalDegree + 1, fun l hl => h2 l (by omega)⟩
  | zero =>
    refine ⟨theta_zero, 0, fun l _ => ?_⟩
    have := (L l).2.2 0 0 theta_zero
    rwa [zero_smul, zero_smul] at this
  | add x y _ _ hx hy =>
    obtain ⟨hx1, N, hx2⟩ := hx
    obtain ⟨hy1, M, hy2⟩ := hy
    refine ⟨theta_add hx1 hy1, max N M, fun l hl => ?_⟩
    rw [(L l).2.1 x y hx1 hy1, hx2 l (le_of_max_le_left hl), hy2 l (le_of_max_le_right hl), add_zero]
  | smul a x _ hx =>
    obtain ⟨hx1, N, hx2⟩ := hx
    refine ⟨theta_smul a hx1, N, fun l hl => ?_⟩
    rw [(L l).2.2 a x hx1, hx2 l hl, smul_zero]

end Span

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hm sS sT hsS hsT f hf`. Take `⟨A, rfl⟩` from `exists_fr_of_cartanInv S sS hsS`. Take `⟨B, rfl⟩` from `exists_fr_of_cartanInv T sT hsT`. Take `⟨U, hU, hfU, hd⟩` from `GlobalTheory.FockDensity.fockDense D S T A B θ ψ hψ hθ μ 𝓕 hm f hf`. Use `⟨U, hU, hfU, fun d δ hδ => ?_⟩` and prove the remaining obligations.

Take `⟨g, hg, hgU, hlt⟩` from `hd d δ hδ`. Conclude with `⟨g, isFockVec_of_mem hψ hθ A B U hg, hgU, hlt⟩`.
-/
theorem fockDense_cart : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (sS : RealMat S) (sT : RealMat T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ f ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g, IsFockVec ψ θ S T sS sT g ∧ g ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm sS sT hsS hsT f hf
  obtain ⟨A, rfl⟩ := exists_fr_of_cartanInv S sS hsS
  obtain ⟨B, rfl⟩ := exists_fr_of_cartanInv T sT hsT
  obtain ⟨U, hU, hfU, hd⟩ := GlobalTheory.FockDensity.fockDense D S T A B θ ψ hψ hθ μ 𝓕 hm f hf
  refine ⟨U, hU, hfU, fun d δ hδ => ?_⟩
  obtain ⟨g, hg, hgU, hlt⟩ := hd d δ hδ
  exact ⟨g, isFockVec_of_mem hψ hθ A B U hg, hgU, hlt⟩

end UpperTheory.Lit.Rallis.FockDensCart
end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart | exact UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart | (intros; apply UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.thetaFun_approx_by_fockVectors_of_cartanInvolutions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (sS : RealMat S) (sT : RealMat T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ f ∈ thetaLevel ψ S T U ∧ ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g, IsFockVec ψ θ S T sS sT g ∧ g ∈ thetaLevel ψ S T U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  first | exact @UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart | exact UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart | (intros; apply UpperTheory.Lit.Rallis.FockDensCart.fockDense_cart <;> assumption)
end

section
open MeasureTheory

namespace UpperTheory.Lit.Rallis
open GlobalTheory

/- English proof (translation)
Set `V` to `Submodule.span ℂ (Set.range ρ)`. Set `b` to `Module.finBasis ℂ V`. Set `r : K → V` to `fun k => ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩`. Establish `hr : Continuous r` using `Continuous.subtype_mk (continuous_pi hρ) _`. Use `⟨_, b, fun i k => b.coord i (r k), fun i => ?_, fun k => ?_⟩` and prove the remaining obligations.

Conclude with `(LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hr`. Conclude with `(b.sum_repr (r k)).symm`.
-/
theorem exists_continuous_coords_of_finiteDimensional_span
    {K : Type} [TopologicalSpace K] {Y : Type} (ρ : K → Y → ℂ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ)))
    (hρ : ∀ y, Continuous fun k => ρ k y) :
    ∃ (n : ℕ) (b : Fin n → Submodule.span ℂ (Set.range ρ)) (c : Fin n → K → ℂ),
      (∀ i, Continuous (c i)) ∧
      ∀ k, (⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩ : Submodule.span ℂ (Set.range ρ))
        = ∑ i, c i k • b i := by
  let V := Submodule.span ℂ (Set.range ρ)
  let b := Module.finBasis ℂ V
  let r : K → V := fun k => ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩
  have hr : Continuous r := Continuous.subtype_mk (continuous_pi hρ) _
  refine ⟨_, b, fun i k => b.coord i (r k), fun i => ?_, fun k => ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hr
  · exact (b.sum_repr (r k)).symm

/- English proof (translation)
Introduce `K _ _ _ _ _ ν _ Y ρ e he hfd hρ`. Take `⟨n, b, c, hc, hrep⟩` from `exists_continuous_coords_of_finiteDimensional_span ρ hfd hρ`. Establish `hint : ∀ i, Integrable (fun k => e k * c i k) ν` using `fun i => by`. Establish `h : ContinuousOn (fun k => e k * c i k) Set.univ` using `(he.mul (hc i)).continuousOn`. Conclude with `integrableOn_univ.mp (h.integrableOn_compact' isCompact_univ MeasurableSet.univ)`.

Establish `key : ∀ (L : Submodule.span ℂ (Set.range ρ) →ₗ[ℂ] ℂ), ∫ k, e k * L ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩ ∂ν = L (∑ i, (∫ k, e k * c i k ∂ν) • b i)`. Introduce `L`. Establish `h1 : ∀ k, e k * L ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩ = ∑ i, (e k * c i k) * L (b i)`. Introduce `k`. Rewrite using `[hrep k, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_assoc]`. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_finset_sum _ (fun i _ => (hint i).mul_const _), map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_mul_const, map_smul, smul_eq_mul]`. Use `set w : Submodule.span ℂ (Set.range ρ) := ∑ i, (∫ k, e k * c i k ∂ν) • b i with hw`. Establish `hfun : (fun y => ∫ k, e k * ρ k y ∂ν) = (w : Y → ℂ)`. Use function extensionality and compare the values at `y`. Conclude with `key ((LinearMap.proj y).comp (Submodule.span ℂ (Set.range ρ)).subtype)`.

Use `⟨hfun ▸ w.2, fun Λ hadd hsmul => ?_⟩` and prove the remaining obligations. Set `L : Submodule.span ℂ (Set.range ρ) →ₗ[ℂ] ℂ` to `{ toFun := fun v => Λ v map_add' := fun u v => hadd _ u.2 _ v.2 map_smul' := fun a v => hsmul a _ v.2 }`. Rewrite using `[hfun]`. Conclude with `(key L).symm`.
-/
theorem weightedIntegral_mem_span_and_map_integral :
    ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν] (Y : Type) (ρ : K → Y → ℂ) (e : K → ℂ), Continuous e → FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ)) → (∀ y, Continuous fun k => ρ k y) → (fun y => ∫ k, e k * ρ k y ∂ν) ∈ Submodule.span ℂ (Set.range ρ) ∧ ∀ Λ : (Y → ℂ) → ℂ, (∀ f ∈ Submodule.span ℂ (Set.range ρ), ∀ f' ∈ Submodule.span ℂ (Set.range ρ), Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ), ∀ f ∈ Submodule.span ℂ (Set.range ρ), Λ (c • f) = c * Λ f) → Λ (fun y => ∫ k, e k * ρ k y ∂ν) = ∫ k, e k * Λ (ρ k) ∂ν := by
  intro K _ _ _ _ _ ν _ Y ρ e he hfd hρ
  obtain ⟨n, b, c, hc, hrep⟩ := exists_continuous_coords_of_finiteDimensional_span ρ hfd hρ
  have hint : ∀ i, Integrable (fun k => e k * c i k) ν := fun i => by
    have h : ContinuousOn (fun k => e k * c i k) Set.univ := (he.mul (hc i)).continuousOn
    exact integrableOn_univ.mp (h.integrableOn_compact' isCompact_univ MeasurableSet.univ)
  have key : ∀ (L : Submodule.span ℂ (Set.range ρ) →ₗ[ℂ] ℂ),
      ∫ k, e k * L ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩ ∂ν
        = L (∑ i, (∫ k, e k * c i k ∂ν) • b i) := by
    intro L
    have h1 : ∀ k, e k * L ⟨ρ k, Submodule.subset_span ⟨k, rfl⟩⟩
        = ∑ i, (e k * c i k) * L (b i) := by
      intro k
      rw [hrep k, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_assoc]
    simp_rw [h1]
    rw [integral_finset_sum _ (fun i _ => (hint i).mul_const _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, map_smul, smul_eq_mul]
  set w : Submodule.span ℂ (Set.range ρ) := ∑ i, (∫ k, e k * c i k ∂ν) • b i with hw
  have hfun : (fun y => ∫ k, e k * ρ k y ∂ν) = (w : Y → ℂ) := by
    funext y
    exact key ((LinearMap.proj y).comp (Submodule.span ℂ (Set.range ρ)).subtype)
  refine ⟨hfun ▸ w.2, fun Λ hadd hsmul => ?_⟩
  let L : Submodule.span ℂ (Set.range ρ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => Λ v
      map_add' := fun u v => hadd _ u.2 _ v.2
      map_smul' := fun a v => hsmul a _ v.2 }
  rw [hfun]
  exact (key L).symm

end UpperTheory.Lit.Rallis
end

section
open MeasureTheory

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral | exact UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral | (intros; apply UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.weighted_integral_mem_span_of_finiteDimensional_orbit : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν] (Y : Type) (ρ : K → Y → ℂ) (e : K → ℂ), Continuous e → FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ)) → (∀ y, Continuous fun k => ρ k y) → (fun y => ∫ k, e k * ρ k y ∂ν) ∈ Submodule.span ℂ (Set.range ρ) ∧ ∀ Λ : (Y → ℂ) → ℂ, (∀ f ∈ Submodule.span ℂ (Set.range ρ), ∀ f' ∈ Submodule.span ℂ (Set.range ρ), Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ), ∀ f ∈ Submodule.span ℂ (Set.range ρ), Λ (c • f) = c * Λ f) → Λ (fun y => ∫ k, e k * ρ k y ∂ν) = ∫ k, e k * Λ (ρ k) ∂ν := by
  first | exact @UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral | exact UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral | (intros; apply UpperTheory.Lit.Rallis.weightedIntegral_mem_span_and_map_integral <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section
namespace UpperTheory.Lit.Rallis.SWFinSpan
open GlobalTheory

/- English proof (translation)
Introduce `D ψ A B χ om hom ν 𝓨 hν a hI n α`. Establish `hI' : ∀ g : GA D (dblSp A), ∃ p : siegel A, ∃ k : Khat A a, g = (p : GA D (dblSp A)) * (k : GA D (dblSp A))`. Introduce `g`. Take `⟨p, k, hk, h⟩` from `hI g`. Conclude with `⟨p, ⟨k, hk⟩, h⟩`.

Use `choose p k hpk using hI'`. Set `c : GA D (dblSp A) → ℂ` to `fun g => (χ⁻¹ (aP A (p g)) : Circle) * npow (absA D (aP A (p g))) (sZero A B + (A.rank : ℂ) / 2)`. Set `F : Fin n → GA D (dblSp A) → ℂ` to `fun i g => c g * α i (k g)`. Use `⟨Submodule.span ℂ (Set.range F), FiniteDimensional.span_of_finite ℂ (Set.finite_range F), ?_⟩` and prove the remaining obligations. Introduce `φ hφ β hβ`.

Establish `h : swSec A B om ν 𝓨 φ = ∑ i, β i • F i`. Use function extensionality and compare the values at `g`. Establish `h1` using `GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ om hom ν 𝓨 hν φ hφ (p g) (k g)`. Rewrite `h1` using `[← hpk g, hβ (k g)]`. Rewrite using `[h1, Finset.sum_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [F, c, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem swSec_mem_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ a : GL (Fin A.rank) (AE D), HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ (n : ℕ) (α : Fin n → Khat A a → ℂ), ∃ X₀ : Submodule ℂ (GA D (dblSp A) → ℂ), FiniteDimensional ℂ X₀ ∧ ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ β : Fin n → ℂ, (∀ k : Khat A a, swSec A B om ν 𝓨 φ k = ∑ i, β i * α i k) → swSec A B om ν 𝓨 φ ∈ X₀ := by
  intro D ψ A B χ om hom ν 𝓨 hν a hI n α
  have hI' : ∀ g : GA D (dblSp A), ∃ p : siegel A, ∃ k : Khat A a, g = (p : GA D (dblSp A)) * (k : GA D (dblSp A)) := by
    intro g
    obtain ⟨p, k, hk, h⟩ := hI g
    exact ⟨p, ⟨k, hk⟩, h⟩
  choose p k hpk using hI'
  let c : GA D (dblSp A) → ℂ := fun g => (χ⁻¹ (aP A (p g)) : Circle) *
    npow (absA D (aP A (p g))) (sZero A B + (A.rank : ℂ) / 2)
  let F : Fin n → GA D (dblSp A) → ℂ := fun i g => c g * α i (k g)
  refine ⟨Submodule.span ℂ (Set.range F), FiniteDimensional.span_of_finite ℂ (Set.finite_range F), ?_⟩
  intro φ hφ β hβ
  have h : swSec A B om ν 𝓨 φ = ∑ i, β i • F i := by
    funext g
    have h1 := GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ om hom ν 𝓨 hν φ hφ (p g) (k g)
    rw [← hpk g, hβ (k g)] at h1
    rw [h1, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F, c, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end UpperTheory.Lit.Rallis.SWFinSpan

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional | exact UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional | (intros; apply UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.exists_finiteDimensional_space_of_siegelWeilSections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ a : GL (Fin A.rank) (AE D), HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ (n : ℕ) (α : Fin n → Khat A a → ℂ), ∃ X₀ : Submodule ℂ (GA D (dblSp A) → ℂ), FiniteDimensional ℂ X₀ ∧ ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ β : Fin n → ℂ, (∀ k : Khat A a, swSec A B om ν 𝓨 φ k = ∑ i, β i * α i k) → swSec A B om ν 𝓨 φ ∈ X₀ := by
  first | exact @UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional | exact UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional | (intros; apply UpperTheory.Lit.Rallis.SWFinSpan.swSec_mem_finiteDimensional <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.ThetaDens
open GlobalTheory

/- English proof (translation)
Introduce `D ψ A B χ om hom θ hθ ν 𝓨 hν μ 𝓕 hμ U hU K hK`. Take `⟨U', hU', hlev, hb⟩` from `UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont D ψ (dblSp A) B 1 χ om hom θ hθ μ 𝓕 hμ ((fun y => (y, (1 : GA D B))) '' K) (hK.image (continuous_id.prodMk continuous_const)) U hU`. Take `⟨d₁, C₁, h₁⟩` from `UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO D ψ hom.std θ hθ (dblSp A) B μ 𝓕 hμ U' hU'`. Take `⟨d', C', h'⟩` from `hb d₁`. Use `⟨d', C₁ * C', fun f hf y hy => ?_⟩` and prove the remaining obligations.

Establish `hm : (y, (1 : GA D B)) ∈ (fun y => (y, (1 : GA D B))) '' K` using `⟨y, hy, rfl⟩`. Establish `hsup` using `h₁ _ (hlev f hf _ hm)`. Establish `hle` using `h' f hf _ hm`. Establish `hone : ν 𝓨 = 1` using `hν.2.2`. Unfold `swSec GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero`.

Use `(enorm_integral_le_lintegral_enorm _).trans ?_` and prove the remaining obligations. Use `(lintegral_mono fun w => hsup _).trans ?_` and prove the remaining obligations. Rewrite using `[lintegral_const, Measure.restrict_apply_univ, hone, mul_one, ENNReal.coe_mul, mul_assoc]`. Use `gcongr`.
-/
theorem swSec_sobBdd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ (μ : Measure (WO (dblSp A) B)) (𝓕 : Set (WO (dblSp A) B)), IsCovolOne (ratL B (dblSp A)) μ 𝓕 → SobBdd ψ θ μ 𝓕 fun φ y => ‖swSec A B om ν 𝓨 φ y‖ₑ := by
  intro D ψ A B χ om hom θ hθ ν 𝓨 hν μ 𝓕 hμ U hU K hK
  obtain ⟨U', hU', hlev, hb⟩ := UpperTheory.Lit.Rallis.ThetaDens.om_compact_sobCont D ψ (dblSp A) B 1 χ om hom θ hθ μ 𝓕 hμ
    ((fun y => (y, (1 : GA D B))) '' K) (hK.image (continuous_id.prodMk continuous_const)) U hU
  obtain ⟨d₁, C₁, h₁⟩ := UpperTheory.Lit.Rallis.ThetaDensSup.sup_le_sobO D ψ hom.std θ hθ (dblSp A) B μ 𝓕 hμ U' hU'
  obtain ⟨d', C', h'⟩ := hb d₁
  refine ⟨d', C₁ * C', fun f hf y hy => ?_⟩
  have hm : (y, (1 : GA D B)) ∈ (fun y => (y, (1 : GA D B))) '' K := ⟨y, hy, rfl⟩
  have hsup := h₁ _ (hlev f hf _ hm)
  have hle := h' f hf _ hm
  have hone : ν 𝓨 = 1 := hν.2.2
  unfold swSec GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono fun w => hsup _).trans ?_
  rw [lintegral_const, Measure.restrict_apply_univ, hone, mul_one, ENNReal.coe_mul, mul_assoc]
  gcongr

end UpperTheory.Lit.Rallis.ThetaDens
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd | exact UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Rallis.T.siegelWeilSection_bounded_by_sobolevSeminorm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ (μ : Measure (WO (dblSp A) B)) (𝓕 : Set (WO (dblSp A) B)), IsCovolOne (ratL B (dblSp A)) μ 𝓕 → SobBdd ψ θ μ 𝓕 fun φ y => ‖swSec A B om ν 𝓨 φ y‖ₑ := by
  first | exact @UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd | exact UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd | (intros; apply UpperTheory.Lit.Rallis.ThetaDens.swSec_sobBdd <;> assumption)
end
