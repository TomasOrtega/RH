import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.VacDensity

/- English proof (translation)
Introduce `X ι _ _ M hfd ρ hst hid hmul hirr P hP`. Distinguish the cases in `hM : M = ⊥`. Use `⟨0, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hM, Submodule.mem_bot]`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Set `r : ι → Module.End ℂ M` to `fun i => (ρ i).restrict (hst i)`. Establish `hr : ∀ i (x : M), (r i x : X) = ρ i x` using `fun _ _ => rfl`. Set `p : Submodule ℂ (Module.End ℂ M)` to `Submodule.span ℂ (Set.range r)`. Establish `h1 : (1 : Module.End ℂ M) ∈ p`.

Take `⟨i, hi⟩` from `hid`. Establish `: r i = 1` using `LinearMap.ext fun x => Subtype.ext (hi x x.2)`. Rewrite using `[← this]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `hm : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p`.

Introduce `x y hx hy`. Establish `hle : p * p ≤ p`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩`. Take `⟨a, k, hk⟩` from `hmul i j`.

Establish `: r i * r j = a • r k` using `LinearMap.ext fun x => Subtype.ext (hk x x.2)`. Use `show r i * r j ∈ p`. Rewrite using `[this]`. Conclude with `p.smul_mem a (Submodule.subset_span ⟨k, rfl⟩)`. Conclude with `hle (Submodule.mul_mem_mul hx hy)`.

Set `A : Subalgebra ℂ (Module.End ℂ M)` to `p.toSubalgebra h1 hm`. Establish `hntM : Nontrivial M` using `Submodule.nontrivial_iff_ne_bot.2 hM`. Use `haveI : IsSimpleModule A M := by`. Use `{ toNontrivial := ?_, eq_bot_or_eq_top := fun N => ?_ }` and prove the remaining obligations. Take `⟨x, hx⟩` from `exists_ne (0 : M)`.

Use `⟨⟨⊥, ⊤, fun h => hx ?_⟩⟩` and prove the remaining obligations. Establish `: x ∈ (⊤ : Submodule A M)` using `Submodule.mem_top`. Rewrite `this` using `[← h]`. Conclude with `(Submodule.mem_bot A).1 this`. Set `W : Submodule ℂ X` to `(N.restrictScalars ℂ).map M.subtype`.

Establish `hWM : W ≤ M`. Introduce and unpack `_ ⟨m, -, rfl⟩`. Conclude with `m.2`. Establish `hWst : ∀ i, ∀ x ∈ W, ρ i x ∈ W`. Introduce and unpack `i _ ⟨m, hm, rfl⟩`.

Use `⟨r i m, ?_, rfl⟩` and prove the remaining obligations. Establish `hri : r i ∈ A` using `Submodule.subset_span ⟨i, rfl⟩`. Conclude with `N.smul_mem (⟨r i, hri⟩ : A) hm`. Break down `hirr W hWM hWst with h | h` into its components or cases. Use `left`.

Use `eq_bot_iff.2 fun m hm => (Submodule.mem_bot A).2 ?_` and prove the remaining obligations. Establish `: (m : X) ∈ W` using `⟨m, hm, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Use `right`.

Use `eq_top_iff.2 fun m _ => ?_` and prove the remaining obligations. Establish `: (m : X) ∈ W` using `by rw [h]; exact m.2`. Take `⟨m', hm', e⟩` from `this`. Rewrite `hm'` using `[Subtype.ext e]`. Then use the resulting hypothesis. Establish `hscal : ∀ φ : Module.End A M, ∃ c : ℂ, ∀ m, φ m = c • m`.

Introduce `φ`. Take `⟨c, hc⟩` from `(IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := M) ℂ).2 φ`. Conclude with `⟨c, fun m => by rw [← hc]; rfl⟩`. Set `F : Module.End (Module.End A M) M` to `{ toFun := fun m => ⟨P m, hP m m.2⟩ map_add' := fun x y => Subtype.ext (by simp) map_smul' := fun φ m => by`. Take `⟨c, hc⟩` from `hscal φ`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Module.End.smul_def, RingHom.id_apply, hc, Submodule.coe_smul, map_smul] }`. Set `b` to `Module.finBasis ℂ M`. Take `⟨a, ha⟩` from `jacobson_density F (Finset.univ.image b)`. Establish `hPa : (a : Module.End ℂ M) = P.restrict hP`.

Use `b.ext fun i => ?_` and prove the remaining obligations. Use `ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))` as an intermediate fact. Conclude with `this.symm`. Establish `hap : (a : Module.End ℂ M) ∈ p` using `a.2`. Take `⟨c, hc⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hap`.

Use `⟨c, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun e : Module.End ℂ M => (e ⟨x, hx⟩ : X)) (hc.trans hPa)`. Simplify using `only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul] at e`. Simplify using `only [Finsupp.sum]`. Conclude with `e`.
-/
theorem burn_span : ∀ {X ι : Type} [AddCommGroup X] [Module ℂ X] (M : Submodule ℂ X), FiniteDimensional ℂ M →
    ∀ (ρ : ι → X →ₗ[ℂ] X), (∀ i, ∀ x ∈ M, ρ i x ∈ M) → (∃ i, ∀ x ∈ M, ρ i x = x) →
    (∀ i j, ∃ (a : ℂ) (k : ι), ∀ x ∈ M, ρ i (ρ j x) = a • ρ k x) →
    (∀ W : Submodule ℂ X, W ≤ M → (∀ i, ∀ x ∈ W, ρ i x ∈ W) → W = ⊥ ∨ W = M) →
    ∀ P : X →ₗ[ℂ] X, (∀ x ∈ M, P x ∈ M) → ∃ c : ι →₀ ℂ, ∀ x ∈ M, (c.sum fun i z => z • ρ i x) = P x := by
  intro X ι _ _ M hfd ρ hst hid hmul hirr P hP
  classical
  by_cases hM : M = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    rw [hM, Submodule.mem_bot] at hx
    subst hx
    simp
  let r : ι → Module.End ℂ M := fun i => (ρ i).restrict (hst i)
  have hr : ∀ i (x : M), (r i x : X) = ρ i x := fun _ _ => rfl
  let p : Submodule ℂ (Module.End ℂ M) := Submodule.span ℂ (Set.range r)
  have h1 : (1 : Module.End ℂ M) ∈ p := by
    obtain ⟨i, hi⟩ := hid
    have : r i = 1 := LinearMap.ext fun x => Subtype.ext (hi x x.2)
    rw [← this]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hm : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p := by
    intro x y hx hy
    have hle : p * p ≤ p := by
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      obtain ⟨a, k, hk⟩ := hmul i j
      have : r i * r j = a • r k := LinearMap.ext fun x => Subtype.ext (hk x x.2)
      show r i * r j ∈ p
      rw [this]
      exact p.smul_mem a (Submodule.subset_span ⟨k, rfl⟩)
    exact hle (Submodule.mul_mem_mul hx hy)
  let A : Subalgebra ℂ (Module.End ℂ M) := p.toSubalgebra h1 hm
  have hntM : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hM
  haveI : IsSimpleModule A M := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top := fun N => ?_ }
    · obtain ⟨x, hx⟩ := exists_ne (0 : M)
      refine ⟨⟨⊥, ⊤, fun h => hx ?_⟩⟩
      have : x ∈ (⊤ : Submodule A M) := Submodule.mem_top
      rw [← h] at this
      exact (Submodule.mem_bot A).1 this
    · let W : Submodule ℂ X := (N.restrictScalars ℂ).map M.subtype
      have hWM : W ≤ M := by
        rintro _ ⟨m, -, rfl⟩
        exact m.2
      have hWst : ∀ i, ∀ x ∈ W, ρ i x ∈ W := by
        rintro i _ ⟨m, hm, rfl⟩
        refine ⟨r i m, ?_, rfl⟩
        have hri : r i ∈ A := Submodule.subset_span ⟨i, rfl⟩
        exact N.smul_mem (⟨r i, hri⟩ : A) hm
      rcases hirr W hWM hWst with h | h
      · left
        refine eq_bot_iff.2 fun m hm => (Submodule.mem_bot A).2 ?_
        have : (m : X) ∈ W := ⟨m, hm, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · right
        refine eq_top_iff.2 fun m _ => ?_
        have : (m : X) ∈ W := by rw [h]; exact m.2
        obtain ⟨m', hm', e⟩ := this
        rwa [Subtype.ext e] at hm'
  have hscal : ∀ φ : Module.End A M, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := M) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  let F : Module.End (Module.End A M) M :=
    { toFun := fun m => ⟨P m, hP m m.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        apply Subtype.ext
        simp only [Module.End.smul_def, RingHom.id_apply, hc, Submodule.coe_smul, map_smul] }
  let b := Module.finBasis ℂ M
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image b)
  have hPa : (a : Module.End ℂ M) = P.restrict hP := by
    refine b.ext fun i => ?_
    have := ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact this.symm
  have hap : (a : Module.End ℂ M) ∈ p := a.2
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hap
  refine ⟨c, fun x hx => ?_⟩
  have e := congrArg (fun e : Module.End ℂ M => (e ⟨x, hx⟩ : X)) (hc.trans hPa)
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul] at e
  simp only [Finsupp.sum]
  exact e

/- English proof (translation)
Introduce `X _ _ M W hfd hWM B hl hr horth`. Use `haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWM`. Establish `hl0 : ∀ g ∈ M, B 0 g = 0` using `fun g hg => by`. Use `hl 1 0 0 g M.zero_mem M.zero_mem hg` as an intermediate fact. Simplify using `only [smul_zero, add_zero, star_one, one_mul] at this`.

Take the linear combination `-this`. Establish `hr0 : ∀ f ∈ M, B f 0 = 0` using `fun f hf => by`. Use `hr 1 f 0 0 hf M.zero_mem M.zero_mem` as an intermediate fact. Simplify using `only [smul_zero, add_zero, one_mul] at this`. Take the linear combination `-this`.

Set `b` to `Module.finBasis ℂ W`. Set `L : M →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ)` to `{ toFun := fun f i => star (B f (b i)) map_add' := fun f f' => funext fun i => by`. Use `hl 1 f f' (b i) f.2 f'.2 (hWM (b i).2)` as an intermediate fact. Simplify using `only [one_smul, star_one, one_mul] at this`. Simplify using `[this]`.

Use the proof step `map_smul' := fun a f => funext fun i => by`. Use `hl a f 0 (b i) f.2 M.zero_mem (hWM (b i).2)` as an intermediate fact. Rewrite `this` using `[add_zero, hl0 _ (hWM (b i).2), add_zero]`. Simplify using `[this] }`. Establish `hinj : Function.Injective L`.

Use `(injective_iff_map_eq_zero L).2 fun f hf => Subtype.ext (horth f f.2 fun g hg => ?_)` and prove the remaining obligations. Establish `hbi : ∀ i, B f (b i) = 0` using `fun i => by`. Use `congrFun hf i` as an intermediate fact. Simplify `this` using `[L]`. Set `K : Submodule ℂ X` to `{ carrier := {g | g ∈ M ∧ B f g = 0} add_mem' := fun {g g'} hg hg' => ⟨M.add_mem hg.1 hg'.1, by`.

Use `hr 1 f g g' f.2 hg.1 hg'.1` as an intermediate fact. Simplify using `only [one_smul, one_mul] at this`. Rewrite using `[this, hg.2, hg'.2, add_zero]⟩`. Use the proof step `zero_mem' := ⟨M.zero_mem, hr0 f f.2⟩`. Use the proof step `smul_mem' := fun a g hg => ⟨M.smul_mem a hg.1, by`.

Use `hr a f g 0 f.2 hg.1 M.zero_mem` as an intermediate fact. Rewrite `this` using `[add_zero, hr0 f f.2, add_zero]`. Rewrite using `[this, hg.2, mul_zero]⟩ }`. Establish `hsum` using `b.sum_repr ⟨g, hg⟩`. Establish `hgK : (⟨g, hg⟩ : W) = ∑ i, (b.repr ⟨g, hg⟩ i) • b i` using `hsum.symm`.

Establish `: g ∈ K`. Establish `e` using `congrArg Subtype.val hgK`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at e`. Rewrite using `[e]`. Conclude with `K.sum_mem fun i _ => K.smul_mem _ ⟨hWM (b i).2, hbi i⟩`.

Conclude with `this.2`. Establish `hle : Module.finrank ℂ M ≤ Module.finrank ℂ W`. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact. Simplify using `using this`. Conclude with `Submodule.eq_of_le_of_finrank_le hWM hle`.
-/
theorem eq_of_orth : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (M W : Submodule ℂ X), FiniteDimensional ℂ M → W ≤ M →
    ∀ B : X → X → ℂ, (∀ (a : ℂ) (f f' g : X), f ∈ M → f' ∈ M → g ∈ M → B (a • f + f') g = star a * B f g + B f' g) →
    (∀ (a : ℂ) (f g g' : X), f ∈ M → g ∈ M → g' ∈ M → B f (a • g + g') = a * B f g + B f g') →
    (∀ f ∈ M, (∀ g ∈ W, B f g = 0) → f = 0) → W = M := by
  intro X _ _ M W hfd hWM B hl hr horth
  classical
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWM
  have hl0 : ∀ g ∈ M, B 0 g = 0 := fun g hg => by
    have := hl 1 0 0 g M.zero_mem M.zero_mem hg
    simp only [smul_zero, add_zero, star_one, one_mul] at this
    linear_combination -this
  have hr0 : ∀ f ∈ M, B f 0 = 0 := fun f hf => by
    have := hr 1 f 0 0 hf M.zero_mem M.zero_mem
    simp only [smul_zero, add_zero, one_mul] at this
    linear_combination -this
  let b := Module.finBasis ℂ W
  let L : M →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun f i => star (B f (b i))
      map_add' := fun f f' => funext fun i => by
        have := hl 1 f f' (b i) f.2 f'.2 (hWM (b i).2)
        simp only [one_smul, star_one, one_mul] at this
        simp [this]
      map_smul' := fun a f => funext fun i => by
        have := hl a f 0 (b i) f.2 M.zero_mem (hWM (b i).2)
        rw [add_zero, hl0 _ (hWM (b i).2), add_zero] at this
        simp [this] }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun f hf => Subtype.ext (horth f f.2 fun g hg => ?_)
    have hbi : ∀ i, B f (b i) = 0 := fun i => by
      have := congrFun hf i
      simpa [L] using this
    let K : Submodule ℂ X :=
      { carrier := {g | g ∈ M ∧ B f g = 0}
        add_mem' := fun {g g'} hg hg' => ⟨M.add_mem hg.1 hg'.1, by
          have := hr 1 f g g' f.2 hg.1 hg'.1
          simp only [one_smul, one_mul] at this
          rw [this, hg.2, hg'.2, add_zero]⟩
        zero_mem' := ⟨M.zero_mem, hr0 f f.2⟩
        smul_mem' := fun a g hg => ⟨M.smul_mem a hg.1, by
          have := hr a f g 0 f.2 hg.1 M.zero_mem
          rw [add_zero, hr0 f f.2, add_zero] at this
          rw [this, hg.2, mul_zero]⟩ }
    have hsum := b.sum_repr ⟨g, hg⟩
    have hgK : (⟨g, hg⟩ : W) = ∑ i, (b.repr ⟨g, hg⟩ i) • b i := hsum.symm
    have : g ∈ K := by
      have e := congrArg Subtype.val hgK
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      rw [e]
      exact K.sum_mem fun i _ => K.smul_mem _ ⟨hWM (b i).2, hbi i⟩
    exact this.2
  have hle : Module.finrank ℂ M ≤ Module.finrank ℂ W := by
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  exact Submodule.eq_of_le_of_finrank_le hWM hle

end GlobalTheory.VacDensity

/- English proof (translation)
Introduce `D ψ θ S T hψ hθ sS sT hcS hcT v hv hvac U hU`. Distinguish the cases in `hv0 : v = 0`. Use `⟨0, by simp, by simp [hv0], fun x _ _ => ⟨0, by simp⟩⟩` and prove the remaining obligations. Take `⟨U₀, o₀, l₀⟩` from `hv.level`. Use `set U' : AddSubgroup (WO S T) := U ⊓ U₀ with hU'def`.

Establish `hU' : IsOpen (U' : Set (WO S T))` using `by rw [hU'def, AddSubgroup.coe_inf]; exact hU.inter o₀`. Use `set M := GlobalTheory.VacSchurFin.vacSub hψ hθ sS sT U' with hMdef`. Establish `hfd` using `GlobalTheory.VacSchurFin.fd_vacSub hψ hθ sS sT hcS hcT U' hU'`. Establish `hvM : v ∈ M` using `GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨hv, fun u hu h => l₀ u (AddSubgroup.mem_inf.1 hu).2 h, hvac⟩`. Establish `hxM : ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) → x ∈ M` using `fun x hx hxv => GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨hx.1, fun u hu h => hx.2 u (AddSubgroup.mem_inf.1 hu).1 h, hxv⟩`.

Set `N : Set (WO S T)` to `{w | w.map (infPart D) = 0 ∧ ∀ u ∈ U', u.map (infPart D) = 0 → ψ (symplO S T u w) = 1}`. Set `ρ : N → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)` to `fun i => GlobalTheory.SplitScalar.heisL ψ S T i.1`. Establish `laws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `hst : ∀ w ∈ N, ∀ f ∈ M, heisO ψ S T w f ∈ M`. Introduce and unpack `w ⟨hw, hA⟩ f hf`.

Take `⟨hfT, hfL, hfV⟩` from `GlobalTheory.VacSchurFin.mem_vacSub.1 hf`. Conclude with `GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨laws.1 w f hfT, fun u hu h0 => by`. Rewrite using `[GlobalTheory.SplitScalar.heisO_comm, hA u hu h0, one_smul, hfL u hu h0], GlobalTheory.VacSchurFin.vac_heisO_fin hθ hw hfV⟩`. Establish `h0N : (0 : WO S T) ∈ N` using `⟨by ext i j; show infPart D (0 : AE D) = 0; exact RingHom.map_zero _, fun u _ _ => by`. Rewrite using `[GlobalTheory.SplitScalar.symplO_zero_right, AddChar.map_zero_eq_one]⟩`.

Establish `haddN : ∀ w ∈ N, ∀ w' ∈ N, w + w' ∈ N`. Introduce and unpack `w ⟨hw, hA⟩ w' ⟨hw', hA'⟩`. Use `⟨?_, fun u hu h0 => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h1 : infPart D (w i j) = 0` using `congrFun (congrFun hw i) j`.

Establish `h2 : infPart D (w' i j) = 0` using `congrFun (congrFun hw' i) j`. Use `show infPart D (w i j + w' i j) = 0`. Rewrite using `[RingHom.map_add, h1, h2, add_zero]`. Rewrite using `[GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, hA u hu h0, hA' u hu h0, one_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (WO S T → ℂ), ℓ v = 1 := by`.

Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual ℂ (WO S T → ℂ), f v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)`. Conclude with `⟨(f v)⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩`.

Set `P : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)` to `ℓ.smulRight v`. Establish `hirr : ∀ W : Submodule ℂ (WO S T → ℂ), W ≤ M → (∀ i, ∀ x ∈ W, ρ i x ∈ W) → W = ⊥ ∨ W = M`. Introduce `W hWM hWst`. Distinguish the cases in `hW : W = ⊥`. Conclude with `Or.inl hW`.

Use `right`. Take `⟨g, hgW, hg0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Take `⟨vol⟩` from `GlobalTheory.Unf.Inhab.nonempty_volM D T.rank S.rank`. Establish `hcv : IsCovolOne (ratL T S) vol.μ vol.𝓕` using `vol.covol`. Use `GlobalTheory.VacDensity.eq_of_orth M W hfd hWM (GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕) (fun a f f' g hf hf' hg => GlobalTheory.VacSchurFin.thetaInner_left hψ hcv a (GlobalTheory.VacSchurFin.mem_vacSub.1 hf).1 (GlobalTheory.VacSchurFin.mem_vacSub.1 hf').1 (GlobalTheory.VacSchur …` and prove the remaining obligations.

Introduce `f hf hfo`. Take `⟨hfT, hfL, hfV⟩` from `GlobalTheory.VacSchurFin.mem_vacSub.1 hf`. Take `⟨hgT, hgL, hgV⟩` from `GlobalTheory.VacSchurFin.mem_vacSub.1 (hWM hgW)`. Use `(GlobalTheory.VacSchurFin.irr_vac D ψ θ S T hψ hθ sS sT hcS hcT vol.μ vol.𝓕 hcv f g hfT hgT hfV hgV fun w hw => ?_).resolve_right hg0` and prove the remaining obligations. Distinguish the cases in `hA : ∀ u ∈ U', u.map (infPart D) = 0 → ψ (symplO S T u w) = 1`.

Conclude with `hfo _ (hWst ⟨w, hw, hA⟩ g hgW)`. Use `push_neg at hA`. Take `⟨u, hu, h0, hne1⟩` from `hA`. Establish `hwg : IsThetaFunO ψ S T (heisO ψ S T w g)` using `laws.1 w g hgT`. Establish `e1 : GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 f (heisO ψ S T w g) = GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 (heisO ψ S T u f) (heisO ψ S T u (heisO ψ S T w g))` using `(GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hfT hwg u).symm`.

Rewrite `e1` using `[hfL u hu h0, GlobalTheory.SplitScalar.heisO_comm, hgL u hu h0, GlobalTheory.VacSchurFin.thetaInner_smul_right]`. Establish `: (1 - ψ (symplO S T u w)) * GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 f (heisO ψ S T w g) = 0`. Take the linear combination `e1`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne1))`. Take `⟨c, hc⟩` from `GlobalTheory.VacDensity.burn_span M hfd ρ (fun i x hx => hst i.1 i.2 x hx) ⟨⟨0, h0N⟩, fun x _ => GlobalTheory.SplitScalar.heisO_zero ψ S T x⟩ (fun i j => ⟨ψ (symplOH S T i.1 j.1), ⟨i.1 + j.1, haddN i.1 i.2 j.1 j.2⟩, fun x _ => GlobalTheory.SplitScalar.heisO_heisO ψ S T i.1 j.1 x⟩ …`.

Establish `hsum : ∀ x, ((c.mapDomain Subtype.val).sum fun u z => z • heisO ψ S T u x) = c.sum fun i z => z • ρ i x` using `fun x => Finsupp.sum_mapDomain_index (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)`. Use `⟨c.mapDomain Subtype.val, fun u hu => ?_, ?_, fun x hx hxv => ⟨ℓ x, ?_⟩⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hu)`. Conclude with `i.2.1`. Rewrite using `[hsum, hc v hvM]`.

Simplify using `[P, hℓ]`. Rewrite using `[hsum, hc x (hxM x hx hxv)]`. Simplify using `[P]`.
-/
theorem GlobalTheory.VacDensity.proj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ v : WO S T → ℂ, IsThetaFunO ψ S T v → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) v) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) ∧ (c.sum fun u z => z • heisO ψ S T u v) = v ∧ ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) → ∃ a : ℂ, (c.sum fun u z => z • heisO ψ S T u x) = a • v := by
  intro D ψ θ S T hψ hθ sS sT hcS hcT v hv hvac U hU
  classical
  by_cases hv0 : v = 0
  · refine ⟨0, by simp, by simp [hv0], fun x _ _ => ⟨0, by simp⟩⟩
  obtain ⟨U₀, o₀, l₀⟩ := hv.level
  set U' : AddSubgroup (WO S T) := U ⊓ U₀ with hU'def
  have hU' : IsOpen (U' : Set (WO S T)) := by rw [hU'def, AddSubgroup.coe_inf]; exact hU.inter o₀
  set M := GlobalTheory.VacSchurFin.vacSub hψ hθ sS sT U' with hMdef
  have hfd := GlobalTheory.VacSchurFin.fd_vacSub hψ hθ sS sT hcS hcT U' hU'
  have hvM : v ∈ M := GlobalTheory.VacSchurFin.mem_vacSub.2
    ⟨hv, fun u hu h => l₀ u (AddSubgroup.mem_inf.1 hu).2 h, hvac⟩
  have hxM : ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) →
      x ∈ M := fun x hx hxv => GlobalTheory.VacSchurFin.mem_vacSub.2
    ⟨hx.1, fun u hu h => hx.2 u (AddSubgroup.mem_inf.1 hu).1 h, hxv⟩
  let N : Set (WO S T) := {w | w.map (infPart D) = 0 ∧ ∀ u ∈ U', u.map (infPart D) = 0 → ψ (symplO S T u w) = 1}
  let ρ : N → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := fun i => GlobalTheory.SplitScalar.heisL ψ S T i.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hst : ∀ w ∈ N, ∀ f ∈ M, heisO ψ S T w f ∈ M := by
    rintro w ⟨hw, hA⟩ f hf
    obtain ⟨hfT, hfL, hfV⟩ := GlobalTheory.VacSchurFin.mem_vacSub.1 hf
    exact GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨laws.1 w f hfT, fun u hu h0 => by
      rw [GlobalTheory.SplitScalar.heisO_comm, hA u hu h0, one_smul, hfL u hu h0], GlobalTheory.VacSchurFin.vac_heisO_fin hθ hw hfV⟩
  have h0N : (0 : WO S T) ∈ N := ⟨by ext i j; show infPart D (0 : AE D) = 0; exact RingHom.map_zero _, fun u _ _ => by
    rw [GlobalTheory.SplitScalar.symplO_zero_right, AddChar.map_zero_eq_one]⟩
  have haddN : ∀ w ∈ N, ∀ w' ∈ N, w + w' ∈ N := by
    rintro w ⟨hw, hA⟩ w' ⟨hw', hA'⟩
    refine ⟨?_, fun u hu h0 => ?_⟩
    · ext i j
      have h1 : infPart D (w i j) = 0 := congrFun (congrFun hw i) j
      have h2 : infPart D (w' i j) = 0 := congrFun (congrFun hw' i) j
      show infPart D (w i j + w' i j) = 0
      rw [RingHom.map_add, h1, h2, add_zero]
    · rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, hA u hu h0, hA' u hu h0, one_mul]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (WO S T → ℂ), ℓ v = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (WO S T → ℂ), f v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
    exact ⟨(f v)⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  let P : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := ℓ.smulRight v
  have hirr : ∀ W : Submodule ℂ (WO S T → ℂ), W ≤ M → (∀ i, ∀ x ∈ W, ρ i x ∈ W) → W = ⊥ ∨ W = M := by
    intro W hWM hWst
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨g, hgW, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨vol⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank S.rank
    have hcv : IsCovolOne (ratL T S) vol.μ vol.𝓕 := vol.covol
    refine GlobalTheory.VacDensity.eq_of_orth M W hfd hWM (GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕)
      (fun a f f' g hf hf' hg => GlobalTheory.VacSchurFin.thetaInner_left hψ hcv a (GlobalTheory.VacSchurFin.mem_vacSub.1 hf).1
        (GlobalTheory.VacSchurFin.mem_vacSub.1 hf').1 (GlobalTheory.VacSchurFin.mem_vacSub.1 hg).1)
      (fun a f g g' hf hg hg' => GlobalTheory.VacSchurFin.thetaInner_right hψ hcv a (GlobalTheory.VacSchurFin.mem_vacSub.1 hf).1
        (GlobalTheory.VacSchurFin.mem_vacSub.1 hg).1 (GlobalTheory.VacSchurFin.mem_vacSub.1 hg').1) ?_
    intro f hf hfo
    obtain ⟨hfT, hfL, hfV⟩ := GlobalTheory.VacSchurFin.mem_vacSub.1 hf
    obtain ⟨hgT, hgL, hgV⟩ := GlobalTheory.VacSchurFin.mem_vacSub.1 (hWM hgW)
    refine (GlobalTheory.VacSchurFin.irr_vac D ψ θ S T hψ hθ sS sT hcS hcT vol.μ vol.𝓕 hcv f g hfT hgT hfV hgV
      fun w hw => ?_).resolve_right hg0
    by_cases hA : ∀ u ∈ U', u.map (infPart D) = 0 → ψ (symplO S T u w) = 1
    · exact hfo _ (hWst ⟨w, hw, hA⟩ g hgW)
    · push_neg at hA
      obtain ⟨u, hu, h0, hne1⟩ := hA
      have hwg : IsThetaFunO ψ S T (heisO ψ S T w g) := laws.1 w g hgT
      have e1 : GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 f (heisO ψ S T w g) =
          GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 (heisO ψ S T u f) (heisO ψ S T u (heisO ψ S T w g)) :=
        (GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hfT hwg u).symm
      rw [hfL u hu h0, GlobalTheory.SplitScalar.heisO_comm, hgL u hu h0, GlobalTheory.VacSchurFin.thetaInner_smul_right] at e1
      have : (1 - ψ (symplO S T u w)) * GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 f (heisO ψ S T w g) = 0 := by
        linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne1))
  obtain ⟨c, hc⟩ := GlobalTheory.VacDensity.burn_span M hfd ρ (fun i x hx => hst i.1 i.2 x hx)
    ⟨⟨0, h0N⟩, fun x _ => GlobalTheory.SplitScalar.heisO_zero ψ S T x⟩
    (fun i j => ⟨ψ (symplOH S T i.1 j.1), ⟨i.1 + j.1, haddN i.1 i.2 j.1 j.2⟩, fun x _ =>
      GlobalTheory.SplitScalar.heisO_heisO ψ S T i.1 j.1 x⟩) hirr P (fun x _ => M.smul_mem _ hvM)
  have hsum : ∀ x, ((c.mapDomain Subtype.val).sum fun u z => z • heisO ψ S T u x) = c.sum fun i z => z • ρ i x :=
    fun x => Finsupp.sum_mapDomain_index (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)
  refine ⟨c.mapDomain Subtype.val, fun u hu => ?_, ?_, fun x hx hxv => ⟨ℓ x, ?_⟩⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
    exact i.2.1
  · rw [hsum, hc v hvM]
    simp [P, hℓ]
  · rw [hsum, hc x (hxM x hx hxv)]
    simp [P]
