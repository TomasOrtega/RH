import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.SliceExt

/- English proof (translation)
Take `⟨p, hp⟩` from `j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)`. Establish `hp' : ∀ s, p (j s) = s` using `fun s => LinearMap.congr_fun hp s`. Use `⟨{ toFun := fun g => j ∘ₗ (ρ g) ∘ₗ p + (LinearMap.id - j ∘ₗ p) map_one' := ?_ map_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using the standard rewrite rules.

Introduce `g g'`. Use extensionality with `v`. Simplify using `[hp']`. Introduce `g s`. Simplify using `[hp']`.
-/
theorem exists_extend {G S V : Type*} [Monoid G] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V] (j : S →ₗ[ℂ] V) (hj : Function.Injective j)
    (ρ : G →* Module.End ℂ S) :
    ∃ L : G →* Module.End ℂ V, ∀ g s, L g (j s) = j (ρ g s) := by
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hp' : ∀ s, p (j s) = s := fun s => LinearMap.congr_fun hp s
  refine ⟨{ toFun := fun g => j ∘ₗ (ρ g) ∘ₗ p + (LinearMap.id - j ∘ₗ p)
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext v; simp
  · intro g g'; ext v; simp [hp']
  · intro g s; simp [hp']

noncomputable def splitPts (F : Type) [Field F] [NumberField F] (κ : Type) :
    (κ → AF F) ≃ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := by
    funext i
    show (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), (x i).2) : AF F) = x i
    rw [RingEquiv.symm_apply_apply]; rfl
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i
    exact RingEquiv.apply_symm_apply _ _

open scoped TensorProduct in
open NumberField MeasureTheory in

/- English proof (translation)
Set `ι : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hι : Function.Injective ι` using `DFunLike.coe_injective`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl (LinearMap.range ι)`. Set `j` to `LinearEquiv.ofInjective ι hι`. Set `e` to `Submodule.prodEquivOfIsCompl _ C hC`.

Set `A : G → Module.End ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `fun g => e.toLinearMap ∘ₗ ((j.toLinearMap ∘ₗ (ρ g).toLinearMap ∘ₗ j.symm.toLinearMap).prodMap LinearMap.id) ∘ₗ e.symm.toLinearMap`. Establish `hA1 : A 1 = 1`. Use extensionality with `v`. Simplify using `[A]`. Establish `hAmul : ∀ g h, A (g * h) = A g * A h`.

Introduce `g h`. Use extensionality with `v`. Simplify using `[A]`. Establish `hAι : ∀ g f, A g (ι f) = ι (ρ g f)`. Introduce `g f`.

Establish `: e.symm (ι f) = (j f, 0)`. Rewrite using `[show ι f = ((j f : LinearMap.range ι) : _) from rfl]`. Conclude with `Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC _`. Simplify using `only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.prodMap_apply, LinearEquiv.symm_apply_apply, map_zero, LinearMap.id_apply]`. Rewrite using `[Submodule.coe_prodEquivOfIsCompl']`.

Simplify using `[j]`. Set `s` to `_root_.GlobalTheory.SliceExt.splitPts F κ`. Set `slice : ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → (κ → mixedEmbedding.mixedSpace F) → ℂ` to `fun Φ y a => Φ (s.symm (a, y))`. Set `W : G → Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)` to `fun g => { toFun := fun Φ x => A g (slice Φ (s x).2) (s x).1 map_add' := by`. Introduce `Φ Ψ`.

Use function extensionality and compare the values at `x`. Establish `: slice (Φ + Ψ) (s x).2 = slice Φ (s x).2 + slice Ψ (s x).2` using `rfl`. Simplify using `only [this, map_add, Pi.add_apply]`. Use the proof step `map_smul' := by`. Introduce `c Φ`.

Use function extensionality and compare the values at `x`. Establish `: slice (c • Φ) (s x).2 = c • slice Φ (s x).2` using `rfl`. Simplify using `only [this, map_smul, Pi.smul_apply, RingHom.id_apply] }`. Use `⟨{ toFun := W, map_one' := ?_, map_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Use extensionality with `Φ x`.

Simplify using `only [W, hA1, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply, slice, Prod.mk.eta, Equiv.symm_apply_apply]`. Introduce `g h`. Use extensionality with `Φ x`. Simplify using `only [W, hAmul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]`. Establish `hsl : slice (fun x => A h (slice Φ (s x).2) (s x).1) (s x).2 = A h (slice Φ (s x).2)`.

Use function extensionality and compare the values at `a`. Simplify using `only [slice, Equiv.apply_symm_apply]`. Rewrite using `[hsl]`. Introduce `g f h`. Use function extensionality and compare the values at `x`.

Establish `hsl : ∀ (f' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ), slice (_root_.GlobalTheory.WeilM.pureA F f' h) (s x).2 = h (s x).2 • ι f'`. Introduce `f'`. Use function extensionality and compare the values at `a`. Establish `h1` using `s.apply_symm_apply (a, (s x).2)`. Simplify using `only [slice, _root_.GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]`.

Establish `ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (s.symm (a, (s x).2) i).1) = a` using `congrArg Prod.fst h1`. Establish `hy : (fun i => (s.symm (a, (s x).2) i).2) = (s x).2` using `congrArg Prod.snd h1`. Rewrite using `[ha, hy, mul_comm]`. Both sides reduce to the same expression. Use `show A g (slice (_root_.GlobalTheory.WeilM.pureA F f h) (s x).2) (s x).1 = _`.

Rewrite using `[hsl, map_smul, hAι]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.WeilM.pureA]`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.SliceExt.exists_rep_pure (F : Type) [Field F] [NumberField F]
    (κ : Type) [Fintype κ]
    (G : Type) [Group G] (ρ : G →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →L[ℂ] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)) :
    ∃ ω₀ : G →* Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ), ∀ (g : G) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
      (h : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ),
      ω₀ g (_root_.GlobalTheory.WeilM.pureA F f h) = _root_.GlobalTheory.WeilM.pureA F (ρ g f) h := by
  classical
  let ι : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := DFunLike.coe_injective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range ι)
  let j := LinearEquiv.ofInjective ι hι
  let e := Submodule.prodEquivOfIsCompl _ C hC
  let A : G → Module.End ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ) := fun g =>
    e.toLinearMap ∘ₗ ((j.toLinearMap ∘ₗ (ρ g).toLinearMap ∘ₗ j.symm.toLinearMap).prodMap
      LinearMap.id) ∘ₗ e.symm.toLinearMap
  have hA1 : A 1 = 1 := by
    ext v
    simp [A]
  have hAmul : ∀ g h, A (g * h) = A g * A h := by
    intro g h
    ext v
    simp [A]
  have hAι : ∀ g f, A g (ι f) = ι (ρ g f) := by
    intro g f
    have : e.symm (ι f) = (j f, 0) := by
      rw [show ι f = ((j f : LinearMap.range ι) : _) from rfl]
      exact Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC _
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.prodMap_apply,
      LinearEquiv.symm_apply_apply, map_zero, LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp [j]
  let s := _root_.GlobalTheory.SliceExt.splitPts F κ
  let slice : ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → (κ → mixedEmbedding.mixedSpace F) → ℂ :=
    fun Φ y a => Φ (s.symm (a, y))
  let W : G → Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) := fun g =>
    { toFun := fun Φ x => A g (slice Φ (s x).2) (s x).1
      map_add' := by
        intro Φ Ψ
        funext x
        have : slice (Φ + Ψ) (s x).2 = slice Φ (s x).2 + slice Ψ (s x).2 := rfl
        simp only [this, map_add, Pi.add_apply]
      map_smul' := by
        intro c Φ
        funext x
        have : slice (c • Φ) (s x).2 = c • slice Φ (s x).2 := rfl
        simp only [this, map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨{ toFun := W, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext Φ x
    simp only [W, hA1, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply, slice,
      Prod.mk.eta, Equiv.symm_apply_apply]
  · intro g h
    ext Φ x
    simp only [W, hAmul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    have hsl : slice (fun x => A h (slice Φ (s x).2) (s x).1) (s x).2 = A h (slice Φ (s x).2) := by
      funext a
      simp only [slice, Equiv.apply_symm_apply]
    rw [hsl]
  · intro g f h
    funext x
    have hsl : ∀ (f' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ),
        slice (_root_.GlobalTheory.WeilM.pureA F f' h) (s x).2 = h (s x).2 • ι f' := by
      intro f'
      funext a
      have h1 := s.apply_symm_apply (a, (s x).2)
      simp only [slice, _root_.GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
      have ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (s.symm (a, (s x).2) i).1) = a :=
        congrArg Prod.fst h1
      have hy : (fun i => (s.symm (a, (s x).2) i).2) = (s x).2 := congrArg Prod.snd h1
      rw [ha, hy, mul_comm]
      rfl
    show A g (slice (_root_.GlobalTheory.WeilM.pureA F f h) (s x).2) (s x).1 = _
    rw [hsl, map_smul, hAι]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.WeilM.pureA]
    rw [mul_comm]
    rfl

end GlobalTheory.SliceExt
