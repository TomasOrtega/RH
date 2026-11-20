import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentSupportPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxVanishOffFinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

/- English proof (translation)
Introduce `v w h`. Establish `h1 : Ideal.map (Formalism.DivisionValues.cO K) v.asIdeal = Ideal.map (Formalism.DivisionValues.cO K) w.asIdeal` using `congrArg HeightOneSpectrum.asIdeal h`. Establish `hb : Function.Bijective (Formalism.DivisionValues.cO K)` using `(Formalism.DivisionValues.cO K).bijective`. Establish `h2` using `congrArg (Ideal.comap (Formalism.DivisionValues.cO K)) h1`. Rewrite `h2` using `[Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb]`.

Conclude with `HeightOneSpectrum.ext h2`.
-/
theorem conjPl_injective {K : Type} [Field K] [StarRing K] :
    Function.Injective (Formalism.DivisionValues.conjPl (K := K)) := by
  intro v w h
  have h1 : Ideal.map (Formalism.DivisionValues.cO K) v.asIdeal = Ideal.map (Formalism.DivisionValues.cO K) w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal h
  have hb : Function.Bijective (Formalism.DivisionValues.cO K) := (Formalism.DivisionValues.cO K).bijective
  have h2 := congrArg (Ideal.comap (Formalism.DivisionValues.cO K)) h1
  rw [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h2
  exact HeightOneSpectrum.ext h2

/- English proof (translation)
Take `⟨S, hS⟩` from `hA.fg`. Establish `hSm : ∀ a ∈ S, a ∈ A` using `fun a ha => hS ▸ Submodule.subset_span ha`. Establish `mem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔ ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x`. Introduce `x`. Unfold `Formalism.HermitianLatticesTheory.dual Formalism.E.hdual`.

Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]`. Use `choose g hg using fun (x : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) (a : S) => (mem x).1 x.2 a (hSm a a.2)`. Establish `inj : Function.Injective (algebraMap (𝓞 K) K)` using `FaithfulSMul.algebraMap_injective (𝓞 K) K`. Set `φ : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A →ₗ[𝓞 K] (S → 𝓞 K)` to `{ toFun := g map_add' := fun x y => funext fun a => inj (by`. Rewrite using `[hg, Submodule.coe_add, map_add, Pi.add_apply, map_add, hg, hg])`.

Use the proof step `map_smul' := fun s x => funext fun a => inj (by`. Rewrite using `[hg, Submodule.coe_smul, ← algebraMap_smul K s (x : Fin d → K), map_smul]`. Simplify using `only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hg]) }`. Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `h0 : ∀ a ∈ S, Formalism.DivisionValues.hform H a x = 0`. Introduce `a ha`. Rewrite using `[← hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩, map_zero]`. Establish `hL : ∀ a ∈ A, Formalism.DivisionValues.hform H a x = 0`.

Introduce `a ha`. Rewrite `ha` using `[← hS]`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha => exact h0 a ha`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]`. Consider the case `smul s a _ ha => rw [← algebraMap_smul K s a, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]`. Establish `hV : ∀ a, Formalism.DivisionValues.hform H a x = 0`. Introduce `a`. Establish `ha : a ∈ Submodule.span K (A : Set (Fin d → K))` using `by rw [hA.span_eq_top]; trivial`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha => exact hL a ha`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]`. Consider the case `smul s a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]`.

Establish `hM : Matrix.mulVec H (x : Fin d → K) = 0`. Use function extensionality and compare the values at `i`. Use `hV (Pi.single i 1)` as an intermediate fact. Simplify `this` using `[Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm]`. Conclude with `Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hH.ne_zero hM)`.

Conclude with `Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)`.
-/
theorem dual_fg {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A).FG := by
  classical
  obtain ⟨S, hS⟩ := hA.fg
  have hSm : ∀ a ∈ S, a ∈ A := fun a ha => hS ▸ Submodule.subset_span ha
  have mem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
    intro x
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
  choose g hg using fun (x : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) (a : S) => (mem x).1 x.2 a (hSm a a.2)
  have inj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let φ : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := g
      map_add' := fun x y => funext fun a => inj (by
        rw [hg, Submodule.coe_add, map_add, Pi.add_apply, map_add, hg, hg])
      map_smul' := fun s x => funext fun a => inj (by
        rw [hg, Submodule.coe_smul, ← algebraMap_smul K s (x : Fin d → K), map_smul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hg]) }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ a ∈ S, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩, map_zero]
    have hL : ∀ a ∈ A, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hS] at ha
      induction ha using Submodule.span_induction with
      | mem a ha => exact h0 a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [← algebraMap_smul K s a, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hV : ∀ a, Formalism.DivisionValues.hform H a x = 0 := by
      intro a
      have ha : a ∈ Submodule.span K (A : Set (Fin d → K)) := by rw [hA.span_eq_top]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha => exact hL a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hM : Matrix.mulVec H (x : Fin d → K) = 0 := by
      funext i
      have := hV (Pi.single i 1)
      simpa [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm] using this
    exact Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hH.ne_zero hM)
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `GlobalTheory.Mem.IdxFin.lidx_finite A _ hA.fg (dual_fg H hH A hA)`.
-/
theorem jw_finite_of_lat {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.jw H w A ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite A _ hA.fg (dual_fg H hH A hA)

/- English proof (translation)
The claim follows from `GlobalTheory.Mem.IdxFin.lidx_finite M _ hM (hL.map _)`.
-/
theorem idx_finite_of_fg {K : Type} [Field K] [NumberField K] {d d' : ℕ} (M : Submodule (𝓞 K) (Fin d' → K))
    (θ : Matrix (Fin d') (Fin d) K) (L : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG) (hL : L.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.idx w M (Formalism.DivisionValues.matLat θ L) ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite M _ hM (hL.map _)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
