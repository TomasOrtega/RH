import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
namespace GlobalTheory.TransportIso

/- English proof (translation)
Introduce `G G' _ _ _ _ _ _ _ _ Φ ν W _ _ σ`. Establish `hs : ∀ g' : G', Φ.symm.toMulEquiv g' = Φ.symm g'` using `fun _ => rfl`. Establish `hs2 : ∀ g' : G', Φ.symm.toMulEquiv.toMonoidHom g' = Φ.symm g'` using `fun _ => rfl`. Establish `hcomp' : ∀ g' : G', (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' = σ (Φ.symm g')` using `fun _ => rfl`. Establish `hcomp : ∀ g : G, (σ.comp Φ.symm.toMulEquiv.toMonoidHom) (Φ g) = σ g`.

Introduce `g`. Rewrite using `[hcomp', Φ.symm_apply_apply]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hσ`. Set `e : Subrepresentation (σ.comp Φ.symm.toMulEquiv.toMonoidHom) ≃o Subrepresentation σ` to `{ toFun := fun U => ⟨U.toSubmodule, fun g v hv => by`.

Use `U.apply_mem_toSubmodule (Φ g) hv` as an intermediate fact. Rewrite using `[hcomp] at this⟩` and apply the resulting hypothesis. Use `invFun := fun U => ⟨U.toSubmodule, fun g' v hv => by`. Rewrite using `[hcomp']`. Conclude with `U.apply_mem_toSubmodule _ hv⟩`.

Use `left_inv := fun U => rfl`. Use `right_inv := fun U => rfl`. Use the proof step `map_rel_iff' := Iff.rfl }`. Conclude with `e.isSimpleOrder`. Introduce and unpack `⟨hsm, hfd⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Establish `: {g' : G' | (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v = v} = Φ.symm ⁻¹' {g | σ g v = v}`. Use extensionality with `g'`. Conclude with `Iff.rfl`.

Rewrite using `[this]`. Conclude with `(hsm v).preimage Φ.symm.continuous`. Introduce `K' hK'o hK'c`. Set `K : Subgroup G` to `K'.comap Φ.toMulEquiv.toMonoidHom`. Establish `hKo : IsOpen (K : Set G)` using `hK'o.preimage Φ.continuous`.

Establish `hKc : IsCompact (K : Set G)`. Establish `: (K : Set G) = Φ.symm '' (K' : Set G')`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg; exact ⟨Φ g, hg, by simp⟩`.

Introduce and unpack `⟨g', hg', rfl⟩ show Φ (Φ.symm g') ∈ K'`. Simplify using `using hg'`. Rewrite using `[this]`. Conclude with `hK'c.image Φ.symm.continuous`. Establish `heq : GlobalTheory.PRep.fixed (σ.comp Φ.symm.toMulEquiv.toMonoidHom) K' = GlobalTheory.PRep.fixed σ K`.

Use extensionality with `v`. Simplify using `only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]`. Prove the components needed by the constructor for the conclusion. Introduce `hv h`. Use `hv ⟨Φ h, h.2⟩` as an intermediate fact.

Simplify using `at this ⊢`. Use `this using 3` and compare the differences between its conclusion and the goal. Conclude with `(Φ.symm_apply_apply _).symm`. Introduce `hv h`. Use `hv ⟨Φ.symm h, show Φ (Φ.symm h) ∈ K' by simpa using h.2⟩` as an intermediate fact.

Simplify using `at this ⊢`. Use `this using 3` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `hfd K hKo hKc`.

Introduce `f f' hf A`. Set `e : G ≃ᵐ G'` to `Φ.toHomeomorph.toMeasurableEquiv`. Establish `hmap : ν.map Φ = ν.map e` using `rfl`. Establish `he : ∀ g, e g = Φ g` using `fun g => rfl`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp, hmap]`.

Use `forall_congr' fun v => forall_congr' fun l => ?_` and prove the remaining obligations. Rewrite using `[integrable_map_equiv, integral_map_equiv]`. Establish `hfun : ((fun g' => f' g' * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v)) ∘ e) = fun g => f g * l (σ g v)`. Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp_apply, he, hf, hcomp]`.

Establish `hfun' : (fun g => f' (e g) * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) (e g) v)) = fun g => f g * l (σ g v)`. Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp_apply, he, hf, hcomp]`. Rewrite using `[hfun, hfun']`.
-/
theorem irreducible_admissible_integralOp_transport : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  intro G G' _ _ _ _ _ _ _ _ Φ ν W _ _ σ
  have hs : ∀ g' : G', Φ.symm.toMulEquiv g' = Φ.symm g' := fun _ => rfl
  have hs2 : ∀ g' : G', Φ.symm.toMulEquiv.toMonoidHom g' = Φ.symm g' := fun _ => rfl
  have hcomp' : ∀ g' : G', (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' = σ (Φ.symm g') := fun _ => rfl
  have hcomp : ∀ g : G, (σ.comp Φ.symm.toMulEquiv.toMonoidHom) (Φ g) = σ g := by
    intro g; rw [hcomp', Φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro hσ
    let e : Subrepresentation (σ.comp Φ.symm.toMulEquiv.toMonoidHom) ≃o Subrepresentation σ :=
      { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
          have := U.apply_mem_toSubmodule (Φ g) hv
          rwa [hcomp] at this⟩
        invFun := fun U => ⟨U.toSubmodule, fun g' v hv => by
          rw [hcomp']
          exact U.apply_mem_toSubmodule _ hv⟩
        left_inv := fun U => rfl
        right_inv := fun U => rfl
        map_rel_iff' := Iff.rfl }
    exact e.isSimpleOrder
  · rintro ⟨hsm, hfd⟩
    refine ⟨?_, ?_⟩
    · intro v
      have : {g' : G' | (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v = v} = Φ.symm ⁻¹' {g | σ g v = v} := by
        ext g'; exact Iff.rfl
      rw [this]
      exact (hsm v).preimage Φ.symm.continuous
    · intro K' hK'o hK'c
      let K : Subgroup G := K'.comap Φ.toMulEquiv.toMonoidHom
      have hKo : IsOpen (K : Set G) := hK'o.preimage Φ.continuous
      have hKc : IsCompact (K : Set G) := by
        have : (K : Set G) = Φ.symm '' (K' : Set G') := by
          ext g; constructor
          · intro hg; exact ⟨Φ g, hg, by simp⟩
          · rintro ⟨g', hg', rfl⟩
            show Φ (Φ.symm g') ∈ K'
            simpa using hg'
        rw [this]; exact hK'c.image Φ.symm.continuous
      have heq : GlobalTheory.PRep.fixed (σ.comp Φ.symm.toMulEquiv.toMonoidHom) K' = GlobalTheory.PRep.fixed σ K := by
        ext v
        simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]
        constructor
        · intro hv h
          have := hv ⟨Φ h, h.2⟩
          simp at this ⊢
          convert this using 3
          exact (Φ.symm_apply_apply _).symm
        · intro hv h
          have := hv ⟨Φ.symm h, show Φ (Φ.symm h) ∈ K' by simpa using h.2⟩
          simp at this ⊢
          convert this using 3
          rfl
      rw [heq]
      exact hfd K hKo hKc
  · intro f f' hf A
    let e : G ≃ᵐ G' := Φ.toHomeomorph.toMeasurableEquiv
    have hmap : ν.map Φ = ν.map e := rfl
    have he : ∀ g, e g = Φ g := fun g => rfl
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp, hmap]
    refine forall_congr' fun v => forall_congr' fun l => ?_
    rw [integrable_map_equiv, integral_map_equiv]
    have hfun : ((fun g' => f' g' * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v)) ∘ e) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    have hfun' : (fun g => f' (e g) * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) (e g) v)) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    rw [hfun, hfun']

end GlobalTheory.TransportIso
