import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingRepresentationInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingActionCommutesTranslationStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UAut GlobalTheory.Mem.Th GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

/- English proof (translation)
Introduce `k γ hγ g`. Use `choose p hp e using fun i => (hγ i).eq_oneP hθ`. Simplify `(smooth_iff R f.1).2 f.2 k (fun i => (p i).1) (fun i => (p i).2) hp g` using `only [e]`.
-/
theorem isSm_of_smF (hθ : IsInfFam θ) (R : RealPoints θ V) (f : SmF θ V) : IsSm D.sp.cm.sig V.gram f.1 := by
  intro k γ hγ g
  choose p hp e using fun i => (hγ i).eq_oneP hθ
  simpa only [e] using (smooth_iff R f.1).2 f.2 k (fun i => (p i).1) (fun i => (p i).2) hp g

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨1, fun f => by rw [map_one]; rfl⟩`. Consider the case `cons γ l ih`. Take `⟨w, hw⟩` from `ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)`. Take `⟨⟨τ, X⟩, hX, rfl⟩` from `(hl γ List.mem_cons_self).eq_oneP hθ`.

Use `⟨UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] ⟨X, hX⟩)) * w, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply, ← envIncl_ι, envRepAll_envIncl, envRep_ι, opInf_coe, ← hw, List.foldr_cons]`. Conclude with `Rder_eq R τ ⟨X, hX⟩ _`.
-/
theorem exists_word (hθ : IsInfFam θ) (R : RealPoints θ V) (l : List (ℝ → GA D V))
    (hl : ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ w : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, l.foldr lineDer f.1 = (envRepAll R w f).1 := by
  classical
  induction l with
  | nil => exact ⟨1, fun f => by rw [map_one]; rfl⟩
  | cons γ l ih =>
    obtain ⟨w, hw⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    obtain ⟨⟨τ, X⟩, hX, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    refine ⟨UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] ⟨X, hX⟩)) * w,
      fun f => ?_⟩
    rw [map_mul, Module.End.mul_apply, ← envIncl_ι, envRepAll_envIncl, envRep_ι, opInf_coe, ← hw, List.foldr_cons]
    exact Rder_eq R τ ⟨X, hX⟩ _

/- English proof (translation)
Use `choose! w hw using fun l (hl : l ∈ z.support) => exists_word hθ R l (hz l hl)`. Use `⟨∑ l ∈ z.support, z l • w l, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, LinearMap.sum_apply, Submodule.coe_sum]`. Use function extensionality and compare the values at `g`. Simplify using `only [dop, Finsupp.sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← hw l hl]`.
-/
theorem exists_env (hθ : IsInfFam θ) (R : RealPoints θ V) (z : List (ℝ → GA D V) →₀ ℂ)
    (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ u : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  classical
  choose! w hw using fun l (hl : l ∈ z.support) => exists_word hθ R l (hz l hl)
  refine ⟨∑ l ∈ z.support, z l • w l, fun f => ?_⟩
  rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  simp only [dop, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← hw l hl]

/- English proof (translation)
Rewrite using `[Subalgebra.mem_center_iff]`. Introduce `b`. Establish `hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V))`. Unfold `UniversalEnvelopingAlgebra.mkAlgHom`. Apply the tactic sequence `first | exact RingCon.mkₐ_surjective _ _ | exact RingCon.mkₐ_surjective _ | exact fun b => Quotient.inductionOn' b fun t => ⟨t, rfl⟩ | exact Quot.mk_surjective`.

Take `⟨t, rfl⟩` from `hs b`. Proceed by induction on `t using TensorAlgebra.induction with`. Consider the case `algebraMap r => rw [AlgHom.commutes]`. Conclude with `Algebra.commutes r u`. Consider the case `ι x => exact h x`.

Consider the case `mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]`. Consider the case `add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]`.
-/
theorem mem_center_of_comm (u : GlobalTheory.AutFinLit.Env V)
    (h : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x * u = u * UniversalEnvelopingAlgebra.ι ℂ x) :
    u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V)) := by
    unfold UniversalEnvelopingAlgebra.mkAlgHom
    first | exact RingCon.mkₐ_surjective _ _ | exact RingCon.mkₐ_surjective _ | exact fun b => Quotient.inductionOn' b fun t => ⟨t, rfl⟩ | exact Quot.mk_surjective
  obtain ⟨t, rfl⟩ := hs b
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r u
  | ι x => exact h x
  | mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]

/- English proof (translation)
Use `choose c hc hg using exists_gelf R`. Establish `hloc : ∀ τ, ∀ z ∈ Subalgebra.center ℂ (EnvAt V τ), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W`. Introduce `τ z hz`. Rewrite `hz` using `[hc τ]`. Proceed by induction on `hz using Algebra.adjoin_induction with`.

Consider the case `mem x hx => obtain ⟨k, rfl⟩ := hx`. Introduce `f hf`. Rewrite using `[← hg]`. Conclude with `hs τ k _ hf`. Consider the case `algebraMap r => intro f hf`.

Rewrite using `[AlgHom.commutes]`. Conclude with `W.smul_mem r hf`. Consider the case `add x y _ _ hx hy => intro f hf`. Rewrite using `[map_add]`. Conclude with `add_mem (hx f hf) (hy f hf)`.

Consider the case `mul x y _ _ hx hy => intro f hf`. Rewrite using `[map_mul]`. Conclude with `hx _ (hy f hf)`. Rewrite `hu` using `[GlobalTheory.EnvCentre.center_directSum D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) (fun τ => envIncl V τ) (fun τ x => envIncl_ι τ x)]`. Proceed by induction on `hu using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨τ, z, hz, rfl⟩` from `Set.mem_iUnion.1 hx |>.imp fun τ h => h`. Introduce `f hf`. Rewrite using `[envRepAll_envIncl]`. Conclude with `hloc τ z hz f hf`.

Consider the case `algebraMap r => intro f hf`. Rewrite using `[AlgHom.commutes]`. Conclude with `W.smul_mem r hf`. Consider the case `add x y _ _ hx hy => intro f hf`. Rewrite using `[map_add]`.

Conclude with `add_mem (hx f hf) (hy f hf)`. Consider the case `mul x y _ _ hx hy => intro f hf`. Rewrite using `[map_mul]`. Conclude with `hx _ (hy f hf)`.
-/
theorem mem_of_mem_center (R : RealPoints θ V) {W : Submodule ℂ (GA D V → ℂ)}
    (hs : ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) {u : GlobalTheory.AutFinLit.Env V}
    (hu : u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V)) : ∀ f : SmF θ V, f.1 ∈ W → (envRepAll R u f).1 ∈ W := by
  classical
  choose c hc hg using exists_gelf R
  have hloc : ∀ τ, ∀ z ∈ Subalgebra.center ℂ (EnvAt V τ), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W := by
    intro τ z hz
    rw [hc τ] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; rw [← hg]; exact hs τ k _ hf
    | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
    | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)
  rw [GlobalTheory.EnvCentre.center_directSum D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) (fun τ => envIncl V τ)
    (fun τ x => envIncl_ι τ x)] at hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, z, hz, rfl⟩ := Set.mem_iUnion.1 hx |>.imp fun τ h => h
    intro f hf; rw [envRepAll_envIncl]; exact hloc τ z hz f hf
  | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
  | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
  | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_env hθ R z hz.1`. Use `⟨u, mem_center_of_comm u fun x => GlobalTheory.T.enveloping_representation_injective _ _ hθ V R ?_, hu⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Use `GlobalTheory.T.enveloping_action_commutes_translation _ _ hθ V R u (fun a ha f hfa => ?_) x` and prove the remaining obligations. Rewrite using `[← hu, ← hu]`.

Use function extensionality and compare the values at `g`. Conclude with `hz.2 f.1 (isSm_of_smF hθ R f) a ha g`.
-/
theorem exists_center (hθ : IsInfFam θ) (R : RealPoints θ V) {z : List (ℝ → GA D V) →₀ ℂ}
    (hz : IsCentral D.sp.cm.sig V.gram z) :
    ∃ u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V), ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  obtain ⟨u, hu⟩ := exists_env hθ R z hz.1
  refine ⟨u, mem_center_of_comm u fun x => GlobalTheory.T.enveloping_representation_injective _ _ hθ V R ?_, hu⟩
  rw [map_mul, map_mul]
  refine GlobalTheory.T.enveloping_action_commutes_translation _ _ hθ V R u (fun a ha f hfa => ?_) x
  rw [← hu, ← hu]
  funext g
  exact hz.2 f.1 (isSm_of_smF hθ R f) a ha g

end GlobalTheory.CentralOps
