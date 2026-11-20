import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFunctionsAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKStepA

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `μ 𝓕 _ _ _ h`. Simplify using the standard rewrite rules. Introduce `t m _ h`. Simplify using the standard rewrite rules.

Introduce `t m _ h`. Simplify using the standard rewrite rules.
-/
theorem split2_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' d₁ : ℕ} {W : Spc F E (a + a')} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) :
    Split2 W₁ H' X (0 : UA σ W.J → ℂ) 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ 𝓕 _ _ _ h
    simp
  · intro t m _ h
    simp
  · intro t m _ h
    simp

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Set `τ : E →+* ℂ` to `(B.emb w).1`. Establish `hcm : ∀ z : E, τ (σ z) = star (τ z)` using `fun z => hB.cm.2.2.2 τ z`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm, hcm, star_star]`.
-/
theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) (hB : B.IsGood σ) (z : E) : σ (σ z) = z := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let τ : E →+* ℂ := (B.emb w).1
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  apply τ.injective
  rw [hcm, hcm, star_star]

end GlobalTheory.ThKStepA

open GlobalTheory.ThKStepA in

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' Φ' hΦ' hI`. Take `⟨C, hC0, hC'⟩` from `(GlobalTheory.T.constant_terms_vanish hKP).2 F E σ B b a' G G₁ H H' hC e' he'`. Take `⟨fa, hs, hfa⟩` from `hC' X om om' om₁ om₁' hT hT₁ Φ' hΦ'`. Rewrite `hs` using `[hI]`. Take `⟨hfa0, -⟩` from `GlobalTheory.T.split_functions_adapted_plane hKP F E σ B (b + 2) a' G.W (b + a') G₁.W H' 0 (b + 1) _ _ _ _ X hT.base hT.geo.lt hT.geo.hW hT₁.geo.hW hC.hH' 0 fa 0 0 0 hs (split2_zero G₁.W H' X)`.

Use function extensionality and compare the values at `h₁`. Take `⟨m, hm, -⟩` from `GlobalTheory.PlaneLeviExt.levi_existsUnique F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ _ _ (sigma_sigma B hT.base) hT.geo.hW hT₁.geo.hW hC.hH' h₁`. Establish `key` using `hfa h₁ m hm 1`. Rewrite `key` using `[mul_one, hfa0]`. Establish `h11 : om' (1, 1) = 1` using `map_one om'`.

Rewrite `key` using `[h11, Module.End.one_apply]`. Use `(mul_eq_zero.mp key.symm).resolve_left hC0` as an intermediate fact. Simplify using `using this`.
-/
theorem GlobalTheory.ThK.stepA_vanish : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∀ Φ' ∈ PolData B G.M', G.M'.I om' Φ' = 0 → G₁.M'.I om₁' (e' Φ') = 0 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' Φ' hΦ' hI
  obtain ⟨C, hC0, hC'⟩ := (GlobalTheory.T.constant_terms_vanish hKP).2 F E σ B b a' G G₁ H H' hC e' he'
  obtain ⟨fa, hs, hfa⟩ := hC' X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  rw [hI] at hs
  obtain ⟨hfa0, -⟩ := GlobalTheory.T.split_functions_adapted_plane hKP F E σ B (b + 2) a' G.W (b + a') G₁.W H' 0 (b + 1) _ _ _ _ X hT.base hT.geo.lt
    hT.geo.hW hT₁.geo.hW hC.hH' 0 fa 0 0 0 hs (split2_zero G₁.W H' X)
  funext h₁
  obtain ⟨m, hm, -⟩ := GlobalTheory.PlaneLeviExt.levi_existsUnique F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ _ _
    (sigma_sigma B hT.base) hT.geo.hW hT₁.geo.hW hC.hH' h₁
  have key := hfa h₁ m hm 1
  rw [mul_one, hfa0] at key
  have h11 : om' (1, 1) = 1 := map_one om'
  rw [h11, Module.End.one_apply] at key
  have := (mul_eq_zero.mp key.symm).resolve_left hC0
  simpa using this
