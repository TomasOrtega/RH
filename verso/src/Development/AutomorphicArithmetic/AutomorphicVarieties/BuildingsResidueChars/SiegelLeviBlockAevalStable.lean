import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModOfInjectiveIntertwining
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInter
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qe22.aeval_inter f T T' h p x`.
-/
private theorem aeval_inter {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N) (h : ∀ x, f (T x) = T' (f x))
    (p : Polynomial ℂ) (x : M) : f (Polynomial.aeval T p x) = Polynomial.aeval T' p (f x) :=
  _root_.UpperTheory.Reformulated.B.Qe22.aeval_inter f T T' h p x

/- English proof (translation)
Introduce `K _ _ a n e Γ S Z ι _ D hZ hS z hz`. Use `UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ {x | ∃ τ u, x = capOp D a τ u} ?_ ?_ _ (UpperTheory.centerU_action_mem_adjoin_capOp K a ι D z hz)` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩ _ ⟨σ, v, rfl⟩`. Conclude with `Zc_comm (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D τ u) (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D σ v)`. Introduce and unpack `_ ⟨τ, u, rfl⟩`.

Take `⟨p, hp, hpS⟩` from `hS τ u`. Use `⟨p, hp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hle : slSp e Γ S ≤ LinearMap.ker (Polynomial.aeval (capOp D a τ u) p)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `φ ⟨ψ, hψ, g, hg, hφ⟩`.

Take `⟨f, hf, hl⟩` from `UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g`. Establish `hfφ : φ = f ψ` using `Subtype.ext (funext fun m => (hφ m).trans (hf ψ m).symm)`. Establish `hgen : ∀ i j y, f (gen D (lam K n) τ (e i) (e j) y) = gen D (lam K a) τ i j (f y)` using `fun i j y => gen_inter D (lam K n) (lam K a) τ (e i) (e j) i j (f ∘ₗ LinearMap.applyₗ y) (LinearMap.applyₗ (f y)) fun t => by`. Express the relevant statement in the definitionally equal form `f (lam K n (Matrix.single (e i) (e j) t) y) = lam K a (Matrix.single i j t) (f y)`. Rewrite using `[← matrixExtendByZero_single, hl]`.

Establish `hq : ∀ y, f (archCapBlock D e τ u y) = capOp D a τ u (f y)` using `UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ hgen u`. Express the relevant statement in the definitionally equal form `Polynomial.aeval (capOp D a τ u) p φ = 0`. Rewrite using `[hfφ, ← aeval_inter f _ _ hq]`. Conclude with `Subtype.ext (funext fun m => (hf _ m).trans (hZ _ (hpS ψ hψ) g hg m))`. Conclude with `hle hx`.
-/
theorem UpperTheory.siegelLevi_block_aeval_stable :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S Z : Submodule ℂ (archSmooth K n)) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), (∀ ψ ∈ Z, ∀ g ∈ Γ, ∀ m, ψ.1 (g * emb e m) = 0) → (∀ τ u, AlgMod S Z (archCapBlock D e τ u)) → Centre (slSp e Γ S) := by
  intro K _ _ a n e Γ S Z ι _ D hZ hS z hz
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ {x | ∃ τ u, x = capOp D a τ u} ?_ ?_ _ (UpperTheory.centerU_action_mem_adjoin_capOp K a ι D z hz)
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨σ, v, rfl⟩
    exact Zc_comm (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D τ u) (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D σ v)
  · rintro _ ⟨τ, u, rfl⟩
    obtain ⟨p, hp, hpS⟩ := hS τ u
    refine ⟨p, hp, fun x hx => ?_⟩
    have hle : slSp e Γ S ≤ LinearMap.ker (Polynomial.aeval (capOp D a τ u) p) := by
      refine Submodule.span_le.2 ?_
      rintro φ ⟨ψ, hψ, g, hg, hφ⟩
      obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
      have hfφ : φ = f ψ := Subtype.ext (funext fun m => (hφ m).trans (hf ψ m).symm)
      have hgen : ∀ i j y, f (gen D (lam K n) τ (e i) (e j) y) = gen D (lam K a) τ i j (f y) := fun i j y =>
        gen_inter D (lam K n) (lam K a) τ (e i) (e j) i j (f ∘ₗ LinearMap.applyₗ y) (LinearMap.applyₗ (f y))
          fun t => by
            change f (lam K n (Matrix.single (e i) (e j) t) y) = lam K a (Matrix.single i j t) (f y)
            rw [← matrixExtendByZero_single, hl]
      have hq : ∀ y, f (archCapBlock D e τ u y) = capOp D a τ u (f y) :=
        UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ hgen u
      change Polynomial.aeval (capOp D a τ u) p φ = 0
      rw [hfφ, ← aeval_inter f _ _ hq]
      exact Subtype.ext (funext fun m => (hf _ m).trans (hZ _ (hpS ψ hψ) g hg m))
    exact hle hx
