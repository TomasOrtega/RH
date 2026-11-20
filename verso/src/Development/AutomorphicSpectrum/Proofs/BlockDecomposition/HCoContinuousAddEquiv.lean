import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ d b n`. Take `⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R`. Take `⟨hinv, δ, hδ, hσδ⟩` from `GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM`. Establish `hfin : Module.finrank F E = 2` using `hCM.2.2.1`. Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _`. Use `haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _`. Set `h1 : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)` to `(GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv hfin hδ hσδ n t5 t6).homeomorph _`. Set `h2 : (R ⊗[F] E) ≃ₜ (Fin d → R)` to `(t7 d b).homeomorph _`. Establish `h2a : ∀ y k, h2 y k = (Algebra.TensorProduct.basis R b).repr y k` using `fun _ _ => rfl`.

Set `G : ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) ≃ₜ (Idx n d → R)` to `{ toFun := fun x => Sum.elim x.1 (fun q => h2 (x.2 q.2) q.1) invFun := fun f => (fun i => f (Sum.inl i), fun p => h2.symm fun k => f (Sum.inr (k, p))) left_inv := by`. Introduce and unpack `⟨x, y⟩`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Conclude with `h2.symm_apply_apply (y p)`.

Use `right_inv := by`. Introduce `f`. Use function extensionality and compare the values at `q`. Break down `q with i | ⟨k, p⟩` into its components or cases. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Use `continuous_toFun := by`. Use `continuous_pi fun q => ?_` and prove the remaining obligations. Break down `q with i | ⟨k, p⟩` into its components or cases. Conclude with `(continuous_apply i).comp continuous_fst`.

Conclude with `(continuous_apply k).comp (h2.continuous.comp ((continuous_apply p).comp continuous_snd))`. Use `continuous_invFun := by`. Use `Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun p => ?_)` and prove the remaining obligations. Conclude with `h2.symm.continuous.comp (continuous_pi fun k => continuous_apply _) }`. Set `H : HermR R σ n ≃ₜ (Idx n d → R)` to `h1.trans G`.

Establish `hH : ∀ S, H S = hCo R σ b S`. Introduce `S`. Use function extensionality and compare the values at `q`. Apply the tactic sequence `rcases q with i | ⟨k, p⟩ <;> rfl`. Use `⟨{ toEquiv := H.toEquiv map_add' := ?_ continuous_toFun := H.continuous continuous_invFun := H.symm.continuous }, hH⟩` and prove the remaining obligations.

Introduce `S T`. Use `show H (S + T) = H S + H T`. Rewrite using `[hH, hH, hH]`. Use function extensionality and compare the values at `q`. Break down `q with i | ⟨k, p⟩` into its components or cases.

Simplify using `[hCo, map_add, mul_add]`. Simplify using `[hCo, map_add]`.
-/
theorem hCo_continuousAddEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ d b n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hfin : Module.finrank F E = 2 := hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  let h1 : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv hfin hδ hσδ n t5 t6).homeomorph _
  let h2 : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  have h2a : ∀ y k, h2 y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let G : ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) ≃ₜ (Idx n d → R) :=
    { toFun := fun x => Sum.elim x.1 (fun q => h2 (x.2 q.2) q.1)
      invFun := fun f => (fun i => f (Sum.inl i), fun p => h2.symm fun k => f (Sum.inr (k, p)))
      left_inv := by
        rintro ⟨x, y⟩
        refine Prod.ext rfl ?_
        funext p
        exact h2.symm_apply_apply (y p)
      right_inv := by
        intro f
        funext q
        rcases q with i | ⟨k, p⟩
        · rfl
        · simp
      continuous_toFun := by
        refine continuous_pi fun q => ?_
        rcases q with i | ⟨k, p⟩
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply k).comp
            (h2.continuous.comp ((continuous_apply p).comp continuous_snd))
      continuous_invFun := by
        refine Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun p => ?_)
        exact h2.symm.continuous.comp (continuous_pi fun k => continuous_apply _) }
  let H : HermR R σ n ≃ₜ (Idx n d → R) := h1.trans G
  have hH : ∀ S, H S = hCo R σ b S := by
    intro S
    funext q
    rcases q with i | ⟨k, p⟩ <;> rfl
  refine ⟨{ toEquiv := H.toEquiv
            map_add' := ?_
            continuous_toFun := H.continuous
            continuous_invFun := H.symm.continuous }, hH⟩
  intro S T
  show H (S + T) = H S + H T
  rw [hH, hH, hH]
  funext q
  rcases q with i | ⟨k, p⟩
  · simp [hCo, map_add, mul_add]
  · simp [hCo, map_add]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
