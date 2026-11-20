import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIntertwining
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIsomorphism

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TransportF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}
variable {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat`. Establish `hR : IsTotallyReal F` using `hB.cm.1`. Establish `hψ : IsCharAF F B.ψ` using `hω.std.1`. Set `τ` to `Fintype.equivFin κ`. Establish `he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (numCoordF co τ w) (numCoordF co τ w')` using `fun w w' => by`.

Rewrite using `[symplOF_eq_symp hA hB', co.form]`. Simplify using `only [symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]`. Establish `hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F, numCoordF co τ (ratWF x) = (rat y, rat z)` using `fun x => by`. Take `⟨y, z, h⟩` from `hrat x`. Conclude with `⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩`.

Establish `hadd : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (Φ + Φ') = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ + GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ'` using `fun Φ hΦ Φ' hΦ' => by`. Simplify using `only [thetaTr_eqF co τ]`. Conclude with `congrArg (· ∘ numCoordF co τ) (thV_add hR hψ (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ)) (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ')))`. Establish `hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' → Φ = Φ'` using `fun Φ hΦ Φ' hΦ' h => by`. Simplify using `only [thetaTr_eqF co τ] at h`.

Establish `h2` using `thV_injOn hR hψ (comp_mem_schA τ hΦ) (comp_mem_schA τ hΦ') ((numCoordF co τ).surjective.injective_comp_right h)`. Use function extensionality and compare the values at `x`. Simplify `congrFun h2 (x ∘ τ.symm)` using `[Function.comp_def]`. Establish `hon : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f ↔ ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = f` using `fun f => by`. Prove the components needed by the constructor for the conclusion.

Introduce `hf`. Take `⟨Φ, hΦ, h⟩` from `_root_.GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr f hf`. Use `⟨_, comp_mem_schA τ.symm hΦ, ?_⟩` and prove the remaining obligations. Rewrite using `[thetaTr_eqF co τ, ← h]`. Use `congr 2`.

Use function extensionality and compare the values at `x`. Simplify using `[Function.comp_def]`. Introduce and unpack `⟨Φ, hΦ, rfl⟩`. Rewrite using `[thetaTr_eqF co τ]`. Conclude with `_root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr _ (comp_mem_schA τ hΦ)`.

Take `⟨om, hom⟩` from `exists_transport' _ _ _ hadd (thetaTr_smulF co) hinj hon (ω.comp (pairHomF hS hξ0 hA hB')) fun p f hf => hω.om_pres _ f hf`. Use `⟨om, ?_⟩` and prove the remaining obligations. Introduce `a b g h hh hg Φ hΦ`. Establish `e : (ω.comp (pairHomF hS hξ0 hA hB')) (a, b) = ω (g, h)` using `congrArg ω (pairHomF_eq hS hξ0 hA hB' a b g h hh hg)`. Establish `h2` using `hom (a, b) Φ hΦ`.

Conclude with `⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩`.
-/
theorem exists_isTransportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let τ := Fintype.equivFin κ
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (numCoordF co τ w) (numCoordF co τ w') := fun w w' => by
    rw [symplOF_eq_symp hA hB', co.form]
    simp only [symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      numCoordF co τ (ratWF x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩
  have hadd : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (Φ + Φ') =
        GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ + GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' := fun Φ hΦ Φ' hΦ' => by
    simp only [thetaTr_eqF co τ]
    exact congrArg (· ∘ numCoordF co τ) (thV_add hR hψ
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ))
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ')))
  have hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' → Φ = Φ' :=
    fun Φ hΦ Φ' hΦ' h => by
    simp only [thetaTr_eqF co τ] at h
    have h2 := thV_injOn hR hψ (comp_mem_schA τ hΦ) (comp_mem_schA τ hΦ')
      ((numCoordF co τ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ τ.symm)
  have hon : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f ↔
      ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = f := fun f => by
    constructor
    · intro hf
      obtain ⟨Φ, hΦ, h⟩ := _root_.GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr f hf
      refine ⟨_, comp_mem_schA τ.symm hΦ, ?_⟩
      rw [thetaTr_eqF co τ, ← h]
      congr 2
      funext x
      simp [Function.comp_def]
    · rintro ⟨Φ, hΦ, rfl⟩
      rw [thetaTr_eqF co τ]
      exact _root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr _
        (comp_mem_schA τ hΦ)
  obtain ⟨om, hom⟩ := exists_transport' _ _ _ hadd (thetaTr_smulF co) hinj hon
    (ω.comp (pairHomF hS hξ0 hA hB')) fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  intro a b g h hh hg Φ hΦ
  have e : (ω.comp (pairHomF hS hξ0 hA hB')) (a, b) = ω (g, h) :=
    congrArg ω (pairHomF_eq hS hξ0 hA hB' a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩
end GlobalTheory.TransportF
end
end
