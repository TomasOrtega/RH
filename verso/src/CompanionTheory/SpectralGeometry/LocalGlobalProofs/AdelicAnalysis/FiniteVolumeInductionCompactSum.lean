import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeBlockOneExtensionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CountGen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hE_eq_dot (σ : E →ₐ[F] E) {M : ℕ} (A : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hE σ A x y = ((σ : E →+* E) ∘ x) ⬝ᵥ (A *ᵥ y) := by
  simp [hE, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hE_mulVec (σ : E →ₐ[F] E) {M : ℕ} (J g : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hE σ J (g *ᵥ x) (g *ᵥ y) = hE σ (cT (σ : E →+* E) g * J * g) x y := by
  have h1 : ((σ : E →+* E) ∘ (g *ᵥ x)) = (g.map (σ : E →+* E)) *ᵥ ((σ : E →+* E) ∘ x) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) g x i
  rw [hE_eq_dot, hE_eq_dot, h1, ← Matrix.mulVec_mulVec y (cT (σ : E →+* E) g * J) g,
    ← Matrix.mulVec_mulVec _ (cT (σ : E →+* E) g) J,
    Matrix.dotProduct_mulVec ((σ : E →+* E) ∘ x) (cT (σ : E →+* E) g) _]
  simp only [cT, Matrix.vecMul_transpose]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a b
  exact hE_mulVec σ J g (X a) (X b)

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCompact_preimage_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    {Ω : Set (Fin n → Fin M → R ⊗[F] E)} (hΩ : IsCompact Ω) :
    IsCompact (actTup R g ⁻¹' Ω) := by
  have h : actTup R g ⁻¹' Ω = actTup R g⁻¹ '' Ω := by
    ext X
    constructor
    · intro hX
      refine ⟨actTup R g X, hX, ?_⟩
      funext a
      simp [actTup, Matrix.mulVec_mulVec]
    · rintro ⟨Y, hY, rfl⟩
      have : actTup R g (actTup R g⁻¹ Y) = Y := by
        funext a
        simp [actTup, Matrix.mulVec_mulVec]
      simpa [Set.mem_preimage, this] using hY
  rw [h]
  exact hΩ.image (continuous_actTup R g⁻¹)

end Top

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Split into cases according to the possible forms of the given data.

Treat this case separately. It suffices to derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem finite_count : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ (M' : ℕ), M' < M → ∀ J' : Matrix (Fin M') (Fin M') E, IsHermND σ J' → FinVol F E σ M' J') → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | gramE σ J X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hvol t ht μ 𝓕 hμ h𝓕 Ω hΩ
  by_cases hS : ∃ X : Fin 1 → Fin M → E, gramE σ J X = fun _ _ => algebraMap F E t
  · obtain ⟨X₀, hX₀⟩ := hS
    have hx : hE σ J (X₀ 0) (X₀ 0) = algebraMap F E t := congrFun (congrFun hX₀ 0) 0
    cases M with
    | zero =>
      exfalso
      have h0 : hE σ J (X₀ 0) (X₀ 0) = 0 := by simp [hE, hform]
      rw [h0] at hx
      exact ht ((map_eq_zero (algebraMap F E)).1 hx.symm)
    | succ M₁ =>
      obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
      have htop := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).1
      obtain ⟨g, J₁, hJ₁, hblock, -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hcm M₁ J hJ t (X₀ 0) ht hx
      obtain ⟨μ', 𝓕', hμ', h𝓕', -, hcnt⟩ :=
        GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hcm (M₁ + 1) J hJ g _ hblock μ 𝓕 hμ h𝓕
      rw [hcnt 1 _ _]
      have hset : {X : Fin 1 → Fin (M₁ + 1) → E |
          (fun a => (g : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E) *ᵥ X a) ∈
            {X : Fin 1 → Fin (M₁ + 1) → E | gramE σ J X = fun _ _ => algebraMap F E t}} =
          {X | gramE σ (blockOne (algebraMap F E t) J₁) X = fun _ _ => algebraMap F E t} := by
        ext X
        simp only [Set.mem_setOf_eq, gramE_mulVec, hblock]
      have hfun : (fun Y : Fin 1 → Fin (M₁ + 1) → AF F ⊗[F] E =>
          Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) (bc (inclR (AF F)) g) Y)) =
          Set.indicator (actTup (AF F) (bc (inclR (AF F)) g) ⁻¹' Ω) (fun _ => (1 : ℝ≥0∞)) := by
        funext Y
        by_cases hY : actTup (AF F) (bc (inclR (AF F)) g) Y ∈ Ω
        · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (Set.mem_preimage.2 hY)]
        · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (Set.mem_preimage.1 h))]
      rw [hset, hfun]
      exact GlobalTheory.T.finite_volume_block_one_extension F E σ hcm M₁ J₁ hJ₁ (hvol M₁ (Nat.lt_succ_self M₁) J₁ hJ₁) t ht μ' 𝓕' hμ' h𝓕' _
        (isCompact_preimage_actTup (AF F) _ hΩ)
  · have hemp : {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hS ⟨X, h⟩
    rw [hemp]
    simp [cntI]

end GlobalTheory.CompanionTheory.SW.CountGen
