import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlaneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnitsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFiniteVolumeIntegralBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.IsoBox

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) (x y : n → A) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (fun i => s (x i)) (cT s g)]`. Use `congr 1`. Use extensionality with `i`. Simplify using `[cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => s (x i)) (cT s g)]
  congr 1
  ext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `a c`. Conclude with `hform_mulVec (σ : E →+* E) J g (X a) (X c)`.
-/
theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a c
  exact hform_mulVec (σ : E →+* E) J g (X a) (X c)

/- English proof (translation)
Use extensionality with `X`. Simplify using `only [Set.mem_ofPred_eq, gramE_mulVec]`. Use `and_congr_left fun _ => not_congr ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use function extensionality and compare the values at `a`. Establish `h1` using `congrFun h a`. Establish `h2 : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((g : Matrix (Fin M) (Fin M) E) *ᵥ X a) = X a`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules.

Rewrite using `[← h2]`. Simplify using `only [Pi.zero_apply] at h1 ⊢`. Rewrite using `[h1, Matrix.mulVec_zero]`. Introduce `h`. Use function extensionality and compare the values at `a`.

Simplify using `[h]`.
-/
theorem isotropic_preimage (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : GL (Fin M) E) :
    {X : Fin 1 → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈
        {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}} =
      {X : Fin 1 → Fin M → E | X ≠ 0 ∧
        gramE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
          (g : Matrix (Fin M) (Fin M) E)) X = 0} := by
  ext X
  simp only [Set.mem_ofPred_eq, gramE_mulVec]
  refine and_congr_left fun _ => not_congr ?_
  constructor
  · intro h
    funext a
    have h1 := congrFun h a
    have h2 : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((g : Matrix (Fin M) (Fin M) E) *ᵥ X a) = X a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
      simp
    rw [← h2]
    simp only [Pi.zero_apply] at h1 ⊢
    rw [h1, Matrix.mulVec_zero]
  · intro h
    funext a
    simp [h]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[actTup, Matrix.mulVec_smul]`.
-/
theorem actTup_smul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    (c : R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) :
    actTup R g (c • Y) = c • actTup R g Y := by
  funext a
  simp [actTup, Matrix.mulVec_smul]

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [actTup, Matrix.mulVec, dotProduct]`. Use `continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((continuous_apply j).comp (continuous_apply a))`.
-/
theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

end GlobalTheory.CompanionTheory.SW.IsoBox

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hF d b N hN`. Distinguish the cases in `hiso : ∃ x : Fin M → E, x ≠ 0 ∧ hE σ J x x = 0`. Take `⟨x, hx, hxx⟩` from `hiso`. Take `⟨M₁, hM₁, g, J₁, hJ₁, hg⟩` from `GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane F E σ hCM M J hJ x hx hxx`. Substitute `hM₁` using the available equality.

Take `⟨μ', 𝓕', hH', hF', -, hT⟩` from `GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hCM (M₁ + 2) J hJ g (hypJ J₁) hg μ 𝓕 hH hF`. Take `⟨τ, hτ⟩` from `GlobalTheory.T.exists_real_flow_adelic_units F E σ hCM`. Take `⟨hbc, -, hsc⟩` from `GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 (M₁ + 2)`. Take `⟨⟨hA1, hA2, hA3⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Use `hA1` as an intermediate fact.

Use `hA2` as an intermediate fact. Use `hA3` as an intermediate fact. Establish `: IsTopologicalRing (AF F ⊗[F] E)` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).1`. Use `set G : GL (Fin (M₁ + 2)) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG`. Establish `hΩ : IsCompact (actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)))`.

Establish `himg : actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) = actTup (AF F) G⁻¹ '' box b N 1`. Use extensionality with `Y`. Prove the components needed by the constructor for the conclusion. Introduce `hY`. Use `⟨_, hY, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Simplify using `[actTup, Matrix.mulVec_mulVec]`. Introduce and unpack `⟨Z, hZ, rfl⟩`. Establish `: actTup (AF F) G (actTup (AF F) G⁻¹ Z) = Z`. Use function extensionality and compare the values at `a`.

Simplify using `[actTup, Matrix.mulVec_mulVec]`. Simplify `hZ` using `[Set.mem_preimage, this]`. Rewrite using `[himg]`. Conclude with `(hbc N 1 hN).image (IsoBox.continuous_actTup (AF F) G⁻¹)`. Take `⟨C, hC⟩` from `GlobalTheory.T.hyperbolic_finite_volume_integral_bound F E σ hCM M₁ J₁ hJ₁ (by omega) (GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M₁ J₁ hJ₁) τ hτ μ' 𝓕' hH' hF' _ hΩ`.

Use `⟨C, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hfun : (fun Y : Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) G Y)) = fun Y => (Set.indicator (actTup (AF F) G ⁻¹' box b N 1) (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • …`. Use function extensionality and compare the values at `Y`. Establish `hmem : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) ↔ ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))`. Establish `h` using `hsc τ hτ N r (-Real.log r) (actTup (AF F) G Y)`.

Establish `h1 : Real.exp (-Real.log r) * r = 1`. Rewrite using `[Real.exp_neg, Real.exp_log hr]`. Conclude with `inv_mul_cancel₀ hr.ne'`. Rewrite `h` using `[h1]`. Rewrite using `[Set.mem_preimage, IsoBox.actTup_smul]`.

Conclude with `h.symm`. Distinguish the cases in `hY : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))`. Rewrite using `[Set.indicator_of_mem hY, Set.indicator_of_mem (hmem.1 hY)]`. Rewrite using `[Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (hmem.2 h))]`. Establish `hset` using `IsoBox.isotropic_preimage σ J g`.

Rewrite `hset` using `[← hg]`. Rewrite using `[hT 1, hset, hfun]`. Simplify using `using hC r hr`. Use `⟨0, fun r _ => ?_⟩` and prove the remaining obligations. Establish `hempty : {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} = ∅`.

Use extensionality with `X`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hX hgr`. Apply `hiso` to reduce the goal to its premises. Use `⟨X 0, fun h0 => hX ?_, congrFun (congrFun hgr 0) 0⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Rewrite using `[Subsingleton.elim a 0, h0]`. Both sides reduce to the same expression. Simplify using `[cntI, hempty]`.
-/
theorem mean_isotropic_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M - 1))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hF d b N hN
  by_cases hiso : ∃ x : Fin M → E, x ≠ 0 ∧ hE σ J x x = 0
  · obtain ⟨x, hx, hxx⟩ := hiso
    obtain ⟨M₁, hM₁, g, J₁, hJ₁, hg⟩ := GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane F E σ hCM M J hJ x hx hxx
    subst hM₁
    obtain ⟨μ', 𝓕', hH', hF', -, hT⟩ :=
      GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hCM (M₁ + 2) J hJ g (hypJ J₁) hg μ 𝓕 hH hF
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hCM
    obtain ⟨hbc, -, hsc⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 (M₁ + 2)
    obtain ⟨⟨hA1, hA2, hA3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have := hA1
    have := hA2
    have := hA3
    have : IsTopologicalRing (AF F ⊗[F] E) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).1
    set G : GL (Fin (M₁ + 2)) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
    have hΩ : IsCompact (actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))) := by
      have himg : actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) =
          actTup (AF F) G⁻¹ '' box b N 1 := by
        ext Y
        constructor
        · intro hY
          refine ⟨_, hY, ?_⟩
          funext a
          simp [actTup, Matrix.mulVec_mulVec]
        · rintro ⟨Z, hZ, rfl⟩
          have : actTup (AF F) G (actTup (AF F) G⁻¹ Z) = Z := by
            funext a
            simp [actTup, Matrix.mulVec_mulVec]
          simpa [Set.mem_preimage, this] using hZ
      rw [himg]
      exact (hbc N 1 hN).image (IsoBox.continuous_actTup (AF F) G⁻¹)
    obtain ⟨C, hC⟩ := GlobalTheory.T.hyperbolic_finite_volume_integral_bound F E σ hCM M₁ J₁ hJ₁ (by omega)
      (GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M₁ J₁ hJ₁) τ hτ μ' 𝓕' hH' hF' _ hΩ
    refine ⟨C, fun r hr => ?_⟩
    have hfun : (fun Y : Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E =>
          Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) G Y)) =
        fun Y => (Set.indicator (actTup (AF F) G ⁻¹' box b N 1) (fun _ => (1 : ℝ≥0∞)))
          (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y) := by
      funext Y
      have hmem : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) ↔
          ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈
            actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) := by
        have h := hsc τ hτ N r (-Real.log r) (actTup (AF F) G Y)
        have h1 : Real.exp (-Real.log r) * r = 1 := by
          rw [Real.exp_neg, Real.exp_log hr]
          exact inv_mul_cancel₀ hr.ne'
        rw [h1] at h
        rw [Set.mem_preimage, IsoBox.actTup_smul]
        exact h.symm
      by_cases hY : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hmem.1 hY)]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (hmem.2 h))]
    have hset := IsoBox.isotropic_preimage σ J g
    rw [← hg] at hset
    rw [hT 1, hset, hfun]
    simpa using hC r hr
  · refine ⟨0, fun r _ => ?_⟩
    have hempty : {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hX hgr
      apply hiso
      refine ⟨X 0, fun h0 => hX ?_, congrFun (congrFun hgr 0) 0⟩
      funext a
      rw [Subsingleton.elim a 0, h0]
      rfl
    simp [cntI, hempty]

end GlobalTheory.CompanionTheory.SW
