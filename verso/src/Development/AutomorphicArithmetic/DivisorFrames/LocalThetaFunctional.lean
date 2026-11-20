import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `φ hφ h`. Establish `h0 : ι φ = ι 0`. Rewrite using `[map_zero]`.

Use function extensionality and compare the values at `y`. Assume the negation of the conclusion as `hy`. Simplify using `using h y hy`. Rewrite using `[hι.injOn hφ N.zero_mem h0, map_zero]`. Consider the case `insert s T _ ih`.

Introduce `φ hφ h`. Establish `hf : ι φ ∈ SB Y` using `hι.mapsTo hφ`. Establish `hg : (fun y => (χ s y - 1)⁻¹ * ι φ y) ∈ SB Y` using `⟨((hχ s).comp fun z => (z - 1)⁻¹).mul hf.1, hf.2.mul_left⟩`. Take `⟨g, hgN, hge⟩` from `hι.surjOn hg`. Take `⟨g₁, hg₁, e1, e2⟩` from `hL s g hgN`.

Use `ih (φ - (g₁ - g)) (N.sub_mem hφ (N.sub_mem hg₁ hgN)) fun y hy => by` as an intermediate fact. Simplify using `only [map_sub, Pi.sub_apply, e2, hge] at hy`. Distinguish the cases in `hs : χ s y = 1`. Establish `hy' : ι φ y ≠ 0` using `by simpa [hs] using hy`. Take `⟨s', hs', h'⟩` from `h y hy'`.

Break down `Finset.mem_insert.1 hs' with rfl | hs'` into its components or cases. Conclude with `absurd hs h'`. Conclude with `⟨s', hs', h'⟩`. It suffices to derive a contradiction. Use `sub_ne_zero.2 hs` as an intermediate fact.

Apply `hy` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify `this` using `[map_sub, e1]`.
-/
private theorem kill_fin {V Y S : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace Y] (N : Submodule ℂ V)
    (ι : V →ₗ[ℂ] (Y → ℂ)) (hι : Set.BijOn ι (N : Set V) (SB Y : Set _)) (L : V →ₗ[ℂ] ℂ) (χ : S → Y → ℂ)
    (hχ : ∀ s, IsLocallyConstant (χ s))
    (hL : ∀ s, ∀ φ ∈ N, ∃ φ₁ ∈ N, L φ₁ = L φ ∧ ∀ y, ι φ₁ y = χ s y * ι φ y) (T : Finset S) :
    ∀ φ ∈ N, (∀ y, ι φ y ≠ 0 → ∃ s ∈ T, χ s y ≠ 1) → L φ = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφ h
    have h0 : ι φ = ι 0 := by
      rw [map_zero]; funext y; by_contra hy; simpa using h y hy
    rw [hι.injOn hφ N.zero_mem h0, map_zero]
  | insert s T _ ih =>
    intro φ hφ h
    have hf : ι φ ∈ SB Y := hι.mapsTo hφ
    have hg : (fun y => (χ s y - 1)⁻¹ * ι φ y) ∈ SB Y :=
      ⟨((hχ s).comp fun z => (z - 1)⁻¹).mul hf.1, hf.2.mul_left⟩
    obtain ⟨g, hgN, hge⟩ := hι.surjOn hg
    obtain ⟨g₁, hg₁, e1, e2⟩ := hL s g hgN
    have := ih (φ - (g₁ - g)) (N.sub_mem hφ (N.sub_mem hg₁ hgN)) fun y hy => by
      simp only [map_sub, Pi.sub_apply, e2, hge] at hy
      by_cases hs : χ s y = 1
      · have hy' : ι φ y ≠ 0 := by simpa [hs] using hy
        obtain ⟨s', hs', h'⟩ := h y hy'
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd hs h'
        · exact ⟨s', hs', h'⟩
      · exfalso
        have := sub_ne_zero.2 hs
        apply hy
        field_simp
        ring
    simpa [map_sub, e1] using this

/- English proof (translation)
Introduce `φ hφ h`. Establish `hf : ι φ ∈ SB Y` using `hι.mapsTo hφ`. Establish `hcl : IsClosed (Function.support (ι φ))` using `((IsLocallyConstant.iff_isOpen_fiber.1 hf.1 0).isClosed_compl)`. Establish `hc : IsCompact (Function.support (ι φ))` using `hf.2.isCompact.of_isClosed_subset hcl (subset_tsupport _)`. Take `⟨T, hT⟩` from `hc.elim_finite_subcover (fun s => {y | χ s y ≠ 1}) (fun s => hχ s {z | z ≠ 1}) (fun y hy => Set.mem_iUnion.2 (h y hy))`.

Use `kill_fin N ι hι L χ hχ hL T φ hφ fun y hy => ?_` and prove the remaining obligations. Simplify using `using hT hy`.
-/
private theorem kill {V Y S : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace Y] (N : Submodule ℂ V)
    (ι : V →ₗ[ℂ] (Y → ℂ)) (hι : Set.BijOn ι (N : Set V) (SB Y : Set _)) (L : V →ₗ[ℂ] ℂ) (χ : S → Y → ℂ)
    (hχ : ∀ s, IsLocallyConstant (χ s))
    (hL : ∀ s, ∀ φ ∈ N, ∃ φ₁ ∈ N, L φ₁ = L φ ∧ ∀ y, ι φ₁ y = χ s y * ι φ y) :
    ∀ φ ∈ N, (∀ y, ι φ y ≠ 0 → ∃ s, χ s y ≠ 1) → L φ = 0 := by
  intro φ hφ h
  have hf : ι φ ∈ SB Y := hι.mapsTo hφ
  have hcl : IsClosed (Function.support (ι φ)) := ((IsLocallyConstant.iff_isOpen_fiber.1 hf.1 0).isClosed_compl)
  have hc : IsCompact (Function.support (ι φ)) := hf.2.isCompact.of_isClosed_subset hcl (subset_tsupport _)
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun s => {y | χ s y ≠ 1}) (fun s => hχ s {z | z ≠ 1})
    (fun y hy => Set.mem_iUnion.2 (h y hy))
  refine kill_fin N ι hι L χ hχ hL T φ hφ fun y hy => ?_
  simpa using hT hy

/- English proof (translation)
Simplify using `only [Matrix.vecMul, dotProduct]`. Use `fun_prop`.
-/
private theorem cont_pair {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n d : ℕ} (p : Fin n → K)
    (q : Fin d → K) : Continuous fun Y : Matrix (Fin n) (Fin d) K => -((p ᵥ* Y) ⬝ᵥ q) := by
  simp only [Matrix.vecMul, dotProduct]
  fun_prop

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW x₀ hx₀ v t L hL φ hφ`. Take `⟨hφ, ι, hι, hsupp⟩` from `hφ`. Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.continuous_psiAt _ hB.std.1 v`. Establish `hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1` using `GlobalTheory.PsiNontriv.psiAt_ne_one _ hB.std v`. Establish `hlc : IsLocallyConstant (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.isLocallyConstant_addChar _ hψc`.

Establish `hinc : ∀ (τ : E →ₐ[F] Fv F v) (x : E), piW τ (inclR (F` using `F) (AF F) x) = τ x := fun τ x => by`. Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x`. Simplify using `[compFin]`. Use `kill (S := Fin d → Fv F v) (SB _) ι (Model.IsLin.bij hι) L (fun q Y => GlobalTheory.LatVac.psiAt B.ψ v (-(((fun i => t (x₀ i)) ᵥ* Y) ⬝ᵥ q))) (fun q => ?_) (fun q f hf => ?_) φ hφ (fun Y hY => ?_)` and prove the remaining obligations. Conclude with `hlc.comp_continuous (cont_pair (fun i => t (x₀ i)) q)`.

Take `⟨u, hu, h0, h1⟩` from `GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (Matrix.of fun i (_ : Unit) => q i) 0`. Establish `hat : At (evFin F v) (Matrix.vecMulVec (incV F x₀) fun j => u j ())`. Introduce `a ha`. Use extensionality with `i j`. Use `congrFun (congrFun (hu a ha) j) ()` as an intermediate fact.

Simplify using `only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply] at this ⊢`. Rewrite using `[← mul_smul_comm, this, mul_zero]`. Establish `hsb` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v (GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incV F x₀) fun j => u j ())) f hf`. Establish `hact` using `GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat f`. Establish `y0 : GlobalTheory.FlipMatch.coY σ X W t 1 1 (Matrix.vecMulVec (incV F x₀) fun j => u j ()) = 0`.

Establish `: (Matrix.vecMulVec (incV F x₀) fun j => u j ()).map (piW (t.comp σ)) = 0`. Use extensionality with `i j`. Use `congrFun (congrFun h1 j) ()` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at this`. Simplify using `[Matrix.vecMulVec_apply, this]`.

Simplify using `[GlobalTheory.FlipMatch.coY, this]`. Establish `x0 : GlobalTheory.FlipMatch.coX t 1 1 (Matrix.vecMulVec (incV F x₀) fun j => u j ()) = Matrix.vecMulVec (fun i => t (x₀ i)) q`. Use extensionality with `i j`. Use `congrFun (congrFun h0 j) ()` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.of_apply] at this`.

Simplify using `only [GlobalTheory.FlipMatch.coX, inv_one, Units.val_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, this]`. Rewrite using `[← hinc t]`. Both sides reduce to the same expression. Use `⟨_, hsb, hL _ hat f hf _ hsb hact, fun Y => ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hB.cm X W hX.herm hW.skew (GlobalTheory.FinUniq.det_ne_zero_herm hX) (GlobalTheory.FinUniq.det_ne_zero_skew hW) M B.ψ hB.std t 1 1 _ hat (by simp [y0, GlobalTheory.FlipMatch.pairM]) f hf _ hsb hact).2 ι hι Y, y0 …`.

Use `congr 3`. Simplify using `only [GlobalTheory.FlipMatch.pairM, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Establish `hr : Y.rank = n` using `by by_contra h; exact hY (hsupp Y h)`.

Establish `hli : LinearIndependent (Fv F v) Y.row`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hr]`. Establish `hne : (fun i => t (x₀ i)) ᵥ* Y ≠ 0`. Introduce `h`. Establish `h2` using `Matrix.vecMul_injective_iff.2 hli (h.trans (Matrix.zero_vecMul Y).symm)`.

Conclude with `hx₀ (funext fun i => (t : E →+* Fv F v).injective (by simpa using congrFun h2 i))`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hne`. Take `⟨a, ha⟩` from `AddChar.ne_one_iff.1 hψ1`. Use `⟨Pi.single j (-(a / ((fun i => t (x₀ i)) ᵥ* Y) j)), ?_⟩` and prove the remaining obligations. Establish `hj' : ((fun i => t (x₀ i)) ᵥ* Y) j ≠ 0` using `hj`.

Rewrite using `[dotProduct_single, mul_neg, neg_neg, mul_div_cancel₀ _ hj']`. Conclude with `ha`.
-/
theorem UpperTheory.local_theta_functional :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
        B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ x₀ : Fin n → E, x₀ ≠ 0 → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
        (L : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
        (∀ z : Fin d → AE F E, At (evFin F v) (Matrix.vecMulVec (incV F x₀) z) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ (Matrix.vecMulVec (incV F x₀) z)) φ φ₁ → L φ₁ = L φ) →
        ∀ φ ∈ M.SoLoc B.ψ t, L φ = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW x₀ hx₀ v t L hL φ hφ
  obtain ⟨hφ, ι, hι, hsupp⟩ := hφ
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hB.std v
  have hlc : IsLocallyConstant (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.isLocallyConstant_addChar _ hψc
  have hinc : ∀ (τ : E →ₐ[F] Fv F v) (x : E), piW τ (inclR (F := F) (AF F) x) = τ x := fun τ x => by
    change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
    simp [compFin]
  refine kill (S := Fin d → Fv F v) (SB _) ι (Model.IsLin.bij hι) L
    (fun q Y => GlobalTheory.LatVac.psiAt B.ψ v (-(((fun i => t (x₀ i)) ᵥ* Y) ⬝ᵥ q))) (fun q => ?_) (fun q f hf => ?_) φ hφ
    (fun Y hY => ?_)
  · exact hlc.comp_continuous (cont_pair (fun i => t (x₀ i)) q)
  · obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (Matrix.of fun i (_ : Unit) => q i) 0
    have hat : At (evFin F v) (Matrix.vecMulVec (incV F x₀) fun j => u j ()) := by
      intro a ha
      ext i j
      have := congrFun (congrFun (hu a ha) j) ()
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply] at this ⊢
      rw [← mul_smul_comm, this, mul_zero]
    have hsb := GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v
      (GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incV F x₀) fun j => u j ())) f hf
    have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat f
    have y0 : GlobalTheory.FlipMatch.coY σ X W t 1 1 (Matrix.vecMulVec (incV F x₀) fun j => u j ()) = 0 := by
      have : (Matrix.vecMulVec (incV F x₀) fun j => u j ()).map (piW (t.comp σ)) = 0 := by
        ext i j
        have := congrFun (congrFun h1 j) ()
        simp only [Matrix.map_apply, Matrix.zero_apply] at this
        simp [Matrix.vecMulVec_apply, this]
      simp [GlobalTheory.FlipMatch.coY, this]
    have x0 : GlobalTheory.FlipMatch.coX t 1 1 (Matrix.vecMulVec (incV F x₀) fun j => u j ()) =
        Matrix.vecMulVec (fun i => t (x₀ i)) q := by
      ext i j
      have := congrFun (congrFun h0 j) ()
      simp only [Matrix.map_apply, Matrix.of_apply] at this
      simp only [GlobalTheory.FlipMatch.coX, inv_one, Units.val_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
        Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, this]
      rw [← hinc t]; rfl
    refine ⟨_, hsb, hL _ hat f hf _ hsb hact, fun Y => ?_⟩
    rw [(GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hB.cm X W hX.herm hW.skew (GlobalTheory.FinUniq.det_ne_zero_herm hX)
      (GlobalTheory.FinUniq.det_ne_zero_skew hW) M B.ψ hB.std t 1 1 _ hat (by simp [y0, GlobalTheory.FlipMatch.pairM]) f hf _ hsb hact).2
      ι hι Y, y0, add_zero, x0, GlobalTheory.LatVac.psiAt_apply]
    congr 3
    simp only [GlobalTheory.FlipMatch.pairM, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · have hr : Y.rank = n := by by_contra h; exact hY (hsupp Y h)
    have hli : LinearIndependent (Fv F v) Y.row := by
      rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hr]
    have hne : (fun i => t (x₀ i)) ᵥ* Y ≠ 0 := by
      intro h
      have h2 := Matrix.vecMul_injective_iff.2 hli (h.trans (Matrix.zero_vecMul Y).symm)
      exact hx₀ (funext fun i => (t : E →+* Fv F v).injective (by simpa using congrFun h2 i))
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 hψ1
    refine ⟨Pi.single j (-(a / ((fun i => t (x₀ i)) ᵥ* Y) j)), ?_⟩
    have hj' : ((fun i => t (x₀ i)) ᵥ* Y) j ≠ 0 := hj
    rw [dotProduct_single, mul_neg, neg_neg, mul_div_cancel₀ _ hj']
    exact ha
