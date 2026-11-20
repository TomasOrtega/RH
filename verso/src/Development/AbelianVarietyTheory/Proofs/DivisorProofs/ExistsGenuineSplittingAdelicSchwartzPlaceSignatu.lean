import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignaturesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicRepExtendingArchimedeanSchwartzRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFiniteStatement

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.GenRepD

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr, mul_add]`.
-/
theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (φ₁ φ₂ : (κ → R) → ℂ) :
    d.rho ψ w (φ₁ + φ₂) = d.rho ψ w φ₁ + d.rho ψ w φ₂ := by
  funext x; simp [Darboux.rho, schr, mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (c : ℂ) (φ : (κ → R) → ℂ) :
    d.rho ψ w (c • φ) = c • d.rho ψ w φ := by
  funext x; simp [Darboux.rho, schr]; ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr]`.
-/
theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) :
    d.rho ψ w 0 = 0 := by
  funext x; simp [Darboux.rho, schr]

open scoped Classical in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ`. Take `⟨ρ, c₀, hR, hcont, hder⟩` from `GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ`. Take `⟨ω₀, hω⟩` from `GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep F κ (UG (cA σ) JB) ρ`. Establish `hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ`. Introduce `g φ hφ`.

Unfold `schA at hφ ⊢`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, h, hh, rfl⟩` from `hx`. Rewrite using `[hω]`.

Conclude with `Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1)` using `fun u _ => by simp`. Establish `hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x` using `fun x => by simp [actB]`. Use `⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ => GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩` and prove the remaining obligations.

Unfold `schA at hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, h, hh, rfl⟩` from `hx`. Take `⟨u, H, hu, hsplit⟩` from `GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w`.

Take `⟨f₁, hf₁⟩` from `GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f`. Establish `e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h)`. Use `hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)` as an intermediate fact. Simplify `this` using `only [hact1]`. Rewrite using `[e1, hω, hω]`.

Conclude with `(hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm`. Consider the case `zero => rw [rho_zero', map_zero, rho_zero']`. Consider the case `add x y _ _ hx hy => rw [rho_add', map_add, map_add, hx, hy, rho_add']`. Consider the case `smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']`. Unfold `schA at hφ`.

Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, h, hh, rfl⟩` from `hx`. Take `⟨T, hT⟩` from `hl h hh`. Establish `e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f)` using `funext fun g => by rw [hω, hT]`.

Rewrite using `[e]`. Conclude with `hcont T f`. Consider the case `zero => simp only [map_zero]`. Conclude with `continuousOn_const`. Consider the case `add x y _ _ hx hy => simp only [map_add]`.

Conclude with `hx.add hy`. Consider the case `smul c x _ hx => simp only [map_smul, smul_eq_mul]`. Conclude with `continuousOn_const.mul hx`. Introduce `γ hγ Y hY T h hh l hl`. Take `⟨L, hL⟩` from `hl h hh`.

Use `show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0`. Simplify using `only [hω, hL]`. Conclude with `hder γ hγ Y hY T L`.
-/
theorem genRepD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsByD τ C ω₀ Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c₀ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ρ, c₀, hR, hcont, hder⟩ := GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ω₀, hω⟩ := GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep F κ (UG (cA σ) JB) ρ
  have hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ := by
    intro g φ hφ
    unfold schA at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      rw [hω]
      exact Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x := fun x => by simp [actB]
  refine ⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ =>
    GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨u, H, hu, hsplit⟩ := GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w
      obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f
      have e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h) := by
        have := hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)
        simpa only [hact1] using this
      rw [e1, hω, hω]
      exact (hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm
    | zero => rw [rho_zero', map_zero, rho_zero']
    | add x y _ _ hx hy => rw [rho_add', map_add, map_add, hx, hy, rho_add']
    | smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨T, hT⟩ := hl h hh
      have e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f) := funext fun g => by rw [hω, hT]
      rw [e]
      exact hcont T f
    | zero => simp only [map_zero]; exact continuousOn_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul, smul_eq_mul]; exact continuousOn_const.mul hx
  · intro γ hγ Y hY T h hh l hl
    obtain ⟨L, hL⟩ := hl h hh
    show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0
    simp only [hω, hL]
    exact hder γ hγ Y hY T L

end GlobalTheory.GenRepD

end
