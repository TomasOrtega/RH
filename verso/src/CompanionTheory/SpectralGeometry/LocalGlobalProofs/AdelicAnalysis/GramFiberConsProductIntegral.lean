import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord

/- English proof (translation)
Introduce `i j`. Establish `hS` using `S.2 i.succ j.succ`. Establish `ht : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t)`. Simplify using `[sigR, inclR]`. Simplify using `only [schurM, map_sub, map_mul, hinv, ht]`.

Rewrite using `[hS]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schurM_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS := S.2 i.succ j.succ
  have ht : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, ht]
  rw [hS]
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D`. Take `⟨hTR, hLC, hSC, hT2, hAr, hRed, hUR, -⟩` from `D.hR`. Establish `hK` using `GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R`. Take `⟨hKR, -, -, -, hsig, htr, -⟩` from `hK`. Establish `hinv` using `(GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R).2.2.2.1`.

Establish `hopenU` using `GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR`. Establish `hs0 : Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))`. Unfold `s0`. Establish `h1 : Continuous (fun S : HermR R σ (n + 1) => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0)` using `(continuous_apply_apply 0 0).comp continuous_subtype_val`. Conclude with `continuous_const.mul (htr.comp h1)`.

Establish `hA : IsOpen {S : HermR R σ (n + 1) | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}` using `D.hB₀.preimage hs0`. Establish `ha : ContinuousOn (fun S : HermR R σ (n + 1) => a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}` using `D.hac.comp hs0.continuousOn (fun S hS => hS)`. Establish `hleft : Continuous (fun r : R => r ⊗ₜ[F] (1 : E))`. Establish `: (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E)`. Use function extensionality and compare the values at `r`.

Simplify using `[Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']`. Rewrite using `[this]`. Conclude with `(continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))`. Establish `hc : ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}`. Use `continuousOn_pi.2 fun j => ?_` and prove the remaining obligations.

Establish `hent : Continuous (fun S : HermR R σ (n + 1) => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ)` using `(continuous_apply_apply 0 j.succ).comp continuous_subtype_val`. Establish `hu : ContinuousOn (fun S : HermR R σ (n + 1) => ((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}` using `(Units.continuous_val (M := R)).comp_continuousOn ha.inv`. Establish `hfac : (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j) = fun S : HermR R σ (n + 1) => (((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) * ((1 : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) * (S : Matr …`. Use function extensionality and compare the values at `S`. Simplify using `[cvec, Algebra.TensorProduct.tmul_mul_tmul]`.

Rewrite using `[hfac]`. Conclude with `((hleft.comp_continuousOn hu).mul continuousOn_const).mul hent.continuousOn`. Establish `hM : ContinuousOn (fun S : HermR R σ (n + 1) => schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}`. Use `continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_` and prove the remaining obligations. Establish `hent : Continuous (fun S : HermR R σ (n + 1) => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ)` using `(continuous_apply_apply i.succ j.succ).comp continuous_subtype_val`.

Establish `hci` using `(continuous_apply i).comp_continuousOn hc`. Establish `hcj` using `(continuous_apply j).comp_continuousOn hc`. Conclude with `hent.continuousOn.sub (((hsig.comp_continuousOn hci).mul continuousOn_const).mul hcj)`. Establish `hsc : ∀ S : HermR R σ (n + 1), (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))` using `fun S => schur_coe R σ t a S (schurM_mem R σ hinv t a S)`. Establish `hcoe : ContinuousOn (fun S : HermR R σ (n + 1) => (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}`.

Simplify `hM` using `only [hsc]`. Establish `hschur : ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}` using `(Topology.IsInducing.subtypeVal.continuousOn_iff).2 hcoe`. Use `⟨hs0, ha, hc, hschur, ?_⟩` and prove the remaining obligations. Establish `hdet : ContinuousOn (fun S : HermR R σ (n + 1) => (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}` using `(continuous_id.matrix_det).comp_continuousOn hcoe`. Establish `hU : IsOpen {y : R ⊗[F] E | IsUnit y}`.

Establish `: {y : R ⊗[F] E | IsUnit y} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E)`. Use extensionality with `y`. Simplify using `[IsUnit]`. Rewrite using `[this]`. Conclude with `hopenU.isOpen_range`.

Use `hdet.isOpen_inter_preimage hA hU` as an intermediate fact. Conclude with `this`.
-/
theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hUR, -⟩ := D.hR
  have hK := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨hKR, -, -, -, hsig, htr, -⟩ := hK
  have hinv := (GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R).2.2.2.1
  have hopenU := GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR

  have hs0 : Continuous (fun S : HermR R σ (n + 1) =>
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
    unfold s0
    have h1 : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) :=
      (continuous_apply_apply 0 0).comp continuous_subtype_val
    exact continuous_const.mul (htr.comp h1)
  have hA : IsOpen {S : HermR R σ (n + 1) |
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := D.hB₀.preimage hs0
  have ha : ContinuousOn (fun S : HermR R σ (n + 1) =>
      a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    D.hac.comp hs0.continuousOn (fun S hS => hS)

  have hleft : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    have : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [this]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hc : ContinuousOn (fun S : HermR R σ (n + 1) =>
      cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) :=
      (continuous_apply_apply 0 j.succ).comp continuous_subtype_val
    have hu : ContinuousOn (fun S : HermR R σ (n + 1) =>
        ((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R)))
        {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
      (Units.continuous_val (M := R)).comp_continuousOn ha.inv
    have hfac : (fun S : HermR R σ (n + 1) =>
        cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j) =
        fun S : HermR R σ (n + 1) =>
        (((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) *
          ((1 : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) *
          (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      funext S
      simp [cvec, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hfac]
    exact ((hleft.comp_continuousOn hu).mul continuousOn_const).mul hent.continuousOn

  have hM : ContinuousOn (fun S : HermR R σ (n + 1) =>
      schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) :=
      (continuous_apply_apply i.succ j.succ).comp continuous_subtype_val
    have hci := (continuous_apply i).comp_continuousOn hc
    have hcj := (continuous_apply j).comp_continuousOn hc
    exact hent.continuousOn.sub (((hsig.comp_continuousOn hci).mul continuousOn_const).mul hcj)
  have hsc : ∀ S : HermR R σ (n + 1),
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :=
    fun S => schur_coe R σ t a S (schurM_mem R σ hinv t a S)
  have hcoe : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    simpa only [hsc] using hM
  have hschur : ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hcoe
  refine ⟨hs0, ha, hc, hschur, ?_⟩

  have hdet : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (continuous_id.matrix_det).comp_continuousOn hcoe
  have hU : IsOpen {y : R ⊗[F] E | IsUnit y} := by
    have : {y : R ⊗[F] E | IsUnit y} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext y; simp [IsUnit]
    rw [this]
    exact hopenU.isOpen_range
  have := hdet.isOpen_inter_preimage hA hU
  exact this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
