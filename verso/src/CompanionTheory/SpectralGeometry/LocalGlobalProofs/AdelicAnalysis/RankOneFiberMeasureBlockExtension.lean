import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousAction

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

/- English proof (translation)
Take `⟨C, hC, hC0⟩` from `exists_compact_mem_nhds (0 : V)`. Establish `h1 : μ C ≠ ⊤` using `hC.measure_lt_top.ne`. Establish `h2 : μ C ≠ 0` using `(Measure.measure_pos_of_mem_nhds μ hC0).ne'`. Establish `h3 : (c : ℝ≥0∞) * μ C = (e : ℝ≥0∞) * μ C`. Establish `h' : (c • μ) C = (e • μ) C` using `by rw [h]`.

Rewrite `h'` using `[Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]`. Then use the resulting hypothesis. Establish `h4` using `(ENNReal.mul_left_inj h2 h1).1 h3`. Conclude with `h4` after adjusting the coercions.
-/
theorem nnreal_eq_of_smul_haar {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {c e : ℝ≥0} (h : c • μ = e • μ) : c = e := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  have h1 : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have h2 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC0).ne'
  have h3 : (c : ℝ≥0∞) * μ C = (e : ℝ≥0∞) * μ C := by
    have h' : (c • μ) C = (e • μ) C := by rw [h]
    rwa [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul] at h'
  have h4 := (ENNReal.mul_left_inj h2 h1).1 h3
  exact_mod_cast h4

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sclMat : R →* Matrix (Fin 1) (Fin 1) (R ⊗[F] E) where
  toFun u := Matrix.of fun _ _ => u ⊗ₜ[F] (1 : E)
  map_one' := by
    ext i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    rw [Matrix.one_apply_eq]
    rfl
  map_mul' u v := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sclMat_apply (u : R) (i j : Fin 1) :
    sclMat (F := F) (E := E) R u i j = u ⊗ₜ[F] (1 : E) := rfl

def unitTens : Rˣ →* (R ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E).toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitTens_coe (u : Rˣ) :
    ((unitTens (F := F) (E := E) R u : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (u : R) ⊗ₜ[F] (1 : E) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Establish `ha : a = 0` using `Subsingleton.elim _ _`. Substitute `ha` using the available equality. Simplify using `only [rmul, scl, Fin.sum_univ_one, sclMat_apply]`.
-/
theorem rmul_sclMat {M : ℕ} (X : Fin 1 → Fin M → R ⊗[F] E) (u : R) :
    rmul R X (sclMat (F := F) (E := E) R u) = scl (u ⊗ₜ[F] (1 : E)) X := by
  funext a i
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  simp only [rmul, scl, Fin.sum_univ_one, sclMat_apply]

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E)` using `by simp [sigR]`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, sclMat_apply, h1]`. Express the relevant statement in the definitionally equal form `(u ^ 2 * s) ⊗ₜ[F] (1 : E) = u ⊗ₜ[F] (1 : E) * s ⊗ₜ[F] (1 : E) * u ⊗ₜ[F] (1 : E)`.

Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cT_sclMat_mul (σ : E →ₐ[F] E) (u s : R) :
    ((hermScal R σ (u ^ 2 * s) : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) (sclMat (F := F) (E := E) R u) *
        ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        sclMat (F := F) (E := E) R u := by
  ext i j
  have h1 : sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E) := by simp [sigR]
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, sclMat_apply, h1]
  change (u ^ 2 * s) ⊗ₜ[F] (1 : E) = u ⊗ₜ[F] (1 : E) * s ⊗ₜ[F] (1 : E) * u ⊗ₜ[F] (1 : E)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  ring

end Alg

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM N J₁ hJ t ht R _ _ _ _ _ hR d b lam hlam m₁ hm₁`. Establish `hR0` using `hR`. Take `⟨i1, i2, i3, i4, -⟩` from `hR0`. Use `haveI := i1`. Use `haveI := i2`.

Use `haveI := i3`. Use `haveI := i4`. Take `⟨k1, k2, k3, k4, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R`. Use `haveI := k1`. Use `haveI := k2`.

Use `haveI := k3`. Use `haveI := k4`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Take `⟨hK, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam`.

Use `haveI := hK`. Take `⟨κ, hκc, -, hκ1, hκ⟩` from `GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hCM N J₁ hJ R hR 1 _ _ m₁ (hW 1 N) (hH 1) hm₁`. Establish `hinc : Continuous (fun r : R => r ⊗ₜ[F] (1 : E))` using `by haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)`. Establish `h : Continuous (fun r : R => r • (1 : R ⊗[F] E))` using `Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id continuous_const`. Use `h.congr fun r => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hcs : Continuous (sclMat (F` using `F) (E := E) R) := continuous_pi fun _ => continuous_pi fun _ => hinc`. Establish `hg : Continuous (Units.map (sclMat (F` using `F) (E := E) R)) := Continuous.units_map _ hcs`. Establish `hu : Continuous (unitTens (F` using `F) (E := E) R) := Continuous.units_map _ hinc`. Take `⟨χ, hχc, hχ⟩` from `exists_continuous_modulus_of_continuous_action (R ⊗[F] E) (coordK R b lam) (R ⊗[F] E)ˣ`.

Set `tU : (R ⊗[F] E)ˣ` to `Units.map (inclR R : E →+* R ⊗[F] E).toMonoidHom (Units.mk0 (algebraMap F E t) ((map_ne_zero _).2 ht))`. Establish `htU : (tU : R ⊗[F] E) = inclR R (algebraMap F E t)` using `rfl`. Establish `hq : ∀ u : Rˣ, ((unitTens (F` using `F) (E := E) R u * tU : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (u : R) ⊗ₜ[F] (algebraMap F E t) := by`. Introduce `u`. Rewrite using `[Units.val_mul, unitTens_coe, htU]`.

Express the relevant statement in the definitionally equal form `(u : R) ⊗ₜ[F] (1 : E) * (1 : R) ⊗ₜ[F] (algebraMap F E t) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Use `⟨fun u => κ (Units.map (sclMat (F := F) (E := E) R) u), fun u => χ (unitTens (F := F) (E := E) R u * tU), hκc.comp hg, by simpa using hκ1, ?_, hχc.comp (hu.mul continuous_const), ?_, ?_⟩` and prove the remaining obligations. Introduce `u`. Establish `h` using `hκ (Units.map (sclMat (F := F) (E := E) R) u) (hermScal R σ (algebraMap F R t)) (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) (cT_sclMat_mul R σ (u : R) _)`.

Rewrite using `[h]`. Use `congr 2`. Use function extensionality and compare the values at `X`. Conclude with `rmul_sclMat R X (u : R)`. Introduce `u`.

Establish `e : (fun y : R ⊗[F] E => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = fun v => (unitTens (F` using `F) (E := E) R u * tU) • v := by`. Use function extensionality and compare the values at `y`. Rewrite using `[Units.smul_def, smul_eq_mul, hq]`. Rewrite using `[e]`. Conclude with `hχ _`.

Introduce `c hc`. Establish `e : (fun y : R ⊗[F] E => inclR R (algebraMap F E t) * y) = fun v => tU • v`. Use function extensionality and compare the values at `y`. Rewrite using `[Units.smul_def, smul_eq_mul, htU]`. Rewrite `hc` using `[e, hχ tU]`.

Use `nnreal_eq_of_smul_haar (coordK R b lam) hc` as an intermediate fact. Simplify using `using this`.
-/
theorem fibre_scale_modulus_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  intro F E _ _ _ _ _ σ hCM N J₁ hJ t ht R _ _ _ _ _ hR d b lam hlam m₁ hm₁
  have hR0 := hR
  obtain ⟨i1, i2, i3, i4, -⟩ := hR0
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  obtain ⟨k1, k2, k3, k4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  haveI := hK
  obtain ⟨κ, hκc, -, hκ1, hκ⟩ :=
    GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hCM N J₁ hJ R hR 1 _ _ m₁ (hW 1 N) (hH 1) hm₁
  have hinc : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have h : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id
        continuous_const
    refine h.congr fun r => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcs : Continuous (sclMat (F := F) (E := E) R) :=
    continuous_pi fun _ => continuous_pi fun _ => hinc
  have hg : Continuous (Units.map (sclMat (F := F) (E := E) R)) := Continuous.units_map _ hcs
  have hu : Continuous (unitTens (F := F) (E := E) R) := Continuous.units_map _ hinc
  obtain ⟨χ, hχc, hχ⟩ := exists_continuous_modulus_of_continuous_action (R ⊗[F] E) (coordK R b lam)
    (R ⊗[F] E)ˣ
  let tU : (R ⊗[F] E)ˣ :=
    Units.map (inclR R : E →+* R ⊗[F] E).toMonoidHom
      (Units.mk0 (algebraMap F E t) ((map_ne_zero _).2 ht))
  have htU : (tU : R ⊗[F] E) = inclR R (algebraMap F E t) := rfl
  have hq : ∀ u : Rˣ, ((unitTens (F := F) (E := E) R u * tU : (R ⊗[F] E)ˣ) : R ⊗[F] E) =
      (u : R) ⊗ₜ[F] (algebraMap F E t) := by
    intro u
    rw [Units.val_mul, unitTens_coe, htU]
    change (u : R) ⊗ₜ[F] (1 : E) * (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨fun u => κ (Units.map (sclMat (F := F) (E := E) R) u),
    fun u => χ (unitTens (F := F) (E := E) R u * tU), hκc.comp hg, by simpa using hκ1, ?_,
    hχc.comp (hu.mul continuous_const), ?_, ?_⟩
  · intro u
    have h := hκ (Units.map (sclMat (F := F) (E := E) R) u) (hermScal R σ (algebraMap F R t))
      (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) (cT_sclMat_mul R σ (u : R) _)
    rw [h]
    congr 2
    funext X
    exact rmul_sclMat R X (u : R)
  · intro u
    have e : (fun y : R ⊗[F] E => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        fun v => (unitTens (F := F) (E := E) R u * tU) • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, hq]
    rw [e]
    exact hχ _
  · intro c hc
    have e : (fun y : R ⊗[F] E => inclR R (algebraMap F E t) * y) = fun v => tU • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, htU]
    rw [e, hχ tU] at hc
    have := nnreal_eq_of_smul_haar (coordK R b lam) hc
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
