import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.DxN

section Gen

open MeasureTheory
open scoped Matrix Kronecker

/- English proof (translation)
Use `symm`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[(MeasurableEquiv.curry A B R).symm.map_apply]`. Establish `hpre : (MeasurableEquiv.curry A B R).symm ⁻¹' Set.pi Set.univ s = Set.pi Set.univ fun i : A => Set.pi Set.univ fun k : B => s (i, k)`. Use extensionality with `x`.

Simplify using `[MeasurableEquiv.curry, Set.mem_pi, Prod.forall, Function.uncurry]`. Rewrite using `[hpre, Measure.pi_pi]`. Repeatedly rewrite using `[Measure.pi_pi]`. Rewrite using `[Fintype.prod_prod_type]`.
-/
theorem map_curry_symm_pi_fintype {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    (Measure.pi fun _ : A => Measure.pi fun _ : B => lam).map (MeasurableEquiv.curry A B R).symm =
      Measure.pi fun _ : A × B => lam := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.curry A B R).symm.map_apply]
  have hpre : (MeasurableEquiv.curry A B R).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i : A => Set.pi Set.univ fun k : B => s (i, k) := by
    ext x
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall, Function.uncurry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.map_apply, Matrix.kroneckerMap_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules.

Introduce `a' _ h`. Simplify using `[Matrix.one_apply_ne (Ne.symm h)]`. Simplify using the standard rewrite rules.
-/
theorem dot_kronecker {K R A ι : Type} [CommRing K] [CommRing R] [Fintype A] [DecidableEq A] [Fintype ι]
    (f : K →+* R) (T : Matrix ι ι K) (u v : A × ι → R) :
    u ⬝ᵥ (((1 : Matrix A A K) ⊗ₖ T).map f *ᵥ v) =
      ∑ a, (fun p => u (a, p)) ⬝ᵥ (T.map f *ᵥ fun p => v (a, p)) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.map_apply,
    Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ h
    simp [Matrix.one_apply_ne (Ne.symm h)]
  · simp

end Gen

section Coord

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open scoped TensorProduct ENNReal NNReal Matrix

def cvN {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → R ⊗[F] E) : Fin n × (Fin M × Fin d) → R :=
  fun p => cv R b (X p.1) p.2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hh, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI := hlam`. Establish `hSF : SigmaFinite lam` using `inferInstance`. Set `e : R ⊗[F] E ≃ₜ (Fin d → R)` to `(hh d b).homeomorph _`.

Set `em : R ⊗[F] E ≃ᵐ (Fin d → R)` to `e.toMeasurableEquiv`. Establish `hem : ∀ y k, em y k = (Algebra.TensorProduct.basis R b).repr y k` using `fun _ _ => rfl`. Establish `hK : coordK R b lam = (Measure.pi fun _ => lam).map em.symm` using `coordK_eq_map b lam em hem`. Use `haveI : SigmaFinite (coordK R b lam) := by`. Rewrite using `[hK]`.

Conclude with `em.symm.measurableEmbedding.sigmaFinite_map`. Establish `hmp : MeasurePreserving em (coordK R b lam) (Measure.pi fun _ : Fin d => lam)` using `⟨em.measurable, by rw [hK]; exact MeasurableEquiv.map_map_symm em⟩`. Set `c1 : (Fin M → R ⊗[F] E) ≃ᵐ (Fin M × Fin d → R)` to `(MeasurableEquiv.piCongrRight fun _ : Fin M => em).trans (MeasurableEquiv.curry (Fin M) (Fin d) R).symm`. Set `Φ : (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × (Fin M × Fin d) → R)` to `(MeasurableEquiv.piCongrRight fun _ : Fin n => c1).trans (MeasurableEquiv.curry (Fin n) (Fin M × Fin d) R).symm`. Establish `hΦ : (cvN R b : (Fin n → Fin M → R ⊗[F] E) → _) = Φ` using `rfl`.

Establish `hsymm : (Φ.symm : (Fin n × (Fin M × Fin d) → R) → Fin n → Fin M → R ⊗[F] E) = fun x a i => e.symm fun k => x (a, (i, k))` using `rfl`. Establish `hc1 : Continuous (Φ : (Fin n → Fin M → R ⊗[F] E) → Fin n × (Fin M × Fin d) → R)`. Rewrite using `[← hΦ]`. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Conclude with `(continuous_apply p.2.2).comp (e.continuous.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))`.

Establish `hc2 : Continuous (Φ.symm : (Fin n × (Fin M × Fin d) → R) → Fin n → Fin M → R ⊗[F] E)`. Rewrite using `[hsymm]`. Use `continuous_pi fun _ => continuous_pi fun i => e.symm.continuous.comp ?_` and prove the remaining obligations. Conclude with `continuous_pi fun k => continuous_apply _`. Set `Ψ : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → R)` to `{ Φ.toEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }`.

Use `⟨Ψ.isHomeomorph, ?_⟩` and prove the remaining obligations. Establish `s1 : MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin d) R).symm (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (Measure.pi fun _ : Fin M × Fin d => lam)` using `⟨(MeasurableEquiv.curry (Fin M) (Fin d) R).symm.measurable, map_curry_symm_pi_fintype lam _ _⟩`. Establish `s2` using `measurePreserving_pi (fun _ : Fin M => coordK R b lam) (fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (fun _ => hmp)`. Establish `s3 : MeasurePreserving c1 (Measure.pi fun _ : Fin M => coordK R b lam) (Measure.pi fun _ : Fin M × Fin d => lam)` using `s1.comp s2`. Establish `s4` using `measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin M => coordK R b lam) (fun _ : Fin n => Measure.pi fun _ : Fin M × Fin d => lam) (fun _ => s3)`.

Establish `s5 : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin M × Fin d) R).symm (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M × Fin d => lam) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lam)` using `⟨(MeasurableEquiv.curry (Fin n) (Fin M × Fin d) R).symm.measurable, map_curry_symm_pi_fintype lam _ _⟩`. Conclude with `(s5.comp s4).map_eq`.
-/
theorem coordMapN (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
    [BorelSpace R] {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (n M : ℕ) :
    IsHomeomorph (cvN R b : (Fin n → Fin M → R ⊗[F] E) → _) ∧
      (coordW R b lam n M).map (cvN R b) = Measure.pi fun _ : Fin n × (Fin M × Fin d) => lam := by
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hlam
  have hSF : SigmaFinite lam := inferInstance
  let e : R ⊗[F] E ≃ₜ (Fin d → R) := (hh d b).homeomorph _
  let em : R ⊗[F] E ≃ᵐ (Fin d → R) := e.toMeasurableEquiv
  have hem : ∀ y k, em y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  have hK : coordK R b lam = (Measure.pi fun _ => lam).map em.symm := coordK_eq_map b lam em hem
  haveI : SigmaFinite (coordK R b lam) := by
    rw [hK]; exact em.symm.measurableEmbedding.sigmaFinite_map
  have hmp : MeasurePreserving em (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨em.measurable, by rw [hK]; exact MeasurableEquiv.map_map_symm em⟩
  let c1 : (Fin M → R ⊗[F] E) ≃ᵐ (Fin M × Fin d → R) :=
    (MeasurableEquiv.piCongrRight fun _ : Fin M => em).trans (MeasurableEquiv.curry (Fin M) (Fin d) R).symm
  let Φ : (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × (Fin M × Fin d) → R) :=
    (MeasurableEquiv.piCongrRight fun _ : Fin n => c1).trans
      (MeasurableEquiv.curry (Fin n) (Fin M × Fin d) R).symm
  have hΦ : (cvN R b : (Fin n → Fin M → R ⊗[F] E) → _) = Φ := rfl
  have hsymm : (Φ.symm : (Fin n × (Fin M × Fin d) → R) → Fin n → Fin M → R ⊗[F] E) =
      fun x a i => e.symm fun k => x (a, (i, k)) := rfl
  have hc1 : Continuous (Φ : (Fin n → Fin M → R ⊗[F] E) → Fin n × (Fin M × Fin d) → R) := by
    rw [← hΦ]
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2.2).comp
      (e.continuous.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))
  have hc2 : Continuous (Φ.symm : (Fin n × (Fin M × Fin d) → R) → Fin n → Fin M → R ⊗[F] E) := by
    rw [hsymm]
    refine continuous_pi fun _ => continuous_pi fun i => e.symm.continuous.comp ?_
    exact continuous_pi fun k => continuous_apply _
  let Ψ : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → R) :=
    { Φ.toEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
  refine ⟨Ψ.isHomeomorph, ?_⟩
  have s1 : MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin d) R).symm
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (Measure.pi fun _ : Fin M × Fin d => lam) :=
    ⟨(MeasurableEquiv.curry (Fin M) (Fin d) R).symm.measurable, map_curry_symm_pi_fintype lam _ _⟩
  have s2 := measurePreserving_pi (fun _ : Fin M => coordK R b lam)
    (fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (fun _ => hmp)
  have s3 : MeasurePreserving c1 (Measure.pi fun _ : Fin M => coordK R b lam)
      (Measure.pi fun _ : Fin M × Fin d => lam) := s1.comp s2
  have s4 := measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin M => coordK R b lam)
    (fun _ : Fin n => Measure.pi fun _ : Fin M × Fin d => lam) (fun _ => s3)
  have s5 : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin M × Fin d) R).symm
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M × Fin d => lam)
      (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lam) :=
    ⟨(MeasurableEquiv.curry (Fin n) (Fin M × Fin d) R).symm.measurable, map_curry_symm_pi_fintype lam _ _⟩
  exact (s5.comp s4).map_eq

end Coord

section Link
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.CoordMat
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing Kronecker
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def gramN (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (n : ℕ) :
    Matrix (Fin n × (Fin M × Fin d)) (Fin n × (Fin M × Fin d)) F :=
  (1 : Matrix (Fin n) (Fin n) F) ⊗ₖ traceGram σ J b

/- English proof (translation)
Establish `hr` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M`. Take `⟨h1, -⟩` from `coordMapN σ hCM (AF F) b (adeleMeasure F) inferInstance n M`. Conclude with `⟨h1.homeomorph, fun _ => rfl, hr⟩`.
-/
theorem exists_coordHomeoN (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F),
      (∀ X, e X = cvN (AF F) b X) ∧ BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  have hr := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  obtain ⟨h1, -⟩ := coordMapN σ hCM (AF F) b (adeleMeasure F) inferInstance n M
  exact ⟨h1.homeomorph, fun _ => rfl, hr⟩

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Establish `h1 : BR (AF F) σ J X Y = cvN (AF F) b X ⬝ᵥ (gramN σ J b n).map (algebraMap F (AF F)) *ᵥ cvN (AF F) b Y`. Rewrite using `[gramN, dot_kronecker (algebraMap F (AF F))]`. Conclude with `Finset.sum_congr rfl fun a _ => trace_hR (AF F) σ J b (X a) (Y a)`. Establish `h2 : (ξ • gramN σ J b n).map (algebraMap F (AF F)) = algebraMap F (AF F) ξ • (gramN σ J b n).map (algebraMap F (AF F))`.

Use extensionality with `p q`. Conclude with `map_mul (algebraMap F (AF F)) ξ (gramN σ J b n p q)`. Rewrite using `[hξ, h1, chiG, h2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`.
-/
theorem psi_BRN (σ : E →ₐ[F] E) {M d n : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (ψ : AddChar (AF F) ℂ) (ξ : F)
    (hξ : ∀ x : AF F, ψ x = ((adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ))
    (X Y : Fin n → Fin M → AF F ⊗[F] E) :
    ψ (BR (AF F) σ J X Y) = chiG (ξ • gramN σ J b n) (cvN (AF F) b X) (cvN (AF F) b Y) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : BR (AF F) σ J X Y = cvN (AF F) b X ⬝ᵥ
      (gramN σ J b n).map (algebraMap F (AF F)) *ᵥ cvN (AF F) b Y := by
    rw [gramN, dot_kronecker (algebraMap F (AF F))]
    exact Finset.sum_congr rfl fun a _ => trace_hR (AF F) σ J b (X a) (Y a)
  have h2 : (ξ • gramN σ J b n).map (algebraMap F (AF F)) =
      algebraMap F (AF F) ξ • (gramN σ J b n).map (algebraMap F (AF F)) := by
    ext p q
    exact map_mul (algebraMap F (AF F)) ξ (gramN σ J b n p q)
  rw [hξ, h1, chiG, h2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Establish `hσ : ∀ x, σ (σ x) = x` using `GlobalTheory.CompanionTheory.SW.BB.RatCoord.sigma_sigma hCM`. Establish `hT` using `traceGram_isSymm σ hσ J hJ.1 b`. Establish `hs0 : (gramN σ J b n).IsSymm`. Use `Matrix.IsSymm.ext fun p q => ?_` and prove the remaining obligations.

Simplify using `only [gramN, Matrix.kroneckerMap_apply]`. Rewrite using `[hT.apply, (Matrix.isSymm_one (n := Fin n) (α := F)).apply]`. Establish `hs : (ξ • gramN σ J b n).IsSymm` using `hs0.smul ξ`. Establish `hdet : (ξ • gramN σ J b n).det ≠ 0`. Rewrite using `[Matrix.det_smul, gramN, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]`.

Conclude with `mul_ne_zero (pow_ne_zero _ hξ0) (pow_ne_zero _ (traceGram_det_ne_zero σ hσ J hJ.2 b))`. Take `⟨t1, -, -, -, -, -, -, -, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)`. Use `haveI : IsTopologicalAddGroup (Fin n → Fin M → AF F ⊗[F] E) := inferInstance`. Use `selfDual_eq _ hs hdet _ (selfDual_transport e ?_ _ _ ?_ dx hdx)` and prove the remaining obligations. Introduce `x y`.

Rewrite using `[he, he, he]`. Use function extensionality and compare the values at `p`. Simplify using `[cvN, cv]`. Introduce `X Y`. Rewrite using `[he, he, psi_BRN σ J b ψ ξ hξ]`.
-/
theorem dx_coordN (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M d n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (ξ : F) (hξ0 : ξ ≠ 0)
    (hξ : ∀ x : AF F, ψ x = ((adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ))
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E)) :
    dx.map e = adeleMeasurePi F := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.BB.RatCoord.sigma_sigma hCM
  have hT := traceGram_isSymm σ hσ J hJ.1 b
  have hs0 : (gramN σ J b n).IsSymm := by
    refine Matrix.IsSymm.ext fun p q => ?_
    simp only [gramN, Matrix.kroneckerMap_apply]
    rw [hT.apply, (Matrix.isSymm_one (n := Fin n) (α := F)).apply]
  have hs : (ξ • gramN σ J b n).IsSymm := hs0.smul ξ
  have hdet : (ξ • gramN σ J b n).det ≠ 0 := by
    rw [Matrix.det_smul, gramN, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (pow_ne_zero _ (traceGram_det_ne_zero σ hσ J hJ.2 b))
  obtain ⟨t1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI : IsTopologicalAddGroup (Fin n → Fin M → AF F ⊗[F] E) := inferInstance
  refine selfDual_eq _ hs hdet _ (selfDual_transport e ?_ _ _ ?_ dx hdx)
  · intro x y
    rw [he, he, he]
    funext p
    simp [cvN, cv]
  · intro X Y
    rw [he, he, psi_BRN σ J b ψ ξ hξ]

end Link

section Meas
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
open GroundTheory.Global
open scoped TensorProduct ENNReal NNReal
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, hAfLC, hAfSC, hAfT2⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`. Take `⟨ξ, hξ⟩` from `GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1`. Establish `hξ0 : ξ ≠ 0`. Introduce and unpack `rfl`.

Take `⟨x, hx⟩` from `hψ.2.2.2`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hξ x]`. Simplify using the standard rewrite rules. Take `⟨e, he, hB⟩` from `exists_coordHomeoN σ hCM n M b`.

Establish `hdxc` using `dx_coordN σ hCM J hJ b ψ ξ hξ0 hξ dx hdx e he hB`. Establish `hEq` using `adele_eq l hH D hD hD1 lf hlf h1`. Take `⟨i1, i3⟩` from `coordMapN σ hCM (Ainf F) b l hH n M`. Take `⟨f1, f3⟩` from `coordMapN σ hCM (Af F) b lf hlf n M`. Use `haveI hBi := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.2.1 n M`.

Use `haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M`. Use `haveI : SigmaFinite l := by`. Conclude with `Measure.IsAddHaarMeasure.sigmaFinite l`. Use `haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf`. Set `eI` to `(i1.homeomorph).toMeasurableEquiv`.

Set `eF` to `(f1.homeomorph).toMeasurableEquiv`. Set `eA` to `e.toMeasurableEquiv`. Establish `hI : MeasurePreserving eI (coordW (Ainf F) b l n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l)` using `⟨eI.measurable, i3⟩`. Establish `hF : MeasurePreserving eF (coordW (Af F) b lf n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf)` using `⟨eF.measurable, f3⟩`. Establish `hΘ` using `measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) (Fin n × (Fin M × Fin d)) (fun _ => l) (fun _ => lf)`.

Establish `hA' : MeasurePreserving eA dx (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf)`. Establish `e1 : GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι` using `Fin n × (Fin M × Fin d)) = Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf := by`. Rewrite using `[GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, hEq]`. Both sides reduce to the same expression. Conclude with `⟨eA.measurable, hdxc.trans e1⟩`.

Set `eP` to `eI.prodCongr eF`. Use `haveI : SFinite (coordW (Af F) b lf n M) := sfinite_coordW σ hCM b lf hlf n M`. Use `haveI : SFinite (coordW (Ainf F) b l n M) := by`. Establish `hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F` using `F) (E := E) (Ainf F) b) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d b`. Use `haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK l`.

Unfold `coordW`. Use `infer_instance`. Establish `hP : MeasurePreserving eP ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M)) ((Measure.pi fun _ : Fin n × (Fin M × Fin d) => l).prod (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf))` using `hI.prod hF`. Use `(hP.comp_left_iff).1 ?_` and prove the remaining obligations. Establish `hc` using `hΘ.comp hA'`.

Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `X`. Establish `hX : ∀ p, e X p = cvN (AF F) b X p` using `fun p => by rw [he]`. Use `Prod.ext (funext fun p => ?_) (funext fun p => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cvN (Ainf F) b (projInf X) p = (e X p).1`.

Rewrite using `[hX]`. Conclude with `GlobalTheory.CompanionTheory.SW.WBox.cK_map b (fstA F) (X p.1 p.2.1) p.2.2`. Express the relevant statement in the definitionally equal form `cvN (Af F) b (projFin X) p = (e X p).2`. Rewrite using `[hX]`. Conclude with `GlobalTheory.CompanionTheory.SW.WBox.cK_map b (sndA F) (X p.1 p.2.1) p.2.2`.
-/
theorem dx_splitN' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hdx : SdW F E σ M J (AF F) ψ n dx)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M)) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM n M b
  have hdxc := dx_coordN σ hCM J hJ b ψ ξ hξ0 hξ dx hdx e he hB
  have hEq := adele_eq l hH D hD hD1 lf hlf h1
  obtain ⟨i1, i3⟩ := coordMapN σ hCM (Ainf F) b l hH n M
  obtain ⟨f1, f3⟩ := coordMapN σ hCM (Af F) b lf hlf n M
  haveI hBi := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.2.1 n M
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  haveI : SigmaFinite l := by
    exact Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  let eI := (i1.homeomorph).toMeasurableEquiv
  let eF := (f1.homeomorph).toMeasurableEquiv
  let eA := e.toMeasurableEquiv
  have hI : MeasurePreserving eI (coordW (Ainf F) b l n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l) :=
    ⟨eI.measurable, i3⟩
  have hF : MeasurePreserving eF (coordW (Af F) b lf n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf) :=
    ⟨eF.measurable, f3⟩
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Fin n × (Fin M × Fin d)) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving eA dx (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf) := by
    have e1 : GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Fin n × (Fin M × Fin d)) =
        Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf := by
      rw [GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, hEq]
      rfl
    exact ⟨eA.measurable, hdxc.trans e1⟩
  let eP := eI.prodCongr eF
  haveI : SFinite (coordW (Af F) b lf n M) := sfinite_coordW σ hCM b lf hlf n M
  haveI : SFinite (coordW (Ainf F) b l n M) := by
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Ainf F) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK l
    unfold coordW
    infer_instance
  have hP : MeasurePreserving eP ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M))
      ((Measure.pi fun _ : Fin n × (Fin M × Fin d) => l).prod (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext X
  have hX : ∀ p, e X p = cvN (AF F) b X p := fun p => by rw [he]
  refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
  · change cvN (Ainf F) b (projInf X) p = (e X p).1
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (fstA F) (X p.1 p.2.1) p.2.2
  · change cvN (Af F) b (projFin X) p = (e X p).2
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (sndA F) (X p.1 p.2.1) p.2.2

end Meas

section Euler
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
open scoped TensorProduct ENNReal NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F))` using `(GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq`. Take `⟨l, hl, hH, D, hD, hD1⟩` from `@std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm`. Establish `h` using `dx_splitN' σ hCM M J hJ ψ hψ n dx hdx b l hH D hD hD1 lf hlf h1`. Rewrite `h` using `[coordW_congr hm l laminf hl b n M]`. Conclude with `h`.
-/
theorem dx_splitN (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hdx : SdW F E σ M J (AF F) ψ n dx)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b laminf n M).prod (coordW (Af F) b lf n M)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ := @std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := dx_splitN' σ hCM M J hJ ψ hψ n dx hdx b l hH D hD hD1 lf hlf h1
  rw [coordW_congr hm l laminf hl b n M] at h
  exact h

/- English proof (translation)
Take `⟨lf, hlf, h1⟩` from `GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F`. Establish `hmass` using `fun v => coordW_latV σ hCM b lam hlam n M v`. Use `⟨fun v => ?_, ?_, ∅, fun S _ φinf φ hφi hφ => ?_⟩` and prove the remaining obligations. Simplify using `only [hmass v]`. Conclude with `ENNReal.one_lt_top`.

Simplify using `only [hmass]`. Simplify using `[summable_zero]`. Establish `hT` using `dx_splitN σ hCM M J hJ ψ hψ n dx hdx b laminf hinf lf hlf h1`. Take `⟨hg, hI⟩` from `lint_fin σ hCM b lam hlam lf hlf h1 n M S φ hφ`. Use `haveI := sfinite_coordW σ hCM b lf hlf n M`.

Use `set g := ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator fun Y => ∏ v ∈ S, φ v (projV v Y) with hgdef`. Establish `e : ∀ X, pureL b S φinf φ X = (fun p : _ × _ => φinf p.1 * g p.2) (projInf X, projFin X)`. Introduce `X`. Distinguish the cases in `hX : X ∈ intOff b S`. Establish `hX' : projFin X ∈ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E))` using `hX`.

Simplify using `only [pureL, Set.indicator_of_mem hX, hgdef, Set.indicator_of_mem hX']`. Establish `hX' : projFin X ∉ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E))` using `hX`. Simplify using `only [pureL, Set.indicator_of_notMem hX, hgdef, Set.indicator_of_notMem hX', mul_zero]`. Establish `hm : Measurable (fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => φinf p.1 * g p.2)` using `(hφi.comp measurable_fst).mul (hg.comp measurable_snd)`. Rewrite using `[lintegral_congr e, hT.lintegral_comp hm, lintegral_prod_mul hφi.aemeasurable hg.aemeasurable, hI]`.

Simplify using `[hmass]`.
-/
theorem euler_product_of_standard_local_measures (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hdx : SdW F E σ M J (AF F) ψ n dx)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v)) :
    IsEulerProd b dx 1 (coordW (Ainf F) b laminf n M) (fun v => coordW (Fv F v) b (lam v) n M) := by
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hmass := fun v => coordW_latV σ hCM b lam hlam n M v
  refine ⟨fun v => ?_, ?_, ∅, fun S _ φinf φ hφi hφ => ?_⟩
  · simp only [hmass v]; exact ENNReal.one_lt_top
  · simp only [hmass]; simp [summable_zero]
  · have hT := dx_splitN σ hCM M J hJ ψ hψ n dx hdx b laminf hinf lf hlf h1
    obtain ⟨hg, hI⟩ := lint_fin σ hCM b lam hlam lf hlf h1 n M S φ hφ
    haveI := sfinite_coordW σ hCM b lf hlf n M
    set g := ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y) with hgdef
    have e : ∀ X, pureL b S φinf φ X =
        (fun p : _ × _ => φinf p.1 * g p.2) (projInf X, projFin X) := by
      intro X
      by_cases hX : X ∈ intOff b S
      · have hX' : projFin X ∈ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_mem hX, hgdef, Set.indicator_of_mem hX']
      · have hX' : projFin X ∉ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_notMem hX, hgdef, Set.indicator_of_notMem hX', mul_zero]
    have hm : Measurable (fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => φinf p.1 * g p.2) :=
      (hφi.comp measurable_fst).mul (hg.comp measurable_snd)
    rw [lintegral_congr e, hT.lintegral_comp hm, lintegral_prod_mul hφi.aemeasurable hg.aemeasurable, hI]
    simp [hmass]

end Euler

end GlobalTheory.CompanionTheory.SiegelND.DxN

end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.DxN

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx d b laminf lam hinf hlam`. Conclude with `⟨euler_product_of_standard_local_measures σ hCM M J hJ ψ hψ n dx hdx b laminf lam hinf hlam, fun v => GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hCM b lam hlam n M v⟩`.
-/
theorem selfDual_isEulerProd_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → GlobalTheory.CompanionTheory.SW.IsEulerProd b dx 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (fun v => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) ∧ ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx d b laminf lam hinf hlam
  exact ⟨euler_product_of_standard_local_measures σ hCM M J hJ ψ hψ n dx hdx b laminf lam hinf hlam,
    fun v => GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hCM b lam hlam n M v⟩

end GlobalTheory.CompanionTheory.SiegelND.DxN
