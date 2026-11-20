import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2, hcm.2.2.2]`. Simplify using the standard rewrite rules.
-/
theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

/- English proof (translation)
Simplify using `only [hE, hform, map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : σ ((σ : E →+* E) (x j)) = x j` using `sigma_sigma hcm _`. Establish `h2 : (σ : E →+* E) (x i) = σ (x i)` using `rfl`.

Rewrite using `[h1, hJ.1 i j, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_self_fixed (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma hcm _
  have h2 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, hJ.1 i j, h2]
  ring

/- English proof (translation)
Establish `hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b` using `fun a b => by`. Rewrite using `[Subsingleton.elim a b]`. Conclude with `hE_self_fixed hcm hJ _`. Take `⟨β, e, h, -⟩` from `GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm _ hT`. Use `⟨β, h ?_, e⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_unique]`. Introduce `h0`. Conclude with `hX (funext fun a => by rw [Subsingleton.elim a default]; exact hA _ h0)`.
-/
theorem exists_len (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    {X : Fin 1 → Fin 2 → E} (hX : X ≠ 0) : ∃ β : F, β ≠ 0 ∧ X ∈ sph σ J β := by
  have hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b := fun a b => by
    rw [Subsingleton.elim a b]
    exact hE_self_fixed hcm hJ _
  obtain ⟨β, e, h, -⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm _ hT
  refine ⟨β, h ?_, e⟩
  rw [Matrix.det_unique]
  intro h0
  exact hX (funext fun a => by rw [Subsingleton.elim a default]; exact hA _ h0)

/- English proof (translation)
Establish `e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β'` using `h.symm.trans h'`. Conclude with `(algebraMap F E).injective (congrFun (congrFun e 0) 0)`.
-/
theorem sph_unique {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β β' : F} (h : X ∈ sph σ J β)
    (h' : X ∈ sph σ J β') : β = β' := by
  have e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β' := h.symm.trans h'
  exact (algebraMap F E).injective (congrFun (congrFun e 0) 0)

/- English proof (translation)
Introduce and unpack `rfl`. Use `hβ (sph_unique h ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `a c`. Simplify using `[gramE, hE, hform]`.
-/
theorem ne_zero_of_mem_sph {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β : F} (hβ : β ≠ 0)
    (h : X ∈ sph σ J β) : X ≠ 0 := by
  rintro rfl
  refine hβ (sph_unique h ?_)
  funext a c
  simp [gramE, hE, hform]

def sphEquiv (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J) :
    (Σ β : {β : F // β ≠ 0}, sph σ J β.1) ≃ {X : Fin 1 → Fin 2 → E | X ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1, ne_zero_of_mem_sph p.1.2 p.2.2⟩) (by
    constructor
    · rintro ⟨β, X⟩ ⟨β', X'⟩ h
      have hX : X.1 = X'.1 := congrArg Subtype.val h
      have hb : β = β' := Subtype.ext (sph_unique X.2 (hX ▸ X'.2))
      subst hb
      obtain rfl : X = X' := Subtype.ext hX
      rfl
    · rintro ⟨X, hX⟩
      obtain ⟨β, h0, hβ⟩ := exists_len hcm hJ hA hX
      exact ⟨⟨⟨β, h0⟩, ⟨X, hβ⟩⟩, rfl⟩)

/- English proof (translation)
Use extensionality with `s hs`. Simplify using `only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]`. Use `congr 1`. Rewrite using `[← (sphEquiv hcm hJ hA).tsum_eq, ENNReal.tsum_sigma']`. Both sides reduce to the same expression.
-/
theorem thetaMeas_ne (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) :
    thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0} =
      Measure.sum fun β : {β : F // β ≠ 0} => thetaMeas σ J μ 𝓕 (sph σ J β.1) := by
  ext s hs
  simp only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
  congr 1
  rw [← (sphEquiv hcm hJ hA).tsum_eq, ENNReal.tsum_sigma']
  rfl

end Alg

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hTE hL hR F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm κ hκ`. Take `⟨⟨θ, hθ⟩, -⟩` from `PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hcm.1`. Take `⟨S, hS⟩` from `hR F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ`. Take `⟨φ, A, ht, hv0, hvT⟩` from `hTE F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm S`. Establish `hLt` using `hL F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A ht`.

Establish `hRt` using `hS S (Finset.Subset.refl _) φ A ht`. Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `: BorelSpace (Ainf F ⊗[F] E)` using `⟨rfl⟩`. Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1`. Take `⟨_, -, -, -, -, -, -, hBinf, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)`.

Use `hBinf 1 2` as an intermediate fact. Take `⟨hφc, -, -, -, hAS, hAo⟩` from `ht`. Establish `hdil : ∀ ε : ℝ, Continuous (dil θ ε : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → _)` using `fun ε => continuous_pi fun a => continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_apply a))`. Establish `hloc : ∀ v, IsCompact (A v) ∧ MeasurableSet (A v) ∧ ∀ s : HermR (Fv F v) σ 1, m v s (A v) < ⊤` using `fun v => by`. Establish `hRv` using `GlobalTheory.T.completion_is_local_ring F v`.

Establish `hRv'` using `hRv`. Take `⟨_, _, _, _, -⟩` from `hRv'`. Establish `: BorelSpace (Fv F v)` using `⟨rfl⟩`. Take `⟨_, _, _, _, -, -, -, hB, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)`. Use `hB 1 2` as an intermediate fact.

Take `⟨-, k1, k2⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1`. Establish `hco : IsCompact (A v) ∧ IsOpen (A v)`. Distinguish the cases in `hv : v ∈ S`. Conclude with `⟨(hAS v hv).1, (hAS v hv).2.1⟩`. Rewrite using `[hAo v hv]`.

Conclude with `(GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v`. Use `⟨hco.1, hco.2.measurableSet, fun s => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 2) (k2 1) (hm v) s).1` as an intermediate fact. Conclude with `hco.1.measure_lt_top`. Establish `hcof : ∀ᶠ v in cofinite, A v = latV b v` using `S.finite_toSet.eventually_cofinite_notMem.mono fun v hv => hAo v (by simpa using hv)`.

Establish `key : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X))) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) = (κ : ℝ≥0∞) * ∑' β : {β : F // β ≠ 0}, (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)) …` using `fun ε => by`. Rewrite using `[thetaMeas_ne hcm hJ hAn, Measure.restrict_sum_of_countable, lintegral_sum_measure, ← ENNReal.tsum_mul_left]`. Use `tsum_congr fun β => ?_` and prove the remaining obligations. Establish `hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β.1)) κ (mi (hermScal (Ainf F) σ (algebraMap F _ β.1))) (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β.1)))` using `hκ β.1 β.2`. Take `⟨-, e⟩` from `GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 2 _ κ _ _ hEu (fun Y => ENNReal.ofReal (φ (dil θ ε Y))) A (hφc.comp (hdil ε)).measurable.ennreal_ofReal (fun v => (hloc v).2.1) (fun v => (hloc v).2.2 _) hcof`.

Rewrite using `[e, mul_assoc]`. Simplify using `only [key] at hLt`. Establish `h1` using `ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hRt (Or.inr ENNReal.coe_ne_top)`. Establish `h2 : (vol b li lam S φ A) = (κ : ℝ≥0∞) * vol b li lam S φ A` using `tendsto_nhds_unique hLt (h1.congr fun ε => mul_left_comm _ _ _)`. Establish `h3 : (κ : ℝ≥0∞) = 1`.

Establish `h4 : (κ : ℝ≥0∞) * vol b li lam S φ A = 1 * vol b li lam S φ A` using `by rw [one_mul]; exact h2.symm`. Conclude with `(ENNReal.mul_left_inj hv0 hvT).1 h4`. Conclude with `h3` after adjusting the coercions.
-/
theorem cnt : TestEx → LSide → RSide → Cnt := by
  intro hTE hL hR F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm κ hκ
  obtain ⟨⟨θ, hθ⟩, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hcm.1
  obtain ⟨S, hS⟩ := hR F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨φ, A, ht, hv0, hvT⟩ := hTE F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm S
  have hLt := hL F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A ht
  have hRt := hS S (Finset.Subset.refl _) φ A ht
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  obtain ⟨_, -, -, -, -, -, -, hBinf, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := hBinf 1 2
  obtain ⟨hφc, -, -, -, hAS, hAo⟩ := ht
  have hdil : ∀ ε : ℝ, Continuous (dil θ ε : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → _) := fun ε =>
    continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hloc : ∀ v, IsCompact (A v) ∧ MeasurableSet (A v) ∧
      ∀ s : HermR (Fv F v) σ 1, m v s (A v) < ⊤ := fun v => by
    have hRv := GlobalTheory.T.completion_is_local_ring F v
    have hRv' := hRv
    obtain ⟨_, _, _, _, -⟩ := hRv'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    have := hB 1 2
    obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have hco : IsCompact (A v) ∧ IsOpen (A v) := by
      by_cases hv : v ∈ S
      · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
      · rw [hAo v hv]
        exact (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v
    refine ⟨hco.1, hco.2.measurableSet, fun s => ?_⟩
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 2) (k2 1) (hm v) s).1
    exact hco.1.measure_lt_top
  have hcof : ∀ᶠ v in cofinite, A v = latV b v :=
    S.finite_toSet.eventually_cofinite_notMem.mono fun v hv => hAo v (by simpa using hv)
  have key : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) =
      (κ : ℝ≥0∞) * ∑' β : {β : F // β ≠ 0},
        (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))) *
          ENNReal.ofReal (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β.1)) (A v)).toReal) := fun ε => by
    rw [thetaMeas_ne hcm hJ hAn, Measure.restrict_sum_of_countable, lintegral_sum_measure, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun β => ?_
    have hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β.1)) κ (mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))
        (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β.1))) := hκ β.1 β.2
    obtain ⟨-, e⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 2 _ κ _ _ hEu (fun Y => ENNReal.ofReal (φ (dil θ ε Y))) A
      (hφc.comp (hdil ε)).measurable.ennreal_ofReal (fun v => (hloc v).2.1) (fun v => (hloc v).2.2 _) hcof
    rw [e, mul_assoc]
  simp only [key] at hLt
  have h1 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hRt (Or.inr ENNReal.coe_ne_top)
  have h2 : (vol b li lam S φ A) = (κ : ℝ≥0∞) * vol b li lam S φ A :=
    tendsto_nhds_unique hLt (h1.congr fun ε => mul_left_comm _ _ _)
  have h3 : (κ : ℝ≥0∞) = 1 := by
    have h4 : (κ : ℝ≥0∞) * vol b li lam S φ A = 1 * vol b li lam S φ A := by rw [one_mul]; exact h2.symm
    exact (ENNReal.mul_left_inj hv0 hvT).1 h4
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.RgMass

end
