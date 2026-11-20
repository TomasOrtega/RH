import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitEtaleHermitianPairIsometryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApplyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuousStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceTowerFiniteEtaleHermitianPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSelfDualPiHaarTraceStarDotProductUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportSelfDualHaarMeasureKernelAddEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEqSumCoordsOfAlgEquivStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show (algebraMap F K).mapMatrix !![1, t; 0, 1] = !![1, algebraMap F K t; 0, 1]`. Apply the tactic sequence `ext i k; fin_cases i <;> fin_cases k <;> simp`.
-/
theorem sl2Map_nS {F K : Type} [Field F] [CommRing K] [Algebra F K] (t : F) :
    SpecialLinearGroup.map (algebraMap F K) (nS t) = nS (algebraMap F K t) := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![1, t; 0, 1] = !![1, algebraMap F K t; 0, 1]
  ext i k; fin_cases i <;> fin_cases k <;> simp

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show (algebraMap F K).mapMatrix !![0, 1; -1, 0] = !![0, 1; -1, 0]`. Apply the tactic sequence `ext i k; fin_cases i <;> fin_cases k <;> simp`.
-/
theorem sl2Map_wS {F K : Type} [Field F] [CommRing K] [Algebra F K] :
    SpecialLinearGroup.map (algebraMap F K) (wS F) = wS K := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![0, 1; -1, 0] = !![0, 1; -1, 0]
  ext i k; fin_cases i <;> fin_cases k <;> simp

/- English proof (translation)
Introduce `hW hG F E _ _ _ _ _ r M ψ hψ`. Apply the tactic sequence `obtain ⟨A, e, j, hj, hNe⟩ := GlobalTheory.T.exists_split_etaleHermitianPair_isometry F E r`. Use `haveI : LocallyCompactSpace E := Unram.lcE (F := F)`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Use `haveI : SecondCountableTopology E := secondCountable_of_proper`.

Use `haveI : CharZero F := Unram.charZero (E := E)`. Use `letI mE : MeasurableSpace E := M.mE`. Use `haveI : BorelSpace E := M.bE`. Take `⟨hjc, hjsc⟩` from `GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous F E A r j`. Set `jh : A.L ≃ₜ (Fin r → E)` to `{ j.toEquiv with continuous_toFun := hjc, continuous_invFun := hjsc }`.

Set `μE : Measure (Fin r → E)` to `Measure.pi fun _ => M.μE`. Set `B : (Fin r → E) → (Fin r → E) → ℂ` to `fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))`. Establish `hsd : SelfDual μE B` using `GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified F E r M ψ hψ`. Take `⟨hT1, hT2⟩` from `GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv j.toAddEquiv hjc hjsc μE B`. Establish `hker : A.kerL ψ ((1 : A.Kˣ) : A.K) = fun x y => B (j.toAddEquiv x) (j.toAddEquiv y)`.

Use function extensionality and compare the values at `x y`. Establish `h1` using `hj x y`. Simplify using `only [map_one, one_mul] at h1`. Use `show ψ (Algebra.trace F A.K (((1 : A.Kˣ) : A.K) * Algebra.trace A.K A.L (star x * y))) = ψ (Algebra.trace F E (star (j x) ⬝ᵥ j y))`. Rewrite using `[Units.val_one, one_mul, GlobalTheory.T.trace_tower_finiteEtaleHermitianPair, h1]`.

Establish `hsdL : SelfDual (Measure.map j.toAddEquiv.symm μE) (A.kerL ψ ((1 : A.Kˣ) : A.K))`. Rewrite using `[hker]`. Conclude with `hT1 hsd`. Take `⟨γ, Wk, hWk⟩` from `hW F E A ψ hψ 1 _ hsdL`. Establish `hγ : γ = 1` using `hG F E A ψ hψ 1 _ hsdL A.etaK γ Wk hWk r j (by simpa using hj)`.

Take `⟨hTrE, -, -⟩` from `GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E`. Establish `htr2 : ∀ a : F, Algebra.trace F E (algebraMap F E a) = 2 * a`. Introduce `a`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[hTrE, Unram.star_fix (F := F) (E := E) a, map_mul, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : ∀ y : A.L, Algebra.trace F A.K (A.NL y) = Algebra.trace F E (star (j y) ⬝ᵥ j y) / 2`. Introduce `y`. Establish `: star (j y) ⬝ᵥ j y = algebraMap F E (∑ i, e (A.NL y) i)`. Simplify using `only [dotProduct, Pi.star_apply, map_sum, hNe y, mul_comm]`.

Rewrite using `[this, htr2, GlobalTheory.T.trace_eq_sum_of_algEquiv_pi r e]`. Clear the denominators using the available nonvanishing facts. Establish `testj : ∀ φ : (Fin r → E) → ℂ, IsTest φ → IsTest (fun y : A.L => φ (j y))` using `fun φ hφ => ⟨hφ.1.comp_continuous hjc, hφ.2.comp_homeomorph jh⟩`. Establish `testjs : ∀ φ : A.L → ℂ, IsTest φ → IsTest (fun b => φ (j.symm b))` using `fun φ hφ => ⟨hφ.1.comp_continuous hjsc, hφ.2.comp_homeomorph jh.symm⟩`. Establish `hz : IsTest (0 : A.L → ℂ)` using `⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩`.

Establish `hW0 : ∀ G, Wk G 0 = 0`. Introduce `G`. Use `hWk.1.2.2.2 G 1 0 0 hz hz` as an intermediate fact. Simplify using `only [one_smul, add_zero] at this`. Simplify using `using this`.

Set `ι : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) A.K` to `SpecialLinearGroup.map (algebraMap F A.K)`. Set `T : SpecialLinearGroup (Fin 2) F → ((Fin r → E) → ℂ) → (Fin r → E) → ℂ` to `fun g φ b => Wk (ι g) (fun y => φ (j y)) (j.symm b)`. Establish `hTt : ∀ g φ, IsTest φ → IsTest (T g φ)` using `fun g φ hφ => testjs _ (hWk.1.1 _ _ (testj φ hφ))`. Establish `hT0 : ∀ g, T g 0 = 0`. Introduce `g`.

Use function extensionality and compare the values at `b`. Use `show Wk (ι g) (fun y => (0 : (Fin r → E) → ℂ) (j y)) (j.symm b) = 0`. Establish `: (fun y => (0 : (Fin r → E) → ℂ) (j y)) = 0` using `rfl`. Rewrite using `[this, hW0]`. Both sides reduce to the same expression.

Establish `hsl : ∀ f : Hn r F E → ℂ, IsTest f → ∀ X : Hn r F E, IsTest (fun y : A.L => f (X.1, j y, X.2.2))` using `fun f hf X => testj _ ((GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T 1) (hTt 1) (hT0 1) f hf).1 X.1 X.2.2)`. Use `⟨fun g f X => T g (fun v => f (X.1, v, X.2.2)) X.2.1, ⟨fun g f hf => (GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T g) (hTt g) (hT0 g) f hf).2, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Use function extensionality and compare the values at `X show Wk (ι 1) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = f X`. Rewrite using `[map_one, hWk.1.2.1 _ (hsl f hf X)]`.

Simplify using the standard rewrite rules. Introduce `g h f hf`. Use function extensionality and compare the values at `X show Wk (ι (g * h)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = Wk (ι g) (fun y => Wk (ι h) (fun y' => f (X.1, j y', X.2.2)) (j.symm (j y))) (j.symm X.2.1)`. Simplify using `only [LinearEquiv.symm_apply_apply]`. Rewrite using `[map_mul, hWk.1.2.2.1 _ _ _ (hsl f hf X)]`.

Introduce `g c f f' hf hf'`. Use function extensionality and compare the values at `X show Wk (ι g) (fun y => (c • f + f') (X.1, j y, X.2.2)) (j.symm X.2.1) = c * Wk (ι g) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) + Wk (ι g) (fun y => f' (X.1, j y, X.2.2)) (j.symm X.2.1)`. Establish `key : (fun y => (c • f + f') (X.1, j y, X.2.2)) = c • (fun y => f (X.1, j y, X.2.2)) + (fun y => f' (X.1, j y, X.2.2))` using `rfl`. Rewrite using `[key, hWk.1.2.2.2 _ _ _ _ (hsl f hf X) (hsl f' hf' X)]`. Both sides reduce to the same expression.

Introduce `f hf`. Use `⟨fun t X => ?_, ?_⟩` and prove the remaining obligations. Establish `hι : ι (nS t) = nS (algebraMap F A.K t)`. Conclude with `sl2Map_nS t`. Use `show Wk (ι (nS t)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = _`.

Rewrite using `[hι, (hWk.2 _ (hsl f hf X)).1]`. Establish `hy` using `hnorm (j.symm X.2.1)`. Rewrite `hy` using `[LinearEquiv.apply_symm_apply]`. Simplify using `only [LinearEquiv.apply_symm_apply, Et.psiK, Units.val_one, mul_one, ← Algebra.smul_def, map_smul, smul_eq_mul, hy, mul_div_assoc]`. Establish `hι : ι (wS F) = wS A.K`.

Conclude with `sl2Map_wS`. Use function extensionality and compare the values at `X`. Use `show Wk (ι (wS F)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = fourU M ψ f X`. Rewrite using `[hι, (hWk.2 _ (hsl f hf X)).2.2, hγ, one_mul, hker, hT2]`. Establish `e1 : j.toAddEquiv (j.symm X.2.1) = X.2.1` using `j.apply_symm_apply _`.

Rewrite using `[e1]`. Use `show ∫ c, f (X.1, j (j.symm c), X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂μE = ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)`. Simplify using `only [LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem weilSL2_hermitian : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  intro hW hG F E _ _ _ _ _ r M ψ hψ
  obtain ⟨A, e, j, hj, hNe⟩ := GlobalTheory.T.exists_split_etaleHermitianPair_isometry F E r
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  haveI : CharZero F := Unram.charZero (E := E)
  letI mE : MeasurableSpace E := M.mE
  haveI : BorelSpace E := M.bE
  obtain ⟨hjc, hjsc⟩ := GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous F E A r j
  let jh : A.L ≃ₜ (Fin r → E) := { j.toEquiv with continuous_toFun := hjc, continuous_invFun := hjsc }
  let μE : Measure (Fin r → E) := Measure.pi fun _ => M.μE
  let B : (Fin r → E) → (Fin r → E) → ℂ := fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))
  have hsd : SelfDual μE B := GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified F E r M ψ hψ
  obtain ⟨hT1, hT2⟩ := GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv j.toAddEquiv hjc hjsc μE B
  have hker : A.kerL ψ ((1 : A.Kˣ) : A.K) = fun x y => B (j.toAddEquiv x) (j.toAddEquiv y) := by
    funext x y
    have h1 := hj x y
    simp only [map_one, one_mul] at h1
    show ψ (Algebra.trace F A.K (((1 : A.Kˣ) : A.K) * Algebra.trace A.K A.L (star x * y))) = ψ (Algebra.trace F E (star (j x) ⬝ᵥ j y))
    rw [Units.val_one, one_mul, GlobalTheory.T.trace_tower_finiteEtaleHermitianPair, h1]
  have hsdL : SelfDual (Measure.map j.toAddEquiv.symm μE) (A.kerL ψ ((1 : A.Kˣ) : A.K)) := by
    rw [hker]; exact hT1 hsd
  obtain ⟨γ, Wk, hWk⟩ := hW F E A ψ hψ 1 _ hsdL
  have hγ : γ = 1 := hG F E A ψ hψ 1 _ hsdL A.etaK γ Wk hWk r j (by simpa using hj)
  obtain ⟨hTrE, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  have htr2 : ∀ a : F, Algebra.trace F E (algebraMap F E a) = 2 * a := by
    intro a
    apply (algebraMap F E).injective
    rw [hTrE, Unram.star_fix (F := F) (E := E) a, map_mul, map_ofNat]; ring
  have hnorm : ∀ y : A.L, Algebra.trace F A.K (A.NL y) = Algebra.trace F E (star (j y) ⬝ᵥ j y) / 2 := by
    intro y
    have : star (j y) ⬝ᵥ j y = algebraMap F E (∑ i, e (A.NL y) i) := by
      simp only [dotProduct, Pi.star_apply, map_sum, hNe y, mul_comm]
    rw [this, htr2, GlobalTheory.T.trace_eq_sum_of_algEquiv_pi r e]; field_simp
  have testj : ∀ φ : (Fin r → E) → ℂ, IsTest φ → IsTest (fun y : A.L => φ (j y)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjc, hφ.2.comp_homeomorph jh⟩
  have testjs : ∀ φ : A.L → ℂ, IsTest φ → IsTest (fun b => φ (j.symm b)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjsc, hφ.2.comp_homeomorph jh.symm⟩
  have hz : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have hW0 : ∀ G, Wk G 0 = 0 := by
    intro G
    have := hWk.1.2.2.2 G 1 0 0 hz hz
    simp only [one_smul, add_zero] at this
    simpa using this
  let ι : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) A.K := SpecialLinearGroup.map (algebraMap F A.K)
  let T : SpecialLinearGroup (Fin 2) F → ((Fin r → E) → ℂ) → (Fin r → E) → ℂ :=
    fun g φ b => Wk (ι g) (fun y => φ (j y)) (j.symm b)
  have hTt : ∀ g φ, IsTest φ → IsTest (T g φ) := fun g φ hφ => testjs _ (hWk.1.1 _ _ (testj φ hφ))
  have hT0 : ∀ g, T g 0 = 0 := by
    intro g; funext b
    show Wk (ι g) (fun y => (0 : (Fin r → E) → ℂ) (j y)) (j.symm b) = 0
    have : (fun y => (0 : (Fin r → E) → ℂ) (j y)) = 0 := rfl
    rw [this, hW0]; rfl
  have hsl : ∀ f : Hn r F E → ℂ, IsTest f → ∀ X : Hn r F E, IsTest (fun y : A.L => f (X.1, j y, X.2.2)) :=
    fun f hf X => testj _ ((GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T 1) (hTt 1) (hT0 1) f hf).1 X.1 X.2.2)
  refine ⟨fun g f X => T g (fun v => f (X.1, v, X.2.2)) X.2.1, ⟨fun g f hf => (GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T g) (hTt g) (hT0 g) f hf).2, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf; funext X
    show Wk (ι 1) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = f X
    rw [map_one, hWk.1.2.1 _ (hsl f hf X)]
    simp
  · intro g h f hf; funext X
    show Wk (ι (g * h)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = Wk (ι g) (fun y => Wk (ι h) (fun y' => f (X.1, j y', X.2.2)) (j.symm (j y))) (j.symm X.2.1)
    simp only [LinearEquiv.symm_apply_apply]
    rw [map_mul, hWk.1.2.2.1 _ _ _ (hsl f hf X)]
  · intro g c f f' hf hf'; funext X
    show Wk (ι g) (fun y => (c • f + f') (X.1, j y, X.2.2)) (j.symm X.2.1) = c * Wk (ι g) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) + Wk (ι g) (fun y => f' (X.1, j y, X.2.2)) (j.symm X.2.1)
    have key : (fun y => (c • f + f') (X.1, j y, X.2.2)) = c • (fun y => f (X.1, j y, X.2.2)) + (fun y => f' (X.1, j y, X.2.2)) := rfl
    rw [key, hWk.1.2.2.2 _ _ _ _ (hsl f hf X) (hsl f' hf' X)]
    rfl
  · intro f hf
    refine ⟨fun t X => ?_, ?_⟩
    · have hι : ι (nS t) = nS (algebraMap F A.K t) := by
        exact sl2Map_nS t
      show Wk (ι (nS t)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = _
      rw [hι, (hWk.2 _ (hsl f hf X)).1]
      have hy := hnorm (j.symm X.2.1)
      rw [LinearEquiv.apply_symm_apply] at hy
      simp only [LinearEquiv.apply_symm_apply, Et.psiK, Units.val_one, mul_one, ← Algebra.smul_def, map_smul, smul_eq_mul, hy, mul_div_assoc]
    · have hι : ι (wS F) = wS A.K := by
        exact sl2Map_wS
      funext X
      show Wk (ι (wS F)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = fourU M ψ f X
      rw [hι, (hWk.2 _ (hsl f hf X)).2.2, hγ, one_mul, hker, hT2]
      have e1 : j.toAddEquiv (j.symm X.2.1) = X.2.1 := j.apply_symm_apply _
      rw [e1]
      show ∫ c, f (X.1, j (j.symm c), X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂μE = ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
      simp only [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory
