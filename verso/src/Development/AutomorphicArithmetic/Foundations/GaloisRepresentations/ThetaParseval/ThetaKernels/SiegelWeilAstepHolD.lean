import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingNStr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepHolB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepHolW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepFc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Establish `hc'` using `hc`. Take `⟨hN, -, -, h1⟩` from `hc'`. Establish `hσ` using `_root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good`. Take `⟨iLC, iSC, iT2, iBo⟩` from `kfour.nA_top hσ d.ok.frame`. Take `⟨K, hK, hKc⟩` from `kfour.nF_cocompact hσ d.ok.frame`.

Take `⟨-, -, hTG, -, -, -⟩` from `H.auxEx F E σ d`. Use `haveI := hTG`. Establish `hψ` using `GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std`. Establish `hnbc` using `kfour.nb_continuous hσ d.ok.frame hN`. Set `u : nA σ d.Y d.b → ℂ` to `fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))`.

Establish `huc : Continuous u` using `kfour.continuous_chr hψ.1 T.1.1`. Set `γf : nA σ d.Y d.b → nA σ d.Y d.b` to `fun β => Classical.choose (hKc β)`. Establish `hγ : ∀ β, γf β ∈ nF σ d.Y d.b ∧ γf β + β ∈ K` using `fun β => Classical.choose_spec (hKc β)`. Set `c : nA σ d.Y d.b → d.G` to `fun β => nb (γf β + β) * x'`. Establish `key : ∀ β (g : d.G), A (c β * g) = A (nb β * (x' * g))`.

Introduce `β g`. Use `show A (nb (γf β + β) * x' * g) = _`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, mul_assoc, hAi _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN (hγ β).1)]`. Use `haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Establish `hC : IsCompact ((fun k => nb k * x') '' K)` using `hK.image (hnbc.mul continuous_const)`.

Establish `hmeas : ∀ y, AEStronglyMeasurable (fun β => A (c β * R.ι w y) * u β) (lam.restrict 𝓖)`. Introduce `y`. Establish `e : (fun β => A (c β * R.ι w y) * u β) = fun β => A (nb β * (x' * R.ι w y)) * u β`. Use function extensionality and compare the values at `fun β => by rw [key]`. Rewrite using `[e]`.

Conclude with `((hAc.comp (hnbc.mul continuous_const)).mul huc).aestronglyMeasurable`. Use `H.holT.2 d.n pp qq e d.G (R.ι w) (R.cont w) A hAc hA (nA σ d.Y d.b) (lam.restrict 𝓖) c u _ hC (fun β => ⟨_, (hγ β).2, rfl⟩) (fun β => (hψ.2.1 _).le) hmeas` as an intermediate fact. Use `this using 2 with y` and compare the differences between its conclusion and the goal. Simplify using `only [fc]`. Use `congr 1`.

Use function extensionality and compare the values at `β`. Rewrite using `[key]`.
-/
theorem holPhi_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (A : d.G → ℂ) (hAc : Continuous A)
    (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g) (pp qq : ℕ) (e : ℤ)
    (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) (x' : d.G) :
    IsHolW pp qq e fun y => fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
  have hc' := hc
  obtain ⟨hN, -, -, h1⟩ := hc'
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ d.ok.frame
  obtain ⟨-, -, hTG, -, -, -⟩ := H.auxEx F E σ d
  haveI := hTG
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have hnbc := kfour.nb_continuous hσ d.ok.frame hN
  let u : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have huc : Continuous u := kfour.continuous_chr hψ.1 T.1.1
  let γf : nA σ d.Y d.b → nA σ d.Y d.b := fun β => Classical.choose (hKc β)
  have hγ : ∀ β, γf β ∈ nF σ d.Y d.b ∧ γf β + β ∈ K := fun β => Classical.choose_spec (hKc β)
  let c : nA σ d.Y d.b → d.G := fun β => nb (γf β + β) * x'
  have key : ∀ β (g : d.G), A (c β * g) = A (nb β * (x' * g)) := by
    intro β g
    show A (nb (γf β + β) * x' * g) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, mul_assoc, hAi _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN (hγ β).1)]
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hC : IsCompact ((fun k => nb k * x') '' K) := hK.image (hnbc.mul continuous_const)
  have hmeas : ∀ y, AEStronglyMeasurable (fun β => A (c β * R.ι w y) * u β) (lam.restrict 𝓖) := by
    intro y
    have e : (fun β => A (c β * R.ι w y) * u β) = fun β => A (nb β * (x' * R.ι w y)) * u β :=
      funext fun β => by rw [key]
    rw [e]
    exact ((hAc.comp (hnbc.mul continuous_const)).mul huc).aestronglyMeasurable
  have := H.holT.2 d.n pp qq e d.G (R.ι w) (R.cont w) A hAc hA (nA σ d.Y d.b) (lam.restrict 𝓖) c u _ hC
    (fun β => ⟨_, (hγ β).2, rfl⟩) (fun β => (hψ.2.1 _).le) hmeas
  convert this using 2 with y
  simp only [fc]
  congr 1
  funext β
  rw [key]
/- English proof (translation)
Establish `hc'` using `hc`. Take `⟨hN, -, -, -⟩` from `hc'`. Establish `hr : ∀ l, _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T L.i₀ l = 0` using `fun l => by`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, (hT.1 l).1]`. Establish `hcol : ∀ k, _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T k L.i₀ = 0` using `fun k => by`.

Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, (hT.1 k).2]`. Establish `hchar : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (h : Matrix (Fin d.n) (Fin d.n) ℂ) (xN y : GR d.n), h.IsHermitian → mR xN = nU h → fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xN * y)) = Complex.exp (Complex.I * (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R …`. Introduce `x' hx' h xN y hh hxN`. Take `⟨β₁, hι, hBw, hBu, hBf⟩` from `_root_.PositivityTheory.SiegelWeilFormula.AStep.unipotent_realEmbedding_exists d R w hN xN h hxN`. Rewrite using `[map_mul, ← mul_assoc, hx' xN, hι, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KSing.fc_shift_k d hc A hAi T β₁, _root_.PositivityTheory.SiegelWeilFormula.AStep.character_unipotent_trace d R w T β₁ h hh hBw hBu hBf]`.

Establish `hright : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx y : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * a = _root_.PositivityTheory.SiegelWeilFormula.AStep.be …` using `fun x' hx' => H.holT.1 d.n pp qq e _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.holPhi_k H R w hc T A hAc hAi pp qq e hA x') (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T) (hchar x' hx')`. Establish `hleft : ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * a = _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T → ∀ x, fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w x …`. Introduce `a a' xx hxx hs x`. Take `⟨x', y₀, rfl, hx'⟩` from `_root_.PositivityTheory.SiegelWeilFormula.AStep.decW_pf_k R w x`. Rewrite using `[← mul_assoc, ← hx' xx, mul_assoc, ← map_mul, hright x' hx' a a' xx y₀ hxx hs]`.

Use `⟨fun τ y hy x => ?_, fun uM ν 𝓤 hu u x => ?_⟩` and prove the remaining obligations. Rewrite using `[hleft _ _ y hy (stab_diag L.i₀ _ (fun k hk => by simp [Pi.single_eq_of_ne hk]) _ hr hcol) x, weight_factor_dilation L.i₀ τ y hy]`. Use `congr 2`. Apply the tactic sequence `rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp`. Establish `h0` using `Krd.zeta_ne R.hζ`.

Use `(H.uEx F E σ d R L).2 uM ν 𝓤 hu w _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcCont_k d hc T A hAc hAi) (fun u hu' x => (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT A hAc hAi u hu' x) ?_ u x` and prove the remaining obligations. Introduce `u y huy x`. Rewrite using `[huy]`. Take `⟨a', ha'⟩` from `hu.1 u`. Use `set S := ∑ j, Matrix.single L.i₀ (L.em j) (u j) with hS`.

Establish `hne : ∀ j, L.em j ≠ L.i₀` using `fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩`. Use `set M := d.cw w S with hMdef`. Establish `hM : ∀ k l, k ≠ L.i₀ → M k l = 0`. Introduce `k l hk`. Simplify using `[hMdef, hS, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.sum_apply, Matrix.single_apply, Ne.symm hk]`.

Establish `hM0 : M L.i₀ L.i₀ = 0`. Simplify using `[hMdef, hS, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.sum_apply, Matrix.single_apply, hne]`. Establish `hmy : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y)) * dZ d.n R.ζ⁻¹`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k]`. Simplify using `only [← Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.mul_one]`. Rewrite `hmy` using `[← huy, ha']`. Establish `hy : mR y = Matrix.fromBlocks (1 + M) 0 0 ((R.ζ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)) * d.cw w a' * (R.ζ⁻¹ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)))`. Rewrite using `[hmy, hMdef]`. Simplify using `[dZ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_add]`.

Rewrite using `[hleft _ _ y hy (stab_row L.i₀ M hM _ hr hcol) x, weight_factor_det_one pp qq e y _ _ hy (det_row L.i₀ M hM hM0), one_mul]`.
-/
theorem holCoef_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x := by
  have hc' := hc
  obtain ⟨hN, -, -, -⟩ := hc'
  have hr : ∀ l, _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T L.i₀ l = 0 := fun l => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, (hT.1 l).1]
  have hcol : ∀ k, _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T k L.i₀ = 0 := fun k => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, (hT.1 k).2]
  have hchar : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (h : Matrix (Fin d.n) (Fin d.n) ℂ) (xN y : GR d.n),
      h.IsHermitian → mR xN = nU h → fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xN * y)) =
        Complex.exp (Complex.I * (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * h).trace) * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
    intro x' hx' h xN y hh hxN
    obtain ⟨β₁, hι, hBw, hBu, hBf⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.unipotent_realEmbedding_exists d R w hN xN h hxN
    rw [map_mul, ← mul_assoc, hx' xN, hι, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KSing.fc_shift_k d hc A hAi T β₁,
      _root_.PositivityTheory.SiegelWeilFormula.AStep.character_unipotent_trace d R w T β₁ h hh hBw hBu hBf]
  have hright : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ)
      (xx y : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * a = _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T →
      fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xx * y)) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) :=
    fun x' hx' => H.holT.1 d.n pp qq e _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.holPhi_k H R w hc T A hAc hAi pp qq e hA x') (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T) (hchar x' hx')
  have hleft : ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' →
      aᴴ * _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * a = _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T →
      ∀ x, fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w xx * x) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T x := by
    intro a a' xx hxx hs x
    obtain ⟨x', y₀, rfl, hx'⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.decW_pf_k R w x
    rw [← mul_assoc, ← hx' xx, mul_assoc, ← map_mul, hright x' hx' a a' xx y₀ hxx hs]
  refine ⟨fun τ y hy x => ?_, fun uM ν 𝓤 hu u x => ?_⟩
  · rw [hleft _ _ y hy (stab_diag L.i₀ _ (fun k hk => by simp [Pi.single_eq_of_ne hk]) _ hr hcol) x,
      weight_factor_dilation L.i₀ τ y hy]
    congr 2
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have h0 := Krd.zeta_ne R.hζ
    refine (H.uEx F E σ d R L).2 uM ν 𝓤 hu w _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcCont_k d hc T A hAc hAi)
      (fun u hu' x => (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT A hAc hAi u hu' x) ?_ u x
    intro u y huy x
    rw [huy]
    obtain ⟨a', ha'⟩ := hu.1 u
    set S := ∑ j, Matrix.single L.i₀ (L.em j) (u j) with hS
    have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
    set M := d.cw w S with hMdef
    have hM : ∀ k l, k ≠ L.i₀ → M k l = 0 := by
      intro k l hk
      simp [hMdef, hS, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.sum_apply, Matrix.single_apply, Ne.symm hk]
    have hM0 : M L.i₀ L.i₀ = 0 := by
      simp [hMdef, hS, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.sum_apply, Matrix.single_apply, hne]
    have hmy : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y)) * dZ d.n R.ζ⁻¹ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k]
      simp only [← Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.one_mul]
      rw [Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.mul_one]
    rw [← huy, ha'] at hmy
    have hy : mR y = Matrix.fromBlocks (1 + M) 0 0 ((R.ζ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)) * d.cw w a' *
        (R.ζ⁻¹ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ))) := by
      rw [hmy, hMdef]
      simp [dZ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_add]
    rw [hleft _ _ y hy (stab_row L.i₀ M hM _ hr hcol) x, weight_factor_det_one pp qq e y _ _ hy (det_row L.i₀ M hM hM0), one_mul]
end PositivityTheory.SiegelWeilFormula.AStep
end
end
