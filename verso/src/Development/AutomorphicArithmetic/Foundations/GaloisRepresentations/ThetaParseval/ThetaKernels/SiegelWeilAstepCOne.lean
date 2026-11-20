import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepFc

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace COne
/- English proof (translation)
The claim follows from `d.ok.dbl.weil.2.1.pres x Φ h`.
-/
theorem om_sch_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
/- English proof (translation)
Use `d.ok.dbl.kill 0 Φ h` as an intermediate fact. Establish `e2 : (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * (diagCols (Fin d.n) : Matrix _ _ (AE F E))ᵀ = 0` using `Matrix.zero_mul _`. Establish `e3 : (0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ = 0` using `Matrix.zero_mul _`. Use `erw [e2] at this`. Use `show d.l (d.dd.rho d.B.ψ ((0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ) Φ) = _`.

Rewrite using `[e3]`. Conclude with `this`.
-/
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have := d.ok.dbl.kill 0 Φ h
  have e2 : (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * (diagCols (Fin d.n) : Matrix _ _ (AE F E))ᵀ = 0 := Matrix.zero_mul _
  have e3 : (0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ = 0 := Matrix.zero_mul _
  erw [e2] at this
  show d.l (d.dd.rho d.B.ψ ((0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ) Φ) = _
  rw [e3]
  exact this
/- English proof (translation)
The claim follows from `(_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_zero_k d (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d x h)).symm`.
-/
theorem constantTerm_eq_fourierAtZero (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (h : Φ ∈ d.sch) (x : d.G) : d.sec0 Φ x = d.T (d.om x Φ) 0 :=
  (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_zero_k d (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d x h)).symm
/- English proof (translation)
Unfold `_root_.PositivityTheory.SiegelWeilFormula.SD_k.T Darboux.rho`. Establish `: schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) Φ`. Use function extensionality and compare the values at `y`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, map_smul, smul_eq_mul]`.
-/
theorem T_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T Darboux.rho
  have : schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) Φ := by
    funext y; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, map_smul, smul_eq_mul]
/- English proof (translation)
Unfold `_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k, tsum_mul_left]`. Simplify using `only [MeasureTheory.average]`. Conclude with `integral_const_mul _ _`.
-/
theorem orb_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) (c : ℂ) (Φ : d.Fn) : d.orb T (c • Φ) = c * d.orb T Φ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k, tsum_mul_left]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
/- English proof (translation)
Establish `e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀}` using `(Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)`. Establish `h1` using `Fintype.card_congr e`. Rewrite `h1` using `[Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]`. Use `L.i₀.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem Ln_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    (Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)
  have h1 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h1
  have := L.i₀.isLt
  omega
/- English proof (translation)
Establish `hK` using `H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)`. Establish `hsec` using `H.secK F E σ d' Ψ hK`. Take `⟨U, p, Ê, t, hE⟩` from `H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)`. Take `⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩` from `hE`. Take `⟨hadd, hbd⟩` from `_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d' hc T g`.

Take `⟨hDiff, hComm⟩` from `lamDeriv (rat2 σ d'.Y) (fun f => fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv`. Establish `hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) = iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g')` using `fun g' => ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g') (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')`. Establish `hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g = c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g`. Introduce `c φ`. Simplify using `only [fc, mul_assoc]`.

Conclude with `integral_const_mul _ _`. Establish `hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) = iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g)`. Introduce `i hi`. Rewrite using `[hComm _ hs i]`. Establish `: (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) = fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g'`.

Use function extensionality and compare the values at `fun g' => by rw [hpt g' i hi]; ring`. Rewrite using `[this, hsm]`. Expand and normalize the polynomial expressions, which then agree. Use `wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)` and prove the remaining obligations. Establish `e1 : Ê z = fun g' => p.eval z * d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g'` using `funext (hfar z hz).2`.

Rewrite using `[e1, hsm]`. Rewrite using `[hder i hi.le, pderiv_lt p _ i hi, zero_mul]`.
-/
theorem fcVal_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d' : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R'' : _root_.PositivityTheory.SiegelWeilFormula.RD_k d') (hMV : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R'') {Ψ : d'.Fn} (hΨ : Ψ ∈ d'.sch)
    (hv : d'.T Ψ ∈ R''.vac) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d'.Y) d'.b nb lam 𝓖) (T : nF σ d'.Y d'.b)
    (g : d'.G) :
    HolValueAt (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z) T g) (s0 d'.m d'.n)
      (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
  have hK := H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)
  have hsec := H.secK F E σ d' Ψ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hadd, hbd⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d' hc T g
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d'.Y) (fun f => fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv
  have hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) =
      iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g') := fun g' =>
    ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g')
      (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')
  have hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g =
      c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g := by
    intro c φ; simp only [fc, mul_assoc]; exact integral_const_mul _ _
  have hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n),
      iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) =
        iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
    intro i hi
    rw [hComm _ hs i]
    have : (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) =
        fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g' :=
      funext fun g' => by rw [hpt g' i hi]; ring
    rw [this, hsm]; ring
  refine wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)
  · have e1 : Ê z = fun g' => p.eval z * d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g' := funext (hfar z hz).2
    rw [e1, hsm]
  · rw [hder i hi.le, pderiv_lt p _ i hi, zero_mul]
end COne
section Deg
variable (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)
include H hIH hΦ hv in
/- English proof (translation)
Take `⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩` from `H.iwaQ F E σ d L x`. Establish `hΦk : d.om k Φ ∈ d.sch` using `_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d k hΦ`. Establish `hvk : d.T (d.om k Φ) ∈ R.vac` using `(H.vacK F E σ d R).1 Φ hΦ hv k hk`. Take `⟨Φ', hres, hv'⟩` from `(H.vacK F E σ d R).2.2 L R' _ hΦk hvk`. Establish `hΦ' : Φ' ∈ L.sd.sch` using `hres.1`.

Establish `hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0`. Introduce `g`. Use `L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)` as an intermediate fact. Rewrite `this` using `[Matrix.submatrix_zero]`. Then use the resulting hypothesis. Establish `hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀)`.

Introduce `g'`. Establish `hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch` using `_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d _ hΦk`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero d hΦ, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero L.sd hΦ', hx]`. Establish `e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ))`. Simplify using `only [map_mul, mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]`. Use `congr 2`. Simplify using `only [map_mul]`. Both sides reduce to the same expression.

Establish `hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2`. Unfold `s0`. Rewrite using `[← _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.Ln_k L]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hid : ∀ z, _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀`. Introduce `z`. Establish `ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n` using `by rw [hs']; ring`. Establish `hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) = (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) * L.sd.sec0 Φ' (g' * g₀))`. Introduce `g'`.

Rewrite using `[hf g', ex]`. Establish `e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ)`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha g']`. Rewrite using `[e1, COne.ht_cpow r _ hr]`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) * L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀)`. Use function extensionality and compare the values at `fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k`. Rewrite using `[hcs]`.

Simplify using `only [fc, mul_one, mul_assoc, integral_const_mul]`. Establish `hW` using `_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.fcVal_k H R' hIH hΦ' hv' hc' T' g₀`. Rewrite `hW` using `[hs']`. Establish `hsh` using `COne.hv_shift _ (s0 d.m d.n) (1 / 2) _ c r hr hW`. Establish `hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀`.

Rewrite using `[H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]`. Rewrite using `[(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.orb_smul_k]`. Conclude with `Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k L.sd g₀ hΦ')`. Introduce `X hX`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k]`.

Establish `h1` using `L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX`. Establish `hΨ` using `_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d (L.j g₀) hΦk`. Establish `h2` using `hTq _ hΨ 1 X hX`. Simplify using `only [map_one, one_mul, Module.End.one_apply] at h2`. Establish `h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X` using `h1`.

Rewrite using `[h1', hx]`. Establish `e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ))` using `by simp only [map_mul]; rfl`. Rewrite using `[e, h2]`. Establish `hfun : (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2)`. Use function extensionality and compare the values at `z`.

Rewrite using `[hid z, hs']`. Rewrite using `[hfun, hv1]`. Use `hsh using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cOneVal_pf_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) := by
  obtain ⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩ := H.iwaQ F E σ d L x
  have hΦk : d.om k Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d k hΦ
  have hvk : d.T (d.om k Φ) ∈ R.vac := (H.vacK F E σ d R).1 Φ hΦ hv k hk
  obtain ⟨Φ', hres, hv'⟩ := (H.vacK F E σ d R).2.2 L R' _ hΦk hvk
  have hΦ' : Φ' ∈ L.sd.sch := hres.1
  have hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0 := by
    intro g
    have := L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)
    rwa [Matrix.submatrix_zero] at this
  have hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀) := by
    intro g'
    have hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d _ hΦk
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero d hΦ, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero L.sd hΦ', hx]
    have e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ)) := by
      simp only [map_mul, mul_assoc]; rfl
    rw [e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]
    congr 2
    simp only [map_mul]; rfl
  have hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2 := by
    unfold s0; rw [← _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.Ln_k L]; push_cast; ring
  have hid : ∀ z, _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀ := by
    intro z
    have ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n := by rw [hs']; ring
    have hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) =
        (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) *
          L.sd.sec0 Φ' (g' * g₀)) := by
      intro g'
      rw [hf g', ex]
      have e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ) := by
        simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha g']
      rw [e1, COne.ht_cpow r _ hr]
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
      ring
    have hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) *
        d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
          L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀) :=
      funext fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g
    unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
    rw [hcs]
    simp only [fc, mul_one, mul_assoc, integral_const_mul]
  have hW := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.fcVal_k H R' hIH hΦ' hv' hc' T' g₀
  rw [hs'] at hW
  have hsh := COne.hv_shift _ (s0 d.m d.n) (1 / 2) _ c r hr hW
  have hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀ := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]
    rw [(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.orb_smul_k]
    · exact Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k L.sd g₀ hΦ')
    · intro X hX
      rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k]
      have h1 := L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX
      have hΨ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d (L.j g₀) hΦk
      have h2 := hTq _ hΨ 1 X hX
      simp only [map_one, one_mul, Module.End.one_apply] at h2
      have h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X := h1
      rw [h1', hx]
      have e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ)) := by simp only [map_mul]; rfl
      rw [e, h2]
  have hfun : (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2) := by
    funext z; rw [hid z, hs']
  rw [hfun, hv1]
  convert hsh using 1
  ring
end Deg
end PositivityTheory.SiegelWeilFormula.AStep
end
end
