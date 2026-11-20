import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LocOpCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
open PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Set `g` to `(GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)`. Establish `hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)` using `GlobalTheory.RealLift.indicator_intPts_mem_SB`. Set `Ψ : Mx F E d.m d.n → ℂ` to `fun X => (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2`. Establish `hΨ : Ψ ∈ R.away w` using `Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩`. Establish `h0 : Ψ 0 ≠ 0`.

Establish `hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0`. Use function extensionality and compare the values at `k`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd`. Rewrite using `[Matrix.zero_apply, map_zero, Finsupp.zero_apply]`. Both sides reduce to the same expression.

Establish `hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1`. Rewrite using `[hc]`. Conclude with `Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _`. Establish `hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _`. Simplify `hp` using `[Ψ, hg0]`.

Use `⟨Ψ, ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun hz => h0 (by rw [hz]; rfl), fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩, h0⟩` and prove the remaining obligations.
-/
theorem goodAway0_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : ∃ Ψ, R.GoodAway w Ψ ∧ Ψ 0 ≠ 0 := by
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have h0 : Ψ 0 ≠ 0 := by
    have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
      funext k
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
      rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
      rfl
    have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
      rw [hc]
      exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
    have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
    simpa [Ψ, hg0] using hp
  refine ⟨Ψ, ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun hz => h0 (by rw [hz]; rfl), fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩, h0⟩
/- English proof (translation)
Introduce `P u`. Take `⟨Ψ, hΨ, hΨ0⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KLI.goodAway0_k R w`. Take `⟨Φ, hΦ, hTΦ⟩` from `R.exists_adm hT hΨ (isSw_fP P)`. Take `⟨Z, hZw, hZf, hZu⟩` from `R.loc_surj w 0 u`. Establish `hΨZ : Ψ Z = Ψ 0` using `by simpa using hΨ.1 0 Z hZw hZf`.

Establish `hZu' : R.loc w Z = u` using `by simpa using hZu`. Establish `key : ∀ y, L y (fP P) u = d.T (d.om (R.ι w y) Φ) Z / Ψ 0`. Introduce `y`. Establish `e` using `congrFun ((hL y (fP P) (isSw_fP P)).2 Ψ hΨ.1 Φ hΦ hTΦ) Z`. Rewrite using `[e]`.

Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZu', hΨZ]`. Clear the denominators using the available nonvanishing facts. Use `set v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) := Z * (incM F d.b.1.toCols₂)ᵀ with hv_def`. Establish `hfv : finOne F • v = 0` using `by rw [hv_def, ← Matrix.smul_mul, hZf, Matrix.zero_mul]`. Establish `hev : finOne F • d.dd.e v = 0` using `by rw [← LinearEquiv.map_smul, hfv, map_zero]`.

Set `π2 : AF F →+* FiniteAdeleRing (𝓞 F) F` to `RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)`. Establish `h1 : π2 (finOne F) = 1` using `rfl`. Establish `hv : ∀ i, ((d.dd.e v).1 i).2 = 0 ∧ ((d.dd.e v).2 i).2 = 0`. Introduce `i`. Establish `e1` using `congrFun (congrArg Prod.fst hev) i`.

Establish `e2` using `congrFun (congrArg Prod.snd hev) i`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] at e1 e2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `congrArg π2 e1` as an intermediate fact. Rewrite `this` using `[map_mul, h1, one_mul, map_zero]`.

Conclude with `this`. Use `congrArg π2 e2` as an intermediate fact. Rewrite `this` using `[map_mul, h1, one_mul, map_zero]`. Conclude with `this`. Establish `hadm` using `rho_adm F d.B.ψ d.ok.good.std d.ok.dbl.adm (d.dd.e v) hv`.

Establish `hc` using `d.ok.dbl.weil.2.1.cont _ hadm Φ hΦ`. Use `((hc.comp (R.cont w)).div_const (Ψ 0)).congr fun y => (key y).symm` and prove the remaining obligations.
-/
theorem locOp_cont_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    ∀ (P : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ), Continuous fun y => L y (fP P) u := by
  intro P u
  obtain ⟨Ψ, hΨ, hΨ0⟩ := _root_.PositivityTheory.SiegelWeilFormula.KLI.goodAway0_k R w
  obtain ⟨Φ, hΦ, hTΦ⟩ := R.exists_adm hT hΨ (isSw_fP P)
  obtain ⟨Z, hZw, hZf, hZu⟩ := R.loc_surj w 0 u
  have hΨZ : Ψ Z = Ψ 0 := by simpa using hΨ.1 0 Z hZw hZf
  have hZu' : R.loc w Z = u := by simpa using hZu
  have key : ∀ y, L y (fP P) u = d.T (d.om (R.ι w y) Φ) Z / Ψ 0 := by
    intro y
    have e := congrFun ((hL y (fP P) (isSw_fP P)).2 Ψ hΨ.1 Φ hΦ hTΦ) Z
    rw [e]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZu', hΨZ]
    field_simp
  set v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) := Z * (incM F d.b.1.toCols₂)ᵀ with hv_def
  have hfv : finOne F • v = 0 := by rw [hv_def, ← Matrix.smul_mul, hZf, Matrix.zero_mul]
  have hev : finOne F • d.dd.e v = 0 := by rw [← LinearEquiv.map_smul, hfv, map_zero]
  let π2 : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : π2 (finOne F) = 1 := rfl
  have hv : ∀ i, ((d.dd.e v).1 i).2 = 0 ∧ ((d.dd.e v).2 i).2 = 0 := by
    intro i
    have e1 := congrFun (congrArg Prod.fst hev) i
    have e2 := congrFun (congrArg Prod.snd hev) i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply] at e1 e2
    refine ⟨?_, ?_⟩
    · have := congrArg π2 e1
      rw [map_mul, h1, one_mul, map_zero] at this
      exact this
    · have := congrArg π2 e2
      rw [map_mul, h1, one_mul, map_zero] at this
      exact this
  have hadm := rho_adm F d.B.ψ d.ok.good.std d.ok.dbl.adm (d.dd.e v) hv
  have hc := d.ok.dbl.weil.2.1.cont _ hadm Φ hΦ
  refine ((hc.comp (R.cont w)).div_const (Ψ 0)).congr fun y => (key y).symm
end PositivityTheory.SiegelWeilFormula.KLI
end
end
