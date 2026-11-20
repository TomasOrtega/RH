import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovFund

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def reix (X : HidaSetting D) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) ≃ᵐ X.B.I.Ginf :=
  MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm

/- English proof (translation)
Conclude with `MeasurableEquiv.piCongrLeft_apply_apply (β := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm p τ`.
-/
theorem reix_apply (p : ∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (τ : D.what₂.Tau) :
    reix X p (vOf X τ) = p τ := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm p τ

/- English proof (translation)
Use `conv_rhs => rw [← (reix X).apply_symm_apply x]`. Conclude with `(reix_apply _ τ).symm`.
-/
theorem reix_symm (x : X.B.I.Ginf) (τ : D.what₂.Tau) : (reix X).symm x τ = x (vOf X τ) := by
  conv_rhs => rw [← (reix X).apply_symm_apply x]
  exact (reix_apply _ τ).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trI_apply (x : X.B.I.Ginf) (τ : D.what₂.Tau) : trI C x τ = GlobalTheory.PullbackComparison.eM C τ (x (vOf X τ)) := rfl

/- English proof (translation)
Use `choose g hg hgf using fun τ : D.what₂.Tau => (GlobalTheory.PullbackComparison.eM_emb C τ).exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)`. Use `MeasurableEmbedding.of_measurable_inverse (g := fun m => reix X (fun τ => g τ (m τ))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `measurable_pi_lambda _ fun τ => (GlobalTheory.PullbackComparison.eM_emb C τ).measurable.comp (measurable_pi_apply (vOf X τ))`. Establish `hR : Set.range (trI C) = Set.univ.pi fun τ => Set.range (GlobalTheory.PullbackComparison.eM C τ)`. Use extensionality with `m`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ τ _`. Conclude with `⟨x (vOf X τ), (trI_apply C x τ).symm⟩`. Introduce `hm choose a ha using fun τ => hm τ (Set.mem_univ τ)`. Use `⟨reix X a, funext fun τ => ?_⟩` and prove the remaining obligations.

Rewrite using `[trI_apply, reix_apply, ha]`. Rewrite using `[hR]`. Conclude with `MeasurableSet.univ_pi fun τ => (GlobalTheory.PullbackComparison.eM_emb C τ).measurableSet_range`. Conclude with `(reix X).measurable.comp (measurable_pi_lambda _ fun τ => (hg τ).comp (measurable_pi_apply τ))`. Introduce `x`.

Establish `h1 : (fun τ => g τ (trI C x τ)) = (reix X).symm x`. Use function extensionality and compare the values at `τ`. Rewrite using `[trI_apply, reix_symm]`. Conclude with `congrFun (hgf τ) _`. Simplify using `only [h1, MeasurableEquiv.apply_symm_apply]`.
-/
theorem trI_emb : MeasurableEmbedding (trI C) := by
  choose g hg hgf using fun τ : D.what₂.Tau =>
    (GlobalTheory.PullbackComparison.eM_emb C τ).exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun m => reix X (fun τ => g τ (m τ))) ?_ ?_ ?_ ?_
  · exact measurable_pi_lambda _ fun τ =>
      (GlobalTheory.PullbackComparison.eM_emb C τ).measurable.comp (measurable_pi_apply (vOf X τ))
  · have hR : Set.range (trI C) = Set.univ.pi fun τ => Set.range (GlobalTheory.PullbackComparison.eM C τ) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩ τ _
        exact ⟨x (vOf X τ), (trI_apply C x τ).symm⟩
      · intro hm
        choose a ha using fun τ => hm τ (Set.mem_univ τ)
        refine ⟨reix X a, funext fun τ => ?_⟩
        rw [trI_apply, reix_apply, ha]
    rw [hR]
    exact MeasurableSet.univ_pi fun τ => (GlobalTheory.PullbackComparison.eM_emb C τ).measurableSet_range
  · exact (reix X).measurable.comp
      (measurable_pi_lambda _ fun τ => (hg τ).comp (measurable_pi_apply τ))
  · intro x
    have h1 : (fun τ => g τ (trI C x τ)) = (reix X).symm x := by
      funext τ
      rw [trI_apply, reix_symm]
      exact congrFun (hgf τ) _
    simp only [h1, MeasurableEquiv.apply_symm_apply]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hv : (q * y) (vOf X τ) = q (vOf X τ) * y (vOf X τ)` using `rfl`. Rewrite using `[trI_apply C (q * y), hv, GlobalTheory.PullbackComparison.eM_mul]`. Both sides reduce to the same expression.
-/
theorem trI_mul (q y : X.B.I.Ginf) : GlobalTheory.DegVol.mulP (trI C q) (trI C y) = trI C (q * y) := by
  funext τ
  have hv : (q * y) (vOf X τ) = q (vOf X τ) * y (vOf X τ) := rfl
  rw [trI_apply C (q * y), hv, GlobalTheory.PullbackComparison.eM_mul]
  rfl

/- English proof (translation)
Establish `hr : ∀ τ, x τ ∈ Set.range (GlobalTheory.PullbackComparison.eM C τ)` using `fun τ => GlobalTheory.PullbackComparison.uh_range C τ (hx τ).1.1`. Use `choose a ha using hr`. Use `⟨reix X a, ?_, funext fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.PullbackComparison.rset_iff C t]`. Introduce `τ`.

Rewrite using `[reix_apply, ha]`. Conclude with `hx τ`. Rewrite using `[trI_apply, reix_apply, ha]`.
-/
theorem exists_pre {Y : Full X} {u : D.what₂.Word} (t : GT Y u) {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hx : x ∈ GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) :
    ∃ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, trI C y = x := by
  have hr : ∀ τ, x τ ∈ Set.range (GlobalTheory.PullbackComparison.eM C τ) := fun τ =>
    GlobalTheory.PullbackComparison.uh_range C τ (hx τ).1.1
  choose a ha using hr
  refine ⟨reix X a, ?_, funext fun τ => ?_⟩
  · rw [GlobalTheory.PullbackComparison.rset_iff C t]
    intro τ
    rw [reix_apply, ha]
    exact hx τ
  · rw [trI_apply, reix_apply, ha]

/- English proof (translation)
Introduce `D X Y u C t K hK`. Use `⟨(trI_emb C).measurableSet_image.2 hK.1, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `exists_pre C t hx`. Take `⟨q, ⟨hq, hqK⟩, huniq⟩` from `hK.2 y hy`.

Use `⟨trI C q, ⟨⟨q, hq, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[trI_mul]`. Conclude with `⟨q * y, hqK, rfl⟩`. Introduce and unpack `m ⟨⟨q', hq', rfl⟩, hm⟩`. Rewrite `hm` using `[trI_mul]`.

Take `⟨z, hz, hzq⟩` from `hm`. Establish `hzq' : z = q' * y` using `(trI_emb C).injective hzq`. Rewrite using `[huniq q' ⟨hq', by rw [← hzq']; exact hz⟩]`.
-/
theorem isFund_image : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (t : GT Y u) (K : Set X.B.I.Ginf), FundR t K → GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.TermOp.ROinf t) (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) (trI C '' K) := by
  intro D X Y u C t K hK
  refine ⟨(trI_emb C).measurableSet_image.2 hK.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := exists_pre C t hx
  obtain ⟨q, ⟨hq, hqK⟩, huniq⟩ := hK.2 y hy
  refine ⟨trI C q, ⟨⟨q, hq, rfl⟩, ?_⟩, ?_⟩
  · rw [trI_mul]
    exact ⟨q * y, hqK, rfl⟩
  · rintro m ⟨⟨q', hq', rfl⟩, hm⟩
    rw [trI_mul] at hm
    obtain ⟨z, hz, hzq⟩ := hm
    have hzq' : z = q' * y := (trI_emb C).injective hzq
    rw [huniq q' ⟨hq', by rw [← hzq']; exact hz⟩]

end GlobalTheory.CovFund
