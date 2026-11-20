import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGQLFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `h1` using `Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left (Bs.π h) (Bs.π_unitary h hh) (C.comp (Bs.π' h')) (A.comp (Bs.π' h'))`. Establish `h2` using `Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right (Bs.π' h') (Bs.π'_unitary h' hh') C A`. Unfold `B.hsInner at h1 h2`. Rewrite using `[h1, h2]`.
-/
theorem sm_inner_conj {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r Bs.z)
    (hh' : h' ∈ UWset k r Bs.z') (A C : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec ((Bs.π h).comp (A.comp (Bs.π' h')))) (B.hsVec ((Bs.π h).comp (C.comp (Bs.π' h')))) =
      inner ℂ (B.hsVec A) (B.hsVec C) := by
  have h1 := Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left (Bs.π h) (Bs.π_unitary h hh) (C.comp (Bs.π' h')) (A.comp (Bs.π' h'))
  have h2 := Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right (Bs.π' h') (Bs.π'_unitary h' hh') C A
  unfold B.hsInner at h1 h2
  rw [h1, h2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, hh, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, (Matrix.mul_one h).symm⟩`.
-/
theorem sm_slev {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h ∈ Q.Slev k r z (Fin.last r) :=
  ⟨h, hh, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, (Matrix.mul_one h).symm⟩

end

/- English proof (translation)
Introduce `hSE hGS Wp Wq _ _ _ _ _ _ P Bs hpl hk`. Take `⟨μ0, hC⟩` from `hSE Wp Wq P Bs hpl hk`. Set `Bs0 : B.RealPlaceData P.k P.r Wp Wq` to `{ Bs with μsec := μ0, sec := hC.1 }`. Take `⟨e0, he0, hid0⟩` from `hGS Wp Wq P Bs0 hpl hk hC`. Establish `hz` using `Bs.z_mem`.

Establish `hz'` using `Bs.z'_mem`. Establish `hT : Tz P.k P.r Bs.z = P.T` using `hpl.2.2.2.1`. Establish `hT' : Tz P.k P.r Bs.z' = P.T'` using `hpl.2.2.2.2.1`. Establish `hTT : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ`. Introduce `ζ hζ`.

Rewrite using `[hT, hT']`. Conclude with `hζ`. Use `set c1 : Fin P.r → ℂ := fun _ => 1 with hc1def`. Establish `hc1 : c1 ∈ OmX P.r` using `fun _ => one_ne_zero`. Establish `hRB : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π'` using `⟨Bs.k_pos, hz, hz', Bs.T_pos, Bs.T'_pos, hC.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩`.

Establish `hφ : ∀ ρ : M.Ty P, (NF.QR P.k P.r Bs.z Bs.z').indicator (fun q => e0 ρ q.2) ∈ NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π'`. Introduce `ρ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ContDiffOn ℝ ∞ (fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) (NF.QR P.k P.r Bs.z Bs.z')`. Use `(he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_` and prove the remaining obligations.

Use `show P.TT < Complex.normSq q.2`. Use `hq.2` as an intermediate fact. Rewrite `this` using `[hT, hT']`. Conclude with `this`. Conclude with `hc.congr fun q hq => Set.indicator_of_mem hq _`.

Introduce `q hq`. Rewrite using `[Set.indicator_of_mem hq]`. Establish `hq2 : P.TT < Complex.normSq q.2`. Use `hq.2` as an intermediate fact. Rewrite `this` using `[hT, hT']`.

Conclude with `this`. Conclude with `(he0.2 q.2 hq2).1 ρ`. Introduce `q hq`. Conclude with `Set.indicator_of_notMem hq _`. Use `choose Φr hΦr hrad using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB _ (hφ ρ)`.

Take `⟨e, he_def⟩ : ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), e = fun ρ ζ => (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)` from `⟨_, rfl⟩`. Establish `hdom : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z'` using `fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩`. Establish `hdom0 : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r μ0 ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z'` using `fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hC.1 (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩`. Establish `hdec : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z', NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h'`. Introduce `ζ hζ`.

Take `⟨h, hh, h', hh', he⟩` from `Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hC.1 (hdom ζ hζ).2.1 (hdom ζ hζ).2.2`. Rewrite `he` using `[Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec (hTT ζ hζ)]`. Conclude with `⟨h, hh, h', hh', he⟩`. Establish `hrad0 : ∀ ρ ζ, P.TT < Complex.normSq ζ → (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r μ0 ζ) = e0 ρ ζ`. Introduce `ρ ζ hζ`.

Establish `hq : (c1, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z'` using `⟨hc1, hTT ζ hζ⟩`. Establish `h1` using `congrFun (hrad ρ) (c1, ζ)`. Unfold `NF.radR at h1`. Rewrite `h1` using `[Set.indicator_of_mem hq, Set.indicator_of_mem hq]`. Conclude with `h1`.

Establish `htr : ∀ ρ ζ, P.TT < Complex.normSq ζ → ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z', NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' → e ρ ζ = (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h'))`. Introduce `ρ ζ hζ h hh h' hh' hd`. Rewrite using `[he_def]`. Use `show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) = _`. Rewrite using `[hd, ← hrad0 ρ ζ hζ]`.

Conclude with `(hΦr ρ).2.2 (c1, NF.muZ P.k P.r μ0 ζ) (hdom0 ζ hζ) h hh h' hh'`. Establish `hsmooth : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}`. Introduce `ρ`. Rewrite using `[he_def]`. Establish `hmZ : ContDiffOn ℝ ∞ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) {ζ : ℂ | P.TT < Complex.normSq ζ}` using `contDiffOn_const.prodMk ((Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).mono fun ζ hζ => hTT ζ hζ)`.

Establish `hopen : IsOpen {ζ : ℂ | P.TT < Complex.normSq ζ}` using `isOpen_lt continuous_const Complex.continuous_normSq`. Use `contDiffOn_of_locally_contDiffOn fun ζ₀ hζ₀ => ?_` and prove the remaining obligations. Take `⟨U, F, hU, hx₀U, hF, hΦF⟩` from `(hΦr ρ).2.1 _ (hdom ζ₀ hζ₀)`. Use `⟨{ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U, hmZ.continuousOn.isOpen_inter_preimage hopen hU, ⟨hζ₀, hx₀U⟩, ?_⟩` and prove the remaining obligations. Establish `hc : ContDiffOn ℝ ∞ (fun ζ : ℂ => F (c1, NF.muZ P.k P.r Bs.μsec ζ)) ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U))` using `hF.comp (hmZ.mono fun ζ hζ => hζ.1) fun ζ hζ => hζ.2.2`.

Conclude with `hc.congr fun ζ hζ => hΦF _ hζ.2.2 (hdom ζ hζ.1).2.1`. Establish `hrep` using `Bs.π_rep`. Establish `hrep'` using `Bs.π'_rep`. Establish `pmi : ∀ h ∈ UWset P.k P.r Bs.z, (Bs.π h).comp (Bs.π h⁻¹) = 1`. Introduce `h hh`.

Rewrite using `[← hrep.2 h hh h⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hrep.1]`. Establish `pim' : ∀ h' ∈ UWset P.k P.r Bs.z', (Bs.π' h'⁻¹).comp (Bs.π' h') = 1`. Introduce `h' hh'`. Rewrite using `[← hrep'.2 h'⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh') h' hh', Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', hrep'.1]`. Establish `hframe : IsFrameB P Bs e`.

Use `⟨hsmooth, fun ζ hζ => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `ρ p hp`. Rewrite using `[he_def]`. Use `show (Bs.π p.1).comp (((Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' p.2)) = (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)`. Rewrite using `[← (hΦr ρ).2.2 (c1, NF.muZ P.k P.r Bs.μsec ζ) (hdom ζ hζ) p.1 hp.1 p.2 hp.2.1]`.

Use `show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) = _`. Rewrite using `[hp.2.2]`. Introduce `ρ ρ'`. Take `⟨h, hh, h', hh', hd⟩` from `hdec ζ hζ`. Rewrite using `[htr ρ ζ hζ h hh h' hh' hd, htr ρ' ζ hζ h hh h' hh' hd, sm_inner_conj Bs hh hh']`.

Conclude with `(he0.2 ζ hζ).2.1 ρ ρ'`. Introduce `X hX`. Take `⟨h, hh, h', hh', hd⟩` from `hdec ζ hζ`. Establish `hhi` using `Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh`. Establish `hhi'` using `Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'`.

Use `set X0 := (Bs.π h⁻¹).comp (X.comp (Bs.π' h'⁻¹)) with hX0def`. Establish `e1 : ∀ Y : B.Mat P.k P.r, h⁻¹ * (h * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul]`. Establish `e2 : ∀ Y : B.Mat P.k P.r, h' * (h'⁻¹ * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul]`.

Establish `hX0 : X0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ`. Introduce `p hp`. Establish `hp1` using `hp.1`. Establish `hp2` using `hp.2.1`. Establish `hp3` using `hp.2.2`.

Establish `ht1 : h * p.1 * h⁻¹ ∈ UWset P.k P.r Bs.z` using `Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi`. Establish `ht2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z'` using `Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh'`. Establish `e3 : ∀ Y : B.Mat P.k P.r, p.1 * (NF.muZ P.k P.r μ0 ζ * (p.2 * Y)) = NF.muZ P.k P.r μ0 ζ * Y`. Introduce `Y`. Use `conv_rhs => rw [← hp3]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `ht : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ`. Use `⟨ht1, ht2, ?_⟩` and prove the remaining obligations. Use `show h * p.1 * h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * (h'⁻¹ * p.2 * h') = NF.muZ P.k P.r Bs.μsec ζ`. Rewrite using `[hd]`.

Simplify using `only [Matrix.mul_assoc, e1, e2, e3]`. Establish `hXt` using `hX _ ht`. Establish `hA : (Bs.π p.1).comp (Bs.π h⁻¹) = (Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))`. Rewrite using `[← hrep.2 _ hp1 _ hhi, ← hrep.2 _ hhi _ ht1]`. Use `congr 1`.

Simplify using `only [Matrix.mul_assoc, e1]`. Establish `hB : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹)`. Rewrite using `[← hrep'.2 _ hhi' _ hp2, ← hrep'.2 _ ht2 _ hhi']`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hX0def, ContinuousLinearMap.comp_assoc]`. Use `_ = ((Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))).comp (X.comp ((Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹))) := by rw [hA, hB]`. Use `_ = (Bs.π h⁻¹).comp (((Bs.π (h * p.1 * h⁻¹)).comp (X.comp (Bs.π' (h'⁻¹ * p.2 * h')))).comp (Bs.π' h'⁻¹)) := by simp only [ContinuousLinearMap.comp_assoc]`. Use `_ = X0 := by rw [hXt]`.

Establish `hXX : X = (Bs.π h).comp (X0.comp (Bs.π' h'))`. Establish `: (Bs.π h).comp (X0.comp (Bs.π' h')) = ((Bs.π h).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' h')))`. Simplify using `only [hX0def, ContinuousLinearMap.comp_assoc]`. Rewrite using `[this, pmi h hh, pim' h' hh']`. Use extensionality with `v`.

Both sides reduce to the same expression. Establish `hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) = inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0)`. Introduce `ρ`. Rewrite using `[htr ρ ζ hζ h hh h' hh' hd]`. Use `conv_lhs => rw [hXX]`.

Conclude with `sm_inner_conj Bs hh hh' _ _`. Establish `hsp0` using `(he0.2 ζ hζ).2.2 X0 hX0`. Establish `hrhs : ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ = ∑ ρ, inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) • (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h'))` using `Finset.sum_congr rfl fun ρ _ => by rw [hc ρ, htr ρ ζ hζ h hh h' hh' hd]`. Rewrite using `[hrhs]`. Use `conv_lhs => rw [hXX, hsp0]`.

Use extensionality with `v`. Simplify using `only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]`. Establish `hfam0 : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ → FamR P Bs0 Dc Φ`. Introduce `Dc Φ hF`. Take `⟨hO, hD, hM, hFF⟩` from `hF`.

Use `⟨hO, hD, fun q => ?_, hFF⟩` and prove the remaining obligations. Establish `hζ : P.TT < Complex.normSq q.1.2` using `q.2.2`. Take `⟨h, hh, h', hh', hd⟩` from `hdec q.1.2 hζ`. Establish `hg : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dc q.1.1` using `⟨(hdom q.1.2 hζ).2.1, hM q⟩`. Establish `h1` using `(hD q.1.1 q.2.1).2 _ hg h⁻¹ (sm_slev (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh)) h'⁻¹ (sm_slev (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'))`.

Establish `e3 : h⁻¹ * NF.muZ P.k P.r Bs.μsec q.1.2 * h'⁻¹ = NF.muZ P.k P.r μ0 q.1.2`. Rewrite using `[hd]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc h⁻¹ h, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]`. Rewrite `h1` using `[e3]`.

Conclude with `h1`. Establish `hraw : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ → ∀ ρ, rawR P Bs.μsec e Φ ρ = rawR P μ0 e0 Φ ρ`. Introduce `Dc Φ hF ρ`. Establish `hF0` using `hfam0 Dc Φ hF`. Use function extensionality and compare the values at `q`.

Establish `hζ : P.TT < Complex.normSq q.1.2` using `q.2.2`. Take `⟨h, hh, h', hh', hd⟩` from `hdec q.1.2 hζ`. Unfold `rawR`. Use `congr 1`. Rewrite using `[htr ρ q.1.2 hζ h hh h' hh' hd, hd]`.

Establish `hg : NF.muZ P.k P.r μ0 q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dc q.1.1` using `⟨(hdom0 q.1.2 hζ).2.1, hF0.2.2.1 q⟩`. Rewrite using `[(hF.2.2.2.2 q.1.1 q.2.1).2.2.2 _ hg h hh h' hh']`. Conclude with `sm_inner_conj Bs hh hh' _ _`. Use `⟨e, hframe, fun Dc Φ hF Y a b ρ => ?_⟩` and prove the remaining obligations. Establish `hQF` using `Formalism.FourierDecayAlt.P.CutMP.Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hF Y a b`.

Rewrite using `[hraw Dc _ hQF ρ]`. Establish `hfun : (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) = fun ρ' => MA.toSm P (rawR P μ0 e0 Φ ρ')`. Use function extensionality and compare the values at `fun ρ' => by rw [hraw Dc Φ hF ρ']`. Rewrite using `[hfun]`. Conclude with `hid0 Dc Φ (hfam0 Dc Φ hF) Y a b ρ`.
-/
theorem section_move_holds : SecMove := by
  intro hSE hGS Wp Wq _ _ _ _ _ _ P Bs hpl hk
  obtain ⟨μ0, hC⟩ := hSE Wp Wq P Bs hpl hk
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hC.1 }
  obtain ⟨e0, he0, hid0⟩ := hGS Wp Wq P Bs0 hpl hk hC
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hTT : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    intro ζ hζ
    rw [hT, hT']
    exact hζ
  set c1 : Fin P.r → ℂ := fun _ => 1 with hc1def
  have hc1 : c1 ∈ OmX P.r := fun _ => one_ne_zero

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' :=
    ⟨Bs.k_pos, hz, hz', Bs.T_pos, Bs.T'_pos, hC.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩

  have hφ : ∀ ρ : M.Ty P, (NF.QR P.k P.r Bs.z Bs.z').indicator (fun q => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨?_, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) (NF.QR P.k P.r Bs.z Bs.z') := by
        refine (he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_
        show P.TT < Complex.normSq q.2
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact hc.congr fun q hq => Set.indicator_of_mem hq _
    · intro q hq
      rw [Set.indicator_of_mem hq]
      have hq2 : P.TT < Complex.normSq q.2 := by
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact (he0.2 q.2 hq2).1 ρ
    · intro q hq
      exact Set.indicator_of_notMem hq _
  choose Φr hΦr hrad using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB _ (hφ ρ)
  obtain ⟨e, he_def⟩ : ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp),
      e = fun ρ ζ => (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) := ⟨_, rfl⟩

  have hdom : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      (c1, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdom0 : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r μ0 ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hC.1 (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdec : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' := by
    intro ζ hζ
    obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hC.1
      (hdom ζ hζ).2.1 (hdom ζ hζ).2.2
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec (hTT ζ hζ)] at he
    exact ⟨h, hh, h', hh', he⟩

  have hrad0 : ∀ ρ ζ, P.TT < Complex.normSq ζ → (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r μ0 ζ) = e0 ρ ζ := by
    intro ρ ζ hζ
    have hq : (c1, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc1, hTT ζ hζ⟩
    have h1 := congrFun (hrad ρ) (c1, ζ)
    unfold NF.radR at h1
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq] at h1
    exact h1

  have htr : ∀ ρ ζ, P.TT < Complex.normSq ζ → ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' →
      e ρ ζ = (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) := by
    intro ρ ζ hζ h hh h' hh' hd
    rw [he_def]
    show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) = _
    rw [hd, ← hrad0 ρ ζ hζ]
    exact (hΦr ρ).2.2 (c1, NF.muZ P.k P.r μ0 ζ) (hdom0 ζ hζ) h hh h' hh'

  have hsmooth : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ} := by
    intro ρ
    rw [he_def]
    have hmZ : ContDiffOn ℝ ∞ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      contDiffOn_const.prodMk ((Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).mono fun ζ hζ => hTT ζ hζ)
    have hopen : IsOpen {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    refine contDiffOn_of_locally_contDiffOn fun ζ₀ hζ₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := (hΦr ρ).2.1 _ (hdom ζ₀ hζ₀)
    refine ⟨{ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U,
      hmZ.continuousOn.isOpen_inter_preimage hopen hU, ⟨hζ₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun ζ : ℂ => F (c1, NF.muZ P.k P.r Bs.μsec ζ))
        ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩
          ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U)) :=
      hF.comp (hmZ.mono fun ζ hζ => hζ.1) fun ζ hζ => hζ.2.2
    exact hc.congr fun ζ hζ => hΦF _ hζ.2.2 (hdom ζ hζ.1).2.1

  have hrep := Bs.π_rep
  have hrep' := Bs.π'_rep
  have pmi : ∀ h ∈ UWset P.k P.r Bs.z, (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    intro h hh
    rw [← hrep.2 h hh h⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hrep.1]
  have pim' : ∀ h' ∈ UWset P.k P.r Bs.z', (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    intro h' hh'
    rw [← hrep'.2 h'⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh') h' hh', Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', hrep'.1]

  have hframe : IsFrameB P Bs e := by
    refine ⟨hsmooth, fun ζ hζ => ⟨?_, ?_, ?_⟩⟩
    · intro ρ p hp
      rw [he_def]
      show (Bs.π p.1).comp (((Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' p.2)) =
        (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)
      rw [← (hΦr ρ).2.2 (c1, NF.muZ P.k P.r Bs.μsec ζ) (hdom ζ hζ) p.1 hp.1 p.2 hp.2.1]
      show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) = _
      rw [hp.2.2]
    · intro ρ ρ'
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      rw [htr ρ ζ hζ h hh h' hh' hd, htr ρ' ζ hζ h hh h' hh' hd, sm_inner_conj Bs hh hh']
      exact (he0.2 ζ hζ).2.1 ρ ρ'
    · intro X hX
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
      set X0 := (Bs.π h⁻¹).comp (X.comp (Bs.π' h'⁻¹)) with hX0def
      have e1 : ∀ Y : B.Mat P.k P.r, h⁻¹ * (h * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul]
      have e2 : ∀ Y : B.Mat P.k P.r, h' * (h'⁻¹ * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul]
      have hX0 : X0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := by
        intro p hp
        have hp1 := hp.1
        have hp2 := hp.2.1
        have hp3 := hp.2.2
        have ht1 : h * p.1 * h⁻¹ ∈ UWset P.k P.r Bs.z :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi
        have ht2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh'
        have e3 : ∀ Y : B.Mat P.k P.r, p.1 * (NF.muZ P.k P.r μ0 ζ * (p.2 * Y)) = NF.muZ P.k P.r μ0 ζ * Y := by
          intro Y
          conv_rhs => rw [← hp3]
          simp only [Matrix.mul_assoc]
        have ht : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ := by
          refine ⟨ht1, ht2, ?_⟩
          show h * p.1 * h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * (h'⁻¹ * p.2 * h') = NF.muZ P.k P.r Bs.μsec ζ
          rw [hd]
          simp only [Matrix.mul_assoc, e1, e2, e3]
        have hXt := hX _ ht
        have hA : (Bs.π p.1).comp (Bs.π h⁻¹) = (Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹)) := by
          rw [← hrep.2 _ hp1 _ hhi, ← hrep.2 _ hhi _ ht1]
          congr 1
          simp only [Matrix.mul_assoc, e1]
        have hB : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
          rw [← hrep'.2 _ hhi' _ hp2, ← hrep'.2 _ ht2 _ hhi']
          congr 1
          simp only [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
        calc (Bs.π p.1).comp (X0.comp (Bs.π' p.2))
            = ((Bs.π p.1).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' p.2))) := by
              simp only [hX0def, ContinuousLinearMap.comp_assoc]
          _ = ((Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))).comp
                (X.comp ((Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹))) := by rw [hA, hB]
          _ = (Bs.π h⁻¹).comp (((Bs.π (h * p.1 * h⁻¹)).comp (X.comp (Bs.π' (h'⁻¹ * p.2 * h')))).comp
                (Bs.π' h'⁻¹)) := by simp only [ContinuousLinearMap.comp_assoc]
          _ = X0 := by rw [hXt]
      have hXX : X = (Bs.π h).comp (X0.comp (Bs.π' h')) := by
        have : (Bs.π h).comp (X0.comp (Bs.π' h')) =
            ((Bs.π h).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' h'))) := by
          simp only [hX0def, ContinuousLinearMap.comp_assoc]
        rw [this, pmi h hh, pim' h' hh']
        ext v
        rfl
      have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) = inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) := by
        intro ρ
        rw [htr ρ ζ hζ h hh h' hh' hd]
        conv_lhs => rw [hXX]
        exact sm_inner_conj Bs hh hh' _ _
      have hsp0 := (he0.2 ζ hζ).2.2 X0 hX0
      have hrhs : ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ =
          ∑ ρ, inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) • (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) :=
        Finset.sum_congr rfl fun ρ _ => by rw [hc ρ, htr ρ ζ hζ h hh h' hh' hd]
      rw [hrhs]
      conv_lhs => rw [hXX, hsp0]
      ext v
      simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]

  have hfam0 : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ → FamR P Bs0 Dc Φ := by
    intro Dc Φ hF
    obtain ⟨hO, hD, hM, hFF⟩ := hF
    refine ⟨hO, hD, fun q => ?_, hFF⟩
    have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
    obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
    have hg : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dc q.1.1 :=
      ⟨(hdom q.1.2 hζ).2.1, hM q⟩
    have h1 := (hD q.1.1 q.2.1).2 _ hg h⁻¹ (sm_slev (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh)) h'⁻¹
      (sm_slev (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'))
    have e3 : h⁻¹ * NF.muZ P.k P.r Bs.μsec q.1.2 * h'⁻¹ = NF.muZ P.k P.r μ0 q.1.2 := by
      rw [hd]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h⁻¹ h, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    rw [e3] at h1
    exact h1
  have hraw : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ → ∀ ρ, rawR P Bs.μsec e Φ ρ = rawR P μ0 e0 Φ ρ := by
    intro Dc Φ hF ρ
    have hF0 := hfam0 Dc Φ hF
    funext q
    have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
    obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
    unfold rawR
    congr 1
    rw [htr ρ q.1.2 hζ h hh h' hh' hd, hd]
    have hg : NF.muZ P.k P.r μ0 q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dc q.1.1 :=
      ⟨(hdom0 q.1.2 hζ).2.1, hF0.2.2.1 q⟩
    rw [(hF.2.2.2.2 q.1.1 q.2.1).2.2.2 _ hg h hh h' hh']
    exact sm_inner_conj Bs hh hh' _ _
  refine ⟨e, hframe, fun Dc Φ hF Y a b ρ => ?_⟩
  have hQF := Formalism.FourierDecayAlt.P.CutMP.Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hF Y a b
  rw [hraw Dc _ hQF ρ]
  have hfun : (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) = fun ρ' => MA.toSm P (rawR P μ0 e0 Φ ρ') :=
    funext fun ρ' => by rw [hraw Dc Φ hF ρ']
  rw [hfun]
  exact hid0 Dc Φ (hfam0 Dc Φ hF) Y a b ρ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
