import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.UpRelationSourceUnique
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

/- English proof (translation)
Simplify using `only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem sum_ite_smul {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (σ : ι) (Q : ι → V) :
    (∑ ρ, (if ρ = σ then (1 : ℂ) else 0) • Q ρ) = Q σ := by
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hk hcs X d hA l hl Pr hPr π ζ hζ X0 hX0`. Take `⟨hpl, hL, hS, hRel, hQQ⟩` from `hA`. Establish `hH : GTHyp P Bs X d` using `⟨hpl, hk, hcs, hL, hS, hRel, hQQ⟩`. Take `⟨e, he, hkF⟩` from `gauge_kappa_holds Wp Wq P Bs X d hH`. Take `⟨Qs, hQ⟩` from `gauge_kappa_pointwise_holds Wp Wq P Bs X d hH`.

Take `⟨s, t, hst, hSL⟩` from `gTSSLocal_of_radT radial_torus_local_holds Wp Wq P Bs X d hH e he hkF`. Establish `hadj` using `second_shift_adjoint_pointwise Wp Wq P Bs X d hH e he hkF s t hst hSL l hl`. Establish `hTz` using `tz_TT P Bs hpl`. Establish `hRB` using `radBase_of P Bs hpl`. Establish `hζT : P.TT < Complex.normSq ζ` using `hζ`.

Establish `hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'`. Introduce `ρ`. Use `⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩` and prove the remaining obligations. Use `show P.TT < Complex.normSq q.2`. Rewrite using `[← hTz]`.

Conclude with `hq.2`. Simplify using `[Set.indicator_of_mem hq]`. Rewrite using `[Set.indicator_of_mem hq]`. Conclude with `(he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ`. Simplify using `[Set.indicator_of_notMem hq]`.

Use `choose Ψ0 hΨ0 hΨr using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)`. Set `Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'` to `fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩`. Establish `hq : ((c1 P.r, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z'` using `⟨constant_one_mem_nonvanishing P.r, by rw [hTz]; exact hζ⟩`. Establish `hΨ : ∀ ρ, (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ`. Introduce `ρ`.

Establish `h` using `congrFun (hΨr ρ) (c1 P.r, ζ)`. Simplify using `only [NF.radR, Set.indicator_of_mem hq] at h`. Conclude with `h`. Establish `hval : ∀ Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ`. Introduce `Z`.

Establish `hmem` using `(Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Z.2).2.1 (c1 P.r, ζ) hq`. Simplify `hmem` using `only [NF.radR, Set.indicator_of_mem hq]`. Establish `hexp` using `(he.2 ζ hζT).2.2`. Establish `hδ : ∀ ρ σ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e σ ζ)) = if ρ = σ then (1 : ℂ) else 0` using `(he.2 ζ hζT).2.1`. Set `q : MA.Qp P.r P.TT` to `⟨(c1 P.r, ζ), fun _ => one_ne_zero, hζT⟩`.

Use `set w : ℂ := ((wR P.k P.TT ζ : ℝ) : ℂ) with hwdef`. Establish `hw : w ≠ 0` using `wRc_ne P hζ`. Establish `hraw : ∀ (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P), rawR P Bs.μsec e Z ρ q = w * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Z (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ)))` using `fun Z ρ => rfl`. Establish `hrawΨ : ∀ σ ρ, rawR P Bs.μsec e (Ψ σ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = w * (if ρ = σ then (1 : ℂ) else 0)`. Introduce `σ ρ`.

Rewrite using `[hraw, hΨ σ, hδ]`. Establish `hmulapply : ∀ (A C : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), (A * C).1 Z = A.1 (C.1 Z)` using `fun A C Z => rfl`. Establish `hκpt : ∀ (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ)).comp (∑ ρ, f ρ …` using `fun f Z => hQ.2.2.2 f Z q`. Establish `hK0 : ∀ σ, e σ ζ ∈ Line P Bs Pr σ ζ`. Introduce `σ`.

Use `(lineQ P Bs X d hH Qs hQ Pr hPr ζ hζ σ (e σ ζ) ((he.2 ζ hζT).1 σ)).2 ?_` and prove the remaining obligations. Establish `h1` using `hκpt (fun ρ => if ρ = σ then (1 : ℂ) else 0) (Ψ σ)`. Rewrite `h1` using `[sum_ite_smul, hΨ σ]`. Rewrite using `[← h1, hexp _ (hval _)]`. Establish `hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((((d.κ (fun ρ => if ρ = σ then (1 : ℂ) else 0)).1 (Ψ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ))) = if ρ = σ then (1 : ℂ) else 0`.

Introduce `ρ`. Establish `h2` using `SSAdjH.kap_pt P Bs hpl hk e he d hkF (fun ρ => if ρ = σ then (1 : ℂ) else 0) (Ψ σ) ρ q`. Rewrite `h2` using `[hraw, hrawΨ]`. Distinguish the cases in `hρ : ρ = σ`. Rewrite `h2`, the goal using `[if_pos hρ]`.

Apply `mul_left_cancel₀ hw` to reduce the goal to its premises. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2`, the goal using `[if_neg hρ]`. Apply `mul_left_cancel₀ hw` to reduce the goal to its premises.

Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `set a : M.Ty P → ℂ := fun σ => inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X0) with hadef`. Set `Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'` to `∑ σ, a σ • Ψ σ`.

Establish `hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r), ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g = ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g`. Introduce `G c g`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]`. Establish `hΦv : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = X0`. Rewrite using `[hsumv]`.

Use `conv_rhs => rw [hexp X0 hX0.1]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hΨ σ]`. Establish `hrawΦ : ∀ ρ, rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = w * a ρ`. Introduce `ρ`.

Rewrite using `[hraw, hΦv]`. Establish `hXQ : X0.comp (Qs π) = X0` using `(lineQ P Bs X d hH Qs hQ Pr hPr ζ hζ π X0 hX0.1).1 hX0`. Establish `hK1 : ∀ σ, σ ≠ π → a σ = 0`. Introduce `σ hσ`. Establish `h1` using `hκpt (fun ρ => if ρ = π then (1 : ℂ) else 0) Φ`.

Rewrite `h1` using `[sum_ite_smul, hΦv, hXQ]`. Establish `h2` using `SSAdjH.kap_pt P Bs hpl hk e he d hkF (fun ρ => if ρ = π then (1 : ℂ) else 0) Φ σ q`. Rewrite `h2` using `[hraw, h1, hrawΦ, if_neg hσ, zero_mul]`. Conclude with `(mul_eq_zero.1 h2).resolve_left hw`. Establish `hSSΨ : ∀ σ, rawR P Bs.μsec e ((((d.SS l).1 (Ψ π) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = s l σ π ζ * w`.

Introduce `σ`. Rewrite using `[(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl (Ψ π) σ q).1]`. Simplify using `only [hrawΨ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Establish `hK2 : ∀ ρ', ¬ M.Up P l π ρ' → s l ρ' π ζ = 0`.

Introduce `ρ' hn`. Establish `hcond : ∀ ρ ρ'', M.Up P l ρ ρ'' → (fun x => if M.Up P l π x then (1 : ℂ) else 0) ρ'' = (fun x => if x = π then (1 : ℂ) else 0) ρ`. Introduce `ρ ρ'' hU`. Simplify using `only`. Distinguish the cases in `hρ : ρ = π`.

Substitute `hρ` using the available equality. Rewrite using `[if_pos hU, if_pos rfl]`. Establish `hn2 : ¬ M.Up P l π ρ''` using `fun h2 => hρ (up_relation_source_unique hU h2)`. Rewrite using `[if_neg hn2, if_neg hρ]`. Establish `heq` using `hRel.2.2.2.1 l _ _ hcond`.

Establish `hz` using `congrArg (fun A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => A.1 (Ψ π)) heq`. Simplify using `only [hmulapply] at hz`. Establish `h3` using `congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' => rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q) hz`. Apply the tactic sequence `try dsimp only at h3`. Rewrite `h3` using `[SSAdjH.kap_pt P Bs hpl hk e he d hkF, hSSΨ, (SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl _ ρ' q).1]`.

Apply the tactic sequence `try dsimp only at h3`. Rewrite `h3` using `[if_neg hn, zero_mul]`. Rewrite using `[Finset.sum_eq_single π (fun b _ hb => by`. Rewrite using `[SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ]`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[if_neg hb]`. Use the proof step `ring)`. Use the proof step `(fun h => absurd (Finset.mem_univ π) h)] at h3`. Rewrite `h3` using `[SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ]`. Apply the tactic sequence `try dsimp only at h3`.

Establish `h4 : s l ρ' π ζ * w = 0`. Establish `h5 : (0 : ℂ) = s l ρ' π ζ * ((if π = π then (1 : ℂ) else 0) * (w * if π = π then (1 : ℂ) else 0))` using `h3`. Rewrite `h5` using `[if_pos rfl]`. Take the linear combination `-h5`. Conclude with `(mul_eq_zero.1 h4).resolve_right hw`.

Establish `hK3 : ∑ σ, star (s l σ π ζ) * s l σ π ζ = ((M.Nrm P l π : ℝ) : ℂ)`. Establish `heq` using `hRel.2.2.2.2.2 l hl`. Establish `hz` using `congrArg (fun A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => A.1 (Ψ π)) heq`. Simplify using `only [hmulapply] at hz`. Establish `h3` using `congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' => rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) π q) hz`.

Apply the tactic sequence `try dsimp only at h3`. Rewrite `h3` using `[(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl _ π q).2, SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ]`. Apply the tactic sequence `try dsimp only at h3`. Rewrite `h3` using `[if_pos rfl]`. Establish `h4 : ∀ σ, t l π σ q.1.2 * rawR P Bs.μsec e ((((d.SS l).1 (Ψ π) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = (star (s l σ π ζ) * s l σ π ζ) * w`.

Introduce `σ`. Rewrite using `[hSSΨ σ, show t l π σ q.1.2 = star (s l σ π ζ) from hadj π σ ζ hζ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[Finset.sum_congr rfl (fun σ _ => h4 σ), ← Finset.sum_mul]`. Apply `mul_right_cancel₀ hw` to reduce the goal to its premises.

Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hY : ∀ ρ', rawR P Bs.μsec e ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q = s l ρ' π ζ * (w * a π)`. Introduce `ρ'`. Rewrite using `[(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl Φ ρ' q).1, Finset.sum_eq_single π (fun b _ hb => by rw [hrawΦ, hK1 b hb]; ring) (fun h => absurd (Finset.mem_univ π) h), hrawΦ]`.

Use `set Y := (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) with hYdef`. Use `⟨Φ, hΦv, ?_, fun ρ hUp => ?_⟩` and prove the remaining obligations. Establish `hp1` using `SSAdjH.hs_pair P Bs hpl hk e he ((d.SS l).1 Φ) ((d.SS l).1 Φ) q`. Simplify using `only [hY] at hp1`. Establish `hp2` using `SSAdjH.hs_pair P Bs hpl hk e he Φ Φ q`.

Simplify using `only [hrawΦ] at hp2`. Rewrite `hp2` using `[Finset.sum_eq_single π (fun b _ hb => by rw [hK1 b hb]; simp) (fun h => absurd (Finset.mem_univ π) h)]`. Establish `hp2' : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0) = star (w * a π) * (w * a π)`. Rewrite using `[← hΦv]`. Conclude with `hp2`.

Establish `hp1' : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec Y) (B.hsVec Y) = ∑ σ, star (s l σ π ζ * (w * a π)) * (s l σ π ζ * (w * a π))` using `hp1`. Establish `hsum1 : ∑ σ, star (s l σ π ζ * (w * a π)) * (s l σ π ζ * (w * a π)) = (star (w * a π) * (w * a π)) * ((M.Nrm P l π : ℝ) : ℂ)`. Rewrite using `[← hK3, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hW2 : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) ≠ 0`. Use `SSTr.wR_pos P hζT` as an intermediate fact. Conclude with `(pow_pos this 2).ne'` after adjusting the coercions. Establish `key : inner ℂ (B.hsVec Y) (B.hsVec Y) = ((M.Nrm P l π : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)`.

Apply `mul_left_cancel₀ hW2` to reduce the goal to its premises. Rewrite using `[hp1', hsum1, show ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * (((M.Nrm P l π : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)) = ((M.Nrm P l π : ℝ) : ℂ) * (((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)) by ring, hp2']`. Expand and normalize the polynomial expressions, which then agree. Establish `k2` using `congrArg Complex.re key`. Rewrite `k2` using `[Complex.re_ofReal_mul]`.

Use `show ‖B.hsVec Y‖ ^ 2 = M.Nrm P l π * ‖B.hsVec X0‖ ^ 2`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]`. Conclude with `k2`. Establish `hc0 : ∀ ρ', ρ' ≠ ρ → inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec Y) = 0`. Introduce `ρ' hne`.

Establish `hn : ¬ M.Up P l π ρ'` using `fun h2 => hne (up_tgt hUp h2).symm`. Establish `h` using `hY ρ'`. Rewrite `h` using `[hraw, hK2 ρ' hn, zero_mul]`. Conclude with `(mul_eq_zero.1 h).resolve_left hw`. Establish `hYe : Y = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) • e ρ ζ` using `by conv_lhs => rw [hexp Y (hval _)]`.

Rewrite using `[Finset.sum_eq_single ρ (fun b _ hb => by rw [hc0 b hb, zero_smul]) (fun h => absurd (Finset.mem_univ ρ) h)]`. Use `show Y ∈ Line P Bs Pr ρ ζ`. Rewrite using `[hYe]`. Conclude with `line_smul P Bs Pr ρ ζ _ (hK0 ρ)`.
-/
theorem cross_section_at_point : AtCSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk hcs X d hA l hl Pr hPr π ζ hζ X0 hX0
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := hA
  have hH : GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hS, hRel, hQQ⟩
  obtain ⟨e, he, hkF⟩ := gauge_kappa_holds Wp Wq P Bs X d hH
  obtain ⟨Qs, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  obtain ⟨s, t, hst, hSL⟩ := gTSSLocal_of_radT radial_torus_local_holds Wp Wq P Bs X d hH e he hkF
  have hadj := second_shift_adjoint_pointwise Wp Wq P Bs X d hH e he hkF s t hst hSL l hl
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  have hζT : P.TT < Complex.normSq ζ := hζ

  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hq : ((c1 P.r, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨constant_one_mem_nonvanishing P.r, by rw [hTz]; exact hζ⟩
  have hΨ : ∀ ρ, (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ := by
    intro ρ
    have h := congrFun (hΨr ρ) (c1 P.r, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hval : ∀ Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro Z
    have hmem := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Z.2).2.1
      (c1 P.r, ζ) hq
    simpa only [NF.radR, Set.indicator_of_mem hq] using hmem
  have hexp := (he.2 ζ hζT).2.2
  have hδ : ∀ ρ σ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e σ ζ)) = if ρ = σ then (1 : ℂ) else 0 :=
    (he.2 ζ hζT).2.1
  let q : MA.Qp P.r P.TT := ⟨(c1 P.r, ζ), fun _ => one_ne_zero, hζT⟩
  set w : ℂ := ((wR P.k P.TT ζ : ℝ) : ℂ) with hwdef
  have hw : w ≠ 0 := wRc_ne P hζ
  have hraw : ∀ (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P), rawR P Bs.μsec e Z ρ q =
      w * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Z (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ))) := fun Z ρ => rfl
  have hrawΨ : ∀ σ ρ, rawR P Bs.μsec e (Ψ σ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
      w * (if ρ = σ then (1 : ℂ) else 0) := by
    intro σ ρ
    rw [hraw, hΨ σ, hδ]
  have hmulapply : ∀ (A C : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      (A * C).1 Z = A.1 (C.1 Z) := fun A C Z => rfl

  have hκpt : ∀ (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
          (NF.muZ P.k P.r Bs.μsec ζ) =
        ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ)).comp (∑ ρ, f ρ • Qs ρ) :=
    fun f Z => hQ.2.2.2 f Z q

  have hK0 : ∀ σ, e σ ζ ∈ Line P Bs Pr σ ζ := by
    intro σ
    refine (lineQ P Bs X d hH Qs hQ Pr hPr ζ hζ σ (e σ ζ) ((he.2 ζ hζT).1 σ)).2 ?_
    have h1 := hκpt (fun ρ => if ρ = σ then (1 : ℂ) else 0) (Ψ σ)
    rw [sum_ite_smul, hΨ σ] at h1
    rw [← h1, hexp _ (hval _)]
    have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((((d.κ (fun ρ => if ρ = σ then (1 : ℂ) else 0)).1 (Ψ σ) :
        Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ))) =
        if ρ = σ then (1 : ℂ) else 0 := by
      intro ρ
      have h2 := SSAdjH.kap_pt P Bs hpl hk e he d hkF (fun ρ => if ρ = σ then (1 : ℂ) else 0) (Ψ σ) ρ q
      rw [hraw, hrawΨ] at h2
      by_cases hρ : ρ = σ
      · rw [if_pos hρ] at h2 ⊢
        apply mul_left_cancel₀ hw
        rw [h2]; ring
      · rw [if_neg hρ] at h2 ⊢
        apply mul_left_cancel₀ hw
        rw [h2]; ring
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  set a : M.Ty P → ℂ := fun σ => inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X0) with hadef
  let Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ∑ σ, a σ • Ψ σ
  have hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g := by
    intro G c g
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  have hΦv : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r) (NF.muZ P.k P.r Bs.μsec ζ) = X0 := by
    rw [hsumv]
    conv_rhs => rw [hexp X0 hX0.1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hΨ σ]
  have hrawΦ : ∀ ρ, rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = w * a ρ := by
    intro ρ
    rw [hraw, hΦv]

  have hXQ : X0.comp (Qs π) = X0 := (lineQ P Bs X d hH Qs hQ Pr hPr ζ hζ π X0 hX0.1).1 hX0
  have hK1 : ∀ σ, σ ≠ π → a σ = 0 := by
    intro σ hσ
    have h1 := hκpt (fun ρ => if ρ = π then (1 : ℂ) else 0) Φ
    rw [sum_ite_smul, hΦv, hXQ] at h1
    have h2 := SSAdjH.kap_pt P Bs hpl hk e he d hkF (fun ρ => if ρ = π then (1 : ℂ) else 0) Φ σ q
    rw [hraw, h1, hrawΦ, if_neg hσ, zero_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left hw

  have hSSΨ : ∀ σ, rawR P Bs.μsec e ((((d.SS l).1 (Ψ π) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = s l σ π ζ * w := by
    intro σ
    rw [(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl (Ψ π) σ q).1]
    simp only [hrawΨ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

  have hK2 : ∀ ρ', ¬ M.Up P l π ρ' → s l ρ' π ζ = 0 := by
    intro ρ' hn
    have hcond : ∀ ρ ρ'', M.Up P l ρ ρ'' →
        (fun x => if M.Up P l π x then (1 : ℂ) else 0) ρ'' = (fun x => if x = π then (1 : ℂ) else 0) ρ := by
      intro ρ ρ'' hU
      dsimp only
      by_cases hρ : ρ = π
      · subst hρ
        rw [if_pos hU, if_pos rfl]
      · have hn2 : ¬ M.Up P l π ρ'' := fun h2 => hρ (up_relation_source_unique hU h2)
        rw [if_neg hn2, if_neg hρ]
    have heq := hRel.2.2.2.1 l _ _ hcond
    have hz := congrArg (fun A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => A.1 (Ψ π)) heq
    simp only [hmulapply] at hz
    have h3 := congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q) hz
    try dsimp only at h3
    rw [SSAdjH.kap_pt P Bs hpl hk e he d hkF, hSSΨ,
      (SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl _ ρ' q).1] at h3
    try dsimp only at h3
    rw [if_neg hn, zero_mul] at h3
    rw [Finset.sum_eq_single π (fun b _ hb => by
        rw [SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ]; try dsimp only
        rw [if_neg hb]; ring)
      (fun h => absurd (Finset.mem_univ π) h)] at h3
    rw [SSAdjH.kap_pt P Bs hpl hk e he d hkF, hrawΨ] at h3
    try dsimp only at h3
    have h4 : s l ρ' π ζ * w = 0 := by
      have h5 : (0 : ℂ) = s l ρ' π ζ * ((if π = π then (1 : ℂ) else 0) * (w * if π = π then (1 : ℂ) else 0)) := h3
      rw [if_pos rfl] at h5
      linear_combination -h5
    exact (mul_eq_zero.1 h4).resolve_right hw

  have hK3 : ∑ σ, star (s l σ π ζ) * s l σ π ζ = ((M.Nrm P l π : ℝ) : ℂ) := by
    have heq := hRel.2.2.2.2.2 l hl
    have hz := congrArg (fun A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => A.1 (Ψ π)) heq
    simp only [hmulapply] at hz
    have h3 := congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) π q) hz
    try dsimp only at h3
    rw [(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl _ π q).2, SSAdjH.kap_pt P Bs hpl hk e he d hkF,
      hrawΨ] at h3
    try dsimp only at h3
    rw [if_pos rfl] at h3
    have h4 : ∀ σ, t l π σ q.1.2 * rawR P Bs.μsec e ((((d.SS l).1 (Ψ π) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = (star (s l σ π ζ) * s l σ π ζ) * w := by
      intro σ
      rw [hSSΨ σ, show t l π σ q.1.2 = star (s l σ π ζ) from hadj π σ ζ hζ]
      ring
    rw [Finset.sum_congr rfl (fun σ _ => h4 σ), ← Finset.sum_mul] at h3
    apply mul_right_cancel₀ hw
    rw [h3]
    ring

  have hY : ∀ ρ', rawR P Bs.μsec e ((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q = s l ρ' π ζ * (w * a π) := by
    intro ρ'
    rw [(SSAdjH.ss_pt P Bs hpl hk e he d s t hst hSL hl Φ ρ' q).1, Finset.sum_eq_single π
      (fun b _ hb => by rw [hrawΦ, hK1 b hb]; ring) (fun h => absurd (Finset.mem_univ π) h), hrawΦ]
  set Y := (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1 P.r)
    (NF.muZ P.k P.r Bs.μsec ζ) with hYdef
  refine ⟨Φ, hΦv, ?_, fun ρ hUp => ?_⟩
  · have hp1 := SSAdjH.hs_pair P Bs hpl hk e he ((d.SS l).1 Φ) ((d.SS l).1 Φ) q
    simp only [hY] at hp1
    have hp2 := SSAdjH.hs_pair P Bs hpl hk e he Φ Φ q
    simp only [hrawΦ] at hp2
    rw [Finset.sum_eq_single π (fun b _ hb => by rw [hK1 b hb]; simp)
      (fun h => absurd (Finset.mem_univ π) h)] at hp2
    have hp2' : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0) = star (w * a π) * (w * a π) := by
      rw [← hΦv]
      exact hp2
    have hp1' : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec Y) (B.hsVec Y) =
        ∑ σ, star (s l σ π ζ * (w * a π)) * (s l σ π ζ * (w * a π)) := hp1
    have hsum1 : ∑ σ, star (s l σ π ζ * (w * a π)) * (s l σ π ζ * (w * a π)) =
        (star (w * a π) * (w * a π)) * ((M.Nrm P l π : ℝ) : ℂ) := by
      rw [← hK3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [star_mul']
      ring
    have hW2 : ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have := SSTr.wR_pos P hζT
      exact_mod_cast (pow_pos this 2).ne'
    have key : inner ℂ (B.hsVec Y) (B.hsVec Y) = ((M.Nrm P l π : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0) := by
      apply mul_left_cancel₀ hW2
      rw [hp1', hsum1, show ((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * (((M.Nrm P l π : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)) =
        ((M.Nrm P l π : ℝ) : ℂ) * (((wR P.k P.TT ζ ^ 2 : ℝ) : ℂ) * inner ℂ (B.hsVec X0) (B.hsVec X0)) by ring, hp2']
      ring
    have k2 := congrArg Complex.re key
    rw [Complex.re_ofReal_mul] at k2
    show ‖B.hsVec Y‖ ^ 2 = M.Nrm P l π * ‖B.hsVec X0‖ ^ 2
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact k2
  · have hc0 : ∀ ρ', ρ' ≠ ρ → inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec Y) = 0 := by
      intro ρ' hne
      have hn : ¬ M.Up P l π ρ' := fun h2 => hne (up_tgt hUp h2).symm
      have h := hY ρ'
      rw [hraw, hK2 ρ' hn, zero_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hw
    have hYe : Y = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) • e ρ ζ := by
      conv_lhs => rw [hexp Y (hval _)]
      rw [Finset.sum_eq_single ρ (fun b _ hb => by rw [hc0 b hb, zero_smul])
        (fun h => absurd (Finset.mem_univ ρ) h)]
    show Y ∈ Line P Bs Pr ρ ζ
    rw [hYe]
    exact line_smul P Bs Pr ρ ζ _ (hK0 ρ)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR
