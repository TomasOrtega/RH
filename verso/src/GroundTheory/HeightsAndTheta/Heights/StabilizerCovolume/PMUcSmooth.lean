import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace MUcSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `smoothRepConj`. Use `split_ifs with h`. Conclude with `h.choose_spec.2.1`. Conclude with `TopNPoly.smoothRep_smooth_of ha hZ hh`.
-/
theorem smoothRepConj_smooth_of {P : Ideal (MRing ι)} {A Z : HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRepConj P A) := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact TopNPoly.smoothRep_smooth_of ha hZ hh

end MUcSmooth

open MuRegSmooth TopNPoly NbarSmooth MUcSmooth in

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D H M w S B p q t hsm`. Establish `hVS : VertFactorSmooth.Statement` using `VertFactorSmooth.proof VertFactorPos.proof`. Use `set P := mCoordIdeal D.y with hPdef`. Use `set a : K → ℤ := (q : ℤ) • muTwDeg H B + (p : ℤ) • D.a' with ha`. Use `set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q * (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef`.

Establish `hSB : ∀ p' ∈ D.SB B, p' ∈ D.S` using `fun p' hp' => (Finset.mem_filter.1 hp').1`. Establish `hMH : IsMultiHomogIdeal P` using `D.arith.2.1.2.1`. Establish `hpos : ∀ z ∈ mcPts P, 0 < F z`. Introduce `z hz`. Establish `h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z` using `Finset.prod_pos fun p' hp' => VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz`.

Conclude with `mul_pos (mul_pos (pow_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q)) (pow_pos (D.A'.pos z hz.1) p)`. Establish `hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z`. Introduce `z hz c hc`. Establish `hcz : torusSmul c z ∈ mcPts P` using `mcPts_smul hMH c hc hz`. Establish `hproj : M.proj (torusSmul c z) = M.proj z` using `((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm`.

Establish `href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ H.aMu k) * S.ref.h z`. Use `S.ref.smul c z hc` as an intermediate fact. Rewrite `this` using `[S.ref_deg]`. Conclude with `this`. Establish `hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z`.

Use `D.A'.smul c z hc` as an intermediate fact. Rewrite `this` using `[D.A'_deg]`. Conclude with `this`. Establish `hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z` using `fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc`. Establish `hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p`.

Introduce `k`. Establish `hx : ‖c k‖ ≠ 0` using `norm_ne_zero_iff.mpr (hc k)`. Establish `hak : a k = (q : ℤ) * (muTwDeg H B) k + (p : ℤ) * D.a' k`. Simplify using `only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]`.

Establish `hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ H.aMu k) * ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p`. Rewrite using `[Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, muTwDeg, prod_norm_zpow_add_sum hc]`. Simplify using `only [hFdef]`. Rewrite using `[hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsmooth : SmoothAlong (mcPts P) F` using `smoothAlong_mul (smoothAlong_mul (smoothAlong_pow (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth) (smoothAlong_exp (hP II Ψ K ι Ω E D M _ hsm))) q) (smoothAlong_pow (smoothAlong_prod _ fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).2) q)) (smoothAlong_pow (smoothAlo …`. Take `⟨Z, hZa, hZs, hZh⟩` from `hE K ι P a F hMH hpos hhom hsmooth`. Use `show IsSmoothHerm (smoothRepConj P (hermOfFun ι a F))`. Conclude with `smoothRepConj_smooth_of (Z := Z) hZa hZs fun z hz => (hZh z hz).trans (hermOfFun_h_of_mem hMH hhom hz (hpos z hz)).symm`.
-/
theorem MUcSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement) : MUcSmooth.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D H M w S B p q t hsm
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ H.aMu k) * S.ref.h z := by
      have := S.ref.smul c z hc
      rw [S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg H B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ H.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  have hsmooth : SmoothAlong (mcPts P) F :=
    smoothAlong_mul (smoothAlong_mul
      (smoothAlong_pow (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth)
        (smoothAlong_exp (hP II Ψ K ι Ω E D M _ hsm))) q)
      (smoothAlong_pow (smoothAlong_prod _ fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).2) q))
      (smoothAlong_pow (smoothAlong_of_contDiffOn D.A'_pos.1) p)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι P a F hMH hpos hhom hsmooth
  show IsSmoothHerm (smoothRepConj P (hermOfFun ι a F))
  exact smoothRepConj_smooth_of (Z := Z) hZa hZs fun z hz =>
    (hZh z hz).trans (hermOfFun_h_of_mem hMH hhom hz (hpos z hz)).symm

end GroundTheory.Heights₂.Heights.NineStatements
