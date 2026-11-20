import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometryOfBounded
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PictureMemStableBounded
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlaneWaveBoundOfCompactPositivity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftBoundOfCompactPositivity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PosAtOfCptCoefOfThmPActualCpt

namespace GlobalTheory.PointwiseBound

noncomputable section

section Wave

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants

/- English proof (translation)
The claim follows from `| [], _, e, h => h e | l :: w, x, e, h => by have h0 := uInv_eq_zero s g w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) (fun a => h _) have h1 := uInv_eq_zero s g w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) (fun a => h _) simp only [KB.uInv] by_cases h : e 0 = 0 · si …`.
-/
theorem uInv_eq_zero {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (s : ℂ) (g : Y) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Y → Z) (e : Wd.Ix (Fin w.length)),
      (∀ a, x a g = 0) → KB.uInv s w x e g = 0
  | [], _, e, h => h e
  | l :: w, x, e, h => by
    have h0 := uInv_eq_zero s g w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) (fun a => h _)
    have h1 := uInv_eq_zero s g w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) (fun a => h _)
    simp only [KB.uInv]
    by_cases h : e 0 = 0
    · simp only [if_pos h]
      exact h0
    · simp only [if_neg h, Pi.add_apply, Pi.smul_apply]
      rw [h0, h1, smul_zero, add_zero]

/- English proof (translation)
Take `⟨ε, hε, hn⟩` from `PBL.nv_of_cv (Bs := Bs) (x := x) hx`. Establish `hw` using `PBFV.waveG_nice Bs ε s w x hn e`. Use `⟨hw.1, ?_, ε, hε, hw.2.2⟩` and prove the remaining obligations. Use `choose R hR using fun a => (hx a).2.1`. Use `⟨∑ a, |R a|, fun g hg hne => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h0 : ∀ a, x a g = 0`. Conclude with `absurd (by simp only [KB.waveG]; rw [uInv_eq_zero s g w x e h0, smul_zero]) hne`. Use `push Not at h0`. Take `⟨a, ha⟩` from `h0`. Conclude with `((hR a g hg ha).trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun a => |R a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))`.
-/
theorem waveG_cptCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef Bs (x e))
    (e : Wd.Ix (Fin w.length)) : KB.CptCoef Bs (KB.waveG Bs s w x e) := by
  obtain ⟨ε, hε, hn⟩ := PBL.nv_of_cv (Bs := Bs) (x := x) hx
  have hw := PBFV.waveG_nice Bs ε s w x hn e
  refine ⟨hw.1, ?_, ε, hε, hw.2.2⟩
  choose R hR using fun a => (hx a).2.1
  refine ⟨∑ a, |R a|, fun g hg hne => ?_⟩
  by_cases h0 : ∀ a, x a g = 0
  · exact absurd (by simp only [KB.waveG]; rw [uInv_eq_zero s g w x e h0, smul_zero]) hne
  · push Not at h0
    obtain ⟨a, ha⟩ := h0
    exact ((hR a g hg ha).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun a => |R a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))

/- English proof (translation)
Introduce `hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'`. Use `⟨waveG_cptCoef _ s w x hx, ?_⟩` and prove the remaining obligations. Take `⟨ε, hε, a, b, -⟩` from `PBL.exists_norm_bound_three_families (Bs := p.T.bs j) (x := x) (y := x') (z := x) hx hx' hx`. Conclude with `GlobalTheory.WaveIsometry.isometry_of_bounded hRad hP Wp Wq P p j hj w hw s x x' ε hε a b (fun e => (hx e).2.1) (fun e => (hx' e).2.1) (fun e => (waveG_cptCoef _ s w x' hx' e).2.1)`.
-/
theorem waveIsometry_of_radial (hRad : JC.RadialModuleForm) : KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'
  refine ⟨waveG_cptCoef _ s w x hx, ?_⟩
  obtain ⟨ε, hε, a, b, -⟩ := PBL.exists_norm_bound_three_families (Bs := p.T.bs j) (x := x) (y := x') (z := x) hx hx' hx
  exact GlobalTheory.WaveIsometry.isometry_of_bounded hRad hP Wp Wq P p j hj w hw s x x' ε hε a b
    (fun e => (hx e).2.1) (fun e => (hx' e).2.1) (fun e => (waveG_cptCoef _ s w x' hx' e).2.1)

end Wave

section Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Introduce `j hj h hh w hw hN`. Take `⟨φ, hφc, hφi, hφ, -⟩` from `PBO.pStd_cpt_of_parts hP (FormsFromXi.radHead hXi) head_top (FormsFromXi.form_const_one hXi) exists_zeta_normalized_haar Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1`. Use `set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef`. Use `⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩` and prove the remaining obligations. Introduce `c hc`.

Simplify using `only`. Rewrite using `[hφ c hc]`. Establish `hA : 0 ≤ A` using `Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl (by rw [hh.2]; omega)`. Establish `hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) = A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)]`. Unfold `TBB.nPt`.

Rewrite using `[Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef, Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]`. Unfold `TBB.NP`. Rewrite using `[hn]`. Distinguish the cases in `hjr : j = P.r`. Substitute `hjr` using the available equality.

Distinguish the cases in `hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'`. Establish `h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0` using `Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Use `push Not at hc2`.

Establish `hT : Tz P.k P.r p.T.base.z = P.T` using `p.hP.2.2.2.1`. Establish `hT' : Tz P.k P.r p.T.base.z' = P.T'` using `p.hP.2.2.2.2.1`. Establish `hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p`. Simplify using `[D.ptGG, D.ptLast]`. Establish `hTT : TBB.TTp p = P.T * P.T'`.

Unfold `TBB.TTp`. Rewrite using `[hT, hT']`. Establish `hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] = KB.levW P (P.r + 1) c`. Rewrite using `[hlast, hTT]`. Rewrite `hc2` using `[hT, hT']`.

Simplify using `only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]`. Rewrite using `[if_pos ⟨by omega, trivial⟩]`. Simplify using the standard rewrite rules. Establish `hlev : 0 ≤ KB.levW P (P.r + 1) c`. Rewrite using `[← hfac, hlast]`.

Simplify using `only [C.nAux]`. Rewrite using `[if_pos ⟨by omega, trivial⟩]`. Establish `: 0 ≤ Complex.normSq c - TBB.TTp p`. Unfold `TBB.TTp`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `using pow_nonneg this _`. Rewrite using `[hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] = KB.levW P (j + 1) c`.

Simplify using `only [C.nAux, KB.levW]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Establish `e : 1 + j + 1 - 1 = j + 1` using `by omega`. Rewrite using `[e]`. Simplify using `only [one_mul, mul_one, Nat.cast_one]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hlev : 0 ≤ KB.levW P (j + 1) c`. Simplify using `only [KB.levW]`. Rewrite using `[if_neg (by omega)]`.

Conclude with `zpow_nonneg (norm_nonneg _) _`. Rewrite using `[hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem extension_at_zero (hXi : B.XiExists) (hP : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := PBO.pStd_cpt_of_parts hP (FormsFromXi.radHead hXi) head_top
    (FormsFromXi.form_const_one hXi) exists_zeta_normalized_haar Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

end Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

end

end GlobalTheory.PointwiseBound
