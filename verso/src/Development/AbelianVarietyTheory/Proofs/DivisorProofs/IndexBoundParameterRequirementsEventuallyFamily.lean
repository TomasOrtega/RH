import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickSetDensityLeInvFourLwStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventuallyStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoSizeRows

/- English proof (translation)
Take `⟨-, -, -, -, -, -, sQD, -, -, -, -, sDe2, sLw, -⟩` from `S`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he` using `L.sc.eps_pos`. Establish `hel` using `L.sc.eps_lt`.

Establish `hm0 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (show 1 ≤ D.R.m by have := D.R.two_le_m; omega)`. Establish `hn0 : (0 : ℝ) < D.R.n` using `by have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _; exact_mod_cast this`. Use `⟨?_, h2, GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq D L Pm Tp hK, by rw [hC], sDe2, ?_, ?_, ?_, GlobalTheory.FinalJoin.RecordRun.k_b'_le Pm (GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound h2), ?_, by exact_mod_cast (show (44 : ℝ) ≤ D.R.m by linarith), hn …` and prove the remaining obligations. Establish `hlogeta` using `Pm.logeta`. Establish `heta` using `L.etaSz_pos`.

Establish `a1 : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4))` using `(Real.log_le_iff_le_exp heta).1 hlogeta`. Establish `a2 : (D.R.n : ℝ) ≤ Real.exp (1 + 3 * Real.log L.sc.x)`. Establish `e3 : Real.exp (3 * Real.log L.sc.x) = L.sc.x ^ 3`. Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]`. Rewrite using `[Real.exp_add, e3]`.

Establish `b1 : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ L.sc.x ^ (3 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Rewrite `b1` using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `b2 : (2 : ℝ) ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `b3 : 0 ≤ L.sc.x ^ 3` using `by positivity`. Use polynomial arithmetic with `[hn.2]`.

Establish `key : L.etaSz * L.sc.X' * D.R.n ≤ Real.exp (L.sc.L / 5)`. Establish `hX : 0 < L.sc.X'` using `Real.exp_pos _`. Combine the equalities or inequalities in the displayed calculation. Unfold `Scale.X'`. Simplify using `only [Real.exp_add]`.

Use `_ ≤ Real.exp (L.sc.L / 5) := by`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Unfold `Scale.L`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb45 : L.sc.b ^ ((4 : ℝ) / 5) = Real.exp (L.sc.L * (4 / 5))`.

Unfold `Scale.b`. Rewrite using `[← Real.exp_mul]`. Establish `hX : 0 < L.sc.X'` using `Real.exp_pos _`. Unfold `Scale.w'' Scale.b' Scale.a`. Rewrite using `[hb45, div_div, le_div_iff₀ (by positivity)]`.

Establish `e5 : Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) = L.sc.b`. Unfold `Scale.b`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation.

Apply `GlobalTheory.T.thickSet_density_le_inv_four_Lw` to reduce the goal to its premises. Establish `a1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Rewrite `a1` using `[Real.rpow_two]`. Establish `: ((8 * D.host.Lw : ℕ) : ℝ) < D.R.n`. Use `push_cast`.

Unfold `SizeLw at sLw`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Introduce `i`. Establish `e : Real.exp (9 * L.sc.L) = L.sc.b ^ 9`.

Unfold `Scale.b`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Rewrite using `[← e]`. Conclude with `hg i`.

Establish `hq : (0 : ℝ) < D.host.q` using `lt_trans (by positivity) Pm.qd_pow.1`. Establish `hd : (0 : ℝ) < D.host.d` using `lt_trans (by positivity) Pm.qd_pow.2`. Take `⟨-, -, q2, -, d2, -⟩` from `sQD`. Unfold `szTh at q2 d2`. Use `push_cast`.

Rewrite using `[Real.log_mul hq.ne' hd.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD` using `Pm.Del_ge.2.2.2`. Establish `hl` using `Pm.logDel`. Establish `hN0 : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`.

Establish `hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10` using `one_le_pow₀ hm0`. Establish `a1 : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ)` using `le_trans (le_mul_of_one_le_right hN0 hm10) hD`. Establish `hX : 0 < L.sc.X'` using `Real.exp_pos _`. Break down `le_or_gt (D.s.Del : ℝ) 0 with h0 | h0` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `a2 : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2)` using `(Real.log_le_iff_le_exp h0).1 hl`. Establish `a3 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Establish `a4 : 0 ≤ L.sc.x ^ (L.sc.eps / 4)` using `by positivity`. Establish `a5 : Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ≤ L.sc.X'`. Unfold `Scale.X'; exact Real.exp_le_exp.2 (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizeRows_at {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    (S : SizesAt L) (hC : Pm.CnW = 10) (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L))
    (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ D.R.n ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps))
    (hm : Real.sqrt (L.sc.x * L.sc.delta1) ≤ D.R.m)
    (h1 : L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + 1 + 3 * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps / 5)
    (h2 : 11 ≤ L.sc.x ^ (L.sc.ez / 5)) (h6 : 8 * Real.log L.sc.x ^ 2 < L.sc.x ^ 2)
    (h8 : 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) ≤ Real.sqrt (L.sc.x * L.sc.delta1))
    (h11 : 44 ≤ Real.sqrt (L.sc.x * L.sc.delta1)) : GlobalTheory.IndexAssembly.SizeRows Tp hK := by
  obtain ⟨-, -, -, -, -, -, sQD, -, -, -, -, sDe2, sLw, -⟩ := S
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have hel := L.sc.eps_lt
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by have := D.R.two_le_m; omega)
  have hn0 : (0 : ℝ) < D.R.n := by have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _; exact_mod_cast this
  refine ⟨?_, h2, GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq D L Pm Tp hK, by rw [hC], sDe2, ?_, ?_, ?_, GlobalTheory.FinalJoin.RecordRun.k_b'_le Pm
    (GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound h2), ?_, by exact_mod_cast (show (44 : ℝ) ≤ D.R.m by linarith), hn0.le⟩
  ·
    have hlogeta := Pm.logeta
    have heta := L.etaSz_pos
    have a1 : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := (Real.log_le_iff_le_exp heta).1 hlogeta
    have a2 : (D.R.n : ℝ) ≤ Real.exp (1 + 3 * Real.log L.sc.x) := by
      have e3 : Real.exp (3 * Real.log L.sc.x) = L.sc.x ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
      rw [Real.exp_add, e3]
      have b1 : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ L.sc.x ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at b1
      have b2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have b3 : 0 ≤ L.sc.x ^ 3 := by positivity
      nlinarith [hn.2]
    have key : L.etaSz * L.sc.X' * D.R.n ≤ Real.exp (L.sc.L / 5) := by
      have hX : 0 < L.sc.X' := Real.exp_pos _
      calc L.etaSz * L.sc.X' * D.R.n
          ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) * L.sc.X' * Real.exp (1 + 3 * Real.log L.sc.x) := by gcongr
        _ = Real.exp (L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + (1 + 3 * Real.log L.sc.x)) := by
          unfold Scale.X'; simp only [Real.exp_add]
        _ ≤ Real.exp (L.sc.L / 5) := by
          apply Real.exp_le_exp.2
          unfold Scale.L
          linarith
    have hb45 : L.sc.b ^ ((4 : ℝ) / 5) = Real.exp (L.sc.L * (4 / 5)) := by
      unfold Scale.b; rw [← Real.exp_mul]
    have hX : 0 < L.sc.X' := Real.exp_pos _
    unfold Scale.w'' Scale.b' Scale.a
    rw [hb45, div_div, le_div_iff₀ (by positivity)]
    have e5 : Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) = L.sc.b := by
      unfold Scale.b; rw [← Real.exp_add]; ring_nf
    calc L.etaSz * Real.exp (L.sc.L * (4 / 5)) * (L.sc.X' * (L.sc.x * D.R.n))
        = L.sc.x * (L.etaSz * L.sc.X' * D.R.n) * Real.exp (L.sc.L * (4 / 5)) := by ring
      _ ≤ L.sc.x * Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) := by gcongr
      _ = L.sc.x * L.sc.b := by rw [mul_assoc, e5]
  · apply GlobalTheory.T.thickSet_density_le_inv_four_Lw
    have a1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    rw [Real.rpow_two] at a1
    have : ((8 * D.host.Lw : ℕ) : ℝ) < D.R.n := by
      push_cast
      unfold SizeLw at sLw
      linarith
    exact_mod_cast this
  · intro i
    have e : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    rw [← e]; exact hg i
  ·
    have hq : (0 : ℝ) < D.host.q := lt_trans (by positivity) Pm.qd_pow.1
    have hd : (0 : ℝ) < D.host.d := lt_trans (by positivity) Pm.qd_pow.2
    obtain ⟨-, -, q2, -, d2, -⟩ := sQD
    unfold szTh at q2 d2
    push_cast
    rw [Real.log_mul hq.ne' hd.ne']
    linarith
  ·
    have hD := Pm.Del_ge.2.2.2
    have hl := Pm.logDel
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ hm0
    have a1 : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) := le_trans (le_mul_of_one_le_right hN0 hm10) hD
    have hX : 0 < L.sc.X' := Real.exp_pos _
    rcases le_or_gt (D.s.Del : ℝ) 0 with h0 | h0
    · linarith
    · have a2 : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := (Real.log_le_iff_le_exp h0).1 hl
      have a3 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have a4 : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := by positivity
      have a5 : Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ≤ L.sc.X' := by
        unfold Scale.X'; exact Real.exp_le_exp.2 (by linarith)
      linarith

/- English proof (translation)
Use `⟨1 / 100, by norm_num, fun eps he hle => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => ?_⟩⟩` and prove the remaining obligations. Establish `hez : 0 < Fm.ez`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_ez 0 i]`. Conclude with `(Fm.L 0 i).sc.ez_pos`.

Establish `hev : ∀ᶠ x : ℝ in Filter.atTop, 11 ≤ x ^ (Fm.ez / 5)` using `(tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 11`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 ((GlobalTheory.T.eventually_rpow_log_inequalities eps he (by linarith)).and hev)`. Use `⟨x0, fun x hx hx0' ι => ?_⟩` and prove the remaining obligations. Establish `hsx` using `Fm.L_x x ι hx`. Establish `hse` using `Fm.L_eps x ι`.

Take `⟨⟨a1, -, a6, a8, a11⟩, a2⟩` from `hx0 x hx0'`. Take `⟨w1, w2, -⟩` from `hc.2.1 x hx ι`. Establish `hd : (Fm.L x ι).sc.delta1 = x ^ (-(eps / 8))` using `by unfold Scale.delta1; rw [hsx, hse]`. Use `sizeRows_at _ _ (Fm.sizes x hx ι) (Fm.fixed.2.2.2.2.2.2.2 x hx ι).1 ((hc.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hsx, hse]`.

Conclude with `w1`. Rewrite using `[hsx]`. Conclude with `w2.1`. Rewrite using `[hsx, hse]`. Conclude with `a1`.

Rewrite using `[hsx, Fm.L_ez x ι]`. Conclude with `a2`. Rewrite using `[hsx]`. Conclude with `a6`. Rewrite using `[hd, hsx, hse]`.

Conclude with `a8`. Rewrite using `[hd, hsx]`. Conclude with `a11`.
-/
theorem sizeRows_along : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  refine ⟨1 / 100, by norm_num, fun eps he hle => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => ?_⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 11 ≤ x ^ (Fm.ez / 5) :=
    (tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 11
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((GlobalTheory.T.eventually_rpow_log_inequalities eps he (by linarith)).and hev)
  refine ⟨x0, fun x hx hx0' ι => ?_⟩
  have hsx := Fm.L_x x ι hx
  have hse := Fm.L_eps x ι
  obtain ⟨⟨a1, -, a6, a8, a11⟩, a2⟩ := hx0 x hx0'
  obtain ⟨w1, w2, -⟩ := hc.2.1 x hx ι
  have hd : (Fm.L x ι).sc.delta1 = x ^ (-(eps / 8)) := by unfold Scale.delta1; rw [hsx, hse]
  refine sizeRows_at _ _ (Fm.sizes x hx ι) (Fm.fixed.2.2.2.2.2.2.2 x hx ι).1
    ((hc.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsx, hse]; exact w1
  · rw [hsx]; exact w2.1
  · rw [hsx, hse]; exact a1
  · rw [hsx, Fm.L_ez x ι]; exact a2
  · rw [hsx]; exact a6
  · rw [hd, hsx, hse]; exact a8
  · rw [hd, hsx]; exact a11

end GlobalTheory.OntoSizeRows
