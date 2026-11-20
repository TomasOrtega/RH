import Formalism.HermitianCurvature.HermitianCurvatureProofs.LamSumPos

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

/- English proof (translation)
Introduce `hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB`. Use `⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩` and prove the remaining obligations. Establish `hB'` using `hB`. Take `⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩` from `hB'`. Take `⟨hl0, -⟩` from `hv v`.

Establish `hCI` using `PBCut.cutInside_of_built hB`. Introduce `s hs2 hsr a ha haN`. Establish `hsr' : s ≤ S.G.r + 1` using `hsr`. Establish `ha' : D.AdmAt S v a` using `ha`. Establish `haN' : a.length + C.Kst ≤ S.Ntop` using `haN`.

Use `set d := S.G.r + 1 - s with hd`. Establish `hds : d + s = S.G.r + 1` using `by omega`. Establish `hd2 : d ≤ 2 * S.G.r` using `by omega`. Take `⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩` from `Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2`. Use `⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩` and prove the remaining obligations.

Introduce `ε hε t Y ht hY`. Establish `hY' : ∀ P ∈ Y, D.ptSize P = d` using `fun P hP => by rw [hd]; exact hY P hP`. Use `set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ`. Use `set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹ with hC0`. Use `set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t with hτ`.

Use `set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc`. Take `⟨hg, hk⟩` from `glob_posT hB`. Establish `hC0nn : 0 ≤ C0` using `mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false)) (inv_nonneg.2 (Real.sqrt_nonneg _))`. Establish `hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod`. Introduce `n`.

Use `List.prod_pos fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hx`. Take `⟨b, rfl⟩` from `List.mem_ofFn.1 hy`. Conclude with `abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1`. Establish `hK1` using `top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v)) (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length)) Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => first …`.

Establish `h` using `second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b)) (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)`. Rewrite using `[List.length_ofFn] at h)` and apply the resulting hypothesis. Express the relevant statement in the definitionally equal form `Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)])) (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) * KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a …`. Establish `hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1` using `fun P hP => by rw [hY' P hP]; omega`. Establish `hgpos` using `g_pos_of_built hB`.

Establish `hrd` using `PBD.rd_pos' E`. Establish `hΓ : 0 < ΓS S (S.G.r + 1)` using `PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _`. Establish `hsa : 0 < S.sizeAt v a` using `sizeAt_pos S hGo v a ha'`. Use `set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka`. Establish `hka0 : 0 ≤ ka` using `by positivity`.

Establish `hΛpos : 0 < Λ` using `lam_sum_pos grid hinj`. Establish `h1` using `loe_diag (omT S s t) (loe_smul ka hka0 hK1)`. Establish `h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)])) (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1), ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) * (((ka / …`. Use `loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1` and prove the remaining obligations. Rewrite using `[gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'`. Establish `hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) = ∑ n : Fin C.Kst → Fin (d + 1), ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * …`. Introduce `P hP Q hQ`. Use `(mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]`. Establish `hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod * S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod`. Rewrite using `[hka]`. Use `(hPn n).ne'` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpsdY` using `psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ) (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le) (fun n P Q => ∑ e', ∑ …`. Establish `hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ`.

Establish `hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ)` using `zpow_pos (by positivity) _`. Use `set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef`. Establish `hτn : ‖τ‖ = lv * ‖t‖`. Rewrite using `[hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg hlv.le]`. Establish `hcn : ‖c‖ = ‖τ‖ ^ C.Kst`.

Rewrite using `[hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]`. Use `set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef`. Establish `hΛB : Λ ≤ B ^ C.Kst` using `lam_sum_le grid B hbnd`. Establish `hlenpos` using `lenI_posT hB (Fin.pos v)`. Establish `hB0 : 0 ≤ B`.

Rewrite using `[hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _`. Establish `hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ) ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (√(S.T * S.T'))⁻¹`. Establish `: 0 ≤ S.G.N` using `by unfold Sz.Glob.N; positivity`. Use `supA_nonneg S hg hk v false` as an intermediate fact. Check the signs of the components of the expression.

Establish `hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0`. Unfold `lamTop`. Rewrite using `[Real.sq_sqrt hA0]`. Establish `e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ)` using `by rw [hd]; push_cast; omega`. Establish `e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ)` using `by push_cast; omega`.

Establish `e3 : (S.g : ℝ) = S.G.g` using `by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring`. Establish `e4 : S.G.r + 2 - s - 1 = d` using `by omega`. Rewrite using `[e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'', len_eq_lenI', hC0, mul_comm d 2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst)`.

Establish `e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst`. Rewrite using `[pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]`. Rewrite using `[e5, hcn, hτn]`. Establish `hΛ0 : 0 ≤ Λ` using `hΛpos.le`. Establish `hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst` using `mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `loe_scale hpsdY hX`. Conclude with `loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)`.
-/
theorem topLocB : TopLocB := by
  intro hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB
  refine ⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  have hCI := PBCut.cutInside_of_built hB
  intro s hs2 hsr a ha haN
  have hsr' : s ≤ S.G.r + 1 := hsr
  have ha' : D.AdmAt S v a := ha
  have haN' : a.length + C.Kst ≤ S.Ntop := haN
  set d := S.G.r + 1 - s with hd
  have hds : d + s = S.G.r + 1 := by omega
  have hd2 : d ≤ 2 * S.G.r := by omega
  obtain ⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩
  intro ε hε t Y ht hY
  have hY' : ∀ P ∈ Y, D.ptSize P = d := fun P hP => by rw [hd]; exact hY P hP
  set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ
  set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹
    with hC0
  set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (s - 1) * t with hτ
  set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hC0nn : 0 ≤ C0 := mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
    intro n
    refine List.prod_pos fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1

  have hK1 := top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v))
    (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length))
    Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => firstSt_inj _)
    (fun e ρ => vecT S p F v ε s t a e ρ)
    (fun n e' ρ => vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => del2 S p v a e ρ) (fun n e' ρ => del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => second_defect_nonneg S p v a e ρ) (fun n e' ρ => second_defect_nonneg S p v _ e' ρ)
    (fun n => ∏ b, F7.lagCo (grid b) (n b))
    (fun n => ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) hPn c C0 C.Kst hC0nn
    (fun P hP e ρ => vecT_deg hDT hB F v ε (hF v ε hε) s hs2 t ht d hds a e ρ grid hinj
      (fun n => (hwords n).2.2.1) P (hY' P hP))
    (fun n e ρ => by
      have h := second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b))
        (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)
      rwa [List.length_ofFn] at h)

  change Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
    (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) *
      KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]))
  have hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1 := fun P hP => by rw [hY' P hP]; omega
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  have hΓ : 0 < ΓS S (S.G.r + 1) := PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _
  have hsa : 0 < S.sizeAt v a := sizeAt_pos S hGo v a ha'
  set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka
  have hka0 : 0 ≤ ka := by positivity
  have hΛpos : 0 < Λ := lam_sum_pos grid hinj

  have h1 := loe_diag (omT S s t) (loe_smul ka hka0 hK1)
  have h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
      (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q))) := by
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1
    · rw [gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]
      ring
    · exact mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'

  have hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
      (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)) := by
    intro P hP Q hQ
    refine (mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]
    have hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod *
        S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
      rw [hka]; have := (hPn n).ne'; field_simp
    rw [hk]
    ring
  have hpsdY := psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ)
    (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod)
    (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le)
    (fun n P Q => ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
      gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)
    (fun n => psd_dsum Y _ (fun e' ρ => second_defect_nonneg S p v _ e' ρ) _)
  have hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ := by
    have hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) :=
      zpow_pos (by positivity) _
    set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef
    have hτn : ‖τ‖ = lv * ‖t‖ := by
      rw [hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hlv.le]
    have hcn : ‖c‖ = ‖τ‖ ^ C.Kst := by
      rw [hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]
    set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef
    have hΛB : Λ ≤ B ^ C.Kst := lam_sum_le grid B hbnd
    have hlenpos := lenI_posT hB (Fin.pos v)
    have hB0 : 0 ≤ B := by
      rw [hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _

    have hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ)
        ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 *
        (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (√(S.T * S.T'))⁻¹ := by
      have : 0 ≤ S.G.N := by unfold Sz.Glob.N; positivity
      have := supA_nonneg S hg hk v false
      positivity
    have hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0 := by
      unfold lamTop
      rw [Real.sq_sqrt hA0]
      have e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ) := by rw [hd]; push_cast; omega
      have e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ) := by push_cast; omega
      have e3 : (S.g : ℝ) = S.G.g := by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring
      have e4 : S.G.r + 2 - s - 1 = d := by omega
      rw [e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'',
        len_eq_lenI', hC0, mul_comm d 2]
      ring
    have hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) := by
      have e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by
        rw [pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]
      rw [e5, hcn, hτn]
      have hΛ0 : 0 ≤ Λ := hΛpos.le
      have hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst := mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)
      calc ((lv * ‖t‖) ^ C.Kst) ^ 2 * Λ * C0 ^ C.Kst * Λ = ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (Λ * Λ) := by ring
        _ ≤ ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (B ^ C.Kst * B ^ C.Kst) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by ring
    linarith
  have h3 := loe_scale hpsdY hX
  exact loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)

end

end Formalism.FourierDecayAlt.P.PBL

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBL.topLocB`.
-/
theorem Formalism.FourierDecayAlt.P.top_local_built_places : Formalism.FourierDecayAlt.P.PBL.TopLocB := Formalism.FourierDecayAlt.P.PBL.topLocB
