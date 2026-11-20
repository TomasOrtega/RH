import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
import Formalism.SharpRestriction.CuspSpanNormBounds.MinorCosetSumOfLatticeIndexHypOfTieOK
import Formalism.SharpRestriction.CuspSpanNormBounds.MinorIntegralityTorus
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeSumBound

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

/- English proof (translation)
Use `set K : ℝ := ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) with hK`. Establish `hmaps : ∀ δ ∈ T, KappaEndpoints.k2ends D j δ ∈ (Finset.Icc 1 j).powerset`. Introduce `δ _`. Rewrite using `[Finset.mem_powerset]`. Unfold `KappaEndpoints.k2ends`.

Conclude with `Finset.filter_subset _ _`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Establish `hS : ∀ S ∈ (Finset.Icc 1 j).powerset, ∑ δ ∈ T with KappaEndpoints.k2ends D j δ = S, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ K`. Introduce `S hSm`. Establish `hSsub` using `Finset.mem_powerset.1 hSm`.

Use `set TS := T.filter (fun δ => KappaEndpoints.k2ends D j δ = S) with hTS`. Establish `step1 : ∑ δ ∈ TS, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∑ δ ∈ TS, ∏ l ∈ S, wl (D` using `D) H1 l (δ l) := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `δ hδ`. Establish `he` using `(Finset.mem_filter.1 hδ).2`.

Use `S_rpow_le (D := D) H1 hj δ` as an intermediate fact. Rewrite `this` using `[he]`. Then use the resulting hypothesis. Establish `hinj : ∀ δ ∈ TS, ∀ δ' ∈ TS, (∀ l ∈ S, δ l = δ' l) → δ = δ'`. Introduce `δ hδ δ' hδ' h`. Take `⟨hδT, he⟩` from `Finset.mem_filter.1 hδ`.

Take `⟨hδT', he'⟩` from `Finset.mem_filter.1 hδ'`. Take `⟨-, hz, h0⟩` from `hfact δ hδT`. Take `⟨-, hz', h0'⟩` from `hfact δ' hδT'`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl0 : l = 0`.

Rewrite using `[hl0, h0, h0']`. Distinguish the cases in `hlj : j < l`. Rewrite using `[hz l hlj, hz' l hlj]`. Distinguish the cases in `hlS : l ∈ S`. Conclude with `h l hlS`.

Establish `hI : l ∈ Finset.Icc 1 j` using `Finset.mem_Icc.2 ⟨by omega, by omega⟩`. Establish `a1 : δ l = 0`. Assume the negation of the conclusion as `hne`. Apply `hlS` to reduce the goal to its premises. Rewrite using `[← he]`.

Unfold `KappaEndpoints.k2ends`. Conclude with `Finset.mem_filter.2 ⟨hI, hne⟩`. Establish `a2 : δ' l = 0`. Assume the negation of the conclusion as `hne`. Apply `hlS` to reduce the goal to its premises.

Rewrite using `[← he']`. Unfold `KappaEndpoints.k2ends`. Conclude with `Finset.mem_filter.2 ⟨hI, hne⟩`. Rewrite using `[a1, a2]`. Establish `step2` using `sum_prod_le S TS (fun l x => wl (D := D) H1 l x) (fun l x => wl_nonneg H1 l x) hinj`.

Establish `step3 : ∏ l ∈ S, ∑ x ∈ TS.image (fun δ => δ l), wl (D` using `D) H1 l x ≤ ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `l _`. Conclude with `Finset.sum_nonneg fun x _ => wl_nonneg H1 l x`. Introduce `l _`.

Establish `hint : ∀ x ∈ TS.image (fun δ => δ l), IsIntegral ℤ x`. Introduce `x hx`. Take `⟨δ, hδ, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(hfact δ (Finset.mem_filter.1 hδ).1).1 l`. Combine the equalities or inequalities in the displayed calculation.

Establish `step4 : ∏ l ∈ S, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ K := by`. Rewrite using `[hK, ← Finset.prod_sdiff hSsub]`. Establish `hge : ∀ l, 1 ≤ (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := fun l => one_le_pow₀ (by linarith [one_le_Rl (D := D) H1 l])`. Establish `h1 : 1 ≤ ∏ l ∈ Finset.Icc 1 j \ S, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun l _ => hge l)`. Establish `h0 : 0 ≤ ∏ l ∈ S, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := Finset.prod_nonneg fun l _ => le_trans zero_le_one (hge l)`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `step1.trans (step2.trans (step3.trans step4))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]`. Simplify using the standard rewrite rules.
-/
theorem cosets_sum_gen {D : D7} (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum)
    [Nonempty D.what₂.Tau] (hrd : 0 < D.host.rdE) {H1 : ℝ}
    (hH : 0 < H1) {j : ℕ} (hj : j ≤ D.R.rS) (T : Finset (ℕ → D.host.E))
    (hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1) :
    ∑ δ ∈ T, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      2 ^ j * ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  set K : ℝ := ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) with hK
  have hmaps : ∀ δ ∈ T, KappaEndpoints.k2ends D j δ ∈ (Finset.Icc 1 j).powerset := by
    intro δ _
    rw [Finset.mem_powerset]
    unfold KappaEndpoints.k2ends
    exact Finset.filter_subset _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hS : ∀ S ∈ (Finset.Icc 1 j).powerset,
      ∑ δ ∈ T with KappaEndpoints.k2ends D j δ = S, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ K := by
    intro S hSm
    have hSsub := Finset.mem_powerset.1 hSm
    set TS := T.filter (fun δ => KappaEndpoints.k2ends D j δ = S) with hTS
    have step1 : ∑ δ ∈ TS, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
        ∑ δ ∈ TS, ∏ l ∈ S, wl (D := D) H1 l (δ l) := by
      apply Finset.sum_le_sum
      intro δ hδ
      have he := (Finset.mem_filter.1 hδ).2
      have := S_rpow_le (D := D) H1 hj δ
      rwa [he] at this
    have hinj : ∀ δ ∈ TS, ∀ δ' ∈ TS, (∀ l ∈ S, δ l = δ' l) → δ = δ' := by
      intro δ hδ δ' hδ' h
      obtain ⟨hδT, he⟩ := Finset.mem_filter.1 hδ
      obtain ⟨hδT', he'⟩ := Finset.mem_filter.1 hδ'
      obtain ⟨-, hz, h0⟩ := hfact δ hδT
      obtain ⟨-, hz', h0'⟩ := hfact δ' hδT'
      funext l
      by_cases hl0 : l = 0
      · rw [hl0, h0, h0']
      by_cases hlj : j < l
      · rw [hz l hlj, hz' l hlj]
      by_cases hlS : l ∈ S
      · exact h l hlS
      have hI : l ∈ Finset.Icc 1 j := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have a1 : δ l = 0 := by
        by_contra hne
        apply hlS
        rw [← he]
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      have a2 : δ' l = 0 := by
        by_contra hne
        apply hlS
        rw [← he']
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      rw [a1, a2]
    have step2 := sum_prod_le S TS (fun l x => wl (D := D) H1 l x) (fun l x => wl_nonneg H1 l x) hinj
    have step3 : ∏ l ∈ S, ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x ≤
        ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
      apply Finset.prod_le_prod
      · intro l _; exact Finset.sum_nonneg fun x _ => wl_nonneg H1 l x
      · intro l _
        have hint : ∀ x ∈ TS.image (fun δ => δ l), IsIntegral ℤ x := by
          intro x hx
          obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
          exact (hfact δ (Finset.mem_filter.1 hδ).1).1 l
        calc ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x
            ≤ ∑ x ∈ TS.image (fun δ => δ l), ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) :=
              Finset.sum_le_sum fun x _ => wl_le hrd hH l x
          _ ≤ _ := sum_one_coord hNT hLS _ hint (one_le_Rl H1 l)
    have step4 : ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ K := by
      rw [hK, ← Finset.prod_sdiff hSsub]
      have hge : ∀ l, 1 ≤ (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        fun l => one_le_pow₀ (by linarith [one_le_Rl (D := D) H1 l])
      have h1 : 1 ≤ ∏ l ∈ Finset.Icc 1 j \ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
          (fun l _ => hge l)
      have h0 : 0 ≤ ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_nonneg fun l _ => le_trans zero_le_one (hge l)
      nlinarith
    exact step1.trans (step2.trans (step3.trans step4))
  calc _ ≤ ∑ S ∈ (Finset.Icc 1 j).powerset, K := Finset.sum_le_sum hS
    _ = 2 ^ j * K := by
      rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      simp

/- English proof (translation)
Take `⟨⟨h0, -, -⟩, -⟩` from `hH`. Take `⟨-, -, hmf, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -, -, -, -, -, hCl⟩` from `h0`. Establish `hjI` using `Finset.mem_Icc.1 hj`. Establish `hrd2 : 2 ≤ D.host.rdE` using `by unfold Formalism.BasicNotions.Host.v at hv; linarith`. Establish `hm2` using `D.R.two_le_m`.

Establish `hf1 : 1 ≤ D.R.f` using `le_trans (Nat.one_le_pow _ _ (by omega)) hmf`. Establish `: Nonempty D.what₂.Tau` using `Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; omega)`. Establish `hb2` using `KappaEndpoints.two_le_scale_b D large₂`. Use `set H1 : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ)) with hH1def`. Establish `hH1 : 0 < H1` using `Real.rpow_pos_of_pos (by linarith) _`.

Establish `hsum` using `cosets_sum_gen hNT hLS (by linarith) hH1 hjI.2 T hfact`. Use `set B : ℝ := D.host.rdE ^ (((2 * (D.R.rS * D.R.rS) : ℕ)) : ℝ) * (max 1 (2 * H1)) ^ (2 * D.R.rS) with hB`. Establish `hB1 : 1 ≤ B` using `one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (Nat.cast_nonneg _)) (one_le_pow₀ (le_max_left _ _))`. Establish `hRl : ∀ l ∈ Finset.Icc 1 j, Rl (D` using `D) H1 l ≤ B := by`. Introduce `l hl`.

Establish `hlr : l ≤ D.R.rS` using `(Finset.mem_Icc.1 hl).2.trans hjI.2`. Establish `hfe` using `frameExp_le hlr`. Use `max_le hB1 (mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) (by positivity) (Real.rpow_nonneg (by linarith) _))` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast (by omega : 2 * frameExp D.R.rS l ≤ 2 * (D.R.rS * D.R.rS)))`. Establish `hprod : ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hfin` using `final_arith (L := large₂.sc.L) (CH := CH) (rd := D.host.rdE) (r := D.R.rS) (m := D.R.m) (f := D.R.f) (n := Fintype.card D.what₂.Tau) (j := j) (KappaEndpoints.one_lt_scale_L D large₂) hCl (by linarith) hrdL (by omega) (by have := KappaEndpoints.two_rank_add_two_eq_m D; omega) hjI. …`. Unfold `Hb`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kloostermanCosetSum_le {D : D7} (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) (large₂ : SizeData₂ D)
    {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0) (CH : ℝ)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) (T : Finset (ℕ → D.host.E))
    (hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1) :
    ∑ δ ∈ T, KappaEndpoints.k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      Hb large₂.sc.b (ccOf CH Cl) D.R.m D.R.f ^ (ccOf CH Cl * (D.R.rS : ℝ)) := by
  obtain ⟨⟨h0, -, -⟩, -⟩ := hH
  obtain ⟨-, -, hmf, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -, -, -, -, -, hCl⟩ := h0
  have hjI := Finset.mem_Icc.1 hj
  have hrd2 : 2 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.v at hv; linarith
  have hm2 := D.R.two_le_m
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; omega)
  have hb2 := KappaEndpoints.two_le_scale_b D large₂
  set H1 : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ)) with hH1def
  have hH1 : 0 < H1 := Real.rpow_pos_of_pos (by linarith) _
  have hsum := cosets_sum_gen hNT hLS (by linarith) hH1 hjI.2 T hfact
  set B : ℝ := D.host.rdE ^ (((2 * (D.R.rS * D.R.rS) : ℕ)) : ℝ) * (max 1 (2 * H1)) ^ (2 * D.R.rS) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (Nat.cast_nonneg _))
    (one_le_pow₀ (le_max_left _ _))
  have hRl : ∀ l ∈ Finset.Icc 1 j, Rl (D := D) H1 l ≤ B := by
    intro l hl
    have hlr : l ≤ D.R.rS := (Finset.mem_Icc.1 hl).2.trans hjI.2
    have hfe := frameExp_le hlr
    refine max_le hB1 (mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) (by positivity)
      (Real.rpow_nonneg (by linarith) _))
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast (by omega : 2 * frameExp D.R.rS l ≤ 2 * (D.R.rS * D.R.rS)))
  have hprod : ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤
      ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by
    calc ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau)
        ≤ ∏ l ∈ Finset.Icc 1 j, (64 * B) ^ (2 * Fintype.card D.what₂.Tau) :=
          Finset.prod_le_prod (fun l _ => pow_nonneg (by linarith [one_le_Rl (D := D) H1 l]) _)
            (fun l hl => pow_le_pow_left₀ (by linarith [one_le_Rl (D := D) H1 l]) (by linarith [hRl l hl]) _)
      _ = ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by rw [Finset.prod_const]; simp
  have hfin := final_arith (L := large₂.sc.L) (CH := CH) (rd := D.host.rdE) (r := D.R.rS) (m := D.R.m) (f := D.R.f)
    (n := Fintype.card D.what₂.Tau) (j := j) (KappaEndpoints.one_lt_scale_L D large₂) hCl (by linarith) hrdL (by omega)
    (by have := KappaEndpoints.two_rank_add_two_eq_m D; omega) hjI.2 (by rw [D.what₂.card_Tau]) hf1
  unfold Hb
  calc _ ≤ _ := hsum
    _ ≤ 2 ^ j * ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ _ := hfin

end Gen

section Conc

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word}

/- English proof (translation)
Establish `hRow : IsRowLat D (X.Fu u) t.lam` using `(Y.rowsOK u).1 t.lam t.mem`. Establish `hOK : FrameOK D t.lam (frq X t.rep)` using `t.rep.2.2.2.2.2.2`. Establish `hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT t.lam` using `hRow.2.1.2.1`. Establish `he : ∀ a, (lf D (X.Fu u)).fl.e a ∈ t.lam` using `e_mem_lam D t.lam (lf D (X.Fu u)) hRow.2.2`. Establish `he' : ∀ a, (frq X t.rep).fl.e a ∈ t.lam` using `e_mem_lam D t.lam (frq X t.rep) hOK.2`.

Establish `hl' : l ≤ D.R.rS + 1` using `by omega`. Unfold `Dl leadMinorE`. Rewrite using `[dif_pos hl']`. Apply `det_isIntegral` to reduce the goal to its premises. Introduce `i j`.

Establish `hi : Fin.castLE hl' i = Fin.castSucc ⟨i, by omega⟩` using `Fin.ext rfl`. Establish `hj : Fin.castLE hl' j = Fin.castSucc ⟨j, by omega⟩` using `Fin.ext rfl`. Simplify using `only [Matrix.submatrix_apply, Zhat, brS]`. Rewrite using `[hi, hj]`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`.

Conclude with `pair_int D hU (he' _) (he _)`.
-/
theorem minorInt_conc (t : GTu Y u) (l : ℕ) (hl : l ≤ D.R.rS) :
    IsIntegral ℤ (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l) := by
  have hRow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hOK : FrameOK D t.lam (frq X t.rep) := t.rep.2.2.2.2.2.2
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT t.lam := hRow.2.1.2.1
  have he : ∀ a, (lf D (X.Fu u)).fl.e a ∈ t.lam := e_mem_lam D t.lam (lf D (X.Fu u)) hRow.2.2
  have he' : ∀ a, (frq X t.rep).fl.e a ∈ t.lam := e_mem_lam D t.lam (frq X t.rep) hOK.2
  have hl' : l ≤ D.R.rS + 1 := by omega
  unfold Dl leadMinorE
  rw [dif_pos hl']
  apply det_isIntegral
  intro i j
  have hi : Fin.castLE hl' i = Fin.castSucc ⟨i, by omega⟩ := Fin.ext rfl
  have hj : Fin.castLE hl' j = Fin.castSucc ⟨j, by omega⟩ := Fin.ext rfl
  simp only [Matrix.submatrix_apply, Zhat, brS]
  rw [hi, hj]
  simp only [FlagG.fvec, Fin.snoc_castSucc]
  exact pair_int D hU (he' _) (he _)

/- English proof (translation)
Use `⟨fun l => ?_, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Unfold `labT split_ifs with hl`. Conclude with `minorInt_conc t l (le_trans hl (Nat.sub_le _ _))`. Conclude with `isIntegral_zero`. Unfold `labT`.

Rewrite using `[if_neg (not_le.mpr (by unfold jT at hl; exact hl))]`. Unfold `labT`. Rewrite using `[if_pos (Nat.zero_le _)]`. Unfold `Dl leadMinorE`. Use `first`.

Consider the case `exact Matrix.det_isEmpty`. Consider the case `simp`. Consider the case `done`.
-/
theorem labFacts_conc (t : GTu Y u) :
    (∀ l, IsIntegral ℤ (labT t l)) ∧ (∀ l, jT t < l → labT t l = 0) ∧ labT t 0 = 1 := by
  refine ⟨fun l => ?_, fun l hl => ?_, ?_⟩
  · unfold labT
    split_ifs with hl
    · exact minorInt_conc t l (le_trans hl (Nat.sub_le _ _))
    · exact isIntegral_zero
  · unfold labT
    rw [if_neg (not_le.mpr (by unfold jT at hl; exact hl))]
  · unfold labT
    rw [if_pos (Nat.zero_le _)]
    unfold Dl leadMinorE
    first
      | exact Matrix.det_isEmpty
      | simp
      | done

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0 CH hCH`. Use `⟨21 + 4 * |CH|, by positivity, 0, 1, fun C' Cl _ hCl1 D large₂ X Y u hH _ j hj T hTm => ?_⟩` and prove the remaining obligations. Establish `hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1`. Introduce `δ hδ`. Take `⟨t, -, rfl, rfl⟩` from `hTm δ hδ`.

Conclude with `labFacts_conc t`. Establish `h` using `kloostermanCosetSum_le NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact`. Unfold `H1C`. Use `h.trans ?_` and prove the remaining obligations. Establish `hb : 1 ≤ large₂.sc.b` using `by linarith [KappaEndpoints.two_le_scale_b D large₂]`.

Establish `hCl0 : 0 < Cl` using `by linarith`. Establish `hc0 : 0 ≤ ccOf CH Cl` using `by unfold ccOf; positivity`. Establish `hcle : ccOf CH Cl ≤ 21 + 4 * |CH|`. Unfold `ccOf`. Establish `: 4 / Cl ≤ 4` using `by rw [div_le_iff₀ hCl0]; linarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Hb`. Rewrite using `[← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]`. Apply `Real.rpow_le_rpow_of_exponent_le hb` to reduce the goal to its premises. Establish `hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS` using `by positivity`.

Establish `e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) = ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS)` using `by ring`. Establish `e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) = (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS)` using `by ring`. Rewrite using `[e1, e2]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx`.
-/
theorem cosetsC_holds : CosetsC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨21 + 4 * |CH|, by positivity, 0, 1, fun C' Cl _ hCl1 D large₂ X Y u hH _ j hj T hTm => ?_⟩
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end Conc

end Formalism.L2.SG.KappaOffDiagonal
