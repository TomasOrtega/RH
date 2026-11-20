import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPrincipalisationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProportionalPositiveVolumesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovHt.GeomBound

/- English proof (translation)
Introduce and unpack `⟨a, ha⟩ ⟨b, hb⟩ hab`. Simplify using `only [Fin.mk_lt_mk] at hab`. Proceed by induction on `b with`. Consider the case `zero => omega`. Consider the case `succ n ih`.

Break down `Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'` into its components or cases. Conclude with `(h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) h')`. Substitute `h'` using the available equality. Conclude with `h ⟨a, ha⟩ ⟨a + 1, hb⟩ rfl`.
-/
theorem strictAnti_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) h')
    · subst h'
      exact h ⟨a, ha⟩ ⟨a + 1, hb⟩ rfl

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

/- English proof (translation)
Take `⟨hsig1, hsig2, hsigr⟩` from `hw.sig`. Take `⟨h0, S, eta, -, -, -, h4T, -, hHyp⟩` from `hw.hyp hi`. Establish `hdiv` using `(quo_iff p i PP h0 S eta u1).1 hu`. Establish `G` using `GlobalTheory.MeanTop.divided_gaps _ _ _ (hHyp u1) hdiv`. Simplify using `only [wtsAt] at G`.

Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `hp1 : 1 ≤ (dat p i).p` using `by rw [hsig1]; simp only [Ranks.sigW]; omega`. Establish `hq1 : 1 ≤ (dat p i).q` using `by rw [hsig2]; simp only [Ranks.sigW]; omega`. Establish `hr2 : 2 ≤ D.R.r` using `by omega`.

Establish `hD1 : 1 ≤ dimFlag (dat p i)`. Rewrite using `[hw.dim]`. Conclude with `Nat.mul_pos (by have := hN.f8; omega) (Nat.choose_pos hr2)`. Establish `hz : (4 : ℝ) ≤ zBase L`. Unfold `zBase`.

Establish `c1 : (8 : ℝ) ≤ D.R.f` using `by exact_mod_cast hN.f8`. Establish `c2 : (2 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr2`. Establish `c3 : (10 : ℝ) ≤ L.sc.L` using `hN.big.2.1`. Establish `: (8 : ℝ) * 2 * 10 ≤ D.R.f * D.R.r * L.sc.L` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hPP : (4 : ℝ) ≤ PP` using `hz.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hN.ppLow)`. Establish `hT : 16 * dimFlag (dat p i) ^ 2 ≤ lenT p i PP`. Establish `h1 : (16 * dimFlag (dat p i) ^ 2 : ℝ) ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)`. Establish `c3 : (0 : ℝ) < D.R.m` using `by exact_mod_cast (by omega : 0 < D.R.m)`. Establish `c4 : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : D.R.m ≤ D.R.k)`.

Establish `c5 : (16 : ℝ) ≤ PP ^ 2` using `by nlinarith`. Rewrite using `[le_div_iff₀ c3]`. Establish `c6 : (0 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `h1.trans (Nat.le_ceil _)`.

Unfold `lenT`. Conclude with `h2` after adjusting the coercions. Introduce `τ a b hb`. Take `⟨g1, g2, -⟩` from `G τ a b hb`. Establish `hTz : (16 * (dimFlag (dat p i) : ℤ) ^ 2) ≤ (lenT p i PP : ℤ)` using `by exact_mod_cast hT`.

Establish `hD1z : (1 : ℤ) ≤ dimFlag (dat p i)` using `by exact_mod_cast hD1`. Establish `hsq : (dimFlag (dat p i) : ℤ) ≤ (dimFlag (dat p i) : ℤ) ^ 2` using `by nlinarith`. Move the coercions through the operations in `at G ⊢`. Distinguish the cases in `hbp : (b : ℕ) = (dat p i).p`. Establish `g` using `(g2 hbp).2`.

Establish `hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ)` using `by nlinarith`. Establish `hle : (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `mul_lt_mul_of_pos_left hc hT0` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Move the coercions through the operations in `at hle`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `g` using `g1 hbp`. Move the coercions through the operations in `at g`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem quo_gaps {PP A M : ℝ} (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) :
    ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) ≤ u1 τ a - u1 τ b := by
  obtain ⟨hsig1, hsig2, hsigr⟩ := hw.sig
  obtain ⟨h0, S, eta, -, -, -, h4T, -, hHyp⟩ := hw.hyp hi
  have hdiv := (quo_iff p i PP h0 S eta u1).1 hu
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ (hHyp u1) hdiv
  simp only [wtsAt] at G
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hr2 : 2 ≤ D.R.r := by omega
  have hD1 : 1 ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact Nat.mul_pos (by have := hN.f8; omega) (Nat.choose_pos hr2)

  have hz : (4 : ℝ) ≤ zBase L := by
    unfold zBase
    have c1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
    have c2 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr2
    have c3 : (10 : ℝ) ≤ L.sc.L := hN.big.2.1
    have : (8 : ℝ) * 2 * 10 ≤ D.R.f * D.R.r * L.sc.L := by gcongr
    linarith
  have hPP : (4 : ℝ) ≤ PP := hz.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hN.ppLow)
  have hT : 16 * dimFlag (dat p i) ^ 2 ≤ lenT p i PP := by
    have h1 : (16 * dimFlag (dat p i) ^ 2 : ℝ) ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      have c3 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      have c4 : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
      have c5 : (16 : ℝ) ≤ PP ^ 2 := by nlinarith
      rw [le_div_iff₀ c3]
      have c6 : (0 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := by positivity
      calc (16 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m ≤ (PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) c3.le
        _ ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k := mul_le_mul_of_nonneg_left c4 (by positivity)
    have h2 := h1.trans (Nat.le_ceil _)
    unfold lenT
    exact_mod_cast h2
  intro τ a b hb
  obtain ⟨g1, g2, -⟩ := G τ a b hb
  have hTz : (16 * (dimFlag (dat p i) : ℤ) ^ 2) ≤ (lenT p i PP : ℤ) := by exact_mod_cast hT
  have hD1z : (1 : ℤ) ≤ dimFlag (dat p i) := by exact_mod_cast hD1
  have hsq : (dimFlag (dat p i) : ℤ) ≤ (dimFlag (dat p i) : ℤ) ^ 2 := by nlinarith
  push_cast at G ⊢
  by_cases hbp : (b : ℕ) = (dat p i).p
  · have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by nlinarith
    have hle : (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    push_cast at hle
    linarith
  · have g := g1 hbp
    push_cast at g
    linarith

/- English proof (translation)
Take `⟨hsig1, hsig2, -⟩` from `hw.sig`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hp1 : 1 ≤ (dat p i).p` using `by rw [hsig1]; simp only [Ranks.sigW]; omega`. Establish `hq1 : 1 ≤ (dat p i).q` using `by rw [hsig2]; simp only [Ranks.sigW]; omega`. Establish `hf : 2 < Module.finrank ℚ D.host.E / 2` using `by rw [hN.deg]; have := hN.f8; omega`.

Establish `hj : InR D ((i : ℕ) + 1)` using `⟨by omega, hi.le⟩`. Establish `hL : LawsJ p.T` using `p.fw.laws`. Establish `hYg` using `hY.1`. Take `⟨-, -, -, -, -, -, hq⟩` from `hsz`. Take `⟨-, hq⟩` from `hq hi`.

Take `⟨-, -, hρ1, -⟩` from `hq u1 hu`. Establish `hgap` using `quo_gaps p i hN hw hi u1 hu`. Establish `hsa : ∀ τ, StrictAnti (u1 τ)` using `fun τ => strictAnti_of_step fun a b hb => by`. Use `hgap τ a b hb` as an intermediate fact. Establish `: (0 : ℤ) ≤ (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ)` using `by positivity`.

Use linear arithmetic over natural numbers and integers. Establish `hg1 : ∀ τ, 1 ≤ GlobalTheory.CompHS.gap (u1 τ) ((dat p i).p - 1)` using `fun τ => by`. Establish `e` using `GlobalTheory.CompHS.gap_eq (u1 τ) (i := ⟨(dat p i).p - 1, by omega⟩) (j := ⟨(dat p i).p, by omega⟩) (by simp only; omega)`. Simplify using `only at e`. Rewrite using `[e]`.

Use `hgap τ ⟨(dat p i).p - 1, by omega⟩ ⟨(dat p i).p, by omega⟩ (by simp only; omega)` as an intermediate fact. Establish `: (0 : ℤ) ≤ ((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ)` using `by positivity`. Move the coercions through the operations in `at *`. Use the polynomial consequences of the given equalities and inequalities. Establish `hgood` using `GlobalTheory.T.good_weight_antitone_gap hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg u1 (fun τ => (hsa τ).antitone) hg1`.

Establish `hbir` using `GlobalTheory.T.weight_principalisation_bound hX hG hQ hS1 (GlobalTheory.T.stronger_published_hypotheses_imply hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hYg u1 hgap`. Establish `hprop` using `(GlobalTheory.T.proportional_positive_volumes hP hS1 hS2 hS3 _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg).1`. Introduce `Z`. Use `⟨hgood.2 Z, hbir Z, ?_⟩` and prove the remaining obligations. Establish `hv : vdm u1 ≠ 0` using `(GlobalTheory.CompHt.vdm_pos hsa).ne'`.

Rewrite using `[delPrime_eq Y.U Z hv]`. Conclude with `mul_le_mul_of_nonneg_left (GlobalTheory.DegTop.compDeg_le hprop Z hsa) (by linarith)`.
-/
theorem geomAt_of (hX : GlobalTheory.CovTop.HypothesesX) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hP : Hypotheses2) (hS1 : GlobalTheory.Published.SiegelToroidalIntegral) (hS2 : GlobalTheory.Published.ToroidalForFanKS)
    (hS3 : GlobalTheory.Published.SemiAbelianLieSeminegative)
    {PP C A M : ℝ} (hsz : SizeAt p i PP C) (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (Y : Cov p i) (hY : GoodCov p i Y) (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) : GeomAt p i Y u1 := by
  obtain ⟨hsig1, hsig2, -⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by rw [hN.deg]; have := hN.f8; omega
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hL : LawsJ p.T := p.fw.laws
  have hYg := hY.1
  obtain ⟨-, -, -, -, -, -, hq⟩ := hsz
  obtain ⟨-, hq⟩ := hq hi
  obtain ⟨-, -, hρ1, -⟩ := hq u1 hu
  have hgap := quo_gaps p i hN hw hi u1 hu
  have hsa : ∀ τ, StrictAnti (u1 τ) := fun τ => strictAnti_of_step fun a b hb => by
    have := hgap τ a b hb
    have : (0 : ℤ) ≤ (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) := by positivity
    omega
  have hg1 : ∀ τ, 1 ≤ GlobalTheory.CompHS.gap (u1 τ) ((dat p i).p - 1) := fun τ => by
    have e := GlobalTheory.CompHS.gap_eq (u1 τ) (i := ⟨(dat p i).p - 1, by omega⟩) (j := ⟨(dat p i).p, by omega⟩)
      (by simp only; omega)
    simp only at e
    rw [e]
    have := hgap τ ⟨(dat p i).p - 1, by omega⟩ ⟨(dat p i).p, by omega⟩ (by simp only; omega)
    have : (0 : ℤ) ≤ ((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) := by positivity
    push_cast at *
    nlinarith
  have hgood := GlobalTheory.T.good_weight_antitone_gap hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg u1 (fun τ => (hsa τ).antitone) hg1
  have hbir := GlobalTheory.T.weight_principalisation_bound hX hG hQ hS1 (GlobalTheory.T.stronger_published_hypotheses_imply hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hYg u1 hgap
  have hprop := (GlobalTheory.T.proportional_positive_volumes hP hS1 hS2 hS3 _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg).1
  intro Z
  refine ⟨hgood.2 Z, hbir Z, ?_⟩
  have hv : vdm u1 ≠ 0 := (GlobalTheory.CompHt.vdm_pos hsa).ne'
  rw [delPrime_eq Y.U Z hv]
  exact mul_le_mul_of_nonneg_left (GlobalTheory.DegTop.compDeg_le hprop Z hsa) (by linarith)

end Point

/- English proof (translation)
Introduce `hX hG hQ hP h1 h2 h3 _ hS`. Establish `hH` using `Sizes.hostN 0`. Establish `hW` using `WtShape.wtN`. Unfold `Geom Covers Lifts`. Unfold `Size Lifts at hS`.

Unfold `HostN Lifts at hH`. Unfold `WtN Lifts at hW`. Use `((hS.and hH).and hW).imp fun Fm CH _ h => ?_` and prove the remaining obligations. Take `⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩` from `h`. Take `⟨x0, hx0⟩` from `(e1.and e2).and e3`.

Use `⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩` and prove the remaining obligations. Take `⟨⟨b1, b2⟩, b3⟩` from `hx0 x hx hle ι p hp`. Conclude with `geomAt_of p i hX hG hQ hP h1 h2 h3 (b1 i) (b2 i) (b3 i) hi Y hY u1 hu`.
-/
theorem geom : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → Hypotheses2 →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → Geom := by
  intro hX hG hQ hP h1 h2 h3 _ hS
  have hH := Sizes.hostN 0
  have hW := WtShape.wtN
  unfold Geom Covers Lifts
  unfold Size Lifts at hS
  unfold HostN Lifts at hH
  unfold WtN Lifts at hW
  refine ((hS.and hH).and hW).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, hx0⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3⟩ := hx0 x hx hle ι p hp
  exact geomAt_of p i hX hG hQ hP h1 h2 h3 (b1 i) (b2 i) (b3 i) hi Y hY u1 hu

end GlobalTheory.CovHt.GeomBound

end
