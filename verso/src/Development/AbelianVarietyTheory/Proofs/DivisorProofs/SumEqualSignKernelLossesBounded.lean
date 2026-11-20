import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerLe
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Set `c : HeightOneSpectrum (𝓞 D.host.F) → ℕ` to `fun v => ringChar (𝓞 D.host.F ⧸ v.asIdeal)`. Establish `key : ∀ l : ℕ, l.Prime → depL G l = 0 ∨ ∃ v ∈ G.pl.S0, c v = l ∧ l ≤ Ideal.absNorm v.asIdeal ∧ depL G l = G.pl.depth sc v`. Introduce `l hl`. Break down `(G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).eq_empty_or_nonempty with h | h` into its components or cases. Use `left`.

Unfold `depL`. Rewrite using `[h]`. Both sides reduce to the same expression. Use `right`. Take `⟨PP, hPP, e⟩` from `Finset.exists_mem_eq_sup _ h (depthAt G)`.

Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hPP`. Establish `h1' : ∃ v ∈ G.pl.S0, G.pl.w v = PP`. Unfold `Places.W0 at h1`. Simplify `h1` using `only [Finset.mem_image]`. Take `⟨v, hv, rfl⟩` from `h1'`.

Establish `hlv : (l : 𝓞 D.host.F) ∈ v.asIdeal`. Rewrite using `[← G.pl.under_w hv]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) l ∈ (G.pl.w v).asIdeal`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Use `haveI := v.isPrime`.

Use `haveI : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Establish `h0 : ((l : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hlv`. Establish `hc : c v = l` using `CharP.ringChar_of_prime_eq_zero hl h0`.

Use `⟨v, hv, hc, ?_, ?_⟩` and prove the remaining obligations. Establish `h3 : ((Nat.card (𝓞 D.host.F ⧸ v.asIdeal) : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0` using `by haveI := Fintype.ofFinite (𝓞 D.host.F ⧸ v.asIdeal)`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero _`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hc]`.

Conclude with `Nat.le_of_dvd Nat.card_pos (ringChar.dvd h3)`. Rewrite using `[← (depthAt_w G hv).2, ← e]`. Unfold `depL`. Reduce the equality to equality of the corresponding arguments. Apply the tactic sequence `refine ⟨(G.pl.S0.image c).filter Nat.Prime, fun l hl => (Finset.mem_filter.1 hl).2, fun l => by dsimp only; split_ifs <;> positivity, fun l hl => ?_, ?_⟩`.

Simplify using `only split_ifs with hp`. Break down `key l hp with h | ⟨v, hv, h, -⟩` into its components or cases. Rewrite using `[h, Nat.cast_zero]`. Conclude with `absurd (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨v, hv, h⟩, hp⟩) hl`. Both sides reduce to the same expression.

Establish `hnn : ∀ v, 0 ≤ (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal)` using `fun v => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`. Unfold `sig`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := c) (t := G.pl.S0.image c) (fun w hw => Finset.mem_image_of_mem _ hw)]`. Use `le_trans (Finset.sum_le_sum fun l hl => ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Nat.Prime _) fun l _ _ => Finset.sum_nonneg fun v _ => hnn v)` and prove the remaining obligations. Establish `hp` using `(Finset.mem_filter.1 hl).2`.

Simplify using `only`. Rewrite using `[if_pos hp]`. Break down `key l hp with h | ⟨v, hv, h, h1, h2⟩` into its components or cases. Rewrite using `[h, Nat.cast_zero, zero_mul]`. Conclude with `Finset.sum_nonneg fun v _ => hnn v`.

Use `le_trans ?_ (Finset.single_le_sum (f := fun v => (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) (fun v _ => hnn v) (Finset.mem_filter.2 ⟨hv, h⟩))` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h1)) (Nat.cast_nonneg _)`.
-/
private theorem GlobalTheory.SumSize.TopSize.depSum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  let c : HeightOneSpectrum (𝓞 D.host.F) → ℕ := fun v => ringChar (𝓞 D.host.F ⧸ v.asIdeal)
  have key : ∀ l : ℕ, l.Prime → depL G l = 0 ∨ ∃ v ∈ G.pl.S0, c v = l ∧ l ≤ Ideal.absNorm v.asIdeal ∧
      depL G l = G.pl.depth sc v := by
    intro l hl
    rcases (G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).eq_empty_or_nonempty with h | h
    · left; unfold depL; rw [h]; rfl
    · right
      obtain ⟨PP, hPP, e⟩ := Finset.exists_mem_eq_sup _ h (depthAt G)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hPP
      have h1' : ∃ v ∈ G.pl.S0, G.pl.w v = PP := by
        unfold Places.W0 at h1; simpa only [Finset.mem_image] using h1
      obtain ⟨v, hv, rfl⟩ := h1'
      have hlv : (l : 𝓞 D.host.F) ∈ v.asIdeal := by
        rw [← G.pl.under_w hv]
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) l ∈ (G.pl.w v).asIdeal
        rwa [map_natCast]
      haveI := v.isPrime
      haveI : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
      have h0 : ((l : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hlv
      have hc : c v = l := CharP.ringChar_of_prime_eq_zero hl h0
      refine ⟨v, hv, hc, ?_, ?_⟩
      · have h3 : ((Nat.card (𝓞 D.host.F ⧸ v.asIdeal) : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
          haveI := Fintype.ofFinite (𝓞 D.host.F ⧸ v.asIdeal)
          rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hc]
        exact Nat.le_of_dvd Nat.card_pos (ringChar.dvd h3)
      · rw [← (depthAt_w G hv).2, ← e]; unfold depL; congr
  refine ⟨(G.pl.S0.image c).filter Nat.Prime, fun l hl => (Finset.mem_filter.1 hl).2,
    fun l => by dsimp only; split_ifs <;> positivity, fun l hl => ?_, ?_⟩
  · dsimp only
    split_ifs with hp
    · rcases key l hp with h | ⟨v, hv, h, -⟩
      · rw [h, Nat.cast_zero]
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨v, hv, h⟩, hp⟩) hl
    · rfl
  have hnn : ∀ v, 0 ≤ (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) :=
    fun v => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  unfold sig
  rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := G.pl.S0.image c) (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Nat.Prime _)
    fun l _ _ => Finset.sum_nonneg fun v _ => hnn v)
  have hp := (Finset.mem_filter.1 hl).2
  dsimp only
  rw [if_pos hp]
  rcases key l hp with h | ⟨v, hv, h, h1, h2⟩
  · rw [h, Nat.cast_zero, zero_mul]; exact Finset.sum_nonneg fun v _ => hnn v
  · refine le_trans ?_ (Finset.single_le_sum (f := fun v => (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))
      (fun v _ => hnn v) (Finset.mem_filter.2 ⟨hv, h⟩))
    rw [h2]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h1)) (Nat.cast_nonneg _)

/- English proof (translation)
Take `⟨-, h0, hS, hB⟩` from `hE`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem GlobalTheory.SumSize.TopSize.sum_le_of_exponents {S : Finset ℕ} {h : ℕ → ℝ} {B : ℝ} (hE : GlobalTheory.NormSum.Exponents S h B)
    (P : Finset ℕ) : ∑ p ∈ P, h p * Real.log p ≤ B := by
  obtain ⟨-, h0, hS, hB⟩ := hE
  calc ∑ p ∈ P, h p * Real.log p ≤ ∑ p ∈ P ∪ S, h p * Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun p _ _ => mul_nonneg (h0 p) (Real.log_natCast_nonneg p))
    _ = ∑ p ∈ S, h p * Real.log p :=
        (Finset.sum_subset Finset.subset_union_right (fun x _ hxS => by rw [hS x hxS, zero_mul])).symm
    _ ≤ _ := hB

/- English proof (translation)
Simplify using `only [ite_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter]`. Break down `lt_or_ge X 1 with h1 | h1` into its components or cases. Rewrite using `[Finset.filter_false_of_mem, Finset.sum_empty]`. Check the signs of the components of the expression.

Introduce `p hp hle`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast (hP p hp).one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_left (Real.log_nonneg h1)]`. Use `le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_) (UpperTheory.WildA.logSum X h1)` and prove the remaining obligations.

Take `⟨hp1, hp2⟩` from `Finset.mem_filter.1 hp`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hp2)), hP p hp1⟩`. Establish `hp'` using `(Finset.mem_filter.1 hp).2`. Conclude with `mul_nonneg (Real.logb_nonneg (by exact_mod_cast hp'.one_lt) h1) (Real.log_natCast_nonneg p)`.
-/
private theorem GlobalTheory.SumSize.TopSize.sum_nab_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {X : ℝ} (hX : 0 ≤ X) :
    ∑ p ∈ P, (if (p : ℝ) ≤ X then Real.logb p X else 0) * Real.log p ≤ X * max (Real.log X) 0 := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rcases lt_or_ge X 1 with h1 | h1
  · rw [Finset.filter_false_of_mem, Finset.sum_empty]
    · positivity
    · intro p hp hle
      have : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      linarith
  · rw [max_eq_left (Real.log_nonneg h1)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_) (UpperTheory.WildA.logSum X h1)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hp2)), hP p hp1⟩
    · have hp' := (Finset.mem_filter.1 hp).2
      exact mul_nonneg (Real.logb_nonneg (by exact_mod_cast hp'.one_lt) h1) (Real.log_natCast_nonneg p)

/- English proof (translation)
Take `⟨-, -, -, hf, hm, -⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ h`. Take `⟨-, -, -, -, -, hb, -⟩` from `h`. Establish `hk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hN1 : 1 ≤ D.R.N D.R.m` using `by simp only [Formalism.BasicNotions.Ranks.N]; omega`. Establish `h1 : 1 ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2` using `Nat.mul_pos (Nat.mul_pos (by omega) hf) (by positivity)`.

Establish `h2 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2` using `by exact_mod_cast h1`. Conclude with `(le_mul_of_one_le_left (Nat.cast_nonneg _) h2).trans hb`.
-/
private theorem GlobalTheory.SumSize.TopSize.d_le {D : D7} (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) :
    (D.host.d : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, hf, hm, -⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ h
  obtain ⟨-, -, -, -, -, hb, -⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have h1 : 1 ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 := Nat.mul_pos (Nat.mul_pos (by omega) hf) (by positivity)
  have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by exact_mod_cast h1
  exact (le_mul_of_one_le_left (Nat.cast_nonneg _) h2).trans hb

/- English proof (translation)
Establish `hM0 : 0 ≤ f * m * N ^ 2 * b * (lb + sg)` using `by positivity`. Establish `hNN : N ≤ N ^ 2` using `by nlinarith`. Establish `hT1 : C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * 26 * (f * m * N ^ 2 * b * (lb + sg))`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : |Real.log C1| + lb ≤ (|Real.log C1| + 1) * (lb + sg)` using `by nlinarith [abs_nonneg (Real.log C1)]`.

Establish `hT2 : C1 * m * (f * N ^ 2) * s4 ≤ C1 ^ 2 * (|Real.log C1| + 1) * (f * m * N ^ 2 * b * (lb + sg))`. Combine the equalities or inequalities in the displayed calculation. Establish `hC0` using `mul_le_mul_of_nonneg_right hC hM0`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem GlobalTheory.SumSize.TopSize.arith {C1 C f m N b lb sg s1 s2 s3 s4 : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) (hf : 0 ≤ f) (hm : 0 ≤ m) (hN : 1 ≤ N) (hb : 0 ≤ b) (hlb : 1 ≤ lb)
    (hsg : 0 ≤ sg) (h1 : s1 ≤ lb / 100) (h2 : s2 ≤ lb) (h3 : s3 ≤ sg) (h4 : s4 ≤ C1 * b * (|Real.log C1| + lb)) :
    C1 * m * (13 * f * N * b) * s1 + C1 * m * (13 * f * N * b) * s2 + C1 * m * (13 * f * N * b) * s3 +
      C1 * m * (f * N ^ 2) * s4 ≤ C * f * m * N ^ 2 * (lb + sg) * b := by
  have hM0 : 0 ≤ f * m * N ^ 2 * b * (lb + sg) := by positivity
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hT1 : C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * 26 * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * m * (13 * f * N * b) * (2 * (lb + sg)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ C1 * m * (13 * f * N ^ 2 * b) * (2 * (lb + sg)) := by gcongr
      _ = _ := by ring
  have h5 : |Real.log C1| + lb ≤ (|Real.log C1| + 1) * (lb + sg) := by nlinarith [abs_nonneg (Real.log C1)]
  have hT2 : C1 * m * (f * N ^ 2) * s4 ≤ C1 ^ 2 * (|Real.log C1| + 1) * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (f * N ^ 2) * s4 ≤ C1 * m * (f * N ^ 2) * (C1 * b * (|Real.log C1| + lb)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ C1 * m * (f * N ^ 2) * (C1 * b * ((|Real.log C1| + 1) * (lb + sg))) := by gcongr
      _ = _ := by ring
  have hC0 := mul_le_mul_of_nonneg_right hC hM0
  calc _ = C1 * m * (13 * f * N * b) * (s1 + s2 + s3) + C1 * m * (f * N ^ 2) * s4 := by ring
    _ ≤ (C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1)) * (f * m * N ^ 2 * b * (lb + sg)) := by linarith
    _ ≤ C * (f * m * N ^ 2 * b * (lb + sg)) := hC0
    _ = _ := by ring

open GlobalTheory.SumSize.TopInt GlobalTheory.SumSize.TopSize in
/- English proof (translation)
Take `⟨Sd, hSd⟩` from `depSum G`. Take `⟨-, -, hN, -, -, -, hrd, hb12⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs`. Establish `hd` using `d_le large₂ hs`. Establish `hker : ∀ j, j < D.R.m → ((∑ τ, ∑ a, (wt G (.top (j + 1)) τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V (.top j)).rank * (G.V (.top (j + 1))).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b` using `fun j hj => UpperTheory.WildA.kerLe (G := G) large₂ hs hH hc (.top t j) hj`. Generalize the expression as in `large₂.sc.b = b at *`.

Establish `hδ0` using `hδ.2.1`. Establish `hlb : 1 ≤ Real.log b`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Combine the linear relations using `[Real.exp_one_lt_d9]`. Establish `hsig : 0 ≤ sig G` using `Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`.

Use `set h : ℕ → ℝ := fun l => if l.Prime then C1 * ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) l (depL G l) else 0 with hh`. Use `set P : Finset ℕ := (S ∪ {D.host.d} ∪ Sd ∪ Finset.range (⌊C1 * b⌋₊ + 1)).filter Nat.Prime with hP`. Establish `hPp : ∀ p ∈ P, p.Prime` using `fun p hp => (Finset.mem_filter.1 hp).2`. Establish `e : topDl G δ C1 b = fun w : PlL D => (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (primeUnder w)`. Use function extensionality and compare the values at `w`.

Simplify using `only [hh, if_pos (primeUnder_prime w), topDl, mul_assoc]`. Rewrite using `[e]`. Use `UpperTheory.WildA.expLoss D P h _ ⟨hPp, fun l => ?_, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hh] split_ifs with hl`. Conclude with `mul_nonneg hC1.le (Finset.sum_nonneg fun j _ => kerLoss_nonneg G hδ0 C1 b _ _ hl _)`.

Conclude with `le_rfl`. Simplify using `only [hh] split_ifs with hp`. Simplify using `only [hP, Finset.mem_filter, hp, and_true, Finset.mem_union, Finset.mem_singleton, Finset.mem_range, not_or] at hl`. Take `⟨⟨⟨h1, h2⟩, h3⟩, h4⟩` from `hl`. Establish `e1` using `hδ.2.2.1 l h1`.

Establish `e3 : (depL G l : ℝ) = 0` using `by simpa only [if_pos hp] using hSd.2.2.1 l h3`. Establish `e4 : ¬ (l : ℝ) ≤ C1 * b` using `fun h5 => h4 (Nat.lt_succ_of_le (Nat.le_floor h5))`. Simplify using `only [kerLoss, e1, e3, if_neg h2, if_neg e4, add_zero, mul_zero, Finset.sum_const_zero]`. Both sides reduce to the same expression. Establish `hKp : ∀ p ∈ P, h p * Real.log p ≤ C1 * D.R.m * (13 * D.R.f * bigN D * b) * (δ p * Real.log p) + C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p = D.host.d then (1 : ℝ) else 0) * Real.log p) + C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p.Prime then (depL G p : ℝ) else 0) * Real …`.

Introduce `p hp`. Establish `hM : 0 ≤ δ p + (if p = D.host.d then (1 : ℝ) else 0) + (depL G p : ℝ)`. Use `hδ0 p` as an intermediate fact. Apply the tactic sequence `have : 0 ≤ (if p = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num`. Check the signs of the components of the expression.

Establish `hK` using `Finset.sum_le_card_nsmul (Finset.range D.R.m) (fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) p (depL G p)) ((13 * D.R.f * bigN D * b) * (δ p + (if p = D.host.d then 1 else 0) + (depL G p : ℝ)) + D.R.f * (bigN D : ℝ) ^ 2 * (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) …`. Unfold `kerLoss`. Conclude with `add_le_add (mul_le_mul_of_nonneg_right (hker j (Finset.mem_range.1 hj)) hM) le_rfl)`. Rewrite `hK` using `[Finset.card_range, nsmul_eq_mul]`. Establish `hlp : 0 ≤ Real.log p` using `Real.log_natCast_nonneg p`.

Simplify using `only [hh, if_pos (hPp p hp)]`. Use `(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC1.le) hlp).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hs2 : ∑ p ∈ P, (if p = D.host.d then (1 : ℝ) else 0) * Real.log p ≤ Real.log b`. Simplify using `only [ite_mul, one_mul, zero_mul]`.

Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hdP`. Conclude with `Real.log_le_log (by exact_mod_cast (hPp _ hdP).pos) hd`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs4 : ∑ p ∈ P, (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p ≤ C1 * b * (|Real.log C1| + Real.log b)`.

Establish `h0 : 0 ≤ C1 * b` using `mul_nonneg hC1.le (by linarith)`. Use `(sum_nab_le P hPp h0).trans (mul_le_mul_of_nonneg_left ?_ h0)` and prove the remaining obligations. Rewrite using `[Real.log_mul hC1.ne' (by linarith)]`. Conclude with `max_le (by linarith [le_abs_self (Real.log C1)]) (by linarith [abs_nonneg (Real.log C1)])`. Use `(Finset.sum_le_sum hKp).trans ?_` and prove the remaining obligations.

Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum]`. Conclude with `arith hC1 hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hN) (by linarith) hlb hsig ((sum_le_of_exponents hδ P).trans hrd) hs2 (sum_le_of_exponents hSd P) hs4`.
-/
private theorem GlobalTheory.SumSize.TopSize.core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) {C1 C : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) {S : Finset ℕ} {δ : ℕ → ℝ}
    (hδ : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE)) :
    Loss (topDl G δ C1 large₂.sc.b) (bOne G C large₂.sc.b) := by
  classical
  obtain ⟨Sd, hSd⟩ := depSum G
  obtain ⟨-, -, hN, -, -, -, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  have hd := d_le large₂ hs
  have hker : ∀ j, j < D.R.m → ((∑ τ, ∑ a, (wt G (.top (j + 1)) τ).natW a : ℕ) : ℝ) +
      (D.R.f : ℝ) * (G.V (.top j)).rank * (G.V (.top (j + 1))).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b :=
    fun j hj => UpperTheory.WildA.kerLe (G := G) large₂ hs hH hc (.top t j) hj
  generalize large₂.sc.b = b at *
  have hδ0 := hδ.2.1
  have hlb : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  set h : ℕ → ℝ := fun l => if l.Prime then
    C1 * ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) l (depL G l) else 0 with hh
  set P : Finset ℕ := (S ∪ {D.host.d} ∪ Sd ∪ Finset.range (⌊C1 * b⌋₊ + 1)).filter Nat.Prime with hP
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have e : topDl G δ C1 b = fun w : PlL D => (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (primeUnder w) := by
    funext w
    simp only [hh, if_pos (primeUnder_prime w), topDl, mul_assoc]
  rw [e]
  refine UpperTheory.WildA.expLoss D P h _ ⟨hPp, fun l => ?_, fun l hl => ?_, ?_⟩
  · simp only [hh]
    split_ifs with hl
    · exact mul_nonneg hC1.le (Finset.sum_nonneg fun j _ => kerLoss_nonneg G hδ0 C1 b _ _ hl _)
    · exact le_rfl
  · simp only [hh]
    split_ifs with hp
    · simp only [hP, Finset.mem_filter, hp, and_true, Finset.mem_union, Finset.mem_singleton, Finset.mem_range, not_or] at hl
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hl
      have e1 := hδ.2.2.1 l h1
      have e3 : (depL G l : ℝ) = 0 := by simpa only [if_pos hp] using hSd.2.2.1 l h3
      have e4 : ¬ (l : ℝ) ≤ C1 * b := fun h5 => h4 (Nat.lt_succ_of_le (Nat.le_floor h5))
      simp only [kerLoss, e1, e3, if_neg h2, if_neg e4, add_zero, mul_zero, Finset.sum_const_zero]
    · rfl
  have hKp : ∀ p ∈ P, h p * Real.log p ≤
      C1 * D.R.m * (13 * D.R.f * bigN D * b) * (δ p * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p = D.host.d then (1 : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p.Prime then (depL G p : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (D.R.f * (bigN D : ℝ) ^ 2) * ((if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p) := by
    intro p hp
    have hM : 0 ≤ δ p + (if p = D.host.d then (1 : ℝ) else 0) + (depL G p : ℝ) := by
      have := hδ0 p
      have : 0 ≤ (if p = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      positivity
    have hK := Finset.sum_le_card_nsmul (Finset.range D.R.m)
      (fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) p (depL G p))
      ((13 * D.R.f * bigN D * b) * (δ p + (if p = D.host.d then 1 else 0) + (depL G p : ℝ)) +
        D.R.f * (bigN D : ℝ) ^ 2 * (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0)) (fun j hj => by
        unfold kerLoss
        exact add_le_add (mul_le_mul_of_nonneg_right (hker j (Finset.mem_range.1 hj)) hM) le_rfl)
    rw [Finset.card_range, nsmul_eq_mul] at hK
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    simp only [hh, if_pos (hPp p hp)]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC1.le) hlp).trans (le_of_eq ?_)
    ring
  have hs2 : ∑ p ∈ P, (if p = D.host.d then (1 : ℝ) else 0) * Real.log p ≤ Real.log b := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    split_ifs with hdP
    · exact Real.log_le_log (by exact_mod_cast (hPp _ hdP).pos) hd
    · linarith
  have hs4 : ∑ p ∈ P, (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p ≤
      C1 * b * (|Real.log C1| + Real.log b) := by
    have h0 : 0 ≤ C1 * b := mul_nonneg hC1.le (by linarith)
    refine (sum_nab_le P hPp h0).trans (mul_le_mul_of_nonneg_left ?_ h0)
    rw [Real.log_mul hC1.ne' (by linarith)]
    exact max_le (by linarith [le_abs_self (Real.log C1)]) (by linarith [abs_nonneg (Real.log C1)])
  refine (Finset.sum_le_sum hKp).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact arith hC1 hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hN) (by linarith) hlb hsig
    ((sum_le_of_exponents hδ P).trans hrd) hs2 (sum_le_of_exponents hSd P) hs4

/- English proof (translation)
Introduce `C1 hC1`. Use `⟨0, fun CF _ => ⟨C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1), fun ε C hC => ⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch _ hAt _ _ S δ hLet`. Establish `hc : ch.sc.cGap = 1` using `by rw [hAt]`. Conclude with `GlobalTheory.SumSize.TopSize.core ch.G A.μ0 large₂ hSet.size hSet.host hc hC1 hC ⟨hLet.1, hLet.2.1, hLet.2.2.1, hLet.2.2.2.1⟩`.
-/
theorem _root_.GlobalTheory.T.sum_equalSign_kernel_losses_bounded : ∀ C1 : ℝ, 0 < C1 → ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.NormSum.Inp D →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
        Loss (GlobalTheory.SumSize.TopInt.topDl ch.G δ C1 large₂.sc.b) (bOne ch.G C large₂.sc.b) := by
  intro C1 hC1
  refine ⟨0, fun CF _ => ⟨C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1), fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch _ hAt _ _ S δ hLet
  have hc : ch.sc.cGap = 1 := by rw [hAt]
  exact GlobalTheory.SumSize.TopSize.core ch.G A.μ0 large₂ hSet.size hSet.host hc hC1 hC ⟨hLet.1, hLet.2.1, hLet.2.2.1, hLet.2.2.2.1⟩
