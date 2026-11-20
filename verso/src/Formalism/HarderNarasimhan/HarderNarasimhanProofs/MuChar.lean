import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax

open Module Submodule

noncomputable section

namespace Formalism.HN

/- English proof (translation)
Introduce `y hy`. Take `⟨x, hx, rfl⟩ : ∃ x ∈ A, ρ x = y` from `hy`. Conclude with `(⟨x, h hx, rfl⟩ : ∃ x' ∈ B, ρ x' = ρ x)`.
-/
theorem muChar_zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ A, ρ x = y := hy
  exact (⟨x, h hx, rfl⟩ : ∃ x' ∈ B, ρ x' = ρ x)

universe u v w in
/- English proof (translation)
Introduce `R V E _ _ _ _ _ _ ρ L hL hL0`. Take `⟨-, P2, P3, P4, P5, P6, -, P8⟩` from `h2 R V E ρ L hL`. Establish `hdisc : DiscreteTopology (zl ρ L)` using `hL.2`. Establish `hrk0 : rk ρ (⊥ : Submodule R V) = 0` using `(P4 ⊥ bot_le).2 rfl`. Establish `hrkpos : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → (0 : ℝ) < rk ρ N`.

Introduce `N hN hN0`. Establish `: rk ρ N ≠ 0` using `fun h => hN0 ((P4 N hN).1 h)`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions. Establish `hslope : ∀ N : Submodule R V, slope ρ N = deg ρ N / rk ρ N` using `fun N => rfl`. Establish `hzlne : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → zl ρ N ≠ ⊥`.

Introduce `N hN hN0 h`. Apply `hN0` to reduce the goal to its premises. Apply `(P4 N hN).1` to reduce the goal to its premises. Use `show Formalism.F.rk (zl ρ N) = 0`. Rewrite using `[h]`.

Simplify using `[Formalism.F.rk]`. Take `⟨c, hc⟩` from `Formalism.F.slopesBdd E (zl ρ L) hdisc`. Establish `hsc : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → slope ρ N ≤ c` using `fun N hN hN0 => hc ⟨zl ρ N, muChar_zl_mono ρ hN, hzlne N hN hN0, rfl⟩`. Establish `hdegbd : ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ max c 0 * rk ρ L`. Introduce `N hN`.

Distinguish the cases in `hN0 : N = ⊥`. Substitute `hN0` using the available equality. Rewrite using `[P5]`. Conclude with `mul_nonneg (le_max_right c 0) (Nat.cast_nonneg _)`. Establish `hpos` using `hrkpos N hN hN0`.

Establish `hs` using `hsc N hN hN0`. Rewrite `hs` using `[hslope, div_le_iff₀ hpos]`. Establish `hr : (rk ρ N : ℝ) ≤ rk ρ L` using `by exact_mod_cast (P2 N L hN le_rfl).1`. Establish `e1 : c * (rk ρ N : ℝ) ≤ max c 0 * rk ρ N` using `mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg _)`. Establish `e2 : max c 0 * (rk ρ N : ℝ) ≤ max c 0 * rk ρ L` using `mul_le_mul_of_nonneg_left hr (le_max_right c 0)`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set T : Set ℝ := {t | ∃ N : Submodule R V, N ≤ L ∧ N ≠ ⊥ ∧ slope ρ N = t} with hT`. Establish `hmuMax : muMax ρ L = sSup T` using `rfl`. Establish `hTne : T.Nonempty` using `⟨_, L, le_rfl, hL0, rfl⟩`. Establish `hTbdd : BddAbove T`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨N, hN, hN0, rfl⟩`. Conclude with `hsc N hN hN0`. Establish `part1 : ∀ θ : ℝ, muMax ρ L ≤ θ ↔ ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N`. Introduce `θ`.

Rewrite using `[hmuMax]`. Prove the components needed by the constructor for the conclusion. Introduce `h N hN`. Distinguish the cases in `hN0 : N = ⊥`. Substitute `hN0` using the available equality.

Rewrite using `[P5, hrk0]`. Simplify using the standard rewrite rules. Establish `h1 : slope ρ N ≤ θ` using `(le_csSup hTbdd ⟨N, hN, hN0, rfl⟩).trans h`. Rewrite `h1` using `[hslope, div_le_iff₀ (hrkpos N hN hN0)]`. Conclude with `h1`.

Introduce `h`. Use `csSup_le hTne ?_` and prove the remaining obligations. Introduce and unpack `t ⟨N, hN, hN0, rfl⟩`. Rewrite using `[hslope, div_le_iff₀ (hrkpos N hN hN0)]`. Conclude with `h N hN`.

Establish `hsatlt : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L → rk ρ S < rk ρ L`. Introduce `S hS hSL`. Establish `hle` using `(P8 S hS).2.1`. Break down `lt_or_eq_of_le hle with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd (P3 S L hS hS.1 le_rfl h.symm).symm hSL`. Establish `hdpos : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L → (1 : ℝ) ≤ (rk ρ L : ℝ) - rk ρ S`. Introduce `S hS hSL`. Establish `h' : rk ρ S + 1 ≤ rk ρ L` using `hsatlt S hS hSL`. Establish `: (rk ρ S : ℝ) + 1 ≤ rk ρ L` using `by exact_mod_cast h'`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqslope : ∀ S : Submodule R V, IsSat ρ L S → Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ S)) = (deg ρ L - deg ρ S) / ((rk ρ L : ℝ) - rk ρ S)`. Introduce `S hS`. Take `⟨hr, hle, hd⟩` from `P8 S hS`. Use `show Formalism.F.deg _ / (Formalism.F.rk _ : ℝ) = _`.

Rewrite using `[hr, hd, Nat.cast_sub hle]`. Use `set U : Set ℝ := {t | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧ Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t} with hU`. Establish `hmuMin : muMin ρ L = sInf U` using `rfl`. Establish `hUne : U.Nonempty` using `⟨_, ⊥, P6, hL0.symm, rfl⟩`. Establish `hUbdd : BddBelow U`.

Use `⟨min (deg ρ L - max c 0 * rk ρ L) 0, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨N, hN, hNL, rfl⟩`. Rewrite using `[hqslope N hN]`. Establish `hd` using `hdpos N hN hNL`. Rewrite using `[le_div_iff₀ (by linarith)]`.

Establish `hb` using `hdegbd N hN.1`. Establish `m1` using `min_le_left (deg ρ L - max c 0 * rk ρ L) 0`. Establish `m2` using `min_le_right (deg ρ L - max c 0 * rk ρ L) 0`. Establish `m3` using `mul_le_mul_of_nonpos_left hd m2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `part2 : ∀ θ : ℝ, θ ≤ muMin ρ L ↔ ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N`. Introduce `θ`. Rewrite using `[hmuMin]`. Prove the components needed by the constructor for the conclusion. Introduce `h N hN`.

Take `⟨N', hNN', hN'L, hzl⟩` from `h1 R V E ρ L N hL hN`. Take `⟨hsat, -, hrkeq⟩` from `Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc (muChar_zl_mono ρ hN)`. Establish `hN'sat : IsSat ρ L N'` using `⟨hN'L, by rw [hzl]; exact hsat⟩`. Establish `hrk' : rk ρ N' = rk ρ N` using `by show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)`. Rewrite using `[hzl]`.

Conclude with `hrkeq`. Establish `hdeg' : deg ρ N ≤ deg ρ N'` using `(P2 N N' hNN' hN'L).2 hrk'.symm`. Distinguish the cases in `hN'L' : N' = L`. Establish `hr : rk ρ N = rk ρ L` using `by rw [← hrk', hN'L']`. Establish `hdg : deg ρ N ≤ deg ρ L` using `hN'L' ▸ hdeg'`.

Rewrite using `[hr, sub_self, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht` using `h.trans (csInf_le hUbdd ⟨N', hN'sat, hN'L', rfl⟩)`. Rewrite `ht` using `[hqslope N' hN'sat]`. Establish `hd` using `hdpos N' hN'sat hN'L'`.

Rewrite `ht` using `[le_div_iff₀ (by linarith)]`. Rewrite using `[← hrk']`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`. Use `le_csInf hUne ?_` and prove the remaining obligations.

Introduce and unpack `t ⟨N, hN, hNL, rfl⟩`. Rewrite using `[hqslope N hN]`. Establish `hd` using `hdpos N hN hNL`. Rewrite using `[le_div_iff₀ (by linarith)]`. Conclude with `h N hN.1`.

Establish `part3 : ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ ⊥ ∧ slope ρ N = muMax ρ L`. Take `⟨N, hbN, hNsat, hmax⟩` from `h3 R V E ρ L ⊥ hL P6 hL0.symm`. Establish `hN0 : N ≠ ⊥` using `hbN.ne'`. Use `⟨N, hNsat, hN0, ?_⟩` and prove the remaining obligations. Rewrite using `[hmuMax]`.

Use `(IsGreatest.csSup_eq ⟨(show slope ρ N ∈ T from ⟨N, hNsat.1, hN0, rfl⟩), ?_⟩).symm` and prove the remaining obligations. Introduce and unpack `t ⟨N', hN', hN'0, rfl⟩`. Establish `hm` using `hmax N' (bot_lt_iff_ne_bot.2 hN'0) hN'`. Rewrite `hm` using `[P5, hrk0]`. Simplify using `only [sub_zero, Nat.cast_zero] at hm`.

Rewrite using `[hslope, hslope, div_le_div_iff₀ (hrkpos N' hN' hN'0) (hrkpos N hNsat.1 hN0)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hquotbot : Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) = slope ρ L`. Rewrite using `[hqslope ⊥ P6, P5, hrk0, hslope]`. Simplify using the standard rewrite rules.

Use `⟨part1, part2, part3, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmuMin, ← hquotbot]`. Conclude with `csInf_le hUbdd (show Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) ∈ U from ⟨⊥, P6, hL0.symm, rfl⟩)`. Rewrite using `[hmuMax]`. Conclude with `le_csSup hTbdd (show slope ρ L ∈ T from ⟨L, le_rfl, hL0, rfl⟩)`.
-/
theorem muChar_of (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) (h3 : RatioMax.{u, v, w}) :
    MuChar.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL hL0
  obtain ⟨-, P2, P3, P4, P5, P6, -, P8⟩ := h2 R V E ρ L hL
  have hdisc : DiscreteTopology (zl ρ L) := hL.2
  have hrk0 : rk ρ (⊥ : Submodule R V) = 0 := (P4 ⊥ bot_le).2 rfl
  have hrkpos : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → (0 : ℝ) < rk ρ N := by
    intro N hN hN0
    have : rk ρ N ≠ 0 := fun h => hN0 ((P4 N hN).1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hslope : ∀ N : Submodule R V, slope ρ N = deg ρ N / rk ρ N := fun N => rfl
  have hzlne : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → zl ρ N ≠ ⊥ := by
    intro N hN hN0 h
    apply hN0
    apply (P4 N hN).1
    show Formalism.F.rk (zl ρ N) = 0
    rw [h]
    simp [Formalism.F.rk]
  obtain ⟨c, hc⟩ := Formalism.F.slopesBdd E (zl ρ L) hdisc
  have hsc : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → slope ρ N ≤ c := fun N hN hN0 =>
    hc ⟨zl ρ N, muChar_zl_mono ρ hN, hzlne N hN hN0, rfl⟩
  have hdegbd : ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ max c 0 * rk ρ L := by
    intro N hN
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [P5]
      exact mul_nonneg (le_max_right c 0) (Nat.cast_nonneg _)
    · have hpos := hrkpos N hN hN0
      have hs := hsc N hN hN0
      rw [hslope, div_le_iff₀ hpos] at hs
      have hr : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (P2 N L hN le_rfl).1
      have e1 : c * (rk ρ N : ℝ) ≤ max c 0 * rk ρ N :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg _)
      have e2 : max c 0 * (rk ρ N : ℝ) ≤ max c 0 * rk ρ L :=
        mul_le_mul_of_nonneg_left hr (le_max_right c 0)
      linarith

  set T : Set ℝ := {t | ∃ N : Submodule R V, N ≤ L ∧ N ≠ ⊥ ∧ slope ρ N = t} with hT
  have hmuMax : muMax ρ L = sSup T := rfl
  have hTne : T.Nonempty := ⟨_, L, le_rfl, hL0, rfl⟩
  have hTbdd : BddAbove T := by
    refine ⟨c, ?_⟩
    rintro t ⟨N, hN, hN0, rfl⟩
    exact hsc N hN hN0
  have part1 : ∀ θ : ℝ, muMax ρ L ≤ θ ↔
      ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N := by
    intro θ
    rw [hmuMax]
    constructor
    · intro h N hN
      by_cases hN0 : N = ⊥
      · subst hN0
        rw [P5, hrk0]
        simp
      · have h1 : slope ρ N ≤ θ := (le_csSup hTbdd ⟨N, hN, hN0, rfl⟩).trans h
        rw [hslope, div_le_iff₀ (hrkpos N hN hN0)] at h1
        exact h1
    · intro h
      refine csSup_le hTne ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      rw [hslope, div_le_iff₀ (hrkpos N hN hN0)]
      exact h N hN

  have hsatlt : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L → rk ρ S < rk ρ L := by
    intro S hS hSL
    have hle := (P8 S hS).2.1
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (P3 S L hS hS.1 le_rfl h.symm).symm hSL
  have hdpos : ∀ S : Submodule R V, IsSat ρ L S → S ≠ L →
      (1 : ℝ) ≤ (rk ρ L : ℝ) - rk ρ S := by
    intro S hS hSL
    have h' : rk ρ S + 1 ≤ rk ρ L := hsatlt S hS hSL
    have : (rk ρ S : ℝ) + 1 ≤ rk ρ L := by exact_mod_cast h'
    linarith
  have hqslope : ∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ S)) =
        (deg ρ L - deg ρ S) / ((rk ρ L : ℝ) - rk ρ S) := by
    intro S hS
    obtain ⟨hr, hle, hd⟩ := P8 S hS
    show Formalism.F.deg _ / (Formalism.F.rk _ : ℝ) = _
    rw [hr, hd, Nat.cast_sub hle]
  set U : Set ℝ := {t | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧
    Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t} with hU
  have hmuMin : muMin ρ L = sInf U := rfl
  have hUne : U.Nonempty := ⟨_, ⊥, P6, hL0.symm, rfl⟩
  have hUbdd : BddBelow U := by
    refine ⟨min (deg ρ L - max c 0 * rk ρ L) 0, ?_⟩
    rintro t ⟨N, hN, hNL, rfl⟩
    rw [hqslope N hN]
    have hd := hdpos N hN hNL
    rw [le_div_iff₀ (by linarith)]
    have hb := hdegbd N hN.1
    have m1 := min_le_left (deg ρ L - max c 0 * rk ρ L) 0
    have m2 := min_le_right (deg ρ L - max c 0 * rk ρ L) 0
    have m3 := mul_le_mul_of_nonpos_left hd m2
    linarith
  have part2 : ∀ θ : ℝ, θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N := by
    intro θ
    rw [hmuMin]
    constructor
    · intro h N hN
      obtain ⟨N', hNN', hN'L, hzl⟩ := h1 R V E ρ L N hL hN
      obtain ⟨hsat, -, hrkeq⟩ :=
        Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc (muChar_zl_mono ρ hN)
      have hN'sat : IsSat ρ L N' := ⟨hN'L, by rw [hzl]; exact hsat⟩
      have hrk' : rk ρ N' = rk ρ N := by
        show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
        rw [hzl]
        exact hrkeq
      have hdeg' : deg ρ N ≤ deg ρ N' := (P2 N N' hNN' hN'L).2 hrk'.symm
      by_cases hN'L' : N' = L
      · have hr : rk ρ N = rk ρ L := by rw [← hrk', hN'L']
        have hdg : deg ρ N ≤ deg ρ L := hN'L' ▸ hdeg'
        rw [hr, sub_self, mul_zero]
        linarith
      · have ht := h.trans (csInf_le hUbdd ⟨N', hN'sat, hN'L', rfl⟩)
        rw [hqslope N' hN'sat] at ht
        have hd := hdpos N' hN'sat hN'L'
        rw [le_div_iff₀ (by linarith)] at ht
        rw [← hrk']
        linarith
    · intro h
      refine le_csInf hUne ?_
      rintro t ⟨N, hN, hNL, rfl⟩
      rw [hqslope N hN]
      have hd := hdpos N hN hNL
      rw [le_div_iff₀ (by linarith)]
      exact h N hN.1
  have part3 : ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ ⊥ ∧ slope ρ N = muMax ρ L := by
    obtain ⟨N, hbN, hNsat, hmax⟩ := h3 R V E ρ L ⊥ hL P6 hL0.symm
    have hN0 : N ≠ ⊥ := hbN.ne'
    refine ⟨N, hNsat, hN0, ?_⟩
    rw [hmuMax]
    refine (IsGreatest.csSup_eq ⟨(show slope ρ N ∈ T from ⟨N, hNsat.1, hN0, rfl⟩), ?_⟩).symm
    rintro t ⟨N', hN', hN'0, rfl⟩
    have hm := hmax N' (bot_lt_iff_ne_bot.2 hN'0) hN'
    rw [P5, hrk0] at hm
    simp only [sub_zero, Nat.cast_zero] at hm
    rw [hslope, hslope, div_le_div_iff₀ (hrkpos N' hN' hN'0) (hrkpos N hNsat.1 hN0)]
    linarith
  have hquotbot : Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) = slope ρ L := by
    rw [hqslope ⊥ P6, P5, hrk0, hslope]
    simp
  refine ⟨part1, part2, part3, ?_, ?_⟩
  · rw [hmuMin, ← hquotbot]
    exact csInf_le hUbdd
      (show Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ (⊥ : Submodule R V))) ∈ U from ⟨⊥, P6, hL0.symm, rfl⟩)
  · rw [hmuMax]
    exact le_csSup hTbdd (show slope ρ L ∈ T from ⟨L, le_rfl, hL0, rfl⟩)

/- English proof (translation)
The claim follows from `muChar_of real_saturation_property saturation_basic_properties maximal_slope_ratio`.
-/
theorem slope_characterization : MuChar := muChar_of real_saturation_property saturation_basic_properties maximal_slope_ratio

end Formalism.HN
