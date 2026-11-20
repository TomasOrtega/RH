import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceHeckeCharacterBoundedLevelTriviaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterNonInertBoundedLevelKillsUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterBoundedConductorKillsIdeleNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEtaCharacterKillsFiniteIdeleNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotInertPlaceOfMemStatement

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

open GlobalTheory.HeckeUOps

/- English proof (translation)
Introduce `x hx hle` and use `h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))`.
-/
theorem levelLe_one_two {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

/- English proof (translation)
Establish `k1 : 1 ≤ D.R.m - (i : ℕ)` using `by omega`. Establish `k2 : D.R.m - (i : ℕ) ≤ D.R.m` using `by omega`. Use `choose! qf hqf using GlobalTheory.T.exists_prime_notInert_place_of_mem G.pl`. Establish `hS : ∀ q ∈ G.pl.S0.image qf, q.Prime ∧ ¬ InertQ D q`. Introduce `q hq`.

Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hq`. Conclude with `⟨(hqf v hv).1, (hqf v hv).2.1⟩`. Establish `hlev : ∀ v, (G.ch.chiH (D.R.m - i)).UnrAt v ∨ ∃ q ∈ G.pl.S0.image qf, Formalism.L2.Host.OverP D.host q v ∧ (G.ch.chiH (D.R.m - i)).LevelLe v 2`. Introduce `PP`. Distinguish the cases in `h : PP.under (𝓞 D.host.F) ∈ G.pl.S0`.

Use `Or.inr ⟨qf _, Finset.mem_image_of_mem _ h, ?_, ?_⟩` and prove the remaining obligations. Use `(hqf _ h).2.2` as an intermediate fact. Simplify `this` using `[HeightOneSpectrum.under, Formalism.L2.Host.OverP]`. Break down `G.pl.mem_S0_of_sum_eq.1 h with h0 | h1` into its components or cases. Conclude with `levelLe_one_two (G.ch.lev0 _ k1 k2 PP h0).1`.

Conclude with `(G.ch.lev1 _ k1 k2 PP h1).1`. Conclude with `Or.inl (G.ch.unr _ k1 k2 PP h)`. Establish `hcu` using `GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ k1 k2)`. Establish `hci : (G.ch.chiH (D.R.m - i)).HasInf (embT D) (fun τ => 2 * cen D sc.cGap τ (D.R.m - i))` using `G.ch.inf _ k1 k2`. Set `χc : HeckeU D 0` to `ofChar 0 _ _ hcu hci (GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial D _ _ 2 (fun q hq => (hS q hq).1) hlev) (GlobalTheory.T.heckeCharacter_bounded_conductor_kills_idele_norms D _ _ _ 2 (G.ch.triv _ k1 k2) hci (fun q hq => (hS q hq).1) hlev) (fun τ => by si …`.

Establish `he` using `L.C.isEta`. Establish `hei : L.C.eta.HasInf (embT D) (fun _ => 1)` using `fun a => by`. Rewrite using `[he.inf a, ← D.eTau.prod_comp]`. Both sides reduce to the same expression. Set `χe : HeckeU D 1` to `ofChar 1 L.C.eta _ he.unitary hei (GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v)) (GlobalTheory.T.unramified_eta_character_kills_finite_idele_norm D _ he) (fun τ => by simp) (GlobalTheory.T.heckeCharacter_nonIne …`.

Establish `hr : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D` using `by simp only [rankV]; ring`. Establish `hx` using `(ranks_exact D i j).1`. Take `⟨u, hu⟩` from `D.R.t_odd`. Take `⟨w, hw⟩` from `odd_sLen D`. Break down `Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h` into its components or cases.

Use `⟨inv _ χc (by rw [Int.even_iff]; omega), fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [betaH, h, pow_zero, mul_one, inv_f]`. Both sides reduce to the same expression. Use `⟨inv _ (mul 1 χc χe (by decide)) (by rw [Int.even_iff]; omega), fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [betaH, h, pow_one, inv_f, mul_f]`.

Both sides reduce to the same expression.
-/
theorem exists_betaInv_heckeU {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (_hL : L.Is μ₀) (G : GridData L sc)
    (i j : Fin D.R.m) : ∃ χ : HeckeU D (botBig D i j), ∀ x, χ.f x = (betaH G i j)⁻¹.1 (finIdl D x) := by
  classical
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  choose! qf hqf using GlobalTheory.T.exists_prime_notInert_place_of_mem G.pl
  have hS : ∀ q ∈ G.pl.S0.image qf, q.Prime ∧ ¬ InertQ D q := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨(hqf v hv).1, (hqf v hv).2.1⟩
  have hlev : ∀ v, (G.ch.chiH (D.R.m - i)).UnrAt v ∨ ∃ q ∈ G.pl.S0.image qf, Formalism.L2.Host.OverP D.host q v ∧
      (G.ch.chiH (D.R.m - i)).LevelLe v 2 := by
    intro PP
    by_cases h : PP.under (𝓞 D.host.F) ∈ G.pl.S0
    · refine Or.inr ⟨qf _, Finset.mem_image_of_mem _ h, ?_, ?_⟩
      · have := (hqf _ h).2.2
        simpa [HeightOneSpectrum.under, Formalism.L2.Host.OverP] using this
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
        · exact levelLe_one_two (G.ch.lev0 _ k1 k2 PP h0).1
        · exact (G.ch.lev1 _ k1 k2 PP h1).1
    · exact Or.inl (G.ch.unr _ k1 k2 PP h)
  have hcu := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ k1 k2)
  have hci : (G.ch.chiH (D.R.m - i)).HasInf (embT D) (fun τ => 2 * cen D sc.cGap τ (D.R.m - i)) := G.ch.inf _ k1 k2
  let χc : HeckeU D 0 := ofChar 0 _ _ hcu hci (GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial D _ _ 2 (fun q hq => (hS q hq).1) hlev)
    (GlobalTheory.T.heckeCharacter_bounded_conductor_kills_idele_norms D _ _ _ 2 (G.ch.triv _ k1 k2) hci (fun q hq => (hS q hq).1) hlev)
    (fun τ => by simp) (GlobalTheory.T.heckeCharacter_nonInert_bounded_level_kills_units D _ _ 2 hS hlev)
  have he := L.C.isEta
  have hei : L.C.eta.HasInf (embT D) (fun _ => 1) := fun a => by
    rw [he.inf a, ← D.eTau.prod_comp]
    rfl
  let χe : HeckeU D 1 := ofChar 1 L.C.eta _ he.unitary hei (GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
    (GlobalTheory.T.unramified_eta_character_kills_finite_idele_norm D _ he) (fun τ => by simp) (GlobalTheory.T.heckeCharacter_nonInert_bounded_level_kills_units D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
  have hr : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have hx := (ranks_exact D i j).1
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨w, hw⟩ := odd_sLen D
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨inv _ χc (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_zero, mul_one, inv_f]
    rfl
  · refine ⟨inv _ (mul 1 χc χe (by decide)) (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_one, inv_f, mul_f]
    rfl

end GlobalTheory.FunObj.SqNum
