import Formalism.PeriodIntegrals.OrbAddUp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.SolvableEquivalenceOfBaseChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.ExpSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetRen

noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbJet.OrbW PI.OrbShared

def orbE (D : D7) (p : ℕ) (r : Pl D) : ZMod (nP D p) ↪ Pl D := ⟨orbMap D p r, orbMap_inj D p r⟩

abbrev pE (D : D7) (p : ℕ) (r : Pl D) (γ : Type) : ZMod (nP D p) × γ ↪ Pl D × γ := OJ.pEmb (orbE D p r) γ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pE_apply (D : D7) (p : ℕ) (r : Pl D) (γ : Type) (v : ZMod (nP D p) × γ) :
    pE D p r γ v = (orbMap D p r v.1, v.2) := rfl

/- English proof (translation)
Use `show (logPl D p v) 0 = 0`. Unfold `logPl`. Use `Finset.sum_eq_zero fun e _ => if_neg fun h => ?_` and prove the remaining obligations. Conclude with `pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)`.
-/
theorem cc_log (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) :
    constantCoeff (logPl D p v) = 0 := by
  show (logPl D p v) 0 = 0
  unfold logPl
  refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
  exact pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)

/- English proof (translation)
Use `first`. Consider the case `exact Finsupp.degree_single v k`. Consider the case `(rcases eq_or_ne k 0 with rfl | hk`. Simplify using the standard rewrite rules. Simplify using `[Finsupp.degree, Finsupp.support_single_ne_zero _ hk])`.
-/
theorem degree_single' {σ : Type*} (v : σ) (k : ℕ) : (Finsupp.single v k).degree = k := by
  first
  | exact Finsupp.degree_single v k
  | (rcases eq_or_ne k 0 with rfl | hk
     · simp
     · classical
       simp [Finsupp.degree, Finsupp.support_single_ne_zero _ hk])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem JetTdeg_eq_degree {σ : Type*} (m : σ →₀ ℕ) : JetTdeg m = m.degree := rfl

/- English proof (translation)
Establish `hp : 1 < l` using `(Fact.out : l.Prime).one_lt`. Use `show (jetLogG l d w) n = _`. Unfold `jetLogG`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules.

Introduce `e _ he`. Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Rewrite `hn` using `[degree_single']`. Establish `h2 : 1 < l ^ 2` using `by nlinarith`.

Establish `h3 : 1 < (l ^ 2) ^ e` using `by first`. Consider the case `exact Nat.one_lt_pow he h2`. Consider the case `exact Nat.one_lt_pow (Nat.pos_of_ne_zero he) h2`. Consider the case `exact one_lt_pow₀ h2 he`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h`.
-/
theorem jet_lin (l d : ℕ) [Fact l.Prime] {β : Type*} (w : ZMod d × β) (n : ZMod d × β →₀ ℕ) (hn : n.degree ≤ 1) :
    coeff n (jetLogG l d w) = if n = single w 1 then 1 else 0 := by
  have hp : 1 < l := (Fact.out : l.Prime).one_lt
  show (jetLogG l d w) n = _
  unfold jetLogG
  rw [Finset.sum_eq_single 0]
  · simp
  · intro e _ he
    rw [if_neg]
    rintro rfl
    rw [degree_single'] at hn
    have h2 : 1 < l ^ 2 := by nlinarith
    have h3 : 1 < (l ^ 2) ^ e := by
      first
      | exact Nat.one_lt_pow he h2
      | exact Nat.one_lt_pow (Nat.pos_of_ne_zero he) h2
      | exact one_lt_pow₀ h2 he
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/- English proof (translation)
Establish `hp : 1 < p` using `(Fact.out : p.Prime).one_lt`. Use `show (logPl D p v) n = _`. Unfold `logPl`. Rewrite using `[Finset.sum_eq_single 0]`. Establish `h0 : backPl D p v.1 0 = v.1` using `by first`.

Consider the case `simpa [backPl] using posPl_zero D p v.1`. Consider the case `simp [backPl, posPl_zero]`. Consider the case `simp [backPl, posPl, partner]`. Simplify using `[h0]`. Introduce `e _ he`.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Rewrite `hn` using `[degree_single']`. Establish `h2 : 1 < p ^ 2` using `by nlinarith`. Establish `h3 : 1 < (p ^ 2) ^ e` using `by first`.

Consider the case `exact Nat.one_lt_pow he h2`. Consider the case `exact Nat.one_lt_pow (Nat.pos_of_ne_zero he) h2`. Consider the case `exact one_lt_pow₀ h2 he`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Conclude with `absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h`.
-/
theorem log_lin (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) (n : Pl D × β →₀ ℕ) (hn : n.degree ≤ 1) :
    coeff n (logPl D p v) = if n = single v 1 then 1 else 0 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  show (logPl D p v) n = _
  unfold logPl
  rw [Finset.sum_eq_single 0]
  · have h0 : backPl D p v.1 0 = v.1 := by
      first
      | simpa [backPl] using posPl_zero D p v.1
      | simp [backPl, posPl_zero]
      | simp [backPl, posPl, partner]
    simp [h0]
  · intro e _ he
    rw [if_neg]
    rintro rfl
    rw [degree_single'] at hn
    have h2 : 1 < p ^ 2 := by nlinarith
    have h3 : 1 < (p ^ 2) ^ e := by
      first
      | exact Nat.one_lt_pow he h2
      | exact Nat.one_lt_pow (Nat.pos_of_ne_zero he) h2
      | exact one_lt_pow₀ h2 he
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/- English proof (translation)
Introduce `v n hn`. Rewrite using `[MvPowerSeries.coeff_C_mul, jet_lin l d v n hn]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isTri_jet (l d : ℕ) [Fact l.Prime] [NeZero d] {β : Type} [Finite β] (ep : ℂ_[l]) :
    Tri.IsTri ep (fun w : ZMod d × β => C ep * jetLogG l d w) := by
  intro v n hn
  rw [MvPowerSeries.coeff_C_mul, jet_lin l d v n hn]
  split_ifs <;> simp

/- English proof (translation)
Introduce `v n hn`. Rewrite using `[MvPowerSeries.coeff_C_mul, log_lin D p v n hn]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isTri_log (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} [Finite β] (ep : ℂ_[p]) :
    Tri.IsTri ep (fun v : Pl D × β => C ep * logPl D p v) := by
  intro v n hn
  rw [MvPowerSeries.coeff_C_mul, log_lin D p v n hn]
  split_ifs <;> simp

/- English proof (translation)
Establish `key : ∀ (s : ZMod (nP D p)) (e : ℕ), backPl D p (orbMap D p r s) e = orbMap D p r (s - ↑e)` using `by first`. Consider the case `exact orbMap_sub D p r`. Consider the case `exact backPl_orbMap D p r`. Establish `hinj : Function.Injective (Finsupp.mapDomain (pE D p r β) : (ZMod (nP D p) × β →₀ ℕ) → (Pl D × β →₀ ℕ))` using `Finsupp.mapDomain_injective (pE D p r β).injective`. Establish `hdeg : ∀ n : ZMod (nP D p) × β →₀ ℕ, JetTdeg (Finsupp.mapDomain (pE D p r β) n) = JetTdeg n`.

Introduce `n`. Rewrite using `[JetTdeg_eq_degree, JetTdeg_eq_degree]`. Use `Finsupp.induction n ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a b f _ _ ih first`.

Consider the case `rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.degree_add, Finsupp.degree_add, degree_single', degree_single', ih]`. Consider the case `simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single, degree_single', ih]`. Establish `hidx : ∀ e : ℕ, Finsupp.single (backPl D p ((pE D p r β) w).1 (2 * e), ((pE D p r β) w).2) ((p ^ 2) ^ e) = Finsupp.mapDomain (pE D p r β) (Finsupp.single (w.1 - 2 * (e : ZMod (nP D p)), w.2) ((p ^ 2) ^ e))`. Introduce `e`. Simplify using `only [Finsupp.mapDomain_single, pE_apply, key, Nat.cast_mul, Nat.cast_ofNat]`.

Use function extensionality and compare the values at `m`. Use `show renameFun (pE D p r β) (jetLogG p (nP D p) w) m = logPl D p ((pE D p r β) w) m`. Unfold `renameFun Filter.TendstoCofinite.mapDomain`. Distinguish the cases in `hm : ∃ n, Finsupp.mapDomain (pE D p r β) n = m`. Take `⟨n, rfl⟩` from `hm`.

Use `(Finset.sum_eq_single n ?_ ?_).trans ?_` and prove the remaining obligations. Introduce `n' hn' hne`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Simplify using `using hn'`. Introduce `hn`. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Unfold `jetLogG logPl`. Rewrite using `[hdeg]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Simplify using `only [hidx, hinj.eq_iff]`. Use `(Finset.sum_eq_zero ?_).trans ?_` and prove the remaining obligations.

Introduce `n hn`. It suffices to derive a contradiction. Apply `hm` to reduce the goal to its premises. Conclude with `⟨n, by simpa using hn⟩`. Use `symm`.

Unfold `logPl`. Use `Finset.sum_eq_zero fun e _ => if_neg ?_` and prove the remaining obligations. Rewrite using `[hidx]`. Conclude with `fun h => hm ⟨_, h.symm⟩`.
-/
theorem rename_jet (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (r : Pl D) (w : ZMod (nP D p) × β) :
    rename (pE D p r β) (jetLogG p (nP D p) w) = logPl D p (pE D p r β w) := by
  have key : ∀ (s : ZMod (nP D p)) (e : ℕ), backPl D p (orbMap D p r s) e = orbMap D p r (s - ↑e) := by
    first
    | exact orbMap_sub D p r
    | exact backPl_orbMap D p r
  have hinj : Function.Injective
      (Finsupp.mapDomain (pE D p r β) : (ZMod (nP D p) × β →₀ ℕ) → (Pl D × β →₀ ℕ)) :=
    Finsupp.mapDomain_injective (pE D p r β).injective
  have hdeg : ∀ n : ZMod (nP D p) × β →₀ ℕ,
      JetTdeg (Finsupp.mapDomain (pE D p r β) n) = JetTdeg n := by
    intro n
    rw [JetTdeg_eq_degree, JetTdeg_eq_degree]
    refine Finsupp.induction n ?_ ?_
    · simp
    · intro a b f _ _ ih
      first
      | rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.degree_add, Finsupp.degree_add,
          degree_single', degree_single', ih]
      | simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single, degree_single', ih]
  have hidx : ∀ e : ℕ, Finsupp.single (backPl D p ((pE D p r β) w).1 (2 * e), ((pE D p r β) w).2) ((p ^ 2) ^ e)
      = Finsupp.mapDomain (pE D p r β) (Finsupp.single (w.1 - 2 * (e : ZMod (nP D p)), w.2) ((p ^ 2) ^ e)) := by
    intro e
    simp only [Finsupp.mapDomain_single, pE_apply, key, Nat.cast_mul, Nat.cast_ofNat]
  funext m
  show renameFun (pE D p r β) (jetLogG p (nP D p) w) m = logPl D p ((pE D p r β) w) m
  unfold renameFun Filter.TendstoCofinite.mapDomain
  by_cases hm : ∃ n, Finsupp.mapDomain (pE D p r β) n = m
  · obtain ⟨n, rfl⟩ := hm
    refine (Finset.sum_eq_single n ?_ ?_).trans ?_
    · intro n' hn' hne
      exfalso
      apply hne
      apply hinj
      simpa using hn'
    · intro hn
      exfalso
      apply hn
      simp
    · unfold jetLogG logPl
      rw [hdeg]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [hidx, hinj.eq_iff]
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro n hn
      exfalso
      apply hm
      exact ⟨n, by simpa using hn⟩
    · symm
      unfold logPl
      refine Finset.sum_eq_zero fun e _ => if_neg ?_
      rw [hidx]
      exact fun h => hm ⟨_, h.symm⟩

end PI.OrbJet.AU

end
