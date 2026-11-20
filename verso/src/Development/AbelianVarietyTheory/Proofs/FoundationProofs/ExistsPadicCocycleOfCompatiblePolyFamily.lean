import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOnStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousLiftCompatible
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.CocLift

open MvPolynomial CongruenceSubgroup

/- English proof (translation)
Rewrite `hδ`, the goal using `[Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hδ`. Establish `key : ∀ x : ℤ, ZMod.castHom h (ZMod a) (x : ZMod b) = (x : ZMod a)` using `fun x => map_intCast _ x`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← key, h1, map_one]`.

Rewrite using `[← key, h2, map_zero]`. Rewrite using `[← key, h3, map_zero]`. Rewrite using `[← key, h4, map_one]`.
-/
theorem gamma_of_dvd {a b : ℕ} (h : a ∣ b) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma b) : δ ∈ Gamma a := by
  rw [Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ x : ℤ, ZMod.castHom h (ZMod a) (x : ZMod b) = (x : ZMod a) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, map_one]
  · rw [← key, h2, map_zero]
  · rw [← key, h3, map_zero]
  · rw [← key, h4, map_one]

/- English proof (translation)
Establish `h1` using `Gamma_mem.mp (gamma_of_dvd hN hδ)`. Establish `h2` using `Gamma_mem.mp (gamma_of_dvd hl hδ)`. Use `Subgroup.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Gamma1_mem]`. Conclude with `⟨h1.1, h1.2.2.2, h1.2.2.1⟩`.

Rewrite using `[Gamma0_mem]`. Conclude with `h2.2.2.1`.
-/
theorem gamma_le_gam {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    δ ∈ Gam N l := by
  have h1 := Gamma_mem.mp (gamma_of_dvd hN hδ)
  have h2 := Gamma_mem.mp (gamma_of_dvd hl hδ)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]; exact ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · rw [Gamma0_mem]; exact h2.2.2.1

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `Gamma_mem.mp hδ`. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]`.
-/
theorem entries_of_gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma K) :
    ∀ i j, (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.mp hδ
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Use `haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Take `⟨z', hz', hz'n⟩` from `GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ (n + 1)`. Use `set c := ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) with hc`.

Establish `L` using `GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))`. Establish `L'` using `GlobalTheory.KZ.polySlash_laws (ZMod (l ^ (n + 1)))`. Set `r : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))` to `fun δ => MvPolynomial.map c (z' δ)`. Establish `hr : IsCoc w (Gam N l) r`. Use `⟨fun γ hγ => (hz'.1 γ hγ).map c, fun γ hγ δ hδ => ?_⟩` and prove the remaining obligations.

Simplify using `only [r]`. Rewrite using `[hz'.2 γ hγ δ hδ, map_add, L'.2.2.2.2.1 _ c]`. Establish `hnear : Near r y`. Take `⟨M1, hM1, h1⟩` from `hz'n`. Take `⟨M2, hM2, h2⟩` from `hΦ.2.2.2 n`.

Take `⟨M3, hM3, h3⟩` from `hyn`. Use `⟨M1 * M2 * M3, by positivity, fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `d1` using `gamma_of_dvd (Dvd.intro _ rfl |>.trans (Dvd.intro _ rfl)) hδ`. Establish `d2` using `gamma_of_dvd ((Dvd.intro_left _ rfl).trans (Dvd.intro _ rfl)) hδ`. Establish `d3` using `gamma_of_dvd (Dvd.intro_left _ rfl) hδ`.

Simplify using `only [r]`. Rewrite using `[h1 δ d1]`. Conclude with `(h2 δ d2).trans (h3 δ d3).symm`. Take `⟨p, hph, hpγ⟩` from `GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn N l w n hN hp hl2 hlN hw r y hr hy hnear`. Set `pt : MvPolynomial (Fin 2) (ZMod (l ^ (n + 1)))` to `∑ m ∈ p.support, MvPolynomial.monomial m (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))`.

Establish `hpc : ∀ m, pt.coeff m = (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))`. Introduce `m`. Simplify using `only [pt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite `h` using `[MvPolynomial.notMem_support_iff]`. Rewrite using `[h, ZMod.val_zero, Nat.cast_zero]`. Establish `hmap : MvPolynomial.map c pt = p`. Use extensionality with `m`.

Rewrite using `[MvPolynomial.coeff_map, hpc, map_natCast, ZMod.natCast_zmod_val]`. Establish `hpth : pt.IsHomogeneous w`. Introduce `m hm`. Apply `hph` to reduce the goal to its premises. Introduce `h0`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[hpc, h0, ZMod.val_zero, Nat.cast_zero]`. Use `⟨fun δ => z' δ - (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) pt - pt), ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hz'.1 γ hγ).sub ((L'.2.2.1 _ w pt hpth).sub hpth)`. Simplify using `only`.

Rewrite using `[hz'.2 γ hγ δ hδ, Matrix.SpecialLinearGroup.coe_mul, L'.1, map_sub, map_sub]`. Normalize the expressions using the abelian group laws. Take `⟨M1, hM1, h1⟩` from `hz'n`. Use `⟨M1 * l ^ (n + 1), Nat.mul_pos hM1 (pow_pos hp.pos _), fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `d1` using `gamma_of_dvd (Dvd.intro _ rfl) hδ`.

Establish `d2` using `gamma_of_dvd (Dvd.intro_left _ rfl) hδ`. Simplify using `only`. Rewrite using `[L'.2.2.2.2.2.1 _ 1 pt (entries_of_gamma d2), L'.2.1, sub_self, sub_zero, h1 δ d1]`. Introduce `γ hγ`. Simplify using `only`.

Rewrite using `[map_sub, map_sub, L'.2.2.2.2.1 _ c, hmap, ← hpγ γ hγ]`. Simplify using `only [r]`. Normalize the expressions using the abelian group laws.
-/
theorem step (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w)
    (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) (hΦ : IsFam l w (Gam N l) Φ)
    (n : ℕ) (y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (hy : IsCoc w (Gam N l) y) (hyn : Near y (Φ n)) :
    ∃ y' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))), IsCoc w (Gam N l) y' ∧ Near y' (Φ (n + 1)) ∧
      ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (y' γ) = y γ := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨z', hz', hz'n⟩ := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ (n + 1)
  set c := ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) with hc
  have L := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  have L' := GlobalTheory.KZ.polySlash_laws (ZMod (l ^ (n + 1)))
  let r : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) := fun δ => MvPolynomial.map c (z' δ)
  have hr : IsCoc w (Gam N l) r := by
    refine ⟨fun γ hγ => (hz'.1 γ hγ).map c, fun γ hγ δ hδ => ?_⟩
    simp only [r]
    rw [hz'.2 γ hγ δ hδ, map_add, L'.2.2.2.2.1 _ c]
  have hnear : Near r y := by
    obtain ⟨M1, hM1, h1⟩ := hz'n
    obtain ⟨M2, hM2, h2⟩ := hΦ.2.2.2 n
    obtain ⟨M3, hM3, h3⟩ := hyn
    refine ⟨M1 * M2 * M3, by positivity, fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl |>.trans (Dvd.intro _ rfl)) hδ
    have d2 := gamma_of_dvd ((Dvd.intro_left _ rfl).trans (Dvd.intro _ rfl)) hδ
    have d3 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only [r]
    rw [h1 δ d1]
    exact (h2 δ d2).trans (h3 δ d3).symm
  obtain ⟨p, hph, hpγ⟩ := GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn N l w n hN hp hl2 hlN hw r y hr hy hnear
  let pt : MvPolynomial (Fin 2) (ZMod (l ^ (n + 1))) :=
    ∑ m ∈ p.support, MvPolynomial.monomial m (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1)))
  have hpc : ∀ m, pt.coeff m = (((p.coeff m).val : ℕ) : ZMod (l ^ (n + 1))) := by
    intro m
    simp only [pt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff] at h
      rw [h, ZMod.val_zero, Nat.cast_zero]
  have hmap : MvPolynomial.map c pt = p := by
    ext m
    rw [MvPolynomial.coeff_map, hpc, map_natCast, ZMod.natCast_zmod_val]
  have hpth : pt.IsHomogeneous w := by
    intro m hm
    apply hph
    intro h0
    apply hm
    rw [hpc, h0, ZMod.val_zero, Nat.cast_zero]
  refine ⟨fun δ => z' δ - (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) pt - pt), ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩, ?_, ?_⟩
  · exact (hz'.1 γ hγ).sub ((L'.2.2.1 _ w pt hpth).sub hpth)
  · simp only
    rw [hz'.2 γ hγ δ hδ, Matrix.SpecialLinearGroup.coe_mul, L'.1, map_sub, map_sub]
    abel
  · obtain ⟨M1, hM1, h1⟩ := hz'n
    refine ⟨M1 * l ^ (n + 1), Nat.mul_pos hM1 (pow_pos hp.pos _), fun δ hδ => ?_⟩
    have d1 := gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := gamma_of_dvd (Dvd.intro_left _ rfl) hδ
    simp only
    rw [L'.2.2.2.2.2.1 _ 1 pt (entries_of_gamma d2), L'.2.1, sub_self, sub_zero, h1 δ d1]
  · intro γ hγ
    simp only
    rw [map_sub, map_sub, L'.2.2.2.2.1 _ c, hmap, ← hpγ γ hγ]
    simp only [r]
    abel

end GlobalTheory.KZ.H3.CocLift

namespace GlobalTheory.KZ.H3

open Classical in

/- English proof (translation)
Introduce `N l w _ hN hl2 hlN hw Φ hΦ`. Establish `hp : l.Prime` using `Fact.out`. Establish `lev` using `GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ`. Use `choose F hF1 hF2 hF3 using CocLift.step N l w hN hl2 hlN hw Φ hΦ`. Set `seq : (n : ℕ) → {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)}` to `fun n => Nat.rec (motive := fun n => {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)}) ⟨(lev 0).choose, (lev 0).choose_spec⟩ (fun n y => ⟨F n y.1 y.2.1 y.2.2, hF1 n y.1 y.2.1 y.2.2, hF2 n y.1 y.2.1 y.2.2⟩) n`.

Establish `hseq : ∀ n, ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) ((seq (n + 1)).1 γ) = (seq n).1 γ` using `fun n => hF3 n (seq n).1 (seq n).2.1 (seq n).2.2`. Set `fam : SL(2, ℤ) → (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n))` to `fun δ n => if δ ∈ Gam N l then (seq n).1 δ else 0`. Establish `hfam : ∀ δ ∈ Gam N l, ∀ n, fam δ n = (seq n).1 δ` using `fun δ hδ n => if_pos hδ`. Establish `hhom : ∀ δ n, (fam δ n).IsHomogeneous w`. Introduce `δ n`.

Distinguish the cases in `hδ : δ ∈ Gam N l`. Rewrite using `[hfam δ hδ]`. Conclude with `(seq n).2.1.1 δ hδ`. Simplify using `only [fam, if_neg hδ]`. Conclude with `MvPolynomial.isHomogeneous_zero _ _ _`.

Establish `hcomp : ∀ δ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (fam δ (n + 1)) = fam δ n`. Introduce `δ n`. Distinguish the cases in `hδ : δ ∈ Gam N l`. Rewrite using `[hfam δ hδ, hfam δ hδ]`. Conclude with `hseq n δ hδ`.

Simplify using `only [fam, if_neg hδ, map_zero]`. Use `choose q hq using fun δ => homogeneous_lift_compatible l w (fam δ) (hhom δ) (hcomp δ)`. Establish `L` using `GlobalTheory.KZ.polySlash_laws ℤ_[l]`. Use `⟨q, ⟨fun γ _ => (hq γ).1, fun γ hγ δ hδ => ?_⟩, fun n => ?_⟩` and prove the remaining obligations. Use `((hq (γ * δ)).2.2 _ fun n => ?_).symm` and prove the remaining obligations.

Establish `hγδ : γ * δ ∈ Gam N l` using `(Gam N l).mul_mem hγ hδ`. Rewrite using `[map_add, L.2.2.2.2.1 _ _, (hq γ).2.1 n, (hq δ).2.1 n, hfam γ hγ, hfam δ hδ, hfam _ hγδ, (seq n).2.1.2 γ hγ δ hδ]`. Take `⟨M, hM, hMδ⟩` from `(seq n).2.2`. Use `⟨M * (N * l), Nat.mul_pos hM (Nat.mul_pos hN hp.pos), fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `d1` using `CocLift.gamma_of_dvd (Dvd.intro _ rfl) hδ`.

Establish `d2` using `CocLift.gamma_le_gam (N := N) (l := l) ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl)) ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)) hδ`. Simplify using `only`. Rewrite using `[(hq δ).2.1 n, hfam δ d2]`. Conclude with `hMδ δ d1`.
-/
theorem cocycle_lift_of_fam : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ →
    ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) ℤ_[l], IsCoc w (Gam N l) z ∧
      ∀ n, Near (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (z δ)) (Φ n) := by
  intro N l w _ hN hl2 hlN hw Φ hΦ
  have hp : l.Prime := Fact.out
  have lev := GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence N l w hN hp hl2 hlN hw Φ hΦ
  choose F hF1 hF2 hF3 using CocLift.step N l w hN hl2 hlN hw Φ hΦ
  let seq : (n : ℕ) → {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) // IsCoc w (Gam N l) y ∧ Near y (Φ n)} :=
    fun n => Nat.rec (motive := fun n => {y : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) //
        IsCoc w (Gam N l) y ∧ Near y (Φ n)})
      ⟨(lev 0).choose, (lev 0).choose_spec⟩
      (fun n y => ⟨F n y.1 y.2.1 y.2.2, hF1 n y.1 y.2.1 y.2.2, hF2 n y.1 y.2.1 y.2.2⟩) n
  have hseq : ∀ n, ∀ γ ∈ Gam N l, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      ((seq (n + 1)).1 γ) = (seq n).1 γ :=
    fun n => hF3 n (seq n).1 (seq n).2.1 (seq n).2.2
  let fam : SL(2, ℤ) → (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n)) :=
    fun δ n => if δ ∈ Gam N l then (seq n).1 δ else 0
  have hfam : ∀ δ ∈ Gam N l, ∀ n, fam δ n = (seq n).1 δ := fun δ hδ n => if_pos hδ
  have hhom : ∀ δ n, (fam δ n).IsHomogeneous w := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ]; exact (seq n).2.1.1 δ hδ
    · simp only [fam, if_neg hδ]; exact MvPolynomial.isHomogeneous_zero _ _ _
  have hcomp : ∀ δ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)))
      (fam δ (n + 1)) = fam δ n := by
    intro δ n
    by_cases hδ : δ ∈ Gam N l
    · rw [hfam δ hδ, hfam δ hδ]; exact hseq n δ hδ
    · simp only [fam, if_neg hδ, map_zero]
  choose q hq using fun δ => homogeneous_lift_compatible l w (fam δ) (hhom δ) (hcomp δ)
  have L := GlobalTheory.KZ.polySlash_laws ℤ_[l]
  refine ⟨q, ⟨fun γ _ => (hq γ).1, fun γ hγ δ hδ => ?_⟩, fun n => ?_⟩
  · refine ((hq (γ * δ)).2.2 _ fun n => ?_).symm
    have hγδ : γ * δ ∈ Gam N l := (Gam N l).mul_mem hγ hδ
    rw [map_add, L.2.2.2.2.1 _ _, (hq γ).2.1 n, (hq δ).2.1 n, hfam γ hγ, hfam δ hδ, hfam _ hγδ,
      (seq n).2.1.2 γ hγ δ hδ]
  · obtain ⟨M, hM, hMδ⟩ := (seq n).2.2
    refine ⟨M * (N * l), Nat.mul_pos hM (Nat.mul_pos hN hp.pos), fun δ hδ => ?_⟩
    have d1 := CocLift.gamma_of_dvd (Dvd.intro _ rfl) hδ
    have d2 := CocLift.gamma_le_gam (N := N) (l := l) ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl))
      ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)) hδ
    simp only
    rw [(hq δ).2.1 n, hfam δ d2]
    exact hMδ δ d1

end GlobalTheory.KZ.H3
