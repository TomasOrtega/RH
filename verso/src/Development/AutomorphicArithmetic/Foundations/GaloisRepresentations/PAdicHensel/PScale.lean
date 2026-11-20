import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v s`.
-/
private lemma val_alg (v : HeightOneSpectrum ℤ) (s : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) s) = v.valuation ℚ s :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v s

/- English proof (translation)
Take `⟨g, hg⟩` from `IsPrincipalIdealRing.principal v.asIdeal`. Establish `hg' : v.asIdeal = Ideal.span {g}` using `hg`. Use `⟨g.natAbs, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hg', Int.natAbs_eq_zero.mp h0]`. Simplify using the standard rewrite rules. Rewrite using `[hg', Ideal.span_singleton_eq_span_singleton]`. Conclude with `Int.associated_natAbs g`.
-/
private lemma exists_gen (v : HeightOneSpectrum ℤ) :
    ∃ q : ℕ, q ≠ 0 ∧ v.asIdeal = Ideal.span {(q : ℤ)} := by
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal v.asIdeal
  have hg' : v.asIdeal = Ideal.span {g} := hg
  refine ⟨g.natAbs, ?_, ?_⟩
  · intro h0
    apply v.ne_bot
    rw [hg', Int.natAbs_eq_zero.mp h0]
    simp
  · rw [hg', Ideal.span_singleton_eq_span_singleton]
    exact Int.associated_natAbs g

/- English proof (translation)
Rewrite using `[← v.valuation_of_algebraMap (K := ℚ)]`. Simplify using the standard rewrite rules.
-/
private lemma val_nat (v : HeightOneSpectrum ℤ) (q : ℕ) :
    v.valuation ℚ (q : ℚ) = v.intValuation (q : ℤ) := by
  rw [← v.valuation_of_algebraMap (K := ℚ)]
  simp

/- English proof (translation)
Rewrite using `[val_nat]`. Conclude with `HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast h0) h`.
-/
private lemma val_self (v : HeightOneSpectrum ℤ) {q : ℕ} (h0 : q ≠ 0)
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) : v.valuation ℚ (q : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [val_nat]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast h0) h

/- English proof (translation)
Rewrite using `[val_nat]`. Apply `le_antisymm (w.intValuation_le_one _)` to reduce the goal to its premises. Rewrite using `[← not_lt, w.intValuation_lt_one_iff_mem]`. Introduce `hm`. Apply `hne` to reduce the goal to its premises.

Establish `hle : v.asIdeal ≤ w.asIdeal`. Rewrite using `[h, Ideal.span_le]`. Simplify using `using hm`. Conclude with `HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)`.
-/
private lemma val_other (v w : HeightOneSpectrum ℤ) {q : ℕ}
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) (hne : w ≠ v) : w.valuation ℚ (q : ℚ) = 1 := by
  rw [val_nat]
  apply le_antisymm (w.intValuation_le_one _)
  rw [← not_lt, w.intValuation_lt_one_iff_mem]
  intro hm
  apply hne
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [h, Ideal.span_le]
    simpa using hm
  exact HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

/- English proof (translation)
Establish `ht` using `(t : AfP p).2`. Establish `hti` using `((t⁻¹ : (AfP p)ˣ) : AfP p).2`. Use `(Filter.eventually_cofinite.mp (ht.and hti)).subset ?_` and prove the remaining obligations. Introduce `v hv hboth`. Apply `hv` to reduce the goal to its premises.

Take `⟨h1, h2⟩` from `hboth`. Establish `h1' : Valued.v (AfP.eval v (t : AfP p)) ≤ 1` using `h1`. Establish `h2' : Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) ≤ 1` using `h2`. Establish `hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`.

Apply `le_antisymm h1'` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma finite_ne_one (p : ℕ) (t : (AfP p)ˣ) :
    {v : AwayP p | Valued.v (AfP.eval v (t : AfP p)) ≠ 1}.Finite := by
  have ht := (t : AfP p).2
  have hti := ((t⁻¹ : (AfP p)ˣ) : AfP p).2
  refine (Filter.eventually_cofinite.mp (ht.and hti)).subset ?_
  intro v hv hboth
  apply hv
  obtain ⟨h1, h2⟩ := hboth
  have h1' : Valued.v (AfP.eval v (t : AfP p)) ≤ 1 := h1
  have h2' : Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) ≤ 1 := h2
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  apply le_antisymm h1'
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
    _ ≤ Valued.v (AfP.eval v (t : AfP p)) * 1 := mul_le_mul_right h2' _
    _ = _ := mul_one _

/- English proof (translation)
Introduce `h`. Establish `hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Rewrite `hm` using `[h, zero_mul]`. Conclude with `zero_ne_one hm`.
-/
private lemma val_ne_zero (p : ℕ) (t : (AfP p)ˣ) (v : AwayP p) :
    Valued.v (AfP.eval v (t : AfP p)) ≠ 0 := by
  intro h
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [h, zero_mul] at hm
  exact zero_ne_one hm

/- English proof (translation)
Introduce `p t`. Use `choose q hq0 hq using fun v : AwayP p => exists_gen v.1`. Set `n : AwayP p → ℤ` to `fun v => WithZero.log (Valued.v (AfP.eval v (t : AfP p)))`. Set `S` to `(finite_ne_one p t).toFinset`. Use `⟨∏ v ∈ S, ((q v : ℚ) ^ (-n v)), ?_, ?_⟩` and prove the remaining obligations.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `v _`. Apply `zpow_pos` to reduce the goal to its premises. Conclude with `Nat.pos_of_ne_zero (hq0 v)` after adjusting the coercions. Introduce `w`.

Rewrite using `[val_alg, map_prod]`. Establish `hterm : ∀ v ∈ S, w.1.valuation ℚ ((q v : ℚ) ^ (-n v)) = if v = w then WithZero.exp (n v) else 1`. Introduce `v _`. Rewrite using `[map_zpow₀]`. Use `split_ifs with hvw`.

Substitute `hvw` using the available equality. Rewrite using `[val_self v.1 (hq0 v) (hq v), ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules. Rewrite using `[val_other v.1 w.1 (hq v) (fun h => hvw (Subtype.ext h.symm)), _root_.one_zpow]`. Rewrite using `[Finset.prod_congr rfl hterm, Finset.prod_ite_eq']`.

Use `split_ifs with hw`. Conclude with `(WithZero.exp_log (val_ne_zero p t w)).symm`. Establish `: ¬ Valued.v (AfP.eval w (t : AfP p)) ≠ 1`. Introduce `h`. Apply `hw` to reduce the goal to its premises.

Simplify `h` using `[S]`. Conclude with `not_not.mp this`.
-/
theorem UpperTheory.Gal.G1.pScale :
    Scale := by
  intro p t
  classical
  choose q hq0 hq using fun v : AwayP p => exists_gen v.1
  let n : AwayP p → ℤ := fun v => WithZero.log (Valued.v (AfP.eval v (t : AfP p)))
  let S := (finite_ne_one p t).toFinset
  refine ⟨∏ v ∈ S, ((q v : ℚ) ^ (-n v)), ?_, ?_⟩
  · apply Finset.prod_pos
    intro v _
    apply zpow_pos
    exact_mod_cast Nat.pos_of_ne_zero (hq0 v)
  · intro w
    rw [val_alg, map_prod]
    have hterm : ∀ v ∈ S, w.1.valuation ℚ ((q v : ℚ) ^ (-n v)) =
        if v = w then WithZero.exp (n v) else 1 := by
      intro v _
      rw [map_zpow₀]
      split_ifs with hvw
      · subst hvw
        rw [val_self v.1 (hq0 v) (hq v), ← WithZero.exp_zsmul]
        simp
      · rw [val_other v.1 w.1 (hq v) (fun h => hvw (Subtype.ext h.symm)), _root_.one_zpow]
    rw [Finset.prod_congr rfl hterm, Finset.prod_ite_eq']
    split_ifs with hw
    · exact (WithZero.exp_log (val_ne_zero p t w)).symm
    · have : ¬ Valued.v (AfP.eval w (t : AfP p)) ≠ 1 := by
        intro h
        apply hw
        simpa [S] using h
      exact not_not.mp this
