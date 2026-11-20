import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS subst_mem_SerS subst_psubst)

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨by simpa using hu, by simpa using hv⟩)`.
-/
theorem hasSubst2 {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨by simpa using hu, by simpa using hv⟩)

/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_X hs]`. Simplify using the standard rewrite rules.
-/
theorem subst_pair_first_variable {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = u := by
  rw [MvPowerSeries.subst_X hs]; simp

/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_X hs]`. Simplify using the standard rewrite rules.
-/
theorem subst_pair_second_variable {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = v := by
  rw [MvPowerSeries.subst_X hs]; simp

/- English proof (translation)
Rewrite using `[subst_psubst (PowerSeries.HasSubst.X 0) hs, subst_pair_first_variable hs]`.
-/
theorem subst_pair_first_series {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst u f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 0) hs, subst_pair_first_variable hs]

/- English proof (translation)
Rewrite using `[subst_psubst (PowerSeries.HasSubst.X 1) hs, subst_pair_second_variable hs]`.
-/
theorem subst_pair_second_series {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst v f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 1) hs, subst_pair_second_variable hs]

/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_comp_subst_apply hs' hs]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem subst_pair_comp {u v u' v' : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v])
    (hs' : MvPowerSeries.HasSubst ![u', v']) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.subst ![u', v'] H) =
      MvPowerSeries.subst ![MvPowerSeries.subst ![u, v] u', MvPowerSeries.subst ![u, v] v'] H := by
  rw [MvPowerSeries.subst_comp_subst_apply hs' hs]
  congr 1
  funext i
  fin_cases i <;> simp

/- English proof (translation)
Establish `e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] = MvPowerSeries.X`. Apply the tactic sequence `funext i; fin_cases i <;> simp`. Rewrite using `[e, MvPowerSeries.subst_self]`. Both sides reduce to the same expression.
-/
theorem subst_pair_variables_self (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] H = H := by
  have e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i; fin_cases i <;> simp
  rw [e, MvPowerSeries.subst_self]; rfl

/- English proof (translation)
Rewrite using `[mem_SerS]`. Introduce `e`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `S.one_mem`.

Conclude with `S.zero_mem`.
-/
theorem X_mem_SerS (S : Subring ℂ_[p]) (i : Fin 2) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
  rw [mem_SerS]; intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

/- English proof (translation)
Rewrite using `[mem_SerS]`. Introduce `e`. Establish `he : e = Finsupp.single () (e ())` using `by ext; simp`. Rewrite using `[he]`. Conclude with `h (e ())`.
-/
theorem serS_unit {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} (h : ∀ n, PowerSeries.coeff n f ∈ S) :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS]; intro e
  have he : e = Finsupp.single () (e ()) := by ext; simp
  rw [he]; exact h (e ())

/- English proof (translation)
Use `⟨fun h n => ?_, serS_unit⟩` and prove the remaining obligations. Conclude with `(mem_SerS S _).1 h (Finsupp.single () n)`.
-/
theorem serS_unit_iff {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by
  refine ⟨fun h n => ?_, serS_unit⟩
  exact (mem_SerS S _).1 h (Finsupp.single () n)

/- English proof (translation)
Rewrite using `[MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]`. Use `congr 1`. Simplify using `[Finsupp.single_le_iff]`.
-/
theorem coeff_mul_second_variable (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.X 1) =
      if 1 ≤ e 1 then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Apply the tactic sequence `intro h; ext j; fin_cases j <;> simp [h]`.
-/
theorem single0_iff (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

/- English proof (translation)
Use `set a : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 0 with ha`. Use `set b : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 1 with hb`. Use `set s : MvPowerSeries (Fin 2) ℂ_[p] := PowerSeries.subst a f with hs`. Establish `ha0 : MvPowerSeries.constantCoeff a = 0` using `MvPowerSeries.constantCoeff_X 0`. Establish `hb0 : MvPowerSeries.constantCoeff b = 0` using `MvPowerSeries.constantCoeff_X 1`.

Establish `hs0 : MvPowerSeries.constantCoeff s = 0` using `PowerSeries.constantCoeff_subst_eq_zero ha0 f hf0`. Establish `haS : a ∈ SerS S (Fin 2)` using `X_mem_SerS S 0`. Establish `hbS : b ∈ SerS S (Fin 2)` using `X_mem_SerS S 1`. Establish `hsS : s ∈ SerS S (Fin 2)` using `subst_mem_SerS S ha0 haS (serS_unit hfS)`. Establish `hP : MvPowerSeries.HasSubst ![a, b + s]` using `hasSubst2 ha0 (by rw [map_add, hb0, hs0, add_zero])`.

Establish `hM : MvPowerSeries.HasSubst ![a, b - s]` using `hasSubst2 ha0 (by rw [map_sub, hb0, hs0, sub_zero])`. Establish `hZ : MvPowerSeries.HasSubst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])]` using `hasSubst2 ha0 (map_zero _)`. Use `set Hp := MvPowerSeries.subst ![a, b + s] H with hHp`. Establish `hback : MvPowerSeries.subst ![a, b - s] Hp = H`. Rewrite using `[hHp, subst_pair_comp hM hP, subst_pair_first_variable hM, MvPowerSeries.subst_add hM, subst_pair_second_variable hM, hs, subst_pair_first_series hM, ← hs, sub_add_cancel, ha, hb, subst_pair_variables_self]`.

Establish `hzero : MvPowerSeries.subst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] Hp = 0`. Rewrite using `[hHp, subst_pair_comp hZ hP, subst_pair_first_variable hZ, MvPowerSeries.subst_add hZ, subst_pair_second_variable hZ, hs, subst_pair_first_series hZ, ← hs, zero_add]`. Conclude with `hz`. Use `set Qt : MvPowerSeries (Fin 2) ℂ_[p] := fun e => MvPowerSeries.coeff (e + Finsupp.single 1 1) Hp with hQt`. Use `set r : PowerSeries ℂ_[p] := PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n) Hp with hr`.

Establish `hdec : Hp = Qt * b + PowerSeries.subst a r`. Use extensionality with `e`. Rewrite using `[map_add, hb, coeff_mul_second_variable, ha, PowerSeries.coeff_subst_single]`. Distinguish the cases in `he : e 1 = 0`. Establish `he' : e = Finsupp.single 0 (e 0)` using `(single0_iff e).2 he`.

Rewrite using `[if_neg (by omega), if_pos he', zero_add, hr, PowerSeries.coeff_mk, ← he']`. Establish `he' : ¬ e = Finsupp.single 0 (e 0)` using `fun h => he ((single0_iff e).1 h)`. Rewrite using `[if_pos (by omega), if_neg he', add_zero]`. Use `show MvPowerSeries.coeff e Hp = MvPowerSeries.coeff (e - Finsupp.single 1 1 + Finsupp.single 1 1) Hp`. Rewrite using `[tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))]`.

Establish `hR : PowerSeries.subst a r = 0`. Establish `h1` using `hzero`. Rewrite `h1` using `[hdec, MvPowerSeries.subst_add hZ, MvPowerSeries.subst_mul hZ, subst_pair_second_variable hZ, mul_zero, zero_add, ha, subst_pair_first_series hZ]`. Conclude with `h1`. Establish `hdec' : Hp = Qt * b` using `by rw [hdec, hR, add_zero]`.

Establish `hQtS : Qt ∈ SerS S (Fin 2)`. Establish `hHpS : Hp ∈ SerS S (Fin 2)` using `mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩) (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using add_mem hbS hsS⟩) hH`. Rewrite using `[mem_SerS]`. Introduce `e`. Conclude with `(mem_SerS S Hp).1 hHpS _`.

Use `⟨MvPowerSeries.subst ![a, b - s] Qt, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩) (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using sub_mem hbS hsS⟩) hQtS`. Use `conv_lhs => rw [← hback, hdec', MvPowerSeries.subst_mul hM, hb, subst_pair_second_variable hM]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fact_div {S : Subring ℂ_[p]} {H : MvPowerSeries (Fin 2) ℂ_[p]} {f : PowerSeries ℂ_[p]}
    (hf0 : PowerSeries.constantCoeff f = 0) (hfS : ∀ n, PowerSeries.coeff n f ∈ S) (hH : H ∈ SerS S (Fin 2))
    (hz : MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f] H = 0) :
    ∃ Q ∈ SerS S (Fin 2),
      H = (MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) * Q := by
  set a : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 0 with ha
  set b : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 1 with hb
  set s : MvPowerSeries (Fin 2) ℂ_[p] := PowerSeries.subst a f with hs
  have ha0 : MvPowerSeries.constantCoeff a = 0 := MvPowerSeries.constantCoeff_X 0
  have hb0 : MvPowerSeries.constantCoeff b = 0 := MvPowerSeries.constantCoeff_X 1
  have hs0 : MvPowerSeries.constantCoeff s = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 f hf0
  have haS : a ∈ SerS S (Fin 2) := X_mem_SerS S 0
  have hbS : b ∈ SerS S (Fin 2) := X_mem_SerS S 1
  have hsS : s ∈ SerS S (Fin 2) := subst_mem_SerS S ha0 haS (serS_unit hfS)
  have hP : MvPowerSeries.HasSubst ![a, b + s] := hasSubst2 ha0 (by rw [map_add, hb0, hs0, add_zero])
  have hM : MvPowerSeries.HasSubst ![a, b - s] := hasSubst2 ha0 (by rw [map_sub, hb0, hs0, sub_zero])
  have hZ : MvPowerSeries.HasSubst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] := hasSubst2 ha0 (map_zero _)
  set Hp := MvPowerSeries.subst ![a, b + s] H with hHp

  have hback : MvPowerSeries.subst ![a, b - s] Hp = H := by
    rw [hHp, subst_pair_comp hM hP, subst_pair_first_variable hM, MvPowerSeries.subst_add hM, subst_pair_second_variable hM, hs, subst_pair_first_series hM, ← hs,
      sub_add_cancel, ha, hb, subst_pair_variables_self]

  have hzero : MvPowerSeries.subst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] Hp = 0 := by
    rw [hHp, subst_pair_comp hZ hP, subst_pair_first_variable hZ, MvPowerSeries.subst_add hZ, subst_pair_second_variable hZ, hs, subst_pair_first_series hZ, ← hs,
      zero_add]
    exact hz

  set Qt : MvPowerSeries (Fin 2) ℂ_[p] := fun e => MvPowerSeries.coeff (e + Finsupp.single 1 1) Hp with hQt
  set r : PowerSeries ℂ_[p] := PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n) Hp with hr
  have hdec : Hp = Qt * b + PowerSeries.subst a r := by
    ext e
    rw [map_add, hb, coeff_mul_second_variable, ha, PowerSeries.coeff_subst_single]
    by_cases he : e 1 = 0
    · have he' : e = Finsupp.single 0 (e 0) := (single0_iff e).2 he
      rw [if_neg (by omega), if_pos he', zero_add, hr, PowerSeries.coeff_mk, ← he']
    · have he' : ¬ e = Finsupp.single 0 (e 0) := fun h => he ((single0_iff e).1 h)
      rw [if_pos (by omega), if_neg he', add_zero]
      show MvPowerSeries.coeff e Hp = MvPowerSeries.coeff (e - Finsupp.single 1 1 + Finsupp.single 1 1) Hp
      rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))]
  have hR : PowerSeries.subst a r = 0 := by
    have h1 := hzero
    rw [hdec, MvPowerSeries.subst_add hZ, MvPowerSeries.subst_mul hZ, subst_pair_second_variable hZ, mul_zero, zero_add, ha,
      subst_pair_first_series hZ] at h1
    exact h1
  have hdec' : Hp = Qt * b := by rw [hdec, hR, add_zero]
  have hQtS : Qt ∈ SerS S (Fin 2) := by
    have hHpS : Hp ∈ SerS S (Fin 2) :=
      mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
        (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using add_mem hbS hsS⟩) hH
    rw [mem_SerS]; intro e
    exact (mem_SerS S Hp).1 hHpS _
  refine ⟨MvPowerSeries.subst ![a, b - s] Qt, ?_, ?_⟩
  · exact mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
      (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using sub_mem hbS hsS⟩) hQtS
  · conv_lhs => rw [← hback, hdec', MvPowerSeries.subst_mul hM, hb, subst_pair_second_variable hM]
    ring

end PI.FglChordFactor.Wk
