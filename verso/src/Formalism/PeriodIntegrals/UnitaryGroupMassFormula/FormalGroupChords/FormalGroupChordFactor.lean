import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.SubstBivariateSeriesDifferencePair

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS mvsubst_mem_SerS subst_mem_SerS)

/- English proof (translation)
Take `⟨S, hS⟩` from `PI.AddIntG.Wk.exists_intS p`. Establish `hwS : ∀ n, PowerSeries.coeff n wq ∈ S` using `PI.AddIntG.Wk.wq_mem ((hS _).2 h1) ((hS _).2 h2) ((hS _).2 h3) ((hS _).2 h4) ((hS _).2 h6) (isWq_bridge hW)`. Establish `hiS` using `iW_mem ((hS _).2 h1) ((hS _).2 h3) hwS`. Establish `hl0` using `flog_const W wq`. Establish `hl1 : PowerSeries.coeff 1 (flog W wq) = 1` using `PI.AddIntG.Wk.coeff_one_flog (isWq_bridge hW)`.

Establish `hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X` using `PI.AddIntG.Wk.subst_left_inv hl0 hl1 hex0 hex`. Establish `hwq0` using `wq_const' hW`. Establish `ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0` using `MvPowerSeries.constantCoeff_X 0`. Establish `hb0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0` using `MvPowerSeries.constantCoeff_X 1`. Establish `hia0` using `constantCoeff_inverse_variable W wq 0`.

Establish `hib0` using `constantCoeff_inverse_variable W wq 1`. Establish `haS` using `X_mem_SerS S 0`. Establish `hbS` using `X_mem_SerS S 1`. Establish `hiaS : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) ∈ SerS S (Fin 2)` using `subst_mem_SerS S ha0 haS (serS_unit hiS)`. Establish `hibS : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) ∈ SerS S (Fin 2)` using `subst_mem_SerS S hb0 hbS (serS_unit hiS)`.

Establish `hwaS : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq ∈ SerS S (Fin 2)` using `subst_mem_SerS S ha0 haS (serS_unit hwS)`. Establish `hwbS : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq ∈ SerS S (Fin 2)` using `subst_mem_SerS S hb0 hbS (serS_unit hwS)`. Establish `hFS : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)` using `(mem_SerS S _).2 fun e => (hS _).2 (hF e)`. Establish `hF'S : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)`. Rewrite using `[F'_eq hW]`.

Conclude with `mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simpa using hib0⟩) (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using hibS⟩) hFS`. Establish `hPS : Pser wq ∈ SerS S (Fin 2)`. Rewrite using `[Pser]`. Conclude with `sub_mem (mul_mem (pow_mem haS 2) hwaS) (mul_mem (pow_mem hbS 2) hwbS)`. Establish `hXS : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ_[p]) ∈ S`.

Introduce `n`. Rewrite using `[PowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `S.one_mem`. Conclude with `S.zero_mem`.

Establish `hsX : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PowerSeries.X : PowerSeries ℂ_[p]) = MvPowerSeries.X 0` using `PowerSeries.subst_X (PowerSeries.HasSubst.X 0)`. Establish `hX0ne : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0`. Introduce `h0`. Use `congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h0` as an intermediate fact. Simplify using `at this`.

Establish `hX1ne : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0`. Introduce `h0`. Use `congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) h0` as an intermediate fact. Simplify using `at this`. Take `⟨P1, hP1S, hPd⟩` from `fact_div PowerSeries.constantCoeff_X hXS hPS (by rw [hsX]; exact P_at_diagonal wq)`.

Rewrite `hPd` using `[hsX]`. Take `⟨U', hU'S, hF'd⟩` from `fact_div PowerSeries.constantCoeff_X hXS hF'S (by rw [hsX]; exact F'_at_aa hex0)`. Rewrite `hF'd` using `[hsX]`. Take `⟨U, hUS, hFd⟩` from `fact_div (iW_const W wq) hiS hFS (F_at_ia hW hex0)`. Establish `hs` using `hasSubst2 ha0 hia0`.

Establish `hDa : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 1`. Rewrite using `[cc_psubst ha0, D_const]`. Establish `hne : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) - MvPowerSeries.X 0 ≠ 0`. Introduce `h0`. Establish `hiD` using `mulD_at W wq (PowerSeries.HasSubst.X (S := ℂ_[p]) (0 : Fin 2))`.

Establish `h5 : MvPowerSeries.X 0 * (1 + PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 0`. Take the linear combination `hiD - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) * h0`. Break down `mul_eq_zero.1 h5 with h | h` into its components or cases. Conclude with `hX0ne h`. Establish `h7` using `congrArg MvPowerSeries.constantCoeff h`.

Rewrite `h7` using `[map_add, map_one, hDa, map_zero]`. Evaluate the numerical expressions using `at h7`. Establish `hP1z : MvPowerSeries.subst ![MvPowerSeries.X 0, PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)] P1 = 0`. Establish `hz` using `P_at_inverse hW`. Rewrite `hz` using `[hPd, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_sub hs, subst_pair_first_variable hs, subst_pair_second_variable hs]`.

Conclude with `(mul_eq_zero.1 hz).resolve_left hne`. Take `⟨P2, hP2S, hP1d⟩` from `fact_div (iW_const W wq) hiS hP1S hP1z`. Establish `hs0` using `hasSubst2 (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := ℂ_[p]))) hb0`. Establish `hφ0 : ∀ i, MvPowerSeries.constantCoeff (![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] i) = 0` using `Fin.forall_fin_two.2 ⟨by simp, by simpa using hb0⟩`. Establish `e_ia0 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) = 0`.

Rewrite using `[subst_pair_first_series hs0, PowerSeries.subst_zero_of_constantCoeff_zero (iW_const W wq)]`. Establish `hUc : MvPowerSeries.constantCoeff U = 1`. Establish `e` using `congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hFd`. Rewrite `e` using `[formal_add_first_zero hexl, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_sub hs0, subst_pair_second_variable hs0, e_ia0, sub_zero]`. Establish `e2 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] U = 1`.

Use `mul_left_cancel₀ hX1ne ?_` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `e.symm`. Rewrite using `[← cc_msubst hs0 hφ0 U, e2, map_one]`. Establish `hU'c : MvPowerSeries.constantCoeff U' = -1`.

Establish `e` using `congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hF'd`. Rewrite `e` using `[formal_sub_first_zero hW hexl, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_sub hs0, subst_pair_second_variable hs0, subst_pair_first_variable hs0, sub_zero]`. Establish `hiD1` using `mulD_at W wq (PowerSeries.HasSubst.X (S := ℂ_[p]) (1 : Fin 2))`. Establish `hDb : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 1`. Rewrite using `[cc_psubst hb0, D_const]`.

Establish `h5 : MvPowerSeries.X 1 * (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] U' * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) + 1) = 0`. Take the linear combination `hiD1 - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) * e`. Establish `h7` using `congrArg MvPowerSeries.constantCoeff ((mul_eq_zero.1 h5).resolve_left hX1ne)`. Rewrite `h7` using `[map_add, map_mul, hDb, map_one, map_zero, mul_one, cc_msubst hs0 hφ0 U']`. Take the linear combination `h7`.

Establish `hP2c : MvPowerSeries.constantCoeff P2 = -1`. Establish `hPP : Pser wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) * P2)`. Rewrite using `[hPd, hP1d]`. Establish `e` using `congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hPP`. Rewrite `e` using `[Pser]`.

Simplify using `only [MvPowerSeries.subst_sub hs0, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_pow hs0, subst_pair_first_variable hs0, subst_pair_second_variable hs0, subst_pair_second_series hs0, e_ia0] at e`. Establish `h5 : MvPowerSeries.X 1 ^ 2 * (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] P2 + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 0`. Take the linear combination `-e`. Establish `h7` using `congrArg MvPowerSeries.constantCoeff ((mul_eq_zero.1 h5).resolve_left (pow_ne_zero 2 hX1ne))`. Rewrite `h7` using `[map_add, cc_psubst hb0, hwq0, map_zero, cc_msubst hs0 hφ0 P2]`.

Take the linear combination `h7`. Establish `hwa0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 1`. Rewrite using `[cc_psubst ha0, hwq0]`. Establish `hwb0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 1`. Rewrite using `[cc_psubst hb0, hwq0]`.

Establish `hV0 : MvPowerSeries.constantCoeff (-U') = 1` using `by rw [map_neg, hU'c, neg_neg]`. Establish `hUi : U * U⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel _ (by rw [hUc]; exact one_ne_zero)`. Establish `hVi : (-U') * (-U')⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel _ (by rw [hV0]; exact one_ne_zero)`. Establish `hwa : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel _ (by rw [hwa0]; exact one_ne_zero)`. Establish `hwb : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel _ (by rw [hwb0]; exact one_ne_zero)`.

Establish `hnS : -(P2 * U⁻¹ * (-U')⁻¹) * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ ∈ SerS S (Fin 2)` using `mul_mem (mul_mem (neg_mem (mul_mem (mul_mem hP2S (inv_mem_SerS S hUc hUS)) (inv_mem_SerS S hV0 (neg_mem hU'S)))) (inv_mem_SerS S hwa0 hwaS)) (inv_mem_SerS S hwb0 hwbS)`. Use `⟨-(P2 * U⁻¹ * (-U')⁻¹) * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `e`. Conclude with `(hS _).1 ((mem_SerS S _).1 hnS e)`. Simplify using `only [map_mul, map_neg, MvPowerSeries.constantCoeff_inv, hP2c, hUc, hU'c, hwa0, hwb0]`.

Evaluate the numerical expressions. Establish `hPd' : MvPowerSeries.X 0 ^ 2 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq - MvPowerSeries.X 1 ^ 2 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P1` using `hPd`. Rewrite using `[hFd, hF'd]`. Take the linear combination `(-(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hwa + ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hwb …`.
-/
theorem main_mv (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p])
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (hW : IsWq W wq) (hex0 : PowerSeries.constantCoeff ex = 0)
    (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : IntegralMv (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) ℂ_[p])) :
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      MvPowerSeries.X 0 ^ 2 * (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ -
          MvPowerSeries.X 1 ^ 2 * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ =
        add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) *
          sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) * n := by
  obtain ⟨S, hS⟩ := PI.AddIntG.Wk.exists_intS p
  have hwS : ∀ n, PowerSeries.coeff n wq ∈ S :=
    PI.AddIntG.Wk.wq_mem ((hS _).2 h1) ((hS _).2 h2) ((hS _).2 h3) ((hS _).2 h4) ((hS _).2 h6) (isWq_bridge hW)
  have hiS := iW_mem ((hS _).2 h1) ((hS _).2 h3) hwS
  have hl0 := flog_const W wq
  have hl1 : PowerSeries.coeff 1 (flog W wq) = 1 := PI.AddIntG.Wk.coeff_one_flog (isWq_bridge hW)
  have hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X := PI.AddIntG.Wk.subst_left_inv hl0 hl1 hex0 hex
  have hwq0 := wq_const' hW
  have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hb0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hia0 := constantCoeff_inverse_variable W wq 0
  have hib0 := constantCoeff_inverse_variable W wq 1
  have haS := X_mem_SerS S 0
  have hbS := X_mem_SerS S 1
  have hiaS : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) ∈ SerS S (Fin 2) :=
    subst_mem_SerS S ha0 haS (serS_unit hiS)
  have hibS : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) ∈ SerS S (Fin 2) :=
    subst_mem_SerS S hb0 hbS (serS_unit hiS)
  have hwaS : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq ∈ SerS S (Fin 2) :=
    subst_mem_SerS S ha0 haS (serS_unit hwS)
  have hwbS : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq ∈ SerS S (Fin 2) :=
    subst_mem_SerS S hb0 hbS (serS_unit hwS)
  have hFS : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) :=
    (mem_SerS S _).2 fun e => (hS _).2 (hF e)
  have hF'S : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := by
    rw [F'_eq hW]
    exact mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simpa using hib0⟩)
      (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using hibS⟩) hFS
  have hPS : Pser wq ∈ SerS S (Fin 2) := by
    rw [Pser]
    exact sub_mem (mul_mem (pow_mem haS 2) hwaS) (mul_mem (pow_mem hbS 2) hwbS)
  have hXS : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ_[p]) ∈ S := by
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hsX : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PowerSeries.X : PowerSeries ℂ_[p]) =
      MvPowerSeries.X 0 := PowerSeries.subst_X (PowerSeries.HasSubst.X 0)
  have hX0ne : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h0
    simp at this
  have hX1ne : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) h0
    simp at this

  obtain ⟨P1, hP1S, hPd⟩ := fact_div PowerSeries.constantCoeff_X hXS hPS (by rw [hsX]; exact P_at_diagonal wq)
  rw [hsX] at hPd
  obtain ⟨U', hU'S, hF'd⟩ := fact_div PowerSeries.constantCoeff_X hXS hF'S (by rw [hsX]; exact F'_at_aa hex0)
  rw [hsX] at hF'd
  obtain ⟨U, hUS, hFd⟩ := fact_div (iW_const W wq) hiS hFS (F_at_ia hW hex0)
  have hs := hasSubst2 ha0 hia0
  have hDa : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 1 := by
    rw [cc_psubst ha0, D_const]
  have hne : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) - MvPowerSeries.X 0 ≠ 0 := by
    intro h0
    have hiD := mulD_at W wq (PowerSeries.HasSubst.X (S := ℂ_[p]) (0 : Fin 2))
    have h5 : MvPowerSeries.X 0 * (1 + PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p])
        (Dser W wq)) = 0 := by
      linear_combination hiD - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) * h0
    rcases mul_eq_zero.1 h5 with h | h
    · exact hX0ne h
    · have h7 := congrArg MvPowerSeries.constantCoeff h
      rw [map_add, map_one, hDa, map_zero] at h7
      norm_num at h7
  have hP1z : MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)] P1 = 0 := by
    have hz := P_at_inverse hW
    rw [hPd, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_sub hs, subst_pair_first_variable hs, subst_pair_second_variable hs] at hz
    exact (mul_eq_zero.1 hz).resolve_left hne
  obtain ⟨P2, hP2S, hP1d⟩ := fact_div (iW_const W wq) hiS hP1S hP1z

  have hs0 := hasSubst2 (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := ℂ_[p]))) hb0
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff
      (![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] i) = 0 :=
    Fin.forall_fin_two.2 ⟨by simp, by simpa using hb0⟩
  have e_ia0 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) = 0 := by
    rw [subst_pair_first_series hs0, PowerSeries.subst_zero_of_constantCoeff_zero (iW_const W wq)]
  have hUc : MvPowerSeries.constantCoeff U = 1 := by
    have e := congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hFd
    rw [formal_add_first_zero hexl, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_sub hs0, subst_pair_second_variable hs0, e_ia0, sub_zero] at e
    have e2 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] U = 1 := by
      refine mul_left_cancel₀ hX1ne ?_
      rw [mul_one]; exact e.symm
    rw [← cc_msubst hs0 hφ0 U, e2, map_one]
  have hU'c : MvPowerSeries.constantCoeff U' = -1 := by
    have e := congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hF'd
    rw [formal_sub_first_zero hW hexl, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_sub hs0, subst_pair_second_variable hs0, subst_pair_first_variable hs0,
      sub_zero] at e
    have hiD1 := mulD_at W wq (PowerSeries.HasSubst.X (S := ℂ_[p]) (1 : Fin 2))
    have hDb : MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq)) = 1 := by
      rw [cc_psubst hb0, D_const]
    have h5 : MvPowerSeries.X 1 * (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] U' *
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) + 1) = 0 := by
      linear_combination hiD1 - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (Dser W wq) * e
    have h7 := congrArg MvPowerSeries.constantCoeff ((mul_eq_zero.1 h5).resolve_left hX1ne)
    rw [map_add, map_mul, hDb, map_one, map_zero, mul_one, cc_msubst hs0 hφ0 U'] at h7
    linear_combination h7
  have hP2c : MvPowerSeries.constantCoeff P2 = -1 := by
    have hPP : Pser wq = (MvPowerSeries.X 1 - MvPowerSeries.X 0) *
        ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) * P2) := by
      rw [hPd, hP1d]
    have e := congrArg (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]) hPP
    rw [Pser] at e
    simp only [MvPowerSeries.subst_sub hs0, MvPowerSeries.subst_mul hs0, MvPowerSeries.subst_pow hs0, subst_pair_first_variable hs0,
      subst_pair_second_variable hs0, subst_pair_second_series hs0, e_ia0] at e
    have h5 : MvPowerSeries.X 1 ^ 2 * (MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] P2 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 0 := by
      linear_combination -e
    have h7 := congrArg MvPowerSeries.constantCoeff ((mul_eq_zero.1 h5).resolve_left (pow_ne_zero 2 hX1ne))
    rw [map_add, cc_psubst hb0, hwq0, map_zero, cc_msubst hs0 hφ0 P2] at h7
    linear_combination h7

  have hwa0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 1 := by
    rw [cc_psubst ha0, hwq0]
  have hwb0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq) = 1 := by
    rw [cc_psubst hb0, hwq0]
  have hV0 : MvPowerSeries.constantCoeff (-U') = 1 := by rw [map_neg, hU'c, neg_neg]
  have hUi : U * U⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hUc]; exact one_ne_zero)
  have hVi : (-U') * (-U')⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hV0]; exact one_ne_zero)
  have hwa : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq *
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hwa0]; exact one_ne_zero)
  have hwb : PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq *
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hwb0]; exact one_ne_zero)
  have hnS : -(P2 * U⁻¹ * (-U')⁻¹) * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ ∈ SerS S (Fin 2) :=
    mul_mem (mul_mem (neg_mem (mul_mem (mul_mem hP2S (inv_mem_SerS S hUc hUS)) (inv_mem_SerS S hV0 (neg_mem hU'S))))
      (inv_mem_SerS S hwa0 hwaS)) (inv_mem_SerS S hwb0 hwbS)
  refine ⟨-(P2 * U⁻¹ * (-U')⁻¹) * (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
      (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹, ?_, ?_, ?_⟩
  · intro e
    exact (hS _).1 ((mem_SerS S _).1 hnS e)
  · simp only [map_mul, map_neg, MvPowerSeries.constantCoeff_inv, hP2c, hUc, hU'c, hwa0, hwb0]
    norm_num
  · have hPd' : MvPowerSeries.X 0 ^ 2 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq -
        MvPowerSeries.X 1 ^ 2 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq =
        (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P1 := hPd
    rw [hFd, hF'd]
    linear_combination
      (-(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hwa +
      ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 *
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hwb +
      ((PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hPd' +
      ((PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (MvPowerSeries.X 1 - MvPowerSeries.X 0)) * hP1d -
      ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) *
        (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P2 *
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹) * hUi -
      ((MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) *
        (MvPowerSeries.X 1 - MvPowerSeries.X 0) * P2 *
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ *
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ * U * U⁻¹) * hVi

/- English proof (translation)
Introduce `p _ W wq ex h1 h2 h3 h4 h6 _ hW hex0 hex hF`. Conclude with `main_mv p W wq ex h1 h2 h3 h4 h6 hW hex0 hex hF`.
-/
theorem formal_group_chord_factor : PI.FglChordFactor.Lemma := by
  intro p _ W wq ex h1 h2 h3 h4 h6 _ hW hex0 hex hF
  exact main_mv p W wq ex h1 h2 h3 h4 h6 hW hex0 hex hF

end PI.FglChordFactor.Wk
