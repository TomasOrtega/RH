import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.VarZeroSubVarOneNe

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

def bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p] :=
  fun i => if i = 0 then 0 else Z3 W wq

/- English proof (translation)
Introduce `i`. Unfold `bZ`. Use `split_ifs`. Conclude with `map_zero _`. Conclude with `constantCoeff_thirdRoot W wq`.
-/
theorem bZ_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    ∀ i, MvPowerSeries.constantCoeff (bZ W wq i) = 0 := by
  intro i
  unfold bZ
  split_ifs
  · exact map_zero _
  · exact constantCoeff_thirdRoot W wq

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero (bZ_const W wq)`.
-/
theorem hasSubst_bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.HasSubst (bZ W wq) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (bZ_const W wq)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fch_eq (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    Fch W wq = MvPowerSeries.subst (bZ W wq) (Z3 W wq) := rfl

/- English proof (translation)
Rewrite using `[PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hb]`.
-/
theorem subst_psubst {a : MvPowerSeries (Fin 2) ℂ_[p]} (ha : PowerSeries.HasSubst a)
    {b : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hb]

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Unfold `PI.AddIntG.flog`. Rewrite using `[PowerSeries.coeff_mk, if_pos rfl]`.
-/
theorem constantCoeff_flog' (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold PI.AddIntG.flog
  rw [PowerSeries.coeff_mk, if_pos rfl]

/- English proof (translation)
Rewrite using `[Fch_eq]`. Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_bZ W wq) (bZ_const W wq) (constantCoeff_thirdRoot W wq)`.
-/
theorem constantCoeff_Fch (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Fch W wq) = 0 := by
  rw [Fch_eq]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_bZ W wq) (bZ_const W wq) (constantCoeff_thirdRoot W wq)

/- English proof (translation)
Establish `hZ` using `thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h`. Establish `hb : ∀ i, bZ W wq i ∈ SerS S (Fin 2)`. Introduce `i`. Unfold `bZ`. Use `split_ifs`.

Conclude with `zero_mem _`. Conclude with `hZ`. Rewrite using `[Fch_eq]`. Conclude with `(mem_SerS S _).mp (mvsubst_mem_SerS S (bZ_const W wq) hb hZ)`.
-/
theorem Fch_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, MvPowerSeries.coeff n (Fch W wq) ∈ S := by
  have hZ := thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h
  have hb : ∀ i, bZ W wq i ∈ SerS S (Fin 2) := by
    intro i
    unfold bZ
    split_ifs
    · exact zero_mem _
    · exact hZ
  rw [Fch_eq]
  exact (mem_SerS S _).mp (mvsubst_mem_SerS S (bZ_const W wq) hb hZ)

/- English proof (translation)
Establish `hA` using `abel h`. Establish `hb` using `hasSubst_bZ W wq`. Establish `hX : ∀ i : Fin 2, PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p])` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Establish `hZ : PowerSeries.HasSubst (Z3 W wq)` using `PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_thirdRoot W wq)`. Establish `hB` using `congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) hb) hA`.

Rewrite `hB` using `[map_add, map_add, map_zero, MvPowerSeries.coe_substAlgHom, subst_psubst (hX 0) hb, subst_psubst (hX 1) hb, subst_psubst hZ hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, ← Fch_eq]`. Establish `h0 : bZ W wq 0 = 0` using `by simp [bZ]`. Establish `h1' : bZ W wq 1 = Z3 W wq` using `by simp [bZ]`. Rewrite `hB` using `[h0, h1', PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_flog' W wq)]`. Take the linear combination `hB - hA`.
-/
theorem flog_Fch {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Fch W wq) (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) := by
  have hA := abel h
  have hb := hasSubst_bZ W wq
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hZ : PowerSeries.HasSubst (Z3 W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_thirdRoot W wq)
  have hB := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) hb) hA
  rw [map_add, map_add, map_zero, MvPowerSeries.coe_substAlgHom, subst_psubst (hX 0) hb,
    subst_psubst (hX 1) hb, subst_psubst hZ hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    ← Fch_eq] at hB
  have h0 : bZ W wq 0 = 0 := by simp [bZ]
  have h1' : bZ W wq 1 = Z3 W wq := by simp [bZ]
  rw [h0, h1', PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_flog' W wq)] at hB
  linear_combination hB - hA

/- English proof (translation)
Introduce `p _ S W wq h1 h2 h3 h4 h6 h`. Conclude with `⟨Fch W wq, Fch_mem h1 h2 h3 h4 h6 h, constantCoeff_Fch W wq, flog_Fch h⟩`.
-/
theorem formalGroupLawExists : KeyF := by
  intro p _ S W wq h1 h2 h3 h4 h6 h
  exact ⟨Fch W wq, Fch_mem h1 h2 h3 h4 h6 h, constantCoeff_Fch W wq, flog_Fch h⟩

end PI.AddIntG.Wk
