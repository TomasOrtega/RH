import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LogSigmaOnePullbackSpec

noncomputable section

namespace Formalism.L2.Th1.C

namespace Dict

section Alg

variable {K : Type} [Field K] {σ τ : Type} {l linv : PowerSeries K}

/- English proof (translation)
Establish `hsa : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K, MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f`. Introduce `b hb f`. Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b) (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hb)) hsa]`.

Establish `hu' : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hu l h.1`. Establish `hv' : MvPowerSeries.constantCoeff (PowerSeries.subst v l) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hv l h.1`. Unfold `fadd`. Rewrite using `[psub _ (by rw [map_add, hu', hv', add_zero]), ← MvPowerSeries.coe_substAlgHom hsa, map_add, MvPowerSeries.coe_substAlgHom hsa, psub u hu, psub v hv]`.
-/
theorem substMv_fadd [Finite σ] (h : IsLogPair l linv) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (fadd l linv u v) =
      fadd l linv (MvPowerSeries.subst a u) (MvPowerSeries.subst a v) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K,
      MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f := by
    intro b hb f
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hb)) hsa]
  have hu' : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hu l h.1
  have hv' : MvPowerSeries.constantCoeff (PowerSeries.subst v l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hv l h.1
  unfold fadd
  rw [psub _ (by rw [map_add, hu', hv', add_zero]), ← MvPowerSeries.coe_substAlgHom hsa, map_add,
    MvPowerSeries.coe_substAlgHom hsa, psub u hu, psub v hv]

/- English proof (translation)
Establish `hsa : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K, MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f`. Introduce `b hb f`. Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b) (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hb)) hsa]`.

Establish `hu' : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hu l h.1`. Establish `hv' : MvPowerSeries.constantCoeff (PowerSeries.subst v l) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hv l h.1`. Establish `hf : MvPowerSeries.constantCoeff (fadd l linv u v) = 0` using `PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hu', hv', add_zero]) linv h.2.2.1`. Unfold `be0`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hsa, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hsa, psub _ hf, psub u hu, psub v hv, substMv_fadd h hu hv ha]`.
-/
theorem subst_biextension_form [Finite σ] (h : IsLogPair l linv) (ph : PowerSeries K) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (be0 l linv ph u v) =
      be0 l linv ph (MvPowerSeries.subst a u) (MvPowerSeries.subst a v) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K,
      MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f := by
    intro b hb f
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hb)) hsa]
  have hu' : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hu l h.1
  have hv' : MvPowerSeries.constantCoeff (PowerSeries.subst v l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hv l h.1
  have hf : MvPowerSeries.constantCoeff (fadd l linv u v) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hu', hv', add_zero]) linv h.2.2.1
  unfold be0
  rw [← MvPowerSeries.coe_substAlgHom hsa, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hsa,
    psub _ hf, psub u hu, psub v hv, substMv_fadd h hu hv ha]

/- English proof (translation)
Introduce `s`. Use `fin_cases s`. Simplify using `using hx`. Simplify using `using hy`.
-/
theorem constantCoeff_vecCons_pair_eq_zero {x y : MvPowerSeries τ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ s : Fin 2, MvPowerSeries.constantCoeff (![x, y] s) = 0 := by
  intro s
  fin_cases s
  · simpa using hx
  · simpa using hy

/- English proof (translation)
Introduce `s`. Use `fin_cases s`. Simplify using `using hx`. Simplify using `using hy`. Simplify using `using hz`.
-/
theorem constantCoeff_vec_three_eq_zero {x y z : MvPowerSeries τ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (hz : MvPowerSeries.constantCoeff z = 0) :
    ∀ s : Fin 3, MvPowerSeries.constantCoeff (![x, y, z] s) = 0 := by
  intro s
  fin_cases s
  · simpa using hx
  · simpa using hy
  · simpa using hz

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cob_eq (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph =
      be0 l linv ph (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := rfl

/- English proof (translation)
Rewrite using `[cob_eq, subst_biextension_form h ph (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1) (constantCoeff_vecCons_pair_eq_zero hx hy), MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vecCons_pair_eq_zero hx hy)), MvPowerSeries.subs …`. Both sides reduce to the same expression.
-/
theorem subst_cob (h : IsLogPair l linv) (ph : PowerSeries K) {x y : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst ![x, y]
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph) =
      be0 l linv ph x y := by
  rw [cob_eq, subst_biextension_form h ph (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1)
      (constantCoeff_vecCons_pair_eq_zero hx hy),
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vecCons_pair_eq_zero hx hy)),
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vecCons_pair_eq_zero hx hy))]
  rfl

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0` using `MvPowerSeries.constantCoeff_X 0`. Establish `h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0` using `MvPowerSeries.constantCoeff_X 1`. Establish `h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0` using `MvPowerSeries.constantCoeff_X 2`. Establish `e : Formalism.InvariantFactorPaths.G7.in3 (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) = fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3))` using `(Pts.fadd_eq_substMv h h0 h1).symm`. Rewrite using `[Formalism.InvariantFactorPaths.G7.d1, e, subst_cob h ph (Pts.constantCoeff_fadd h h0 h1) h2, subst_cob h ph h0 h2, subst_cob h ph h1 h2]`.
-/
theorem coboundary_formal_add_biextension (h : IsLogPair l linv) (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.d1 (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph) =
      be0 l linv ph (fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3)))
          (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (1 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 2
  have e : Formalism.InvariantFactorPaths.G7.in3
      (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) =
      fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3)) :=
    (Pts.fadd_eq_substMv h h0 h1).symm
  rw [Formalism.InvariantFactorPaths.G7.d1, e, subst_cob h ph (Pts.constantCoeff_fadd h h0 h1) h2, subst_cob h ph h0 h2,
    subst_cob h ph h1 h2]

/- English proof (translation)
Establish `e : PowerSeries.subst F l = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l + PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l`. Use `hc` as an intermediate fact. Rewrite `this` using `[Formalism.InvariantFactorPaths.G7.cob, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1]`. Take the linear combination `this`. Rewrite using `[fadd, ← e, Pts.subst_linv_l h hF]`.
-/
theorem law_eq (h : IsLogPair l linv) {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (hc : Formalism.InvariantFactorPaths.G7.cob F l = 0) :
    F = fadd l linv (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
  have e : PowerSeries.subst F l = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l := by
    have := hc
    rw [Formalism.InvariantFactorPaths.G7.cob, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1] at this
    linear_combination this
  rw [fadd, ← e, Pts.subst_linv_l h hF]

end Alg

section Sigma

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Use extensionality with `n`. Use `match n with`. Consider the case `0 => rw [Formalism.L2.Th1.B.Ph.coeff_zero_prim, dblInt, PowerSeries.coeff_mk, if_pos (by norm_num)]`. Consider the case `1`. Rewrite using `[Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_zero_prim, zero_div, dblInt, PowerSeries.coeff_mk, if_pos (by norm_num)]`.

Consider the case `m + 2`. Rewrite using `[Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_prim_succ, dblInt, PowerSeries.coeff_mk, if_neg (by omega), Nat.add_sub_cancel, div_div]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prim_prim (e : PowerSeries K) : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim e) = dblInt e := by
  ext n
  match n with
  | 0 => rw [Formalism.L2.Th1.B.Ph.coeff_zero_prim, dblInt, PowerSeries.coeff_mk, if_pos (by norm_num)]
  | 1 =>
    rw [Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_zero_prim, zero_div, dblInt,
      PowerSeries.coeff_mk, if_pos (by norm_num)]
  | m + 2 =>
    rw [Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_prim_succ, dblInt,
      PowerSeries.coeff_mk, if_neg (by omega), Nat.add_sub_cancel, div_div]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish `h1 : MvPowerSeries.constantCoeff (-(dblInt e) : PowerSeries K) = 0`. Rewrite using `[← prim_prim]`. Conclude with `Formalism.L2.Th1.B.Ph.constantCoeff_sigS e`. Establish `h2 : MvPowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0` using `by show PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0`. Simplify using the standard rewrite rules.

Establish `e1 : -(lam e s2) = -(dblInt e) + -(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)`. Rewrite using `[lam]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sgStar, e1, mvExp_add h1 h2, Formalism.L2.Th1.B.sgStar, Formalism.L2.Th1.B.sigma, Formalism.L2.Th1.B.sigS, prim_prim, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem sgStar_eq (e : PowerSeries K) (s2 : K) : Formalism.L2.Th1.B.sgStar s2 e = sgStar e s2 := by
  have h1 : MvPowerSeries.constantCoeff (-(dblInt e) : PowerSeries K) = 0 := by
    rw [← prim_prim]
    exact Formalism.L2.Th1.B.Ph.constantCoeff_sigS e
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
    show PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0
    simp
  have e1 : -(lam e s2) = -(dblInt e) + -(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) := by
    rw [lam]; ring
  rw [sgStar, e1, mvExp_add h1 h2, Formalism.L2.Th1.B.sgStar, Formalism.L2.Th1.B.sigma, Formalism.L2.Th1.B.sigS,
    prim_prim, mul_assoc]
  rfl

end Sigma

end Dict

/- English proof (translation)
Introduce `_ _ _ _ _ _ _` and use `Iff.rfl`.
-/
theorem simeq_iff_congruence : SimeqIffCong := fun _ _ _ _ _ _ _ => Iff.rfl

/- English proof (translation)
Introduce `K _ _`. Conclude with `isClosed_le continuous_norm continuous_const`.
-/
theorem unit_ball_closed : UnitBallClosed := by
  intro K _ _
  exact isClosed_le continuous_norm continuous_const

/- English proof (translation)
Introduce `K _ _ e l s2 hl hl1`. Take `⟨h0, h1⟩` from `Formalism.L2.Th1.B.Ph.logSigmaPullbackSpec K s2 e l hl hl1`. Use `⟨Dict.sgStar_eq e s2, h0, ?_⟩` and prove the remaining obligations. Rewrite using `[← Dict.sgStar_eq, h1]`. Both sides reduce to the same expression.
-/
theorem odd_phi_is_phi : PhOIsPh := by
  intro K _ _ e l s2 hl hl1
  obtain ⟨h0, h1⟩ := Formalism.L2.Th1.B.Ph.logSigmaPullbackSpec K s2 e l hl hl1
  refine ⟨Dict.sgStar_eq e s2, h0, ?_⟩
  rw [← Dict.sgStar_eq, h1]
  rfl

/- English proof (translation)
Introduce `K _ _ _ F l linv ph h hL hph hS`. Take `⟨hF0, hFi, -, -, hc⟩` from `hL`. Establish `hF` using `Dict.law_eq h hF0 hc`. Establish `hFG : FGInt (Formalism.G.unitBall K) l linv`. Rewrite using `[FGInt, ← hF]`.

Conclude with `hFi`. Use `⟨hF, hFG, ?_⟩` and prove the remaining obligations. Introduce `σ x x' y hx hx' hy`. Establish `hLG : LG (Formalism.G.unitBall K) (Formalism.InvariantFactorPaths.G7.d1 F (Formalism.InvariantFactorPaths.G7.cob F ph))`. Use `(simeq_iff_congruence K (Fin 3) _ _).1 hS` as an intermediate fact.

Rewrite `this` using `[Cong, sub_zero]`. Then use the resulting hypothesis. Establish `hpt : ∀ s : Fin 3, IsPt (Formalism.G.unitBall K) (![x, x', y] s)`. Introduce `s`. Use `fin_cases s`. Conclude with `hx`.

Conclude with `hx'`. Conclude with `hy`. Establish `ha` using `Dict.constantCoeff_vec_three_eq_zero hx.1 hx'.1 hy.1`. Establish `hs` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `key` using `lGSubstMv K (Formalism.G.unitBall K) (Fin 3) _ hLG σ ![x, x', y] hpt`.

Establish `h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0` using `MvPowerSeries.constantCoeff_X 0`. Establish `h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0` using `MvPowerSeries.constantCoeff_X 1`. Establish `h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0` using `MvPowerSeries.constantCoeff_X 2`. Rewrite `key` using `[hF, Dict.coboundary_formal_add_biextension h ph, MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs, Dict.subst_biextension_form h ph (Pts.constantCoeff_fadd h h0 h1) h2 ha, Dict.subst_biextension_form h ph h0 h2 ha, Dict.subst_biextension_form h ph h1 h2 ha, Dict.substMv_fa …`. Rewrite using `[Cong, ← sub_sub]`.

Conclude with `key`.
-/
theorem first_level_from_universal_holds : FirstLevelFromUniversal := by
  intro K _ _ _ F l linv ph h hL hph hS
  obtain ⟨hF0, hFi, -, -, hc⟩ := hL
  have hF := Dict.law_eq h hF0 hc
  have hFG : FGInt (Formalism.G.unitBall K) l linv := by
    rw [FGInt, ← hF]
    exact hFi
  refine ⟨hF, hFG, ?_⟩
  intro σ x x' y hx hx' hy
  have hLG : LG (Formalism.G.unitBall K) (Formalism.InvariantFactorPaths.G7.d1 F (Formalism.InvariantFactorPaths.G7.cob F ph)) := by
    have := (simeq_iff_congruence K (Fin 3) _ _).1 hS
    rwa [Cong, sub_zero] at this
  have hpt : ∀ s : Fin 3, IsPt (Formalism.G.unitBall K) (![x, x', y] s) := by
    intro s
    fin_cases s
    · exact hx
    · exact hx'
    · exact hy
  have ha := Dict.constantCoeff_vec_three_eq_zero hx.1 hx'.1 hy.1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have key := lGSubstMv K (Formalism.G.unitBall K) (Fin 3) _ hLG σ ![x, x', y] hpt
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 2
  rw [hF, Dict.coboundary_formal_add_biextension h ph, MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs,
    Dict.subst_biextension_form h ph (Pts.constantCoeff_fadd h h0 h1) h2 ha, Dict.subst_biextension_form h ph h0 h2 ha,
    Dict.subst_biextension_form h ph h1 h2 ha, Dict.substMv_fadd h h0 h1 ha, MvPowerSeries.subst_X hs,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs] at key
  rw [Cong, ← sub_sub]
  exact key

/- English proof (translation)
Introduce `K _ _ _ F l linv ph a b h hL hph ha hb hA`. Take `⟨hF0, hFi, -, -, hc⟩` from `hL`. Establish `hF` using `Dict.law_eq h hF0 hc`. Establish `h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0` using `MvPowerSeries.constantCoeff_X 0`. Establish `h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0` using `MvPowerSeries.constantCoeff_X 1`.

Establish `p0 : IsPt (Formalism.G.unitBall K) (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)` using `⟨h0, Pts.intMv_X 0⟩`. Establish `p1 : IsPt (Formalism.G.unitBall K) (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)` using `⟨h1, Pts.intMv_X 1⟩`. Establish `key` using `hA (Fin 2) _ _ p0 p1`. Rewrite using `[simeq_iff_congruence K (Fin 2), hF, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1, ← Pts.fmul_eq_subst_mulBy h a h0, ← Pts.fmul_eq_subst_mulBy h b h1, Dict.subst_cob h ph (Pts.constantCoeff_fmul h a h0) h1, Dict.subst_cob h ph h0 (Pts.constantCoeff …`. Conclude with `key`.
-/
theorem adjoint_universal_form : AdjUniversal := by
  intro K _ _ _ F l linv ph a b h hL hph ha hb hA
  obtain ⟨hF0, hFi, -, -, hc⟩ := hL
  have hF := Dict.law_eq h hF0 hc
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have p0 : IsPt (Formalism.G.unitBall K) (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    ⟨h0, Pts.intMv_X 0⟩
  have p1 : IsPt (Formalism.G.unitBall K) (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    ⟨h1, Pts.intMv_X 1⟩
  have key := hA (Fin 2) _ _ p0 p1
  rw [simeq_iff_congruence K (Fin 2), hF, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1,
    ← Pts.fmul_eq_subst_mulBy h a h0, ← Pts.fmul_eq_subst_mulBy h b h1,
    Dict.subst_cob h ph (Pts.constantCoeff_fmul h a h0) h1,
    Dict.subst_cob h ph h0 (Pts.constantCoeff_fmul h b h1)]
  exact key

end Formalism.L2.Th1.C
