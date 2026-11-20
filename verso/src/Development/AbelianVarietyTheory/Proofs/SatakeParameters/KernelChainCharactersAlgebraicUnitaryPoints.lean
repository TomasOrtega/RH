import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.TieAlgValues

/- English proof (translation)
Rewrite `h`, the goal using `[Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]`. Conclude with `IsIntegral.of_pow hn h`.
-/
theorem mem_Qbar_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact IsIntegral.of_pow hn h

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) k).map φ.toRatAlgHom`.
-/
theorem emb_mem_Qbar {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (k : L) : φ k ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) k).map φ.toRatAlgHom

/- English proof (translation)
Rewrite `h`, the goal using `[Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral]`. Conclude with `h.map (starRingEnd ℂ).toRatAlgHom`.
-/
theorem conj_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : (starRingEnd ℂ) z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [Formalism.MainNotions.TaylorLogMetric.Qbar, mem_algebraicClosure_iff, isAlgebraic_iff_isIntegral] at h ⊢
  exact h.map (starRingEnd ℂ).toRatAlgHom

/- English proof (translation)
Use `mem_Qbar_of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Establish `e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `mul_mem h (conj_mem_Qbar h)`.
-/
theorem norm_mem_Qbar {z : ℂ} (h : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : ((‖z‖ : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  refine mem_Qbar_of_pow (n := 2) (by norm_num) ?_
  have e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e]
  exact mul_mem h (conj_mem_Qbar h)

/- English proof (translation)
Rewrite using `[h k]`. Conclude with `prod_mem fun i _ => zpow_mem (div_mem (emb_mem_Qbar _ _) (norm_mem_Qbar (emb_mem_Qbar _ _))) _`.
-/
theorem inf_mem_Qbar {L : Type} [Field L] [NumberField L] {χ : HChar L} {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (h : χ.HasInf φ n) (k : Lˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  rw [h k]
  exact prod_mem fun i _ => zpow_mem (div_mem (emb_mem_Qbar _ _) (norm_mem_Qbar (emb_mem_Qbar _ _))) _

/- English proof (translation)
Break down `eq_or_ne γ 0 with rfl | h0` into its components or cases. Conclude with `zero_le`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Use `Formalism.UG.P.glint_finite_residueField (F := L) v` as an intermediate fact. Set `_` to `Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))`. Use `set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hN`. Establish `hN2 : 1 < N` using `Fintype.one_lt_card`. Establish `hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hx.le`. Use `set y : v.adicCompletionIntegers L := ⟨x, hxO⟩`. Establish `hyu : IsUnit y` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx`. Establish `hr : IsLocalRing.residue _ y ≠ 0`.

Rewrite using `[ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Conclude with `hyu`. Establish `hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0`. Rewrite using `[map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]`. Rewrite `hp` using `[IsLocalRing.residue_eq_zero_iff]`.

Establish `hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1` using `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp`. Use `⟨N - 1, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Use `hv _ ?_ ?_` and prove the remaining obligations. Use `show Valued.v (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1`.

Rewrite using `[Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]`. Establish `e : (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) - 1 = (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L)` using `by push_cast; rfl`. Rewrite using `[e]`. Conclude with `le_exp_neg_one hlt`.
-/
theorem loc_pow_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ∃ n : ℕ, 0 < n ∧ χ.loc v x ^ n = 1 := by
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hN
  have hN2 : 1 < N := Fintype.one_lt_card
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  refine ⟨N - 1, by omega, ?_⟩
  rw [← map_pow]
  refine hv _ ?_ ?_
  · show Valued.v (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  · have e : (((x ^ (N - 1) : (v.adicCompletion L)ˣ)) : v.adicCompletion L) - 1 =
        (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) := by
      push_cast; rfl
    rw [e]
    exact le_exp_neg_one hlt

/- English proof (translation)
Take `⟨n, hn, h⟩` from `loc_pow_eq_one χ v hv x hx`. Use `mem_Qbar_of_pow hn ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, h, Units.val_one]`. Conclude with `one_mem _`.
-/
theorem loc_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hv : χ.TameAt v)
    (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) : ((χ.loc v x : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  obtain ⟨n, hn, h⟩ := loc_pow_eq_one χ v hv x hx
  refine mem_Qbar_of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact one_mem _

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open PI.HeckeProdW

/- English proof (translation)
Take `⟨h, hh, hx⟩` from `CharEx.classExp L`. Take `⟨k, hk⟩` from `hx b`. Use `set u : Ideles L := b ^ h * diagUnits L k with hu`. Use `set w : Ideles L := (infDiag k)⁻¹ * u with hw`. Establish `hwInf : (w : AdeleRing (𝓞 L) L).1 = 1`.

Use function extensionality and compare the values at `pl`. Use `show pw pl w = 1`. Use `f_inv_mul (pw pl) _ _ ?_` and prove the remaining obligations. Rewrite using `[pw_infDiag, hu, map_mul, map_pow, pw_diag]`. Establish `: pw pl b = 1` using `hb pl`.

Rewrite using `[this, one_pow, one_mul]`. Establish `hwFin : ∀ v, Valued.v ((w : AdeleRing (𝓞 L) L).2 v) = 1`. Introduce `v`. Use `show Valued.v (pv v w) = 1`. Rewrite using `[hw, f_inv_mul' (pv v) _ _ (pv_infDiag v k)]`.

Conclude with `hk v`. Establish `hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (w : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L` using `fun v => by`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `(hwFin v).le`. Establish `hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L)` using `fun v => HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (hwFin v)`.

Set `y : Pu L` to `fun v => (hunit v).unit`. Establish `hwy : w = Phi L y` using `Units.ext (Prod.ext (hwInf.trans rfl) (Subtype.ext (funext fun v => rfl)))`. Take `⟨T, hT⟩` from `exists_strictHenselian_absolutely_closed_local_ring χ`. Use `set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp`. Establish `hpv : ∀ v ∈ T, p v = y v` using `fun v hv => by`.

Rewrite using `[hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]`. Establish `hsplit : y = p * (p⁻¹ * y)` using `by rw [mul_inv_cancel_left]`. Establish `hrest : χ.1 (Phi L (p⁻¹ * y)) = 1` using `hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]`. Establish `hwQ : ((χ.1 w : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Rewrite using `[hwy, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod, Units.coe_prod]`.

Use `prod_mem fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Phi_single]`. Use `loc_mem_Qbar χ v (htame v) _ ?_` and prove the remaining obligations. Use `show Valued.v (((y v : v.adicCompletionIntegers L) : v.adicCompletion L)) = 1`. Conclude with `hwFin v`.

Establish `hue : u = infDiag k * w` using `by rw [hw, mul_inv_cancel_left]`. Establish `hχu : χ.1 u = χ.1 b ^ h` using `by rw [hu, map_mul, χ.2.2 k, mul_one, map_pow]`. Use `mem_Qbar_of_pow hh ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← hχu, hue, map_mul, Units.val_mul]`. Conclude with `mul_mem (hinf k) hwQ`.
-/
theorem fin_mem_Qbar {L : Type} [Field L] [NumberField L] (χ : HChar L) (htame : ∀ v, χ.TameAt v)
    (hinf : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (b : Ideles L) (hb : IsFinIdele b) :
    ((χ.1 b : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  classical
  obtain ⟨h, hh, hx⟩ := CharEx.classExp L
  obtain ⟨k, hk⟩ := hx b
  set u : Ideles L := b ^ h * diagUnits L k with hu
  set w : Ideles L := (infDiag k)⁻¹ * u with hw
  have hwInf : (w : AdeleRing (𝓞 L) L).1 = 1 := by
    funext pl
    show pw pl w = 1
    refine f_inv_mul (pw pl) _ _ ?_
    rw [pw_infDiag, hu, map_mul, map_pow, pw_diag]
    have : pw pl b = 1 := hb pl
    rw [this, one_pow, one_mul]
  have hwFin : ∀ v, Valued.v ((w : AdeleRing (𝓞 L) L).2 v) = 1 := by
    intro v
    show Valued.v (pv v w) = 1
    rw [hw, f_inv_mul' (pv v) _ _ (pv_infDiag v k)]
    exact hk v
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (w : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (hwFin v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (hwFin v)
  let y : Pu L := fun v => (hunit v).unit
  have hwy : w = Phi L y := Units.ext (Prod.ext (hwInf.trans rfl) (Subtype.ext (funext fun v => rfl)))
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  have hwQ : ((χ.1 w : ℂˣ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    rw [hwy, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod, Units.coe_prod]
    refine prod_mem fun v _ => ?_
    rw [Phi_single]
    refine loc_mem_Qbar χ v (htame v) _ ?_
    show Valued.v (((y v : v.adicCompletionIntegers L) : v.adicCompletion L)) = 1
    exact hwFin v
  have hue : u = infDiag k * w := by rw [hw, mul_inv_cancel_left]
  have hχu : χ.1 u = χ.1 b ^ h := by rw [hu, map_mul, χ.2.2 k, mul_one, map_pow]
  refine mem_Qbar_of_pow hh ?_
  rw [← Units.val_pow_eq_pow_val, ← hχu, hue, map_mul, Units.val_mul]
  exact mul_mem (hinf k) hwQ

end GlobalTheory.TieAlgValues

namespace GlobalTheory.TieAlgValues

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

def finIdele {L : Type} [Field L] [NumberField L] (z : (FiniteAdeleRing (𝓞 L) L)ˣ) : Ideles L :=
  MulEquiv.prodUnits.symm (1, z)

/- English proof (translation)
Introduce `D _ _ _ _ _ _ _ _ t u μ _ A dtU _ hP _ i hi y`. Take `⟨x, hx⟩` from `hP.q_read.1 (dtU y)`. Take `⟨ι, hι⟩` from `exists_isAdIso t.X.F t.X.E`. Use `set b : Ideles t.X.E := finIdele (Units.map ι.toRingHom.toMonoidHom x) with hbdef`. Establish `hb : IsFinIdele b` using `fun _ => rfl`.

Establish `hbx : ι (x : AfE t.X.F t.X.E) = (b : AdeleRing (𝓞 t.X.E) t.X.E).2` using `rfl`. Establish `key : ((D.muTil (i + 1) (A.q x) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar`. Rewrite using `[hP.muTil ι hι ⟨i, hi⟩ b x hb hbx]`. Take `⟨n, -, hn⟩` from `(hP.mu0 ⟨i, hi⟩).inf`. Conclude with `fin_mem_Qbar _ (hP.mu0 ⟨i, hi⟩).tame (inf_mem_Qbar hn) b hb`.

Distinguish the cases in `hμ : μ = D.what₂.mu0`. Rewrite using `[(hP.ref hμ).2, ← hx]`. Conclude with `key`. Take `⟨ξ, hξ, hmt⟩` from `hP.tw μ hμ rfl`. Establish `e : (t.O u μ).mt (i + 1) = D.muTil (i + 1) * ξ`.

Rewrite using `[hmt u]`. Conclude with `if_pos (⟨by omega, by omega⟩ : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m)`. Rewrite using `[e, MonoidHom.mul_apply, Units.val_mul, ← hx]`. Use `mul_mem key ?_` and prove the remaining obligations. Rewrite using `[hξ x, Units.coe_map]`.

Conclude with `emb_mem_Qbar _ _`.
-/
theorem mt_mem_Qbar : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m,
    ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  intro D _ _ _ _ _ _ _ _ t u μ _ A dtU _ hP _ i hi y
  obtain ⟨x, hx⟩ := hP.q_read.1 (dtU y)
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Ideles t.X.E := finIdele (Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : IsFinIdele b := fun _ => rfl
  have hbx : ι (x : AfE t.X.F t.X.E) = (b : AdeleRing (𝓞 t.X.E) t.X.E).2 := rfl
  have key : ((D.muTil (i + 1) (A.q x) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
    rw [hP.muTil ι hι ⟨i, hi⟩ b x hb hbx]
    obtain ⟨n, -, hn⟩ := (hP.mu0 ⟨i, hi⟩).inf
    exact fin_mem_Qbar _ (hP.mu0 ⟨i, hi⟩).tame (inf_mem_Qbar hn) b hb
  by_cases hμ : μ = D.what₂.mu0
  · rw [(hP.ref hμ).2, ← hx]
    exact key
  · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ hμ rfl
    have e : (t.O u μ).mt (i + 1) = D.muTil (i + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m)
    rw [e, MonoidHom.mul_apply, Units.val_mul, ← hx]
    refine mul_mem key ?_
    rw [hξ x, Units.coe_map]
    exact emb_mem_Qbar _ _

end GlobalTheory.TieAlgValues
