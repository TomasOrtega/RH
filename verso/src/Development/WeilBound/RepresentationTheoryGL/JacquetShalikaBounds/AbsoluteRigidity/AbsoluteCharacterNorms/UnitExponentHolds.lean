import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace PositivityTheory.RgJS

namespace UnitExponent

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def nu (E : Type) [Field E] [NumberField E] (s : ℝ) : HChar E :=
  ⟨(GlobalTheory.Mem.Chr.CharModel.absChar E s).1, (GlobalTheory.Mem.Chr.CharModel.absChar E s).2⟩

def zc (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (t : ℝ) :=
  infId E (expU fun _ : InfinitePlace E => (t : ℂ))

/- English proof (translation)
Unfold `zc`. Rewrite using `[← map_mul, ← expU_add]`. Use `congr 2`. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules.
-/
theorem zc_add (s t : ℝ) : zc E (s + t) = zc E s * zc E t := by
  unfold zc
  rw [← map_mul, ← expU_add]
  congr 2
  funext w
  simp

/- English proof (translation)
Unfold `zc`. Use `(continuous_infId E).comp (continuous_expU.comp ?_)` and prove the remaining obligations. Conclude with `continuous_pi fun _ => Complex.continuous_ofReal`.
-/
theorem continuous_zc : Continuous (zc E) := by
  unfold zc
  refine (continuous_infId E).comp (continuous_expU.comp ?_)
  exact continuous_pi fun _ => Complex.continuous_ofReal

/- English proof (translation)
Unfold `zc`. Rewrite using `[Model.logNorm_infId]`. Establish `: ∀ w : InfinitePlace E, 2 * Real.log ‖((expU fun _ : InfinitePlace E => (t : ℂ) : (InfinitePlace E → ℂ)ˣ) : InfinitePlace E → ℂ) w‖ = 2 * t` using `fun w => by`. Establish `e : ((expU fun _ : InfinitePlace E => (t : ℂ) : (InfinitePlace E → ℂ)ˣ) : InfinitePlace E → ℂ) w = Complex.exp (t : ℂ)` using `rfl`. Rewrite using `[e, Complex.norm_exp, Complex.ofReal_re, Real.log_exp]`.

Rewrite using `[Finset.sum_congr rfl fun w _ => this w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNorm_zc (t : ℝ) : GlobalTheory.Mem.Chr.CharModel.logNorm E (zc E t) = (2 * Fintype.card (InfinitePlace E) : ℝ) * t := by
  unfold zc
  rw [Model.logNorm_infId]
  have : ∀ w : InfinitePlace E, 2 * Real.log ‖((expU fun _ : InfinitePlace E => (t : ℂ) : (InfinitePlace E → ℂ)ˣ) :
      InfinitePlace E → ℂ) w‖ = 2 * t := fun w => by
    have e : ((expU fun _ : InfinitePlace E => (t : ℂ) : (InfinitePlace E → ℂ)ˣ) : InfinitePlace E → ℂ) w =
        Complex.exp (t : ℂ) := rfl
    rw [e, Complex.norm_exp, Complex.ofReal_re, Real.log_exp]
  rw [Finset.sum_congr rfl fun w _ => this w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/- English proof (translation)
Set `G : ℝ →+ ℝ` to `{ toFun := fun t => Real.log ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖ map_zero' := by`. Establish `: zc E 0 = 1`. Establish `h` using `zc_add (E := E) 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `left_eq_mul.mp h`.

Rewrite using `[this, map_one, Units.val_one, norm_one, Real.log_one]`. Use the proof step `map_add' := fun s t => by show Real.log _ = Real.log _ + Real.log _`. Rewrite using `[zc_add, map_mul, Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 (Units.ne_zero _))] }`. Establish `hG : Continuous G` using `by show Continuous fun t => Real.log ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖`. Use `Continuous.log ?_ fun t => norm_ne_zero_iff.2 (Units.ne_zero _)` and prove the remaining obligations.

Conclude with `(Units.continuous_val.comp (ω.2.1.comp continuous_zc)).norm`. Use `⟨G 1, fun t => ?_⟩` and prove the remaining obligations. Establish `h1 : G t = t * G 1`. Use `(G.toRealLinearMap hG).map_smul t 1` as an intermediate fact. Simplify `this` using `[smul_eq_mul]`.

Establish `h2 : G t = Real.log ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖` using `rfl`. Rewrite using `[← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 (zc E t)))), ← h2, h1, mul_comm]`.
-/
theorem log_norm_zc (ω : HChar E) : ∃ c : ℝ, ∀ t : ℝ, ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖ = Real.exp (c * t) := by
  let G : ℝ →+ ℝ :=
    { toFun := fun t => Real.log ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖
      map_zero' := by
        have : zc E 0 = 1 := by
          have h := zc_add (E := E) 0 0
          rw [add_zero] at h
          exact left_eq_mul.mp h
        rw [this, map_one, Units.val_one, norm_one, Real.log_one]
      map_add' := fun s t => by
        show Real.log _ = Real.log _ + Real.log _
        rw [zc_add, map_mul, Units.val_mul, norm_mul,
          Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 (Units.ne_zero _))] }
  have hG : Continuous G := by
    show Continuous fun t => Real.log ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖
    refine Continuous.log ?_ fun t => norm_ne_zero_iff.2 (Units.ne_zero _)
    exact (Units.continuous_val.comp (ω.2.1.comp continuous_zc)).norm
  refine ⟨G 1, fun t => ?_⟩
  have h1 : G t = t * G 1 := by
    have := (G.toRealLinearMap hG).map_smul t 1
    simpa [smul_eq_mul] using this
  have h2 : G t = Real.log ‖((ω.1 (zc E t) : ℂˣ) : ℂ)‖ := rfl
  rw [← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 (zc E t)))), ← h2, h1, mul_comm]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖Complex.exp ((r : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E (zc E t))‖ = _`. Rewrite using `[Complex.norm_exp, logNorm_zc]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem norm_absChar_zc (r t : ℝ) :
    ‖(((UnitExponent.nu E r).1 (zc E t) : ℂˣ) : ℂ)‖ =
      Real.exp (r * ((2 * Fintype.card (InfinitePlace E) : ℝ) * t)) := by
  change ‖Complex.exp ((r : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E (zc E t))‖ = _
  rw [Complex.norm_exp, logNorm_zc]
  congr 1
  simp

end UnitExponent

open UnitExponent in
/- English proof (translation)
Introduce `E _ _ _`. Use `⟨fun t => UnitExponent.nu E t, fun t => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) t, ?_⟩` and prove the remaining obligations. Introduce `m π hm`. Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `_ π₁`.

Take `⟨ω, hω⟩` from `Central.exists_hasCentral E m π₁`. Take `⟨c, hc⟩` from `log_norm_zc ω`. Establish `hn : (0 : ℝ) < 2 * Fintype.card (InfinitePlace E)`. Establish `: Nonempty (InfinitePlace E)` using `inferInstance`. Use `Fintype.card_pos (α := InfinitePlace E)` as an intermediate fact.

Check the signs of the components of the expression. Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`. Use `set r : ℝ := -c / ((2 * Fintype.card (InfinitePlace E) : ℝ) * m) with hr`. Use `set χ : HChar E := UnitExponent.nu E r with hχ`. Use `set π₀ : CuspSub E m := π₁.twist χ with hπ₀`.

Establish `hω₀ : π₀.HasCentral (ω * χ ^ m)` using `hω.twist χ`. Establish `hz : ∀ t, ‖(((ω * χ ^ m).1 (zc E t) : ℂˣ) : ℂ)‖ = 1` using `fun t => by`. Establish `e : (((ω * χ ^ m).1 (zc E t) : ℂˣ) : ℂ) = ((ω.1 (zc E t) : ℂˣ) : ℂ) * (((χ.1 (zc E t) : ℂˣ) : ℂ)) ^ m`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_pow, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]`. Rewrite using `[e, norm_mul, norm_pow, hc, hχ, norm_absChar_zc, ← Real.exp_nat_mul, ← Real.exp_add]`.

Rewrite using `[Real.exp_eq_one_iff]`. Rewrite using `[hr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hu : π₀.IsUnitary`.

Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π₀.ne_bot`. Take `⟨C, hC⟩` from `GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E m φ (π₀.cusp φ hφ) fun t g => by`. Rewrite using `[CuspidalL2GL.splitCentre_eq_scalar, hω₀.apply hφ, norm_mul]`. Establish `: (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) = zc E t` using `rfl`. Rewrite using `[this, hz t, one_mul]`.

Take `⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0` from `Function.ne_iff.1 fun e => h0 (Subtype.ext e)`. Establish `hle : ∀ x, ‖(((ω * χ ^ m).1 x : ℂˣ) : ℂ)‖ ≤ 1` using `fun x => by`. Assume the negation of the conclusion as `hcon`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (C / ‖φ.1 g‖) (not_le.1 hcon)`. Use `hC (GeneralLinearGroup.scalar (Fin m) (x ^ n) * g)` as an intermediate fact.

Rewrite `this` using `[hω₀.apply hφ, norm_mul, map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Conclude with `hn.not_ge ((le_div_iff₀ (norm_pos_iff.2 hg)).2 this)`. Use `⟨ω * χ ^ m, fun x => le_antisymm (hle x) ?_, hω₀⟩` and prove the remaining obligations. Use `hle x⁻¹` as an intermediate fact. Rewrite `this` using `[map_inv, Units.val_inv_eq_inv_val, norm_inv]`.

Conclude with `(inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this`. Use `⟨CG.mk π₀, -r, (CG.isUnitary_mk π₀).2 hu, ?_⟩` and prove the remaining obligations. Establish `hinv : χ * UnitExponent.nu E (-r) = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `MonoidHom.ext` to reduce the goal to its premises.

Introduce `x`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Complex.exp ((r : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x) * Complex.exp (((-r : ℝ) : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x) = 1`. Rewrite using `[← Complex.exp_add]`. Use `push_cast`.

Put the polynomial expressions in normal form. Conclude with `Complex.exp_zero`. Use `show CG.mk π₁ = (CG.mk (π₁.twist χ)).twist (UnitExponent.nu E (-r))`. Rewrite using `[show CG.mk (π₁.twist χ) = (CG.mk π₁).twist χ from rfl, ← CG.twist_mul, hinv, CG.twist_one]`.
-/
theorem unit_exponent_holds : UnitEx := by
  intro E _ _ _
  refine ⟨fun t => UnitExponent.nu E t, fun t => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) t, ?_⟩
  intro m π hm
  induction π using Quotient.inductionOn with
  | _ π₁ =>
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E m π₁
  obtain ⟨c, hc⟩ := log_norm_zc ω
  have hn : (0 : ℝ) < 2 * Fintype.card (InfinitePlace E) := by
    have : Nonempty (InfinitePlace E) := inferInstance
    have := Fintype.card_pos (α := InfinitePlace E)
    positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set r : ℝ := -c / ((2 * Fintype.card (InfinitePlace E) : ℝ) * m) with hr
  set χ : HChar E := UnitExponent.nu E r with hχ
  set π₀ : CuspSub E m := π₁.twist χ with hπ₀
  have hω₀ : π₀.HasCentral (ω * χ ^ m) := hω.twist χ

  have hz : ∀ t, ‖(((ω * χ ^ m).1 (zc E t) : ℂˣ) : ℂ)‖ = 1 := fun t => by
    have e : (((ω * χ ^ m).1 (zc E t) : ℂˣ) : ℂ) = ((ω.1 (zc E t) : ℂˣ) : ℂ) * (((χ.1 (zc E t) : ℂˣ) : ℂ)) ^ m := by
      rw [Subgroup.coe_mul, Subgroup.coe_pow, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
        Units.val_pow_eq_pow_val]
    rw [e, norm_mul, norm_pow, hc, hχ, norm_absChar_zc, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    rw [hr]
    field_simp
    ring

  have hu : π₀.IsUnitary := by
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π₀.ne_bot
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E m φ (π₀.cusp φ hφ) fun t g => by
      rw [CuspidalL2GL.splitCentre_eq_scalar, hω₀.apply hφ, norm_mul]
      have : (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) = zc E t := rfl
      rw [this, hz t, one_mul]
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
    have hle : ∀ x, ‖(((ω * χ ^ m).1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
      by_contra hcon
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖φ.1 g‖) (not_le.1 hcon)
      have := hC (GeneralLinearGroup.scalar (Fin m) (x ^ n) * g)
      rw [hω₀.apply hφ, norm_mul, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
      exact hn.not_ge ((le_div_iff₀ (norm_pos_iff.2 hg)).2 this)
    refine ⟨ω * χ ^ m, fun x => le_antisymm (hle x) ?_, hω₀⟩
    have := hle x⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
    exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this
  refine ⟨CG.mk π₀, -r, (CG.isUnitary_mk π₀).2 hu, ?_⟩
  have hinv : χ * UnitExponent.nu E (-r) = 1 := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    change Complex.exp ((r : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x) *
      Complex.exp (((-r : ℝ) : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x) = 1
    rw [← Complex.exp_add]
    push_cast
    ring_nf
    exact Complex.exp_zero
  show CG.mk π₁ = (CG.mk (π₁.twist χ)).twist (UnitExponent.nu E (-r))
  rw [show CG.mk (π₁.twist χ) = (CG.mk π₁).twist χ from rfl, ← CG.twist_mul, hinv, CG.twist_one]

end PositivityTheory.RgJS
