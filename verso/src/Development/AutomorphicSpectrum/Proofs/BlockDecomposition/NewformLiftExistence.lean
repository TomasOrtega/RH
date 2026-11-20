import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3 Ad3.R
open GroundTheory.Global.RationalSymbol (prime unitAt)
open GroundTheory.Automorphic.GodementSection (adeleAt)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelbergQ

open DirichletHecke
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

/- English proof (translation)
Establish `h1 : normalizedValuation (Qv v) x ≤ normalizedValuation (Qv v) 1`. Rewrite using `[map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `normalizedValuation_le_iff.1 h1`. Rewrite `h2` using `[map_one]`.

Conclude with `(mem_valuationInteger_iff v x).1 h2`.
-/
theorem mem_adicCompletionIntegers_of_ord_nonneg (v : Pl) {x : Qv v} (hx : x ≠ 0) (h : 0 ≤ ord x) :
    x ∈ v.adicCompletionIntegers ℚ := by
  have h1 : normalizedValuation (Qv v) x ≤ normalizedValuation (Qv v) 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact (mem_valuationInteger_iff v x).1 h2

/- English proof (translation)
Use `norm_padicRingEquiv_eq_one ((Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `mem_adicCompletionIntegers_of_ord_nonneg v a.ne_zero h.ge`. Use `mem_adicCompletionIntegers_of_ord_nonneg v (a⁻¹).ne_zero ?_` and prove the remaining obligations. Rewrite using `[ord_units_inv, h]`. Simplify using the standard rewrite rules.
-/
theorem norm_padicRingEquiv_of_ord_eq_zero (v : Pl) (a : (Qv v)ˣ) (h : ord (a : Qv v) = 0) :
    ‖padicRingEquiv v (a : Qv v)‖ = 1 := by
  refine norm_padicRingEquiv_eq_one ((Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩)
  · exact mem_adicCompletionIntegers_of_ord_nonneg v a.ne_zero h.ge
  · refine mem_adicCompletionIntegers_of_ord_nonneg v (a⁻¹).ne_zero ?_
    rw [ord_units_inv, h]
    simp

/- English proof (translation)
Use `mem_positiveSubgroup_of (fun w => norm_padicRingEquiv_of_ord_eq_zero w (lf w e) (h w)) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 < ((RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom (IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite e)) : ℝˣ) : ℝ)`. Rewrite using `[IdeleGroup.toInfinite_ofFinite, map_one, Units.val_one]`. Conclude with `one_pos`.
-/
theorem ofFinite_mem_positiveSubgroup (e : Afˣ) (h : ∀ v, ord (lf v e : Qv v) = 0) :
    IdeleGroup.ofFinite e ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w => norm_padicRingEquiv_of_ord_eq_zero w (lf w e) (h w)) ?_
  change 0 < ((RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom
    (IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite e)) : ℝˣ) : ℝ)
  rw [IdeleGroup.toInfinite_ofFinite, map_one, Units.val_one]
  exact one_pos

/- English proof (translation)
Establish `hO` using `(mem_valuationInteger_iff w _).1 hx`. Establish `hn : ‖padicRingEquiv w (((N : Qv w))⁻¹ * (x - n))‖ ≤ 1` using `(PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hO)`. Set `z : ℤ_[prime w]` to `⟨_, hn⟩`. Establish `hN : ((N : ℕ) : ℚ_[prime w]) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne N)`. Establish `hz : u = (n : ℤ_[prime w]) + (N : ℤ_[prime w]) * z`.

Apply `PadicInt.ext` to reduce the goal to its premises. Establish `hzc : ((z : ℤ_[prime w]) : ℚ_[prime w]) = ((N : ℚ_[prime w]))⁻¹ * (padicRingEquiv w x - n)`. Express the relevant statement in the definitionally equal form `padicRingEquiv w (((N : Qv w))⁻¹ * (x - n)) = _`. Simplify using `only [map_mul, map_inv₀, map_sub, map_natCast, map_intCast]`. Rewrite using `[PadicInt.coe_add, PadicInt.coe_mul, hzc, hu]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ((N : ℕ) : ZMod (prime w ^ N.factorization (prime w))) = 0` using `(ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd N (prime w))`. Rewrite using `[hz, map_add, map_mul, map_natCast, map_intCast, map_intCast, h0, zero_mul, add_zero]`.
-/
theorem toZModPow_eq_of_congr {N : ℕ} [NeZero N] (w : Pl) (x : Qv w) (u : ℤ_[prime w]) (n : ℤ)
    (hu : (u : ℚ_[prime w]) = padicRingEquiv w x)
    (hx : ((N : Qv w))⁻¹ * (x - n) ∈ 𝒪[Qv w]) :
    PadicInt.toZModPow (N.factorization (prime w)) u =
      ZMod.castHom (Nat.ordProj_dvd N (prime w)) _ (n : ZMod N) := by
  have hO := (mem_valuationInteger_iff w _).1 hx
  have hn : ‖padicRingEquiv w (((N : Qv w))⁻¹ * (x - n))‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hO)
  let z : ℤ_[prime w] := ⟨_, hn⟩
  have hN : ((N : ℕ) : ℚ_[prime w]) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hz : u = (n : ℤ_[prime w]) + (N : ℤ_[prime w]) * z := by
    apply PadicInt.ext
    have hzc : ((z : ℤ_[prime w]) : ℚ_[prime w]) = ((N : ℚ_[prime w]))⁻¹ * (padicRingEquiv w x - n) := by
      change padicRingEquiv w (((N : Qv w))⁻¹ * (x - n)) = _
      simp only [map_mul, map_inv₀, map_sub, map_natCast, map_intCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, hzc, hu]
    push_cast
    field_simp
    ring
  have h0 : ((N : ℕ) : ZMod (prime w ^ N.factorization (prime w))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd N (prime w))
  rw [hz, map_add, map_mul, map_natCast, map_intCast, map_intCast, h0, zero_mul, add_zero]

/- English proof (translation)
Establish `hinv : ∀ v, ord (lf v d⁻¹ : Qv v) = 0` using `fun v => by`. Establish `: lf v d⁻¹ = (lf v d)⁻¹` using `map_inv (Units.map (adeleAt v).toMonoidHom) d`. Rewrite using `[this, ord_units_inv, h0 v]`. Simplify using the standard rewrite rules. Set `y : RationalIdeles.positiveSubgroup` to `⟨IdeleGroup.ofFinite d⁻¹, ofFinite_mem_positiveSubgroup d⁻¹ hinv⟩`.

Establish `key : (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ (n : ZMod N)`. Use `coe_heckeCharacter_mk_of_forall χ y fun w hw => ?_` and prove the remaining obligations. Use `toZModPow_eq_of_congr w (lf w d : Qv w) _ n ?_ (h1 w ?_)` and prove the remaining obligations. Establish `hc` using `coe_unitAt y w`. Establish `hy : (IdeleGroup.finiteProj w (y : IdeleGroup ℚ) : Qv w) = ((lf w d : Qv w))⁻¹`.

Establish `: lf w d⁻¹ = (lf w d)⁻¹` using `map_inv (Units.map (adeleAt w).toMonoidHom) d`. Express the relevant statement in the definitionally equal form `((lf w d⁻¹ : (Qv w)ˣ) : Qv w) = _`. Rewrite using `[this, Units.val_inv_eq_inv_val]`. Establish `hm : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) * ((unitAt y w : ℤ_[prime w]) : ℚ_[prime w]) = 1`. Rewrite using `[← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]`.

Rewrite `hm` using `[hc, hy, map_inv₀]`. Establish `hne : padicRingEquiv w (lf w d : Qv w) ≠ 0` using `(map_ne_zero _).2 (lf w d).ne_zero`. Clear denominators, using `at hm` for the nonvanishing conditions. Conclude with `hm`. Rewrite using `[show pOf w = prime w from absNorm_asIdeal w]`.

Conclude with `hw`. Rewrite using `[← key, HeckeCharacter.toIdele_apply, ← Circle.coe_mul, ← map_mul, ← map_mul, ← map_mul]`. Simplify using `[y]`.
-/
theorem heckeCharacter_ofFinite_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : Afˣ) (n : ℤ)
    (h0 : ∀ v, ord (lf v d : Qv v) = 0)
    (h1 : ∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) :
    ((heckeCharacter χ).toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1 := by
  have hinv : ∀ v, ord (lf v d⁻¹ : Qv v) = 0 := fun v => by
    have : lf v d⁻¹ = (lf v d)⁻¹ := map_inv (Units.map (adeleAt v).toMonoidHom) d
    rw [this, ord_units_inv, h0 v]
    simp
  let y : RationalIdeles.positiveSubgroup :=
    ⟨IdeleGroup.ofFinite d⁻¹, ofFinite_mem_positiveSubgroup d⁻¹ hinv⟩
  have key : (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ (n : ZMod N) := by
    refine coe_heckeCharacter_mk_of_forall χ y fun w hw => ?_
    refine toZModPow_eq_of_congr w (lf w d : Qv w) _ n ?_ (h1 w ?_)
    · have hc := coe_unitAt y w
      have hy : (IdeleGroup.finiteProj w (y : IdeleGroup ℚ) : Qv w) = ((lf w d : Qv w))⁻¹ := by
        have : lf w d⁻¹ = (lf w d)⁻¹ := map_inv (Units.map (adeleAt w).toMonoidHom) d
        change ((lf w d⁻¹ : (Qv w)ˣ) : Qv w) = _
        rw [this, Units.val_inv_eq_inv_val]
      have hm : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
          ((unitAt y w : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
        rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
      rw [hc, hy, map_inv₀] at hm
      have hne : padicRingEquiv w (lf w d : Qv w) ≠ 0 := (map_ne_zero _).2 (lf w d).ne_zero
      field_simp at hm
      exact hm
    · rw [show pOf w = prime w from absNorm_asIdeal w]
      exact hw
  rw [← key, HeckeCharacter.toIdele_apply, ← Circle.coe_mul, ← map_mul, ← map_mul, ← map_mul]
  simp [y]

/- English proof (translation)
Introduce `_ _ _ χ` and use `⟨heckeCharacter χ, ⟨isOfFinOrder_heckeCharacter χ, fun d n h0 h1 => heckeCharacter_ofFinite_mul χ d n h0 h1⟩⟩`.
-/
theorem f0 : Ad3.R.B0 → Ad3.R.F0 := fun _ _ _ χ =>
  ⟨heckeCharacter χ, ⟨isOfFinOrder_heckeCharacter χ, fun d n h0 h1 =>
    heckeCharacter_ofFinite_mul χ d n h0 h1⟩⟩

end GlobalTheory.CompanionTheory.RankinSelbergQ
