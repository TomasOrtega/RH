import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.NewformLiftConductor

open Ad3 Ad3.R

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `h1 : x ∈ 𝒪[F] ↔ ValuativeRel.valuation F x ≤ 1` using `Iff.rfl`. Rewrite using `[h1, ← map_one (ValuativeRel.valuation F), ← normalizedValuation_le_iff, map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_integers_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  have h1 : x ∈ 𝒪[F] ↔ ValuativeRel.valuation F x ≤ 1 := Iff.rfl
  rw [h1, ← map_one (ValuativeRel.valuation F), ← normalizedValuation_le_iff, map_one,
    normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Establish `hϖ0 : (ϖ : F) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`. Establish `hval : ValuativeRel.valuation F y = ValuativeRel.valuation F (ϖ : F) ^ j`. Rewrite using `[← map_pow, ← normalizedValuation_eq_iff, normalizedValuation_eq_exp_ord hy, hord, map_pow, normalizedValuation_eq_exp_ord hϖ0, ord_uniformizer hϖ, ← WithZero.exp_nsmul]`. Use `congr 1`.

Simplify using the standard rewrite rules. Establish `hy0 : ValuativeRel.valuation F y ≠ 0` using `by simpa using hy`. Establish `h1 : y⁻¹ * ((u : F) - 1) ∈ 𝒪[F] ↔ ValuativeRel.valuation F (y⁻¹ * ((u : F) - 1)) ≤ 1` using `Iff.rfl`. Rewrite using `[mem_unitFiltrationUnits_iff hj hϖ, h1, map_mul, map_inv₀, ← hval, mul_comm, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 hy0)]`.
-/
theorem mem_unitFiltrationUnits_iff_inv_mul {j : ℕ} (hj : 1 ≤ j) {y : F} (hy : y ≠ 0)
    (hord : ord y = j) (u : Fˣ) : u ∈ unitFiltrationUnits F j ↔ y⁻¹ * ((u : F) - 1) ∈ 𝒪[F] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hval : ValuativeRel.valuation F y = ValuativeRel.valuation F (ϖ : F) ^ j := by
    rw [← map_pow, ← normalizedValuation_eq_iff, normalizedValuation_eq_exp_ord hy, hord, map_pow,
      normalizedValuation_eq_exp_ord hϖ0, ord_uniformizer hϖ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hy0 : ValuativeRel.valuation F y ≠ 0 := by simpa using hy
  have h1 : y⁻¹ * ((u : F) - 1) ∈ 𝒪[F] ↔ ValuativeRel.valuation F (y⁻¹ * ((u : F) - 1)) ≤ 1 := Iff.rfl
  rw [mem_unitFiltrationUnits_iff hj hϖ, h1, map_mul, map_inv₀, ← hval, mul_comm,
    ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 hy0)]

/- English proof (translation)
Simplify using `[ord]`.
-/
theorem ord_neg_one : ord (-1 : F) = 0 := by
  simp [ord]

end Loc

section Glob

open IdeleGroup (finiteUnitsSingle finiteComponent ofFinite prodEquiv diagonal finiteComponent_finiteUnitsSingle finiteComponent_finiteUnitsSingle_of_ne ofFinite_finiteUnitsSingle)

abbrev fs (v : Pl) (a : (Qv v)ˣ) : Afˣ := finiteUnitsSingle v a

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lf_eq (v : Pl) (d : Afˣ) : lf v d = finiteComponent v d := rfl

/- English proof (translation)
The claim follows from `finiteComponent_finiteUnitsSingle v a`.
-/
theorem lf_fs (v : Pl) (a : (Qv v)ˣ) : lf v (fs v a) = a := finiteComponent_finiteUnitsSingle v a

/- English proof (translation)
The claim follows from `finiteComponent_finiteUnitsSingle_of_ne h a`.
-/
theorem lf_fs_ne {v w : Pl} (h : w ≠ v) (a : (Qv v)ˣ) : lf w (fs v a) = 1 :=
  finiteComponent_finiteUnitsSingle_of_ne h a

/- English proof (translation)
Rewrite using `[ofFinite_finiteUnitsSingle]`. Both sides reduce to the same expression.
-/
theorem localChar_coe (ω : HeckeCharacter ℚ) (v : Pl) (a : (Qv v)ˣ) :
    ((localChar ω v a : ℂˣ) : ℂ) = (ω.toIdele (ofFinite (fs v a)) : ℂ) := by
  rw [ofFinite_finiteUnitsSingle]; rfl

/- English proof (translation)
Simplify using `[ord]`.
-/
theorem ord_one' (v : Pl) : ord (1 : Qv v) = 0 := by simp [ord]

/- English proof (translation)
Rewrite using `[localChar_coe]`. Use `h.val (fs v u) n (fun w => ?_) (fun w hw' => ?_)` and prove the remaining obligations. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[lf_fs]`.

Conclude with `hu`. Rewrite using `[lf_fs_ne hwv]`. Conclude with `ord_one' w`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality.

Rewrite using `[lf_fs]`. Conclude with `hv hw'`. Rewrite using `[lf_fs_ne hwv]`. Simplify using `using hw w hwv hw'`.
-/
theorem single_val {N : ℕ} {χ : DirichletCharacter ℂ N} {ω : HeckeCharacter ℚ} (h : Om N χ ω)
    (v : Pl) (u : (Qv v)ˣ) (hu : ord (u : Qv v) = 0) (n : ℤ)
    (hv : pOf v ∣ N → ((N : Qv v))⁻¹ * ((u : Qv v) - n) ∈ 𝒪[Qv v])
    (hw : ∀ w, w ≠ v → pOf w ∣ N → ((N : Qv w))⁻¹ * (1 - n) ∈ 𝒪[Qv w]) :
    ((localChar ω v u : ℂˣ) : ℂ) * χ (n : ZMod N) = 1 := by
  rw [localChar_coe]
  refine h.val (fs v u) n (fun w => ?_) (fun w hw' => ?_)
  · by_cases hwv : w = v
    · subst hwv; rw [lf_fs]; exact hu
    · rw [lf_fs_ne hwv]; exact ord_one' w
  · by_cases hwv : w = v
    · subst hwv; rw [lf_fs]; exact hv hw'
    · rw [lf_fs_ne hwv]; simpa using hw w hwv hw'

/- English proof (translation)
Establish `hq : (p : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hp`. Set `A : Jd` to `diagonal ℚ (Units.mk0 (p : ℚ) hq)`. Establish `hAv : (A : 𝔸[ℚ]) = (p : 𝔸[ℚ])` using `by show algebraMap ℚ 𝔸[ℚ] (p : ℚ) = _`. Simplify using the standard rewrite rules. Set `pf : Afˣ` to `(prodEquiv ℚ A).2`.

Establish `hpf : (pf : Af) = (p : Af)`. Establish `: (pf : Af) = (A : 𝔸[ℚ]).2` using `rfl`. Rewrite using `[this, hAv]`. Both sides reduce to the same expression. Use `⟨pf, hpf, fun ω hω => ?_⟩` and prove the remaining obligations.

Take `⟨m, hm, hωm⟩` from `isOfFinOrder_iff_pow_eq_one.1 hω`. Establish `hpos : (0 : ℝ) < p` using `by positivity`. Set `r : ℝ` to `(p : ℝ) ^ ((m : ℝ)⁻¹)`. Establish `hr0 : r ≠ 0` using `(Real.rpow_pos_of_pos hpos _).ne'`. Establish `hrm : r ^ m = p` using `Real.rpow_inv_natCast_pow hpos.le hm.ne'`.

Set `e` to `fun w : InfinitePlace ℚ => InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)`. Set `T : (InfiniteAdeleRing ℚ)ˣ` to `{ val := fun w => (e w).symm r inv := fun w => (e w).symm r⁻¹ val_inv := by`. Use function extensionality and compare the values at `w`. Use `show (e w).symm r * (e w).symm r⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ hr0, map_one]`.

Use `inv_val := by`. Use function extensionality and compare the values at `w`. Use `show (e w).symm r⁻¹ * (e w).symm r = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hr0, map_one] }`. Establish `hT : T ^ m = (prodEquiv ℚ A).1`.

Apply `Units.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Establish `h1 : (((prodEquiv ℚ A).1 : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (A : 𝔸[ℚ]).1` using `rfl`. Rewrite using `[h1, hAv, Units.val_pow_eq_pow_val]`. Use `show ((e w).symm r) ^ m = (p : w.Completion)`.

Rewrite using `[← map_pow, hrm, map_natCast]`. Establish `hA : A = ((prodEquiv ℚ).symm (T, 1)) ^ m * ofFinite pf`. Apply `(prodEquiv ℚ).injective` to reduce the goal to its premises. Establish `h2 : prodEquiv ℚ (ofFinite pf) = (1, pf)` using `by show prodEquiv ℚ ((ContinuousMulEquiv.symm (prodEquiv ℚ)) (1, pf)) = _`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`.

Rewrite using `[map_mul, map_pow, ContinuousMulEquiv.apply_symm_apply, h2]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[hT]`. Simplify using `[pf]`. Establish `hpow : ∀ (k : ℕ) (x : Jd), (ω ^ k).toIdele x = ω.toIdele x ^ k`.

Introduce `k x`. Proceed by induction on `k with`. Consider the case `zero => simp [HeckeCharacter.toIdele_apply]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, ← ih]`.

Both sides reduce to the same expression. Establish `h3 : ω.toIdele ((prodEquiv ℚ).symm (T, 1)) ^ m = 1`. Rewrite using `[← hpow, hωm]`. Both sides reduce to the same expression. Establish `h4` using `ω.toIdele_diagonal (Units.mk0 (p : ℚ) hq)`.

Express the relevant statement in the definitionally equal form `ω.toIdele A = 1 at h4`. Rewrite `h4` using `[hA, map_mul, map_pow, h3, one_mul]`. Conclude with `h4`.
-/
theorem exists_finite_part (p : ℕ) (hp : p ≠ 0) : ∃ pf : Afˣ, (pf : Af) = (p : Af) ∧
    ∀ ω : HeckeCharacter ℚ, IsOfFinOrder ω → ω.toIdele (ofFinite pf) = 1 := by
  have hq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp
  let A : Jd := diagonal ℚ (Units.mk0 (p : ℚ) hq)
  have hAv : (A : 𝔸[ℚ]) = (p : 𝔸[ℚ]) := by
    show algebraMap ℚ 𝔸[ℚ] (p : ℚ) = _
    simp
  let pf : Afˣ := (prodEquiv ℚ A).2
  have hpf : (pf : Af) = (p : Af) := by
    have : (pf : Af) = (A : 𝔸[ℚ]).2 := rfl
    rw [this, hAv]; rfl
  refine ⟨pf, hpf, fun ω hω => ?_⟩
  obtain ⟨m, hm, hωm⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  have hpos : (0 : ℝ) < p := by positivity
  let r : ℝ := (p : ℝ) ^ ((m : ℝ)⁻¹)
  have hr0 : r ≠ 0 := (Real.rpow_pos_of_pos hpos _).ne'
  have hrm : r ^ m = p := Real.rpow_inv_natCast_pow hpos.le hm.ne'
  let e := fun w : InfinitePlace ℚ => InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  let T : (InfiniteAdeleRing ℚ)ˣ :=
    { val := fun w => (e w).symm r
      inv := fun w => (e w).symm r⁻¹
      val_inv := by
        funext w
        show (e w).symm r * (e w).symm r⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
      inv_val := by
        funext w
        show (e w).symm r⁻¹ * (e w).symm r = 1
        rw [← map_mul, inv_mul_cancel₀ hr0, map_one] }
  have hT : T ^ m = (prodEquiv ℚ A).1 := by
    apply Units.ext
    funext w
    have h1 : (((prodEquiv ℚ A).1 : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (A : 𝔸[ℚ]).1 := rfl
    rw [h1, hAv, Units.val_pow_eq_pow_val]
    show ((e w).symm r) ^ m = (p : w.Completion)
    rw [← map_pow, hrm, map_natCast]
  have hA : A = ((prodEquiv ℚ).symm (T, 1)) ^ m * ofFinite pf := by
    apply (prodEquiv ℚ).injective
    have h2 : prodEquiv ℚ (ofFinite pf) = (1, pf) := by
      show prodEquiv ℚ ((ContinuousMulEquiv.symm (prodEquiv ℚ)) (1, pf)) = _
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [map_mul, map_pow, ContinuousMulEquiv.apply_symm_apply, h2]
    refine Prod.ext ?_ ?_
    · simp [hT]
    · simp [pf]
  have hpow : ∀ (k : ℕ) (x : Jd), (ω ^ k).toIdele x = ω.toIdele x ^ k := by
    intro k x
    induction k with
    | zero => simp [HeckeCharacter.toIdele_apply]
    | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      rfl
  have h3 : ω.toIdele ((prodEquiv ℚ).symm (T, 1)) ^ m = 1 := by
    rw [← hpow, hωm]; rfl
  have h4 := ω.toIdele_diagonal (Units.mk0 (p : ℚ) hq)
  change ω.toIdele A = 1 at h4
  rw [hA, map_mul, map_pow, h3, one_mul] at h4
  exact h4

end Glob

section Main

open IdeleGroup (finiteUnitsSingle finiteComponent ofFinite prodEquiv diagonal)

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {ω : HeckeCharacter ℚ}

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 hn`.
-/
theorem natCast_ne (v : Pl) {n : ℕ} (hn : n ≠ 0) : (n : Qv v) ≠ 0 := Nat.cast_ne_zero.2 hn

/- English proof (translation)
The claim follows from `intCast_mem _ m`.
-/
theorem intCast_mem_O (v : Pl) (m : ℤ) : (m : Qv v) ∈ 𝒪[Qv v] := intCast_mem _ m

/- English proof (translation)
Use `isUnramifiedChar_iff.2 fun u hu => ?_` and prove the remaining obligations. Establish `h1` using `single_val h v u hu 1 (fun h' => absurd h' hv) (fun w _ _ => by simp)`. Simplify using `only [Int.cast_one, map_one, mul_one] at h1`. Conclude with `Units.ext h1`.
-/
theorem unram (h : Om N χ ω) (v : Pl) (hv : ¬ pOf v ∣ N) : IsUnramifiedChar (localChar ω v) := by
  refine isUnramifiedChar_iff.2 fun u hu => ?_
  have h1 := single_val h v u hu 1 (fun h' => absurd h' hv) (fun w _ _ => by simp)
  simp only [Int.cast_one, map_one, mul_one] at h1
  exact Units.ext h1

/- English proof (translation)
Use `set p := pOf v with hp`. Establish `hp0 : p ≠ 0` using `(hpr v).ne_zero`. Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Take `⟨pf, hpf, hpf1⟩` from `exists_finite_part p hp0`. Establish `hcomp : ∀ w : Pl, (((finiteComponent w pf : (Qv w)ˣ)) : Qv w) = (p : Qv w)`.

Introduce `w`. Rewrite using `[IdeleGroup.coe_finiteComponent, hpf]`. Conclude with `map_natCast (adeleAt w) p`. Set `pv : (Qv v)ˣ` to `Units.mk0 (p : Qv v) (natCast_ne v hp0)`. Establish `hpv : ord ((pv : (Qv v)ˣ) : Qv v) = 1` using `by show ord (p : Qv v) = 1`.

Rewrite using `[hord v p hp0, ← hp, (hpr v).factorization_self]`. Both sides reduce to the same expression. Set `D : Afˣ` to `pf⁻¹ * fs v pv`. Establish `hlfD : ∀ w, lf w D = (finiteComponent w pf)⁻¹ * lf w (fs v pv)`. Introduce `w`.

Use `show finiteComponent w D = _`. Simplify using `only [D, map_mul, map_inv]`. Both sides reduce to the same expression. Establish `hDv : lf v D = 1`. Rewrite using `[hlfD, lf_fs]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, hcomp]`. Conclude with `inv_mul_cancel₀ (natCast_ne v hp0)`. Establish `hordw : ∀ w, w ≠ v → ord (p : Qv w) = 0`. Introduce `w hw`.

Rewrite using `[hord w p hp0]`. Establish `: ¬ pOf w ∣ p` using `fun hd => hw (hinj ((Nat.prime_dvd_prime_iff_eq (hpr w) (hpr v)).1 hd))`. Rewrite using `[Nat.factorization_eq_zero_of_not_dvd this]`. Both sides reduce to the same expression. Establish `hDw : ∀ w, w ≠ v → ((lf w D : (Qv w)ˣ) : Qv w) = (p : Qv w)⁻¹`.

Introduce `w hw`. Rewrite using `[hlfD, lf_fs_ne hw, mul_one, Units.val_inv_eq_inv_val, hcomp]`. Establish `hcop : IsCoprime (p : ℤ) (N : ℤ)` using `Nat.isCoprime_iff_coprime.2 (((hpr v).coprime_iff_not_dvd).2 hv)`. Take `⟨a, b, hab⟩` from `hcop`. Establish `hval` using `h.val D a (fun w => ?_) (fun w hw => ?_)`.

Establish `hD1 : ω.toIdele (ofFinite D) = ω.toIdele (ofFinite (fs v pv))`. Simplify using `only [D, map_mul, map_inv, hpf1 ω h.fin, inv_one, one_mul]`. Rewrite `hval` using `[hD1, ← localChar_coe]`. Establish `hpa : χ (a : ZMod N) * χ (p : ZMod N) = 1`. Rewrite using `[← map_mul, ← map_one χ]`.

Use `congr 1`. Use `congrArg (Int.cast : ℤ → ZMod N) hab` as an intermediate fact. Simplify using `using this`. Establish `hpvχ : ((localChar ω v pv : ℂˣ) : ℂ) = χ (p : ZMod N)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hun : localChar ω v (unifUnit (Qv v) * pv⁻¹) = 1`. Use `isUnramifiedChar_iff.1 (unram h v hv) _ ?_` and prove the remaining obligations. Rewrite using `[ord_units_mul, ord_units_inv, ord_unifUnit, hpv]`. Both sides reduce to the same expression. Rewrite `hun` using `[map_mul, map_inv, mul_inv_eq_one]`.

Rewrite using `[hun, hpvχ]`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[hDv]`. Conclude with `ord_one' w`.

Rewrite using `[hDw w hwv]`. Establish `: ord (((Units.mk0 (p : Qv w) (natCast_ne w hp0))⁻¹ : (Qv w)ˣ) : Qv w) = 0`. Rewrite using `[ord_units_inv]`. Simplify using `using hordw w hwv`. Simplify using `using this`.

Establish `hwv : w ≠ v` using `fun e => hv (by rw [hp, ← e]; exact hw)`. Rewrite using `[hDw w hwv]`. Establish `hpw` using `natCast_ne w hp0`. Establish `hNw` using `natCast_ne w hN0`. Establish `hq : (p : Qv w)⁻¹ ∈ 𝒪[Qv w]`.

Establish `h0 : ord (((Units.mk0 (p : Qv w) hpw)⁻¹ : (Qv w)ˣ) : Qv w) = 0`. Rewrite using `[ord_units_inv]`. Simplify using `using hordw w hwv`. Establish `h1` using `(mem_integers_iff_ord (x := (((Units.mk0 (p : Qv w) hpw)⁻¹ : (Qv w)ˣ) : Qv w)) (Units.ne_zero _)).2 h0.ge`. Simplify using `using h1`.

Establish `hab' : (a : Qv w) * (p : Qv w) + (b : Qv w) * (N : Qv w) = 1`. Use `congrArg (Int.cast : ℤ → Qv w) hab` as an intermediate fact. Simplify `this` using `[mul_comm]`. Establish `: (N : Qv w)⁻¹ * ((p : Qv w)⁻¹ - (a : Qv w)) = (p : Qv w)⁻¹ * (b : Qv w)`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(-1 : Qv w) * hab'`. Rewrite using `[this]`. Conclude with `mul_mem hq (intCast_mem_O w b)`.
-/
theorem value (h : Om N χ ω)
    (hord : ∀ (v : Pl) (n : ℕ), n ≠ 0 → ord ((n : ℕ) : Qv v) = n.factorization (pOf v))
    (hpr : ∀ v, (pOf v).Prime) (hinj : Function.Injective pOf) (v : Pl) (hv : ¬ pOf v ∣ N) :
    ((localChar ω v (unifUnit (Qv v)) : ℂˣ) : ℂ) = χ (pOf v) := by
  set p := pOf v with hp
  have hp0 : p ≠ 0 := (hpr v).ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨pf, hpf, hpf1⟩ := exists_finite_part p hp0
  have hcomp : ∀ w : Pl, (((finiteComponent w pf : (Qv w)ˣ)) : Qv w) = (p : Qv w) := by
    intro w
    rw [IdeleGroup.coe_finiteComponent, hpf]
    exact map_natCast (adeleAt w) p
  let pv : (Qv v)ˣ := Units.mk0 (p : Qv v) (natCast_ne v hp0)
  have hpv : ord ((pv : (Qv v)ˣ) : Qv v) = 1 := by
    show ord (p : Qv v) = 1
    rw [hord v p hp0, ← hp, (hpr v).factorization_self]; rfl
  let D : Afˣ := pf⁻¹ * fs v pv
  have hlfD : ∀ w, lf w D = (finiteComponent w pf)⁻¹ * lf w (fs v pv) := by
    intro w
    show finiteComponent w D = _
    simp only [D, map_mul, map_inv]
    rfl
  have hDv : lf v D = 1 := by
    rw [hlfD, lf_fs]
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hcomp]
    exact inv_mul_cancel₀ (natCast_ne v hp0)
  have hordw : ∀ w, w ≠ v → ord (p : Qv w) = 0 := by
    intro w hw
    rw [hord w p hp0]
    have : ¬ pOf w ∣ p := fun hd => hw (hinj ((Nat.prime_dvd_prime_iff_eq (hpr w) (hpr v)).1 hd))
    rw [Nat.factorization_eq_zero_of_not_dvd this]; rfl
  have hDw : ∀ w, w ≠ v → ((lf w D : (Qv w)ˣ) : Qv w) = (p : Qv w)⁻¹ := by
    intro w hw
    rw [hlfD, lf_fs_ne hw, mul_one, Units.val_inv_eq_inv_val, hcomp]
  have hcop : IsCoprime (p : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (((hpr v).coprime_iff_not_dvd).2 hv)
  obtain ⟨a, b, hab⟩ := hcop
  have hval := h.val D a (fun w => ?_) (fun w hw => ?_)
  · have hD1 : ω.toIdele (ofFinite D) = ω.toIdele (ofFinite (fs v pv)) := by
      simp only [D, map_mul, map_inv, hpf1 ω h.fin, inv_one, one_mul]
    rw [hD1, ← localChar_coe] at hval
    have hpa : χ (a : ZMod N) * χ (p : ZMod N) = 1 := by
      rw [← map_mul, ← map_one χ]
      congr 1
      have := congrArg (Int.cast : ℤ → ZMod N) hab
      simpa using this
    have hpvχ : ((localChar ω v pv : ℂˣ) : ℂ) = χ (p : ZMod N) := by
      calc ((localChar ω v pv : ℂˣ) : ℂ)
          = ((localChar ω v pv : ℂˣ) : ℂ) * (χ (a : ZMod N) * χ (p : ZMod N)) := by rw [hpa, mul_one]
        _ = χ (p : ZMod N) := by rw [← mul_assoc, hval, one_mul]
    have hun : localChar ω v (unifUnit (Qv v) * pv⁻¹) = 1 := by
      refine isUnramifiedChar_iff.1 (unram h v hv) _ ?_
      rw [ord_units_mul, ord_units_inv, ord_unifUnit, hpv]; rfl
    rw [map_mul, map_inv, mul_inv_eq_one] at hun
    rw [hun, hpvχ]
  · by_cases hwv : w = v
    · subst hwv; rw [hDv]; exact ord_one' w
    · rw [hDw w hwv]
      have : ord (((Units.mk0 (p : Qv w) (natCast_ne w hp0))⁻¹ : (Qv w)ˣ) : Qv w) = 0 := by
        rw [ord_units_inv]
        simpa using hordw w hwv
      simpa using this
  · have hwv : w ≠ v := fun e => hv (by rw [hp, ← e]; exact hw)
    rw [hDw w hwv]
    have hpw := natCast_ne w hp0
    have hNw := natCast_ne w hN0
    have hq : (p : Qv w)⁻¹ ∈ 𝒪[Qv w] := by
      have h0 : ord (((Units.mk0 (p : Qv w) hpw)⁻¹ : (Qv w)ˣ) : Qv w) = 0 := by
        rw [ord_units_inv]
        simpa using hordw w hwv
      have h1 := (mem_integers_iff_ord (x := (((Units.mk0 (p : Qv w) hpw)⁻¹ : (Qv w)ˣ) : Qv w))
        (Units.ne_zero _)).2 h0.ge
      simpa using h1
    have hab' : (a : Qv w) * (p : Qv w) + (b : Qv w) * (N : Qv w) = 1 := by
      have := congrArg (Int.cast : ℤ → Qv w) hab
      simpa [mul_comm] using this
    have : (N : Qv w)⁻¹ * ((p : Qv w)⁻¹ - (a : Qv w)) = (p : Qv w)⁻¹ * (b : Qv w) := by
      field_simp
      linear_combination (-1 : Qv w) * hab'
    rw [this]
    exact mul_mem hq (intCast_mem_O w b)

/- English proof (translation)
Use `set p := pOf v with hp`. Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Establish `hp0 : p ≠ 0` using `(hpr v).ne_zero`. Use `set e := N.factorization p with he`. Establish `he1 : 1 ≤ e` using `(hpr v).factorization_pos_of_dvd hN0 hv`.

Establish `hmem : unitFiltrationUnits (Qv v) e ≤ (localChar ω v).ker`. Introduce `u hu`. Establish `hu0 : ord ((u : (Qv v)ˣ) : Qv v) = 0` using `mem_unitFiltrationUnits_zero_iff_ord.1 (unitFiltrationUnits_antitone (Nat.zero_le e) hu)`. Establish `hNo : ord (N : Qv v) = (e : ℤ)` using `hord v N hN0`. Establish `h1` using `single_val h v u hu0 1 (fun _ => by`.

Simplify using `using (mem_unitFiltrationUnits_iff_inv_mul he1 (natCast_ne v hN0) hNo u).1 hu)`. Use the proof step `(fun w _ _ => by simp)`. Simplify using `only [Int.cast_one, map_one, mul_one] at h1`. Conclude with `Units.ext h1`. Establish `hnot : ¬ unitFiltrationUnits (Qv v) (e - 1) ≤ (localChar ω v).ker`.

Introduce `hker`. Take `⟨M, hM⟩` from `hv`. Establish `hM0 : M ≠ 0` using `by rintro rfl; simp at hM; exact hN0 hM`. Establish `hMN : M ∣ N` using `⟨p, by rw [hM, mul_comm]⟩`. Establish `hfac : M.factorization p = e - 1`.

Establish `: N.factorization p = M.factorization p + 1`. Establish `hpp : p.factorization p = 1` using `(hpr v).factorization_self`. Rewrite using `[hM, Nat.factorization_mul hp0 hM0]`. Simplify using `[hpp, add_comm]`. Use linear arithmetic over natural numbers and integers.

Establish `hft : χ.FactorsThrough M`. Rewrite using `[DirichletCharacter.factorsThrough_iff_ker_unitsMap hMN]`. Introduce `t ht`. Use `set nn : ℕ := (t : ZMod N).val with hnn`. Establish `hcast : ((nn : ℕ) : ZMod N) = t` using `ZMod.natCast_zmod_val _`.

Establish `hcop : Nat.Coprime nn N` using `ZMod.val_coe_unit_coprime t`. Establish `hpn : ¬ p ∣ nn`. Introduce `hd`. Establish `: p ∣ Nat.gcd nn N` using `Nat.dvd_gcd hd ⟨M, hM⟩`. Rewrite `this` using `[hcop]`.

Conclude with `(hpr v).one_lt.ne' (Nat.dvd_one.1 this)`. Establish `hnn0 : nn ≠ 0` using `by rintro h0; rw [h0] at hpn; exact hpn (dvd_zero p)`. Establish `hMd : (M : ℤ) ∣ (nn : ℤ) - 1` using `by haveI : NeZero M := ⟨hM0⟩`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `h1 : (((t : ZMod N)).cast : ZMod M) = 1`.

Use `congrArg Units.val (MonoidHom.mem_ker.1 ht)` as an intermediate fact. Simplify `this` using `[ZMod.unitsMap_val]`. Establish `h2 : ((nn : ℕ) : ZMod M) = 1`. Rewrite using `[hnn, ZMod.natCast_val]`. Conclude with `h1`.

Use `push_cast`. Rewrite using `[h2, sub_self]`. Take `⟨m, hm⟩` from `hMd`. Establish `hnv : ((nn : ℤ) : Qv v) - 1 = (M : Qv v) * (m : Qv v)`. Use `congrArg (Int.cast : ℤ → Qv v) hm` as an intermediate fact.

Simplify using `using this`. Set `u : (Qv v)ˣ` to `Units.mk0 (nn : Qv v) (natCast_ne v hnn0)`. Establish `hu0 : ord ((u : (Qv v)ˣ) : Qv v) = 0` using `by show ord (nn : Qv v) = 0`. Rewrite using `[hord v nn hnn0, Nat.factorization_eq_zero_of_not_dvd hpn]`. Both sides reduce to the same expression.

Establish `humem : u ∈ unitFiltrationUnits (Qv v) (e - 1)`. Break down `Nat.eq_zero_or_pos (e - 1) with h0 | hpos` into its components or cases. Rewrite using `[h0]`. Conclude with `mem_unitFiltrationUnits_zero_iff_ord.2 hu0`. Use `(mem_unitFiltrationUnits_iff_inv_mul hpos (natCast_ne v hM0) ?_ u).2 ?_` and prove the remaining obligations.

Rewrite using `[hord v M hM0, ← hfac]`. Establish `hMv` using `natCast_ne v hM0`. Establish `: (M : Qv v)⁻¹ * ((u : Qv v) - 1) = (m : Qv v)`. Establish `hu' : ((u : (Qv v)ˣ) : Qv v) = (nn : Qv v)` using `rfl`. Establish `hn' : ((u : (Qv v)ˣ) : Qv v) - 1 = (M : Qv v) * (m : Qv v)`.

Rewrite using `[hu']`. Simplify using `using hnv`. Rewrite using `[hn']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `intCast_mem_O v m`. Establish `h1` using `single_val h v u hu0 (nn : ℤ) (fun _ => by`. Establish `: ((u : (Qv v)ˣ) : Qv v) - ((nn : ℤ) : Qv v) = 0` using `by simp [u]`. Rewrite using `[this, mul_zero]`. Conclude with `zero_mem _)`.

Use the proof step `(fun w hw _ => by`. Establish `hpw : ord (p : Qv w) = 0`. Rewrite using `[hord w p hp0]`. Establish `: ¬ pOf w ∣ p` using `fun hd => hw (hinj ((Nat.prime_dvd_prime_iff_eq (hpr w) (hpr v)).1 hd))`. Rewrite using `[Nat.factorization_eq_zero_of_not_dvd this]`.

Both sides reduce to the same expression. Establish `hpw0` using `natCast_ne w hp0`. Establish `hMw` using `natCast_ne w hM0`. Establish `hq : (p : Qv w)⁻¹ ∈ 𝒪[Qv w]`. Establish `h0 : ord (((Units.mk0 (p : Qv w) hpw0)⁻¹ : (Qv w)ˣ) : Qv w) = 0`.

Rewrite using `[ord_units_inv]`. Simplify using `using hpw`. Establish `h1` using `(mem_integers_iff_ord (x := (((Units.mk0 (p : Qv w) hpw0)⁻¹ : (Qv w)ˣ) : Qv w)) (Units.ne_zero _)).2 h0.ge`. Simplify using `using h1`. Establish `hnw : ((nn : ℤ) : Qv w) - 1 = (M : Qv w) * (m : Qv w)`.

Use `congrArg (Int.cast : ℤ → Qv w) hm` as an intermediate fact. Simplify using `using this`. Establish `: (N : Qv w)⁻¹ * (1 - ((nn : ℤ) : Qv w)) = (p : Qv w)⁻¹ * ((-m : ℤ) : Qv w)`. Establish `hNc : (N : Qv w) = (p : Qv w) * (M : Qv w)` using `by rw [hM]; push_cast; rfl`. Establish `h1n : 1 - ((nn : ℤ) : Qv w) = -((M : Qv w) * (m : Qv w))`.

Rewrite using `[← hnw]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1n, hNc]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `mul_mem hq (intCast_mem_O w _))`. Establish `h2 : ((localChar ω v u : ℂˣ) : ℂ) = 1`. Use `hker humem` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker]`.

Rewrite using `[this]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2, one_mul]`. Rewrite using `[MonoidHom.mem_ker]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[MulChar.coe_toUnitHom]`. Establish `hcast' : (((nn : ℤ)) : ZMod N) = t` using `by simpa using hcast`. Rewrite using `[← hcast', h1]`. Both sides reduce to the same expression. Establish `hle : N ≤ M`.

Establish `: χ.conductor ≤ M` using `Nat.sInf_le hft`. Rewrite `this` using `[hχ]`. Then use the resulting hypothesis. Establish `hlt : M < N`. Rewrite using `[hM]`. Use `(hpr v).one_lt` as an intermediate fact.

Conclude with `lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hM0) this`. Use linear arithmetic over natural numbers and integers. Establish `hne : {n : ℕ | unitFiltrationUnits (Qv v) n ≤ (localChar ω v).ker}.Nonempty` using `⟨e, hmem⟩`. Use `le_antisymm (Nat.sInf_le hmem) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Establish `hc : unitFiltrationUnits (Qv v) (quasiCharConductor (localChar ω v)) ≤ (localChar ω v).ker` using `Nat.sInf_mem hne`. Establish `hle' : quasiCharConductor (localChar ω v) ≤ e - 1` using `by omega`. Conclude with `hnot ((unitFiltrationUnits_antitone hle').trans hc)`.
-/
theorem conductor_eq (h : Om N χ ω) (hχ : χ.IsPrimitive)
    (hord : ∀ (v : Pl) (n : ℕ), n ≠ 0 → ord ((n : ℕ) : Qv v) = n.factorization (pOf v))
    (hpr : ∀ v, (pOf v).Prime) (hinj : Function.Injective pOf) (v : Pl) (hv : pOf v ∣ N) :
    quasiCharConductor (localChar ω v) = N.factorization (pOf v) := by
  set p := pOf v with hp
  have hN0 : N ≠ 0 := NeZero.ne N
  have hp0 : p ≠ 0 := (hpr v).ne_zero
  set e := N.factorization p with he
  have he1 : 1 ≤ e := (hpr v).factorization_pos_of_dvd hN0 hv
  have hmem : unitFiltrationUnits (Qv v) e ≤ (localChar ω v).ker := by
    intro u hu
    have hu0 : ord ((u : (Qv v)ˣ) : Qv v) = 0 :=
      mem_unitFiltrationUnits_zero_iff_ord.1 (unitFiltrationUnits_antitone (Nat.zero_le e) hu)
    have hNo : ord (N : Qv v) = (e : ℤ) := hord v N hN0
    have h1 := single_val h v u hu0 1
      (fun _ => by
        simpa using (mem_unitFiltrationUnits_iff_inv_mul he1 (natCast_ne v hN0) hNo u).1 hu)
      (fun w _ _ => by simp)
    simp only [Int.cast_one, map_one, mul_one] at h1
    exact Units.ext h1
  have hnot : ¬ unitFiltrationUnits (Qv v) (e - 1) ≤ (localChar ω v).ker := by
    intro hker
    obtain ⟨M, hM⟩ := hv
    have hM0 : M ≠ 0 := by rintro rfl; simp at hM; exact hN0 hM
    have hMN : M ∣ N := ⟨p, by rw [hM, mul_comm]⟩
    have hfac : M.factorization p = e - 1 := by
      have : N.factorization p = M.factorization p + 1 := by
        have hpp : p.factorization p = 1 := (hpr v).factorization_self
        rw [hM, Nat.factorization_mul hp0 hM0]
        simp [hpp, add_comm]
      omega
    have hft : χ.FactorsThrough M := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hMN]
      intro t ht
      set nn : ℕ := (t : ZMod N).val with hnn
      have hcast : ((nn : ℕ) : ZMod N) = t := ZMod.natCast_zmod_val _
      have hcop : Nat.Coprime nn N := ZMod.val_coe_unit_coprime t
      have hpn : ¬ p ∣ nn := by
        intro hd
        have : p ∣ Nat.gcd nn N := Nat.dvd_gcd hd ⟨M, hM⟩
        rw [hcop] at this
        exact (hpr v).one_lt.ne' (Nat.dvd_one.1 this)
      have hnn0 : nn ≠ 0 := by rintro h0; rw [h0] at hpn; exact hpn (dvd_zero p)
      have hMd : (M : ℤ) ∣ (nn : ℤ) - 1 := by
        haveI : NeZero M := ⟨hM0⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have h1 : (((t : ZMod N)).cast : ZMod M) = 1 := by
          have := congrArg Units.val (MonoidHom.mem_ker.1 ht)
          simpa [ZMod.unitsMap_val] using this
        have h2 : ((nn : ℕ) : ZMod M) = 1 := by
          rw [hnn, ZMod.natCast_val]; exact h1
        push_cast
        rw [h2, sub_self]
      obtain ⟨m, hm⟩ := hMd
      have hnv : ((nn : ℤ) : Qv v) - 1 = (M : Qv v) * (m : Qv v) := by
        have := congrArg (Int.cast : ℤ → Qv v) hm
        simpa using this
      let u : (Qv v)ˣ := Units.mk0 (nn : Qv v) (natCast_ne v hnn0)
      have hu0 : ord ((u : (Qv v)ˣ) : Qv v) = 0 := by
        show ord (nn : Qv v) = 0
        rw [hord v nn hnn0, Nat.factorization_eq_zero_of_not_dvd hpn]; rfl
      have humem : u ∈ unitFiltrationUnits (Qv v) (e - 1) := by
        rcases Nat.eq_zero_or_pos (e - 1) with h0 | hpos
        · rw [h0]; exact mem_unitFiltrationUnits_zero_iff_ord.2 hu0
        · refine (mem_unitFiltrationUnits_iff_inv_mul hpos (natCast_ne v hM0) ?_ u).2 ?_
          · rw [hord v M hM0, ← hfac]
          · have hMv := natCast_ne v hM0
            have : (M : Qv v)⁻¹ * ((u : Qv v) - 1) = (m : Qv v) := by
              have hu' : ((u : (Qv v)ˣ) : Qv v) = (nn : Qv v) := rfl
              have hn' : ((u : (Qv v)ˣ) : Qv v) - 1 = (M : Qv v) * (m : Qv v) := by
                rw [hu']; simpa using hnv
              rw [hn']; field_simp
            rw [this]; exact intCast_mem_O v m
      have h1 := single_val h v u hu0 (nn : ℤ)
        (fun _ => by
          have : ((u : (Qv v)ˣ) : Qv v) - ((nn : ℤ) : Qv v) = 0 := by simp [u]
          rw [this, mul_zero]; exact zero_mem _)
        (fun w hw _ => by
          have hpw : ord (p : Qv w) = 0 := by
            rw [hord w p hp0]
            have : ¬ pOf w ∣ p := fun hd => hw (hinj ((Nat.prime_dvd_prime_iff_eq (hpr w) (hpr v)).1 hd))
            rw [Nat.factorization_eq_zero_of_not_dvd this]; rfl
          have hpw0 := natCast_ne w hp0
          have hMw := natCast_ne w hM0
          have hq : (p : Qv w)⁻¹ ∈ 𝒪[Qv w] := by
            have h0 : ord (((Units.mk0 (p : Qv w) hpw0)⁻¹ : (Qv w)ˣ) : Qv w) = 0 := by
              rw [ord_units_inv]
              simpa using hpw
            have h1 := (mem_integers_iff_ord (x := (((Units.mk0 (p : Qv w) hpw0)⁻¹ : (Qv w)ˣ) : Qv w))
              (Units.ne_zero _)).2 h0.ge
            simpa using h1
          have hnw : ((nn : ℤ) : Qv w) - 1 = (M : Qv w) * (m : Qv w) := by
            have := congrArg (Int.cast : ℤ → Qv w) hm
            simpa using this
          have : (N : Qv w)⁻¹ * (1 - ((nn : ℤ) : Qv w)) = (p : Qv w)⁻¹ * ((-m : ℤ) : Qv w) := by
            have hNc : (N : Qv w) = (p : Qv w) * (M : Qv w) := by rw [hM]; push_cast; rfl
            have h1n : 1 - ((nn : ℤ) : Qv w) = -((M : Qv w) * (m : Qv w)) := by
              rw [← hnw]; ring
            rw [h1n, hNc]; push_cast; field_simp
          rw [this]
          exact mul_mem hq (intCast_mem_O w _))
      have h2 : ((localChar ω v u : ℂˣ) : ℂ) = 1 := by
        have := hker humem
        rw [MonoidHom.mem_ker] at this
        rw [this]; rfl
      rw [h2, one_mul] at h1
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [MulChar.coe_toUnitHom]
      have hcast' : (((nn : ℤ)) : ZMod N) = t := by simpa using hcast
      rw [← hcast', h1]; rfl
    have hle : N ≤ M := by
      have : χ.conductor ≤ M := Nat.sInf_le hft
      rwa [hχ] at this
    have hlt : M < N := by
      rw [hM]
      have := (hpr v).one_lt
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hM0) this
    omega
  have hne : {n : ℕ | unitFiltrationUnits (Qv v) n ≤ (localChar ω v).ker}.Nonempty := ⟨e, hmem⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  have hc : unitFiltrationUnits (Qv v) (quasiCharConductor (localChar ω v)) ≤ (localChar ω v).ker :=
    Nat.sInf_mem hne
  have hle' : quasiCharConductor (localChar ω v) ≤ e - 1 := by omega
  exact hnot ((unitFiltrationUnits_antitone hle').trans hc)

/- English proof (translation)
Set `d : Afˣ` to `∏ v ∈ S, fs v (-1)`. Establish `hd : ∀ w, finiteComponent w d = if w ∈ S then -1 else 1`. Introduce `w`. Simplify using `only [d, map_prod]`. Use `split_ifs with hw`.

Rewrite using `[Finset.prod_eq_single_of_mem w hw]`. Conclude with `lf_fs w (-1)`. Introduce `b _ hb`. Conclude with `lf_fs_ne (Ne.symm hb) (-1)`. Use `Finset.prod_eq_one fun b hb => ?_` and prove the remaining obligations.

Conclude with `lf_fs_ne (fun e : w = b => hw (by rw [e]; exact hb)) (-1)`. Establish `hval` using `h.val d (-1) (fun w => ?_) (fun w hw => ?_)`. Set `Φ : Afˣ →* ℂ` to `(Circle.coeHom : Circle →* ℂ).comp (ω.toIdele.comp ofFinite)`. Establish `hprod : ∏ v ∈ S, ((localChar ω v (-1) : ℂˣ) : ℂ) = Φ d`. Simplify using `only [d, map_prod]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Conclude with `localChar_coe ω v (-1)`. Establish `hΦ : Φ d = (ω.toIdele (ofFinite d) : ℂ)` using `rfl`. Rewrite using `[hprod, hΦ]`. Establish `h2 : χ (((-1 : ℤ)) : ZMod N) = (-1) ^ k` using `by simpa using hk`.

Rewrite `hval` using `[h2]`. Establish `h3 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lf_eq, hd] split_ifs`. Simplify using `using ord_neg_one`.

Conclude with `ord_one' w`. Rewrite using `[lf_eq, hd, if_pos (hS w hw)]`. Simplify using the standard rewrite rules.
-/
theorem sign_eq (h : Om N χ ω) (k : ℕ) (hk : χ (-1) = (-1) ^ k) (S : Finset Pl)
    (hS : ∀ v, pOf v ∣ N → v ∈ S) : ∏ v ∈ S, ((localChar ω v (-1) : ℂˣ) : ℂ) = (-1) ^ k := by
  let d : Afˣ := ∏ v ∈ S, fs v (-1)
  have hd : ∀ w, finiteComponent w d = if w ∈ S then -1 else 1 := by
    intro w
    simp only [d, map_prod]
    split_ifs with hw
    · rw [Finset.prod_eq_single_of_mem w hw]
      · exact lf_fs w (-1)
      · intro b _ hb
        exact lf_fs_ne (Ne.symm hb) (-1)
    · refine Finset.prod_eq_one fun b hb => ?_
      exact lf_fs_ne (fun e : w = b => hw (by rw [e]; exact hb)) (-1)
  have hval := h.val d (-1) (fun w => ?_) (fun w hw => ?_)
  · let Φ : Afˣ →* ℂ := (Circle.coeHom : Circle →* ℂ).comp (ω.toIdele.comp ofFinite)
    have hprod : ∏ v ∈ S, ((localChar ω v (-1) : ℂˣ) : ℂ) = Φ d := by
      simp only [d, map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      exact localChar_coe ω v (-1)
    have hΦ : Φ d = (ω.toIdele (ofFinite d) : ℂ) := rfl
    rw [hprod, hΦ]
    have h2 : χ (((-1 : ℤ)) : ZMod N) = (-1) ^ k := by simpa using hk
    rw [h2] at hval
    have h3 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    calc (ω.toIdele (ofFinite d) : ℂ)
        = (ω.toIdele (ofFinite d) : ℂ) * (((-1 : ℂ) ^ k) * (-1) ^ k) := by rw [h3, mul_one]
      _ = (-1) ^ k := by rw [← mul_assoc, hval, one_mul]
  · rw [lf_eq, hd]
    split_ifs
    · simpa using ord_neg_one
    · exact ord_one' w
  · rw [lf_eq, hd, if_pos (hS w hw)]
    simp

/- English proof (translation)
Introduce `hB k N _ χ hχ hk ω hω`. Take `⟨hloc, hinj, -⟩` from `hB`. Establish `hord : ∀ (v : Pl) (n : ℕ), n ≠ 0 → ord ((n : ℕ) : Qv v) = n.factorization (pOf v)` using `fun v => (hloc v).2.2.2.2.1`. Establish `hpr : ∀ v, (pOf v).Prime` using `fun v => (hloc v).2.2.1`. Conclude with `⟨fun v hv => ⟨unram hω v hv, value hω hord hpr hinj v hv⟩, fun v hv => conductor_eq hω hχ hord hpr hinj v hv, fun S hS => sign_eq hω k hk S hS⟩`.
-/
theorem f0b : Ad3.R.B0 → Ad3.R.F0b := by
  intro hB k N _ χ hχ hk ω hω
  obtain ⟨hloc, hinj, -⟩ := hB
  have hord : ∀ (v : Pl) (n : ℕ), n ≠ 0 → ord ((n : ℕ) : Qv v) = n.factorization (pOf v) :=
    fun v => (hloc v).2.2.2.2.1
  have hpr : ∀ v, (pOf v).Prime := fun v => (hloc v).2.2.1
  exact ⟨fun v hv => ⟨unram hω v hv, value hω hord hpr hinj v hv⟩,
    fun v hv => conductor_eq hω hχ hord hpr hinj v hv,
    fun S hS => sign_eq hω k hk S hS⟩

end Main

end GlobalTheory.CompanionTheory.NewformLiftConductor

end
