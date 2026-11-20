import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenySeparable
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobeniusSep

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F]

section Prelim

variable [DecidableEq F] {E : WeierstrassCurve F} [E.IsElliptic]

/- English proof (translation)
Apply `algHom_eq_of_map_genericPoint' E` to reduce the goal to its premises. Rewrite using `[Isogeny.map_comap_genericPoint, ← Point.map_map, Isogeny.map_comap_genericPoint, mulIsogeny_val, mulIsogeny_val, map_zsmul, Isogeny.map_comap_genericPoint, mulIsogeny_val, mul_comm, mul_zsmul]`.
-/
theorem Isogeny.mulIsogeny_comap_mul (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (mulIsogeny E (m * n) (mul_ne_zero hm hn)).comap =
      (mulIsogeny E m hm).comap.comp (mulIsogeny E n hn).comap := by
  apply algHom_eq_of_map_genericPoint' E
  rw [Isogeny.map_comap_genericPoint, ← Point.map_map, Isogeny.map_comap_genericPoint, mulIsogeny_val,
    mulIsogeny_val, map_zsmul, Isogeny.map_comap_genericPoint, mulIsogeny_val, mul_comm, mul_zsmul]

/- English proof (translation)
Establish `: (mulIsogeny E 1 one_ne_zero).comap = AlgHom.id F _`. Apply `algHom_eq_of_map_genericPoint' E` to reduce the goal to its premises. Rewrite using `[Isogeny.map_comap_genericPoint, mulIsogeny_val, one_zsmul]`. Apply the tactic sequence `cases genericPoint E <;> rfl`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem Isogeny.comap_mulIsogeny_one (f : E.toAffine.FunctionField) :
    (mulIsogeny E 1 one_ne_zero).comap f = f := by
  have : (mulIsogeny E 1 one_ne_zero).comap = AlgHom.id F _ := by
    apply algHom_eq_of_map_genericPoint' E
    rw [Isogeny.map_comap_genericPoint, mulIsogeny_val, one_zsmul]
    cases genericPoint E <;> rfl
  rw [this]; rfl

end Prelim

/- English proof (translation)
Consider the cases of `c with`. Consider the case `zero => exact fun h => h`. Consider the case `some x y h => exact fun ht => ht (isAlgebraic_algebraMap x)`.
-/
theorem not_isGenPt_constMap [DecidableEq F] (E : WeierstrassCurve F) {L : Type*} [Field L]
    [Algebra F L] [DecidableEq L] (c : E.toAffine.Point) : ¬ IsGenPt E (constMap E L c) := by
  cases c with
  | zero => exact fun h => h
  | some x y h => exact fun ht => ht (isAlgebraic_algebraMap x)

section Frobenius

variable [IsAlgClosed F] [DecidableEq F] {E : WeierstrassCurve F} [E.IsElliptic]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem mulIsogeny_congr {m n : ℤ} (h : m = n) (hm : m ≠ 0) (hn : n ≠ 0) :
    mulIsogeny E m hm = mulIsogeny E n hn := by
  subst h; rfl

/- English proof (translation)
Use `set φ := mulIsogeny E p (by exact_mod_cast hp.out.ne_zero)`. Use `φ.finiteDimensional` as an intermediate fact. Establish `hker : Nat.card φ.pointHom.ker = Nat.card {P : E.toAffine.Point // (p : ℤ) • P = 0}` using `Nat.card_congr (Equiv.subtypeEquivRight fun P => by`. Rewrite using `[AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny])`. Establish `hdeg : Module.finrank φ.comap.fieldRange E.toAffine.FunctionField = p ^ 2`.

Use `degree_mulIsogeny E (n := (p : ℤ)) (by exact_mod_cast hp.out.ne_zero)` as an intermediate fact. Rewrite `this` using `[Int.natAbs_natCast]`. Conclude with `this`. Establish `hlt : Field.finSepDegree φ.comap.fieldRange E.toAffine.FunctionField < Module.finrank φ.comap.fieldRange E.toAffine.FunctionField`. Establish `h1` using `φ.finSepDegree_le_card_ker`.

Establish `h2` using `card_torsion_lt E p`. Use linear arithmetic over natural numbers and integers. Establish `hle` using `le_powField_of_finSepDegree_lt E p φ.comap.fieldRange hlt`. Take `⟨g, hg⟩` from `(mem_powField_iff E p _).mp (hle ⟨f, rfl⟩)`. Conclude with `⟨g, hg.symm⟩`.
-/
theorem exists_mulIsogeny_comap_eq_pow_char (p : ℕ) [hp : Fact p.Prime] [CharP F p]
    (f : E.toAffine.FunctionField) :
    ∃ g, (mulIsogeny E p (by exact_mod_cast hp.out.ne_zero)).comap f = g ^ p := by
  set φ := mulIsogeny E p (by exact_mod_cast hp.out.ne_zero)
  have := φ.finiteDimensional
  have hker : Nat.card φ.pointHom.ker = Nat.card {P : E.toAffine.Point // (p : ℤ) • P = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P => by
      rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny])
  have hdeg : Module.finrank φ.comap.fieldRange E.toAffine.FunctionField = p ^ 2 := by
    have := degree_mulIsogeny E (n := (p : ℤ)) (by exact_mod_cast hp.out.ne_zero)
    rw [Int.natAbs_natCast] at this
    exact this
  have hlt : Field.finSepDegree φ.comap.fieldRange E.toAffine.FunctionField <
      Module.finrank φ.comap.fieldRange E.toAffine.FunctionField := by
    have h1 := φ.finSepDegree_le_card_ker
    have h2 := card_torsion_lt E p
    omega
  have hle := le_powField_of_finSepDegree_lt E p φ.comap.fieldRange hlt
  obtain ⟨g, hg⟩ := (mem_powField_iff E p _).mp (hle ⟨f, rfl⟩)
  exact ⟨g, hg.symm⟩

/- English proof (translation)
Take `⟨n, rfl⟩` from `hq`. Use `revert hq0`. Proceed by induction on `n generalizing f with`. Consider the case `zero`. Introduce `hq0`.

Use `⟨f, ?_⟩` and prove the remaining obligations. Rewrite using `[mulIsogeny_congr (by simp) hq0 one_ne_zero, Isogeny.comap_mulIsogeny_one, pow_zero, pow_one]`. Consider the case `succ n ih`. Introduce `hq0`. Establish `he0 : ((ringExpChar F : ℕ) : ℤ) ≠ 0`.

Use `(expChar_pos F (ringExpChar F)).ne'` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hn0 : ((ringExpChar F ^ n : ℕ) : ℤ) ≠ 0` using `by push_cast; exact pow_ne_zero _ he0`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, (mulIsogeny E (ringExpChar F) he0).comap f = g ^ ringExpChar F := by`. Break down `expChar_is_prime_or_one F (ringExpChar F) with hpr | h1` into its components or cases.

Establish `: Fact (ringExpChar F).Prime` using `⟨hpr⟩`. Establish `: CharP F (ringExpChar F)`. Establish `hc : ringChar F = ringExpChar F`. Use `hpr.two_le` as an intermediate fact. Simplify using `only [ringExpChar] at this ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← hc]`. Conclude with `ringChar.charP F`. Conclude with `exists_mulIsogeny_comap_eq_pow_char (ringExpChar F) f`. Use `⟨f, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulIsogeny_congr (by rw [h1]; rfl) he0 one_ne_zero, Isogeny.comap_mulIsogeny_one, h1, pow_one]`. Take `⟨h, hh⟩` from `ih g hn0`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `hmul : ((ringExpChar F ^ (n + 1) : ℕ) : ℤ) = ((ringExpChar F ^ n : ℕ) : ℤ) * ((ringExpChar F : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[mulIsogeny_congr hmul hq0 (mul_ne_zero hn0 he0), Isogeny.mulIsogeny_comap_mul _ _ hn0 he0, AlgHom.comp_apply, hg, map_pow, hh, ← pow_mul, pow_succ]`.
-/
theorem exists_mulIsogeny_comap_eq_pow (q : ℕ) (hq : ∃ n, q = ringExpChar F ^ n)
    (hq0 : (q : ℤ) ≠ 0) (f : E.toAffine.FunctionField) :
    ∃ g, (mulIsogeny E q hq0).comap f = g ^ q := by
  obtain ⟨n, rfl⟩ := hq
  revert hq0
  induction n generalizing f with
  | zero =>
    intro hq0
    refine ⟨f, ?_⟩
    rw [mulIsogeny_congr (by simp) hq0 one_ne_zero, Isogeny.comap_mulIsogeny_one, pow_zero,
      pow_one]
  | succ n ih =>
    intro hq0
    have he0 : ((ringExpChar F : ℕ) : ℤ) ≠ 0 := by
      have := (expChar_pos F (ringExpChar F)).ne'
      exact_mod_cast this
    have hn0 : ((ringExpChar F ^ n : ℕ) : ℤ) ≠ 0 := by
      push_cast; exact pow_ne_zero _ he0
    obtain ⟨g, hg⟩ : ∃ g, (mulIsogeny E (ringExpChar F) he0).comap f = g ^ ringExpChar F := by
      rcases expChar_is_prime_or_one F (ringExpChar F) with hpr | h1
      · have : Fact (ringExpChar F).Prime := ⟨hpr⟩
        have : CharP F (ringExpChar F) := by
          have hc : ringChar F = ringExpChar F := by
            have := hpr.two_le
            simp only [ringExpChar] at this ⊢
            omega
          rw [← hc]; exact ringChar.charP F
        exact exists_mulIsogeny_comap_eq_pow_char (ringExpChar F) f
      · refine ⟨f, ?_⟩
        rw [mulIsogeny_congr (by rw [h1]; rfl) he0 one_ne_zero, Isogeny.comap_mulIsogeny_one, h1,
          pow_one]
    obtain ⟨h, hh⟩ := ih g hn0
    refine ⟨h, ?_⟩
    have hmul : ((ringExpChar F ^ (n + 1) : ℕ) : ℤ) =
        ((ringExpChar F ^ n : ℕ) : ℤ) * ((ringExpChar F : ℕ) : ℤ) := by push_cast; ring
    rw [mulIsogeny_congr hmul hq0 (mul_ne_zero hn0 he0), Isogeny.mulIsogeny_comap_mul _ _ hn0 he0,
      AlgHom.comp_apply, hg, map_pow, hh, ← pow_mul, pow_succ]

end Frobenius

section Dual

variable [IsAlgClosed F] [DecidableEq F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] [E''.IsElliptic]

namespace Isogeny

/- English proof (translation)
Introduce `a b h` and use `Subtype.ext (show a.1 = b.1 from congrArg (fun Q : isogHom E E' => Q.1) h)`.
-/
theorem toHom_injective : Function.Injective (toHom : Isogeny E E' → isogHom E E') :=
  fun a b h => Subtype.ext (show a.1 = b.1 from congrArg (fun Q : isogHom E E' => Q.1) h)

/- English proof (translation)
Apply `toHom_injective` to reduce the goal to its premises. Rewrite using `[← homComp_toHom, ← homComp_toHom, ← homComp_toHom, ← homComp_toHom, homComp_assoc]`.
-/
theorem comp_assoc {E''' : WeierstrassCurve F} [E'''.IsElliptic] (χ : Isogeny E'' E''')
    (ψ : Isogeny E' E'') (φ : Isogeny E E') : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  apply toHom_injective
  rw [← homComp_toHom, ← homComp_toHom, ← homComp_toHom, ← homComp_toHom, homComp_assoc]

/- English proof (translation)
Use `congrArg Subtype.val h` as an intermediate fact. Rewrite `this` using `[comp_val, comp_val]`. Conclude with `Subtype.ext (Point.map_injective (W' := E'') φ.comap this)`.
-/
theorem comp_cancel_right {α β : Isogeny E' E''} (φ : Isogeny E E') (h : α.comp φ = β.comp φ) :
    α = β := by
  have := congrArg Subtype.val h
  rw [comp_val, comp_val] at this
  exact Subtype.ext (Point.map_injective (W' := E'') φ.comap this)

/- English proof (translation)
Establish `h1 : (mulIsogeny E n hn).toHom = n • (homId : isogEnd E)` using `Subtype.ext (by rw [toHom_val, mulIsogeny_val]; rfl)`. Use `congrArg Subtype.val (homComp_toHom φ (mulIsogeny E n hn))` as an intermediate fact. Rewrite using `[← toHom_val, ← this, h1]`. Establish `e` using `map_zsmul (AddMonoidHom.mk' (homComp φ.toHom) (homComp_add_right φ.toHom)) n homId`. Simplify using `only [AddMonoidHom.mk'_apply] at e`.

Rewrite using `[e, homComp_id_right]`. Both sides reduce to the same expression.
-/
theorem comp_mulIsogeny_val (φ : Isogeny E E') (n : ℤ) (hn : n ≠ 0) :
    (φ.comp (mulIsogeny E n hn)).1 = n • φ.1 := by
  have h1 : (mulIsogeny E n hn).toHom = n • (homId : isogEnd E) :=
    Subtype.ext (by rw [toHom_val, mulIsogeny_val]; rfl)
  have := congrArg Subtype.val (homComp_toHom φ (mulIsogeny E n hn))
  rw [← toHom_val, ← this, h1]
  have e := map_zsmul (AddMonoidHom.mk' (homComp φ.toHom) (homComp_add_right φ.toHom)) n homId
  simp only [AddMonoidHom.mk'_apply] at e
  rw [e, homComp_id_right]
  rfl

/- English proof (translation)
Rewrite using `[comp_val, mulIsogeny_val, map_zsmul, map_comap_genericPoint]`.
-/
theorem mulIsogeny_comp_val (φ : Isogeny E E') (n : ℤ) (hn : n ≠ 0) :
    ((mulIsogeny E' n hn).comp φ).1 = n • φ.1 := by
  rw [comp_val, mulIsogeny_val, map_zsmul, map_comap_genericPoint]

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [comp_mulIsogeny_val, mulIsogeny_comp_val])`.
-/
theorem comp_mulIsogeny (φ : Isogeny E E') (n : ℤ) (hn : n ≠ 0) :
    φ.comp (mulIsogeny E n hn) = (mulIsogeny E' n hn).comp φ :=
  Subtype.ext (by rw [comp_mulIsogeny_val, mulIsogeny_comp_val])

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `φ.finiteDimensional` as an intermediate fact. Use `set M := φ.comap.fieldRange`. Use `set Ω := AlgebraicClosure L`. Use `set ι := IsScalarTower.toAlgHom F L Ω`. Use `set j : M →ₐ[F] Ω := (ι.comp (genEval E' P hP)).comp φ.comap.equivFieldRange.symm.toAlgHom`.

Use `letI : Algebra M Ω := j.toRingHom.toAlgebra`. Use `haveI : IsScalarTower F M Ω := IsScalarTower.of_algebraMap_eq fun c => (j.commutes c).symm`. Set `τ₀ : E.toAffine.FunctionField →ₐ[M] Ω` to `IsAlgClosed.lift`. Use `⟨τ₀.restrictScalars F, AlgHom.ext fun f => ?_⟩` and prove the remaining obligations. Establish `h1` using `τ₀.commutes ⟨φ.comap f, f, rfl⟩`.

Establish `h2 : φ.comap.equivFieldRange.symm ⟨φ.comap f, f, rfl⟩ = f`. Rewrite using `[AlgEquiv.symm_apply_eq]; exact Subtype.ext (by simp)`. Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]`. Rewrite using `[show φ.comap f = algebraMap M E.toAffine.FunctionField ⟨φ.comap f, f, rfl⟩ from rfl, h1]`. Use `show ι (genEval E' P hP (φ.comap.equivFieldRange.symm ⟨φ.comap f, f, rfl⟩)) = _`.

Rewrite using `[h2]`.
-/
theorem exists_lift (φ : Isogeny E E') {L : Type u} [Field L] [Algebra F L]
    (P : (E'.baseChange L).toAffine.Point) (hP : IsGenPt E' P) :
    ∃ τ : E.toAffine.FunctionField →ₐ[F] AlgebraicClosure L,
      τ.comp φ.comap = (IsScalarTower.toAlgHom F L (AlgebraicClosure L)).comp (genEval E' P hP) := by
  have := φ.finiteDimensional
  set M := φ.comap.fieldRange
  set Ω := AlgebraicClosure L
  set ι := IsScalarTower.toAlgHom F L Ω
  set j : M →ₐ[F] Ω := (ι.comp (genEval E' P hP)).comp φ.comap.equivFieldRange.symm.toAlgHom
  letI : Algebra M Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower F M Ω := IsScalarTower.of_algebraMap_eq fun c => (j.commutes c).symm
  let τ₀ : E.toAffine.FunctionField →ₐ[M] Ω := IsAlgClosed.lift
  refine ⟨τ₀.restrictScalars F, AlgHom.ext fun f => ?_⟩
  have h1 := τ₀.commutes ⟨φ.comap f, f, rfl⟩
  have h2 : φ.comap.equivFieldRange.symm ⟨φ.comap f, f, rfl⟩ = f := by
    rw [AlgEquiv.symm_apply_eq]; exact Subtype.ext (by simp)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  rw [show φ.comap f = algebraMap M E.toAffine.FunctionField ⟨φ.comap f, f, rfl⟩ from rfl, h1]
  show ι (genEval E' P hP (φ.comap.equivFieldRange.symm ⟨φ.comap f, f, rfl⟩)) = _
  rw [h2]

variable (φ : Isogeny E E')

/- English proof (translation)
Use `set q := φ.insepDeg`. Use `set k := Nat.card φ.pointHom.ker`. Establish `hk : (k : ℤ) ≠ 0`. Establish `: 0 < k` using `Nat.card_pos`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hq : (q : ℤ) ≠ 0` using `by exact_mod_cast φ.insepDeg_pos.ne'`. Establish `hdeg : ((φ.degree : ℕ) : ℤ) = (k : ℤ) * (q : ℤ)`. Rewrite using `[degree_eq_insepDeg_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨g, hg⟩` from `exists_mulIsogeny_comap_eq_pow q φ.exists_insepDeg_eq_pow hq f`. Establish `hfix : (mulIsogeny E k hk).comap g ∈ φ.fixedKer`. Apply `mem_fixedKer_of_forall` to reduce the goal to its premises. Introduce `T hT`. Establish `hkT : (k : ℤ) • T = 0`.

Use `card_nsmul_eq_zero' (G := φ.pointHom.ker) (x := ⟨T, hT⟩)` as an intermediate fact. Use `congrArg Subtype.val this` as an intermediate fact. Simplify using `only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at this`. Rewrite using `[natCast_zsmul]`. Conclude with `this`.

Use `DFunLike.congr_fun ((mulIsogeny E k hk).comap_comp_translate T) g` as an intermediate fact. Rewrite `this` using `[pointMap_mulIsogeny, hkT, translate_zero]`. Conclude with `this.symm`. Take `⟨g', hg'⟩` from `φ.exists_comap_eq_pow hfix`. Use `⟨g', ?_⟩` and prove the remaining obligations.

Rewrite using `[mulIsogeny_congr hdeg _ (mul_ne_zero hk hq), mulIsogeny_comap_mul _ _ hk hq, AlgHom.comp_apply, hg, map_pow, hg']`.
-/
theorem exists_comap_eq_mulIsogeny_comap (f : E.toAffine.FunctionField) :
    ∃ g : E'.toAffine.FunctionField, φ.comap g =
      (mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap f := by
  set q := φ.insepDeg
  set k := Nat.card φ.pointHom.ker
  have hk : (k : ℤ) ≠ 0 := by
    have : 0 < k := Nat.card_pos
    exact_mod_cast this.ne'
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast φ.insepDeg_pos.ne'
  have hdeg : ((φ.degree : ℕ) : ℤ) = (k : ℤ) * (q : ℤ) := by
    rw [degree_eq_insepDeg_mul]; push_cast; ring
  obtain ⟨g, hg⟩ := exists_mulIsogeny_comap_eq_pow q φ.exists_insepDeg_eq_pow hq f
  have hfix : (mulIsogeny E k hk).comap g ∈ φ.fixedKer := by
    apply mem_fixedKer_of_forall
    intro T hT
    have hkT : (k : ℤ) • T = 0 := by
      have := card_nsmul_eq_zero' (G := φ.pointHom.ker) (x := ⟨T, hT⟩)
      have := congrArg Subtype.val this
      simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at this
      rw [natCast_zsmul]; exact this
    have := DFunLike.congr_fun ((mulIsogeny E k hk).comap_comp_translate T) g
    rw [pointMap_mulIsogeny, hkT, translate_zero] at this
    exact this.symm
  obtain ⟨g', hg'⟩ := φ.exists_comap_eq_pow hfix
  refine ⟨g', ?_⟩
  rw [mulIsogeny_congr hdeg _ (mul_ne_zero hk hq), mulIsogeny_comap_mul _ _ hk hq, AlgHom.comp_apply,
    hg, map_pow, hg']

noncomputable def dualComap : E.toAffine.FunctionField →ₐ[F] E'.toAffine.FunctionField :=
  φ.comap.equivFieldRange.symm.toAlgHom.comp
    ((mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (fun f => by
        obtain ⟨g, hg⟩ := φ.exists_comap_eq_mulIsogeny_comap f
        exact ⟨g, hg⟩))

/- English proof (translation)
Use `φ.comap.equivFieldRange.apply_symm_apply ((mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap.codRestrict φ.comap.fieldRange.toSubalgebra (fun f => by` as an intermediate fact. Take `⟨g, hg⟩` from `φ.exists_comap_eq_mulIsogeny_comap f`. Conclude with `⟨g, hg⟩) f)`. Conclude with `congrArg Subtype.val this`.
-/
theorem comap_dualComap (f : E.toAffine.FunctionField) :
    φ.comap (φ.dualComap f) =
      (mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap f := by
  have := φ.comap.equivFieldRange.apply_symm_apply
    ((mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (fun f => by
        obtain ⟨g, hg⟩ := φ.exists_comap_eq_mulIsogeny_comap f
        exact ⟨g, hg⟩) f)
  exact congrArg Subtype.val this

noncomputable def dualPt : (E.baseChange E'.toAffine.FunctionField).toAffine.Point :=
  Point.map φ.dualComap (genericPoint E)

/- English proof (translation)
The claim follows from `isGenPt_map_genericPoint E _`.
-/
theorem isGenPt_dualPt : IsGenPt E φ.dualPt := isGenPt_map_genericPoint E _

/- English proof (translation)
The claim follows from `Classical.decEq (AlgebraicClosure L) Point.map (IsScalarTower.toAlgHom F L (AlgebraicClosure L)) (Point.map (genEval E' P hP) φ.dualPt) = (φ.degree : ℤ) • Point.map τ (genericPoint E) := by classical have : φ.comap.comp φ.dualComap = (mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ …`.
-/
theorem map_dualPt_of_lift {L : Type u} [Field L] [Algebra F L] [DecidableEq L]
    (P : (E'.baseChange L).toAffine.Point) (hP : IsGenPt E' P)
    (τ : E.toAffine.FunctionField →ₐ[F] AlgebraicClosure L)
    (hτ : τ.comp φ.comap = (IsScalarTower.toAlgHom F L (AlgebraicClosure L)).comp (genEval E' P hP)) :
    haveI := Classical.decEq (AlgebraicClosure L)
    Point.map (IsScalarTower.toAlgHom F L (AlgebraicClosure L))
        (Point.map (genEval E' P hP) φ.dualPt) =
      (φ.degree : ℤ) • Point.map τ (genericPoint E) := by
  classical
  have : φ.comap.comp φ.dualComap =
      (mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap :=
    AlgHom.ext φ.comap_dualComap
  rw [dualPt, Point.map_map, Point.map_map, ← hτ, AlgHom.comp_assoc, this, ← Point.map_map,
    map_comap_genericPoint, mulIsogeny_val, map_zsmul]

/- English proof (translation)
Rewrite using `[respectsAdd_iff]`. Introduce `L _ _ _ P₁ P₂ h₁ h₂ h₃`. Use `set Ω := AlgebraicClosure L`. Use `set ι := IsScalarTower.toAlgHom F L Ω`. Take `⟨τ₁, hτ₁⟩` from `φ.exists_lift P₁ h₁`.

Take `⟨τ₂, hτ₂⟩` from `φ.exists_lift P₂ h₂`. Use `set R₁ := Point.map τ₁ (genericPoint E)`. Use `set R₂ := Point.map τ₂ (genericPoint E)`. Establish `hR₁ : IsGenPt E R₁` using `isGenPt_map_genericPoint E τ₁`. Establish `hR₂ : IsGenPt E R₂` using `isGenPt_map_genericPoint E τ₂`.

Establish `happ : ∀ (P : (E'.baseChange L).toAffine.Point) (hP : IsGenPt E' P) (τ : E.toAffine.FunctionField →ₐ[F] Ω) (hτ : τ.comp φ.comap = ι.comp (genEval E' P hP)), φ.app (Point.map τ (genericPoint E)) (isGenPt_map_genericPoint E τ) = Point.map ι P`. Introduce `P hP τ hτ`. Rewrite using `[φ.app_eq_map_comp, ← eq_genEval E τ rfl, hτ, ← Point.map_map, map_genEval_genericPoint]`. Establish `hR₃ : IsGenPt E (R₁ + R₂)`. Assume the negation of the conclusion as `hn`.

Take `⟨c, hc⟩` from `exists_map_eq_of_not_isGenPt E _ hn`. Establish `hR₂' : R₂ = -R₁ + constMap E Ω c` using `by rw [hc]; abel`. Establish `e` using `φ.app_congr hR₂' hR₂ (hR₂' ▸ hR₂)`. Establish `eneg : φ.app (-R₁) (isGenPt_neg hR₁) = -φ.app R₁ hR₁` using `map_genEval_neg φ.respectsAdd hR₁`. Rewrite `e` using `[φ.app_add_constMap (isGenPt_neg hR₁) c, eneg]`.

Establish `e₁` using `happ P₁ h₁ τ₁ hτ₁`. Establish `e₂` using `happ P₂ h₂ τ₂ hτ₂`. Rewrite `e` using `[e₂, e₁]`. Establish `: Point.map ι (P₁ + P₂) = constMap E' Ω (φ.pointMap c)`. Rewrite using `[map_add, e]`.

Normalize the expressions using the abelian group laws. Establish `hg` using `isGenPt_map E' ι h₃`. Rewrite `hg` using `[this]`. Conclude with `not_isGenPt_constMap E' (φ.pointMap c) hg`. Establish `hτ₃ : (genEval E (R₁ + R₂) hR₃).comp φ.comap = ι.comp (genEval E' (P₁ + P₂) h₃)`.

Rewrite using `[← genEval_app, ← genEval_map]`. Apply `genEval_congr` to reduce the goal to its premises. Rewrite using `[φ.app_add hR₁ hR₂ hR₃, happ P₁ h₁ τ₁ hτ₁, happ P₂ h₂ τ₂ hτ₂, map_add]`. Apply `Point.map_injective (W' := E) ι` to reduce the goal to its premises. Rewrite using `[map_add, φ.map_dualPt_of_lift _ h₁ τ₁ hτ₁, φ.map_dualPt_of_lift _ h₂ τ₂ hτ₂, φ.map_dualPt_of_lift _ h₃ _ hτ₃, map_genEval_genericPoint, zsmul_add]`.
-/
theorem respectsAdd_dualPt : RespectsAdd E' E φ.dualPt := by
  classical
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  set Ω := AlgebraicClosure L
  set ι := IsScalarTower.toAlgHom F L Ω
  obtain ⟨τ₁, hτ₁⟩ := φ.exists_lift P₁ h₁
  obtain ⟨τ₂, hτ₂⟩ := φ.exists_lift P₂ h₂
  set R₁ := Point.map τ₁ (genericPoint E)
  set R₂ := Point.map τ₂ (genericPoint E)
  have hR₁ : IsGenPt E R₁ := isGenPt_map_genericPoint E τ₁
  have hR₂ : IsGenPt E R₂ := isGenPt_map_genericPoint E τ₂
  have happ : ∀ (P : (E'.baseChange L).toAffine.Point) (hP : IsGenPt E' P)
      (τ : E.toAffine.FunctionField →ₐ[F] Ω) (hτ : τ.comp φ.comap = ι.comp (genEval E' P hP)),
      φ.app (Point.map τ (genericPoint E)) (isGenPt_map_genericPoint E τ) = Point.map ι P := by
    intro P hP τ hτ
    rw [φ.app_eq_map_comp, ← eq_genEval E τ rfl, hτ, ← Point.map_map, map_genEval_genericPoint]
  have hR₃ : IsGenPt E (R₁ + R₂) := by
    by_contra hn
    obtain ⟨c, hc⟩ := exists_map_eq_of_not_isGenPt E _ hn
    have hR₂' : R₂ = -R₁ + constMap E Ω c := by rw [hc]; abel
    have e := φ.app_congr hR₂' hR₂ (hR₂' ▸ hR₂)
    have eneg : φ.app (-R₁) (isGenPt_neg hR₁) = -φ.app R₁ hR₁ := map_genEval_neg φ.respectsAdd hR₁
    rw [φ.app_add_constMap (isGenPt_neg hR₁) c, eneg] at e
    have e₁ := happ P₁ h₁ τ₁ hτ₁
    have e₂ := happ P₂ h₂ τ₂ hτ₂
    rw [e₂, e₁] at e
    have : Point.map ι (P₁ + P₂) = constMap E' Ω (φ.pointMap c) := by
      rw [map_add, e]; abel
    have hg := isGenPt_map E' ι h₃
    rw [this] at hg
    exact not_isGenPt_constMap E' (φ.pointMap c) hg
  have hτ₃ : (genEval E (R₁ + R₂) hR₃).comp φ.comap = ι.comp (genEval E' (P₁ + P₂) h₃) := by
    rw [← genEval_app, ← genEval_map]
    apply genEval_congr
    rw [φ.app_add hR₁ hR₂ hR₃, happ P₁ h₁ τ₁ hτ₁, happ P₂ h₂ τ₂ hτ₂, map_add]
  apply Point.map_injective (W' := E) ι
  rw [map_add, φ.map_dualPt_of_lift _ h₁ τ₁ hτ₁, φ.map_dualPt_of_lift _ h₂ τ₂ hτ₂,
    φ.map_dualPt_of_lift _ h₃ _ hτ₃, map_genEval_genericPoint, zsmul_add]

noncomputable def dual : Isogeny E' E :=
  ⟨φ.dualPt, (isIsogeny_iff _).mpr ⟨φ.isGenPt_dualPt, φ.respectsAdd_dualPt⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dual_val : φ.dual.1 = φ.dualPt := rfl

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[comp_val, dual_val, dualPt, Point.map_map]`. Establish `: φ.comap.comp φ.dualComap = (mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap` using `AlgHom.ext φ.comap_dualComap`. Rewrite using `[this, map_comap_genericPoint]`.
-/
theorem dual_comp : φ.dual.comp φ =
    mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne') := by
  refine Subtype.ext ?_
  rw [comp_val, dual_val, dualPt, Point.map_map]
  have : φ.comap.comp φ.dualComap =
      (mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')).comap :=
    AlgHom.ext φ.comap_dualComap
  rw [this, map_comap_genericPoint]

/- English proof (translation)
Apply `comp_cancel_right φ` to reduce the goal to its premises. Rewrite using `[comp_assoc, dual_comp, comp_mulIsogeny]`.
-/
theorem comp_dual : φ.comp φ.dual =
    mulIsogeny E' φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne') := by
  apply comp_cancel_right φ
  rw [comp_assoc, dual_comp, comp_mulIsogeny]

/- English proof (translation)
Establish `h` using `congrArg Isogeny.degree φ.dual_comp`. Rewrite `h` using `[degree_comp, degree_mulIsogeny, Int.natAbs_natCast, sq]`. Conclude with `Nat.eq_of_mul_eq_mul_right φ.degree_pos h`.
-/
theorem degree_dual : φ.dual.degree = φ.degree := by
  have h := congrArg Isogeny.degree φ.dual_comp
  rw [degree_comp, degree_mulIsogeny, Int.natAbs_natCast, sq] at h
  exact Nat.eq_of_mul_eq_mul_right φ.degree_pos h

/- English proof (translation)
The claim follows from `comp_cancel_right φ (h.trans φ.dual_comp.symm)`.
-/
theorem eq_dual_of_comp {ψ : Isogeny E' E}
    (h : ψ.comp φ = mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne')) : ψ = φ.dual :=
  comp_cancel_right φ (h.trans φ.dual_comp.symm)

/- English proof (translation)
Introduce `Q`. Take `⟨P, hP⟩` from `exists_zsmul_eq E' (Nat.cast_ne_zero.mpr φ.degree_pos.ne' : (φ.degree : ℤ) ≠ 0) Q`. Use `⟨φ.dual.pointMap P, ?_⟩` and prove the remaining obligations. Rewrite using `[← pointMap_comp, comp_dual, pointMap_mulIsogeny, hP]`.
-/
theorem pointMap_surjective : Function.Surjective φ.pointMap := by
  intro Q
  obtain ⟨P, hP⟩ := exists_zsmul_eq E' (Nat.cast_ne_zero.mpr φ.degree_pos.ne' : (φ.degree : ℤ) ≠ 0) Q
  refine ⟨φ.dual.pointMap P, ?_⟩
  rw [← pointMap_comp, comp_dual, pointMap_mulIsogeny, hP]

end Isogeny

end Dual

end GroundTheory.Arith.Abelian
