import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.BaseAcris

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

def invS (h : IsBase l A) : A.A →+* Ob l := (RingEquiv.ofBijective A.s h).symm.toRingHom

/- English proof (translation)
The claim follows from `RingHom.ext fun x => (RingEquiv.ofBijective A.s h).symm_apply_apply x`.
-/
theorem invS_comp (h : IsBase l A) : (invS A h).comp A.s = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).symm_apply_apply x

/- English proof (translation)
The claim follows from `RingHom.ext fun x => (RingEquiv.ofBijective A.s h).apply_symm_apply x`.
-/
theorem comp_invS (h : IsBase l A) : A.s.comp (invS A h) = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).apply_symm_apply x

/- English proof (translation)
Rewrite using `[xi, sW, ← wmap_comp, invS_comp, wmap_id]`.
-/
theorem map_xi_invS (h : IsBase l A) : WittVector.map (invS A h) A.xi = xi0 l := by
  rw [xi, sW, ← wmap_comp, invS_comp, wmap_id]

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← awayW_comp, invS_comp, awayW_id]`. Both sides reduce to the same expression.
-/
theorem awayW_left (h : IsBase l A) (y : WL l (Ob l)) : awayW (invS A h) (awayW A.s y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, invS_comp, awayW_id]; rfl

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← awayW_comp, comp_invS, awayW_id]`. Both sides reduce to the same expression.
-/
theorem awayW_right (h : IsBase l A) (y : WL l A.A) : awayW A.s (awayW (invS A h) y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, comp_invS, awayW_id]; rfl

/- English proof (translation)
Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`. Establish `e` using `awayW_dpw (invS A h) k (A.isUnit_natCast k.factorial_ne_zero) A.xi`. Rewrite `e` using `[map_xi_invS]`.

Conclude with `Set.mem_of_eq_of_mem e (ACris.dpow_mem xi0_mem k)`. Consider the case `algebraMap x => rw [awayW_algebraMap]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`.
-/
theorem awayW_inv_mem (h : IsBase l A) {y : WL l A.A} (hy : y ∈ A.Acr0) :
    awayW (invS A h) y ∈ ACris.ACrisZero ℂ_[l] l := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have e := awayW_dpw (invS A h) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [map_xi_invS] at e
    exact Set.mem_of_eq_of_mem e (ACris.dpow_mem xi0_mem k)
  | algebraMap x => rw [awayW_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `e : awayW A.s x.1 = awayW A.s y.1` using `congrArg Subtype.val hxy`. Establish `e'` using `congrArg (awayW (invS A h)) e`. Rewrite `e'` using `[awayW_left, awayW_left]`.

Conclude with `Subtype.ext e'`. Introduce `y`. Conclude with `⟨⟨awayW (invS A h) y.1, awayW_inv_mem A h y.2⟩, Subtype.ext (awayW_right A h y.1)⟩`.
-/
theorem acrisZero_bijective_of_isBase (h : IsBase l A) : Function.Bijective A.cris0 := by
  constructor
  · intro x y hxy
    have e : awayW A.s x.1 = awayW A.s y.1 := congrArg Subtype.val hxy
    have e' := congrArg (awayW (invS A h)) e
    rw [awayW_left, awayW_left] at e'
    exact Subtype.ext e'
  · intro y
    exact ⟨⟨awayW (invS A h) y.1, awayW_inv_mem A h y.2⟩, Subtype.ext (awayW_right A h y.1)⟩

/- English proof (translation)
The claim follows from `Function.bijective_iff_has_inverse.2 ⟨WittVector.map (invS A h), fun x => by change WittVector.map (invS A h) (WittVector.map A.s x) = x rw [← wmap_comp, invS_comp, wmap_id], fun x => by change WittVector.map A.s (WittVector.map (invS A h) x) = x rw [← wmap_comp, comp_invS, wmap_ …`.
-/
theorem sW_bijective (h : IsBase l A) : Function.Bijective A.sW :=
  Function.bijective_iff_has_inverse.2 ⟨WittVector.map (invS A h),
    fun x => by
      change WittVector.map (invS A h) (WittVector.map A.s x) = x
      rw [← wmap_comp, invS_comp, wmap_id],
    fun x => by
      change WittVector.map A.s (WittVector.map (invS A h) x) = x
      rw [← wmap_comp, comp_invS, wmap_id]⟩

/- English proof (translation)
Establish `hs` using `sW_bijective A h`. Establish `hth` using `IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`.

Take `⟨x, rfl⟩` from `hth y`. Rewrite `hy` using `[oC_theta0]`. Establish `hm : A.sW x ∈ Ideal.span {A.xi}` using `Ideal.Quotient.eq_zero_iff_mem.1 hy`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hm`. Take `⟨c', rfl⟩` from `hs.2 c`.

Establish `e : x = c' * xi0 l` using `hs.1 (by rw [map_mul, ← hc]; rfl)`. Establish `: x ∈ RingHom.ker (theta0 l)`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ xi0_mem`. Conclude with `this`.

Introduce `u`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨x, rfl⟩` from `hs.2 w`. Conclude with `⟨theta0 l x, A.oC_theta0 x⟩`.
-/
theorem oC_bijective (h : IsBase l A) : Function.Bijective A.oC := by
  have hs := sW_bijective A h
  have hth := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hth y
    rw [oC_theta0] at hy
    have hm : A.sW x ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := hs.2 c
    have e : x = c' * xi0 l := hs.1 (by rw [map_mul, ← hc]; rfl)
    have : x ∈ RingHom.ker (theta0 l) := by
      rw [e]; exact Ideal.mul_mem_left _ _ xi0_mem
    exact this
  · intro u
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨x, rfl⟩ := hs.2 w
    exact ⟨theta0 l x, A.oC_theta0 x⟩

/- English proof (translation)
Rewrite using `[← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval _ a (by simp), h, map_zero]`.
-/
theorem mem_map_of_evalₐ_eq_zero (B : Type) [CommRing B] (π : B) (n : ℕ)
    (a : AdicCompletion (Ideal.span {π}) B) (h : AdicCompletion.evalₐ (Ideal.span {π}) n a = 0) :
    a ∈ (Ideal.span {π} ^ n).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
  rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    ← AdicCompletion.factor_evalₐ_eq_eval _ a (by simp), h, map_zero]

/- English proof (translation)
Introduce `u`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨y, rfl⟩` from `(acrisZero_bijective_of_isBase A h).2 w`. Conclude with `⟨AdicCompletion.of _ _ y, A.cris_of n y⟩`.
-/
theorem cris_surjective (h : IsBase l A) (n : ℕ) : Function.Surjective (A.cris n) := by
  intro u
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨y, rfl⟩ := (acrisZero_bijective_of_isBase A h).2 w
  exact ⟨AdicCompletion.of _ _ y, A.cris_of n y⟩

/- English proof (translation)
Rewrite using `[map_pow, map_natCast, pow_l_acr]`.
-/
theorem cris_natCast_pow (n : ℕ) : A.cris n ((l : Acris l) ^ n) = 0 := by
  rw [map_pow, map_natCast, pow_l_acr]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : Acris0 l)}) n a)`. Establish `e : A.cris n a = A.mkAcr n (A.cris0 y)`. Simplify using `only [cris, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hy, Ideal.Quotient.lift_mk]`.

Rewrite `ha` using `[RingHom.mem_ker, e]`. Establish `hm : A.cris0 y ∈ Ideal.span {(l : A.Acr0) ^ n}` using `Ideal.Quotient.eq_zero_iff_mem.1 ha`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hm`. Take `⟨c', rfl⟩` from `(acrisZero_bijective_of_isBase A h).2 c`. Establish `e2 : y = c' * (l : Acris0 l) ^ n` using `(acrisZero_bijective_of_isBase A h).1 (by`.

Rewrite using `[map_mul, map_pow, map_natCast, hc])`. Establish `hz : Ideal.Quotient.mk (Ideal.span {(l : Acris0 l)} ^ n) y = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (by`. Rewrite using `[e2, Ideal.span_singleton_pow]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))`. Rewrite `hy` using `[hz]`.

Establish `hk : a ∈ (Ideal.span {(l : Acris0 l)} ^ n).map (algebraMap (Acris0 l) (Acris l))`. Conclude with `mem_map_of_evalₐ_eq_zero _ _ n a hy.symm`. Rewrite `hk` using `[ACris.map_span_p_pow, Ideal.span_singleton_pow]`. Conclude with `hk`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`.

Conclude with `cris_natCast_pow A n`.
-/
theorem ker_cris (h : IsBase l A) (n : ℕ) :
    RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : Acris0 l)}) n a)
    have e : A.cris n a = A.mkAcr n (A.cris0 y) := by
      simp only [cris, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hy,
        Ideal.Quotient.lift_mk]
    rw [RingHom.mem_ker, e] at ha
    have hm : A.cris0 y ∈ Ideal.span {(l : A.Acr0) ^ n} := Ideal.Quotient.eq_zero_iff_mem.1 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := (acrisZero_bijective_of_isBase A h).2 c
    have e2 : y = c' * (l : Acris0 l) ^ n := (acrisZero_bijective_of_isBase A h).1 (by
      rw [map_mul, map_pow, map_natCast, hc])
    have hz : Ideal.Quotient.mk (Ideal.span {(l : Acris0 l)} ^ n) y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by
        rw [e2, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [hz] at hy
    have hk : a ∈ (Ideal.span {(l : Acris0 l)} ^ n).map (algebraMap (Acris0 l) (Acris l)) := by
      exact mem_map_of_evalₐ_eq_zero _ _ n a hy.symm
    rw [ACris.map_span_p_pow, Ideal.span_singleton_pow] at hk
    exact hk
  · rw [Ideal.span_singleton_le_iff_mem]
    exact cris_natCast_pow A n

/- English proof (translation)
Introduce `A h` and use `⟨⟨acrisZero_bijective_of_isBase A h, oC_bijective A h⟩, fun n => ⟨cris_surjective A h n, ker_cris A h n⟩⟩`.
-/
theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A →
    (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧
      ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} :=
  fun A h => ⟨⟨acrisZero_bijective_of_isBase A h, oC_bijective A h⟩, fun n => ⟨cris_surjective A h n, ker_cris A h n⟩⟩

end GlobalTheory.CompanionTheory.BaseAcris
