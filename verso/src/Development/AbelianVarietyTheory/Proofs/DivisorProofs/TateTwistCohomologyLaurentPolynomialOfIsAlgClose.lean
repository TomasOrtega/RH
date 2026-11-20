import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.LaurentUnits
open LaurentPolynomial Polynomial

variable (K : Type) [Field K]

/- English proof (translation)
The claim follows from `IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (X : K[X])) _ (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)`.
-/
theorem isDomain : IsDomain (LaurentPolynomial K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (X : K[X])) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

/- English proof (translation)
Use `⟨fun P => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `(IsPrincipalIdealRing.principal (P.comap (algebraMap K[X] (LaurentPolynomial K))))`. Use `⟨algebraMap K[X] (LaurentPolynomial K) g, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalization.map_comap (Submonoid.powers (X : K[X])) (LaurentPolynomial K) P, Ideal.under_def, hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]`.
-/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (LaurentPolynomial K) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.comap (algebraMap K[X] (LaurentPolynomial K))))
  refine ⟨algebraMap K[X] (LaurentPolynomial K) g, ?_⟩
  rw [← IsLocalization.map_comap (Submonoid.powers (X : K[X])) (LaurentPolynomial K) P, Ideal.under_def, hg,
    Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/- English proof (translation)
Take `⟨n, p, hp⟩` from `exists_T_pow (u : LaurentPolynomial K)`. Take `⟨n', r, hr⟩` from `exists_T_pow ((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)`. Establish `hpr : p * r = X ^ (n + n')`. Apply `Polynomial.toLaurent_injective` to reduce the goal to its premises. Rewrite using `[map_mul, hp, hr, Polynomial.toLaurent_X_pow]`.

Establish `: (u : LaurentPolynomial K) * T n * (((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) * T n') = T n * T n'`. Rewrite using `[mul_mul_mul_comm, Units.mul_inv, one_mul]`. Rewrite using `[this, ← T_add]`. Use `push_cast`. Both sides reduce to the same expression.

Take `⟨i, -, hi⟩` from `(dvd_prime_pow Polynomial.prime_X (n + n')).1 ⟨r, hpr.symm⟩`. Take `⟨v, hv⟩` from `hi.symm`. Take `⟨c, -, hc⟩` from `Polynomial.isUnit_iff.1 v.isUnit`. Use `⟨c, (i : ℤ) - n, ?_⟩` and prove the remaining obligations. Establish `h1 : (u : LaurentPolynomial K) * T n = LaurentPolynomial.C c * T i`.

Rewrite using `[← hp, ← hv, ← hc, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]`. Use `_ = LaurentPolynomial.C c * T ((i : ℤ) - n) := by rw [h1, mul_assoc, ← T_add, sub_eq_add_neg]`.
-/
theorem units_eq (u : (LaurentPolynomial K)ˣ) :
    ∃ (c : K) (m : ℤ), (u : LaurentPolynomial K) = LaurentPolynomial.C c * T m := by
  obtain ⟨n, p, hp⟩ := exists_T_pow (u : LaurentPolynomial K)
  obtain ⟨n', r, hr⟩ := exists_T_pow ((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)
  have hpr : p * r = X ^ (n + n') := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hr, Polynomial.toLaurent_X_pow]
    have : (u : LaurentPolynomial K) * T n * (((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) * T n')
        = T n * T n' := by
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]
    rw [this, ← T_add]; push_cast; rfl
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X (n + n')).1 ⟨r, hpr.symm⟩
  obtain ⟨v, hv⟩ := hi.symm
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 v.isUnit
  refine ⟨c, (i : ℤ) - n, ?_⟩
  have h1 : (u : LaurentPolynomial K) * T n = LaurentPolynomial.C c * T i := by
    rw [← hp, ← hv, ← hc, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm]
  calc (u : LaurentPolynomial K) = (u : LaurentPolynomial K) * T n * T (-(n : ℤ)) := by
        rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
    _ = LaurentPolynomial.C c * T ((i : ℤ) - n) := by rw [h1, mul_assoc, ← T_add, sub_eq_add_neg]

/- English proof (translation)
Use `haveI := isDomain K`. Use `haveI := isPrincipalIdealRing K`. Use `haveI := UniqueFactorizationMonoid.toGCDMonoid (LaurentPolynomial K)`. Use `infer_instance`.
-/
theorem pic_subsingleton : Subsingleton (CommRing.Pic (LaurentPolynomial K)) := by
  haveI := isDomain K
  haveI := isPrincipalIdealRing K
  haveI := UniqueFactorizationMonoid.toGCDMonoid (LaurentPolynomial K)
  infer_instance

/- English proof (translation)
Use `haveI := isDomain K`. Use `haveI := isPrincipalIdealRing K`. Use `infer_instance`.
-/
theorem isDedekindDomain : IsDedekindDomain (LaurentPolynomial K) := by
  haveI := isDomain K
  haveI := isPrincipalIdealRing K
  infer_instance

/- English proof (translation)
Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [map_zero, zero_mul] at h`. Conclude with `(isUnit_T (R := K) a).ne_zero h`. Establish `h2` using `congrArg LaurentPolynomial.degree h`.

Rewrite `h2` using `[degree_T, degree_C_mul_T _ _ hc]`. Conclude with `WithBot.coe_inj.1 h2`.
-/
theorem laurent_monomial_exponent_eq {a b : ℤ} {c : K} (h : (T a : LaurentPolynomial K) = LaurentPolynomial.C c * T b) : a = b := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul] at h
    exact (isUnit_T (R := K) a).ne_zero h
  have h2 := congrArg LaurentPolynomial.degree h
  rw [degree_T, degree_C_mul_T _ _ hc] at h2
  exact WithBot.coe_inj.1 h2

/- English proof (translation)
Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]`. Consider the case `pred i ih`. Rewrite using `[zpow_sub_one, Units.val_mul, ih]`.

Establish `: ((((isUnit_T 1).unit)⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T (-1)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[IsUnit.unit_spec, ← T_add]`. Simplify using the standard rewrite rules. Rewrite using `[this, ← T_add]`.

Put the polynomial expressions in normal form.
-/
theorem val_T_unit_zpow (m : ℤ) :
    ((((isUnit_T 1).unit : (LaurentPolynomial K)ˣ) ^ m : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    have : ((((isUnit_T 1).unit)⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T (-1) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec, ← T_add]; simp
    rw [this, ← T_add]; ring_nf

end GlobalTheory.LaurentUnits

namespace GlobalTheory.GmAlgClosed
open LaurentPolynomial GlobalTheory.LaurentUnits

variable (q : ℕ) [NeZero q] (K : Type) [Field K]

noncomputable abbrev gEq : Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤) ≃+* LaurentPolynomial K :=
  (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial K))).commRingCatIsoToRingEquiv

/- English proof (translation)
Simplify using `using hq.map (algebraMap K (LaurentPolynomial K))`.
-/
theorem isUnit_q_L (hq : IsUnit (q : K)) : IsUnit (q : LaurentPolynomial K) := by
  simpa using hq.map (algebraMap K (LaurentPolynomial K))

/- English proof (translation)
Simplify using `using hq.map (gEq K).symm.toRingHom`.
-/
theorem isUnit_q_Γ (hq : IsUnit (q : LaurentPolynomial K)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤)) := by
  simpa using hq.map (gEq K).symm.toRingHom

noncomputable def kumL (hq : IsUnit (q : LaurentPolynomial K)) :
    (LaurentPolynomial K)ˣ →* Multiplicative (Ht q (sp (LaurentPolynomial K)) 1 1) where
  toFun u := Multiplicative.ofAdd (kum q (Units.map (gEq K).symm.toRingHom.toMonoidHom u))
  map_one' := by
    have h := ((a6add_holds q).2 (1 : (Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤))ˣ) 1
      (isUnit_q_Γ q K hq)).1
    rw [mul_one] at h
    rw [map_one, ofAdd_eq_one]
    exact add_left_cancel (b := kum q _) (c := 0) (by rw [add_zero]; exact h.symm)
  map_mul' u v := by
    rw [map_mul, ((a6add_holds q).2 _ _ (isUnit_q_Γ q K hq)).1, ofAdd_add]

/- English proof (translation)
Use `show Multiplicative.ofAdd (kum q _) = 1`. Rewrite using `[map_pow, ((a6add_holds q).2 _ 1 (isUnit_q_Γ q K hq)).2, ofAdd_zero]`.
-/
theorem kumL_pow_q (hq : IsUnit (q : LaurentPolynomial K)) (u : (LaurentPolynomial K)ˣ) :
    kumL q K hq (u ^ q) = 1 := by
  show Multiplicative.ofAdd (kum q _) = 1
  rw [map_pow, ((a6add_holds q).2 _ 1 (isUnit_q_Γ q K hq)).2, ofAdd_zero]

noncomputable abbrev tau : (LaurentPolynomial K)ˣ := (isUnit_T 1).unit

/- English proof (translation)
Rewrite using `[zmultiplesHom_apply, natCast_zsmul, ← toAdd_pow, ← map_pow, kumL_pow_q, toAdd_one]`.
-/
theorem zsmul_q (hq : IsUnit (q : LaurentPolynomial K)) :
    zmultiplesHom _ (Multiplicative.toAdd (kumL q K hq (tau K))) (q : ℤ) = 0 := by
  rw [zmultiplesHom_apply, natCast_zsmul, ← toAdd_pow, ← map_pow, kumL_pow_q, toAdd_one]

noncomputable def fL (hq : IsUnit (q : LaurentPolynomial K)) : ZMod q →+ Ht q (sp (LaurentPolynomial K)) 1 1 :=
  ZMod.lift q ⟨zmultiplesHom _ (Multiplicative.toAdd (kumL q K hq (tau K))), zsmul_q q K hq⟩

/- English proof (translation)
Rewrite using `[fL, ZMod.lift_coe]`. Use `show zmultiplesHom _ _ m = _`. Rewrite using `[zmultiplesHom_apply, map_zpow, toAdd_zpow]`.
-/
theorem fL_intCast (hq : IsUnit (q : LaurentPolynomial K)) (m : ℤ) :
    fL q K hq (m : ZMod q) = Multiplicative.toAdd (kumL q K hq (tau K ^ m)) := by
  rw [fL, ZMod.lift_coe]
  show zmultiplesHom _ _ m = _
  rw [zmultiplesHom_apply, map_zpow, toAdd_zpow]

variable [IsAlgClosed K]

/- English proof (translation)
Introduce `x`. Take `⟨u', hu'⟩` from `GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (LaurentPolynomial K) hq (fun c _ => @Subsingleton.elim _ (pic_subsingleton K) _ _) x`. Use `set u : (LaurentPolynomial K)ˣ := Units.map (gEq K).toRingHom.toMonoidHom u'`. Establish `hu : Units.map (gEq K).symm.toRingHom.toMonoidHom u = u'` using `by ext; simp [u]`. Take `⟨c, m, hcm⟩` from `units_eq K u`.

Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hcm` using `[map_zero, zero_mul]`. Conclude with `u.ne_zero hcm`. Take `⟨d, hd⟩` from `IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero (NeZero.ne q))`.

Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`. Conclude with `hc (by rw [← hd, zero_pow (NeZero.ne q)])`. Use `set w : (LaurentPolynomial K)ˣ := Units.map (LaurentPolynomial.C : K →+* LaurentPolynomial K).toMonoidHom (Units.mk0 d hd0)`. Establish `huw : u = w ^ q * tau K ^ m`.

Use `ext`. Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val, val_T_unit_zpow, hcm, ← hd, map_pow]`. Both sides reduce to the same expression. Use `⟨(m : ZMod q), ?_⟩` and prove the remaining obligations. Rewrite using `[fL_intCast, ← hu', ← hu]`.

Use `show _ = Multiplicative.toAdd (kumL q K hq u)`. Rewrite using `[huw, map_mul, kumL_pow_q, one_mul]`.
-/
theorem fL_surjective (hq : IsUnit (q : LaurentPolynomial K)) : Function.Surjective (fL q K hq) := by
  intro x
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (LaurentPolynomial K) hq
    (fun c _ => @Subsingleton.elim _ (pic_subsingleton K) _ _) x
  set u : (LaurentPolynomial K)ˣ := Units.map (gEq K).toRingHom.toMonoidHom u'
  have hu : Units.map (gEq K).symm.toRingHom.toMonoidHom u = u' := by ext; simp [u]
  obtain ⟨c, m, hcm⟩ := units_eq K u
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcm
    exact u.ne_zero hcm
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hd, zero_pow (NeZero.ne q)])
  set w : (LaurentPolynomial K)ˣ := Units.map (LaurentPolynomial.C : K →+* LaurentPolynomial K).toMonoidHom (Units.mk0 d hd0)
  have huw : u = w ^ q * tau K ^ m := by
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, val_T_unit_zpow, hcm, ← hd, map_pow]
    rfl
  refine ⟨(m : ZMod q), ?_⟩
  rw [fL_intCast, ← hu', ← hu]
  show _ = Multiplicative.toAdd (kumL q K hq u)
  rw [huw, map_mul, kumL_pow_q, one_mul]

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun z hz => ?_` and prove the remaining obligations. Establish `hz' : fL q K hq ((z.val : ℤ) : ZMod q) = 0`. Rewrite using `[Int.cast_natCast, ZMod.natCast_zmod_val]`. Conclude with `hz`. Rewrite `hz'` using `[fL_intCast, zpow_natCast]`.

Take `⟨v, hv⟩` from `GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial K) hq _ hz'`. Establish `hv' : tau K ^ z.val = (Units.map (gEq K).toRingHom.toMonoidHom v) ^ q`. Use `congrArg (Units.map (gEq K).toRingHom.toMonoidHom) hv` as an intermediate fact. Rewrite using `[← map_pow, ← this]`. Use `ext`.

Simplify using the standard rewrite rules. Take `⟨c, k, hck⟩` from `units_eq K (Units.map (gEq K).toRingHom.toMonoidHom v)`. Establish `hT : (T (z.val : ℤ) : LaurentPolynomial K) = LaurentPolynomial.C (c ^ q) * T ((q : ℤ) * k)`. Use `congrArg (fun w : (LaurentPolynomial K)ˣ => (w : LaurentPolynomial K)) hv'` as an intermediate fact. Simplify using `only [Units.val_pow_eq_pow_val, hck, IsUnit.unit_spec, T_pow, mul_one, mul_pow, map_pow] at this`.

Rewrite using `[map_pow]`. Conclude with `this`. Establish `he` using `laurent_monomial_exponent_eq K hT`. Establish `hlt : ((z.val : ℕ) : ℤ) < q` using `by exact_mod_cast ZMod.val_lt z`. Establish `hq0 : (0 : ℤ) < q` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)`.

Establish `h0 : ((z.val : ℕ) : ℤ) = 0`. Break down `le_or_gt k 0 with hk | hk` into its components or cases. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Conclude with `(ZMod.val_eq_zero z).1 (by exact_mod_cast h0)`.
-/
theorem fL_injective (hq : IsUnit (q : LaurentPolynomial K)) : Function.Injective (fL q K hq) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have hz' : fL q K hq ((z.val : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hz
  rw [fL_intCast, zpow_natCast] at hz'
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial K) hq _ hz'
  have hv' : tau K ^ z.val = (Units.map (gEq K).toRingHom.toMonoidHom v) ^ q := by
    have := congrArg (Units.map (gEq K).toRingHom.toMonoidHom) hv
    rw [← map_pow, ← this]; ext; simp
  obtain ⟨c, k, hck⟩ := units_eq K (Units.map (gEq K).toRingHom.toMonoidHom v)
  have hT : (T (z.val : ℤ) : LaurentPolynomial K) = LaurentPolynomial.C (c ^ q) * T ((q : ℤ) * k) := by
    have := congrArg (fun w : (LaurentPolynomial K)ˣ => (w : LaurentPolynomial K)) hv'
    simp only [Units.val_pow_eq_pow_val, hck, IsUnit.unit_spec, T_pow, mul_one, mul_pow, map_pow] at this
    rw [map_pow]; exact this
  have he := laurent_monomial_exponent_eq K hT
  have hlt : ((z.val : ℕ) : ℤ) < q := by exact_mod_cast ZMod.val_lt z
  have hq0 : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h0 : ((z.val : ℕ) : ℤ) = 0 := by
    rcases le_or_gt k 0 with hk | hk
    · nlinarith
    · nlinarith
  exact (ZMod.val_eq_zero z).1 (by exact_mod_cast h0)

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic q K) (by`. Rewrite using `[Polynomial.degree_cyclotomic]`. Conclude with `(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne')` after adjusting the coercions. Use `⟨algebraMap K _ ζ, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, hζ.eq_zero, map_zero]`.
-/
theorem exists_root_L (hq : IsUnit (q : K)) :
    ∃ ζ : LaurentPolynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q K) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne')
  refine ⟨algebraMap K _ ζ, ?_⟩
  rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    Polynomial.map_cyclotomic, hζ.eq_zero, map_zero]

end GlobalTheory.GmAlgClosed

/- English proof (translation)
Introduce `q _ K _ _ hq n i`. Use `haveI := GlobalTheory.LaurentUnits.isDedekindDomain K`. Use `⟨fun hn => GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (LaurentPolynomial K) hq n i hn, ?_⟩` and prove the remaining obligations. Establish `hqL` using `GlobalTheory.GmAlgClosed.isUnit_q_L q K hq`. Take `⟨e1⟩` from `GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (LaurentPolynomial K) hqL (GlobalTheory.GmAlgClosed.exists_root_L q K hq) 1 i 1`.

Conclude with `⟨e1.trans (AddEquiv.ofBijective _ ⟨GlobalTheory.GmAlgClosed.fL_injective q K hqL, GlobalTheory.GmAlgClosed.fL_surjective q K hqL⟩).symm⟩`.
-/
theorem GlobalTheory.EtC.gm_algClosed_cohomology : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial K)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial K)) 1 i ≃+ ZMod q) := by
  intro q _ K _ _ hq n i
  haveI := GlobalTheory.LaurentUnits.isDedekindDomain K
  refine ⟨fun hn => GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (LaurentPolynomial K) hq n i hn, ?_⟩
  have hqL := GlobalTheory.GmAlgClosed.isUnit_q_L q K hq
  obtain ⟨e1⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (LaurentPolynomial K) hqL (GlobalTheory.GmAlgClosed.exists_root_L q K hq) 1 i 1
  exact ⟨e1.trans (AddEquiv.ofBijective _
    ⟨GlobalTheory.GmAlgClosed.fL_injective q K hqL, GlobalTheory.GmAlgClosed.fL_surjective q K hqL⟩).symm⟩
