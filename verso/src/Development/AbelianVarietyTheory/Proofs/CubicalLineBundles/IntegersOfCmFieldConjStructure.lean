import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmGeneratorSqQuadraticEq

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CM

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

/- English proof (translation)
Establish `h1 : algebraMap ℤ (𝓞 E) N ∣ algebraMap ℤ (𝓞 E) m` using `⟨z, by simpa using h.symm⟩`. Establish `h2` using `map_dvd (Algebra.norm ℤ) h1`. Rewrite `h2` using `[Algebra.norm_algebraMap, Algebra.norm_algebraMap]`. Conclude with `(Int.pow_dvd_pow_iff Module.finrank_pos.ne').1 h2`.
-/
theorem int_dvd_of_mul_eq_ringOfIntegers {N m : ℤ} {z : 𝓞 E} (h : (N : 𝓞 E) * z = m) : N ∣ m := by
  have h1 : algebraMap ℤ (𝓞 E) N ∣ algebraMap ℤ (𝓞 E) m := ⟨z, by simpa using h.symm⟩
  have h2 := map_dvd (Algebra.norm ℤ) h1
  rw [Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').1 h2

/- English proof (translation)
Take `⟨N', v', h1, h2, h3⟩` from `extract_gcd N v`. Generalize the expression as in `gcd N v = g at h1 h2`. Substitute `h1 h2` using the available equality. Establish `hg : g ≠ 0` using `left_ne_zero_of_mul hN`. Establish `h4 : N' ^ 2 ∣ d * v' ^ 2`.

Rewrite `h` using `[mul_pow, mul_pow, mul_left_comm]`. Conclude with `(mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).1 h`. Establish `hc : IsCoprime N' v'` using `(gcd_isUnit_iff _ _).1 h3`. Establish `h5 : N' * N' ∣ d`. Rewrite using `[← sq]`.

Conclude with `(hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h4`. Conclude with `mul_dvd_mul_left g (hd _ h5).dvd`.
-/
theorem int_dvd_of_sq_dvd_squarefree_mul_sq {d N v : ℤ} (hd : Squarefree d) (hN : N ≠ 0)
    (h : N ^ 2 ∣ d * v ^ 2) : N ∣ v := by
  obtain ⟨N', v', h1, h2, h3⟩ := extract_gcd N v
  generalize gcd N v = g at h1 h2
  subst h1 h2
  have hg : g ≠ 0 := left_ne_zero_of_mul hN
  have h4 : N' ^ 2 ∣ d * v' ^ 2 := by
    rw [mul_pow, mul_pow, mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).1 h
  have hc : IsCoprime N' v' := (gcd_isUnit_iff _ _).1 h3
  have h5 : N' * N' ∣ d := by
    rw [← sq]
    exact (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h4
  exact mul_dvd_mul_left g (hd _ h5).dvd

/- English proof (translation)
Establish `h4 : 4 * ((1 + H.d) / 4) = 1 + H.d` using `by have := H.d_mod; omega`. Establish `h5 : (4 : 𝓞 E) * (((1 + H.d) / 4 : ℕ) : 𝓞 E) = 1 + H.d` using `by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) h4`. Establish `h` using `H.rt_sq`. Rewrite `h` using `[rt_eq]`. Apply `mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)` to reduce the goal to its premises.

Take the linear combination `h + h5`.
-/
theorem cm_generator_sq_quadratic_eq (H : Host E) : H.w0 ^ 2 + (((1 + H.d) / 4 : ℕ) : 𝓞 E) = H.w0 := by
  have h4 : 4 * ((1 + H.d) / 4) = 1 + H.d := by have := H.d_mod; omega
  have h5 : (4 : 𝓞 E) * (((1 + H.d) / 4 : ℕ) : 𝓞 E) = 1 + H.d := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) h4
  have h := H.rt_sq
  rw [rt_eq] at h
  apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
  linear_combination h + h5

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CMGeneratorSquare.main`. Consider the case `exact _root_.GlobalTheory.CMGeneratorSquare.main`. Consider the case `(apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CMGeneratorSquare.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CMGeneratorSquare.main ..)`.
-/
theorem exists_coord (H : Host E) {a : 𝓞 E} (ha : a ∈ OK H) : ∃ u v : ℤ, a = u + v * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquare.main
  | exact _root_.GlobalTheory.CMGeneratorSquare.main
  | (apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquare.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquare.main ..)

/- English proof (translation)
Establish `h1` using `congrArg H.bar h`. Rewrite `h1` using `[map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator, map_zero]`. Establish `h2 : (v : 𝓞 E) * H.rt = 0` using `by rw [rt_eq]; linear_combination h - h1`. Establish `h3 : v = 0` using `by exact_mod_cast (mul_eq_zero.1 h2).resolve_right (rt_ne_zero H)`. Substitute `h3` using the available equality.

Conclude with `⟨by simpa using h, rfl⟩`.
-/
theorem coord_eq_zero (H : Host E) {u v : ℤ} (h : (u : 𝓞 E) + v * H.w0 = 0) : u = 0 ∧ v = 0 := by
  have h1 := congrArg H.bar h
  rw [map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator, map_zero] at h1
  have h2 : (v : 𝓞 E) * H.rt = 0 := by rw [rt_eq]; linear_combination h - h1
  have h3 : v = 0 := by exact_mod_cast (mul_eq_zero.1 h2).resolve_right (rt_ne_zero H)
  subst h3
  exact ⟨by simpa using h, rfl⟩

/- English proof (translation)
The claim follows from `add_mem (intCast_mem _ u) (mul_mem (intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))`.
-/
theorem coord_mem (H : Host E) (u v : ℤ) : (u : 𝓞 E) + v * H.w0 ∈ OK H :=
  add_mem (intCast_mem _ u) (mul_mem (intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))

/- English proof (translation)
Establish `h` using `cm_generator_sq_quadratic_eq H`. Generalize the expression as in `(1 + H.d) / 4 = k at h`. Rewrite using `[map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]`. Use `push_cast`. Take the linear combination `(-v ^ 2 : 𝓞 E) * h`.
-/
theorem coord_mul_bar (H : Host E) (u v : ℤ) : ((u : 𝓞 E) + v * H.w0) * H.bar (u + v * H.w0) =
    ((u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 : ℤ) : 𝓞 E) := by
  have h := cm_generator_sq_quadratic_eq H
  generalize (1 + H.d) / 4 = k at h
  rw [map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (-v ^ 2 : 𝓞 E) * h

/- English proof (translation)
Take `⟨u, v, h⟩` from `exists_coord H hy`. Establish `hb` using `congrArg H.bar h`. Establish `hn` using `coord_mul_bar H u v`. Rewrite `hn` using `[← h, map_mul, map_intCast]`. Rewrite `hb` using `[map_mul, map_add, map_mul, map_intCast, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]`.

Establish `h1 : N ∣ 2 * u + v` using `int_dvd_of_mul_eq_ringOfIntegers (z := y + H.bar y) (by push_cast; linear_combination h + hb)`. Establish `h2 : N ^ 2 ∣ u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2` using `int_dvd_of_mul_eq_ringOfIntegers (z := y * H.bar y) (by rw [← hn]; push_cast; ring)`. Establish `h4 : (4 : ℤ) * ((1 + H.d) / 4 : ℕ) = 1 + H.d` using `by have := H.d_mod; omega`. Establish `h3 : N ^ 2 ∣ H.d * v ^ 2`. Use `dvd_sub (h2.mul_left 4) (pow_dvd_pow_of_dvd h1 2)` as an intermediate fact.

Rewrite using `[show 4 * (u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2) - (2 * u + v) ^ 2 = H.d * v ^ 2 by` and apply the resulting hypothesis. Take the linear combination `v ^ 2 * h4] at this`. Take `⟨v', rfl⟩` from `int_dvd_of_sq_dvd_squarefree_mul_sq (Int.squarefree_natCast.2 H.d_prime.squarefree) hN h3`. Take `⟨u', rfl⟩ : N ∣ u` from `int_dvd_of_mul_eq_ringOfIntegers (z := y - (v' : 𝓞 E) * H.w0) (by push_cast at h; linear_combination h)`. Establish `: y = u' + v' * H.w0` using `mul_left_cancel₀ (show (N : 𝓞 E) ≠ 0 by exact_mod_cast hN) (by push_cast at h; linear_combination h)`.

Rewrite using `[this]`. Conclude with `coord_mem H u' v'`.
-/
theorem mem_OK_of_int_mul_mem (H : Host E) {N : ℤ} (hN : N ≠ 0) {y : 𝓞 E} (hy : (N : 𝓞 E) * y ∈ OK H) :
    y ∈ OK H := by
  obtain ⟨u, v, h⟩ := exists_coord H hy
  have hb := congrArg H.bar h
  have hn := coord_mul_bar H u v
  rw [← h, map_mul, map_intCast] at hn
  rw [map_mul, map_add, map_mul, map_intCast, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator] at hb
  have h1 : N ∣ 2 * u + v :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y + H.bar y) (by push_cast; linear_combination h + hb)
  have h2 : N ^ 2 ∣ u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y * H.bar y) (by rw [← hn]; push_cast; ring)
  have h4 : (4 : ℤ) * ((1 + H.d) / 4 : ℕ) = 1 + H.d := by have := H.d_mod; omega
  have h3 : N ^ 2 ∣ H.d * v ^ 2 := by
    have := dvd_sub (h2.mul_left 4) (pow_dvd_pow_of_dvd h1 2)
    rwa [show 4 * (u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2) - (2 * u + v) ^ 2 = H.d * v ^ 2 by
      linear_combination v ^ 2 * h4] at this
  obtain ⟨v', rfl⟩ := int_dvd_of_sq_dvd_squarefree_mul_sq
    (Int.squarefree_natCast.2 H.d_prime.squarefree) hN h3
  obtain ⟨u', rfl⟩ : N ∣ u :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y - (v' : 𝓞 E) * H.w0) (by push_cast at h; linear_combination h)
  have : y = u' + v' * H.w0 :=
    mul_left_cancel₀ (show (N : 𝓞 E) ≠ 0 by exact_mod_cast hN) (by push_cast at h; linear_combination h)
  rw [this]
  exact coord_mem H u' v'

/- English proof (translation)
The claim follows from `Module.Finite.of_injective (OK H).val.toLinearMap Subtype.val_injective`.
-/
theorem finite_int_OK (H : Host E) : Module.Finite ℤ (OK H) :=
  Module.Finite.of_injective (OK H).val.toLinearMap Subtype.val_injective

/- English proof (translation)
Use `finite_int_OK H` as an intermediate fact. Rewrite using `[isIntegrallyClosed_iff (FractionRing (OK H))]`. Introduce `x hx`. Establish `hinj : Function.Injective (algebraMap (OK H) E)` using `RingOfIntegers.coe_injective.comp Subtype.val_injective`. Set `φ : FractionRing (OK H) →ₐ[OK H] E` to `IsFractionRing.liftAlgHom (g := Algebra.ofId (OK H) E) hinj`.

Establish `hy : IsIntegral ℤ (φ x)` using `isIntegral_trans _ (hx.map φ)`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := OK H) x`. Take `⟨n, hn, c, hc⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) b).exists_nonzero_dvd hb`. Establish `hb' : algebraMap (OK H) E b ≠ 0` using `(map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)`. Establish `hm : (⟨_, hy⟩ : 𝓞 E) ∈ OK H`.

Use `mem_OK_of_int_mul_mem H hn ?_` and prove the remaining obligations. Use `(a * c).2 using 1` and compare the differences between its conclusion and the goal. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h1 : (n : E) = algebraMap (OK H) E b * algebraMap (OK H) E c`. Rewrite using `[← map_mul, ← hc]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(n : E) * φ _ = algebraMap (OK H) E (a * c)`. Rewrite using `[map_div₀, φ.commutes, φ.commutes, h1, map_mul]`. Clear the denominators using the available nonvanishing facts. Use `⟨⟨_, hm⟩, φ.injective ?_⟩` and prove the remaining obligations.

Conclude with `φ.commutes _`.
-/
theorem isIntegrallyClosed_OK (H : Host E) : IsIntegrallyClosed (OK H) := by
  have := finite_int_OK H
  rw [isIntegrallyClosed_iff (FractionRing (OK H))]
  intro x hx
  have hinj : Function.Injective (algebraMap (OK H) E) :=
    RingOfIntegers.coe_injective.comp Subtype.val_injective
  let φ : FractionRing (OK H) →ₐ[OK H] E :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId (OK H) E) hinj
  have hy : IsIntegral ℤ (φ x) := isIntegral_trans _ (hx.map φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OK H) x
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) b).exists_nonzero_dvd hb
  have hb' : algebraMap (OK H) E b ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
  have hm : (⟨_, hy⟩ : 𝓞 E) ∈ OK H := by
    refine mem_OK_of_int_mul_mem H hn ?_
    convert (a * c).2 using 1
    apply RingOfIntegers.coe_injective
    have h1 : (n : E) = algebraMap (OK H) E b * algebraMap (OK H) E c := by
      rw [← map_mul, ← hc]; simp
    change (n : E) * φ _ = algebraMap (OK H) E (a * c)
    rw [map_div₀, φ.commutes, φ.commutes, h1, map_mul]
    field_simp
  refine ⟨⟨_, hm⟩, φ.injective ?_⟩
  exact φ.commutes _

/- English proof (translation)
The claim follows from `have := finite_int_OK H { isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ (OK H)), Ring.DimensionLEOne.of_isIntegral ℤ (OK H), isIntegrallyClosed_OK H with }`.
-/
theorem isDedekindDomain_OK (H : Host E) : IsDedekindDomain (OK H) :=
  have := finite_int_OK H
  { isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ (OK H)),
    Ring.DimensionLEOne.of_isIntegral ℤ (OK H), isIntegrallyClosed_OK H with }

/- English proof (translation)
Take `⟨u, v, h⟩` from `exists_coord H a.2`. Use `⟨(u, v), Subtype.ext h, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨u', v'⟩ h'`. Establish `h2 : (a : 𝓞 E) = u' + v' * H.w0` using `congrArg Subtype.val h'`. Take `⟨h3, h4⟩` from `coord_eq_zero H (u := u' - u) (v := v' - v) (by push_cast; linear_combination h - h2)`.

Conclude with `Prod.ext (sub_eq_zero.1 h3) (sub_eq_zero.1 h4)`.
-/
theorem existsUnique_coord (H : Host E) (a : OK H) :
    ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H := by
  obtain ⟨u, v, h⟩ := exists_coord H a.2
  refine ⟨(u, v), Subtype.ext h, ?_⟩
  rintro ⟨u', v'⟩ h'
  have h2 : (a : 𝓞 E) = u' + v' * H.w0 := congrArg Subtype.val h'
  obtain ⟨h3, h4⟩ := coord_eq_zero H (u := u' - u) (v := v' - v) (by push_cast; linear_combination h - h2)
  exact Prod.ext (sub_eq_zero.1 h3) (sub_eq_zero.1 h4)

/- English proof (translation)
Set `f : (ℤ × ℤ) →ₗ[ℤ] OK H` to `LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1) (LinearMap.toSpanSingleton ℤ _ (wK H))`. Establish `hf : Function.Bijective f`. Rewrite using `[Function.bijective_iff_existsUnique]`. Introduce `a`. Simplify `existsUnique_coord H a` using `[f, eq_comm (a := a)]`.

Rewrite using `[← (LinearEquiv.ofBijective f hf).finrank_eq]`. Simplify using the standard rewrite rules.
-/
theorem finrank_int_OK (H : Host E) : Module.finrank ℤ (OK H) = 2 := by
  let f : (ℤ × ℤ) →ₗ[ℤ] OK H := LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1)
    (LinearMap.toSpanSingleton ℤ _ (wK H))
  have hf : Function.Bijective f := by
    rw [Function.bijective_iff_existsUnique]
    intro a
    simpa [f, eq_comm (a := a)] using existsUnique_coord H a
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  simp

def barOK (H : Host E) : OK H ≃+* OK H where
  toFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  invFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  left_inv a := Subtype.ext (bar_bar H a)
  right_inv a := Subtype.ext (bar_bar H a)
  map_mul' a b := Subtype.ext (map_mul H.bar _ _)
  map_add' a b := Subtype.ext (map_add H.bar _ _)

/- English proof (translation)
Use `finite_int_OK H` as an intermediate fact. Establish `: Module.Finite ℤ M` using `Module.Finite.trans (𝓞 E) M`. Establish `: Module.Finite (OK H) M` using `Module.Finite.of_restrictScalars_finite ℤ _ _`. Rewrite using `[← finrank_int_OK H, ← finrank_int_eq_mul_of_finite, ← RingOfIntegers.rank, ← finrank_int_eq_mul_of_finite]`.
-/
theorem two_mul_finrank_OK (H : Host E) (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] :
    2 * Module.finrank (OK H) M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  have := finite_int_OK H
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  have : Module.Finite (OK H) M := Module.Finite.of_restrictScalars_finite ℤ _ _
  rw [← finrank_int_OK H, ← finrank_int_eq_mul_of_finite, ← RingOfIntegers.rank,
    ← finrank_int_eq_mul_of_finite]

/- English proof (translation)
Introduce `E _ _ _ H`. Establish `h2 : 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E`. Simplify using `using two_mul_finrank_OK H (𝓞 E)`. Use `⟨isDedekindDomain_OK H, existsUnique_coord H, ⟨barOK H, fun _ => rfl, Subtype.ext ?_, fun a => Subtype.ext (bar_bar H a)⟩, Subtype.ext (cm_generator_sq_quadratic_eq H), h2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `H.w0 + H.bar H.w0 = 1`.

Rewrite using `[cmHost_bar_halfIntegerGenerator, add_sub_cancel]`. Introduce `M _ _ _ _`. Use `finite_int_OK H` as an intermediate fact. Use `isDedekindDomain_OK H` as an intermediate fact. Establish `: Module.Finite ℤ M` using `Module.Finite.trans (𝓞 E) M`.

Establish `: Module.IsTorsionFree ℤ M` using `Module.IsTorsionFree.trans (𝓞 E)`. Use `⟨Module.Finite.of_restrictScalars_finite ℤ _ _, Forms.projective_of_int _ _, ?_⟩` and prove the remaining obligations. Establish `h3` using `two_mul_finrank_OK H M`. Rewrite `h3` using `[← h2, mul_assoc]`. Rewrite using `[← h2, Nat.mul_div_cancel_left _ two_pos]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem OK_isDedekindDomain_and_projective :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  intro E _ _ _ H
  have h2 : 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E := by
    simpa using two_mul_finrank_OK H (𝓞 E)
  refine ⟨isDedekindDomain_OK H, existsUnique_coord H,
    ⟨barOK H, fun _ => rfl, Subtype.ext ?_, fun a => Subtype.ext (bar_bar H a)⟩, Subtype.ext (cm_generator_sq_quadratic_eq H), h2, ?_⟩
  · change H.w0 + H.bar H.w0 = 1
    rw [cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  · intro M _ _ _ _
    have := finite_int_OK H
    have := isDedekindDomain_OK H
    have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
    have : Module.IsTorsionFree ℤ M := Module.IsTorsionFree.trans (𝓞 E)
    refine ⟨Module.Finite.of_restrictScalars_finite ℤ _ _, Forms.projective_of_int _ _, ?_⟩
    have h3 := two_mul_finrank_OK H M
    rw [← h2, mul_assoc] at h3
    rw [← h2, Nat.mul_div_cancel_left _ two_pos]
    omega

end GlobalTheory.CM
