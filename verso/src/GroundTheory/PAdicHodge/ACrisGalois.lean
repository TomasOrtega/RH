import Mathlib
import GroundTheory.PAdicHodge.FactorizationFactorialLe
import GroundTheory.PAdicHodge.AInfGalois
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section ExtGeneric

variable {A B : Type*} [CommRing A] [CommRing B]

/- English proof (translation)
Establish `hz' : z ∈ (Ideal.span {a} ^ n).map (algebraMap A (AdicCompletion (Ideal.span {a}) A))`. Rewrite using `[← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _) n, RingHom.mem_ker]`. Conclude with `hz`. Rewrite `hz'` using `[Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hz'`.

Rewrite using `[map_mul, map_pow, map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hF n)`.
-/
theorem AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero {a : A} {b : B}
    (F : AdicCompletion (Ideal.span {a}) A →+* B)
    (hF : F (algebraMap A _ a) ∈ Ideal.span {b}) (n : ℕ) {z : AdicCompletion (Ideal.span {a}) A}
    (hz : AdicCompletion.evalₐ (Ideal.span {a}) n z = 0) :
    F z ∈ Ideal.span {b} ^ n := by
  have hz' : z ∈ (Ideal.span {a} ^ n).map (algebraMap A (AdicCompletion (Ideal.span {a}) A)) := by
    rw [← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _) n, RingHom.mem_ker]
    exact hz
  rw [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    at hz'
  obtain ⟨c, rfl⟩ := hz'
  rw [map_mul, map_pow, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hF n)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[IsHausdorff.eq_iff_smodEq (I := Ideal.span {b})]`. Introduce `n`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {a}) n x)`.

Establish `h1 : AdicCompletion.evalₐ (Ideal.span {a}) n (algebraMap A (AdicCompletion (Ideal.span {a}) A) y) = Ideal.Quotient.mk _ y`. Rewrite using `[AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of]`. Establish `hz : AdicCompletion.evalₐ (Ideal.span {a}) n (x - algebraMap A (AdicCompletion (Ideal.span {a}) A) y) = 0`. Rewrite using `[map_sub, h1, hy, sub_self]`. Establish `e : F x - G x = F (x - algebraMap A _ y) - G (x - algebraMap A _ y)`.

Rewrite using `[map_sub, map_sub, h y]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem (AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero F hF n hz) (AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero G hG n hz)`.
-/
theorem AdicCompletion.ringHom_ext_span {a : A} {b : B} [IsHausdorff (Ideal.span {b}) B]
    {F G : AdicCompletion (Ideal.span {a}) A →+* B}
    (hF : F (algebraMap A _ a) ∈ Ideal.span {b}) (hG : G (algebraMap A _ a) ∈ Ideal.span {b})
    (h : ∀ y : A, F (algebraMap A _ y) = G (algebraMap A _ y)) : F = G := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {b})]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {a}) n x)
  have h1 : AdicCompletion.evalₐ (Ideal.span {a}) n
      (algebraMap A (AdicCompletion (Ideal.span {a}) A) y) = Ideal.Quotient.mk _ y := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.evalₐ_of]
  have hz : AdicCompletion.evalₐ (Ideal.span {a}) n
      (x - algebraMap A (AdicCompletion (Ideal.span {a}) A) y) = 0 := by
    rw [map_sub, h1, hy, sub_self]
  have e : F x - G x = F (x - algebraMap A _ y) - G (x - algebraMap A _ y) := by
    rw [map_sub, map_sub, h y]; ring
  rw [e]
  exact sub_mem (AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero F hF n hz)
    (AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero G hG n hz)

end ExtGeneric

namespace ACris

section Ext

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

/- English proof (translation)
Use `AdicCompletion.ringHom_ext_span (b := (p : B)) ?_ ?_ fun y => ?_` and prove the remaining obligations. Rewrite using `[map_natCast, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[map_natCast, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`.

Rewrite using `[AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Conclude with `h y`.
-/
theorem ringHom_ext {B : Type*} [CommRing B] [IsHausdorff (Ideal.span {(p : B)}) B]
    {F G : ACris K p →+* B}
    (h : ∀ y : ACrisZero K p, F (AdicCompletion.of _ _ y) = G (AdicCompletion.of _ _ y)) :
    F = G := by
  refine AdicCompletion.ringHom_ext_span (b := (p : B)) ?_ ?_ fun y => ?_
  · rw [map_natCast, map_natCast]; exact Ideal.mem_span_singleton_self _
  · rw [map_natCast, map_natCast]; exact Ideal.mem_span_singleton_self _
  · rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact h y

/- English proof (translation)
Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem span_p_le_comap_endo (f : ACrisZero K p →+* ACrisZero K p) :
    Ideal.span {(p : ACrisZero K p)} ≤ (Ideal.span {(p : ACris K p)}).comap
      ((algebraMap (ACrisZero K p) (ACris K p)).comp f) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

def extendEndo (f : ACrisZero K p →+* ACrisZero K p) : ACris K p →+* ACris K p :=
  AdicCompletion.extendRingHom _ _ ((algebraMap (ACrisZero K p) (ACris K p)).comp f)
    (span_p_le_comap_endo f)

/- English proof (translation)
The claim follows from `AdicCompletion.extendRingHom_of _ _ _ _ y`.
-/
theorem extendEndo_of (f : ACrisZero K p →+* ACrisZero K p) (y : ACrisZero K p) :
    extendEndo f (AdicCompletion.of _ _ y) = AdicCompletion.of _ _ (f y) :=
  AdicCompletion.extendRingHom_of _ _ _ _ y

/- English proof (translation)
The claim follows from `ringHom_ext fun y => by rw [extendEndo_of, RingHom.id_apply, RingHom.id_apply]`.
-/
theorem extendEndo_id : extendEndo (RingHom.id (ACrisZero K p)) = RingHom.id (ACris K p) :=
  ringHom_ext fun y => by rw [extendEndo_of, RingHom.id_apply, RingHom.id_apply]

/- English proof (translation)
The claim follows from `ringHom_ext fun y => by rw [RingHom.comp_apply, extendEndo_of g y, extendEndo_of f (g y), extendEndo_of (f.comp g) y, RingHom.comp_apply]`.
-/
theorem extendEndo_comp (f g : ACrisZero K p →+* ACrisZero K p) :
    (extendEndo f).comp (extendEndo g) = extendEndo (f.comp g) :=
  ringHom_ext fun y => by
    rw [RingHom.comp_apply, extendEndo_of g y, extendEndo_of f (g y), extendEndo_of (f.comp g) y,
      RingHom.comp_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_eq_extendEndo : phi K p = extendEndo (phiZero K p) :=
  rfl

end Ext

section Galois

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

def galAway (σ : Gal(PadicAlgCl p/K)) : 𝔸 →+* 𝔸 :=
  Localization.awayLift ((algebraMap (AInf ℂ_[p] p) 𝔸).comp (AInf.galMap σ)) (p : AInf ℂ_[p] p)
    (by
      rw [RingHom.comp_apply, map_natCast (AInf.galMap σ)]
      exact IsLocalization.Away.algebraMap_isUnit (p : AInf ℂ_[p] p))

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ x`.
-/
theorem galAway_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    galAway σ (algebraMap (AInf ℂ_[p] p) 𝔸 x) = algebraMap (AInf ℂ_[p] p) 𝔸 (σ • x) :=
  IsLocalization.lift_eq _ x

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap, one_smul, RingHom.id_apply])`.
-/
theorem galAway_one : galAway (1 : Gal(PadicAlgCl p/K)) = RingHom.id 𝔸 :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap, one_smul, RingHom.id_apply])

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap, galAway_algebraMap, galAway_algebraMap, mul_smul])`.
-/
theorem galAway_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galAway (σ * τ) = (galAway σ).comp (galAway τ) :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap,
      galAway_algebraMap, galAway_algebraMap, mul_smul])

/- English proof (translation)
Use `symm`. Rewrite using `[dpow_eq_iff, ← map_natCast (galAway σ), ← map_mul, factorial_mul_dpow, map_pow, galAway_algebraMap]`.
-/
theorem galAway_dpow (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (x : AInf ℂ_[p] p) :
    galAway σ (dpow n x) = dpow n (σ • x) := by
  symm
  rw [dpow_eq_iff, ← map_natCast (galAway σ), ← map_mul, factorial_mul_dpow, map_pow,
    galAway_algebraMap]

/- English proof (translation)
Rewrite `hx`, the goal using `[RingHom.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AInf.fontaineTheta_gal_smul, hx]`. Simplify using the standard rewrite rules.
-/
theorem gal_smul_mem_ker (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ RingHom.ker θ) :
    σ • x ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker] at hx ⊢
  apply Subtype.ext
  rw [AInf.fontaineTheta_gal_smul, hx]
  simp

/- English proof (translation)
Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨n, x, hx, rfl⟩` from `hy`. Rewrite using `[galAway_dpow]`. Conclude with `dpow_mem (gal_smul_mem_ker σ hx) n`.

Consider the case `algebraMap r`. Rewrite using `[galAway_algebraMap]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `mul y z _ _ hy hz => rw [map_mul]`. Conclude with `mul_mem hy hz`.
-/
theorem galAway_mem (σ : Gal(PadicAlgCl p/K)) {y : 𝔸} (hy : y ∈ ACrisZero ℂ_[p] p) :
    galAway σ y ∈ ACrisZero ℂ_[p] p := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [galAway_dpow]
    exact dpow_mem (gal_smul_mem_ker σ hx) n
  | algebraMap r =>
    rw [galAway_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def galZero (σ : Gal(PadicAlgCl p/K)) : ACrisZero ℂ_[p] p →+* ACrisZero ℂ_[p] p :=
  ((galAway σ).comp (ACrisZero ℂ_[p] p).val.toRingHom).codRestrict (ACrisZero ℂ_[p] p)
    fun y => galAway_mem σ y.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_galZero (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    (galZero σ y : 𝔸) = galAway σ y :=
  rfl

instance instMulSemiringActionGalZero :
    MulSemiringAction Gal(PadicAlgCl p/K) (ACrisZero ℂ_[p] p) where
  smul σ y := galZero σ y
  one_smul y := Subtype.ext (by
    change galAway 1 (y : 𝔸) = y
    rw [galAway_one, RingHom.id_apply])
  mul_smul σ τ y := Subtype.ext (by
    change galAway (σ * τ) (y : 𝔸) = galAway σ (galAway τ y)
    rw [galAway_mul, RingHom.comp_apply])
  smul_zero σ := map_zero (galZero σ)
  smul_add σ := map_add (galZero σ)
  smul_one σ := map_one (galZero σ)
  smul_mul σ := map_mul (galZero σ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gal_smul_zero_def (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    σ • y = galZero σ y :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_gal_smul_zero (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    ((σ • y : ACrisZero ℂ_[p] p) : 𝔸) = galAway σ y :=
  rfl

/- English proof (translation)
The claim follows from `Subtype.ext (galAway_algebraMap σ x)`.
-/
theorem gal_smul_algebraMap_zero (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) x =
      algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) (σ • x) :=
  Subtype.ext (galAway_algebraMap σ x)

/- English proof (translation)
The claim follows from `Subtype.ext (galAway_dpow σ n x)`.
-/
theorem gal_smul_dpow (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ RingHom.ker θ)
    (n : ℕ) :
    σ • (⟨dpow n x, dpow_mem hx n⟩ : ACrisZero ℂ_[p] p) =
      ⟨dpow n (σ • x), dpow_mem (gal_smul_mem_ker σ hx) n⟩ :=
  Subtype.ext (galAway_dpow σ n x)

/- English proof (translation)
The claim follows from `RingHom.ext fun y => one_smul Gal(PadicAlgCl p/K) y`.
-/
theorem galZero_one : galZero (1 : Gal(PadicAlgCl p/K)) = RingHom.id (ACrisZero ℂ_[p] p) :=
  RingHom.ext fun y => one_smul Gal(PadicAlgCl p/K) y

/- English proof (translation)
The claim follows from `RingHom.ext fun y => mul_smul σ τ y`.
-/
theorem galZero_mul (σ τ : Gal(PadicAlgCl p/K)) : galZero (σ * τ) = (galZero σ).comp (galZero τ) :=
  RingHom.ext fun y => mul_smul σ τ y

def galCris (σ : Gal(PadicAlgCl p/K)) : ACris ℂ_[p] p →+* ACris ℂ_[p] p :=
  extendEndo (galZero σ)

/- English proof (translation)
The claim follows from `extendEndo_of _ y`.
-/
theorem galCris_of (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    galCris σ (AdicCompletion.of _ _ y) = AdicCompletion.of _ _ (σ • y) :=
  extendEndo_of _ y

/- English proof (translation)
Rewrite using `[galCris, galZero_one, extendEndo_id]`.
-/
theorem galCris_one : galCris (1 : Gal(PadicAlgCl p/K)) = RingHom.id (ACris ℂ_[p] p) := by
  rw [galCris, galZero_one, extendEndo_id]

/- English proof (translation)
Rewrite using `[galCris, galCris, galCris, galZero_mul, extendEndo_comp]`.
-/
theorem galCris_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galCris (σ * τ) = (galCris σ).comp (galCris τ) := by
  rw [galCris, galCris, galCris, galZero_mul, extendEndo_comp]

instance instMulSemiringActionGal : MulSemiringAction Gal(PadicAlgCl p/K) (ACris ℂ_[p] p) where
  smul σ x := galCris σ x
  one_smul x := by
    change galCris 1 x = x
    rw [galCris_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galCris (σ * τ) x = galCris σ (galCris τ x)
    rw [galCris_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galCris σ)
  smul_add σ := map_add (galCris σ)
  smul_one σ := map_one (galCris σ)
  smul_mul σ := map_mul (galCris σ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gal_smul_def (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) : σ • x = galCris σ x :=
  rfl

/- English proof (translation)
The claim follows from `galCris_of σ y`.
-/
theorem gal_smul_of (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    σ • AdicCompletion.of (Ideal.span {(p : ACrisZero ℂ_[p] p)}) _ y =
      AdicCompletion.of _ _ (σ • y) :=
  galCris_of σ y

/- English proof (translation)
Rewrite using `[AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, gal_smul_of, gal_smul_algebraMap_zero]`.
-/
theorem gal_smul_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) x =
      algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (σ • x) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, gal_smul_of,
    gal_smul_algebraMap_zero]

/- English proof (translation)
Establish `h : (thetaAway ℂ_[p] p).comp (galAway σ) = ((galCp σ : ℂ_[p] ≃+* ℂ_[p]) : ℂ_[p] →+* ℂ_[p]).comp (thetaAway ℂ_[p] p)` using `IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by`. Simplify using `only [RingHom.comp_apply, galAway_algebraMap, thetaAway_algebraMap, RingEquiv.coe_toRingHom, galCp_apply]`. Conclude with `AInf.fontaineTheta_gal_smul σ x)`. Conclude with `congrFun (congrArg DFunLike.coe h) y`.
-/
theorem thetaAway_galAway (σ : Gal(PadicAlgCl p/K)) (y : 𝔸) :
    thetaAway ℂ_[p] p (galAway σ y) = σ • thetaAway ℂ_[p] p y := by
  have h : (thetaAway ℂ_[p] p).comp (galAway σ) =
      ((galCp σ : ℂ_[p] ≃+* ℂ_[p]) : ℂ_[p] →+* ℂ_[p]).comp (thetaAway ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, galAway_algebraMap, thetaAway_algebraMap, RingEquiv.coe_toRingHom,
        galCp_apply]
      exact AInf.fontaineTheta_gal_smul σ x)
  exact congrFun (congrArg DFunLike.coe h) y

/- English proof (translation)
Rewrite using `[coe_thetaZero, coe_thetaZero, coe_gal_smul_zero, thetaAway_galAway]`.
-/
theorem thetaZero_gal_smul (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    ((thetaZero ℂ_[p] p (σ • y) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((thetaZero ℂ_[p] p y : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [coe_thetaZero, coe_thetaZero, coe_gal_smul_zero, thetaAway_galAway]

/- English proof (translation)
Establish `h : (theta ℂ_[p] p).comp (galCris σ) = (integerMap (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)).comp (theta ℂ_[p] p)` using `ringHom_ext fun y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, galCris_of, theta_of, theta_of, coe_integerMap, thetaZero_gal_smul]`. Both sides reduce to the same expression. Establish `h'` using `congrArg (fun f => ((f x : normInteger ℂ_[p]) : ℂ_[p])) h`.

Simplify using `only [RingHom.comp_apply, coe_integerMap] at h'`. Conclude with `h'`.
-/
theorem theta_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    ((theta ℂ_[p] p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((theta ℂ_[p] p x : normInteger ℂ_[p]) : ℂ_[p]) := by
  have h : (theta ℂ_[p] p).comp (galCris σ) =
      (integerMap (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)).comp
        (theta ℂ_[p] p) :=
    ringHom_ext fun y => by
      apply Subtype.ext
      rw [RingHom.comp_apply, RingHom.comp_apply, galCris_of, theta_of, theta_of,
        coe_integerMap, thetaZero_gal_smul]
      rfl
  have h' := congrArg (fun f => ((f x : normInteger ℂ_[p]) : ℂ_[p])) h
  simp only [RingHom.comp_apply, coe_integerMap] at h'
  exact h'

/- English proof (translation)
Establish `h : (phiAway ℂ_[p] p).comp (galAway σ) = (galAway σ).comp (phiAway ℂ_[p] p)` using `IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by`. Simplify using `only [RingHom.comp_apply, galAway_algebraMap, phiAway_algebraMap, AInf.gal_smul_frobeniusEquiv])`. Conclude with `congrFun (congrArg DFunLike.coe h) y`.
-/
theorem phiAway_galAway (σ : Gal(PadicAlgCl p/K)) (y : 𝔸) :
    phiAway ℂ_[p] p (galAway σ y) = galAway σ (phiAway ℂ_[p] p y) := by
  have h : (phiAway ℂ_[p] p).comp (galAway σ) = (galAway σ).comp (phiAway ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, galAway_algebraMap, phiAway_algebraMap,
        AInf.gal_smul_frobeniusEquiv])
  exact congrFun (congrArg DFunLike.coe h) y

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [coe_phiZero, coe_gal_smul_zero, coe_gal_smul_zero, coe_phiZero, phiAway_galAway])`.
-/
theorem phiZero_gal_smul (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    phiZero ℂ_[p] p (σ • y) = σ • phiZero ℂ_[p] p y :=
  Subtype.ext (by
    rw [coe_phiZero, coe_gal_smul_zero, coe_gal_smul_zero, coe_phiZero, phiAway_galAway])

/- English proof (translation)
Establish `h0 : (phiZero ℂ_[p] p).comp (galZero σ) = (galZero σ).comp (phiZero ℂ_[p] p)` using `RingHom.ext fun y => phiZero_gal_smul σ y`. Establish `h : (phi ℂ_[p] p).comp (galCris σ) = (galCris σ).comp (phi ℂ_[p] p)`. Rewrite using `[phi_eq_extendEndo, galCris, extendEndo_comp, extendEndo_comp, h0]`. Conclude with `congrFun (congrArg DFunLike.coe h) x`.
-/
theorem phi_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    phi ℂ_[p] p (σ • x) = σ • phi ℂ_[p] p x := by
  have h0 : (phiZero ℂ_[p] p).comp (galZero σ) = (galZero σ).comp (phiZero ℂ_[p] p) :=
    RingHom.ext fun y => phiZero_gal_smul σ y
  have h : (phi ℂ_[p] p).comp (galCris σ) = (galCris σ).comp (phi ℂ_[p] p) := by
    rw [phi_eq_extendEndo, galCris, extendEndo_comp, extendEndo_comp, h0]
  exact congrFun (congrArg DFunLike.coe h) x

end Galois

end ACris

end GroundTheory.PAdicHodge
