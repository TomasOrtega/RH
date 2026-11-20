import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero

open Set Filter Polynomial NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.TrEll.Hasse

abbrev Ten {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r) (k : Type) [CommRing k]
    [Algebra F k] : Type := k ⊗[F] Fld P

section Bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (P : PPol (IsCMField.complexConj E).toAlgHom r)

def toSR : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, by rw [coeff_zero_eq_eval_zero]; exact P.2.2.2.2.1, by
    have h := P.2.2.2.2.2
    rw [sharp, ← coeff_zero_eq_eval_zero] at h
    exact h⟩

variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

def incl : k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P) →+* Ten P k :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.inclPlus (toSR P) k).toRingHom

/- English proof (translation)
The claim follows from `Module.Flat.lTensor_preserves_injective_linearMap (M := k) (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P)).val.toLinearMap Subtype.val_injective`.
-/
theorem incl_injective : Function.Injective (incl P k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P)).val.toLinearMap
    Subtype.val_injective

/- English proof (translation)
The claim follows from `GlobalTheory.TraceClasses.involBase_inclPlus (toSR P) k a`.
-/
theorem sigR_incl (a) : sigR k (star' P) (incl P k a) = incl P k a :=
  GlobalTheory.TraceClasses.involBase_inclPlus (toSR P) k a

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul s y`. Use `⟨s ⊗ₜ ⟨y + star' P y, ?_⟩, TensorProduct.tmul_add _ _ _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star' P (y + star' P y) = y + star' P y`.

Establish `: star' P (star' P y) = y` using `GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_invol (toSR P) y`. Rewrite using `[map_add, this, add_comm]`. Consider the case `add y z hy hz`. Take `⟨a, ha⟩` from `hy`. Take `⟨b, hb⟩` from `hz`.

Conclude with `⟨a + b, by rw [map_add, map_add, ha, hb]; ring⟩`.
-/
theorem exists_incl_eq_add (z : Ten P k) : ∃ a, incl P k a = z + sigR k (star' P) z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨y + star' P y, ?_⟩, TensorProduct.tmul_add _ _ _⟩
    change star' P (y + star' P y) = y + star' P y
    have : star' P (star' P y) = y := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_invol (toSR P) y
    rw [map_add, this, add_comm]
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]; ring⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_incl_eq_add P k ((2⁻¹ : maximalRealSubfield E) • z)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `: sigR k (star' P) ((2⁻¹ : maximalRealSubfield E) • z) = (2⁻¹ : maximalRealSubfield E) • sigR k (star' P) z` using `map_smul (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k) (star' P)) _ _`. Rewrite using `[ha, this, hz, ← add_smul]`. Evaluate the numerical expressions.
-/
theorem exists_incl_eq {z : Ten P k} (hz : sigR k (star' P) z = z) : ∃ a, incl P k a = z := by
  obtain ⟨a, ha⟩ := exists_incl_eq_add P k ((2⁻¹ : maximalRealSubfield E) • z)
  refine ⟨a, ?_⟩
  have : sigR k (star' P) ((2⁻¹ : maximalRealSubfield E) • z) = (2⁻¹ : maximalRealSubfield E) • sigR k (star' P) z :=
    map_smul (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k) (star' P)) _ _
  rw [ha, this, hz, ← add_smul]
  norm_num

def unitMap : (k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P))ˣ →* plusUnits P k :=
  (Units.map (incl P k).toMonoidHom).codRestrict _ fun a => Units.ext (sigR_incl P k a)

/- English proof (translation)
Introduce `x`. Take `⟨a, ha⟩` from `exists_incl_eq P k (z := x.1.1) (congrArg Units.val x.2)`. Take `⟨b, hb⟩` from `exists_incl_eq P k (z := (x⁻¹).1.1) (congrArg Units.val (x⁻¹).2)`. Establish `h : a * b = 1` using `incl_injective P k (by rw [map_mul, ha, hb, map_one]; exact x.1.mul_inv)`. Conclude with `⟨Units.mkOfMulEqOne a b h, Subtype.ext (Units.ext ha)⟩`.
-/
theorem unitMap_surjective : Function.Surjective (unitMap P k) := by
  intro x
  obtain ⟨a, ha⟩ := exists_incl_eq P k (z := x.1.1) (congrArg Units.val x.2)
  obtain ⟨b, hb⟩ := exists_incl_eq P k (z := (x⁻¹).1.1) (congrArg Units.val (x⁻¹).2)
  have h : a * b = 1 := incl_injective P k (by rw [map_mul, ha, hb, map_one]; exact x.1.mul_inv)
  exact ⟨Units.mkOfMulEqOne a b h, Subtype.ext (Units.ext ha)⟩

/- English proof (translation)
Rewrite using `[QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem mk_unitMap_eq_iff (a b) : (QuotientGroup.mk (unitMap P k a) : Cls P k) = QuotientGroup.mk (unitMap P k b) ↔
    (QuotientGroup.mk a : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
  rfl

def clsMap : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k →* Cls P k :=
  QuotientGroup.map _ _ (unitMap P k) fun _ h => h

/- English proof (translation)
Introduce `q q' h`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective q'`. Conclude with `(mk_unitMap_eq_iff P k a b).1 h`.
-/
theorem clsMap_injective : Function.Injective (clsMap P k) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  exact (mk_unitMap_eq_iff P k a b).1 h

/- English proof (translation)
Introduce `q`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨a, rfl⟩` from `unitMap_surjective P k x`. Conclude with `⟨QuotientGroup.mk a, rfl⟩`.
-/
theorem clsMap_surjective : Function.Surjective (clsMap P k) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, rfl⟩ := unitMap_surjective P k x
  exact ⟨QuotientGroup.mk a, rfl⟩

/- English proof (translation)
Rewrite using `[Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.HermLocal.ccBase E k (u' j) * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * u i = u i * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * GlobalTheory.HermLocal.ccBase E k (u' j)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_eq (J : Matrix (Fin r) (Fin r) E) (u u' : Fin r → k ⊗[maximalRealSubfield E] E) :
    Formalism.UG.hform (sigR k (IsCMField.complexConj E).toAlgHom) (JR k J) u' u = GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm k Jᵀ u u' := by
  rw [Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change GlobalTheory.HermLocal.ccBase E k (u' j) * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * u i =
    u i * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * GlobalTheory.HermLocal.ccBase E k (u' j)
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, h⟩`. Conclude with `⟨φ.toAddEquiv, fun e y => φ.map_smul e y, fun y y' => (hform_eq k J _ _).symm.trans (h y y')⟩`. Introduce and unpack `⟨φ, h1, h2⟩`. Conclude with `⟨{ φ with map_smul' := h1 }, fun y y' => (hform_eq k J _ _).trans (h2 y y')⟩`.
-/
theorem isometric_iff (J : Matrix (Fin r) (Fin r) E) (a) :
    (∃ φ, IsIsom P k J (incl P k a) φ) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric (toSR P) k Jᵀ a := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨φ.toAddEquiv, fun e y => φ.map_smul e y, fun y y' => (hform_eq k J _ _).symm.trans (h y y')⟩
  · rintro ⟨φ, h1, h2⟩
    exact ⟨{ φ with map_smul' := h1 }, fun y y' => (hform_eq k J _ _).trans (h2 y y')⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, φ, e, h⟩`. Take `⟨a, rfl⟩` from `unitMap_surjective P k x`. Conclude with `⟨a, clsMap_injective P k e, (isometric_iff P k J a.1).1 ⟨φ, h⟩⟩`. Introduce and unpack `⟨a, rfl, h⟩`.

Take `⟨φ, h⟩` from `(isometric_iff P k J a.1).2 h`. Conclude with `⟨unitMap P k a, φ, rfl, h⟩`.
-/
theorem clsMap_mem_iff (J : Matrix (Fin r) (Fin r) E) (q) :
    clsMap P k q ∈ XSet P k J ↔ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.classes (toSR P) k Jᵀ := by
  constructor
  · rintro ⟨x, φ, e, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P k x
    exact ⟨a, clsMap_injective P k e, (isometric_iff P k J a.1).1 ⟨φ, h⟩⟩
  · rintro ⟨a, rfl, h⟩
    obtain ⟨φ, h⟩ := (isometric_iff P k J a.1).2 h
    exact ⟨unitMap P k a, φ, rfl, h⟩

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero]`. Conclude with `(map_zero _).symm`. Consider the case `tmul a b => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb]`.

Conclude with `(map_add _ _ _).symm`.
-/
theorem incl_toLocalPlus (a) : incl P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k a) =
    Algebra.TensorProduct.map (Algebra.ofId (maximalRealSubfield E) k) (AlgHom.id _ (Fld P))
      (incl P (maximalRealSubfield E) a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (map_zero _).symm
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]; exact (map_add _ _ _).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, x', e, rfl, h⟩`. Take `⟨a, rfl⟩` from `unitMap_surjective P _ x`. Take `rfl : QuotientGroup.mk a = q` from `clsMap_injective P _ e`. Use `congrArg QuotientGroup.mk (Subtype.ext (Units.ext ?_))` and prove the remaining obligations.

Conclude with `h.trans (incl_toLocalPlus P k a.1).symm`. Introduce and unpack `rfl`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `⟨unitMap P _ a, unitMap P k (Units.map (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k).toMonoidHom a), rfl, rfl, incl_toLocalPlus P k a.1⟩`.
-/
theorem mapsCls_iff (q) (c : Cls P k) :
    MapsCls P (k := maximalRealSubfield E) (Algebra.ofId (maximalRealSubfield E) k) (clsMap P _ q) c ↔
      c = clsMap P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocal (toSR P) k q) := by
  constructor
  · rintro ⟨x, x', e, rfl, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P _ x
    obtain rfl : QuotientGroup.mk a = q := clsMap_injective P _ e
    refine congrArg QuotientGroup.mk (Subtype.ext (Units.ext ?_))
    exact h.trans (incl_toLocalPlus P k a.1).symm
  · rintro rfl
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨unitMap P _ a, unitMap P k (Units.map (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k).toMonoidHom a), rfl, rfl,
      incl_toLocalPlus P k a.1⟩

end Bridge

/- English proof (translation)
Introduce `E _ _ F _ σ hcm hur r P J hJ`. Take `⟨h1, h2, h3, h4⟩` from `hcm`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h3⟩`. Use `haveI : IsCMField E := IsCMField.ofCMExtension F E`. Take `rfl : F = maximalRealSubfield E` from `CMExtension.eq_maximalRealSubfield E F`.

Choose the witnesses or unpack the hypotheses as in `rfl : σ = (IsCMField.complexConj E).toAlgHom := by`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `AlgHom.ext fun x => φ.injective ((h4 φ x).trans (IsCMField.complexEmbedding_complexConj E φ x).symm)`. Establish `H` using `GlobalTheory.TraceClasses.rationalEqAdelic E hur r Jᵀ (fun a b => hJ.1 a b) (by rw [Matrix.det_transpose]; exact hJ.2) (toSR P)`. Prove the components needed by the constructor for the conclusion.

Introduce `q q' hq hq' hf ha`. Take `⟨q, rfl⟩` from `clsMap_surjective P _ q`. Take `⟨q', rfl⟩` from `clsMap_surjective P _ q'`. Use `congrArg _ (H.injOn ((clsMap_mem_iff P _ J q).1 hq) ((clsMap_mem_iff P _ J q').1 hq') (Prod.ext (funext fun v => ?_) (funext fun w => ?_)))` and prove the remaining obligations. Take `⟨a, e, e'⟩` from `hf v`.

Conclude with `clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))`. Take `⟨a, e, e'⟩` from `ha w`. Conclude with `clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))`. Introduce `qf qa hf ha h1 choose xf hxf using fun v => clsMap_surjective P _ (qf v) choose xa hxa using fun w => clsMap_surjective P _ (qa w)`. Take `⟨q, hq, e⟩` from `H.surjOn (show (xf, xa) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.adelicClasses (toSR P) Jᵀ from ⟨fun v => (clsMap_mem_iff P _ J _).1 (by rw [hxf]; exact hf v), fun w => (clsMap_mem_iff P _ J _).1 (by rw [hxa]; exact ha w), by`.

Use `(Filter.eventually_cofinite.1 h1).subset fun v hv hv1 => hv ?_` and prove the remaining obligations. Establish `: xf v = 1` using `clsMap_injective P _ (by rw [hxf, hv1, map_one])`. Conclude with `⟨1, RingHom.isIntegralElem_one _, RingHom.isIntegralElem_one _, this.symm⟩⟩)`. Use `⟨clsMap P _ q, (clsMap_mem_iff P _ J q).2 hq, fun v => (mapsCls_iff P _ q _).2 ?_, fun w => (mapsCls_iff P _ q _).2 ?_⟩` and prove the remaining obligations. Conclude with `(hxf v).symm.trans (congrArg _ (congrFun (congrArg Prod.fst e) v).symm)`.

Conclude with `(hxa w).symm.trans (congrArg _ (congrFun (congrArg Prod.snd e) w).symm)`.
-/
theorem rational_eq_local : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  intro E _ _ F _ σ hcm hur r P J hJ
  obtain ⟨h1, h2, h3, h4⟩ := hcm
  haveI : Algebra.IsQuadraticExtension F E := ⟨h3⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  obtain rfl : F = maximalRealSubfield E := CMExtension.eq_maximalRealSubfield E F
  obtain rfl : σ = (IsCMField.complexConj E).toAlgHom := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact AlgHom.ext fun x => φ.injective ((h4 φ x).trans (IsCMField.complexEmbedding_complexConj E φ x).symm)
  have H := GlobalTheory.TraceClasses.rationalEqAdelic E hur r Jᵀ (fun a b => hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) (toSR P)
  constructor
  · intro q q' hq hq' hf ha
    obtain ⟨q, rfl⟩ := clsMap_surjective P _ q
    obtain ⟨q', rfl⟩ := clsMap_surjective P _ q'
    refine congrArg _ (H.injOn ((clsMap_mem_iff P _ J q).1 hq) ((clsMap_mem_iff P _ J q').1 hq')
      (Prod.ext (funext fun v => ?_) (funext fun w => ?_)))
    · obtain ⟨a, e, e'⟩ := hf v
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
    · obtain ⟨a, e, e'⟩ := ha w
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
  · intro qf qa hf ha h1
    choose xf hxf using fun v => clsMap_surjective P _ (qf v)
    choose xa hxa using fun w => clsMap_surjective P _ (qa w)
    obtain ⟨q, hq, e⟩ := H.surjOn (show (xf, xa) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.adelicClasses (toSR P) Jᵀ from
      ⟨fun v => (clsMap_mem_iff P _ J _).1 (by rw [hxf]; exact hf v),
        fun w => (clsMap_mem_iff P _ J _).1 (by rw [hxa]; exact ha w), by
        refine (Filter.eventually_cofinite.1 h1).subset fun v hv hv1 => hv ?_
        have : xf v = 1 := clsMap_injective P _ (by rw [hxf, hv1, map_one])
        exact ⟨1, RingHom.isIntegralElem_one _, RingHom.isIntegralElem_one _, this.symm⟩⟩)
    refine ⟨clsMap P _ q, (clsMap_mem_iff P _ J q).2 hq, fun v => (mapsCls_iff P _ q _).2 ?_,
      fun w => (mapsCls_iff P _ q _).2 ?_⟩
    · exact (hxf v).symm.trans (congrArg _ (congrFun (congrArg Prod.fst e) v).symm)
    · exact (hxa w).symm.trans (congrArg _ (congrFun (congrArg Prod.snd e) w).symm)

end GlobalTheory.TrEll.Hasse
