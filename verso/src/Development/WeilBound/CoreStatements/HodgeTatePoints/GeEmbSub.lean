import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariantStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Ge.EmbSub
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

section alg

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

open Classical in

noncomputable def ind (H : Subgroup T) : T → R := fun x => if x ∈ H then 1 else 0

open Classical in

noncomputable def extZero (H : Subgroup T) (a : H → R) : T → R := fun x => if h : x ∈ H then a ⟨x, h⟩ else 0

/- English proof (translation)
Use `(hB _).2 fun t => ?_` and prove the remaining obligations. Distinguish the cases in `h : c * t ∈ H`. Establish `: (fun x : H => ind (R` using `R) H (c * (t * x))) = 1 := by`. Use function extensionality and compare the values at `x`. Establish `: c * (t * x) ∈ H`.

Rewrite using `[← _root_.mul_assoc]`. Conclude with `H.mul_mem h x.2`. Simplify using `[ind, this]`. Rewrite using `[this]`. Conclude with `A.one_mem`.

Establish `: (fun x : H => ind (R` using `R) H (c * (t * x))) = 0 := by`. Use function extensionality and compare the values at `x`. Establish `: c * (t * x) ∉ H`. Rewrite using `[← _root_.mul_assoc]`. Conclude with `fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))`.

Simplify using `[ind, this]`. Rewrite using `[this]`. Conclude with `A.zero_mem`.
-/
theorem ind_translate_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A) (c : T) :
    (fun x => ind (R := R) H (c * x)) ∈ B := by
  refine (hB _).2 fun t => ?_
  by_cases h : c * t ∈ H
  · have : (fun x : H => ind (R := R) H (c * (t * x))) = 1 := by
      funext x
      have : c * (t * x) ∈ H := by
        rw [← _root_.mul_assoc]
        exact H.mul_mem h x.2
      simp [ind, this]
    rw [this]
    exact A.one_mem
  · have : (fun x : H => ind (R := R) H (c * (t * x))) = 0 := by
      funext x
      have : c * (t * x) ∉ H := by
        rw [← _root_.mul_assoc]
        exact fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))
      simp [ind, this]
    rw [this]
    exact A.zero_mem

/- English proof (translation)
Use `(hB _).2 fun t => ?_` and prove the remaining obligations. Distinguish the cases in `h : t ∈ H`. Establish `: (fun x : H => extZero H a (t * x)) = fun x => a (⟨t, h⟩ * x)`. Use function extensionality and compare the values at `x`. Establish `h' : t * x ∈ H` using `H.mul_mem h x.2`.

Simplify using `only [extZero, dif_pos h']`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hA a ha _`. Establish `: (fun x : H => extZero H a (t * x)) = 0`.

Use function extensionality and compare the values at `x`. Establish `h' : t * x ∉ H` using `fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))`. Simplify using `[extZero, h']`. Rewrite using `[this]`. Conclude with `A.zero_mem`.
-/
theorem extZero_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A)
    (hA : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A) {a : H → R} (ha : a ∈ A) : extZero H a ∈ B := by
  refine (hB _).2 fun t => ?_
  by_cases h : t ∈ H
  · have : (fun x : H => extZero H a (t * x)) = fun x => a (⟨t, h⟩ * x) := by
      funext x
      have h' : t * x ∈ H := H.mul_mem h x.2
      simp only [extZero, dif_pos h']
      rfl
    rw [this]
    exact hA a ha _
  · have : (fun x : H => extZero H a (t * x)) = 0 := by
      funext x
      have h' : t * x ∉ H := fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))
      simp [extZero, h']
    rw [this]
    exact A.zero_mem

/- English proof (translation)
Use `(hB _).2 fun t => ?_` and prove the remaining obligations. Simplify `(hB f).1 hf (c * t)` using `only [_root_.mul_assoc]`.
-/
theorem translate_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A) {f : T → R} (hf : f ∈ B) (c : T) :
    (fun x => f (c * x)) ∈ B := by
  refine (hB _).2 fun t => ?_
  simpa only [_root_.mul_assoc] using (hB f).1 hf (c * t)

def transl {B : Subalgebra R (T → R)} (hB : ∀ f ∈ B, ∀ c : T, (fun x => f (c * x)) ∈ B) (c : T) : B →+* B where
  toFun f := ⟨fun x => (f : T → R) (c * x), hB _ f.2 c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Use `Fintype.ofFinite T` as an intermediate fact. Establish `h0 : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Establish `hx : ((∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B)) : B) : T → R) x = ∏ t : T, (1 - ind (R` using `R) H (t⁻¹ * x)) := by`.

Rewrite using `[← Subalgebra.coe_val, map_prod, Finset.prod_apply]`. Both sides reduce to the same expression. Rewrite using `[hx]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ x) (by simp [ind, H.one_mem])`. Establish `hP : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) ∈ P` using `h0 ▸ P.zero_mem`.

Take `⟨t, -, ht⟩` from `(Ideal.IsPrime.prod_mem_iff (p := P)).1 hP`. Use `⟨t, fun h => ?_⟩` and prove the remaining obligations. Establish `: (1 : B) ∈ P`. Use `P.add_mem ht h` as an intermediate fact. Simplify using `using this`.

Conclude with `(Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›) this`.
-/
theorem exists_translate_notMem [Finite T] {H : Subgroup T} {B : Subalgebra R (T → R)}
    (he : ∀ c : T, (fun x => ind (R := R) H (c * x)) ∈ B) (P : Ideal B) [P.IsPrime] :
    ∃ t : T, (⟨_, he t⁻¹⟩ : B) ∉ P := by
  classical
  have := Fintype.ofFinite T
  have h0 : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) = 0 := by
    apply Subtype.ext
    funext x
    have hx : ((∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B)) : B) : T → R) x
        = ∏ t : T, (1 - ind (R := R) H (t⁻¹ * x)) := by
      rw [← Subalgebra.coe_val, map_prod, Finset.prod_apply]
      rfl
    rw [hx]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [ind, H.one_mem])
  have hP : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) ∈ P := h0 ▸ P.zero_mem
  obtain ⟨t, -, ht⟩ := (Ideal.IsPrime.prod_mem_iff (p := P)).1 hP
  refine ⟨t, fun h => ?_⟩
  have : (1 : B) ∈ P := by
    have := P.add_mem ht h
    simpa using this
  exact (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›) this

end alg

section geom

/- English proof (translation)
Use `hF.finite` as an intermediate fact. Establish `: IsAffineHom (U.ι ≫ Γ.G.hom)` using `inferInstance`. Conclude with `isAffine_of_isAffineHom (U.ι ≫ Γ.G.hom)`.
-/
theorem isAffineOpen_of_fin {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
    {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U) : IsAffineOpen U := by
  have := hF.finite
  have : IsAffineHom (U.ι ≫ Γ.G.hom) := inferInstance
  exact isAffine_of_isAffineHom (U.ι ≫ Γ.G.hom)

noncomputable def valRing {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valRing_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valRing x U h s = valAt x U h s := rfl

/- English proof (translation)
Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h`. Rewrite `e` using `[IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]`. Establish `: CommRingCat.ofHom (valRing x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom` using `rfl`. Rewrite using `[this, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp]`. Simplify using the standard rewrite rules.
-/
theorem spec_valRing_fromSpec {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (valRing x U h)) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : CommRingCat.ofHom (valRing x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom := rfl
  rw [this, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp]
  simp

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`. Conclude with `⟨z, rfl⟩`.
-/
theorem fromSpec_mem' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (z) : hU.fromSpec z ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨z, rfl⟩

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

/- English proof (translation)
Establish `e1` using `spec_valRing_fromSpec (Γ.pt t).left hU h`. Establish `e2` using `hj.pt t`. Rewrite `e2` using `[← e1, Category.assoc, ← hψ, ← Spec.map_comp]`. Use `congrArg (fun g => g.hom f) (Spec.map_injective e2)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this`.

Conclude with `this`.
-/
theorem val_pullback (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hU : IsAffineOpen U) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (ψ : CommRingCat.of A ⟶ Γ(Γ.G.left, U))
    (hψ : Spec.map ψ = hU.fromSpec ≫ j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (f : A) :
    valAt (Γ.pt t).left U h (ψ.hom f) = algebraMap R (FractionRing R) ((f : T → R) t) := by
  have e1 := spec_valRing_fromSpec (Γ.pt t).left hU h
  have e2 := hj.pt t
  rw [← e1, Category.assoc, ← hψ, ← Spec.map_comp] at e2
  have := congrArg (fun g => g.hom f) (Spec.map_injective e2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

/- English proof (translation)
Set `ρ : R →+* Γ(Γ.G.left, U)` to `ψ.hom.comp (algebraMap R A)`. Use `letI : Algebra R Γ(Γ.G.left, U) := ρ.toAlgebra`. Establish `hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U)))`. Establish `e : CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U)) = CommRingCat.ofHom (algebraMap R A) ≫ ψ` using `rfl`. Rewrite using `[e, Spec.map_comp, hψ, Category.assoc, hj.isOver]`.

Use `hF.finite` as an intermediate fact. Establish `hfin : IsFinite (hU.fromSpec ≫ Γ.G.hom)`. Rewrite using `[← hU.isoSpec_inv_ι, Category.assoc]`. Use `infer_instance`. Rewrite `hfin` using `[hρ]`.

Establish `hfin' : Module.Finite R Γ(Γ.G.left, U)` using `RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 hfin)`. Establish `h1 : IsIntegral R s` using `Algebra.IsIntegral.isIntegral s`. Establish `h2 : (algebraMap R (FractionRing R)).comp (RingHom.id R) = (valRing (Γ.pt t).left U h).comp (algebraMap R Γ(Γ.G.left, U))`. Use extensionality with `r`. Use `val_pullback Γ hU hj ψ hψ t h (algebraMap R A r)` as an intermediate fact.

Conclude with `this.symm`. Establish `h3 : IsIntegral R (valRing (Γ.pt t).left U h s)` using `h1.map_of_comp_eq _ _ h2`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 h3`.
-/
theorem val_mem_range [IsIntegrallyClosed R] (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U)
    (hU : IsAffineOpen U) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (ψ : CommRingCat.of A ⟶ Γ(Γ.G.left, U))
    (hψ : Spec.map ψ = hU.fromSpec ≫ j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (s : Γ(Γ.G.left, U)) :
    ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left U h s := by
  let ρ : R →+* Γ(Γ.G.left, U) := ψ.hom.comp (algebraMap R A)
  letI : Algebra R Γ(Γ.G.left, U) := ρ.toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) := by
    have e : CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U)) = CommRingCat.ofHom (algebraMap R A) ≫ ψ := rfl
    rw [e, Spec.map_comp, hψ, Category.assoc, hj.isOver]
  have := hF.finite
  have hfin : IsFinite (hU.fromSpec ≫ Γ.G.hom) := by
    rw [← hU.isoSpec_inv_ι, Category.assoc]
    infer_instance
  rw [hρ] at hfin
  have hfin' : Module.Finite R Γ(Γ.G.left, U) := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 hfin)
  have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
  have h2 : (algebraMap R (FractionRing R)).comp (RingHom.id R) =
      (valRing (Γ.pt t).left U h).comp (algebraMap R Γ(Γ.G.left, U)) := by
    ext r
    have := val_pullback Γ hU hj ψ hψ t h (algebraMap R A r)
    exact this.symm
  have h3 : IsIntegral R (valRing (Γ.pt t).left U h s) := h1.map_of_comp_eq _ _ h2
  exact IsIntegrallyClosed.isIntegral_iff.1 h3

end geom

end PositivityTheory.HtPt.Ge.EmbSub

namespace PositivityTheory.HtPt.Ge.EmbSub
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `R _ _ _ T _ _ Γ U hF j hj`. Take `⟨H, A, hH, hA, hAs⟩` from `GlobalTheory.T.finite_open_hopf_order R T Γ U hF`. Establish `hU` using `isAffineOpen_of_fin Γ hF`. Establish `hTr : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A` using `GlobalTheory.T.hopf_order_translation_invariant R H A hA`. Establish `hB : ∀ f : T → R, f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h : H => f (t * h)) ∈ A`.

Introduce `f`. Rewrite using `[← Htat.bt_sub_eq_top R T Γ U hF, GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]`. Prove the components needed by the constructor for the conclusion. Introduce `hf t`. Take `⟨s, hs⟩` from `(GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)`.

Conclude with `(hAs _).2 ⟨s, fun x h => hs x h⟩`. Introduce `hf t`. Take `⟨s, hs⟩` from `(hAs _).1 (hf t)`. Conclude with `(GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ⟨s, fun x h => hs ⟨x, (hH x).2 h⟩ h⟩`. Set `ψ : CommRingCat.of (Γ.btOrder ⊤) ⟶ Γ(Γ.G.left, U)` to `Spec.preimage (hU.fromSpec ≫ j)`.

Establish `hψ : Spec.map ψ = hU.fromSpec ≫ j` using `Spec.map_preimage _`. Establish `hv` using `val_pullback Γ hU hj ψ hψ`. Establish `hi` using `val_mem_range Γ hF hU hj ψ hψ`. Establish `inj : Function.Injective (algebraMap R (FractionRing R))` using `IsFractionRing.injective R _`. Establish `hsurj : Function.Surjective ψ.hom`.

Introduce `s`. Use `choose a ha using fun t : H => hi t ((hH t).1 t.2) s`. Establish `haA : a ∈ A` using `(hAs a).2 ⟨s, fun t h => (ha t).symm⟩`. Use `⟨⟨extZero H a, extZero_mem hB hTr haA⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_` and prove the remaining obligations. Establish `ht : t ∈ H` using `(hH t).2 h`. Rewrite using `[← valRing_apply, map_sub, valRing_apply, valRing_apply, hv t h, ← ha ⟨t, ht⟩]`. Simplify using `[extZero, ht]`. Establish `hz : ∀ f : Γ.btOrder ⊤, ψ.hom f = 0 ↔ ∀ t ∈ H, (f : T → R) t = 0`.

Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce `hf t ht`. Use `hv t ((hH t).1 ht) f` as an intermediate fact. Rewrite `this` using `[hf, ← valRing_apply, map_zero]`.

Conclude with `inj (by rw [← this, map_zero])`. Introduce `hf`. Use `GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_` and prove the remaining obligations. Rewrite using `[hv t h, hf t ((hH t).2 h), map_zero]`. Set `e : Γ.btOrder ⊤` to `⟨_, ind_translate_mem hB 1⟩`.

Establish `he1 : ∀ x ∈ H, (e : T → R) x = 1` using `fun x hx => by simp [e, ind, hx]`. Establish `he0 : ∀ x, x ∉ H → (e : T → R) x = 0` using `fun x hx => by simp [e, ind, hx]`. Establish `hidem : IsIdempotentElem e`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Express the relevant statement in the definitionally equal form `(e : T → R) x * (e : T → R) x = (e : T → R) x`. Distinguish the cases in `hx : x ∈ H`. Simplify using `[he1 x hx]`. Simplify using `[he0 x hx]`. Establish `hker : RingHom.ker ψ.hom = Ideal.span {1 - e}`.

Use extensionality with `f`. Rewrite using `[RingHom.mem_ker, Ideal.mem_span_singleton', hz]`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Use `⟨f, Subtype.ext (funext fun x => ?_)⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(f : T → R) x * (1 - (e : T → R) x) = (f : T → R) x`. Distinguish the cases in `hx : x ∈ H`. Simplify using `[hf x hx]`. Simplify using `[he0 x hx]`. Introduce and unpack `⟨b, rfl⟩ t ht`.

Express the relevant statement in the definitionally equal form `(b : T → R) t * (1 - (e : T → R) t) = 0`. Simplify using `[he1 t ht]`. Establish `hoi : IsOpenImmersion (Spec.map ψ)` using `(isOpenImmersion_SpecMap_iff_of_surjective ψ hsurj).2 ⟨1 - e, hidem.one_sub, hker⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: U.ι ≫ j = hU.isoSpec.hom ≫ Spec.map ψ`.

Rewrite using `[hψ, ← hU.isoSpec_inv_ι]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `infer_instance`. Introduce `P`.

Establish `hBt : ∀ f ∈ Γ.btOrder ⊤, ∀ c : T, (fun x => f (c * x)) ∈ Γ.btOrder ⊤` using `fun f hf c => translate_mem hB hf c`. Take `⟨t, ht⟩` from `exists_translate_notMem (B := Γ.btOrder ⊤) (H := H) (ind_translate_mem hB) P.asIdeal`. Set `Q : Ideal (Γ.btOrder ⊤)` to `P.asIdeal.comap (transl hBt t⁻¹)`. Establish `hQ : Q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `heQ : e ∉ Q`.

Introduce `h`. Apply `ht` to reduce the goal to its premises. Establish `: transl hBt t⁻¹ e = ⟨_, ind_translate_mem hB t⁻¹⟩` using `Subtype.ext (funext fun x => by simp [transl, e])`. Rewrite using `[← this]`. Conclude with `h`.

Establish `h1e : 1 - e ∈ Q`. Establish `h0 : e * (1 - e) ∈ Q`. Rewrite using `[mul_sub, _root_.mul_one, hidem.eq, sub_self]`. Conclude with `Q.zero_mem`. Conclude with `(hQ.mem_or_mem h0).resolve_left heQ`.

Establish `hk : RingHom.ker ψ.hom ≤ Q`. Rewrite using `[hker, Ideal.span_singleton_le_iff_mem]`. Conclude with `h1e`. Choose the witnesses or unpack the hypotheses as in `⟨Q', hQ'⟩ : (⟨Q, hQ⟩ : PrimeSpectrum (Γ.btOrder ⊤)) ∈ Set.range (PrimeSpectrum.comap ψ.hom) := by`. Rewrite using `[range_comap_of_surjective _ _ hsurj]`.

Conclude with `hk`. Use `⟨t, hU.fromSpec Q', fromSpec_mem' hU _, fun f f' hff => ?_⟩` and prove the remaining obligations. Establish `hjg : (j (hU.fromSpec Q')).asIdeal = Q`. Establish `h1 : j (hU.fromSpec Q') = (Spec.map ψ) Q'`. Rewrite using `[hψ]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `congrArg PrimeSpectrum.asIdeal hQ'`. Rewrite using `[hjg]`. Establish `h2 : transl hBt t⁻¹ f' = f` using `Subtype.ext (funext fun x => by`.

Express the relevant statement in the definitionally equal form `(f' : T → R) (t⁻¹ * x) = (f : T → R) x`. Rewrite using `[hff, mul_inv_cancel_left])`. Express the relevant statement in the definitionally equal form `f ∈ P.asIdeal ↔ transl hBt t⁻¹ f' ∈ P.asIdeal`. Rewrite using `[h2]`.
-/
theorem openImmersion_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion (U.ι ≫ j) ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j U := by
  intro R _ _ _ T _ _ Γ U hF j hj
  obtain ⟨H, A, hH, hA, hAs⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hF
  have hU := isAffineOpen_of_fin Γ hF
  have hTr : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := GlobalTheory.T.hopf_order_translation_invariant R H A hA
  have hB : ∀ f : T → R, f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h : H => f (t * h)) ∈ A := by
    intro f
    rw [← Htat.bt_sub_eq_top R T Γ U hF, GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)
      exact (hAs _).2 ⟨s, fun x h => hs x h⟩
    · intro hf t
      obtain ⟨s, hs⟩ := (hAs _).1 (hf t)
      exact (GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ⟨s, fun x h => hs ⟨x, (hH x).2 h⟩ h⟩
  let ψ : CommRingCat.of (Γ.btOrder ⊤) ⟶ Γ(Γ.G.left, U) := Spec.preimage (hU.fromSpec ≫ j)
  have hψ : Spec.map ψ = hU.fromSpec ≫ j := Spec.map_preimage _
  have hv := val_pullback Γ hU hj ψ hψ
  have hi := val_mem_range Γ hF hU hj ψ hψ
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hsurj : Function.Surjective ψ.hom := by
    intro s
    choose a ha using fun t : H => hi t ((hH t).1 t.2) s
    have haA : a ∈ A := (hAs a).2 ⟨s, fun t h => (ha t).symm⟩
    refine ⟨⟨extZero H a, extZero_mem hB hTr haA⟩, ?_⟩
    rw [← sub_eq_zero]
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_
    have ht : t ∈ H := (hH t).2 h
    rw [← valRing_apply, map_sub, valRing_apply, valRing_apply, hv t h, ← ha ⟨t, ht⟩]
    simp [extZero, ht]
  have hz : ∀ f : Γ.btOrder ⊤, ψ.hom f = 0 ↔ ∀ t ∈ H, (f : T → R) t = 0 := by
    intro f
    constructor
    · intro hf t ht
      have := hv t ((hH t).1 ht) f
      rw [hf, ← valRing_apply, map_zero] at this
      exact inj (by rw [← this, map_zero])
    · intro hf
      refine GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_
      rw [hv t h, hf t ((hH t).2 h), map_zero]
  let e : Γ.btOrder ⊤ := ⟨_, ind_translate_mem hB 1⟩
  have he1 : ∀ x ∈ H, (e : T → R) x = 1 := fun x hx => by simp [e, ind, hx]
  have he0 : ∀ x, x ∉ H → (e : T → R) x = 0 := fun x hx => by simp [e, ind, hx]
  have hidem : IsIdempotentElem e := by
    apply Subtype.ext
    funext x
    change (e : T → R) x * (e : T → R) x = (e : T → R) x
    by_cases hx : x ∈ H
    · simp [he1 x hx]
    · simp [he0 x hx]
  have hker : RingHom.ker ψ.hom = Ideal.span {1 - e} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton', hz]
    constructor
    · intro hf
      refine ⟨f, Subtype.ext (funext fun x => ?_)⟩
      change (f : T → R) x * (1 - (e : T → R) x) = (f : T → R) x
      by_cases hx : x ∈ H
      · simp [hf x hx]
      · simp [he0 x hx]
    · rintro ⟨b, rfl⟩ t ht
      change (b : T → R) t * (1 - (e : T → R) t) = 0
      simp [he1 t ht]
  have hoi : IsOpenImmersion (Spec.map ψ) :=
    (isOpenImmersion_SpecMap_iff_of_surjective ψ hsurj).2 ⟨1 - e, hidem.one_sub, hker⟩
  refine ⟨?_, ?_⟩
  · have : U.ι ≫ j = hU.isoSpec.hom ≫ Spec.map ψ := by
      rw [hψ, ← hU.isoSpec_inv_ι]
      simp
    rw [this]
    infer_instance
  · intro P
    have hBt : ∀ f ∈ Γ.btOrder ⊤, ∀ c : T, (fun x => f (c * x)) ∈ Γ.btOrder ⊤ :=
      fun f hf c => translate_mem hB hf c
    obtain ⟨t, ht⟩ := exists_translate_notMem (B := Γ.btOrder ⊤) (H := H) (ind_translate_mem hB) P.asIdeal
    let Q : Ideal (Γ.btOrder ⊤) := P.asIdeal.comap (transl hBt t⁻¹)
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have heQ : e ∉ Q := by
      intro h
      apply ht
      have : transl hBt t⁻¹ e = ⟨_, ind_translate_mem hB t⁻¹⟩ :=
        Subtype.ext (funext fun x => by simp [transl, e])
      rw [← this]
      exact h
    have h1e : 1 - e ∈ Q := by
      have h0 : e * (1 - e) ∈ Q := by
        rw [mul_sub, _root_.mul_one, hidem.eq, sub_self]
        exact Q.zero_mem
      exact (hQ.mem_or_mem h0).resolve_left heQ
    have hk : RingHom.ker ψ.hom ≤ Q := by
      rw [hker, Ideal.span_singleton_le_iff_mem]
      exact h1e
    obtain ⟨Q', hQ'⟩ : (⟨Q, hQ⟩ : PrimeSpectrum (Γ.btOrder ⊤)) ∈ Set.range (PrimeSpectrum.comap ψ.hom) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact hk
    refine ⟨t, hU.fromSpec Q', fromSpec_mem' hU _, fun f f' hff => ?_⟩
    have hjg : (j (hU.fromSpec Q')).asIdeal = Q := by
      have h1 : j (hU.fromSpec Q') = (Spec.map ψ) Q' := by
        rw [hψ]
        rfl
      rw [h1]
      exact congrArg PrimeSpectrum.asIdeal hQ'
    rw [hjg]
    have h2 : transl hBt t⁻¹ f' = f :=
      Subtype.ext (funext fun x => by
        change (f' : T → R) (t⁻¹ * x) = (f : T → R) x
        rw [hff, mul_inv_cancel_left])
    change f ∈ P.asIdeal ↔ transl hBt t⁻¹ f' ∈ P.asIdeal
    rw [h2]

end PositivityTheory.HtPt.Ge.EmbSub
