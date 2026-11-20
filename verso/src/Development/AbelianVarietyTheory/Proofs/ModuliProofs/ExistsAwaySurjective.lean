import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DenseFibreIso

section Algebra

variable {A : Type} [CommRing A]

/- English proof (translation)
Set `p : PrimeSpectrum A` to `PrimeSpectrum.comap (algebraMap A A') m`. Establish `hp : p ∉ Module.support A N`. Rewrite using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]`. Set `k` to `p.asIdeal.ResidueField`. Set `L` to `m.asIdeal.ResidueField`.

Set `: Algebra k L` to `(Ideal.ResidueField.map p.asIdeal m.asIdeal (algebraMap A A') rfl).toAlgebra`. Establish `: IsScalarTower A k L` using `.of_algebraMap_eq fun r => (Ideal.ResidueField.map_algebraMap p.asIdeal m.asIdeal (algebraMap A A') rfl r).symm`. Establish `h1 : Subsingleton (L ⊗[A] N)` using `(TensorProduct.AlgebraTensorModule.cancelBaseChange A A' L L N).symm.toEquiv.subsingleton`. Establish `h2 : Subsingleton (L ⊗[k] (k ⊗[A] N))` using `(TensorProduct.AlgebraTensorModule.cancelBaseChange A k L L N).toEquiv.subsingleton`. Conclude with `(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k L).1 h2`.

Rewrite `hp` using `[Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists]`. Take `⟨a, ha, ha'⟩` from `hp`. Conclude with `⟨a, ha', Module.mem_annihilator.1 ha⟩`.
-/
theorem exists_smul_eq_zero {N : Type} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (A' : Type) [CommRing A'] [Algebra A A'] [Subsingleton (A' ⊗[A] N)] (m : PrimeSpectrum A') :
    ∃ a : A, algebraMap A A' a ∉ m.asIdeal ∧ ∀ n : N, a • n = 0 := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A A') m
  have hp : p ∉ Module.support A N := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    let k := p.asIdeal.ResidueField
    let L := m.asIdeal.ResidueField
    let : Algebra k L := (Ideal.ResidueField.map p.asIdeal m.asIdeal (algebraMap A A') rfl).toAlgebra
    have : IsScalarTower A k L := .of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p.asIdeal m.asIdeal (algebraMap A A') rfl r).symm
    have h1 : Subsingleton (L ⊗[A] N) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' L L N).symm.toEquiv.subsingleton
    have h2 : Subsingleton (L ⊗[k] (k ⊗[A] N)) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A k L L N).toEquiv.subsingleton
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k L).1 h2
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hp
  obtain ⟨a, ha, ha'⟩ := hp
  exact ⟨a, ha', Module.mem_annihilator.1 ha⟩

/- English proof (translation)
Use `subsingleton_of_forall_eq 0 fun z => ?_` and prove the remaining obligations. Proceed by induction on `z with`. Consider the case `zero => rfl`. Consider the case `add y z hy hz => rw [hy, hz, add_zero]`. Consider the case `tmul c n`.

Take `⟨u, hu⟩` from `hu.exists_left_inv`. Establish `e : c = a • (c * u)` using `by rw [Algebra.smul_def, mul_comm, _root_.mul_assoc, hu, _root_.mul_one]`. Rewrite using `[e, TensorProduct.smul_tmul, h, TensorProduct.tmul_zero]`.
-/
theorem subsingleton_of_isUnit {N : Type} [AddCommGroup N] [Module A N] {a : A}
    (h : ∀ n : N, a • n = 0) (S : Type) [CommRing S] [Algebra A S]
    (hu : IsUnit (algebraMap A S a)) : Subsingleton (S ⊗[A] N) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z with
  | zero => rfl
  | add y z hy hz => rw [hy, hz, add_zero]
  | tmul c n =>
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    have e : c = a • (c * u) := by rw [Algebra.smul_def, mul_comm, _root_.mul_assoc, hu, _root_.mul_one]
    rw [e, TensorProduct.smul_tmul, h, TensorProduct.tmul_zero]

variable {B : Type} [CommRing B] [Algebra A B]

/- English proof (translation)
Use extensionality with `c`. Simplify using the standard rewrite rules.
-/
theorem includeLeft_eq (S : Type) [CommRing S] [Algebra A S] :
    ⇑(Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) =
      (Algebra.linearMap A B).lTensor S ∘ (TensorProduct.rid A S).symm := by
  ext c
  simp

/- English proof (translation)
Rewrite using `[includeLeft_eq, EquivLike.surjective_comp]`. Establish `hs` using `LinearMap.lTensor_surjective S (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective`. Establish `hex` using `lTensor_exact S (LinearMap.exact_map_mkQ_range (Algebra.linearMap A B)) (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `subsingleton_of_forall_eq 0 fun z => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hs z`. Conclude with `(hex y).2 (h y)`. Introduce `h y`. Conclude with `(hex y).1 (Subsingleton.elim _ _)`.
-/
theorem surjective_iff (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) ↔
      Subsingleton (S ⊗[A] (B ⧸ LinearMap.range (Algebra.linearMap A B))) := by
  rw [includeLeft_eq, EquivLike.surjective_comp]
  have hs := LinearMap.lTensor_surjective S (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective
  have hex := lTensor_exact S (LinearMap.exact_map_mkQ_range (Algebra.linearMap A B))
    (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective
  constructor
  · intro h
    refine subsingleton_of_forall_eq 0 fun z => ?_
    obtain ⟨y, rfl⟩ := hs z
    exact (hex y).2 (h y)
  · intro h y
    exact (hex y).1 (Subsingleton.elim _ _)

/- English proof (translation)
Rewrite `h` using `[surjective_iff]`. Take `⟨a, ha, ha'⟩` from `exists_smul_eq_zero (A := A) (N := B ⧸ LinearMap.range (Algebra.linearMap A B)) A' m`. Conclude with `⟨a, ha, (surjective_iff _).2 (subsingleton_of_isUnit ha' _ (IsLocalization.Away.algebraMap_isUnit a))⟩`.
-/
theorem exists_away_surjective [Module.Finite A B] (A' : Type) [CommRing A'] [Algebra A A']
    (h : Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] B))
    (m : PrimeSpectrum A') :
    ∃ a : A, algebraMap A A' a ∉ m.asIdeal ∧ Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  rw [surjective_iff] at h
  obtain ⟨a, ha, ha'⟩ :=
    exists_smul_eq_zero (A := A) (N := B ⧸ LinearMap.range (Algebra.linearMap A B)) A' m
  exact ⟨a, ha, (surjective_iff _).2
    (subsingleton_of_isUnit ha' _ (IsLocalization.Away.algebraMap_isUnit a))⟩

/- English proof (translation)
Set `I : Submodule A A` to `LinearMap.ker (Algebra.linearMap A B)`. Establish `hex : Function.Exact I.subtype (Algebra.linearMap A B)` using `LinearMap.exact_subtype_ker_map _`. Establish `hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K)` using `(LinearMap.lTensor_inj_iff_rTensor_inj K _).1 (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs (I.subtype.restrictScalars R) Subtype.val_injective hex K)`. Establish `h1 : Subsingleton (I ⊗[R] K)`. Use `subsingleton_of_forall_eq 0 fun z => hinj (h ?_)` and prove the remaining obligations.

Rewrite using `[map_zero, map_zero]`. Proceed by induction on `z with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]`. Consider the case `tmul x c`.

Establish `e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Establish `hx : (x : A) • (1 : B) = 0`. Rewrite using `[← Algebra.algebraMap_eq_smul_one]`. Conclude with `x.2`.

Express the relevant statement in the definitionally equal form `((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0`. Rewrite using `[e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]`. Establish `h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I)` using `((TensorProduct.comm A _ _).trans (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton`. Take `⟨a, ha, ha'⟩` from `exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations.

Establish `h3` using `subsingleton_of_isUnit ha' (Localization.Away a) (IsLocalization.Away.algebraMap_isUnit a)`. Rewrite using `[includeLeft_eq, EquivLike.bijective_comp]`. Use `⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(lTensor_exact (Localization.Away a) hex hs z).1 hz`. Rewrite using `[Subsingleton.elim y 0, map_zero]`.
-/
theorem exists_away_bijective [IsNoetherianRing A] (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  let I : Submodule A A := LinearMap.ker (Algebra.linearMap A B)
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := LinearMap.exact_subtype_ker_map _
  have hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj K _).1
      (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs
        (I.subtype.restrictScalars R) Subtype.val_injective hex K)
  have h1 : Subsingleton (I ⊗[R] K) := by
    refine subsingleton_of_forall_eq 0 fun z => hinj (h ?_)
    rw [map_zero, map_zero]
    induction z with
    | zero => rw [map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
    | tmul x c =>
      have e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have hx : (x : A) • (1 : B) = 0 := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact x.2
      change ((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0
      rw [e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]
  have h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I) :=
    ((TensorProduct.comm A _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton
  obtain ⟨a, ha, ha'⟩ := exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m
  refine ⟨a, ha, ?_⟩
  have h3 := subsingleton_of_isUnit ha' (Localization.Away a)
    (IsLocalization.Away.algebraMap_isUnit a)
  rw [includeLeft_eq, EquivLike.bijective_comp]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩
  obtain ⟨y, rfl⟩ := (lTensor_exact (Localization.Away a) hex hs z).1 hz
  rw [Subsingleton.elim y 0, map_zero]

end Algebra

section Geometry

variable {R : Type} [CommRing R] {Γ' X : Scheme.{0}} (s : X ⟶ Sp R) (f : Γ' ⟶ X)

/- English proof (translation)
Set `W : Set X` to `{x | ∃ U : X.Opens, x ∈ U ∧ Q (f ∣_ U)}`. Establish `hW : IsOpen W` using `isOpen_iff_forall_mem_open.2 fun x ⟨U, hx, hU⟩ => ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hx⟩`. Use `IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hx`. Establish `hc : IsClosed (s '' Wᶜ)` using `s.isClosedMap _ hW.isClosed_compl`.

Take `⟨p, hp, hp', hle⟩` from `hP (s x).asIdeal (s x).isPrime`. Establish `hsp : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R)` using `(PrimeSpectrum.le_iff_specializes _ _).1 hle`. Take `⟨y, hy, hy'⟩` from `hsp.mem_closed hc ⟨x, hx, rfl⟩`. Take `⟨T, T', g, g', f', H, _, hg, hQ⟩` from `h y (by rw [hy']; exact hp)`. Use `hy ⟨g.opensRange, hg, ?_⟩` and prove the remaining obligations.

Establish `H' : IsPullback (f' ≫ g.isoOpensRange.hom) g' g.opensRange.ι f` using `H.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)`. Establish `H''` using `isPullback_morphismRestrict f g.opensRange`. Rewrite using `[← H''.isoIsPullback_hom_fst _ _ H', Q.cancel_left_of_respectsIso, Q.cancel_right_of_respectsIso]`. Conclude with `hQ`.
-/
theorem of_local (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] [IsProper s]
    (P : Set (Ideal R)) (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p)
    (h : ∀ x : X, (s x).asIdeal ∈ P → ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Γ')
      (f' : T' ⟶ T), IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f') :
    Q f := by
  let W : Set X := {x | ∃ U : X.Opens, x ∈ U ∧ Q (f ∣_ U)}
  have hW : IsOpen W := isOpen_iff_forall_mem_open.2 fun x ⟨U, hx, hU⟩ =>
    ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hx⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  by_contra hx
  have hc : IsClosed (s '' Wᶜ) := s.isClosedMap _ hW.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (s x).isPrime
  have hsp : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hsp.mem_closed hc ⟨x, hx, rfl⟩
  obtain ⟨T, T', g, g', f', H, _, hg, hQ⟩ := h y (by rw [hy']; exact hp)
  refine hy ⟨g.opensRange, hg, ?_⟩
  have H' : IsPullback (f' ≫ g.isoOpensRange.hom) g' g.opensRange.ι f :=
    H.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have H'' := isPullback_morphismRestrict f g.opensRange
  rw [← H''.isoIsPullback_hom_fst _ _ H', Q.cancel_left_of_respectsIso,
    Q.cancel_right_of_respectsIso]
  exact hQ

/- English proof (translation)
Establish `H₀` using `(IsPullback.of_hasPullback f (pullback.fst s t)).flip`. Establish `e : pullback.lift g u hu ≫ pullback.fst s t = g` using `pullback.lift_fst _ _ _`. Establish `H₁` using `IsPullback.of_bot' (h₁₁ := f') (v₁₂ := pullback.lift g u hu) (by rw [e]; exact H) H₀`. Conclude with `(MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip (inferInstanceAs (IsIso _))`.
-/
theorem isIso_of_fibre {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Γ'}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) (u : T ⟶ S) (hu : g ≫ s = u ≫ t) : IsIso f' := by
  have H₀ := (IsPullback.of_hasPullback f (pullback.fst s t)).flip
  have e : pullback.lift g u hu ≫ pullback.fst s t = g := pullback.lift_fst _ _ _
  have H₁ := IsPullback.of_bot' (h₁₁ := f') (v₁₂ := pullback.lift g u hu) (by rw [e]; exact H) H₀
  exact (MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip
    (inferInstanceAs (IsIso _))

/- English proof (translation)
Take `⟨i, hi⟩` from `X.affineOpenCover.openCover.exists_eq x`. Set `j` to `X.affineOpenCover.f i`. Establish `: IsOpenImmersion j` using `X.affineOpenCover.map_prop i`. Set `e` to `(pullback j f).isoSpec`. Use `⟨_, _, Spec.preimage (j ≫ s), Spec.preimage (e.inv ≫ pullback.fst j f), j, e.inv ≫ pullback.snd j f, inferInstance, hi, ?_, (Spec.map_preimage _).symm⟩` and prove the remaining obligations.

Rewrite using `[Spec.map_preimage]`. Conclude with `(IsPullback.of_hasPullback j f).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)`.
-/
theorem exists_chart [IsAffineHom f] (x : X) :
    ∃ (A B : CommRingCat.{0}) (ψ : CommRingCat.of R ⟶ A) (φ : A ⟶ B) (j : Spec A ⟶ X)
      (j' : Spec B ⟶ Γ'), IsOpenImmersion j ∧ x ∈ Set.range j ∧
        IsPullback (Spec.map φ) j' j f ∧ j ≫ s = Spec.map ψ := by
  obtain ⟨i, hi⟩ := X.affineOpenCover.openCover.exists_eq x
  let j := X.affineOpenCover.f i
  have : IsOpenImmersion j := X.affineOpenCover.map_prop i
  let e := (pullback j f).isoSpec
  refine ⟨_, _, Spec.preimage (j ≫ s), Spec.preimage (e.inv ≫ pullback.fst j f), j,
    e.inv ≫ pullback.snd j f, inferInstance, hi, ?_, (Spec.map_preimage _).symm⟩
  rw [Spec.map_preimage]
  exact (IsPullback.of_hasPullback j f).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/- English proof (translation)
The claim follows from `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A S B)`.
-/
theorem isPullback_tensor (A S B : Type) [CommRing A] [CommRing S] [CommRing B] [Algebra A S]
    [Algebra A B] :
    IsPullback (spMap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B))
      (spMap (Algebra.TensorProduct.includeRight.toRingHom : B →+* S ⊗[A] B))
      (spMap (algebraMap A S)) (spMap (algebraMap A B)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A S B)

/- English proof (translation)
Take `⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩` from `exists_chart s f x`. Set `: Algebra R A` to `ψ.hom.toAlgebra`. Set `: Algebra A B` to `φ.hom.toAlgebra`. Set `: Algebra R B` to `(φ.hom.comp ψ.hom).toAlgebra`. Establish `: IsScalarTower R A B` using `.of_algebraMap_eq fun _ => rfl`.

Use `replace H : IsPullback (spMap (algebraMap A B)) j' j f := H`. Use `replace hj : j ≫ s = spMap (algebraMap R A) := hj`. Establish `H₁` using `isPullback_tensor R A K`. Take `⟨m, hm, -⟩` from `Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by`. Rewrite using `[← hj, Scheme.Hom.comp_apply]`.

Conclude with `PrimeSpectrum.ext hx.symm)`. Establish `H₂` using `(isPullback_tensor A (A ⊗[R] K) B).paste_vert H`. Establish `hi` using `isIso_of_fibre s f (spMap (algebraMap R K)) H₂ _ (by`. Rewrite using `[Category.assoc, hj]`. Conclude with `H₁.w)`.

Take `⟨a, ha, hQ⟩` from `h A B j j' H hj (isIso_SpecMap_iff.1 hi) m`. Use `⟨_, _, _, _, _, (isPullback_tensor A (Localization.Away a) B).paste_vert H, inferInstance, ?_, hQ⟩` and prove the remaining obligations. Establish `hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a)))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]`. Conclude with `ha`.

Take `⟨z, rfl⟩` from `hy`. Conclude with `⟨z, Scheme.Hom.comp_apply _ _ _⟩`.
-/
theorem local_of_ring [IsAffineHom f] (Q : MorphismProperty Scheme.{0}) (K : Type) [Field K]
    [Algebra R K] [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (h : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
      [IsScalarTower R A B] (j : Sp A ⟶ X) (j' : Sp B ⟶ Γ') [IsOpenImmersion j],
      IsPullback (spMap (algebraMap A B)) j' j f → j ≫ s = spMap (algebraMap R A) →
      Function.Bijective
        (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) →
      ∀ m : PrimeSpectrum (A ⊗[R] K), ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧
        Q (spMap (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away a →+* Localization.Away a ⊗[A] B)))
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Γ')
      (f' : T' ⟶ T), IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f' := by
  obtain ⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩ := exists_chart s f x
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra R B := (φ.hom.comp ψ.hom).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun _ => rfl
  replace H : IsPullback (spMap (algebraMap A B)) j' j f := H
  replace hj : j ≫ s = spMap (algebraMap R A) := hj
  have H₁ := isPullback_tensor R A K
  obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by
    rw [← hj, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext hx.symm)
  have H₂ := (isPullback_tensor A (A ⊗[R] K) B).paste_vert H
  have hi := isIso_of_fibre s f (spMap (algebraMap R K)) H₂ _ (by
    rw [Category.assoc, hj]; exact H₁.w)
  obtain ⟨a, ha, hQ⟩ := h A B j j' H hj (isIso_SpecMap_iff.1 hi) m
  refine ⟨_, _, _, _, _, (isPullback_tensor A (Localization.Away a) B).paste_vert H,
    inferInstance, ?_, hQ⟩
  have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]
    exact ha
  obtain ⟨z, rfl⟩ := hy
  exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩

end Geometry

set_option backward.isDefEq.respectTransparency.types false in

/- English proof (translation)
Introduce `R _ _ Γ' X s f P hP₀ _ _ _ _ h`. Establish `hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p` using `fun q hq => by`. Take `⟨p, h1, h2, h3, -⟩` from `hP₀ q 1 hq ((Ideal.ne_top_iff_one q).1 hq.ne_top)`. Conclude with `⟨p, h1, h2, h3⟩`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian s`.

Establish `hfin : IsFinite f`. Use `of_local s f @IsFinite P hP fun x hx => ?_` and prove the remaining obligations. Take `⟨K, _, t, ht, hi⟩` from `h _ hx`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := s) (g := spMap t) x (⊥ : PrimeSpectrum K) (PrimeSpectrum.ext ht.symm)`. Establish `hf : (f ⁻¹' {x}).Finite`.

Use `(Set.finite_singleton ((inv (pullback.snd f (pullback.fst s (spMap t))) ≫ pullback.fst f (pullback.fst s (spMap t))) z)).subset fun y hy => ?_` and prove the remaining obligations. Take `⟨w, rfl, rfl⟩` from `Scheme.Pullback.exists_preimage_pullback (f := f) (g := pullback.fst s (spMap t)) y z (hy.trans hz.symm)`. Rewrite using `[Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id_assoc]`. Take `⟨V, hV, hV'⟩` from `exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hf`. Conclude with `⟨_, _, _, _, _, isPullback_morphismRestrict f V, inferInstance, by simpa using hV, hV'⟩`.

Establish `hcl : IsClosedImmersion f`. Use `of_local s f @IsClosedImmersion P hP fun x hx => ?_` and prove the remaining obligations. Take `⟨K, _, t, ht, hi⟩` from `h _ hx`. Set `: Algebra R K` to `t.toAlgebra`. Use `local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x ht` and prove the remaining obligations.

Establish `h1 : IsFinite (spMap (algebraMap A B))` using `MorphismProperty.of_isPullback (P := @IsFinite) H.flip hfin`. Establish `: Module.Finite A B` using `RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)`. Take `⟨a, ha, ha'⟩` from `exists_away_surjective (A ⊗[R] K) hb.2 m`. Conclude with `⟨a, ha, IsClosedImmersion.spec_of_surjective _ ha'⟩`. Use `of_local s f (MorphismProperty.isomorphisms _) P hP fun x hx => ?_` and prove the remaining obligations.

Take `⟨K, _, t, ht, hi⟩` from `h _ hx`. Set `: Algebra R K` to `t.toAlgebra`. Use `local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x ht` and prove the remaining obligations. Establish `h1 : IsClosedImmersion (spMap (algebraMap A B))` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl`. Establish `hs : Function.Surjective (algebraMap A B)`.

Establish `h2` using `(IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2`. Establish `e` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))`. Establish `h3` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2`. Rewrite `h3` using `[← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp]`. Conclude with `h3.of_comp`.

Establish `: IsOpenImmersion j'` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›`. Establish `h2 : Flat (spMap (algebraMap R B))`. Establish `e : spMap (algebraMap R B) = j' ≫ f ≫ s`. Rewrite using `[← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Use `infer_instance`. Establish `: Module.Flat R B` using `RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)`. Establish `: IsNoetherianRing A` using `isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion j)`. Take `⟨a, ha, ha'⟩` from `exists_away_bijective R K hs hb.1 m`.

Conclude with `⟨a, ha, isIso_SpecMap_iff.2 ha'⟩`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Γ' X : Scheme.{0}) (s : X ⟶ Sp R) (f : Γ' ⟶ X) (P : Set (Ideal R)), (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → IsProper s → Flat s → IsProper f → Flat (f ≫ s) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ IsIso (pullback.snd f (pullback.fst s (spMap x)))) → IsIso f := by
  intro R _ _ Γ' X s f P hP₀ _ _ _ _ h
  have hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p := fun q hq => by
    obtain ⟨p, h1, h2, h3, -⟩ := hP₀ q 1 hq ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hfin : IsFinite f := by
    refine of_local s f @IsFinite P hP fun x hx => ?_
    obtain ⟨K, _, t, ht, hi⟩ := h _ hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := spMap t) x
      (⊥ : PrimeSpectrum K) (PrimeSpectrum.ext ht.symm)
    have hf : (f ⁻¹' {x}).Finite := by
      refine (Set.finite_singleton ((inv (pullback.snd f (pullback.fst s (spMap t))) ≫
        pullback.fst f (pullback.fst s (spMap t))) z)).subset fun y hy => ?_
      obtain ⟨w, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
        (g := pullback.fst s (spMap t)) y z (hy.trans hz.symm)
      rw [Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id_assoc]
    obtain ⟨V, hV, hV'⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hf
    exact ⟨_, _, _, _, _, isPullback_morphismRestrict f V, inferInstance, by simpa using hV, hV'⟩
  have hcl : IsClosedImmersion f := by
    refine of_local s f @IsClosedImmersion P hP fun x hx => ?_
    obtain ⟨K, _, t, ht, hi⟩ := h _ hx
    let : Algebra R K := t.toAlgebra
    refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x ht
    have h1 : IsFinite (spMap (algebraMap A B)) :=
      MorphismProperty.of_isPullback (P := @IsFinite) H.flip hfin
    have : Module.Finite A B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)
    obtain ⟨a, ha, ha'⟩ := exists_away_surjective (A ⊗[R] K) hb.2 m
    exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ ha'⟩
  refine of_local s f (MorphismProperty.isomorphisms _) P hP fun x hx => ?_
  obtain ⟨K, _, t, ht, hi⟩ := h _ hx
  let : Algebra R K := t.toAlgebra
  refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x ht
  have h1 : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›
  have h2 : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = j' ≫ f ≫ s := by
      rw [← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]; rfl
    rw [e]; infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)
  have : IsNoetherianRing A :=
    isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion j)
  obtain ⟨a, ha, ha'⟩ := exists_away_bijective R K hs hb.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.2 ha'⟩

end GlobalTheory.DenseFibreIso
