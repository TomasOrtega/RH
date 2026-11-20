import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

/- English proof (translation)
Set `b` to `Module.finBasis ℤ X`. Set `f : (Fin (Module.finrank ℤ X) →₀ ℕ) →+ X` to `b.repr.symm.toLinearMap.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))`. Establish `hf : Function.Injective f` using `b.repr.symm.injective.comp (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)`. Set `P` to `MvPolynomial (Fin (Module.finrank ℤ X)) A`. Set `φ : P →ₐ[A] AddMonoidAlgebra A X` to `AddMonoidAlgebra.mapDomainAlgHom A A f`.

Establish `hφ : ∀ m a, φ (MvPolynomial.monomial m a) = AddMonoidAlgebra.single (f m) a` using `fun m a => AddMonoidAlgebra.mapDomain_single`. Set `_ : Algebra P (AddMonoidAlgebra A X)` to `φ.toRingHom.toAlgebra`. Establish `: IsScalarTower A P (AddMonoidAlgebra A X)` using `IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm`. Set `one : Fin (Module.finrank ℤ X) →₀ ℕ` to `Finsupp.equivFunOnFinite.symm fun _ => 1`. Establish `hr : ∀ n : ℕ, algebraMap P (AddMonoidAlgebra A X) (MvPolynomial.monomial one 1) ^ n = AddMonoidAlgebra.single (n • f one) 1` using `fun n => by show φ _ ^ n = _`.

Rewrite using `[hφ, AddMonoidAlgebra.single_pow, one_pow]`. Establish `: IsLocalization.Away (MvPolynomial.monomial one (1 : A) : P) (AddMonoidAlgebra A X)`. Use `IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun a c h => ⟨0, by rw [AddMonoidAlgebra.mapDomain_injective hf h]⟩)` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-f one) 1) ?_ show φ _ * _ = _` and prove the remaining obligations. Rewrite using `[hφ, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.one_mul]`.

Both sides reduce to the same expression. Proceed by induction on `s using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `add s t hs ht`. Take `⟨n, a, ha⟩` from `hs`.

Take `⟨m, c, hc⟩` from `ht`. Use `⟨n + m, a * MvPolynomial.monomial one 1 ^ m + c * MvPolynomial.monomial one 1 ^ n, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hc]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single x a`.

Set `n : ℕ` to `∑ i, (b.repr x i).natAbs`. Use `⟨n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (b.repr x i + n).toNat) a, ?_⟩` and prove the remaining obligations. Use `show _ = φ _`. Rewrite using `[hr, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one]`. Use `congr 1`.

Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `h₁ : (b.repr x i).natAbs ≤ n` using `Finset.single_le_sum (f := fun i => (b.repr x i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Simplify using `[f, one]`. Use linear arithmetic over natural numbers and integers.

Establish `: Algebra.IsStandardSmooth A P` using `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2 ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis A _, by rintro _ ⟨i, rfl⟩; exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply A _ i).symm⟩⟩`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A P` using `(Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by`. Rewrite using `[rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis A _), Fintype.card_fin])`. Use `Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := AddMonoidAlgebra A X) (MvPolynomial.monomial one (1 : A) : P)` as an intermediate fact. Establish `h` using `Algebra.IsStandardSmoothOfRelativeDimension.trans (Module.finrank ℤ X) 0 A P (AddMonoidAlgebra A X)`.

Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem torus_std (A X : Type) [CommRing A] [Nontrivial A] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A (AddMonoidAlgebra A X) := by
  classical
  let b := Module.finBasis ℤ X
  let f : (Fin (Module.finrank ℤ X) →₀ ℕ) →+ X :=
    b.repr.symm.toLinearMap.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
  have hf : Function.Injective f := b.repr.symm.injective.comp (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)
  let P := MvPolynomial (Fin (Module.finrank ℤ X)) A
  let φ : P →ₐ[A] AddMonoidAlgebra A X := AddMonoidAlgebra.mapDomainAlgHom A A f
  have hφ : ∀ m a, φ (MvPolynomial.monomial m a) = AddMonoidAlgebra.single (f m) a := fun m a =>
    AddMonoidAlgebra.mapDomain_single
  let _ : Algebra P (AddMonoidAlgebra A X) := φ.toRingHom.toAlgebra
  have : IsScalarTower A P (AddMonoidAlgebra A X) := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let one : Fin (Module.finrank ℤ X) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  have hr : ∀ n : ℕ, algebraMap P (AddMonoidAlgebra A X) (MvPolynomial.monomial one 1) ^ n =
      AddMonoidAlgebra.single (n • f one) 1 := fun n => by
    show φ _ ^ n = _
    rw [hφ, AddMonoidAlgebra.single_pow, one_pow]
  have : IsLocalization.Away (MvPolynomial.monomial one (1 : A) : P) (AddMonoidAlgebra A X) := by
    refine IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun a c h => ⟨0, by rw [AddMonoidAlgebra.mapDomain_injective hf h]⟩)
    · refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-f one) 1) ?_
      show φ _ * _ = _
      rw [hφ, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.one_mul]; rfl
    · induction s using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨0, 0, by simp⟩
      | add s t hs ht =>
        obtain ⟨n, a, ha⟩ := hs
        obtain ⟨m, c, hc⟩ := ht
        refine ⟨n + m, a * MvPolynomial.monomial one 1 ^ m + c * MvPolynomial.monomial one 1 ^ n, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hc]; ring
      | single x a =>
        let n : ℕ := ∑ i, (b.repr x i).natAbs
        refine ⟨n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (b.repr x i + n).toNat) a, ?_⟩
        show _ = φ _
        rw [hr, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one]
        congr 1
        apply b.repr.injective
        ext i
        have h₁ : (b.repr x i).natAbs ≤ n := Finset.single_le_sum (f := fun i => (b.repr x i).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp [f, one]
        omega
  have : Algebra.IsStandardSmooth A P := Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
    ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis A _, by rintro _ ⟨i, rfl⟩; exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply A _ i).symm⟩⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A P :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
      rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis A _), Fintype.card_fin])
  have := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := AddMonoidAlgebra A X)
    (MvPolynomial.monomial one (1 : A) : P)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans (Module.finrank ℤ X) 0 A P (AddMonoidAlgebra A X)
  rwa [zero_add] at h

/- English proof (translation)
Establish `h : SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorusAff ZU X).hom` using `(HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Module.finrank ℤ X))).2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (torus_std _ X)))`. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h`.
-/
theorem torus_dim (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom := by
  have h : SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorusAff ZU X).hom :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Module.finrank ℤ X))).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (torus_std _ X)))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, h⟩` from `hm.exists_isStandardSmoothOfRelativeDimension x`. Take `⟨s, hs, h'⟩` from `HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e`. Establish `: Nonempty V` using `⟨⟨x, hx⟩⟩`. Take `⟨p, hp⟩` from `Ideal.exists_maximal Γ(X, V)`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by`.

Assume the negation of the conclusion as `hc`. Conclude with `hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))`. Establish `: Nontrivial (Localization.Away t)`. Assume the negation of the conclusion as `hc`. Take `⟨k, hk⟩` from `(IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)`.

Conclude with `htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))`. Establish `h₁` using `h' t ht`. Establish `h₂` using `(RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).right (Localization.Away t) t _ h`. Set `_` to `((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra`. Establish `r₁` using `@Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n h₁`.

Establish `r₂` using `@Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m h₂`. Conclude with `r₁.symm.trans r₂` after adjusting the coercions.
-/
theorem dim_unique {X Y : Scheme.{0}} (f : X ⟶ Y) {n m : ℕ} (hn : SmoothOfRelativeDimension n f)
    (hm : SmoothOfRelativeDimension m f) (x : X) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have h₂ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).right
    (Localization.Away t) t _ h
  let _ := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have r₁ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n h₁
  have r₂ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m h₂
  exact_mod_cast r₁.symm.trans r₂

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, h⟩` from `Smooth.exists_isStandardSmooth f x`. Establish `: Nonempty V` using `⟨⟨x, hx⟩⟩`. Set `_` to `(f.appLE U V e).hom.toAlgebra`. Establish `: Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V)` using `h`. Take `⟨_, _, _, _, ⟨P⟩⟩` from `this`.

Establish `h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V e).hom` using `⟨_, _, _, ‹_›, P, rfl⟩`. Establish `: IsAffine U` using `hU`. Establish `: IsAffine V` using `hV`. Establish `: SmoothOfRelativeDimension P.dimension (f.resLE U V e)` using `(HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).2 h'))`. Use `⟨P.dimension + 0, V, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.resLE_comp_ι f e]`. Use `infer_instance`.
-/
theorem exists_dim {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (W : X.Opens), x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := h
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
  have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V e).hom := ⟨_, _, _, ‹_›, P, rfl⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : SmoothOfRelativeDimension P.dimension (f.resLE U V e) :=
    (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).2 h'))
  refine ⟨P.dimension + 0, V, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]; infer_instance

/- English proof (translation)
Establish `h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f')` using `(smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback ((isPullback_morphismRestrict a W).paste_vert h) hW`. Establish `h₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W).ι ≫ f')` using `inferInstance`. Conclude with `(dim_unique _ h₁ h₂ ⟨x, hx⟩).trans (zero_add m)`.
-/
theorem dim_base {X S X' S' : Scheme.{0}} {f : X ⟶ S} {f' : X' ⟶ S'} {a : X' ⟶ X} {b : S' ⟶ S} (h : IsPullback a f' f b)
    {n m : ℕ} {W : X.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) (hm : SmoothOfRelativeDimension m f') (x : X')
    (hx : a x ∈ W) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W).ι ≫ f') := inferInstance
  exact (dim_unique _ h₁ h₂ ⟨x, hx⟩).trans (zero_add m)

/- English proof (translation)
Establish `hi : i ≫ q = 1` using `h.w`. Establish `: Mono i` using `h.flip.mono_snd_of_mono`. Use `IsPullback.of_isLimit' ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩ (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]`. Use the proof step `rfl)) s.snd) (fun s => ?_) (fun s => lift_snd _ _)`.

Use the proof step `(fun s m h₁ h₂ => ?_))`. Rewrite using `[MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]`. Rewrite using `[lift_snd, h₂]`.
-/
theorem torsor_pullback {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B)
    [IsMonHom q] (h : IsPullback i (toUnit _) q η[B]) : IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have hi : i ≫ q = 1 := h.w
  have : Mono i := h.flip.mono_snd_of_mono
  refine IsPullback.of_isLimit' ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩
    (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]; rfl)) s.snd) (fun s => ?_) (fun s => lift_snd _ _)
      (fun s m h₁ h₂ => ?_))
  · rw [MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]
    · rw [lift_snd, h₂]

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ t P`. Use `t.semi.smooth` as an intermediate fact. Take `⟨n, W, hW, dW⟩` from `exists_dim t.G.hom (eSec t.G (closedPoint V))`. Establish `all : ∀ y : Sp V, eSec t.G y ∈ W` using `fun y => (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (eSec t.G) hW)).mpr trivial`. Establish `unit : ∀ {S' : Scheme.{0}} (b : S' ⟶ Sp V) (y : S'), pullback.fst t.G.hom b (eSec ((Over.pullback b).obj t.G) y) ∈ W` using `fun b y => (congrArg (fun g => g y ∈ W) (cubeMapOf (isGrpPullback_pullback t.G b)).e_comm).mpr (all _)`.

Establish `g₁ : n = P.A.g`. Use `P.A.smoothDim` as an intermediate fact. Establish `: IsIso P.U.gen.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map P.U.gen.hom))`. Establish `d : SmoothOfRelativeDimension (0 + P.A.g) (pullback.snd t.G.hom (jK V))`. Rewrite using `[show pullback.snd t.G.hom (jK V) = P.U.gen.hom.left ≫ P.A.A.hom from (Over.w P.U.gen.hom).symm]`.

Use `infer_instance`. Conclude with `(dim_base (IsPullback.of_hasPullback _ _) dW d _ (unit (jK V) (default : PrimeSpectrum (FractionRing V)))).trans (zero_add _)`. Set `c` to `P.U.gt 0`. Use `c.q_hom` as an intermediate fact. Use `c.i_hom` as an intermediate fact.

Use `c.q_flat` as an intermediate fact. Use `c.q_surj` as an intermediate fact. Use `c.q_affine` as an intermediate fact. Establish `dT` using `torus_dim (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) P.D.toPre.X`. Establish `: Smooth c.q.left`.

Use `dT.smooth` as an intermediate fact. Use `MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ((torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_` and prove the remaining obligations. Conclude with `smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this`. Establish `: Nontrivial (V ⧸ maximalIdeal V ^ (0 + 1))` using `Ideal.Quotient.nontrivial_iff.2 (by rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal V).ne_top)`. Take `⟨y⟩ : Nonempty (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))))` from `inferInstanceAs (Nonempty (PrimeSpectrum _))`.

Take `⟨m, W₁, hW₁, d₁⟩` from `exists_dim c.q.left (eSec (thickObj V (maximalIdeal V) 0 t.G) y)`. Establish `g₂ : m = Module.finrank ℤ P.D.toPre.X` using `dim_base (c.isKernel.map (Over.forget _)) d₁ dT (eSec _ y) ((congrArg (fun g => g.left y ∈ W₁) (IsMonHom.one_hom c.i)).mpr hW₁)`. Establish `dB : SmoothOfRelativeDimension P.D.toPre.P.g (thickObj V (maximalIdeal V) 0 P.D.toPre.P.A).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) P.D.toPre.P.smoothDim`. Establish `d₂ : SmoothOfRelativeDimension (m + P.D.toPre.P.g) (W₁.ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom)`. Rewrite using `[← Over.w c.q, ← Category.assoc]`.

Use `infer_instance`. Establish `d₃ : SmoothOfRelativeDimension n ((pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom)` using `(smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback ((isPullback_morphismRestrict _ W).paste_vert (IsPullback.of_hasPullback _ _)) dW`. Establish `g₃ : n = m + P.D.toPre.P.g`. Set `W₂` to `pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W`. Establish `e₁ : SmoothOfRelativeDimension (0 + n) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom)`.

Rewrite using `[← Scheme.homOfLE_ι _ (inf_le_left : W₂ ⊓ W₁ ≤ W₂), Category.assoc]`. Use `infer_instance`. Establish `e₂ : SmoothOfRelativeDimension (0 + (m + P.D.toPre.P.g)) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom)`. Rewrite using `[← Scheme.homOfLE_ι _ (inf_le_right : W₂ ⊓ W₁ ≤ W₁), Category.assoc]`. Use `infer_instance`.

Simplify using `using dim_unique _ e₁ e₂ ⟨_, unit _ y, hW₁⟩`. Rewrite using `[← g₁, g₃, g₂]`.
-/
theorem dimSplit : DimSplitStatement := by
  intro E _ _ _ H V _ _ _ t P
  have := t.semi.smooth
  obtain ⟨n, W, hW, dW⟩ := exists_dim t.G.hom (eSec t.G (closedPoint V))
  have all : ∀ y : Sp V, eSec t.G y ∈ W := fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (eSec t.G) hW)).mpr trivial
  have unit : ∀ {S' : Scheme.{0}} (b : S' ⟶ Sp V) (y : S'),
      pullback.fst t.G.hom b (eSec ((Over.pullback b).obj t.G) y) ∈ W := fun b y =>
    (congrArg (fun g => g y ∈ W) (cubeMapOf (isGrpPullback_pullback t.G b)).e_comm).mpr (all _)

  have g₁ : n = P.A.g := by
    have := P.A.smoothDim
    have : IsIso P.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.U.gen.hom))
    have d : SmoothOfRelativeDimension (0 + P.A.g) (pullback.snd t.G.hom (jK V)) := by
      rw [show pullback.snd t.G.hom (jK V) = P.U.gen.hom.left ≫ P.A.A.hom from (Over.w P.U.gen.hom).symm]
      infer_instance
    exact (dim_base (IsPullback.of_hasPullback _ _) dW d _ (unit (jK V) (default : PrimeSpectrum (FractionRing V)))).trans
      (zero_add _)

  let c := P.U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have dT := torus_dim (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) P.D.toPre.X
  have : Smooth c.q.left := by
    have := dT.smooth
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : Nontrivial (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal V).ne_top)
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨m, W₁, hW₁, d₁⟩ := exists_dim c.q.left (eSec (thickObj V (maximalIdeal V) 0 t.G) y)
  have g₂ : m = Module.finrank ℤ P.D.toPre.X := dim_base (c.isKernel.map (Over.forget _)) d₁ dT (eSec _ y)
    ((congrArg (fun g => g.left y ∈ W₁) (IsMonHom.one_hom c.i)).mpr hW₁)
  have dB : SmoothOfRelativeDimension P.D.toPre.P.g (thickObj V (maximalIdeal V) 0 P.D.toPre.P.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      P.D.toPre.P.smoothDim
  have d₂ : SmoothOfRelativeDimension (m + P.D.toPre.P.g) (W₁.ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
    rw [← Over.w c.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension n ((pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W).ι ≫
      (thickObj V (maximalIdeal V) 0 t.G).hom) := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict _ W).paste_vert (IsPullback.of_hasPullback _ _)) dW
  have g₃ : n = m + P.D.toPre.P.g := by
    let W₂ := pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W
    have e₁ : SmoothOfRelativeDimension (0 + n) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W₂ ⊓ W₁ ≤ W₂), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + (m + P.D.toPre.P.g)) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W₂ ⊓ W₁ ≤ W₁), Category.assoc]; infer_instance
    simpa using dim_unique _ e₁ e₂ ⟨_, unit _ y, hW₁⟩
  rw [← g₁, g₃, g₂]

end ReciprocityTheory.ChartRestriction.G.H1
