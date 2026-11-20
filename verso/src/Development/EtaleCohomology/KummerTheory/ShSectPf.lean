import Development.EtaleCohomology.KummerTheory.SecSHPf

open Polynomial IsLocalRing CategoryTheory AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ShSectPf

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Use `hφ a ((mem_maximalIdeal a).2 ha)` as an intermediate fact. Rewrite `h` using `[this]`. Conclude with `not_isUnit_zero h`.
-/
theorem isUnit_of_map {A K : Type} [CommRing A] [IsLocalRing A] [Field K] (φ : A →+* K)
    (hφ : ∀ a ∈ maximalIdeal A, φ a = 0) {a : A} (h : IsUnit (φ a)) : IsUnit a := by
  by_contra ha
  have := hφ a ((mem_maximalIdeal a).2 ha)
  rw [this] at h; exact not_isUnit_zero h

/- English proof (translation)
Take `⟨s, hsQ, hst⟩` from `Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q`. Set `S` to `Localization.Away s`. Set `P : StandardEtalePresentation A S` to `hst.nonempty_standardEtalePresentation.some`. Set `K` to `Q.ResidueField`. Establish `hsu : IsUnit ((IsScalarTower.toAlgHom A B K) s)`.

Rewrite using `[isUnit_iff_ne_zero]`. Use `show algebraMap B Q.ResidueField s ≠ 0`. Rewrite using `[Ne, Ideal.algebraMap_residueField_eq_zero]`. Conclude with `hsQ`. Set `ψ : S →ₐ[A] K` to `IsLocalization.Away.liftAlgHom s hsu`.

Set `xb : K` to `ψ P.x`. Establish `hmap` using `P.hasMap.map ψ`. Establish `hder` using `hmap.isUnit_derivative_f`. Establish `hkill : ∀ a ∈ maximalIdeal A, algebraMap A K a = 0`. Introduce `a ha`.

Rewrite using `[IsScalarTower.algebraMap_apply A B K, Ideal.algebraMap_residueField_eq_zero]`. Rewrite `ha` using `[← hQ]`. Conclude with `ha`. Establish `hloc : IsLocalHom (algebraMap A K)` using `⟨fun a h => isUnit_of_map _ hkill h⟩`. Set `i : ResidueField A →+* K` to `ResidueField.lift (algebraMap A K)`.

Establish `hi : ∀ a, i (residue A a) = algebraMap A K a` using `fun a => ResidueField.lift_residue_apply _ a`. Set `_ : Algebra (ResidueField A) K` to `i.toAlgebra`. Establish `hev : ∀ q : A[X], aeval xb (q.map (residue A)) = aeval xb q`. Introduce `q`. Rewrite using `[aeval_def, aeval_def, eval₂_map]`.

Use `congr 1`. Set `fb` to `P.f.map (residue A)`. Establish `hint : IsIntegral (ResidueField A) xb` using `⟨fb, P.monic_f.map _, by rw [← aeval_def, hev]; exact hmap.1⟩`. Establish `hirr` using `minpoly.irreducible hint`. Establish `hsep : (minpoly (ResidueField A) xb).Separable`.

Rewrite using `[Polynomial.separable_iff_derivative_ne_zero hirr]`. Introduce `h0`. Take `⟨h, hh⟩` from `minpoly.dvd (ResidueField A) xb (p := fb) (by rw [hev]; exact hmap.1)`. Establish `: aeval xb (derivative fb) = 0`. Rewrite using `[hh, derivative_mul, h0]`.

Simplify using the standard rewrite rules. Rewrite `this` using `[show derivative fb = (derivative P.f).map (residue A) from derivative_map _ _, hev]`. Rewrite `hder` using `[this]`. Conclude with `not_isUnit_zero hder`. Take `⟨a0, ha0⟩` from `IsSepClosed.exists_root _ (minpoly.degree_pos hint).ne' hsep`.

Establish `hd0 : X - C a0 ∣ minpoly (ResidueField A) xb` using `dvd_iff_isRoot.2 ha0`. Establish `hdvd : minpoly (ResidueField A) xb ∣ X - C a0` using `Irreducible.dvd_symm (irreducible_X_sub_C a0) hirr hd0`. Take `⟨a00, ha00⟩` from `residue_surjective a0`. Establish `hxb : xb = algebraMap A K a00`. Establish `h1 : aeval xb (X - C a0) = 0`.

Take `⟨c, hc⟩` from `hdvd`. Rewrite using `[hc, map_mul, minpoly.aeval, zero_mul]`. Rewrite `h1` using `[map_sub, aeval_X, aeval_C, sub_eq_zero]`. Rewrite using `[h1, ← ha00]`. Conclude with `hi a00`.

Establish `hzero : ∀ a : A, algebraMap A K a = 0 → a ∈ maximalIdeal A`. Introduce `a ha`. Assume the negation of the conclusion as `hn`. Use `((mem_maximalIdeal a).not.1 hn |> not_not.1).map (algebraMap A K)` as an intermediate fact. Rewrite `this` using `[ha]`.

Conclude with `not_isUnit_zero this`. Establish `hev' : ∀ q : A[X], algebraMap A K (q.eval a00) = aeval xb q`. Introduce `q`. Rewrite using `[hxb, aeval_algebraMap_apply, coe_aeval_eq_eval]`. Take `⟨r, hr, hra⟩` from `HenselianLocalRing.is_henselian P.f P.monic_f a00 (hzero _ (by rw [hev']; exact hmap.1)) (isUnit_of_map _ hkill (by rw [hev']; exact hder))`.

Establish `hrK : algebraMap A K r = xb`. Rewrite using `[hxb, ← sub_eq_zero, ← map_sub]`. Conclude with `hkill _ hra`. Establish `hr' : P.HasMap r`. Use `⟨by rw [coe_aeval_eq_eval]; exact hr, isUnit_of_map _ hkill ?_⟩` and prove the remaining obligations.

Rewrite using `[← aeval_algebraMap_apply, hrK]`. Conclude with `hmap.2`. Conclude with `⟨((P.lift r hr').comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom A B S)⟩`.
-/
theorem alg_sect (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) : Nonempty (B →ₐ[A] A) := by
  obtain ⟨s, hsQ, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away s
  let P : StandardEtalePresentation A S := hst.nonempty_standardEtalePresentation.some
  let K := Q.ResidueField
  have hsu : IsUnit ((IsScalarTower.toAlgHom A B K) s) := by
    rw [isUnit_iff_ne_zero]
    show algebraMap B Q.ResidueField s ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hsQ
  let ψ : S →ₐ[A] K := IsLocalization.Away.liftAlgHom s hsu
  let xb : K := ψ P.x
  have hmap := P.hasMap.map ψ
  have hder := hmap.isUnit_derivative_f

  have hkill : ∀ a ∈ maximalIdeal A, algebraMap A K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B K, Ideal.algebraMap_residueField_eq_zero]
    rw [← hQ] at ha; exact ha
  have hloc : IsLocalHom (algebraMap A K) := ⟨fun a h => isUnit_of_map _ hkill h⟩
  let i : ResidueField A →+* K := ResidueField.lift (algebraMap A K)
  have hi : ∀ a, i (residue A a) = algebraMap A K a := fun a => ResidueField.lift_residue_apply _ a
  let _ : Algebra (ResidueField A) K := i.toAlgebra
  have hev : ∀ q : A[X], aeval xb (q.map (residue A)) = aeval xb q := by
    intro q
    rw [aeval_def, aeval_def, eval₂_map]
    congr 1
  let fb := P.f.map (residue A)
  have hint : IsIntegral (ResidueField A) xb :=
    ⟨fb, P.monic_f.map _, by rw [← aeval_def, hev]; exact hmap.1⟩
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly (ResidueField A) xb).Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hirr]
    intro h0
    obtain ⟨h, hh⟩ := minpoly.dvd (ResidueField A) xb (p := fb) (by rw [hev]; exact hmap.1)
    have : aeval xb (derivative fb) = 0 := by
      rw [hh, derivative_mul, h0]; simp
    rw [show derivative fb = (derivative P.f).map (residue A) from derivative_map _ _,
      hev] at this
    rw [this] at hder; exact not_isUnit_zero hder
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ (minpoly.degree_pos hint).ne' hsep
  have hd0 : X - C a0 ∣ minpoly (ResidueField A) xb := dvd_iff_isRoot.2 ha0
  have hdvd : minpoly (ResidueField A) xb ∣ X - C a0 :=
    Irreducible.dvd_symm (irreducible_X_sub_C a0) hirr hd0
  obtain ⟨a00, ha00⟩ := residue_surjective a0
  have hxb : xb = algebraMap A K a00 := by
    have h1 : aeval xb (X - C a0) = 0 := by
      obtain ⟨c, hc⟩ := hdvd; rw [hc, map_mul, minpoly.aeval, zero_mul]
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1, ← ha00]; exact hi a00
  have hzero : ∀ a : A, algebraMap A K a = 0 → a ∈ maximalIdeal A := by
    intro a ha; by_contra hn
    have := ((mem_maximalIdeal a).not.1 hn |> not_not.1).map (algebraMap A K)
    rw [ha] at this; exact not_isUnit_zero this
  have hev' : ∀ q : A[X], algebraMap A K (q.eval a00) = aeval xb q := by
    intro q; rw [hxb, aeval_algebraMap_apply, coe_aeval_eq_eval]
  obtain ⟨r, hr, hra⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a00
    (hzero _ (by rw [hev']; exact hmap.1)) (isUnit_of_map _ hkill (by rw [hev']; exact hder))
  have hrK : algebraMap A K r = xb := by
    rw [hxb, ← sub_eq_zero, ← map_sub]; exact hkill _ hra
  have hr' : P.HasMap r := by
    refine ⟨by rw [coe_aeval_eq_eval]; exact hr, isUnit_of_map _ hkill ?_⟩
    rw [← aeval_algebraMap_apply, hrK]; exact hmap.2
  exact ⟨((P.lift r hr').comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom A B S)⟩

/- English proof (translation)
Introduce `A _ hA Y f hf hsurj`. Take `⟨hH, hsc⟩` from `hA`. Take `⟨y, hy⟩` from `hsurj.surj (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))`. Set `𝒰` to `Y.affineOpenCover`. Set `j` to `𝒰.idx y`.

Take `⟨y', hy'⟩` from `𝒰.covers y`. Set `g` to `𝒰.f j`. Set `φ : CommRingCat.of A ⟶ 𝒰.X j` to `Spec.preimage (g ≫ f)`. Establish `hφ : Spec.map φ = g ≫ f` using `Spec.map_preimage _`. Establish `het : φ.hom.Etale`.

Rewrite using `[← HasRingHomProperty.Spec_iff (P := @Etale), hφ]`. Use `infer_instance`. Use `algebraize [φ.hom]`. Establish `hpt : (Spec.map φ) y' = IsLocalRing.closedPoint A`. Rewrite using `[hφ, Scheme.Hom.comp_apply]`.

Simplify using `only [g, j] at hy' ⊢`. Rewrite using `[hy', hy]`. Establish `hQ : y'.asIdeal.comap (algebraMap A (𝒰.X j)) = IsLocalRing.maximalIdeal A`. Use `congrArg PrimeSpectrum.asIdeal hpt` as an intermediate fact. Conclude with `this`.

Establish `: y'.asIdeal.IsPrime` using `PrimeSpectrum.isPrime y'`. Take `⟨ψ⟩` from `alg_sect A (𝒰.X j) y'.asIdeal hQ`. Use `⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`. Use `Spec.map_id (CommRingCat.of A)` and compare the differences between its conclusion and the goal.

Use extensionality with `a`. Conclude with `ψ.commutes a`.
-/
theorem ShSect_of : LateralTheory.KummerTheory.SecSHPf.ShSect := by
  intro A _ hA Y f hf hsurj
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨y, hy⟩ := hsurj.surj (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  let 𝒰 := Y.affineOpenCover
  let j := 𝒰.idx y
  obtain ⟨y', hy'⟩ := 𝒰.covers y
  let g := 𝒰.f j
  let φ : CommRingCat.of A ⟶ 𝒰.X j := Spec.preimage (g ≫ f)
  have hφ : Spec.map φ = g ≫ f := Spec.map_preimage _
  have het : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  algebraize [φ.hom]
  have hpt : (Spec.map φ) y' = IsLocalRing.closedPoint A := by
    rw [hφ, Scheme.Hom.comp_apply]
    simp only [g, j] at hy' ⊢
    rw [hy', hy]
  have hQ : y'.asIdeal.comap (algebraMap A (𝒰.X j)) = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal hpt
    exact this
  have : y'.asIdeal.IsPrime := PrimeSpectrum.isPrime y'
  obtain ⟨ψ⟩ := alg_sect A (𝒰.X j) y'.asIdeal hQ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of A)
  ext a
  exact ψ.commutes a

end LateralTheory.KummerTheory.ShSectPf
