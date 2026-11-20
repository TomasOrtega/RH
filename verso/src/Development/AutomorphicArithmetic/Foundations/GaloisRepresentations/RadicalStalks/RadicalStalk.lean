import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverFieldStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

/- English proof (translation)
Use `letI : Field (R ⧸ m) := Ideal.Quotient.field m`. Use `haveI : _root_.IsReduced ((R ⧸ m) ⊗[R] B) := GlobalTheory.T.isReduced_of_smooth_over_field' (R ⧸ m) _`. Establish `e` using `Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m`. Use `haveI : _root_.IsReduced (B ⧸ m.map (algebraMap R B)) := isReduced_of_injective e.toRingEquiv.toRingHom e.injective`. Conclude with `(Ideal.isRadical_iff_quotient_reduced _).mpr this`.
-/
private theorem radical_quot (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (m : Ideal R) [m.IsMaximal] : (m.map (algebraMap R B)).IsRadical := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : _root_.IsReduced ((R ⧸ m) ⊗[R] B) := GlobalTheory.T.isReduced_of_smooth_over_field' (R ⧸ m) _
  have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
  haveI : _root_.IsReduced (B ⧸ m.map (algebraMap R B)) :=
    isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr this

/- English proof (translation)
Introduce `a ⟨n, hn⟩`. Establish `hn' : a ^ (n + 1) ∈ I.map (algebraMap B A)`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_right _ _ hn`. Take `⟨b, u, rfl⟩` from `IsLocalization.exists_mk'_eq M a`.

Take `⟨⟨i, t⟩, ht⟩` from `(IsLocalization.mem_map_algebraMap_iff M A).mp hn'`. Establish `hu : IsLocalization.mk' A b u * algebraMap B A u = algebraMap B A b` using `IsLocalization.mk'_spec A b u`. Establish `e1 : algebraMap B A (b ^ (n + 1) * t) = algebraMap B A (i * u ^ (n + 1))`. Simplify using `only [map_mul, map_pow]`. Rewrite using `[← ht, ← hu]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨d, hd⟩` from `IsLocalization.exists_of_eq (M := M) e1`. Establish `hy : (d : B) * t * b ∈ I`. Apply `hI` to reduce the goal to its premises. Use `⟨n + 1, ?_⟩` and prove the remaining obligations.

Establish `e2 : ((d : B) * t * b) ^ (n + 1) = ((d : B) * t) ^ n * ((d : B) * (b ^ (n + 1) * t))` using `by ring`. Rewrite using `[e2, hd]`. Conclude with `I.mul_mem_left _ (I.mul_mem_left _ (I.mul_mem_right _ i.2))`. Use `(IsLocalization.mem_map_algebraMap_iff M A).mpr ⟨⟨⟨_, hy⟩, u * d * t⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.coe_mul, map_mul]`.

Rewrite using `[← hu]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem radical_loc (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (M : Submonoid B)
    [IsLocalization M A] (I : Ideal B) (hI : I.IsRadical) : (I.map (algebraMap B A)).IsRadical := by
  intro a ⟨n, hn⟩
  have hn' : a ^ (n + 1) ∈ I.map (algebraMap B A) := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hn
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq M a
  obtain ⟨⟨i, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hn'
  have hu : IsLocalization.mk' A b u * algebraMap B A u = algebraMap B A b := IsLocalization.mk'_spec A b u
  have e1 : algebraMap B A (b ^ (n + 1) * t) = algebraMap B A (i * u ^ (n + 1)) := by
    simp only [map_mul, map_pow]
    rw [← ht, ← hu]
    ring
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) e1
  have hy : (d : B) * t * b ∈ I := by
    apply hI
    refine ⟨n + 1, ?_⟩
    have e2 : ((d : B) * t * b) ^ (n + 1) = ((d : B) * t) ^ n * ((d : B) * (b ^ (n + 1) * t)) := by ring
    rw [e2, hd]
    exact I.mul_mem_left _ (I.mul_mem_left _ (I.mul_mem_right _ i.2))
  refine (IsLocalization.mem_map_algebraMap_iff M A).mpr
    ⟨⟨⟨_, hy⟩, u * d * t⟩, ?_⟩
  simp only [Submonoid.coe_mul, map_mul]
  rw [← hu]
  ring

/- English proof (translation)
Take `⟨U, hU, hzU, -⟩` from `exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial`. Establish `hsm : Smooth (hU.fromSpec ≫ s)` using `inferInstance`. Take `⟨ρ, hρ⟩` from `Spec.map_surjective (hU.fromSpec ≫ s)`. Establish `hρs : ρ.hom.Smooth`. Rewrite `hsm` using `[← hρ]`.

Conclude with `(HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm`. Establish `e : r = ρ ≫ X.presheaf.germ U z hzU`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[hr, Spec.map_comp, hρ, ← hU.fromSpecStalk_eq_fromSpecStalk hzU]`. Simplify using `[IsAffineOpen.fromSpecStalk]`.

Use `letI := ρ.hom.toAlgebra`. Use `haveI : Algebra.Smooth R Γ(X, U) := hρs`. Establish `h1` using `radical_quot R Γ(X, U) m`. Use `letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra`. Use `haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := hU.isLocalization_stalk ⟨z, hzU⟩`.

Establish `h2` using `radical_loc Γ(X, U) (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _ h1`. Rewrite `h2` using `[Ideal.map_map]`. Rewrite using `[e]`. Conclude with `h2`.
-/
private theorem radical_stalk (R : Type) [CommRing R] (m : Ideal R) [m.IsMaximal] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X) (r : CommRingCat.of R ⟶ X.presheaf.stalk z)
    (hr : Spec.map r = X.fromSpecStalk z ≫ s) : (m.map r.hom).IsRadical := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hsm : Smooth (hU.fromSpec ≫ s) := inferInstance
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hρs : ρ.hom.Smooth := by
    rw [← hρ] at hsm
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm
  have e : r = ρ ≫ X.presheaf.germ U z hzU := by
    apply Spec.map_injective
    rw [hr, Spec.map_comp, hρ, ← hU.fromSpecStalk_eq_fromSpecStalk hzU]
    simp [IsAffineOpen.fromSpecStalk]
  letI := ρ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, U) := hρs
  have h1 := radical_quot R Γ(X, U) m
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have h2 := radical_loc Γ(X, U) (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _ h1
  rw [Ideal.map_map] at h2
  rw [e]
  exact h2

/- English proof (translation)
Take `⟨r, hr⟩` from `Spec.map_surjective (X.fromSpecStalk z ≫ s)`. Establish `hrc : r ≫ φ = CommRingCat.ofHom c`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hr, h]`. Establish `hrad` using `radical_stalk R (IsLocalRing.maximalIdeal R) X s z r hr`.

Establish `hprime : ∀ P : Ideal (X.presheaf.stalk z), P.IsPrime → (IsLocalRing.maximalIdeal R).map r.hom ≤ P → P = IsLocalRing.maximalIdeal (X.presheaf.stalk z)`. Introduce `P hP hJ`. Set `y : Spec (X.presheaf.stalk z)` to `⟨P, hP⟩`. Establish `h1 : X.fromSpecStalk z y ⤳ z`. Establish `: X.fromSpecStalk z y ∈ Set.range (X.fromSpecStalk z)` using `⟨y, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Establish `h2 : s.base (X.fromSpecStalk z y) = IsLocalRing.closedPoint R`. Establish `e : s.base (X.fromSpecStalk z y) = (Spec.map r).base y` using `by rw [hr]; rfl`. Rewrite using `[e]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Establish `hle : IsLocalRing.maximalIdeal R ≤ P.comap r.hom` using `Ideal.map_le_iff_le_comap.mp hJ`. Conclude with `((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap r.hom).ne_top hle).symm`. Establish `h3` using `hmax _ h2 h1`. Establish `h4 : y = IsLocalRing.closedPoint (X.presheaf.stalk z)` using `(X.fromSpecStalk z).isEmbedding.injective (h3.trans Scheme.fromSpecStalk_closedPoint.symm)`. Conclude with `congrArg PrimeSpectrum.asIdeal h4`.

Introduce `x hx`. Establish `hxJ : x ∈ (IsLocalRing.maximalIdeal R).map r.hom`. Apply `hrad` to reduce the goal to its premises. Rewrite using `[Ideal.radical_eq_sInf]`. Use `Ideal.mem_sInf.mpr fun {P} hP => ?_` and prove the remaining obligations.

Rewrite using `[hprime P hP.2 hP.1]`. Conclude with `hx`. Establish `hker : (IsLocalRing.maximalIdeal R).map r.hom ≤ RingHom.ker φ.hom`. Use `Ideal.map_le_iff_le_comap.mpr fun y hy => ?_` and prove the remaining obligations. Establish `e : φ.hom (r.hom y) = c y` using `congrArg (fun f => f.hom y) hrc`.

Conclude with `(RingHom.mem_ker).mpr (e.trans (hc y hy))`. Conclude with `hker hxJ`.
-/
private theorem kills_max (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X)
    (hmax : ∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z)
    (T : Type) [CommRing T] (φ : X.presheaf.stalk z ⟶ CommRingCat.of T) (c : R →+* T)
    (h : Spec.map φ ≫ X.fromSpecStalk z ≫ s = Spec.map (CommRingCat.ofHom c))
    (hc : ∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) :
    ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z), φ.hom x = 0 := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (X.fromSpecStalk z ≫ s)
  have hrc : r ≫ φ = CommRingCat.ofHom c := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr, h]
  have hrad := radical_stalk R (IsLocalRing.maximalIdeal R) X s z r hr
  have hprime : ∀ P : Ideal (X.presheaf.stalk z), P.IsPrime →
      (IsLocalRing.maximalIdeal R).map r.hom ≤ P → P = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    intro P hP hJ
    let y : Spec (X.presheaf.stalk z) := ⟨P, hP⟩
    have h1 : X.fromSpecStalk z y ⤳ z := by
      have : X.fromSpecStalk z y ∈ Set.range (X.fromSpecStalk z) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : s.base (X.fromSpecStalk z y) = IsLocalRing.closedPoint R := by
      have e : s.base (X.fromSpecStalk z y) = (Spec.map r).base y := by rw [hr]; rfl
      rw [e]
      apply PrimeSpectrum.ext
      have hle : IsLocalRing.maximalIdeal R ≤ P.comap r.hom := Ideal.map_le_iff_le_comap.mp hJ
      exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap r.hom).ne_top hle).symm
    have h3 := hmax _ h2 h1
    have h4 : y = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      (X.fromSpecStalk z).isEmbedding.injective (h3.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  intro x hx
  have hxJ : x ∈ (IsLocalRing.maximalIdeal R).map r.hom := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun {P} hP => ?_
    rw [hprime P hP.2 hP.1]
    exact hx
  have hker : (IsLocalRing.maximalIdeal R).map r.hom ≤ RingHom.ker φ.hom := by
    refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    have e : φ.hom (r.hom y) = c y := congrArg (fun f => f.hom y) hrc
    exact (RingHom.mem_ker).mpr (e.trans (hc y hy))
  exact hker hxJ

end UpperTheory.Gal.Ord

/- English proof (translation)
Introduce `R _ _ _ X s _ z _ hmax T _ _ v c hv hvs hc`. Substitute `hv` using the available equality. Establish `hφ : Spec.map (Scheme.stalkClosedPointTo (R` using `CommRingCat.of T) v) ≫ X.fromSpecStalk _ = v := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of T) v`. Establish `hk` using `kills_max R X s _ hmax T (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) c (by rw [← Category.assoc, hφ]; exact hvs) hc`. Use `⟨Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk, ?_⟩` and prove the remaining obligations.

Establish `e : X.residue _ ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R` using `CommRingCat.of T) v).hom hk) = Scheme.stalkClosedPointTo (R := CommRingCat.of T) v := by`. Use extensionality with `x`. Both sides reduce to the same expression. Use `show Spec.map _ ≫ Spec.map (X.residue _) ≫ X.fromSpecStalk _ = v`. Rewrite using `[← Spec.map_comp_assoc]`.

Conclude with `(congrArg (fun g => Spec.map g ≫ X.fromSpecStalk _) e).trans hφ`.
-/
theorem UpperTheory.Gal.Ord.gen :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] (z : X), s.base z = IsLocalRing.closedPoint R →
      (∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (T : Type) [CommRing T] [IsLocalRing T] (v : Sp T ⟶ X) (c : R →+* T),
      v.base (IsLocalRing.closedPoint T) = z → v ≫ s = spMap c → (∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) →
      ∃ τ : X.residueField z →+* T, spMap τ ≫ X.fromSpecResidueField z = v := by
  intro R _ _ _ X s _ z _ hmax T _ _ v c hv hvs hc
  subst hv
  have hφ : Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) ≫ X.fromSpecStalk _ = v :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of T) v
  have hk := kills_max R X s _ hmax T (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) c
    (by rw [← Category.assoc, hφ]; exact hvs) hc
  refine ⟨Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk, ?_⟩
  have e : X.residue _ ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk) =
      Scheme.stalkClosedPointTo (R := CommRingCat.of T) v := by
    ext x
    rfl
  show Spec.map _ ≫ Spec.map (X.residue _) ≫ X.fromSpecStalk _ = v
  rw [← Spec.map_comp_assoc]
  exact (congrArg (fun g => Spec.map g ≫ X.fromSpecStalk _) e).trans hφ
