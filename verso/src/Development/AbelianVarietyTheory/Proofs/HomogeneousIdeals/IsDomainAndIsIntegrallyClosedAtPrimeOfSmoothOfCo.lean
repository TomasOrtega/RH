import Mathlib

open TensorProduct

universe u

namespace GlobalTheory

/- English proof (translation)
Establish `hq : (p.map (algebraMap B T)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint M T p hp hM`. Establish `hc : (p.map (algebraMap B T)).comap (algebraMap B T) = p` using `IsLocalization.comap_map_of_isPrime_disjoint M T hp hM`. Establish `h1` using `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime (p.map (algebraMap B T))) (p.map (algebraMap B T))`. Establish `h2 : IsLocalization p.primeCompl (Localization.AtPrime (p.map (algebraMap B T)))`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using `[Ideal.primeCompl, hc]`. Take `⟨h3, h4⟩` from `h (p.map (algebraMap B T))`. Set `e : Localization.AtPrime (p.map (algebraMap B T)) ≃ₐ[B] Bp` to `IsLocalization.algEquiv p.primeCompl _ _`. Conclude with `⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩`.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization {B : Type*} [CommRing B]
    (M : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    (p : Ideal B) [hp : p.IsPrime] (hM : Disjoint (M : Set B) (p : Set B))
    (h : ∀ (q : Ideal T) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  have hq : (p.map (algebraMap B T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T p hp hM
  have hc : (p.map (algebraMap B T)).comap (algebraMap B T) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M T hp hM
  have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime (p.map (algebraMap B T))) (p.map (algebraMap B T))
  have h2 : IsLocalization p.primeCompl (Localization.AtPrime (p.map (algebraMap B T))) := by
    convert h1 using 1
    ext x
    simp [Ideal.primeCompl, hc]
  obtain ⟨h3, h4⟩ := h (p.map (algebraMap B T))
  let e : Localization.AtPrime (p.map (algebraMap B T)) ≃ₐ[B] Bp :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocalization.isDomain_of_le_nonZeroDivisors Bp p.primeCompl_le_nonZeroDivisors, isIntegrallyClosed_of_isLocalization Bp p.primeCompl p.primeCompl_le_nonZeroDivisors⟩`.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_isDomain {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors Bp p.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization Bp p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap B (Π i, K i))` using `(isIntegrallyClosedIn_iff.mp hB).1`. Set `φ (i : ι) : B →+* K i` to `(Pi.evalRingHom K i).comp (algebraMap B (Π i, K i))`. Establish `key (i : ι) (x : K i) (hx : (φ i).IsIntegralElem x) : ∃ b : B, algebraMap B (Π i, K i) b = Pi.single i x`. Apply `IsIntegrallyClosedIn.algebraMap_eq_of_integral` to reduce the goal to its premises.

Take `⟨f, hf, hfx⟩` from `hx`. Use `⟨Polynomial.X * f, Polynomial.monic_X.mul hf, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_mul, Polynomial.eval₂_X]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Establish `: (Polynomial.eval₂ (algebraMap B (Π i, K i)) (Pi.single j x) f) j = 0`. Use `Polynomial.hom_eval₂ f (algebraMap B (Π i, K i)) (Pi.evalRingHom K j) (Pi.single j x)` as an intermediate fact. Simplify `this.trans (by simpa [φ] using hfx)` using `[φ]`. Simplify using `[this]`.

Simplify using `[hj]`. Use `choose e he using fun i ↦ key i 1 (RingHom.isIntegralElem_one _)`. Establish `hsum : ∑ i, e i = 1`. Apply `hinj` to reduce the goal to its premises. Simplify using `[he, Finset.univ_sum_single, ← Pi.one_def]`.

Take `⟨i, hi⟩ : ∃ i, e i ∉ p` from `by by_contra! H`. Conclude with `hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hsum ▸ p.sum_mem fun i _ ↦ H i))`. Set `D` to `(φ i).range`. Use `letI : Algebra B D := (φ i).rangeRestrict.toAlgebra`. Establish `hsurj : Function.Surjective (algebraMap B D)` using `(φ i).rangeRestrict_surjective`.

Establish `hidem : IsIdempotentElem (e i)`. Apply `hinj` to reduce the goal to its premises. Simplify using `[he, ← Pi.single_mul]`. Establish `: IsLocalization.Away (e i) D`. Use `IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y ↦ ?_) hsurj` and prove the remaining obligations.

Rewrite using `[Subtype.ext_iff, ← hinj.eq_iff, map_mul, map_mul, he]`. Express the relevant statement in the definitionally equal form `algebraMap B (Π i, K i) x i = algebraMap B (Π i, K i) y i ↔ _`. Use `⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ by simpa using congrFun h i⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[h]`. Simplify using `[hj]`. Establish `: IsIntegrallyClosedIn D (K i)`. Rewrite using `[Subring.isIntegrallyClosedIn_iff]`. Introduce `x hx`.

Use `letI : Algebra B (K i) := (φ i).toAlgebra`. Establish `: IsScalarTower B D (K i)` using `.of_algebraMap_eq fun _ ↦ rfl`. Establish `: Algebra.IsIntegral B D` using `Algebra.isIntegral_of_surjective hsurj`. Take `⟨b, hb⟩` from `key i x (isIntegral_trans x hx)`. Conclude with `⟨b, by simp [φ, hb]⟩`.

Establish `: IsIntegrallyClosed D` using `IsIntegrallyClosed.of_isIntegrallyClosedIn D (K i)`. Use `isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers (e i)) D p ?_ (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_isDomain q _) Bp` and prove the remaining obligations. Rewrite using `[Ideal.disjoint_powers_iff_notMem_of_isPrime]` and apply the resulting hypothesis.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi {B : Type*} [CommRing B]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)] [Algebra B (Π i, K i)]
    [hB : IsIntegrallyClosedIn B (Π i, K i)] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  classical
  have := Fintype.ofFinite ι
  have hinj : Function.Injective (algebraMap B (Π i, K i)) := (isIntegrallyClosedIn_iff.mp hB).1
  let φ (i : ι) : B →+* K i := (Pi.evalRingHom K i).comp (algebraMap B (Π i, K i))
  have key (i : ι) (x : K i) (hx : (φ i).IsIntegralElem x) :
      ∃ b : B, algebraMap B (Π i, K i) b = Pi.single i x := by
    apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
    obtain ⟨f, hf, hfx⟩ := hx
    refine ⟨Polynomial.X * f, Polynomial.monic_X.mul hf, ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
    funext j
    by_cases hj : j = i
    · subst hj
      have : (Polynomial.eval₂ (algebraMap B (Π i, K i)) (Pi.single j x) f) j = 0 := by
        have := Polynomial.hom_eval₂ f (algebraMap B (Π i, K i)) (Pi.evalRingHom K j)
          (Pi.single j x)
        simpa [φ] using this.trans (by simpa [φ] using hfx)
      simp [this]
    · simp [hj]
  choose e he using fun i ↦ key i 1 (RingHom.isIntegralElem_one _)
  have hsum : ∑ i, e i = 1 := by
    apply hinj
    simp [he, Finset.univ_sum_single, ← Pi.one_def]
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ p := by
    by_contra! H
    exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hsum ▸ p.sum_mem fun i _ ↦ H i))
  let D := (φ i).range
  letI : Algebra B D := (φ i).rangeRestrict.toAlgebra
  have hsurj : Function.Surjective (algebraMap B D) := (φ i).rangeRestrict_surjective
  have hidem : IsIdempotentElem (e i) := by
    apply hinj
    simp [he, ← Pi.single_mul]
  have : IsLocalization.Away (e i) D := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y ↦ ?_) hsurj
    rw [Subtype.ext_iff, ← hinj.eq_iff, map_mul, map_mul, he]
    change algebraMap B (Π i, K i) x i = algebraMap B (Π i, K i) y i ↔ _
    refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ by simpa using congrFun h i⟩
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [hj]
  have : IsIntegrallyClosedIn D (K i) := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    letI : Algebra B (K i) := (φ i).toAlgebra
    have : IsScalarTower B D (K i) := .of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.IsIntegral B D := Algebra.isIntegral_of_surjective hsurj
    obtain ⟨b, hb⟩ := key i x (isIntegral_trans x hx)
    exact ⟨b, by simp [φ, hb]⟩
  have : IsIntegrallyClosed D := IsIntegrallyClosed.of_isIntegrallyClosedIn D (K i)
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers (e i)) D p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_isDomain q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

/- English proof (translation)
Take `⟨hinj, hcl⟩` from `isIntegrallyClosedIn_iff.mp hL`. Use `isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx ↦ ?_⟩` and prove the remaining obligations. Conclude with `Algebra.TensorProduct.includeLeft_injective (S := A) hinj`. Take `⟨y, hy⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := A) (S := B) (B := L)).2 ⟨x, hx⟩`. Establish `hy' : Algebra.TensorProduct.map (.id B B) (integralClosure A L).val y = x` using `congrArg Subtype.val hy`.

Substitute `hy'` using the available equality. Use `clear hx hy`. Proceed by induction on `y with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [map_add, map_add, ha, hb]⟩`. Consider the case `tmul b y`. Take `⟨a, ha⟩` from `hcl y.2`.

Use `⟨a • b, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply, Subalgebra.coe_val, ← ha, Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul]`. Both sides reduce to the same expression.
-/
theorem isIntegrallyClosedIn_tensor_of_smooth {A B L : Type*} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A B] [Algebra A L] [Algebra.Smooth A B] [hL : IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by
  obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp hL
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx ↦ ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := A) hinj
  · obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := A) (S := B) (B := L)).2 ⟨x, hx⟩
    have hy' : Algebra.TensorProduct.map (.id B B) (integralClosure A L).val y = x :=
      congrArg Subtype.val hy
    subst hy'
    clear hx hy
    induction y with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | tmul b y =>
      obtain ⟨a, ha⟩ := hcl y.2
      refine ⟨a • b, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply,
        Subalgebra.coe_val, ← ha, Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul]
      rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm`. Consider the case `succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv`.
-/
theorem isIntegrallyClosed_mvPolynomial_fin (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm
  | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv

/- English proof (translation)
Set `L` to `FractionRing A`. Establish `h1 : IsIntegrallyClosedIn B (B ⊗[A] L)` using `isIntegrallyClosedIn_tensor_of_smooth`. Use `Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)` as an intermediate fact. Use `Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[A] B)` as an intermediate fact. Establish `: IsArtinianRing (L ⊗[A] B)` using `isArtinian_of_tower L inferInstance`.

Set `e` to `(Algebra.TensorProduct.comm A B L).toRingEquiv`. Establish `: IsArtinianRing (B ⊗[A] L)` using `e.symm.isArtinianRing`. Establish `: IsReduced (B ⊗[A] L)` using `isReduced_of_injective e e.injective`. Use `letI (m : MaximalSpectrum (B ⊗[A] L)) : Field ((B ⊗[A] L) ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal`. Use `(((IsArtinianRing.equivPi (B ⊗[A] L)).restrictScalars B).isIntegrallyClosedIn).mp h1` as an intermediate fact.

Conclude with `isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi (fun m : MaximalSpectrum (B ⊗[A] L) ↦ (B ⊗[A] L) ⧸ m.asIdeal) p Bp`.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_etale (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let L := FractionRing A
  have h1 : IsIntegrallyClosedIn B (B ⊗[A] L) := isIntegrallyClosedIn_tensor_of_smooth
  have := Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)
  have := Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[A] B)
  have : IsArtinianRing (L ⊗[A] B) := isArtinian_of_tower L inferInstance
  let e := (Algebra.TensorProduct.comm A B L).toRingEquiv
  have : IsArtinianRing (B ⊗[A] L) := e.symm.isArtinianRing
  have : IsReduced (B ⊗[A] L) := isReduced_of_injective e e.injective
  letI (m : MaximalSpectrum (B ⊗[A] L)) : Field ((B ⊗[A] L) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have := (((IsArtinianRing.equivPi (B ⊗[A] L)).restrictScalars B).isIntegrallyClosedIn).mp h1
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
    (fun m : MaximalSpectrum (B ⊗[A] L) ↦ (B ⊗[A] L) ⧸ m.asIdeal) p Bp

/- English proof (translation)
Take `⟨f, hfm, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)`. Use `isIntegrallyClosed_mvPolynomial_fin A n` as an intermediate fact. Use `isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f) (Localization.Away f) p ?_ (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) Bp` and prove the remaining obligations. Rewrite using `[Ideal.disjoint_powers_iff_notMem_of_isPrime]` and apply the resulting hypothesis.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨f, hfm, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

/- English proof (translation)
Set `M` to `(p.comap (algebraMap A B)).primeCompl`. Use `letI : Algebra B (Ap ⊗[A] B) := Algebra.TensorProduct.rightAlgebra`. Establish `: IsLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B)` using `IsLocalization.tensorRight _ _`. Use `isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) p ?_ (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_smooth Ap q _) Bp` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `_ ⟨a, ha, rfl⟩ h`. Conclude with `ha h`.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] (p : Ideal B) [hp : p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap (p.comap (algebraMap A B))] [IsDomain Ap] [IsIntegrallyClosed Ap]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let M := (p.comap (algebraMap A B)).primeCompl
  letI : Algebra B (Ap ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) :=
    IsLocalization.tensorRight _ _
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
    (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_smooth Ap q _) Bp
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha h

/- English proof (translation)
Take `⟨_, _⟩` from `hA (p.comap (algebraMap A B))`. Conclude with `isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := A) p (Localization.AtPrime (p.comap (algebraMap A B))) Bp`.
-/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (hA : ∀ (q : Ideal A) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨_, _⟩ := hA (p.comap (algebraMap A B))
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := A) p
    (Localization.AtPrime (p.comap (algebraMap A B))) Bp

/- English proof (translation)
The claim follows from `IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦ (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p _).2`.
-/
theorem isIntegrallyClosed_of_smooth (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] [IsDomain B] :
    IsIntegrallyClosed B :=
  IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦
    (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p _).2

/- English proof (translation)
The claim follows from `isReduced_ofLocalizationMaximal B fun p _ ↦ have := (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p (Localization.AtPrime p)).1 inferInstance`.
-/
theorem isReduced_of_smooth_of_isIntegrallyClosed (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] : IsReduced B :=
  isReduced_ofLocalizationMaximal B fun p _ ↦
    have := (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p (Localization.AtPrime p)).1
    inferInstance

open AlgebraicGeometry in

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, -⟩` from `Smooth.exists_isStandardSmooth f x`. Establish `hs` using `f.smooth_appLE hU hV e`. Use `algebraize [(f.appLE U V e).hom]`. Use `letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)`. Use `letI := Y.presheaf.algebra_section_stalk (⟨f x, e hx⟩ : U)`.

Establish `h1` using `hV.isLocalization_stalk ⟨x, hx⟩`. Establish `h2` using `hU.isLocalization_stalk ⟨f x, e hx⟩`. Establish `h3 : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) = (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal` using `congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hx)`. Establish `h4 : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)))`. Use `h2` and compare the differences between its conclusion and the goal.

Conclude with `isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := Γ(Y, U)) (hV.primeIdealOf ⟨x, hx⟩).asIdeal (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)`.
-/
theorem isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) [IsDomain (Y.presheaf.stalk (f x))] [IsIntegrallyClosed (Y.presheaf.stalk (f x))] :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, e, -⟩ := Smooth.exists_isStandardSmooth f x
  have hs := f.smooth_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  letI := Y.presheaf.algebra_section_stalk (⟨f x, e hx⟩ : U)
  have h1 := hV.isLocalization_stalk ⟨x, hx⟩
  have h2 := hU.isLocalization_stalk ⟨f x, e hx⟩
  have h3 : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) =
      (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hx)
  have h4 : IsLocalization.AtPrime (Y.presheaf.stalk (f x))
      ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V))) := by
    convert h2
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

open AlgebraicGeometry in

/- English proof (translation)
The claim follows from `have := (hY (f x)).1 have := (hY (f x)).2 isDomain_and_isIntegrallyClosed_stalk_of_smooth f x`.
-/
theorem forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := (hY (f x)).1
  have := (hY (f x)).2
  isDomain_and_isIntegrallyClosed_stalk_of_smooth f x

end GlobalTheory
