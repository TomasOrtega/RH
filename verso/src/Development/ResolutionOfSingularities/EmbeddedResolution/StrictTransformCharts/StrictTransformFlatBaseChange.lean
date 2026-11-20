import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SaturationByPowers
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable def saturationByPowers {A : Type*} [CommRing A] (J : Ideal A) (a : A) : Ideal A :=
  _root_.UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers J a

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_saturationByPowers_iff {A : Type*} [CommRing A] (J : Ideal A) (a x : A) :
    x ∈ saturationByPowers J a ↔ ∃ n : ℕ, a ^ n * x ∈ J := Iff.rfl

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce and unpack `x ⟨n, hn⟩`. Rewrite using `[Ideal.mem_comap, mem_saturationByPowers_iff]`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h` using `Ideal.mem_map_of_mem (algebraMap A B) hn`.

Rewrite `h` using `[map_mul, map_pow]`. Then use the resulting hypothesis.
-/
private theorem map_saturationByPowers_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (a : A) :
    (saturationByPowers J a).map (algebraMap A B) ≤
      saturationByPowers (J.map (algebraMap A B)) (algebraMap A B a) := by
  rw [Ideal.map_le_iff_le_comap]
  rintro x ⟨n, hn⟩
  rw [Ideal.mem_comap, mem_saturationByPowers_iff]
  refine ⟨n, ?_⟩
  have h := Ideal.mem_map_of_mem (algebraMap A B) hn
  rwa [map_mul, map_pow] at h

/- English proof (translation)
Use `le_antisymm (map_saturationByPowers_le J a) ?_` and prove the remaining obligations. Introduce and unpack `y ⟨n, hy⟩`. Take `⟨u, hu⟩ : ∃ u : A →ₗ[A] (A ⧸ J), u = J.mkQ ∘ₗ LinearMap.lsmul A A (a ^ n)` from `⟨_, rfl⟩`. Establish `hker : ∀ c : A, u c = 0 ↔ a ^ n * c ∈ J`. Introduce `c`.

Rewrite using `[hu, LinearMap.comp_apply, LinearMap.lsmul_apply, Submodule.mkQ_apply, smul_eq_mul, Submodule.Quotient.mk_eq_zero]`. Establish `hex : Function.Exact (LinearMap.ker u).subtype u`. Introduce `c`. Prove the components needed by the constructor for the conclusion. Introduce `hc`.

Conclude with `⟨⟨c, hc⟩, rfl⟩`. Introduce and unpack `⟨⟨c, hc⟩, rfl⟩`. Conclude with `hc`. Establish `hflat : Function.Exact (LinearMap.lTensor B (LinearMap.ker u).subtype) (LinearMap.lTensor B u)` using `Module.Flat.lTensor_exact B hex`. Establish `key : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = 0`.

Establish `hmapJ : (Ideal.map (algebraMap A B) J : Ideal B) = Ideal.span (⇑(algebraMap A B) '' (J : Set A))` using `rfl`. Rewrite `hy` using `[hmapJ]`. Take `⟨k, cf, gg, hsum⟩` from `Submodule.mem_span_set'.1 hy`. Establish `hgg : ∀ i, ∃ c : A, c ∈ J ∧ algebraMap A B c = (gg i : B)`. Introduce `i`.

Take `⟨c, hc1, hc2⟩` from `(gg i).2`. Conclude with `⟨c, hc1, hc2⟩`. Use `choose c hcJ hcmap using hgg`. Establish `e1 : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = y ⊗ₜ[A] (J.mkQ (a ^ n))`. Rewrite using `[LinearMap.lTensor_tmul, hu]`.

Simplify using the standard rewrite rules. Establish `e2 : (J.mkQ (a ^ n) : A ⧸ J) = (a ^ n) • (J.mkQ (1 : A))`. Rewrite using `[← map_smul]`. Simplify using the standard rewrite rules. Establish `e3 : algebraMap A B (a ^ n) * y = ∑ i, c i • cf i`.

Rewrite using `[map_pow, ← hsum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hcmap i, smul_eq_mul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, ← TensorProduct.smul_tmul, Algebra.smul_def, e3, TensorProduct.sum_tmul]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul]`. Establish `hz : (c i) • (J.mkQ (1 : A)) = 0`. Establish `hz1 : (c i) • (J.mkQ (1 : A)) = J.mkQ (c i)`. Rewrite using `[← map_smul, smul_eq_mul, mul_one]`.

Rewrite using `[hz1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hcJ i`. Rewrite using `[hz, TensorProduct.tmul_zero]`. Take `⟨w, hw⟩` from `(hflat (y ⊗ₜ[A] (1 : A))).1 key`. Establish `main : ∀ z : TensorProduct A B (LinearMap.ker u), TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype z) ∈ (saturationByPowers J a).map (algebraMap A B)`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b cc`. Establish `hcc : (cc : A) ∈ saturationByPowers J a` using `⟨n, (hker _).1 cc.2⟩`.

Establish `h2 : algebraMap A B (cc : A) * b ∈ (saturationByPowers J a).map (algebraMap A B)` using `Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem (algebraMap A B) hcc)`. Simplify `h2` using `[Algebra.smul_def]`. Consider the case `add z₁ z₂ h₁ h₂`. Rewrite using `[map_add, map_add]`. Conclude with `Ideal.add_mem _ h₁ h₂`.

Establish `hy2 : y = TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype w)`. Rewrite using `[hw]`. Simplify using the standard rewrite rules. Rewrite using `[hy2]`. Conclude with `main w`.
-/
theorem map_saturationByPowers_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J : Ideal A) (a : A) :
    (saturationByPowers J a).map (algebraMap A B) =
      saturationByPowers (J.map (algebraMap A B)) (algebraMap A B a) := by
  refine le_antisymm (map_saturationByPowers_le J a) ?_
  rintro y ⟨n, hy⟩
  obtain ⟨u, hu⟩ : ∃ u : A →ₗ[A] (A ⧸ J), u = J.mkQ ∘ₗ LinearMap.lsmul A A (a ^ n) := ⟨_, rfl⟩
  have hker : ∀ c : A, u c = 0 ↔ a ^ n * c ∈ J := by
    intro c
    rw [hu, LinearMap.comp_apply, LinearMap.lsmul_apply, Submodule.mkQ_apply, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
  have hex : Function.Exact (LinearMap.ker u).subtype u := by
    intro c
    constructor
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact hc
  have hflat : Function.Exact (LinearMap.lTensor B (LinearMap.ker u).subtype)
      (LinearMap.lTensor B u) := Module.Flat.lTensor_exact B hex
  have key : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = 0 := by
    have hmapJ : (Ideal.map (algebraMap A B) J : Ideal B)
        = Ideal.span (⇑(algebraMap A B) '' (J : Set A)) := rfl
    rw [hmapJ] at hy
    obtain ⟨k, cf, gg, hsum⟩ := Submodule.mem_span_set'.1 hy
    have hgg : ∀ i, ∃ c : A, c ∈ J ∧ algebraMap A B c = (gg i : B) := by
      intro i
      obtain ⟨c, hc1, hc2⟩ := (gg i).2
      exact ⟨c, hc1, hc2⟩
    choose c hcJ hcmap using hgg
    have e1 : LinearMap.lTensor B u (y ⊗ₜ[A] (1 : A)) = y ⊗ₜ[A] (J.mkQ (a ^ n)) := by
      rw [LinearMap.lTensor_tmul, hu]
      simp
    have e2 : (J.mkQ (a ^ n) : A ⧸ J) = (a ^ n) • (J.mkQ (1 : A)) := by
      rw [← map_smul]
      simp
    have e3 : algebraMap A B (a ^ n) * y = ∑ i, c i • cf i := by
      rw [map_pow, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcmap i, smul_eq_mul, Algebra.smul_def]
      ring
    rw [e1, e2, ← TensorProduct.smul_tmul, Algebra.smul_def, e3, TensorProduct.sum_tmul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [TensorProduct.smul_tmul]
    have hz : (c i) • (J.mkQ (1 : A)) = 0 := by
      have hz1 : (c i) • (J.mkQ (1 : A)) = J.mkQ (c i) := by
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [hz1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hcJ i
    rw [hz, TensorProduct.tmul_zero]
  obtain ⟨w, hw⟩ := (hflat (y ⊗ₜ[A] (1 : A))).1 key
  have main : ∀ z : TensorProduct A B (LinearMap.ker u),
      TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype z) ∈
        (saturationByPowers J a).map (algebraMap A B) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b cc =>
        have hcc : (cc : A) ∈ saturationByPowers J a := ⟨n, (hker _).1 cc.2⟩
        have h2 : algebraMap A B (cc : A) * b ∈ (saturationByPowers J a).map (algebraMap A B) :=
          Ideal.mul_mem_right b _ (Ideal.mem_map_of_mem (algebraMap A B) hcc)
        simpa [Algebra.smul_def] using h2
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Ideal.add_mem _ h₁ h₂
  have hy2 : y = TensorProduct.rid A B (LinearMap.lTensor B (LinearMap.ker u).subtype w) := by
    rw [hw]
    simp
  rw [hy2]
  exact main w

/- English proof (translation)
Rewrite `hx` using `[IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) B]`. Take `⟨⟨i, m⟩, hxe⟩` from `hx`. Take `⟨p, hp⟩` from `m.2`. Establish `hp' : f ^ p = (m : A)` using `hp`. Establish `h2 : algebraMap A B (x * (m : A)) = algebraMap A B (i : A)`.

Rewrite using `[map_mul]`. Conclude with `hxe`. Take `⟨cc, hcc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers f) B).1 h2`. Take `⟨q, hq⟩` from `cc.2`. Establish `hq' : f ^ q = (cc : A)` using `hq`.

Use `⟨q + p, ?_⟩` and prove the remaining obligations. Establish `h3 : f ^ (q + p) * x = (cc : A) * (x * (m : A))`. Rewrite using `[pow_add, hp', hq']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, hcc]`.

Conclude with `I.mul_mem_left _ i.2`.
-/
private theorem exists_pow_mul_mem_of_mem_map_away {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (f : A) [IsLocalization.Away f B] (I : Ideal A) (x : A)
    (hx : algebraMap A B x ∈ I.map (algebraMap A B)) : ∃ n : ℕ, f ^ n * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) B] at hx
  obtain ⟨⟨i, m⟩, hxe⟩ := hx
  obtain ⟨p, hp⟩ := m.2
  have hp' : f ^ p = (m : A) := hp
  have h2 : algebraMap A B (x * (m : A)) = algebraMap A B (i : A) := by
    rw [map_mul]
    exact hxe
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) B).1 h2
  obtain ⟨q, hq⟩ := cc.2
  have hq' : f ^ q = (cc : A) := hq
  refine ⟨q + p, ?_⟩
  have h3 : f ^ (q + p) * x = (cc : A) * (x * (m : A)) := by
    rw [pow_add, hp', hq']; ring
  rw [h3, hcc]
  exact I.mul_mem_left _ i.2

/- English proof (translation)
Use `U.2.isLocalization_basicOpen f` as an intermediate fact. Conclude with `exists_pow_mul_mem_of_mem_map_away (A := Γ(X, U.1)) (B := Γ(X, X.basicOpen f)) f I x hx`.
-/
private theorem exists_pow_mul_mem_of_mem_map_basicOpen {X : Scheme.{u}} (U : X.affineOpens)
    (f : Γ(X, U.1)) (I : Ideal Γ(X, U.1)) (x : Γ(X, U.1))
    (hx : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈
      Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) I) :
    ∃ n : ℕ, f ^ n * x ∈ I := by
  have := U.2.isLocalization_basicOpen f
  exact exists_pow_mul_mem_of_mem_map_away (A := Γ(X, U.1)) (B := Γ(X, X.basicOpen f)) f I x hx

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hsm⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hmp : m.IsPrime` using `hm.isPrime`. Establish `hy : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈ U`. Establish `hr : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈ Set.range (IsAffineOpen.fromSpec hU).base` using `Set.mem_range_self _`.

Rewrite `hr` using `[IsAffineOpen.range_fromSpec]`. Then use the resulting hypothesis. Take `⟨f, hfs, hf⟩` from `hcov _ hy`. Establish `h1 : (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈ (IsAffineOpen.fromSpec hU) ⁻¹ᵁ X.basicOpen f` using `hf`. Rewrite `h1` using `[IsAffineOpen.fromSpec_preimage_basicOpen hU f]`. Conclude with `((PrimeSpectrum.mem_basicOpen f _).1 h1) (hsm (Ideal.subset_span hfs))`.
-/
private theorem span_eq_top_of_basicOpen_cover {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hcov : ∀ y : X, y ∈ U → ∃ f ∈ s, y ∈ X.basicOpen f) :
    Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
  have hmp : m.IsPrime := hm.isPrime
  have hy : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈ U := by
    have hr : (IsAffineOpen.fromSpec hU).base ⟨m, hmp⟩ ∈
        Set.range (IsAffineOpen.fromSpec hU).base := Set.mem_range_self _
    rwa [IsAffineOpen.range_fromSpec] at hr
  obtain ⟨f, hfs, hf⟩ := hcov _ hy
  have h1 : (⟨m, hmp⟩ : PrimeSpectrum Γ(X, U)) ∈
      (IsAffineOpen.fromSpec hU) ⁻¹ᵁ X.basicOpen f := hf
  rw [IsAffineOpen.fromSpec_preimage_basicOpen hU f] at h1
  exact ((PrimeSpectrum.mem_basicOpen f _).1 h1) (hsm (Ideal.subset_span hfs))

/- English proof (translation)
Establish `key : ∀ P Q : X.IdealSheafData, (∀ f ∈ s, P.ideal (X.affineBasicOpen f) = Q.ideal (X.affineBasicOpen f)) → P.ideal U ≤ Q.ideal U`. Introduce `P Q hPQ x hx`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs x ?_` and prove the remaining obligations. Introduce and unpack `⟨f, hf⟩`. Establish `h1 : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈ Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) (Q.ideal U)`.

Rewrite using `[Q.2 U f, ← hPQ f hf, ← P.2 U f]`. Conclude with `Ideal.mem_map_of_mem _ hx`. Take `⟨m, hm⟩` from `exists_pow_mul_mem_of_mem_map_basicOpen U f (Q.ideal U) x h1`. Conclude with `⟨m, by simpa [smul_eq_mul] using hm⟩`. Conclude with `le_antisymm (key I J h) (key J I fun f hf => (h f hf).symm)`.
-/
private theorem ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top {X : Scheme.{u}} (I J : X.IdealSheafData)
    (U : X.affineOpens) (s : Set Γ(X, U.1)) (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal U = J.ideal U := by
  have key : ∀ P Q : X.IdealSheafData,
      (∀ f ∈ s, P.ideal (X.affineBasicOpen f) = Q.ideal (X.affineBasicOpen f)) →
      P.ideal U ≤ Q.ideal U := by
    intro P Q hPQ x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs x ?_
    rintro ⟨f, hf⟩
    have h1 : (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)) x ∈
        Ideal.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op))
          (Q.ideal U) := by
      rw [Q.2 U f, ← hPQ f hf, ← P.2 U f]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_mem_map_basicOpen U f (Q.ideal U) x h1
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  exact le_antisymm (key I J h) (key J I fun f hf => (h f hf).symm)

/- English proof (translation)
Set `_ : Algebra Γ(Y, U.1) Γ(Y', V.1)` to `(CommRingCat.Hom.hom (g.appLE U.1 V.1 e)).toAlgebra`. Establish `halg : algebraMap Γ(Y, U.1) Γ(Y', V.1) = CommRingCat.Hom.hom (g.appLE U.1 V.1 e)` using `rfl`. Establish `: Module.Flat Γ(Y, U.1) Γ(Y', V.1)` using `(inferInstance : AlgebraicGeometry.Flat g).1 U.2 V.2 e`. Establish `h1 : ((saturation F T).comap g).ideal V = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) ((saturation F T).ideal U)`. Rewrite using `[halg]`.

Conclude with `Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e`. Establish `h3 : (T.comap g).ideal V = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) (T.ideal U)`. Rewrite using `[halg]`. Conclude with `Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e`. Establish `h2 : (saturation F T).ideal U = saturationByPowers (T.ideal U) t`.

Use extensionality with `w`. Rewrite using `[mem_saturationByPowers_iff]`. Conclude with `mem_saturation_ideal_iff F T U t ht w`. Establish `h4 : (F.comap g).ideal V = Ideal.span {algebraMap Γ(Y, U.1) Γ(Y', V.1) t}`. Rewrite using `[halg]`.

Establish `hh` using `Scheme.IdealSheafData.comap_ideal_eq_span_image F g U V e {t} ht`. Simplify using `using hh`. Establish `h5 : (saturation (F.comap g) (T.comap g)).ideal V = saturationByPowers ((T.comap g).ideal V) (algebraMap Γ(Y, U.1) Γ(Y', V.1) t)`. Use extensionality with `w`. Rewrite using `[mem_saturationByPowers_iff]`.

Conclude with `mem_saturation_ideal_iff (F.comap g) (T.comap g) V _ h4 w`. Rewrite using `[h1, h2, h5, h3]`. Conclude with `map_saturationByPowers_of_flat (T.ideal U) t`.
-/
private theorem ideal_comap_saturation_of_ideal_eq_span_singleton {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [AlgebraicGeometry.Flat g] (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)]
    [QuasiCompact (saturationι (F.comap g) (T.comap g))]
    (U : Y.affineOpens) (V : Y'.affineOpens)
    (e : (V : Y'.Opens) ≤ (TopologicalSpace.Opens.map g.base).obj (U : Y.Opens))
    (t : Γ(Y, U.1)) (ht : F.ideal U = Ideal.span {t}) :
    ((saturation F T).comap g).ideal V = (saturation (F.comap g) (T.comap g)).ideal V := by
  let _ : Algebra Γ(Y, U.1) Γ(Y', V.1) := (CommRingCat.Hom.hom (g.appLE U.1 V.1 e)).toAlgebra
  have halg : algebraMap Γ(Y, U.1) Γ(Y', V.1) = CommRingCat.Hom.hom (g.appLE U.1 V.1 e) := rfl
  have : Module.Flat Γ(Y, U.1) Γ(Y', V.1) :=
    (inferInstance : AlgebraicGeometry.Flat g).1 U.2 V.2 e
  have h1 : ((saturation F T).comap g).ideal V
      = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) ((saturation F T).ideal U) := by
    rw [halg]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e
  have h3 : (T.comap g).ideal V
      = Ideal.map (algebraMap Γ(Y, U.1) Γ(Y', V.1)) (T.ideal U) := by
    rw [halg]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ g U V e
  have h2 : (saturation F T).ideal U = saturationByPowers (T.ideal U) t := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff F T U t ht w
  have h4 : (F.comap g).ideal V = Ideal.span {algebraMap Γ(Y, U.1) Γ(Y', V.1) t} := by
    rw [halg]
    have hh := Scheme.IdealSheafData.comap_ideal_eq_span_image F g U V e {t} ht
    simpa using hh
  have h5 : (saturation (F.comap g) (T.comap g)).ideal V
      = saturationByPowers ((T.comap g).ideal V) (algebraMap Γ(Y, U.1) Γ(Y', V.1) t) := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff (F.comap g) (T.comap g) V _ h4 w
  rw [h1, h2, h5, h3]
  exact map_saturationByPowers_of_flat (T.ideal U) t

/- English proof (translation)
Use `Scheme.IdealSheafData.ext (funext fun V => ?_)` and prove the remaining obligations. Use `ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top _ _ V {f : Γ(Y', V.1) | ∃ (U : Y.affineOpens) (t : Γ(Y, U.1)), F.ideal U = Ideal.span {t} ∧ Y'.basicOpen f ≤ (TopologicalSpace.Opens.map g.base).obj U.1} ?_ ?_` and prove the remaining obligations. Use `span_eq_top_of_basicOpen_cover V.1 V.2 _ ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨U, t, hUmem, -, ht⟩` from `hF (g.base y)`.

Take `⟨f, hf1, hf2⟩` from `IsAffineOpen.exists_basicOpen_le V.2 (⟨y, ⟨hy, hUmem⟩⟩ : (V.1 ⊓ (TopologicalSpace.Opens.map g.base).obj U.1 : Y'.Opens)) hy`. Conclude with `⟨f, ⟨U, t, ht, le_trans hf1 inf_le_right⟩, hf2⟩`. Introduce and unpack `f ⟨U, t, ht, hle⟩`. Conclude with `ideal_comap_saturation_of_ideal_eq_span_singleton g F T U (Y'.affineBasicOpen f) hle t ht`.
-/
theorem comap_saturation_of_flat {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [AlgebraicGeometry.Flat g] (F T : Y.IdealSheafData) (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F)
    [QuasiCompact (saturationι F T)]
    [QuasiCompact (saturationι (F.comap g) (T.comap g))] :
    (saturation F T).comap g = saturation (F.comap g) (T.comap g) := by
  classical
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  refine ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top _ _ V
    {f : Γ(Y', V.1) | ∃ (U : Y.affineOpens) (t : Γ(Y, U.1)), F.ideal U = Ideal.span {t} ∧
      Y'.basicOpen f ≤ (TopologicalSpace.Opens.map g.base).obj U.1} ?_ ?_
  · refine span_eq_top_of_basicOpen_cover V.1 V.2 _ ?_
    intro y hy
    obtain ⟨U, t, hUmem, -, ht⟩ := hF (g.base y)
    obtain ⟨f, hf1, hf2⟩ := IsAffineOpen.exists_basicOpen_le V.2
      (⟨y, ⟨hy, hUmem⟩⟩ : (V.1 ⊓ (TopologicalSpace.Opens.map g.base).obj U.1 : Y'.Opens)) hy
    exact ⟨f, ⟨U, t, ht, le_trans hf1 inf_le_right⟩, hf2⟩
  · rintro f ⟨U, t, ht, hle⟩
    exact ideal_comap_saturation_of_ideal_eq_span_singleton g F T U (Y'.affineBasicOpen f) hle t ht

/- English proof (translation)
Establish `hZ : (Z.comap π).comap g₁ = (Z.comap g).comap π'`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]`. Establish `hD : (D.comap π).comap g₁ = (D.comap g).comap π'`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]`. Establish `: AlgebraicGeometry.Flat g₁` using `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Flat) hsq.flip inferInstance`.

Establish `i1 : QuasiCompact (saturationι (Z.comap π) (D.comap π))` using `inferInstanceAs (QuasiCompact (strictTransformι π Z D))`. Establish `i2 : QuasiCompact (saturationι ((Z.comap π).comap g₁) ((D.comap π).comap g₁))`. Rewrite using `[hZ, hD]`. Conclude with `inferInstanceAs (QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g)))`. Establish `h` using `comap_saturation_of_flat g₁ (Z.comap π) (D.comap π) hπ.1`.

Simplify using `only [strictTransform_eq_saturation]`. Rewrite using `[h, hZ, hD]`.
-/
theorem comap_strictTransform_of_flat {X X₁ X' X₁' : Scheme.{u}}
    (π : X₁ ⟶ X) (g : X' ⟶ X) (π' : X₁' ⟶ X') (g₁ : X₁' ⟶ X₁)
    [AlgebraicGeometry.Flat g]
    (hsq : IsPullback g₁ π' π g)
    (Z D : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g))] :
    (Blowup.strictTransform π Z D).comap g₁ = Blowup.strictTransform π' (Z.comap g) (D.comap g) := by
  have hZ : (Z.comap π).comap g₁ = (Z.comap g).comap π' := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]
  have hD : (D.comap π).comap g₁ = (D.comap g).comap π' := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.w, Scheme.IdealSheafData.comap_comp]
  have : AlgebraicGeometry.Flat g₁ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Flat)
      hsq.flip inferInstance
  have i1 : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have i2 : QuasiCompact (saturationι ((Z.comap π).comap g₁) ((D.comap π).comap g₁)) := by
    rw [hZ, hD]
    exact inferInstanceAs (QuasiCompact (strictTransformι π' (Z.comap g) (D.comap g)))
  have h := comap_saturation_of_flat g₁ (Z.comap π) (D.comap π) hπ.1
  simp only [strictTransform_eq_saturation]
  rw [h, hZ, hD]

/- English proof (translation)
Use `FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D` as an intermediate fact. Use `FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π' (Z.comap g) (D.comap g)` as an intermediate fact. Conclude with `comap_strictTransform_of_flat π g π' g₁ hsq Z D hπ`.
-/
theorem comap_strictTransform_of_flat_of_isLocallyNoetherian {X X₁ X' X₁' : Scheme.{u}}
    (π : X₁ ⟶ X) (g : X' ⟶ X) (π' : X₁' ⟶ X') (g₁ : X₁' ⟶ X₁)
    [AlgebraicGeometry.Flat g] [IsLocallyNoetherian X₁] [IsLocallyNoetherian X₁']
    (hsq : IsPullback g₁ π' π g)
    (Z D : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (Blowup.strictTransform π Z D).comap g₁ = Blowup.strictTransform π' (Z.comap g) (D.comap g) := by
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D
  have := FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian π' (Z.comap g) (D.comap g)
  exact comap_strictTransform_of_flat π g π' g₁ hsq Z D hπ

end FunctorialResolution.EmbeddedResolution
