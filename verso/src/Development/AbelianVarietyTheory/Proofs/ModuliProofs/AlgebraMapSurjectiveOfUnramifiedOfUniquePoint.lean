import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A`. Establish `hker : ∀ a : A, φ a = 0 → a = 0`. Introduce `a ha`. Apply `IsNilpotent.eq_zero` to reduce the goal to its premises. Rewrite using `[nilpotent_iff_mem_prime]`.

Introduce `J hJ`. Establish `hb : Function.Bijective (algebraMap K (A ⧸ J))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : K ≃ₐ[K] (A ⧸ J)` to `AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hb`. Establish `h` using `hφ ((e.symm : (A ⧸ J) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K J))`. Rewrite `ha` using `[← h]`.

Establish `h2 : e.symm (Ideal.Quotient.mk J a) = 0` using `ha`. Rewrite `h2` using `[map_eq_zero_iff _ e.symm.injective]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h2`. Introduce `a`. Use `⟨φ a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Apply `hker` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem algebraMap_surjective_of_unramified_of_unique_point (K A : Type) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ : A →ₐ[K] K) (hφ : ∀ ψ : A →ₐ[K] K, ψ = φ) : Function.Surjective (algebraMap K A) := by
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  have hker : ∀ a : A, φ a = 0 → a = 0 := by
    intro a ha
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hb : Function.Bijective (algebraMap K (A ⧸ J)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] (A ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hb
    have h := hφ ((e.symm : (A ⧸ J) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K J))
    rw [← h] at ha
    have h2 : e.symm (Ideal.Quotient.mk J a) = 0 := ha
    rw [map_eq_zero_iff _ e.symm.injective] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  intro a
  refine ⟨φ a, ?_⟩
  rw [← sub_eq_zero]
  apply hker
  simp

/- English proof (translation)
Rewrite `h` using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct]`. Set `g : p.asIdeal.ResidueField →+* K` to `Ideal.ResidueField.lift p.asIdeal (algebraMap R K) hp.ge (by`. Introduce `r hr`. Establish `: algebraMap R K r ≠ 0` using `fun h0 => hr (hp.le h0)`. Conclude with `(isUnit_iff_ne_zero.mpr this))`.

Use `letI : Algebra p.asIdeal.ResidueField K := g.toAlgebra`. Use `haveI : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq (by`. Introduce `r`. Conclude with `(Ideal.ResidueField.lift_algebraMap ..).symm)`. Use `haveI : Nontrivial (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] C)) := inferInstance`.

Conclude with `(TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K C).symm.toEquiv.nontrivial`.
-/
theorem nontrivial_tensor_of_mem_support (R C K : Type) [CommRing R] [AddCommGroup C] [Module R C]
    [Module.Finite R C] [Field K] [Algebra R K] (p : PrimeSpectrum R)
    (hp : RingHom.ker (algebraMap R K) = p.asIdeal) (h : p ∈ Module.support R C) :
    Nontrivial (K ⊗[R] C) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h
  let g : p.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift p.asIdeal (algebraMap R K)
    hp.ge (by
      intro r hr
      have : algebraMap R K r ≠ 0 := fun h0 => hr (hp.le h0)
      exact (isUnit_iff_ne_zero.mpr this))
  letI : Algebra p.asIdeal.ResidueField K := g.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (Ideal.ResidueField.lift_algebraMap ..).symm)
  haveI : Nontrivial (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] C)) :=
    inferInstance
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K
    C).symm.toEquiv.nontrivial

open scoped TensorProduct in
/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Apply `hP a` to reduce the goal to its premises. Introduce `p hp _`. Take `⟨K, _, _, x, hx, y, hy, -⟩` from `hpt p hp`.

Rewrite using `[← hx, RingHom.mem_ker, ← hy, RingHom.comp_apply, ha, map_zero]`.
-/
private lemma algebraMap_injective_of_denseP_unique_lift {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    (P : Set (Ideal R)) (hP : _root_.GlobalTheory.ZM.DenseP P)
    (hpt : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) :
    Function.Injective (algebraMap R B) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply hP a
  intro p hp _
  obtain ⟨K, _, _, x, hx, y, hy, -⟩ := hpt p hp
  rw [← hx, RingHom.mem_ker, ← hy, RingHom.comp_apply, ha, map_zero]

open scoped TensorProduct in
/- English proof (translation)
Use `haveI := Algebra.FormallyUnramified.isReduced_of_field K A`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite K A`. Establish `hφ₀s : Function.Surjective φ₀` using `fun c => ⟨algebraMap K A c, by simp⟩`. Establish `hmax : ∀ m : Ideal A, m.IsMaximal → m = RingHom.ker φ₀`. Introduce `m hm`.

Use `letI := Ideal.Quotient.field m`. Establish `hs : Function.Surjective (algebraMap K (A ⧸ m))` using `IsSepClosed.algebraMap_surjective K (A ⧸ m)`. Set `e : K ≃ₐ[K] A ⧸ m` to `AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m)) ⟨(algebraMap K (A ⧸ m)).injective, hs⟩`. Establish `h` using `hφ₀ ((e.symm : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m))`. Rewrite using `[← h]`.

Use extensionality with `a`. Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Use `haveI : IsLocalRing A := IsLocalRing.of_unique_max_ideal ⟨RingHom.ker φ₀, RingHom.ker_isMaximal_of_surjective _ hφ₀s, fun m hm => hmax m hm⟩`. Establish `hfield` using `IsArtinianRing.isField_of_isReduced_of_isLocalRing A`. Establish `hinj : Function.Injective φ₀`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `hne`. Take `⟨b, hb⟩` from `hfield.mul_inv_cancel hne`. Use `congrArg φ₀ hb` as an intermediate fact.

Simplify using `[ha] at this`. Introduce `a`. Conclude with `⟨φ₀ a, hinj (by simp)⟩`.
-/
private lemma algebraMap_surjective_of_unique_algHom (K A : Type) [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ₀ : A →ₐ[K] K) (hφ₀ : ∀ φ : A →ₐ[K] K, φ = φ₀) : Function.Surjective (algebraMap K A) := by
  haveI := Algebra.FormallyUnramified.isReduced_of_field K A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hφ₀s : Function.Surjective φ₀ := fun c => ⟨algebraMap K A c, by simp⟩
  have hmax : ∀ m : Ideal A, m.IsMaximal → m = RingHom.ker φ₀ := by
    intro m hm
    letI := Ideal.Quotient.field m
    have hs : Function.Surjective (algebraMap K (A ⧸ m)) := IsSepClosed.algebraMap_surjective K (A ⧸ m)
    let e : K ≃ₐ[K] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m))
      ⟨(algebraMap K (A ⧸ m)).injective, hs⟩
    have h := hφ₀ ((e.symm : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m))
    rw [← h]
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsLocalRing A := IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker φ₀, RingHom.ker_isMaximal_of_surjective _ hφ₀s, fun m hm => hmax m hm⟩
  have hfield := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  have hinj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    have := congrArg φ₀ hb
    simp [ha] at this
  intro a
  exact ⟨φ₀ a, hinj (by simp)⟩

open scoped TensorProduct in
/- English proof (translation)
Use `letI : Algebra R K := x.toAlgebra`. Take `⟨y, hyx, hyu⟩` from `hy`. Set `y' : B →ₐ[R] K` to `{ y with commutes' := fun r => congrArg (fun g : R →+* K => g r) hyx }`. Set `φ₀ : K ⊗[R] B →ₐ[K] K` to `Algebra.TensorProduct.productLeftAlgHom (AlgHom.id K K) y'`. Establish `hΦ : ∀ φ : K ⊗[R] B →ₐ[K] K, φ = φ₀`.

Introduce `φ`. Establish `h1 : ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y`. Apply `hyu` to reduce the goal to its premises. Use extensionality with `r`. Conclude with `((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r`.

Establish `h2 : ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y`. Apply `hyu` to reduce the goal to its premises. Use extensionality with `r`. Conclude with `((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r`. Apply `Algebra.TensorProduct.ext (Subsingleton.elim _ _)` to reduce the goal to its premises.

Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Conclude with `h1.trans h2.symm`. Establish `hsurj` using `algebraMap_surjective_of_unique_algHom K (K ⊗[R] B) φ₀ hΦ`. Set `N : Submodule R B` to `LinearMap.range (Algebra.linearMap R B)`. Establish `hsub : Subsingleton (K ⊗[R] (B ⧸ N))`.

Use `⟨fun u v => ?_⟩` and prove the remaining obligations. Establish `key : ∀ w : K ⊗[R] (B ⧸ N), w = 0`. Introduce `w`. Take `⟨t, rfl⟩` from `LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N) w`. Take `⟨c, rfl⟩` from `hsurj t`.

Establish `h1 : (N.mkQ (1 : B)) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨1, by simp⟩`. Simplify using `[Algebra.TensorProduct.algebraMap_apply, h1]`. Rewrite using `[key u, key v]`.

Establish `hq : (RingHom.ker x).IsPrime` using `RingHom.ker_isPrime x`. Set `xb : (RingHom.ker x).ResidueField →+* K` to `Ideal.ResidueField.lift (RingHom.ker x) x le_rfl (fun a ha => by`. Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]`. Conclude with `ha)`. Use `letI : Algebra (RingHom.ker x).ResidueField K := xb.toAlgebra`.

Use `haveI : IsScalarTower R (RingHom.ker x).ResidueField K := IsScalarTower.of_algebraMap_eq (fun r => by`. Simplify using `[xb, RingHom.algebraMap_toAlgebra])`. Establish `hsub2 : Subsingleton ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N))`. Establish `e` using `TensorProduct.AlgebraTensorModule.cancelBaseChange R (RingHom.ker x).ResidueField K K (B ⧸ N)`. Use `haveI : Subsingleton (K ⊗[(RingHom.ker x).ResidueField] ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N))) := e.toEquiv.subsingleton`.

Conclude with `(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _).mp this`. Establish `hns : (⟨RingHom.ker x, hq⟩ : PrimeSpectrum R) ∉ Module.support R (B ⧸ N)`. Rewrite using `[Module.mem_support_iff_nontrivial_residueField_tensorProduct]`. Conclude with `not_nontrivial_iff_subsingleton.mpr hsub2`. Rewrite `hns` using `[Module.mem_support_iff_of_finite]`.

Take `⟨f, hfann, hfq⟩` from `SetLike.not_le_iff_exists.mp hns`. Use `⟨f, hfq, fun b => ?_⟩` and prove the remaining obligations. Establish `h0` using `Module.mem_annihilator.mp hfann (N.mkQ b)`. Rewrite `h0` using `[← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨a, ha⟩` from `h0`.

Conclude with `⟨a, by simpa using ha.symm⟩`.
-/
private lemma exists_smul_mem_range_algebraMap_of_unique_lift {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] {K : Type} [Field K] [IsAlgClosed K]
    (x : R →+* K) (hy : ∃! y : B →+* K, y.comp (algebraMap R B) = x) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, f • b = algebraMap R B a := by
  letI : Algebra R K := x.toAlgebra
  obtain ⟨y, hyx, hyu⟩ := hy
  let y' : B →ₐ[R] K := { y with commutes' := fun r => congrArg (fun g : R →+* K => g r) hyx }
  let φ₀ : K ⊗[R] B →ₐ[K] K := Algebra.TensorProduct.productLeftAlgHom (AlgHom.id K K) y'
  have hΦ : ∀ φ : K ⊗[R] B →ₐ[K] K, φ = φ₀ := by
    intro φ
    have h1 : ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hyu
      ext r
      exact ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h2 : ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hyu
      ext r
      exact ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    apply AlgHom.coe_ringHom_injective
    exact h1.trans h2.symm
  have hsurj := algebraMap_surjective_of_unique_algHom K (K ⊗[R] B) φ₀ hΦ
  let N : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  have hsub : Subsingleton (K ⊗[R] (B ⧸ N)) := by
    refine ⟨fun u v => ?_⟩
    have key : ∀ w : K ⊗[R] (B ⧸ N), w = 0 := by
      intro w
      obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N) w
      obtain ⟨c, rfl⟩ := hsurj t
      have h1 : (N.mkQ (1 : B)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨1, by simp⟩
      simp [Algebra.TensorProduct.algebraMap_apply, h1]
    rw [key u, key v]
  have hq : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let xb : (RingHom.ker x).ResidueField →+* K := Ideal.ResidueField.lift (RingHom.ker x) x le_rfl
    (fun a ha => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      exact ha)
  letI : Algebra (RingHom.ker x).ResidueField K := xb.toAlgebra
  haveI : IsScalarTower R (RingHom.ker x).ResidueField K := IsScalarTower.of_algebraMap_eq (fun r => by
    simp [xb, RingHom.algebraMap_toAlgebra])
  have hsub2 : Subsingleton ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N)) := by
    have e := TensorProduct.AlgebraTensorModule.cancelBaseChange R (RingHom.ker x).ResidueField K K (B ⧸ N)
    haveI : Subsingleton (K ⊗[(RingHom.ker x).ResidueField] ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N))) :=
      e.toEquiv.subsingleton
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _).mp this
  have hns : (⟨RingHom.ker x, hq⟩ : PrimeSpectrum R) ∉ Module.support R (B ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hsub2
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hfann, hfq⟩ := SetLike.not_le_iff_exists.mp hns
  refine ⟨f, hfq, fun b => ?_⟩
  have h0 := Module.mem_annihilator.mp hfann (N.mkQ b)
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨a, ha⟩ := h0
  exact ⟨a, by simpa using ha.symm⟩

open scoped TensorProduct in

/- English proof (translation)
Introduce `R B _ _ _ _ _ _ P hP hpt`. Establish `hdense : _root_.GlobalTheory.ZM.DenseP P`. Introduce `a ha`. Apply `IsReduced.eq_zero` to reduce the goal to its premises. Rewrite using `[nilpotent_iff_mem_prime]`.

Introduce `q hq`. Assume the negation of the conclusion as `haq`. Take `⟨p, hpP, hp, -, hap⟩` from `hP q a hq haq`. Conclude with `hap (ha p hpP hp)`. Use `⟨algebraMap_injective_of_denseP_unique_lift P hdense hpt, fun b => ?_⟩` and prove the remaining obligations.

Set `M : Submodule R B` to `LinearMap.range (Algebra.linearMap R B)`. Set `s : Set R` to `{f | ∃ a : R, f • b = algebraMap R B a}`. Establish `hs : Ideal.span s = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hsm⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨p, hpP, -, hmp, h1p⟩` from `hP m 1 hm.isPrime (fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h))`. Establish `hpm : p = m` using `(hm.eq_of_le ((Ideal.ne_top_iff_one p).mpr h1p) hmp).symm`. Take `⟨K, _, _, x, hx, hy⟩` from `hpt p hpP`. Take `⟨f, hf, hfb⟩` from `exists_smul_mem_range_algebraMap_of_unique_lift x hy`. Apply `hf` to reduce the goal to its premises.

Rewrite using `[hx, hpm]`. Conclude with `hsm (Ideal.subset_span (hfb b))`. Establish `hb` using `Submodule.mem_of_span_eq_top_of_smul_pow_mem M s hs b (fun r => ⟨1, by`. Take `⟨a, ha⟩` from `r.2`. Rewrite using `[pow_one, ha]`.

Conclude with `⟨a, rfl⟩⟩)`. Take `⟨a, ha⟩` from `hb`. Conclude with `⟨a, ha⟩`.
-/
theorem _root_.GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point :
    ∀ (R B : Type) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B] [Module.Finite R B]
      [Algebra.FormallyUnramified R B] (P : Set (Ideal R)),
      (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) →
      (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
        RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) →
      Function.Bijective (algebraMap R B) := by
  intro R B _ _ _ _ _ _ P hP hpt
  have hdense : _root_.GlobalTheory.ZM.DenseP P := by
    intro a ha
    apply IsReduced.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro q hq
    by_contra haq
    obtain ⟨p, hpP, hp, -, hap⟩ := hP q a hq haq
    exact hap (ha p hpP hp)
  refine ⟨algebraMap_injective_of_denseP_unique_lift P hdense hpt, fun b => ?_⟩
  let M : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  let s : Set R := {f | ∃ a : R, f • b = algebraMap R B a}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hpP, -, hmp, h1p⟩ := hP m 1 hm.isPrime
      (fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h))
    have hpm : p = m := (hm.eq_of_le ((Ideal.ne_top_iff_one p).mpr h1p) hmp).symm
    obtain ⟨K, _, _, x, hx, hy⟩ := hpt p hpP
    obtain ⟨f, hf, hfb⟩ := exists_smul_mem_range_algebraMap_of_unique_lift x hy
    apply hf
    rw [hx, hpm]
    exact hsm (Ideal.subset_span (hfb b))
  have hb := Submodule.mem_of_span_eq_top_of_smul_pow_mem M s hs b (fun r => ⟨1, by
    obtain ⟨a, ha⟩ := r.2
    rw [pow_one, ha]
    exact ⟨a, rfl⟩⟩)
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, ha⟩

end GlobalTheory
