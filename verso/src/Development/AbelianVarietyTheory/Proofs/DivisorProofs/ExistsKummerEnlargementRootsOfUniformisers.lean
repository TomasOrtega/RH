import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

/- English proof (translation)
Use `set p : Ideal A := Q.comap (algebraMap A B) with hp`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ Q`. Use `haveI : Q.LiesOver p := ⟨rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]`.

Introduce `r hr hrp`. Assume the negation of the conclusion as `hcon`. Establish `hr0 : r ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hcon`.

Use `haveI := hr`. Take `⟨P₁, hP₁Q, hP₁, hP₁o⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp`. Use `haveI := hP₁`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Take `⟨P₀, hP₀P₁, hP₀, -⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁ (bot_lt_iff_ne_bot.mpr hr0)`.

Use `haveI := hP₀`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q`. Rewrite `h2` using `[hQ]`. Establish `h4 : (1 : ℕ∞) ≤ P₁.height` using `le_trans le_add_self h1`.

Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (by gcongr) h2`. Conclude with `absurd h3 (by decide)`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Use `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)` as an intermediate fact. Simplify using `using this`.
-/
theorem height_comap_eq_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro r hr hrp
    by_contra hcon
    have hr0 : r ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hr
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
      (bot_lt_iff_ne_bot.mpr hr0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

/- English proof (translation)
Distinguish the cases in `h : p.IsPrime ∧ p.height = 1`. Take `⟨hp, h1⟩` from `h haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one A p h1`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)`. Take `⟨⟨x, s⟩, hxs⟩` from `IsLocalization.surj p.primeCompl ϖ`. Use `⟨x, fun _ => ?_⟩` and prove the remaining obligations.

Establish `hu : IsUnit (algebraMap A (Localization.AtPrime p) s)` using `IsLocalization.map_units _ s`. Establish `e : algebraMap A (Localization.AtPrime p) x = ϖ * algebraMap A (Localization.AtPrime p) s` using `hxs.symm`. Rewrite using `[e]`. Conclude with `(irreducible_mul_isUnit hu).mpr hϖ`. Conclude with `⟨1, fun h1 => absurd ⟨inferInstance, h1⟩ h⟩`.
-/
theorem exists_uniformiser (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) :
    ∃ π : A, ∀ [p.IsPrime], p.height = 1 → Irreducible (algebraMap A (Localization.AtPrime p) π) := by
  by_cases h : p.IsPrime ∧ p.height = 1
  · obtain ⟨hp, h1⟩ := h
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one A p h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj p.primeCompl ϖ
    refine ⟨x, fun _ => ?_⟩
    have hu : IsUnit (algebraMap A (Localization.AtPrime p) s) := IsLocalization.map_units _ s
    have e : algebraMap A (Localization.AtPrime p) x = ϖ * algebraMap A (Localization.AtPrime p) s :=
      hxs.symm
    rw [e]
    exact (irreducible_mul_isUnit hu).mpr hϖ
  · exact ⟨1, fun h1 => absurd ⟨inferInstance, h1⟩ h⟩

end GlobalTheory.KummerEnlarge

namespace GlobalTheory.KummerEnlarge

open GlobalTheory.NormalApprox

/- English proof (translation)
Introduce `T _ _ _ hT q hq hqT A _ _ _ _ _ _ i hi hloc a ha`. Use `haveI : IsIntegrallyClosed T := GlobalTheory.VertUnitsNoeth.isIntegrallyClosed_of_absIntClosed' T hT`. Use `choose π hπ using exists_uniformiser A`. Establish `hy : ∀ p : Ideal A, ∃ y : T, y ^ q = i (π p)`. Introduce `p`.

Take `⟨y, hy⟩` from `hT (X ^ q - C (i (π p))) (monic_X_pow_sub_C _ hq.ne') (by rw [natDegree_X_pow_sub_C]; exact hq)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Simplify `hy` using `[sub_eq_zero]`. Use `choose y hy using hy`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})`.

Use `set S : Finset T := (Algebra.EssFiniteType.finset ℤ A).image i ∪ hfin.toFinset.image y with hS`. Establish `hgen : ∀ z ∈ Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A), i z ∈ gen S`. Introduce `z hz`. Establish `h2 : i.toIntAlgHom z ∈ (Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A)).map i.toIntAlgHom` using `Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩`. Rewrite `h2` using `[AlgHom.map_adjoin]`.

Use `Algebra.adjoin_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `t ⟨u, hu, rfl⟩`. Simplify using `only [hS, Finset.coe_union, Finset.coe_image]`. Conclude with `Or.inl ⟨u, hu, rfl⟩`. Establish `hmem : ∀ x : A, i x ∈ loc S`.

Introduce `x`. Use `haveI := Algebra.EssFiniteType.isLocalization ℤ A`. Take `⟨⟨r, m⟩, hrm⟩` from `IsLocalization.surj (Algebra.EssFiniteType.submonoid ℤ A) x`. Use `⟨i (m.1 : A), gen_le_norm S (hgen _ m.1.2), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsLocalization.map_units A m).map i`.

Rewrite using `[mul_comm, ← map_mul]`. Establish `e : x * (m.1 : A) = (r : A)` using `hrm`. Rewrite using `[e]`. Conclude with `gen_le_norm S (hgen _ r.2)`. Set `f : A →+* loc S` to `i.codRestrict (loc S) hmem`.

Establish `hfinj : Function.Injective f` using `fun x x' h => hi (congrArg Subtype.val h)`. Use `haveI := loc_isLocalization S`. Use `haveI : IsNoetherianRing (loc S) := IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)`. Use `haveI : IsIntegrallyClosed (norm S) := norm_isIntegrallyClosed S`. Use `haveI : IsIntegrallyClosed (loc S) := isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)`.

Use `haveI : IsLocalRing (loc S) := loc_isLocalRing S`. Use `⟨loc S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, GlobalTheory.VertUnitsNoeth.essFiniteType_loc S, f, (loc S).subtype, hfinj, Subtype.val_injective, ⟨fun x hx => isUnit_of_isUnit_coe S x hx⟩, RingHom.ext fun _ => rfl, ?_⟩` and prove the remaining obligations. Introduce `p₁ _ hp₁ hfa`. Use `letI : Algebra A (loc S) := f.toAlgebra`. Use `letI : Algebra A T := i.toAlgebra`.

Establish `hyint : ∀ p : Ideal A, IsIntegral A (y p)`. Introduce `p`. Use `⟨X ^ q - C (π p), monic_X_pow_sub_C _ hq.ne', ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_sub, eval₂_X_pow, eval₂_C, hy]`. Conclude with `sub_self _`.

Establish `hgenC : ∀ z ∈ gen S, z ∈ integralClosure A T`. Introduce `z hz`. Establish `hle : gen S ≤ (integralClosure A T).restrictScalars ℤ`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce `t ht`.

Simplify using `only [hS, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image] at ht`. Break down `ht with ⟨u, -, rfl⟩ | ⟨p, -, rfl⟩` into its components or cases. Conclude with `isIntegral_algebraMap`. Conclude with `hyint p`. Conclude with `hle hz`.

Establish `hnormint : ∀ x (hx : x ∈ norm S), IsIntegral A (⟨x, norm_le_loc S hx⟩ : loc S)`. Introduce `x hx`. Set `φ : gen S →+* integralClosure A T` to `(gen S).val.toRingHom.codRestrict (integralClosure A T) (fun z => hgenC _ z.2)`. Establish `h1 : IsIntegral (integralClosure A T) x` using `IsIntegral.map_of_comp_eq φ (RingHom.id T) rfl hx.1`. Establish `h2 : IsIntegral A x` using `isIntegral_trans x h1`.

Set `g : loc S →ₐ[A] T` to `{ (loc S).subtype with commutes' := fun _ => rfl }`. Conclude with `(isIntegral_algHom_iff g Subtype.val_injective).mp h2`. Set `B` to `integralClosure A (loc S)`. Use `haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (fun x x' h => hfinj (congrArg Subtype.val h))`. Use `haveI : Algebra.HasGoingDown A B := inferInstance`.

Set `M : Submonoid B` to `(IsUnit.submonoid (loc S)).comap (algebraMap B (loc S))`. Use `haveI hML : IsLocalization M (loc S) := by`. Use `⟨fun m => m.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩` and prove the remaining obligations. Take `⟨s, hs, hsu, hsz⟩` from `z.2`. Set `sB : B` to `⟨⟨s, norm_le_loc S hs⟩, hnormint s hs⟩`.

Set `tB : B` to `⟨⟨s * z, norm_le_loc S hsz⟩, hnormint _ hsz⟩`. Establish `hsM : sB ∈ M` using `isUnit_of_isUnit_coe S _ hsu`. Use `⟨(tB, ⟨sB, hsM⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z : T) * s = s * z`. Expand and normalize the polynomial expressions, which then agree.

Establish `: u = v` using `Subtype.val_injective h`. Rewrite using `[this]`. Use `set P : Ideal B := p₁.comap (algebraMap B (loc S)) with hP`. Establish `hPh : P.height = 1`. Rewrite using `[hP, ← hp₁]`.

Conclude with `IsLocalization.height_comap M p₁`. Establish `hcomap : p₁.comap f = P.comap (algebraMap A B)`. Rewrite using `[hP, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]`. Both sides reduce to the same expression. Establish `hne : P.comap (algebraMap A B) ≠ ⊥`.

Rewrite using `[← hcomap]`. Introduce `h`. Establish `: a ∈ p₁.comap f` using `hfa`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `ha this`.

Establish `hheight : (p₁.comap f).height = 1`. Rewrite using `[hcomap]`. Conclude with `height_comap_eq_one_of_goingDown P hPh hne`. Establish `hmin : p₁.comap f ∈ (Ideal.span {a}).minimalPrimes`. Use `⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hfa⟩, fun r hr hrp => ?_⟩` and prove the remaining obligations.

Take `⟨hrprime, har⟩` from `hr`. Assume the negation of the conclusion as `hlt`. Establish `hlt' : r < p₁.comap f` using `lt_of_le_of_ne hrp (fun e => hlt (e ▸ le_rfl))`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Establish `hr0 : (⊥ : Ideal A) < r`.

Use `bot_lt_iff_ne_bot.mpr fun h => ha ?_` and prove the remaining obligations. Establish `: a ∈ r` using `har (Ideal.mem_span_singleton_self a)`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `this`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hr0`.

Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt'`. Rewrite `h2` using `[hheight]`. Establish `h4 : (1 : ℕ∞) ≤ r.height` using `le_trans le_add_self h1`. Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (by gcongr) h2`. Conclude with `absurd h3 (by decide)`.

Establish `hyS : y (p₁.comap f) ∈ S`. Conclude with `Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hmin))`. Use `⟨hheight, π (p₁.comap f), hπ _ hheight, ⟨y (p₁.comap f), mem_loc_of_mem S hyS⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[SubmonoidClass.coe_pow]`.

Conclude with `hy _`.
-/
theorem exists_kummer_enlargement : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ a : A, a ≠ 0 →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      ∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π := by
  intro T _ _ _ hT q hq hqT A _ _ _ _ _ _ i hi hloc a ha
  classical
  haveI : IsIntegrallyClosed T := GlobalTheory.VertUnitsNoeth.isIntegrallyClosed_of_absIntClosed' T hT
  choose π hπ using exists_uniformiser A
  have hy : ∀ p : Ideal A, ∃ y : T, y ^ q = i (π p) := by
    intro p
    obtain ⟨y, hy⟩ := hT (X ^ q - C (i (π p))) (monic_X_pow_sub_C _ hq.ne')
      (by rw [natDegree_X_pow_sub_C]; exact hq)
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using hy
  choose y hy using hy
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})
  set S : Finset T := (Algebra.EssFiniteType.finset ℤ A).image i ∪ hfin.toFinset.image y with hS

  have hgen : ∀ z ∈ Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A),
      i z ∈ gen S := by
    intro z hz
    have h2 : i.toIntAlgHom z ∈ (Algebra.adjoin ℤ ((Algebra.EssFiniteType.finset ℤ A : Finset A) : Set A)).map
        i.toIntAlgHom := Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩
    rw [AlgHom.map_adjoin] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro t ⟨u, hu, rfl⟩
    simp only [hS, Finset.coe_union, Finset.coe_image]
    exact Or.inl ⟨u, hu, rfl⟩
  have hmem : ∀ x : A, i x ∈ loc S := by
    intro x
    haveI := Algebra.EssFiniteType.isLocalization ℤ A
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid ℤ A) x
    refine ⟨i (m.1 : A), gen_le_norm S (hgen _ m.1.2), ?_, ?_⟩
    · exact (IsLocalization.map_units A m).map i
    · rw [mul_comm, ← map_mul]
      have e : x * (m.1 : A) = (r : A) := hrm
      rw [e]
      exact gen_le_norm S (hgen _ r.2)
  let f : A →+* loc S := i.codRestrict (loc S) hmem
  have hfinj : Function.Injective f := fun x x' h => hi (congrArg Subtype.val h)
  haveI := loc_isLocalization S
  haveI : IsNoetherianRing (loc S) :=
    IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)
  haveI : IsIntegrallyClosed (norm S) := norm_isIntegrallyClosed S
  haveI : IsIntegrallyClosed (loc S) :=
    isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)
  haveI : IsLocalRing (loc S) := loc_isLocalRing S
  refine ⟨loc S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.VertUnitsNoeth.essFiniteType_loc S, f, (loc S).subtype, hfinj, Subtype.val_injective,
    ⟨fun x hx => isUnit_of_isUnit_coe S x hx⟩, RingHom.ext fun _ => rfl, ?_⟩
  intro p₁ _ hp₁ hfa
  letI : Algebra A (loc S) := f.toAlgebra
  letI : Algebra A T := i.toAlgebra

  have hyint : ∀ p : Ideal A, IsIntegral A (y p) := by
    intro p
    refine ⟨X ^ q - C (π p), monic_X_pow_sub_C _ hq.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy]
    exact sub_self _
  have hgenC : ∀ z ∈ gen S, z ∈ integralClosure A T := by
    intro z hz
    have hle : gen S ≤ (integralClosure A T).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      intro t ht
      simp only [hS, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image] at ht
      rcases ht with ⟨u, -, rfl⟩ | ⟨p, -, rfl⟩
      · exact isIntegral_algebraMap
      · exact hyint p
    exact hle hz
  have hnormint : ∀ x (hx : x ∈ norm S), IsIntegral A (⟨x, norm_le_loc S hx⟩ : loc S) := by
    intro x hx
    let φ : gen S →+* integralClosure A T :=
      (gen S).val.toRingHom.codRestrict (integralClosure A T) (fun z => hgenC _ z.2)
    have h1 : IsIntegral (integralClosure A T) x :=
      IsIntegral.map_of_comp_eq φ (RingHom.id T) rfl hx.1
    have h2 : IsIntegral A x := isIntegral_trans x h1
    let g : loc S →ₐ[A] T := { (loc S).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff g Subtype.val_injective).mp h2
  let B := integralClosure A (loc S)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (fun x x' h => hfinj (congrArg Subtype.val h))
  haveI : Algebra.HasGoingDown A B := inferInstance
  let M : Submonoid B := (IsUnit.submonoid (loc S)).comap (algebraMap B (loc S))
  haveI hML : IsLocalization M (loc S) := by
    refine ⟨fun m => m.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, hsu, hsz⟩ := z.2
      let sB : B := ⟨⟨s, norm_le_loc S hs⟩, hnormint s hs⟩
      let tB : B := ⟨⟨s * z, norm_le_loc S hsz⟩, hnormint _ hsz⟩
      have hsM : sB ∈ M := isUnit_of_isUnit_coe S _ hsu
      refine ⟨(tB, ⟨sB, hsM⟩), Subtype.ext ?_⟩
      change (z : T) * s = s * z
      ring
    · have : u = v := Subtype.val_injective h
      rw [this]
  set P : Ideal B := p₁.comap (algebraMap B (loc S)) with hP
  have hPh : P.height = 1 := by
    rw [hP, ← hp₁]
    exact IsLocalization.height_comap M p₁
  have hcomap : p₁.comap f = P.comap (algebraMap A B) := by
    rw [hP, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    rfl
  have hne : P.comap (algebraMap A B) ≠ ⊥ := by
    rw [← hcomap]
    intro h
    have : a ∈ p₁.comap f := hfa
    rw [h, Ideal.mem_bot] at this
    exact ha this
  have hheight : (p₁.comap f).height = 1 := by
    rw [hcomap]
    exact height_comap_eq_one_of_goingDown P hPh hne

  have hmin : p₁.comap f ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hfa⟩, fun r hr hrp => ?_⟩
    obtain ⟨hrprime, har⟩ := hr
    by_contra hlt
    have hlt' : r < p₁.comap f := lt_of_le_of_ne hrp (fun e => hlt (e ▸ le_rfl))
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have hr0 : (⊥ : Ideal A) < r := by
      refine bot_lt_iff_ne_bot.mpr fun h => ha ?_
      have : a ∈ r := har (Ideal.mem_span_singleton_self a)
      rw [h, Ideal.mem_bot] at this
      exact this
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hr0
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt'
    rw [hheight] at h2
    have h4 : (1 : ℕ∞) ≤ r.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  have hyS : y (p₁.comap f) ∈ S := by
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hmin))
  refine ⟨hheight, π (p₁.comap f), hπ _ hheight, ⟨y (p₁.comap f), mem_loc_of_mem S hyS⟩, ?_⟩
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact hy _

end GlobalTheory.KummerEnlarge
