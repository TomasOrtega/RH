import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

/- English proof (translation)
Use `UniqueFactorizationMonoid.induction_on_prime y ?_ ?_ ?_` and prove the remaining obligations. Introduce `h`. Conclude with `absurd rfl h`. Introduce `u hu _ _`. Conclude with `⟨0, hu.dvd⟩`.

Introduce `z p hz hp ih _ h`. Take `⟨n, hn⟩` from `ih hz fun q hq hqz => h q hq (hqz.mul_left p)`. Conclude with `⟨n + 1, by rw [pow_succ']; exact mul_dvd_mul (h p hp (dvd_mul_right _ _)) hn⟩`.
-/
theorem exists_dvd_pow_of_forall_prime_dvd {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (a y : A) :
    y ≠ 0 → (∀ q, Prime q → q ∣ y → q ∣ a) → ∃ n : ℕ, y ∣ a ^ n := by
  refine UniqueFactorizationMonoid.induction_on_prime y ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _ _; exact ⟨0, hu.dvd⟩
  · intro z p hz hp ih _ h
    obtain ⟨n, hn⟩ := ih hz fun q hq hqz => h q hq (hqz.mul_left p)
    exact ⟨n + 1, by rw [pow_succ']; exact mul_dvd_mul (h p hp (dvd_mul_right _ _)) hn⟩

/- English proof (translation)
Take `⟨p₀, hp₀⟩` from `hW`. Take `⟨s, hs, x, e⟩` from `hv p₀ hp₀`. Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ p₀.asIdeal.zero_mem)`. Take `⟨y, x', c, hrel, rfl, rfl⟩` from `UniqueFactorizationMonoid.exists_reduced_factors s hs0 x`. Establish `hc : c ≠ 0` using `left_ne_zero_of_mul hs0`.

Establish `hy : y ≠ 0` using `right_ne_zero_of_mul hs0`. Establish `e' : φ x' = φ y * v`. Rewrite `e` using `[map_mul, map_mul, _root_.mul_assoc]`. Conclude with `mul_left_cancel₀ ((map_ne_zero_iff _ hφ).mpr hc) e`. Take `⟨n, z, hz⟩` from `exists_dvd_pow_of_forall_prime_dvd a y hy fun q hq hqy => by`.

Use `ha q ⟨Ideal.span {q}, (Ideal.span_singleton_prime hq.ne_zero).2 hq⟩ hq rfl fun hm => ?_` and prove the remaining obligations. Take `⟨t, ht, w, ew⟩` from `hv _ hm`. Use `ht (Ideal.mem_span_singleton.2 (hqy.trans (hrel.dvd_of_dvd_mul_right ⟨w, hφ ?_⟩)))` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, e', ew, mul_left_comm]`. Use `⟨n, z * x', ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, hz, map_mul, map_mul, e']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pow_mul_mem_range_of_local_denominators {A B : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (hφ : Function.Injective φ) (W : Set (PrimeSpectrum A)) (hW : W.Nonempty) (a : A)
    (ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} → p ∉ W → q ∣ a)
    (v : B) (hv : ∀ p ∈ W, ∃ s, s ∉ p.asIdeal ∧ ∃ x, φ x = φ s * v) :
    ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v := by
  obtain ⟨p₀, hp₀⟩ := hW
  obtain ⟨s, hs, x, e⟩ := hv p₀ hp₀
  have hs0 : s ≠ 0 := fun h => hs (h ▸ p₀.asIdeal.zero_mem)
  obtain ⟨y, x', c, hrel, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors s hs0 x
  have hc : c ≠ 0 := left_ne_zero_of_mul hs0
  have hy : y ≠ 0 := right_ne_zero_of_mul hs0
  have e' : φ x' = φ y * v := by
    rw [map_mul, map_mul, _root_.mul_assoc] at e
    exact mul_left_cancel₀ ((map_ne_zero_iff _ hφ).mpr hc) e
  obtain ⟨n, z, hz⟩ := exists_dvd_pow_of_forall_prime_dvd a y hy fun q hq hqy => by
    refine ha q ⟨Ideal.span {q}, (Ideal.span_singleton_prime hq.ne_zero).2 hq⟩ hq rfl fun hm => ?_
    obtain ⟨t, ht, w, ew⟩ := hv _ hm
    refine ht (Ideal.mem_span_singleton.2 (hqy.trans (hrel.dvd_of_dvd_mul_right ⟨w, hφ ?_⟩)))
    rw [map_mul, map_mul, e', ew, mul_left_comm]
  refine ⟨n, z * x', ?_⟩
  rw [← map_pow, hz, map_mul, map_mul, e']
  ring

/- English proof (translation)
Introduce `A _ _ _ _ U hU hne`. Establish `hloc : ∀ p : PrimeSpectrum A, p ∈ U → ∃ f : A, p ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U`. Introduce `p hp`. Take `⟨_, ⟨f, rfl⟩, h1, h2⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hp U.isOpen`. Conclude with `⟨f, h1, h2⟩`.

Take `⟨p₀, hp₀⟩` from `hne`. Take `⟨f, hf, hfU⟩` from `hloc p₀ hp₀`. Establish `hf0 : f ≠ 0` using `fun h => hf (h ▸ p₀.asIdeal.zero_mem)`. Set `a : A` to `((UniqueFactorizationMonoid.factors f).filter fun q => ∃ p : PrimeSpectrum A, p.asIdeal = Ideal.span {q} ∧ p ∉ U).prod`. Establish `ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} → p ∉ U → q ∣ a`.

Introduce `q p hq hp hpU`. Establish `hqf : q ∣ f`. Rewrite using `[← Ideal.mem_span_singleton, ← hp]`. Assume the negation of the conclusion as `h`. Conclude with `hpU (hfU h)`.

Take `⟨r, hr, hqr⟩` from `UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf0 hq.irreducible hqf`. Use `hqr.dvd.trans (Multiset.dvd_prod (Multiset.mem_filter.2 ⟨hr, p, ?_, hpU⟩))` and prove the remaining obligations. Rewrite using `[hp]`. Conclude with `Ideal.span_singleton_eq_span_singleton.2 hqr`. Use `⟨a, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Introduce `p hp hpa`. Use `p.isPrime` as an intermediate fact. Take `⟨q, hq, hqp⟩` from `(Ideal.IsPrime.multiset_prod_mem_iff_exists_mem p.isPrime _).1 hpa`. Take `⟨-, p', hp', hp'U⟩` from `Multiset.mem_filter.1 hq`. Take `⟨g, hg, hgU⟩` from `hloc p hp`.

Use `hp'U (hgU fun h => hg ?_)` and prove the remaining obligations. Establish `h' : g ∈ p'.asIdeal` using `h`. Rewrite `h'` using `[hp']`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 hqp h'`. Establish `: Nonempty U` using `⟨⟨_, hp₀⟩⟩`.

Establish `hinj` using `map_injective_of_isIntegral (Spec (CommRingCat.of A)) (homOfLE (le_top : U ≤ ⊤))`. Set `φ : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of A), U)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op`. Establish `hφ : Function.Injective φ` using `hinj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1`. Establish `key : ∀ (v : Γ(Spec (CommRingCat.of A), U)) (p : PrimeSpectrum A), p ∈ U → ∃ s, s ∉ p.asIdeal ∧ ∃ a, φ a = φ s * v`. Introduce `v p hp`.

Set `x : Spec (CommRingCat.of A)` to `p`. Take `⟨⟨a, s⟩, e⟩` from `IsLocalization.surj (S := (Spec.structureSheaf A).presheaf.stalk p) p.asIdeal.primeCompl ((Spec (CommRingCat.of A)).presheaf.germ U x hp v)`. Use `⟨s, s.2, a, germ_injective_of_isIntegral _ x hp ?_⟩` and prove the remaining obligations. Establish `hg : ∀ a : A, (Spec (CommRingCat.of A)).presheaf.germ U x hp (φ a) = algebraMap A ((Spec.structureSheaf A).presheaf.stalk p) a`. Introduce `a`.

Conclude with `((Spec (CommRingCat.of A)).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).trans rfl`. Rewrite using `[map_mul, hg, hg]`. Conclude with `e.symm.trans (mul_comm _ _)`. Establish `key2 : ∀ v : Γ(Spec (CommRingCat.of A), U), ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v` using `fun v => exists_pow_mul_mem_range_of_local_denominators φ.hom hφ (U : Set (Spec (CommRingCat.of A))) ⟨p₀, hp₀⟩ a ha v (key v)`. Introduce `p hpa`.

Assume the negation of the conclusion as `hpU`. Establish `hspan : Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}) = ⊤`. Rewrite using `[← hU.self_le_iSup_basicOpen_iff]`. Introduce `x hx`. Take `⟨g, hg, hgU⟩` from `hloc x hx`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨φ g, g, hgU, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : (Spec (CommRingCat.of A)).basicOpen (φ g) = U ⊓ PrimeSpectrum.basicOpen g`. Rewrite using `[← basicOpen_eq_of_affine (R := CommRingCat.of A) g]`. Conclude with `Scheme.basicOpen_res _ _ (homOfLE (le_top : U ≤ ⊤)).op`. Use `show x ∈ (Spec (CommRingCat.of A)).basicOpen (φ g)`.

Rewrite using `[e]`. Conclude with `⟨hx, hg⟩`. Establish `hall : ∀ v ∈ Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}), ∃ (n : ℕ) (x : A), x ∈ p.asIdeal ∧ φ x = φ a ^ n * v`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem v hv`. Take `⟨g, hg, rfl⟩` from `hv`. Use `⟨0, g, ?_, by simp⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hpU (hg h)`.

Consider the case `zero => exact ⟨0, 0, p.asIdeal.zero_mem, by simp⟩`. Consider the case `add v w _ _ hv hw`. Take `⟨n, x, hx, e⟩` from `hv`. Take `⟨m, y, hy, e'⟩` from `hw`. Use `⟨n + m, a ^ m * x + a ^ n * y, p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hx) (p.asIdeal.mul_mem_left _ hy), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, e, e']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c v _ hv`. Take `⟨n, x, hx, e⟩` from `hv`. Take `⟨m, y, e'⟩` from `key2 c`.

Use `⟨n + m, y * x, p.asIdeal.mul_mem_left _ hx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, e, e', smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, x, hx, e⟩` from `hall 1 (hspan ▸ Submodule.mem_top)`. Rewrite `e` using `[_root_.mul_one, ← map_pow]`.

Rewrite `hx` using `[hφ e]`. Conclude with `hpa (p.isPrime.mem_of_pow_mem n hx)`.
-/
theorem exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A] (U : (Spec (CommRingCat.of A)).Opens), IsAffineOpen U → (U : Set (Spec (CommRingCat.of A))).Nonempty → ∃ a : A, U = PrimeSpectrum.basicOpen a := by
  classical
  intro A _ _ _ _ U hU hne
  have hloc : ∀ p : PrimeSpectrum A, p ∈ U → ∃ f : A,
      p ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U := by
    intro p hp
    obtain ⟨_, ⟨f, rfl⟩, h1, h2⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hp U.isOpen
    exact ⟨f, h1, h2⟩
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨f, hf, hfU⟩ := hloc p₀ hp₀
  have hf0 : f ≠ 0 := fun h => hf (h ▸ p₀.asIdeal.zero_mem)
  let a : A := ((UniqueFactorizationMonoid.factors f).filter fun q =>
    ∃ p : PrimeSpectrum A, p.asIdeal = Ideal.span {q} ∧ p ∉ U).prod
  have ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} →
      p ∉ U → q ∣ a := by
    intro q p hq hp hpU
    have hqf : q ∣ f := by
      rw [← Ideal.mem_span_singleton, ← hp]
      by_contra h
      exact hpU (hfU h)
    obtain ⟨r, hr, hqr⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf0 hq.irreducible hqf
    refine hqr.dvd.trans (Multiset.dvd_prod (Multiset.mem_filter.2 ⟨hr, p, ?_, hpU⟩))
    rw [hp]
    exact Ideal.span_singleton_eq_span_singleton.2 hqr
  refine ⟨a, le_antisymm ?_ ?_⟩
  · intro p hp hpa
    have := p.isPrime
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem p.isPrime _).1 hpa
    obtain ⟨-, p', hp', hp'U⟩ := Multiset.mem_filter.1 hq
    obtain ⟨g, hg, hgU⟩ := hloc p hp
    refine hp'U (hgU fun h => hg ?_)
    have h' : g ∈ p'.asIdeal := h
    rw [hp'] at h'
    exact (Ideal.span_singleton_le_iff_mem _).2 hqp h'
  · have : Nonempty U := ⟨⟨_, hp₀⟩⟩
    have hinj := map_injective_of_isIntegral (Spec (CommRingCat.of A)) (homOfLE (le_top : U ≤ ⊤))
    let φ : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of A), U) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    have hφ : Function.Injective φ :=
      hinj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    have key : ∀ (v : Γ(Spec (CommRingCat.of A), U)) (p : PrimeSpectrum A), p ∈ U →
        ∃ s, s ∉ p.asIdeal ∧ ∃ a, φ a = φ s * v := by
      intro v p hp
      let x : Spec (CommRingCat.of A) := p
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (S := (Spec.structureSheaf A).presheaf.stalk p)
        p.asIdeal.primeCompl ((Spec (CommRingCat.of A)).presheaf.germ U x hp v)
      refine ⟨s, s.2, a, germ_injective_of_isIntegral _ x hp ?_⟩
      have hg : ∀ a : A, (Spec (CommRingCat.of A)).presheaf.germ U x hp (φ a) =
          algebraMap A ((Spec.structureSheaf A).presheaf.stalk p) a := by
        intro a
        exact ((Spec (CommRingCat.of A)).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hp
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).trans rfl
      rw [map_mul, hg, hg]
      exact e.symm.trans (mul_comm _ _)
    have key2 : ∀ v : Γ(Spec (CommRingCat.of A), U), ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v :=
      fun v => exists_pow_mul_mem_range_of_local_denominators φ.hom hφ
        (U : Set (Spec (CommRingCat.of A))) ⟨p₀, hp₀⟩ a ha v (key v)
    intro p hpa
    by_contra hpU
    have hspan : Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}) = ⊤ := by
      rw [← hU.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨g, hg, hgU⟩ := hloc x hx
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨φ g, g, hgU, rfl⟩, ?_⟩
      have e : (Spec (CommRingCat.of A)).basicOpen (φ g) = U ⊓ PrimeSpectrum.basicOpen g := by
        rw [← basicOpen_eq_of_affine (R := CommRingCat.of A) g]
        exact Scheme.basicOpen_res _ _ (homOfLE (le_top : U ≤ ⊤)).op
      show x ∈ (Spec (CommRingCat.of A)).basicOpen (φ g)
      rw [e]
      exact ⟨hx, hg⟩
    have hall : ∀ v ∈ Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}),
        ∃ (n : ℕ) (x : A), x ∈ p.asIdeal ∧ φ x = φ a ^ n * v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨g, hg, rfl⟩ := hv
        refine ⟨0, g, ?_, by simp⟩
        by_contra h
        exact hpU (hg h)
      | zero => exact ⟨0, 0, p.asIdeal.zero_mem, by simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, hy, e'⟩ := hw
        refine ⟨n + m, a ^ m * x + a ^ n * y,
          p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hx) (p.asIdeal.mul_mem_left _ hy), ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, e, e']
        ring
      | smul c v _ hv =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, e'⟩ := key2 c
        refine ⟨n + m, y * x, p.asIdeal.mul_mem_left _ hx, ?_⟩
        rw [map_mul, e, e', smul_eq_mul]
        ring
    obtain ⟨n, x, hx, e⟩ := hall 1 (hspan ▸ Submodule.mem_top)
    rw [_root_.mul_one, ← map_pow] at e
    rw [hφ e] at hx
    exact hpa (p.isPrime.mem_of_pow_mem n hx)

end GlobalTheory
