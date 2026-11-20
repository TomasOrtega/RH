import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `κ' _ _ F S hS`. Set `R` to `F.ring`. Use `letI : Algebra ℂ R := F.const.toAlgebra`. Use `haveI : IsScalarTower ℂ R κ' := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.EssFiniteType ℂ R := F.essFiniteType`.

Take `⟨σ, hσ⟩` from `(Algebra.essFiniteType_iff ℂ R).mp inferInstance`. Set `R' : Subalgebra ℂ κ'` to `{ F.ring.toSubring with algebraMap_mem' := F.const_mem }`. Set `T : Set κ'` to `((σ.image (fun x : R => (x : κ')) ∪ S : Finset κ') : Set κ')`. Set `A₀ : Subalgebra ℂ κ'` to `Algebra.adjoin ℂ T`. Establish `hT : T ⊆ R'`.

Introduce `x hx`. Simplify using `only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe] at hx`. Break down `hx with ⟨y, -, rfl⟩ | hx` into its components or cases. Conclude with `y.2`. Conclude with `hS x hx`.

Establish `hA₀R : A₀ ≤ R'` using `Algebra.adjoin_le hT`. Establish `memA₀ : ∀ x : R, x ∈ Algebra.adjoin ℂ (σ : Set R) → (x : κ') ∈ A₀`. Introduce `x hx`. Establish `h1 : (IsScalarTower.toAlgHom ℂ R κ') x ∈ (Algebra.adjoin ℂ (σ : Set R)).map (IsScalarTower.toAlgHom ℂ R κ')` using `⟨x, hx, rfl⟩`. Rewrite `h1` using `[AlgHom.map_adjoin]`.

Use `Algebra.adjoin_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Simplify using `only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe]`. Conclude with `Or.inl ⟨y, hy, rfl⟩`. Establish `hfg : Algebra.FiniteType ℂ A₀` using `(Subalgebra.fg_iff_finiteType A₀).mp (Subalgebra.fg_adjoin_finset _)`.

Use `haveI : Algebra.FinitePresentation ℂ A₀ := Algebra.FinitePresentation.of_finiteType.mp hfg`. Set `ι : A₀ →+* R` to `(A₀.val.toRingHom).codRestrict R (fun x => hA₀R x.2)`. Use `letI : Algebra A₀ R := ι.toAlgebra`. Use `haveI : IsScalarTower ℂ A₀ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `q : Ideal A₀` to `(IsLocalRing.maximalIdeal R).comap ι`.

Use `haveI : q.IsPrime := Ideal.comap_isPrime _ _`. Establish `hloc : IsLocalization q.primeCompl R`. Use `(isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, ht⟩`. Assume the negation of the conclusion as `h`.

Conclude with `ht ((IsLocalRing.mem_maximalIdeal _).2 h)`. Introduce `r`. Take `⟨t, htA, ht, h⟩` from `hσ r`. Use `⟨⟨⟨_, memA₀ _ h⟩, ⟨⟨_, memA₀ _ htA⟩, fun hq => ?_⟩⟩, rfl⟩` and prove the remaining obligations. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hq ht`.

Introduce `x y e`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: (x : κ') = y` using `congrArg (fun z : R => (z : κ')) e`. Simplify using `[Subtype.ext this]`. Use `haveI : Algebra.FormallySmooth ℂ R := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ R`.

Use `haveI : Algebra.IsSmoothAt ℂ q := by`. Establish `e` using `(IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars ℂ`. Conclude with `Algebra.FormallySmooth.of_equiv e.symm`. Take `⟨g, hgq, hsm⟩` from `Algebra.IsSmoothAt.exists_notMem_smooth ℂ q`. Establish `hgu : IsUnit (ι g)`.

Assume the negation of the conclusion as `h`. Conclude with `hgq ((IsLocalRing.mem_maximalIdeal _).2 h)`. Establish `hg0 : (g : κ') ≠ 0`. Introduce `h0`. Take `⟨u, hu⟩` from `hgu.exists_right_inv`.

Use `congrArg (fun x : R => (x : κ')) hu` as an intermediate fact. Simplify using `[ι, h0] at this`. Establish `hgu' : IsUnit (A₀.val g)` using `(isUnit_iff_ne_zero).2 hg0`. Set `φ : Localization.Away g →ₐ[ℂ] κ'` to `IsLocalization.Away.liftAlgHom g hgu'`. Establish `hφ : ∀ a : A₀, φ (algebraMap A₀ (Localization.Away g) a) = a`.

Introduce `a`. Simplify using `[φ]`. Establish `hginv : (g : κ')⁻¹ ∈ F.ring`. Take `⟨u, hu⟩` from `hgu.exists_right_inv`. Establish `h1 : (g : κ') * (u : κ') = 1`.

Use `congrArg (fun x : R => (x : κ')) hu` as an intermediate fact. Simplify `this` using `[ι]`. Rewrite using `[inv_eq_of_mul_eq_one_right h1]`. Conclude with `u.2`. Establish `hpow : ∀ s ∈ Submonoid.powers g, (s : κ') ≠ 0 ∧ (s : κ')⁻¹ ∈ F.ring`.

Introduce and unpack `s ⟨n, rfl⟩`. Use `⟨by simpa using pow_ne_zero n hg0, ?_⟩` and prove the remaining obligations. Simplify `pow_mem hginv n` using `[inv_pow]`. Establish `hrep : ∀ x : Localization.Away g, ∃ a : A₀, ∃ s ∈ Submonoid.powers g, φ x * (s : κ') = a`. Introduce `x`.

Take `⟨⟨a, s, hs⟩, e⟩` from `IsLocalization.surj (Submonoid.powers g) x`. Use `⟨a, s, hs, ?_⟩` and prove the remaining obligations. Use `congrArg φ e` as an intermediate fact. Rewrite `this` using `[map_mul, hφ, hφ]`. Conclude with `this`.

Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨a, s, hs⟩, e⟩` from `IsLocalization.surj (Submonoid.powers g) x`. Establish `h1` using `congrArg φ e`.

Rewrite `h1` using `[map_mul, hφ, hφ, hx, zero_mul]`. Establish `ha : a = 0` using `Subtype.ext h1.symm`. Rewrite `e` using `[ha, map_zero]`. Conclude with `(IsLocalization.map_units (Localization.Away g) (⟨s, hs⟩ : Submonoid.powers g)).mul_left_eq_zero.1 e`. Set `A : Subalgebra ℂ κ'` to `φ.range`.

Use `haveI : Algebra.Smooth ℂ A := Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φ hinj)`. Establish `hA₀A : ∀ a ∈ A₀, a ∈ A` using `fun a ha => ⟨algebraMap A₀ _ ⟨a, ha⟩, hφ ⟨a, ha⟩⟩`. Use `⟨A, inferInstance, ?_, fun x hx => hA₀A x (Algebra.subset_adjoin ?_), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨a, s, hs, e⟩` from `hrep x`.

Take `⟨hs0, hsi⟩` from `hpow s hs`. Establish `: φ x = a * (s : κ')⁻¹` using `by rw [← e, mul_assoc, mul_inv_cancel₀ hs0, mul_one]`. Use `show φ x ∈ F.ring`. Rewrite using `[this]`. Conclude with `F.ring.mul_mem _ _ (hA₀R a.2) hsi`.

Simplify using `only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe]`. Conclude with `Or.inr hx`. Introduce `f`. Take `⟨r1, hr1, r2, hr2, hr20, e⟩` from `F.isLocModel.frac f`. Take `⟨t1, ht1A, ht1, h1⟩` from `hσ ⟨r1, hr1⟩`.

Take `⟨t2, ht2A, ht2, h2⟩` from `hσ ⟨r2, hr2⟩`. Establish `unit_ne : ∀ t : R, IsUnit t → (t : κ') ≠ 0`. Introduce `t ht h0`. Take `⟨u, hu⟩` from `ht.exists_right_inv`. Use `congrArg (fun x : R => (x : κ')) hu` as an intermediate fact.

Simplify using `[h0] at this`. Use `⟨r1 * t1 * t2, hA₀A _ ?_, r2 * t2 * t1, hA₀A _ ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using A₀.mul_mem (memA₀ _ h1) (memA₀ _ ht2A)`. Simplify using `using A₀.mul_mem (memA₀ _ h2) (memA₀ _ ht1A)`. Conclude with `mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)`.

Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Place.exists_smooth_subalgebra : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (S : Finset κ'),
    (∀ x ∈ S, x ∈ F.ring) → ∃ A : Subalgebra ℂ κ', Algebra.Smooth ℂ A ∧
      A.toSubring ≤ F.ring.toSubring ∧ (∀ x ∈ S, x ∈ A) ∧
      ∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
  intro κ' _ _ F S hS
  classical
  let R := F.ring
  letI : Algebra ℂ R := F.const.toAlgebra
  haveI : IsScalarTower ℂ R κ' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := F.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  let R' : Subalgebra ℂ κ' :=
    { F.ring.toSubring with algebraMap_mem' := F.const_mem }
  let T : Set κ' := ((σ.image (fun x : R => (x : κ')) ∪ S : Finset κ') : Set κ')
  let A₀ : Subalgebra ℂ κ' := Algebra.adjoin ℂ T
  have hT : T ⊆ R' := by
    intro x hx
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hx
    rcases hx with ⟨y, -, rfl⟩ | hx
    · exact y.2
    · exact hS x hx
  have hA₀R : A₀ ≤ R' := Algebra.adjoin_le hT

  have memA₀ : ∀ x : R, x ∈ Algebra.adjoin ℂ (σ : Set R) → (x : κ') ∈ A₀ := by
    intro x hx
    have h1 : (IsScalarTower.toAlgHom ℂ R κ') x ∈
        (Algebra.adjoin ℂ (σ : Set R)).map (IsScalarTower.toAlgHom ℂ R κ') := ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe]
    exact Or.inl ⟨y, hy, rfl⟩
  have hfg : Algebra.FiniteType ℂ A₀ :=
    (Subalgebra.fg_iff_finiteType A₀).mp (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FinitePresentation ℂ A₀ := Algebra.FinitePresentation.of_finiteType.mp hfg
  let ι : A₀ →+* R := (A₀.val.toRingHom).codRestrict R (fun x => hA₀R x.2)
  letI : Algebra A₀ R := ι.toAlgebra
  haveI : IsScalarTower ℂ A₀ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let q : Ideal A₀ := (IsLocalRing.maximalIdeal R).comap ι
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization q.primeCompl R := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      by_contra h; exact ht ((IsLocalRing.mem_maximalIdeal _).2 h)
    · intro r
      obtain ⟨t, htA, ht, h⟩ := hσ r
      refine ⟨⟨⟨_, memA₀ _ h⟩, ⟨⟨_, memA₀ _ htA⟩, fun hq => ?_⟩⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · intro x y e
      refine ⟨1, ?_⟩
      have : (x : κ') = y := congrArg (fun z : R => (z : κ')) e
      simp [Subtype.ext this]
  haveI : Algebra.FormallySmooth ℂ R := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ R
  haveI : Algebra.IsSmoothAt ℂ q := by
    have e := (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars ℂ
    exact Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨g, hgq, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℂ q
  have hgu : IsUnit (ι g) := by
    by_contra h; exact hgq ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hg0 : (g : κ') ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have := congrArg (fun x : R => (x : κ')) hu
    simp [ι, h0] at this
  have hgu' : IsUnit (A₀.val g) := (isUnit_iff_ne_zero).2 hg0
  let φ : Localization.Away g →ₐ[ℂ] κ' := IsLocalization.Away.liftAlgHom g hgu'

  have hφ : ∀ a : A₀, φ (algebraMap A₀ (Localization.Away g) a) = a := by
    intro a; simp [φ]
  have hginv : (g : κ')⁻¹ ∈ F.ring := by
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    have h1 : (g : κ') * (u : κ') = 1 := by
      have := congrArg (fun x : R => (x : κ')) hu; simpa [ι] using this
    rw [inv_eq_of_mul_eq_one_right h1]; exact u.2
  have hpow : ∀ s ∈ Submonoid.powers g, (s : κ') ≠ 0 ∧ (s : κ')⁻¹ ∈ F.ring := by
    rintro s ⟨n, rfl⟩
    refine ⟨by simpa using pow_ne_zero n hg0, ?_⟩
    simpa [inv_pow] using pow_mem hginv n
  have hrep : ∀ x : Localization.Away g, ∃ a : A₀, ∃ s ∈ Submonoid.powers g,
      φ x * (s : κ') = a := by
    intro x
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨a, s, hs, ?_⟩
    have := congrArg φ e
    rw [map_mul, hφ, hφ] at this
    exact this
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    have h1 := congrArg φ e
    rw [map_mul, hφ, hφ, hx, zero_mul] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units (Localization.Away g) (⟨s, hs⟩ : Submonoid.powers g)).mul_left_eq_zero.1 e
  let A : Subalgebra ℂ κ' := φ.range
  haveI : Algebra.Smooth ℂ A := Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φ hinj)
  have hA₀A : ∀ a ∈ A₀, a ∈ A := fun a ha => ⟨algebraMap A₀ _ ⟨a, ha⟩, hφ ⟨a, ha⟩⟩
  refine ⟨A, inferInstance, ?_, fun x hx => hA₀A x (Algebra.subset_adjoin ?_), ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, s, hs, e⟩ := hrep x
    obtain ⟨hs0, hsi⟩ := hpow s hs
    have : φ x = a * (s : κ')⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    show φ x ∈ F.ring
    rw [this]; exact F.ring.mul_mem _ _ (hA₀R a.2) hsi
  · simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe]; exact Or.inr hx
  · intro f
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := F.isLocModel.frac f
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    have unit_ne : ∀ t : R, IsUnit t → (t : κ') ≠ 0 := by
      intro t ht h0
      obtain ⟨u, hu⟩ := ht.exists_right_inv
      have := congrArg (fun x : R => (x : κ')) hu
      simp [h0] at this
    refine ⟨r1 * t1 * t2, hA₀A _ ?_, r2 * t2 * t1, hA₀A _ ?_, ?_, ?_⟩
    · simpa using A₀.mul_mem (memA₀ _ h1) (memA₀ _ ht2A)
    · simpa using A₀.mul_mem (memA₀ _ h2) (memA₀ _ ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring

end GlobalTheory.FieldPair
