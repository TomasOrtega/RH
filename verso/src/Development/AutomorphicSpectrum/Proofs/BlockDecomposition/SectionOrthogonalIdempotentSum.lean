import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open CategoryTheory.Limits

namespace GlobalTheory.CompanionTheory.SecAdd

variable {S : Type} [CommRing S]

/- English proof (translation)
Establish `hu : IsUnit (algebraMap S (Localization.Away e) e)` using `IsLocalization.Away.algebraMap_isUnit e`. Establish `h : algebraMap S (Localization.Away e) e * algebraMap S (Localization.Away e) e = algebraMap S (Localization.Away e) e * 1`. Rewrite using `[← map_mul, he.eq, mul_one]`. Conclude with `hu.mul_left_cancel h`.
-/
theorem away_self_eq_one {e : S} (he : IsIdempotentElem e) :
    algebraMap S (Localization.Away e) e = 1 := by
  have hu : IsUnit (algebraMap S (Localization.Away e) e) := IsLocalization.Away.algebraMap_isUnit e
  have h : algebraMap S (Localization.Away e) e * algebraMap S (Localization.Away e) e
      = algebraMap S (Localization.Away e) e * 1 := by
    rw [← map_mul, he.eq, mul_one]
  exact hu.mul_left_cancel h

/- English proof (translation)
Use `congrArg (algebraMap S (Localization.Away e)) h` as an intermediate fact. Rewrite `this` using `[map_mul, away_self_eq_one he, one_mul, map_zero]`. Then use the resulting hypothesis.
-/
theorem away_orth_eq_zero {e x : S} (he : IsIdempotentElem e) (h : e * x = 0) :
    algebraMap S (Localization.Away e) x = 0 := by
  have := congrArg (algebraMap S (Localization.Away e)) h
  rwa [map_mul, away_self_eq_one he, one_mul, map_zero] at this

/- English proof (translation)
Introduce `b`. Take `⟨⟨x, s⟩, hx⟩` from `IsLocalization.surj (Submonoid.powers e) b`. Take `⟨n, hn⟩` from `s.2`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `: algebraMap S (Localization.Away e) (s : S) = 1`.

Rewrite using `[← hn, map_pow, away_self_eq_one he, one_pow]`. Simplify using `only [this, mul_one] at hx`. Conclude with `hx.symm`.
-/
theorem away_surj {e : S} (he : IsIdempotentElem e) :
    Function.Surjective (algebraMap S (Localization.Away e)) := by
  intro b
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers e) b
  obtain ⟨n, hn⟩ := s.2
  refine ⟨x, ?_⟩
  have : algebraMap S (Localization.Away e) (s : S) = 1 := by
    rw [← hn, map_pow, away_self_eq_one he, one_pow]
  simp only [this, mul_one] at hx
  exact hx.symm

/- English proof (translation)
Take `⟨⟨_, n, rfl⟩, hc⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers e) _ x).1 h`. Break down `n with _ | n` into its components or cases. Simplify using `at hc`. Simplify using `[hc]`. Establish `: e ^ (n + 1) = e` using `he.pow_succ_eq n`.

Simplify `hc` using `[this]`.
-/
theorem away_ker {e x : S} (he : IsIdempotentElem e)
    (h : algebraMap S (Localization.Away e) x = 0) : e * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) _ x).1 h
  rcases n with _ | n
  · simp at hc
    simp [hc]
  · have : e ^ (n + 1) = e := he.pow_succ_eq n
    simpa [this] using hc

/- English proof (translation)
Establish `h' : e' * e = 0` using `by rw [mul_comm, h]`. Unfold `IsIdempotentElem`. Rewrite using `[add_mul, mul_add, mul_add, h, h', he.eq, he'.eq, add_zero, zero_add]`.
-/
theorem isIdempotentElem_add {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) : IsIdempotentElem (e + e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  unfold IsIdempotentElem
  rw [add_mul, mul_add, mul_add, h, h', he.eq, he'.eq, add_zero, zero_add]

/- English proof (translation)
Establish `h' : e' * e = 0` using `by rw [mul_comm, h]`. Establish `key : ∀ z : S, algebraMap S (Localization.Away e × Localization.Away e') z = 0 ↔ (e + e') * z = 0`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Establish `h1 : algebraMap S (Localization.Away e) z = 0` using `congrArg Prod.fst hz`. Establish `h2 : algebraMap S (Localization.Away e') z = 0` using `congrArg Prod.snd hz`. Rewrite using `[add_mul, away_ker he h1, away_ker he' h2, add_zero]`. Introduce `hz`. Establish `h1 : e * z = 0`.

Use `congrArg (e * ·) hz` as an intermediate fact. Simplify using `only [mul_zero] at this`. Rewrite using `[← this, ← mul_assoc, mul_add, he.eq, h, add_zero]`. Establish `h2 : e' * z = 0`. Use `congrArg (e' * ·) hz` as an intermediate fact.

Simplify using `only [mul_zero] at this`. Rewrite using `[← this, ← mul_assoc, mul_add, he'.eq, h', zero_add]`. Conclude with `Prod.ext (away_orth_eq_zero he h1) (away_orth_eq_zero he' h2)`. Use `IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_add he he' h) ?_ ?_` and prove the remaining obligations. Introduce `x y`.

Rewrite using `[← sub_eq_zero, ← map_sub, key, mul_sub, sub_eq_zero]`. Introduce and unpack `⟨b, c⟩`. Take `⟨x, rfl⟩` from `away_surj he b`. Take `⟨y, rfl⟩` from `away_surj he' c`. Use `⟨e * x + e' * y, Prod.ext ?_ ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap S (Localization.Away e) (e * x + e' * y) = _`. Establish `: algebraMap S (Localization.Away e) e' = 0` using `away_orth_eq_zero he h`. Rewrite using `[map_add, map_mul, map_mul, away_self_eq_one he, this, one_mul, zero_mul, add_zero]`. Express the relevant statement in the definitionally equal form `algebraMap S (Localization.Away e') (e * x + e' * y) = _`. Establish `: algebraMap S (Localization.Away e') e = 0` using `away_orth_eq_zero he' h'`.

Rewrite using `[map_add, map_mul, map_mul, away_self_eq_one he', this, one_mul, zero_mul, zero_add]`.
-/
theorem isLocalization_prod {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) :
    IsLocalization.Away (e + e') (Localization.Away e × Localization.Away e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  have key : ∀ z : S, algebraMap S (Localization.Away e × Localization.Away e') z = 0 ↔
      (e + e') * z = 0 := by
    intro z
    constructor
    · intro hz
      have h1 : algebraMap S (Localization.Away e) z = 0 := congrArg Prod.fst hz
      have h2 : algebraMap S (Localization.Away e') z = 0 := congrArg Prod.snd hz
      rw [add_mul, away_ker he h1, away_ker he' h2, add_zero]
    · intro hz
      have h1 : e * z = 0 := by
        have := congrArg (e * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he.eq, h, add_zero]
      have h2 : e' * z = 0 := by
        have := congrArg (e' * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he'.eq, h', zero_add]
      exact Prod.ext (away_orth_eq_zero he h1) (away_orth_eq_zero he' h2)
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_add he he' h) ?_ ?_
  · intro x y
    rw [← sub_eq_zero, ← map_sub, key, mul_sub, sub_eq_zero]
  · rintro ⟨b, c⟩
    obtain ⟨x, rfl⟩ := away_surj he b
    obtain ⟨y, rfl⟩ := away_surj he' c
    refine ⟨e * x + e' * y, Prod.ext ?_ ?_⟩
    · change algebraMap S (Localization.Away e) (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e) e' = 0 := away_orth_eq_zero he h
      rw [map_add, map_mul, map_mul, away_self_eq_one he, this, one_mul, zero_mul, add_zero]
    · change algebraMap S (Localization.Away e') (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e') e = 0 := away_orth_eq_zero he' h'
      rw [map_add, map_mul, map_mul, away_self_eq_one he', this, one_mul, zero_mul, zero_add]

/- English proof (translation)
Introduce `S _ Y f e e' he he' h ⟨s, hs⟩ ⟨s', hs'⟩`. Use `haveI := isLocalization_prod he he' h`. Set `B` to `Localization.Away e`. Set `C` to `Localization.Away e'`. Set `A` to `Localization.Away (e + e')`.

Set `φ : (B × C) ≃ₐ[S] A` to `IsLocalization.algEquiv (Submonoid.powers (e + e')) (B × C) A`. Set `t : Spec (CommRingCat.of (B × C)) ⟶ Y` to `inv (coprodSpec B C) ≫ coprod.desc s s'`. Establish `ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B × C)))`. Rewrite using `[← cancel_epi (coprodSpec B C)]`. Simplify using `only [t, Category.assoc, IsIso.hom_inv_id_assoc]`.

Apply `coprod.hom_ext` to reduce the goal to its premises. Rewrite using `[coprod.inl_desc_assoc, hs, coprodSpec_inl_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[coprod.inr_desc_assoc, hs', coprodSpec_inr_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.

Use `⟨Spec.map (CommRingCat.ofHom (φ : B × C →+* A)) ≫ t, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ht, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x`. Conclude with `φ.commutes x`.
-/
theorem secOn_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' →
    e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  intro S _ Y f e e' he he' h ⟨s, hs⟩ ⟨s', hs'⟩
  haveI := isLocalization_prod he he' h
  let B := Localization.Away e
  let C := Localization.Away e'
  let A := Localization.Away (e + e')
  let φ : (B × C) ≃ₐ[S] A :=
    IsLocalization.algEquiv (Submonoid.powers (e + e')) (B × C) A
  let t : Spec (CommRingCat.of (B × C)) ⟶ Y := inv (coprodSpec B C) ≫ coprod.desc s s'
  have ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B × C))) := by
    rw [← cancel_epi (coprodSpec B C)]
    simp only [t, Category.assoc, IsIso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, hs, coprodSpec_inl_assoc, ← Spec.map_comp]
      rfl
    · rw [coprod.inr_desc_assoc, hs', coprodSpec_inr_assoc, ← Spec.map_comp]
      rfl
  refine ⟨Spec.map (CommRingCat.ofHom (φ : B × C →+* A)) ≫ t, ?_⟩
  rw [Category.assoc, ht, ← Spec.map_comp]
  congr 1
  ext x
  exact φ.commutes x

end GlobalTheory.CompanionTheory.SecAdd
