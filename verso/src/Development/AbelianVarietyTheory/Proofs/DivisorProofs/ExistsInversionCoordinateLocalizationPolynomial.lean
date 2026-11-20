import Mathlib

open Polynomial

namespace GlobalTheory

noncomputable def awayLiftAlgHom {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) : Localization.Away P →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers P) (f := f)
    (by rintro ⟨_, n, rfl⟩; simpa using h.pow n)

/- English proof (translation)
Simplify using `[awayLiftAlgHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]`.
-/
theorem awayLiftAlgHom_algebraMap {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) (q : k[X]) :
    awayLiftAlgHom P f h (algebraMap k[X] (Localization.Away P) q) = f q := by
  simp [awayLiftAlgHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

/- English proof (translation)
Use `letI : Invertible x := invertibleOfRightInverse x y h`. Establish `hinv : (⅟x : B) = y` using `invOf_eq_right_inv h`. Use `eval₂_reverse_mul_pow (algebraMap k B) x P` as an intermediate fact. Rewrite `this` using `[hinv]`. Simplify `this` using `[aeval_def]`.
-/
theorem aeval_reverse_mul_pow_of_mul_eq_one {k : Type} [Field k] {B : Type} [CommRing B]
    [Algebra k B] (x y : B) (h : x * y = 1) (P : k[X]) :
    aeval y P.reverse * x ^ P.natDegree = aeval x P := by
  letI : Invertible x := invertibleOfRightInverse x y h
  have hinv : (⅟x : B) = y := invOf_eq_right_inv h
  have := eval₂_reverse_mul_pow (algebraMap k B) x P
  rw [hinv] at this
  simpa [aeval_def] using this

/- English proof (translation)
Establish `: (IsScalarTower.toAlgHom k k[X] B) = aeval (algebraMap k[X] B X)` using `Polynomial.algHom_ext (by simp)`. Simplify using `using DFunLike.congr_fun this p`.
-/
theorem algebraMap_eq_aeval_X {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    [Algebra k[X] B] [IsScalarTower k k[X] B] (p : k[X]) :
    algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by
  have : (IsScalarTower.toAlgHom k k[X] B) = aeval (algebraMap k[X] B X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun this p

/- English proof (translation)
Establish `hrev : P.reverse ≠ 0` using `fun h => hP (reverse_eq_zero.mp h)`. Use `⟨X * P.reverse, mul_ne_zero X_ne_zero hrev, ?_⟩` and prove the remaining obligations. Use `set C := Localization.Away (X * P)`. Use `set u : C := IsLocalization.Away.invSelf (X * P)`. Establish `hu : algebraMap k[X] C (X * P) * u = 1` using `IsLocalization.Away.mul_invSelf _`.

Use `set xC : C := algebraMap k[X] C X`. Use `set xi : C := algebraMap k[X] C P * u`. Establish `hxC : xC * xi = 1` using `by rw [← hu, map_mul]; ring`. Establish `hPC : IsUnit (algebraMap k[X] C P)` using `isUnit_iff_exists_inv.mpr ⟨xC * u, by rw [← hu, map_mul]; ring⟩`. Establish `hxi : IsUnit xi` using `isUnit_iff_exists_inv'.mpr ⟨xC, hxC⟩`.

Establish `hτ : IsUnit (aeval xi (X * P.reverse))`. Rewrite using `[map_mul, aeval_X]`. Use `hxi.mul ?_` and prove the remaining obligations. Establish `key` using `aeval_reverse_mul_pow_of_mul_eq_one (k := k) xC xi hxC P`. Rewrite `key` using `[← algebraMap_eq_aeval_X]`.

Conclude with `isUnit_of_mul_isUnit_left (key ▸ hPC)`. Set `τ` to `awayLiftAlgHom (X * P.reverse) (aeval xi) hτ`. Use `set B := Localization.Away (X * P.reverse)`. Use `set v : B := IsLocalization.Away.invSelf (X * P.reverse)`. Establish `hv : algebraMap k[X] B (X * P.reverse) * v = 1` using `IsLocalization.Away.mul_invSelf _`.

Use `set yB : B := algebraMap k[X] B X`. Use `set yi : B := algebraMap k[X] B P.reverse * v`. Establish `hyB : yB * yi = 1` using `by rw [← hv, map_mul]; ring`. Establish `hrevB : IsUnit (algebraMap k[X] B P.reverse)` using `isUnit_iff_exists_inv.mpr ⟨yB * v, by rw [← hv, map_mul]; ring⟩`. Establish `hyi : IsUnit yi` using `isUnit_iff_exists_inv'.mpr ⟨yB, hyB⟩`.

Establish `hσ : IsUnit (aeval yi P)`. Establish `key` using `aeval_reverse_mul_pow_of_mul_eq_one (k := k) yi yB (by rw [mul_comm]; exact hyB) P`. Rewrite `key` using `[← algebraMap_eq_aeval_X]`. Rewrite using `[← key]`. Conclude with `hrevB.mul (hyi.pow _)`.

Set `σ` to `awayLiftAlgHom P (aeval yi) hσ`. Establish `hτalg : ∀ q : k[X], τ (algebraMap k[X] B q) = aeval xi q` using `awayLiftAlgHom_algebraMap _ _ _`. Establish `hσalg : ∀ q : k[X], σ (algebraMap k[X] (Localization.Away P) q) = aeval yi q` using `awayLiftAlgHom_algebraMap _ _ _`. Use `⟨σ, τ, ?_, ?_⟩` and prove the remaining obligations. Establish `hτyi : τ yi = xC`.

Establish `h1 : τ yB * τ yi = 1` using `by rw [← map_mul, hyB, map_one]`. Establish `h2 : τ yB = xi` using `by rw [hτalg, aeval_X]`. Rewrite `h1` using `[h2]`. Combine the equalities or inequalities in the displayed calculation. Establish `hext : ((τ.comp σ).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away P))) = IsScalarTower.toAlgHom k k[X] C`.

Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']`. Rewrite using `[hσalg, aeval_X, hτyi]`. Conclude with `RingHom.ext fun p => DFunLike.congr_fun hext p`. Conclude with `RingHom.ext fun p => hτalg p`.
-/
theorem localizationAway_inv_coordinate (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    ∃ Q : Polynomial k, Q ≠ 0 ∧
      ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q)
        (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)),
        (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) =
            algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧
          τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) =
            (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
              IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  classical
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  refine ⟨X * P.reverse, mul_ne_zero X_ne_zero hrev, ?_⟩

  set C := Localization.Away (X * P)
  set u : C := IsLocalization.Away.invSelf (X * P)
  have hu : algebraMap k[X] C (X * P) * u = 1 := IsLocalization.Away.mul_invSelf _
  set xC : C := algebraMap k[X] C X
  set xi : C := algebraMap k[X] C P * u
  have hxC : xC * xi = 1 := by rw [← hu, map_mul]; ring
  have hPC : IsUnit (algebraMap k[X] C P) :=
    isUnit_iff_exists_inv.mpr ⟨xC * u, by rw [← hu, map_mul]; ring⟩
  have hxi : IsUnit xi := isUnit_iff_exists_inv'.mpr ⟨xC, hxC⟩
  have hτ : IsUnit (aeval xi (X * P.reverse)) := by
    rw [map_mul, aeval_X]
    refine hxi.mul ?_
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) xC xi hxC P
    rw [← algebraMap_eq_aeval_X] at key
    exact isUnit_of_mul_isUnit_left (key ▸ hPC)
  let τ := awayLiftAlgHom (X * P.reverse) (aeval xi) hτ

  set B := Localization.Away (X * P.reverse)
  set v : B := IsLocalization.Away.invSelf (X * P.reverse)
  have hv : algebraMap k[X] B (X * P.reverse) * v = 1 := IsLocalization.Away.mul_invSelf _
  set yB : B := algebraMap k[X] B X
  set yi : B := algebraMap k[X] B P.reverse * v
  have hyB : yB * yi = 1 := by rw [← hv, map_mul]; ring
  have hrevB : IsUnit (algebraMap k[X] B P.reverse) :=
    isUnit_iff_exists_inv.mpr ⟨yB * v, by rw [← hv, map_mul]; ring⟩
  have hyi : IsUnit yi := isUnit_iff_exists_inv'.mpr ⟨yB, hyB⟩
  have hσ : IsUnit (aeval yi P) := by
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) yi yB (by rw [mul_comm]; exact hyB) P
    rw [← algebraMap_eq_aeval_X] at key
    rw [← key]
    exact hrevB.mul (hyi.pow _)
  let σ := awayLiftAlgHom P (aeval yi) hσ
  have hτalg : ∀ q : k[X], τ (algebraMap k[X] B q) = aeval xi q :=
    awayLiftAlgHom_algebraMap _ _ _
  have hσalg : ∀ q : k[X], σ (algebraMap k[X] (Localization.Away P) q) = aeval yi q :=
    awayLiftAlgHom_algebraMap _ _ _
  refine ⟨σ, τ, ?_, ?_⟩
  · have hτyi : τ yi = xC := by
      have h1 : τ yB * τ yi = 1 := by rw [← map_mul, hyB, map_one]
      have h2 : τ yB = xi := by rw [hτalg, aeval_X]
      rw [h2] at h1
      calc τ yi = τ yi * (xC * xi) := by rw [hxC, mul_one]
        _ = xC * (xi * τ yi) := by ring
        _ = xC := by rw [h1, mul_one]
    have hext : ((τ.comp σ).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away P))) =
        IsScalarTower.toAlgHom k k[X] C := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [hσalg, aeval_X, hτyi]
    exact RingHom.ext fun p => DFunLike.congr_fun hext p
  · exact RingHom.ext fun p => hτalg p

end GlobalTheory
