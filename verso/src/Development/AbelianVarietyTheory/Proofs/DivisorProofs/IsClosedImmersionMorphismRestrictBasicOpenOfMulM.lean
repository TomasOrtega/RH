import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

/- English proof (translation)
Substitute `hA hB` using the available equality. Use `set s := (φ.app V).hom r with hs`. Introduce `y`. Set `resX : Γ(X, φ ⁻¹ᵁ V) →+* Γ(X, X.basicOpen s)` to `(X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom`. Set `resZ : Γ(Z, V) →+* Γ(Z, Z.basicOpen r)` to `(Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op).hom`.

Set `g` to `(φ.appLE (Z.basicOpen r) (X.basicOpen s) e).hom`. Use `haveI := haff.isLocalization_basicOpen s`. Take `⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩` from `IsLocalization.surj (Submonoid.powers s) y`. Take `⟨b, hb⟩` from `h c`. Establish `hu : IsUnit (resZ r)` using `Z.toRingedSpace.isUnit_res_basicOpen r`.

Establish `hv : IsUnit (resX s)` using `X.toRingedSpace.isUnit_res_basicOpen s`. Establish `hg : ∀ t, g (resZ t) = resX (φ.app V t)`. Introduce `t`. Simplify using `only [g, resZ, resX]`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.

Both sides reduce to the same expression. Establish `hc' : y * resX s ^ n = resX c` using `by rw [← map_pow]; exact hc`. Set `x` to `resZ b * ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) ^ (n + 1)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hx : g x * resX s ^ (n + 1) = y * resX s ^ (n + 1)`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Simplify using `only [x, mul_assoc, ← mul_pow]`. Rewrite using `[show ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) * resZ r = 1 from hu.val_inv_mul, one_pow, mul_one]`. Use `_ = resX (φ.app V b) := hg b`.

Use `_ = resX (s * c) := by rw [hb]`. Use `_ = y * resX s ^ (n + 1) := by rw [map_mul, ← hc']; ring`. Conclude with `(hv.pow (n + 1)).mul_left_inj.1 hx`.
-/
theorem appLE_basicOpen_surjective_of_mul_mem_range {X Z : Scheme.{0}} (φ : X ⟶ Z) {V : Z.Opens}
    (haff : IsAffineOpen (φ ⁻¹ᵁ V)) (r : Γ(Z, V))
    (h : ∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b)
    (A : Z.Opens) (B : X.Opens) (e : B ≤ φ ⁻¹ᵁ A) (hA : A = Z.basicOpen r)
    (hB : B = X.basicOpen ((φ.app V).hom r)) : Function.Surjective (φ.appLE A B e) := by
  subst hA hB
  set s := (φ.app V).hom r with hs
  intro y
  let resX : Γ(X, φ ⁻¹ᵁ V) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  let resZ : Γ(Z, V) →+* Γ(Z, Z.basicOpen r) := (Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op).hom
  let g := (φ.appLE (Z.basicOpen r) (X.basicOpen s) e).hom
  haveI := haff.isLocalization_basicOpen s
  obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers s) y
  obtain ⟨b, hb⟩ := h c
  have hu : IsUnit (resZ r) := Z.toRingedSpace.isUnit_res_basicOpen r
  have hv : IsUnit (resX s) := X.toRingedSpace.isUnit_res_basicOpen s
  have hg : ∀ t, g (resZ t) = resX (φ.app V t) := by
    intro t
    simp only [g, resZ, resX]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hc' : y * resX s ^ n = resX c := by rw [← map_pow]; exact hc
  let x := resZ b * ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) ^ (n + 1)
  refine ⟨x, ?_⟩
  have hx : g x * resX s ^ (n + 1) = y * resX s ^ (n + 1) := by
    calc g x * resX s ^ (n + 1) = g (x * resZ r ^ (n + 1)) := by rw [RingHom.map_mul g x (resZ r ^ (n + 1)), map_pow, hg r]
      _ = g (resZ b) := by
          congr 1
          simp only [x, mul_assoc, ← mul_pow]
          rw [show ((hu.unit⁻¹ : (Γ(Z, Z.basicOpen r))ˣ) : Γ(Z, Z.basicOpen r)) * resZ r = 1 from
            hu.val_inv_mul, one_pow, mul_one]
      _ = resX (φ.app V b) := hg b
      _ = resX (s * c) := by rw [hb]
      _ = y * resX s ^ (n + 1) := by rw [map_mul, ← hc']; ring
  exact (hv.pow (n + 1)).mul_left_inj.1 hx

/- English proof (translation)
Introduce `X Z φ V hV haff r h`. Establish `hpre : φ ⁻¹ᵁ Z.basicOpen r = X.basicOpen ((φ.app V).hom r)` using `Scheme.preimage_basicOpen φ r`. Use `haveI : IsAffine (Z.basicOpen r) := hV.basicOpen r`. Use `haveI : IsAffine (φ ⁻¹ᵁ Z.basicOpen r) := by`. Use `haff.basicOpen ((φ.app V).hom r)` as an intermediate fact.

Rewrite `this` using `[← hpre]`. Conclude with `this`. Apply `IsClosedImmersion.of_surjective_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]`. Conclude with `appLE_basicOpen_surjective_of_mul_mem_range φ haff r h _ _ _ (by simp) (by simp [hpre])`.
-/
theorem isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) →
      ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) →
        IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  intro X Z φ V hV haff r h
  have hpre : φ ⁻¹ᵁ Z.basicOpen r = X.basicOpen ((φ.app V).hom r) := Scheme.preimage_basicOpen φ r
  haveI : IsAffine (Z.basicOpen r) := hV.basicOpen r
  haveI : IsAffine (φ ⁻¹ᵁ Z.basicOpen r) := by
    have := haff.basicOpen ((φ.app V).hom r)
    rw [← hpre] at this
    exact this
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  exact appLE_basicOpen_surjective_of_mul_mem_range φ haff r h _ _ _ (by simp) (by simp [hpre])

end GlobalTheory
