import Mathlib

namespace GlobalTheory

open MonoidAlgebra

/- English proof (translation)
Establish `hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i)` using `fun f g h => Finsupp.sum_fintype f g h`. Rewrite using `[MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]`. Rewrite using `[Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Establish `: ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹)` using `fun m => eq_mul_inv_iff_mul_eq.symm`. Repeatedly rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem groupAlgebra_coeff_mul_fintype {R G : Type} [CommRing R] [Group G] [Fintype G]
    (x y : MonoidAlgebra R G) (a : G) :
    (x * y).coeff a = ∑ c : G, x.coeff (a * c⁻¹) * y.coeff c := by
  classical
  have hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i) :=
    fun f g h => Finsupp.sum_fintype f g h
  rw [MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]
  rw [Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹) := fun m => eq_mul_inv_iff_mul_eq.symm
  simp_rw [this]
  simp

/- English proof (translation)
Introduce and unpack `⟨vL, hvL⟩`. Set `M : Matrix G G E` to `fun a c => x.coeff (a * c⁻¹)`. Establish `hsurj : Function.Surjective (M.map j).mulVec`. Introduce `w`. Set `y : MonoidAlgebra L G` to `ofCoeff (Finsupp.equivFunOnFinite.symm w)`.

Use `⟨fun c => (vL * y).coeff c, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Establish `h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a`. Rewrite using `[← mul_assoc, hvL, one_mul]`. Both sides reduce to the same expression.

Rewrite `h1` using `[groupAlgebra_coeff_mul_fintype]`. Simplify using `only [MonoidAlgebra.coeff_mapRingHom] at h1`. Conclude with `h1`. Establish `hU : IsUnit (M.map j)` using `Matrix.mulVec_surjective_iff_isUnit.1 hsurj`. Establish `hdetL : IsUnit (j M.det)`.

Rewrite using `[RingHom.map_det]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 hU`. Establish `hdet : M.det ≠ 0`. Introduce `h`. Rewrite `hdetL` using `[h, map_zero]`.

Conclude with `not_isUnit_zero hdetL`. Establish `hM : IsUnit M` using `(Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)`. Take `⟨u, hu⟩` from `Matrix.mulVec_surjective_iff_isUnit.2 hM (fun a => (1 : MonoidAlgebra E G).coeff a)`. Use `⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩` and prove the remaining obligations. Apply `MonoidAlgebra.ext` to reduce the goal to its premises.

Use extensionality with `a`. Rewrite using `[groupAlgebra_coeff_mul_fintype]`. Use `congrFun hu a` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, M]`.
-/
theorem groupAlgebra_exists_right_inv_of_map {E L G : Type} [Field E] [Field L] [Group G]
    [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G) :
    (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) →
      ∃ v : MonoidAlgebra E G, x * v = 1 := by
  classical
  rintro ⟨vL, hvL⟩
  let M : Matrix G G E := fun a c => x.coeff (a * c⁻¹)

  have hsurj : Function.Surjective (M.map j).mulVec := by
    intro w
    let y : MonoidAlgebra L G := ofCoeff (Finsupp.equivFunOnFinite.symm w)
    refine ⟨fun c => (vL * y).coeff c, ?_⟩
    funext a
    have h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a := by
      rw [← mul_assoc, hvL, one_mul]
      rfl
    rw [groupAlgebra_coeff_mul_fintype] at h1
    simp only [MonoidAlgebra.coeff_mapRingHom] at h1
    exact h1
  have hU : IsUnit (M.map j) := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdetL : IsUnit (j M.det) := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdetL
    exact not_isUnit_zero hdetL
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM
    (fun a => (1 : MonoidAlgebra E G).coeff a)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩
  apply MonoidAlgebra.ext
  ext a
  rw [groupAlgebra_coeff_mul_fintype]
  have := congrFun hu a
  simpa [Matrix.mulVec, dotProduct, M] using this

end GlobalTheory
