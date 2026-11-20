import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.IwasawaLast

/- English proof (translation)
Use `set x : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star ℓ) with hx`. Establish `hx0 : x ≠ 0`. Introduce `h`. Apply `hℓ` to reduce the goal to its premises. Establish `: star ℓ = 0`.

Use `congrArg WithLp.ofLp h` as an intermediate fact. Simplify `this` using `[hx]`. Simplify using `using congrArg star this`. Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.mpr hx0`. Use `set w : EuclideanSpace ℂ (Fin (n + 1)) := ((‖x‖ : ℂ)⁻¹) • x with hw`.

Establish `hw1 : ‖w‖ = 1`. Rewrite using `[hw, norm_smul]`. Simplify using `[hn]`. Establish `hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict (fun _ => w))`. Rewrite using `[orthonormal_iff_ite]`.

Introduce and unpack `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [Set.mem_singleton_iff] at hi hj`. Substitute `hi` using the available equality. Substitute `hj` using the available equality. Simplify using `[Set.domRestrict, inner_self_eq_norm_sq_to_K, hw1]`.

Take `⟨b, hb⟩` from `hon.exists_orthonormalBasis_extension_of_card_eq (by simp)`. Establish `hbl : b (Fin.last n) = w` using `hb _ (Set.mem_singleton _)`. Use `set M := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b with hM`. Establish `hMu : M ∈ unitaryGroup (Fin (n + 1)) ℂ` using `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _`. Use `⟨(‖x‖ : ℂ), by exact_mod_cast hn, star M, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Unitary.star_mem hMu`. Introduce `l`. Simplify using `[hM, Matrix.star_apply, Module.Basis.toMatrix_apply, hbl, hw, hx]`. Establish `hn' : ((‖WithLp.toLp 2 (star ℓ)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hn`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hn', one_mul]`.
-/
theorem exists_unitary_lastRow {n : ℕ} (ℓ : Fin (n + 1) → ℂ) (hℓ : ℓ ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ∃ k ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ l, ℓ l = r * k (Fin.last n) l := by
  set x : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star ℓ) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hℓ
    have : star ℓ = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [hx] using this
    simpa using congrArg star this
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set w : EuclideanSpace ℂ (Fin (n + 1)) := ((‖x‖ : ℂ)⁻¹) • x with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul]
    simp [hn]
  have hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, inner_self_eq_norm_sq_to_K, hw1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbl : b (Fin.last n) = w := hb _ (Set.mem_singleton _)
  set M := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b with hM
  have hMu : M ∈ unitaryGroup (Fin (n + 1)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  refine ⟨(‖x‖ : ℂ), by exact_mod_cast hn, star M, ?_, ?_⟩
  · exact Unitary.star_mem hMu
  · intro l
    simp [hM, Matrix.star_apply, Module.Basis.toMatrix_apply, hbl, hw, hx]
    have hn' : ((‖WithLp.toLp 2 (star ℓ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]

end GlobalTheory.IwasawaLast

namespace GlobalTheory.IwasawaLast

/- English proof (translation)
Introduce `E _ _ _ m y`. Use `set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) with hY`. Use `set ℓ : InfinitePlace E → Fin (m + 1) → ℂ := fun v j => Y (Fin.last m) j v with hℓdef`. Establish `hne : ∀ v, ℓ v ≠ 0`. Introduce `v h`.

Establish `hdet : IsUnit Y.det` using `(Matrix.isUnit_iff_isUnit_det Y).mp (Units.isUnit y)`. Establish `hv : IsUnit (Y.det v)` using `(Pi.isUnit_iff.mp hdet) v`. Establish `hmap : Y.det v = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det` using `RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) Y`. Establish `h0 : ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det = 0` using `Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) (fun j => by`. Simplify `congrFun h j)` using `[hℓdef]`.

Rewrite `hv` using `[hmap, h0]`. Conclude with `not_isUnit_zero hv`. Use `choose r hr kv hkv hℓ using fun v => exists_unitary_lastRow (ℓ v) (hne v)`. Use `set K : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := Matrix.of fun i j v => kv v i j with hKdef`. Establish `hK : K ∈ unitaryGroup (Fin (m + 1)) (Cinf E)`.

Rewrite using `[mem_unitaryGroup_iff]`. Use extensionality with `i j v`. Use `congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) i) j` as an intermediate fact. Apply the tactic sequence `by_cases hij : i = j <;> simp [hKdef, Matrix.mul_apply, Finset.sum_apply, Matrix.star_apply, Matrix.one_apply, hij] at this ⊢ <;> exact this`. Establish `hρ : IsUnit (fun v => r v : Cinf E)` using `Pi.isUnit_iff.mpr fun v => (hr v).isUnit`.

Use `⟨y * (Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ * (Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom hρ.unit)⁻¹, hρ.unit, ⟨K, hK⟩, ?_, by group⟩` and prove the remaining obligations. Introduce `j`. Use extensionality with `v`. Establish `hinv : (((Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) = star K` using `rfl`. Establish `hρv : ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E) v = (r v)⁻¹`.

Establish `h1` using `congrFun hρ.unit.inv_mul v`. Simplify using `only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec, Units.val_one, Pi.one_apply] at h1`. Conclude with `eq_inv_of_mul_eq_one_left h1`. Establish `hrow : ∀ l, Y (Fin.last m) l v = r v * kv v (Fin.last m) l` using `fun l => hℓ v l`. Establish `hu` using `congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) (Fin.last m)) j`.

Simplify using `only [Units.val_mul, Units.coe_map_inv, MonoidHom.coe_coe, hinv]`. Rewrite using `[← hY]`. Use `show (Y * star K * Matrix.scalar (Fin (m + 1)) ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E)) (Fin.last m) j v = _`. Rewrite using `[Matrix.scalar_apply, Matrix.mul_diagonal]`. Simplify using `only [Matrix.scalar_apply, Matrix.mul_diagonal, Pi.mul_apply, hρv, Matrix.mul_apply, Finset.sum_apply, hrow, Matrix.star_apply, Pi.star_apply, hKdef, Matrix.of_apply] at hu ⊢`.

Establish `hs : ∑ x, r v * kv v (Fin.last m) x * star (kv v j x) = r v * ∑ x, kv v (Fin.last m) x * star (kv v j x)`. Rewrite using `[Finset.mul_sum]`. Simplify using `[mul_assoc]`. Rewrite using `[hs, hu, Matrix.one_apply]`. Distinguish the cases in `hj : j = Fin.last m`.

Substitute `hj` using the available equality. Simplify using `[hr v]`. Simplify using `[hj, Ne.symm hj]`.
-/
theorem iwasawa_lastRow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  intro E _ _ _ m y
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) with hY
  set ℓ : InfinitePlace E → Fin (m + 1) → ℂ := fun v j => Y (Fin.last m) j v with hℓdef
  have hne : ∀ v, ℓ v ≠ 0 := by
    intro v h
    have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (Units.isUnit y)
    have hv : IsUnit (Y.det v) := (Pi.isUnit_iff.mp hdet) v
    have hmap : Y.det v = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det :=
      RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) Y
    have h0 : ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) (fun j => by
        simpa [hℓdef] using congrFun h j)
    rw [hmap, h0] at hv
    exact not_isUnit_zero hv
  choose r hr kv hkv hℓ using fun v => exists_unitary_lastRow (ℓ v) (hne v)
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := Matrix.of fun i j v => kv v i j with hKdef
  have hK : K ∈ unitaryGroup (Fin (m + 1)) (Cinf E) := by
    rw [mem_unitaryGroup_iff]
    ext i j v
    have := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) i) j
    by_cases hij : i = j <;> simp [hKdef, Matrix.mul_apply, Finset.sum_apply, Matrix.star_apply, Matrix.one_apply, hij] at this ⊢ <;> exact this
  have hρ : IsUnit (fun v => r v : Cinf E) := Pi.isUnit_iff.mpr fun v => (hr v).isUnit
  refine ⟨y * (Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ *
      (Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom hρ.unit)⁻¹,
    hρ.unit, ⟨K, hK⟩, ?_, by group⟩
  intro j
  ext v
  have hinv : (((Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) = star K := rfl
  have hρv : ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E) v = (r v)⁻¹ := by
    have h1 := congrFun hρ.unit.inv_mul v
    simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec, Units.val_one, Pi.one_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hrow : ∀ l, Y (Fin.last m) l v = r v * kv v (Fin.last m) l := fun l => hℓ v l
  have hu := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) (Fin.last m)) j
  simp only [Units.val_mul, Units.coe_map_inv, MonoidHom.coe_coe, hinv]
  rw [← hY]
  show (Y * star K * Matrix.scalar (Fin (m + 1)) ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E)) (Fin.last m) j v = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Pi.mul_apply, hρv, Matrix.mul_apply, Finset.sum_apply, hrow, Matrix.star_apply, Pi.star_apply, hKdef, Matrix.of_apply] at hu ⊢
  have hs : ∑ x, r v * kv v (Fin.last m) x * star (kv v j x) = r v * ∑ x, kv v (Fin.last m) x * star (kv v j x) := by
    rw [Finset.mul_sum]; simp [mul_assoc]
  rw [hs, hu, Matrix.one_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp [hr v]
  · simp [hj, Ne.symm hj]

end GlobalTheory.IwasawaLast
