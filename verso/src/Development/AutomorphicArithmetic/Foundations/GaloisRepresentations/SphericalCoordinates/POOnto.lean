import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

/- English proof (translation)
Establish `hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p])`. Introduce `a b h`. Conclude with `RingHom.injective_int (algebraMap ℤ ℤ_[p]) h`. Establish `h1` using `Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj`. Introduce `x y hxy`.

Establish `h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ)` using `h1 (by simpa using hxy)`. Establish `h3` using `congrArg (TensorProduct.rid ℤ O) h2`. Simplify using `using h3`.
-/
private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

/- English proof (translation)
Substitute `hm` using the available equality. Apply `tens_inj p` to reduce the goal to its premises. Establish `hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A`. Introduce `A B`. Use extensionality with `i j`.

Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Simplify using `[Matrix.mul_apply, mul_comm]`. Use `hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))` as an intermediate fact. Rewrite `this` using `[← map_mul, ← map_mul]`.

Establish `h2` using `f.injective this`. Simplify using `using h2`.
-/
private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Assume the negation of the conclusion as `h0`. Establish `hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥` using `fun h => h0 (by`. Establish `h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O)` using `hc`.

Rewrite `h1` using `[h]`. Simplify using `using h1)`. Establish `hN` using `Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))`. Establish `hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `hI`. Rewrite `hN` using `[RingHom.mem_ker, map_natCast]`. Establish `h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0`. Rewrite using `[zsmul_one]`. Conclude with `hN` after adjusting the coercions.

Break down `smul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `hN0 (by exact_mod_cast h)`. Conclude with `one_ne_zero h`.
-/
private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

/- English proof (translation)
Introduce `x`. Take `⟨c, e, he, hx⟩` from `hc x`. Use `letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }`. Take `⟨P, hP, hPx⟩ : IsIntegral ℤ x` from `IsIntegral.of_finite ℤ x`. Establish `hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0`.

Rewrite using `[Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]`. Establish `hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c`. Rewrite using `[← hx]`. Simplify using `[zsmul_eq_mul]`. Establish `hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0`.

Apply `a_inj (O := O)` to reduce the goal to its premises. Rewrite using `[map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Establish `hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0`.

Use `congrArg (algebraMap (𝓞 F) F) hQ2` as an intermediate fact. Rewrite `this` using `[map_zero, Polynomial.hom_eval₂]`. Rewrite using `[← this]`. Use `congr 1`. Establish `heF : (algebraMap ℤ F e) ≠ 0` using `by simpa using he`.

Establish `hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e)` using `by field_simp`. Rewrite `hQ3` using `[hcF, Polynomial.scaleRoots_eval₂_mul]`. Establish `hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e)` using `⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩`. Take `⟨c', hc'⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint`. Use `⟨c', ?_⟩` and prove the remaining obligations.

Establish `hcc : c = e • c'`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hcF, ← hc']`. Simplify using `[zsmul_eq_mul]`. Establish `h3 : e • (algebraMap (𝓞 F) O c' - x) = 0`.

Rewrite using `[smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]`. Simplify using the standard rewrite rules. Break down `smul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `absurd h he`. Conclude with `sub_eq_zero.mp h`.
-/
private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

/- English proof (translation)
Introduce `p _ D hm`. Use `haveI := D.freeO`. Use `haveI := D.finO`. Establish `hd : 0 < Module.finrank ℚ D.F` using `Module.finrank_pos`. Use `haveI : Nontrivial D.O := by`.

Apply `Module.nontrivial_of_finrank_pos (R := ℤ)` to reduce the goal to its premises. Rewrite using `[D.rankO, hm]`. Simplify using `using hd`. Take `⟨f⟩` from `D.splitP`. Establish `hcomm : ∀ x y : D.O, x * y = y * x` using `comm_of_split p hm f.toRingEquiv`.

Conclude with `a_onto hcomm fun x => D.central x (hcomm x)`.
-/
theorem oOnto_of : OOnto := by
  intro p _ D hm
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  exact a_onto hcomm fun x => D.central x (hcomm x)

end UpperTheory.Gal.W2
