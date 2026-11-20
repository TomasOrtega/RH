import Mathlib
open NumberField

namespace GlobalTheory
namespace RepTrace

/- English proof (translation)
Establish `hI : Ideal.span {b} ≠ ⊥` using `by simpa using hb`. Establish `hn : Ideal.absNorm (Ideal.span {b}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]` and apply the resulting hypothesis. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {b}))`. Use `set n := Ideal.absNorm (Ideal.span {b})`.

Establish `hu : IsUnit (g b * g c)`. Rewrite using `[← map_mul, ← hc, map_natCast]`. Establish `h1 : (n : P) = algebraMap ℚ P (n : ℚ)` using `by simp`. Rewrite using `[h1]`. Conclude with `(isUnit_iff_ne_zero.2 (by exact_mod_cast hn : (n : ℚ) ≠ 0)).map _`.

Conclude with `isUnit_of_mul_isUnit_left hu`.
-/
theorem isUnit_of_ne_zero {E : Type} [Field E] [NumberField E] {P : Type} [CommRing P] [Algebra ℚ P]
    (g : 𝓞 E →+* P) (b : 𝓞 E) (hb : b ≠ 0) : IsUnit (g b) := by
  have hI : Ideal.span {b} ≠ ⊥ := by simpa using hb
  have hn : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {b}))
  set n := Ideal.absNorm (Ideal.span {b})
  have hu : IsUnit (g b * g c) := by
    rw [← map_mul, ← hc, map_natCast]
    have h1 : (n : P) = algebraMap ℚ P (n : ℚ) := by simp
    rw [h1]
    exact (isUnit_iff_ne_zero.2 (by exact_mod_cast hn : (n : ℚ) ≠ 0)).map _
  exact isUnit_of_mul_isUnit_left hu

/- English proof (translation)
Set `b` to `Module.finBasis L V`. Set `c` to `Module.finBasis K L`. Rewrite using `[LinearMap.trace_eq_matrix_trace K (c.smulTower b), Algebra.trace_eq_matrix_trace c]`. Simplify using `[Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.smulTower_repr_mk, smul_smul, Finsupp.single_apply, Finset.mul_sum, mul_comm]`.
-/
theorem trace_lsmul_restrictScalars {K L V : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V] [FiniteDimensional L V] (a : L) :
    LinearMap.trace K V ((LinearMap.lsmul L V a).restrictScalars K) =
      (Module.finrank L V : K) * Algebra.trace K L a := by
  classical
  let b := Module.finBasis L V
  let c := Module.finBasis K L
  rw [LinearMap.trace_eq_matrix_trace K (c.smulTower b), Algebra.trace_eq_matrix_trace c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.smulTower_repr_mk, smul_smul, Finsupp.single_apply, Finset.mul_sum, mul_comm]

end RepTrace

/- English proof (translation)
Set `g : 𝓞 E →+* Module.End ℚ (Fin r → ℚ)` to `(Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ((Int.castRingHom ℚ).mapMatrix.comp ρ)`. Set `A` to `Algebra.adjoin ℚ (Set.range g)`. Use `letI : CommRing A := Algebra.adjoinCommRingOfComm ℚ (by`. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[← map_mul, ← map_mul, mul_comm])`.

Set `g' : 𝓞 E →+* A` to `g.codRestrict A (fun x => Algebra.subset_adjoin ⟨x, rfl⟩)`. Set `φ : E →+* Module.End ℚ (Fin r → ℚ)` to `(A.val : A →ₐ[ℚ] Module.End ℚ (Fin r → ℚ)).toRingHom.comp (IsLocalization.lift (M := nonZeroDivisors (𝓞 E)) (S := E) (g := g') (fun y => RepTrace.isUnit_of_ne_zero g' y (nonZeroDivisors.ne_zero y.2)))`. Use `letI : Module E (Fin r → ℚ) := Module.compHom (Fin r → ℚ) φ`. Establish `hφq : φ.comp (algebraMap ℚ E) = algebraMap ℚ (Module.End ℚ (Fin r → ℚ))` using `Subsingleton.elim _ _`. Use `haveI : IsScalarTower ℚ E (Fin r → ℚ) := ⟨fun q x v => by`.

Express the relevant statement in the definitionally equal form `φ (q • x) v = q • φ x v`. Rewrite using `[Algebra.smul_def, map_mul, Module.End.mul_apply]`. Use `RingHom.congr_fun hφq q` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this, Module.algebraMap_end_apply]⟩`.

Use `haveI : FiniteDimensional E (Fin r → ℚ) := Module.Finite.of_restrictScalars_finite ℚ E _`. Establish `hfin : Module.finrank E (Fin r → ℚ) = s`. Establish `h` using `Module.finrank_mul_finrank ℚ E (Fin r → ℚ)`. Rewrite `h` using `[Module.finrank_fin_fun]`. Establish `hd : 0 < Module.finrank ℚ E` using `Module.finrank_pos`.

Establish `h2 : Module.finrank ℚ E * Module.finrank E (Fin r → ℚ) = Module.finrank ℚ E * s`. Rewrite using `[h, hr, mul_comm]`. Conclude with `Nat.eq_of_mul_eq_mul_left hd h2`. Establish `key : LinearMap.trace ℚ (Fin r → ℚ) (g a) = ((ρ a).trace : ℚ)`. Express the relevant statement in the definitionally equal form `LinearMap.trace ℚ _ (Matrix.toLin' ((ρ a).map (Int.castRingHom ℚ))) = _`.

Rewrite using `[LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin r)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Simplify using `[Matrix.trace]`. Establish `hga : g a = (LinearMap.lsmul E (Fin r → ℚ) (a : E)).restrictScalars ℚ`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g a v = φ (algebraMap (𝓞 E) E a) v`.

Simplify using `only [φ, RingHom.comp_apply, IsLocalization.lift_eq]`. Both sides reduce to the same expression. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[← key, hga, RepTrace.trace_lsmul_restrictScalars, hfin]`. Use `push_cast`.

Rewrite using `[Algebra.coe_trace_int]`.
-/
theorem repTrace_eq_mul_trace {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ)
    (hr : r = s * Module.finrank ℚ E) (a : 𝓞 E) : (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  classical
  let g : 𝓞 E →+* Module.End ℚ (Fin r → ℚ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp
      ((Int.castRingHom ℚ).mapMatrix.comp ρ)
  let A := Algebra.adjoin ℚ (Set.range g)
  letI : CommRing A := Algebra.adjoinCommRingOfComm ℚ (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])
  let g' : 𝓞 E →+* A := g.codRestrict A (fun x => Algebra.subset_adjoin ⟨x, rfl⟩)
  let φ : E →+* Module.End ℚ (Fin r → ℚ) :=
    (A.val : A →ₐ[ℚ] Module.End ℚ (Fin r → ℚ)).toRingHom.comp
      (IsLocalization.lift (M := nonZeroDivisors (𝓞 E)) (S := E) (g := g')
        (fun y => RepTrace.isUnit_of_ne_zero g' y (nonZeroDivisors.ne_zero y.2)))
  letI : Module E (Fin r → ℚ) := Module.compHom (Fin r → ℚ) φ
  have hφq : φ.comp (algebraMap ℚ E) = algebraMap ℚ (Module.End ℚ (Fin r → ℚ)) := Subsingleton.elim _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := ⟨fun q x v => by
    change φ (q • x) v = q • φ x v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
    have := RingHom.congr_fun hφq q
    simp only [RingHom.comp_apply] at this
    rw [this, Module.algebraMap_end_apply]⟩
  haveI : FiniteDimensional E (Fin r → ℚ) := Module.Finite.of_restrictScalars_finite ℚ E _
  have hfin : Module.finrank E (Fin r → ℚ) = s := by
    have h := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
    rw [Module.finrank_fin_fun] at h
    have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h2 : Module.finrank ℚ E * Module.finrank E (Fin r → ℚ) = Module.finrank ℚ E * s := by
      rw [h, hr, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hd h2
  have key : LinearMap.trace ℚ (Fin r → ℚ) (g a) = ((ρ a).trace : ℚ) := by
    change LinearMap.trace ℚ _ (Matrix.toLin' ((ρ a).map (Int.castRingHom ℚ))) = _
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    simp [Matrix.trace]
  have hga : g a = (LinearMap.lsmul E (Fin r → ℚ) (a : E)).restrictScalars ℚ := by
    refine LinearMap.ext fun v => ?_
    change g a v = φ (algebraMap (𝓞 E) E a) v
    simp only [φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  apply Int.cast_injective (α := ℚ)
  rw [← key, hga, RepTrace.trace_lsmul_restrictScalars, hfin]
  push_cast
  rw [Algebra.coe_trace_int]

end GlobalTheory
