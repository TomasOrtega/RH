import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Establish `hn : n ≠ 0` using `left_ne_zero_of_mul hN`. Establish `hc : c ≠ 0` using `right_ne_zero_of_mul hN`. Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Establish `hc' : (c : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hc`.

Rewrite using `[Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), zeta, zeta, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem zeta_pow_div_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : zeta N ^ (N / n) = zeta n := by
  obtain ⟨c, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hN
  have hc : c ≠ 0 := right_ne_zero_of_mul hN
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Rewrite using `[← zeta_pow_div_of_dvd hN h]`. Conclude with `pow_mem (zetaAway N).2 _`. Take `⟨c, rfl⟩` from `h`.

Establish `hc' : (c : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (right_ne_zero_of_mul hN)`. Establish `e : (n : ℂ)⁻¹ = (c : ℂ) * ((n * c : ℕ) : ℂ)⁻¹`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `mul_mem (natCast_mem _ _) (Subring.subset_closure (Or.inr rfl))`.
-/
theorem cycAway_le_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : cycAway n ≤ cycAway N := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow_div_of_dvd hN h]
    exact pow_mem (zetaAway N).2 _
  · obtain ⟨c, rfl⟩ := h
    have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hN)
    have e : (n : ℂ)⁻¹ = (c : ℂ) * ((n * c : ℕ) : ℂ)⁻¹ := by
      push_cast
      field_simp
    rw [e]
    exact mul_mem (natCast_mem _ _) (Subring.subset_closure (Or.inr rfl))

/- English proof (translation)
The claim follows from `Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one`.
-/
theorem zetaAway_pow_self {N : ℕ} (hN : N ≠ 0) : zetaAway N ^ N = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

/- English proof (translation)
Establish `hD : ∀ x : cycAway N, KaehlerDifferential.D R (cycAway N) x = 0`. Introduce and unpack `⟨x, hx⟩`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases.

Establish `h` using `congrArg (KaehlerDifferential.D R (cycAway N)) (zetaAway_pow_self hN)`. Rewrite `h` using `[Derivation.leibniz_pow, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul (cycAway N), smul_smul]`. Establish `hu : IsUnit ((N : cycAway N) * zetaAway N ^ (N - 1))` using `(isUnit_natCast hN).mul ((IsUnit.of_pow_eq_one (zetaAway_pow_self hN) hN).pow _)`. Conclude with `hu.smul_eq_zero.1 h`. Set `v : cycAway N` to `⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩`.

Establish `hv : (N : cycAway N) * v = 1` using `Subtype.ext (by simpa [v] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0))`. Establish `h` using `congrArg (KaehlerDifferential.D R (cycAway N)) hv`. Rewrite `h` using `[Derivation.leibniz, Derivation.map_one_eq_zero, Derivation.map_natCast, smul_zero, add_zero]`. Conclude with `(isUnit_natCast hN).smul_eq_zero.1 h`. Consider the case `zero => exact map_zero _`.

Consider the case `one => exact Derivation.map_one_eq_zero _`. Consider the case `add x y hx' hy' hx hy`. Use `map_add (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩ ⟨y, hy'⟩` as an intermediate fact. Rewrite `this` using `[hx, hy, add_zero]`. Conclude with `this`.

Consider the case `neg x hx' hx`. Use `map_neg (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩` as an intermediate fact. Rewrite `this` using `[hx, neg_zero]`. Conclude with `this`. Consider the case `mul x y hx' hy' hx hy`.

Use `(KaehlerDifferential.D R (cycAway N)).leibniz ⟨x, hx'⟩ ⟨y, hy'⟩` as an intermediate fact. Rewrite `this` using `[hx, hy, smul_zero, smul_zero, add_zero]`. Conclude with `this`. Use `⟨subsingleton_of_forall_eq 0 fun ω => ?_⟩` and prove the remaining obligations. Establish `hω : ω ∈ Submodule.span (cycAway N) (Set.range (KaehlerDifferential.D R (cycAway N)))`.

Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Use `(Submodule.mem_bot (cycAway N)).1 (Submodule.span_le.2 ?_ hω)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `(Submodule.mem_bot (cycAway N)).2 (hD x)`.
-/
theorem formallyUnramified_cycAway {N : ℕ} (hN : N ≠ 0) (R : Type) [CommRing R] [Algebra R (cycAway N)] :
    Algebra.FormallyUnramified R (cycAway N) := by
  have hD : ∀ x : cycAway N, KaehlerDifferential.D R (cycAway N) x = 0 := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have h := congrArg (KaehlerDifferential.D R (cycAway N)) (zetaAway_pow_self hN)
        rw [Derivation.leibniz_pow, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul (cycAway N), smul_smul] at h
        have hu : IsUnit ((N : cycAway N) * zetaAway N ^ (N - 1)) :=
          (isUnit_natCast hN).mul ((IsUnit.of_pow_eq_one (zetaAway_pow_self hN) hN).pow _)
        exact hu.smul_eq_zero.1 h
      · let v : cycAway N := ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
        have hv : (N : cycAway N) * v = 1 :=
          Subtype.ext (by simpa [v] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0))
        have h := congrArg (KaehlerDifferential.D R (cycAway N)) hv
        rw [Derivation.leibniz, Derivation.map_one_eq_zero, Derivation.map_natCast, smul_zero, add_zero] at h
        exact (isUnit_natCast hN).smul_eq_zero.1 h
    | zero => exact map_zero _
    | one => exact Derivation.map_one_eq_zero _
    | add x y hx' hy' hx hy =>
      have := map_add (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, add_zero] at this
      exact this
    | neg x hx' hx =>
      have := map_neg (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩
      rw [hx, neg_zero] at this
      exact this
    | mul x y hx' hy' hx hy =>
      have := (KaehlerDifferential.D R (cycAway N)).leibniz ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨subsingleton_of_forall_eq 0 fun ω => ?_⟩
  have hω : ω ∈ Submodule.span (cycAway N) (Set.range (KaehlerDifferential.D R (cycAway N))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine (Submodule.mem_bot (cycAway N)).1 (Submodule.span_le.2 ?_ hω)
  rintro _ ⟨x, rfl⟩
  exact (Submodule.mem_bot (cycAway N)).2 (hD x)

/- English proof (translation)
Establish `hn : n ≠ 0` using `fun h0 => hN (by simpa [h0] using h)`. Introduce and unpack `⟨x, hx⟩`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases.

Conclude with `⟨Polynomial.X ^ N - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hN, by`. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]`. Conclude with `sub_eq_zero.2 (zetaAway_pow_self hN)⟩`. Take `⟨c, hc⟩` from `ha`. Set `v : cycAway n` to `⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩`.

Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Establish `hc' : (n : ℂ) ^ a = N * c` using `by exact_mod_cast hc`. Use `RingHom.isIntegralElem_map (Subring.inclusion (cycAway_le_of_dvd hN h)) (x := (c : cycAway n) * v ^ a)` and compare the differences between its conclusion and the goal. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(N : ℂ)⁻¹ = (c : ℂ) * ((n : ℂ)⁻¹) ^ a`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← _root_.mul_assoc, ← hc', ← mul_pow, mul_inv_cancel₀ hn', one_pow]`. Consider the case `zero => exact RingHom.isIntegralElem_zero _`. Consider the case `one => exact RingHom.isIntegralElem_one _`.

Consider the case `add x y _ _ hx hy => exact hx.add _ hy`. Consider the case `neg x _ hx => exact hx.neg _`. Consider the case `mul x y _ _ hx hy => exact hx.mul _ hy`.
-/
theorem isIntegral_inclusion_cycAway {n N a : ℕ} (hN : N ≠ 0) (h : n ∣ N) (ha : N ∣ n ^ a) :
    (Subring.inclusion (cycAway_le_of_dvd hN h)).IsIntegral := by
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  rintro ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Polynomial.X ^ N - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hN, by
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
        exact sub_eq_zero.2 (zetaAway_pow_self hN)⟩
    · obtain ⟨c, hc⟩ := ha
      let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
      have hc' : (n : ℂ) ^ a = N * c := by exact_mod_cast hc
      convert RingHom.isIntegralElem_map (Subring.inclusion (cycAway_le_of_dvd hN h)) (x := (c : cycAway n) * v ^ a)
      refine Subtype.ext ?_
      change (N : ℂ)⁻¹ = (c : ℂ) * ((n : ℂ)⁻¹) ^ a
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← _root_.mul_assoc, ← hc', ← mul_pow, mul_inv_cancel₀ hn', one_pow]
  | zero => exact RingHom.isIntegralElem_zero _
  | one => exact RingHom.isIntegralElem_one _
  | add x y _ _ hx hy => exact hx.add _ hy
  | neg x _ hx => exact hx.neg _
  | mul x y _ _ hx hy => exact hx.mul _ hy

/- English proof (translation)
Introduce `n N hN h`. Establish `hn : n ≠ 0` using `fun h0 => hN (by simpa [h0] using h)`. Set `j` to `Subring.inclusion (cycAway_le_of_dvd hN h)`. Establish `hj : Function.Injective j` using `Subring.inclusion_injective _`. Use `⟨j, hj, Subtype.ext (zeta_pow_div_of_dvd hN h).symm, fun ⟨a, ha⟩ => ?_⟩` and prove the remaining obligations.

Establish `hint : j.IsIntegral` using `isIntegral_inclusion_cycAway hN h ha`. Use `letI := j.toAlgebra`. Establish `: IsDedekindDomain (cycAway n)` using `(arBase_cycAway n hn).1`. Establish `: Algebra.IsIntegral (cycAway n) (cycAway N)` using `⟨hint⟩`. Use `finiteType_cycAway N` as an intermediate fact.

Establish `: Algebra.FiniteType (cycAway n) (cycAway N)` using `.of_restrictScalars_finiteType ℤ _ _`. Establish `hfin : Module.Finite (cycAway n) (cycAway N)` using `Algebra.IsIntegral.finite`. Establish `: FaithfulSMul (cycAway n) (cycAway N)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hj`. Establish `: Module.Flat (cycAway n) (cycAway N)` using `inferInstance`. Establish `: Algebra.FinitePresentation (cycAway n) (cycAway N)` using `Algebra.FinitePresentation.of_finiteType.1 inferInstance`.

Use `formallyUnramified_cycAway hN (cycAway n)` as an intermediate fact. Establish `het : Algebra.Etale (cycAway n) (cycAway N)` using `Algebra.Etale.of_formallyUnramified_of_flat`. Use `⟨(IsFinite.SpecMap_iff _).2 hfin, HasRingHomProperty.Spec_iff.2 het, ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `hint.comap_surjective hj`.
-/
theorem exists_inclusion_cycAway : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧
    j (zetaAway n) = zetaAway N ^ (N / n) ∧
    ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  intro n N hN h
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  let j := Subring.inclusion (cycAway_le_of_dvd hN h)
  have hj : Function.Injective j := Subring.inclusion_injective _
  refine ⟨j, hj, Subtype.ext (zeta_pow_div_of_dvd hN h).symm, fun ⟨a, ha⟩ => ?_⟩
  have hint : j.IsIntegral := isIntegral_inclusion_cycAway hN h ha
  letI := j.toAlgebra
  have : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn).1
  have : Algebra.IsIntegral (cycAway n) (cycAway N) := ⟨hint⟩
  have := finiteType_cycAway N
  have : Algebra.FiniteType (cycAway n) (cycAway N) := .of_restrictScalars_finiteType ℤ _ _
  have hfin : Module.Finite (cycAway n) (cycAway N) := Algebra.IsIntegral.finite
  have : FaithfulSMul (cycAway n) (cycAway N) := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  have : Module.Flat (cycAway n) (cycAway N) := inferInstance
  have : Algebra.FinitePresentation (cycAway n) (cycAway N) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have := formallyUnramified_cycAway hN (cycAway n)
  have het : Algebra.Etale (cycAway n) (cycAway N) := Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨(IsFinite.SpecMap_iff _).2 hfin, HasRingHomProperty.Spec_iff.2 het, ⟨?_⟩⟩
  exact hint.comap_surjective hj

end GlobalTheory.SiegelTor
