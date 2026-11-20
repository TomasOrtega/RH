import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGFree
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DvdOfAeval
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfAevalEqZero

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section
variable {R : Type} [CommRing R] {n : ℕ}

private def kry (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (g ^ (j : ℕ) *ᵥ v) i

private noncomputable def pol (c : Fin n → R) : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)

/- English proof (translation)
Rewrite using `[pol, map_sum, Matrix.sum_mulVec]`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [aeval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [Matrix.mulVec, dotProduct, kry, Matrix.of_apply]`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
private theorem kry_mulVec (g : Matrix (Fin n) (Fin n) R) (v c : Fin n → R) :
    kry g v *ᵥ c = aeval g (pol c) *ᵥ v := by
  rw [pol, map_sum, Matrix.sum_mulVec]
  funext i
  rw [Finset.sum_apply]
  simp only [aeval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, kry, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Simplify using `[pol, coeff_monomial, Fin.val_inj]`.
-/
private theorem coeff_pol (c : Fin n → R) (i : Fin n) : (pol c).coeff i = c i := by
  simp [pol, coeff_monomial, Fin.val_inj]

/- English proof (translation)
Simplify using `only [pol, ← C_mul_X_pow_eq_monomial]`. Conclude with `degree_sum_fin_lt c`.
-/
private theorem degree_pol (c : Fin n → R) : (pol c).degree < n := by
  simp only [pol, ← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt c

/- English proof (translation)
Simplify using `only [pol]`. Conclude with `sum_fin (fun i a => monomial i a) (by simp) h |>.trans (sum_monomial_eq p)`.
-/
private theorem pol_coeff (p : R[X]) (h : p.degree < n) : pol (fun i : Fin n => p.coeff i) = p := by
  simp only [pol]
  exact sum_fin (fun i a => monomial i a) (by simp) h |>.trans (sum_monomial_eq p)

/- English proof (translation)
Rewrite using `[kry_mulVec, pol_coeff, ← Matrix.aeval_eq_aeval_mod_charpoly]`. Use `degree_modByMonic_lt p g.charpoly_monic` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_degree_eq_dim, Fintype.card_fin]`. Then use the resulting hypothesis.
-/
private theorem aeval_mulVec [Nontrivial R] (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (p : R[X]) :
    aeval g p *ᵥ v = kry g v *ᵥ fun i : Fin n => (p %ₘ g.charpoly).coeff i := by
  rw [kry_mulVec, pol_coeff, ← Matrix.aeval_eq_aeval_mod_charpoly]
  have := degree_modByMonic_lt p g.charpoly_monic
  rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (aeval_mulVec g v (X ^ ((j : ℕ) + 1))) i` as an intermediate fact. Rewrite `this` using `[map_pow, aeval_X, pow_succ', ← Matrix.mulVec_mulVec]`. Conclude with `this`.
-/
private theorem mul_kry [Nontrivial R] (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    g * kry g v = kry g v * Matrix.of fun i j : Fin n => ((X ^ ((j : ℕ) + 1) : R[X]) %ₘ g.charpoly).coeff i := by
  ext i j
  have := congrFun (aeval_mulVec g v (X ^ ((j : ℕ) + 1))) i
  rw [map_pow, aeval_X, pow_succ', ← Matrix.mulVec_mulVec] at this
  exact this

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [kry, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec, ← Matrix.map_pow]`.
-/
private theorem kry_map {S : Type} [CommRing S] (f : R →+* S) (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (kry g v).map f = kry (g.map f) (f ∘ v) := by
  ext i j
  simp only [kry, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec, ← Matrix.map_pow]

end

section
variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DvdOfAeval.dvd_of_aeval g h p hp`.
-/
private theorem dvd_of_aeval (g : Matrix (Fin n) (Fin n) K) (h : g.charpoly.Separable) (p : K[X])
    (hp : aeval g p = 0) : g.charpoly ∣ p :=
  _root_.UpperTheory.Reformulated.B.DvdOfAeval.dvd_of_aeval g h p hp

/- English proof (translation)
Take `⟨x, hx⟩` from `Module.exists_ker_toSpanSingleton_eq_annihilator (R := K[X]) (M := Module.AEval' (Matrix.toLin' g))`. Take `⟨v, rfl⟩` from `(Module.AEval'.of (Matrix.toLin' g)).surjective x`. Use `⟨v, fun h0 => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, h1⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Rewrite `h1` using `[kry_mulVec]`.

Establish `e : aeval (Matrix.toLin' g) (pol c) = Matrix.toLin' (aeval g (pol c))` using `aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)) g (pol c)`. Establish `h2 : pol c ∈ LinearMap.ker (LinearMap.toSpanSingleton K[X] _ (Module.AEval'.of (Matrix.toLin' g) v))`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul, e]`. Simplify using `[h1]`. Rewrite `h2` using `[hx, ← span_minpoly_eq_annihilator, Ideal.mem_span_singleton, minpoly.dvd_iff, e, LinearEquiv.map_eq_zero_iff]`.

Establish `h3` using `dvd_of_aeval g h _ h2`. Establish `h4 : pol c = 0` using `eq_zero_of_dvd_of_degree_lt h3 (by`. Rewrite using `[Matrix.charpoly_degree_eq_dim, Fintype.card_fin]`. Conclude with `degree_pol c)`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[← coeff_pol c i, h4, coeff_zero, Pi.zero_apply]`.
-/
private theorem exists_kry_field (g : Matrix (Fin n) (Fin n) K) (h : g.charpoly.Separable) :
    ∃ v, (kry g v).det ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator (R := K[X])
    (M := Module.AEval' (Matrix.toLin' g))
  obtain ⟨v, rfl⟩ := (Module.AEval'.of (Matrix.toLin' g)).surjective x
  refine ⟨v, fun h0 => ?_⟩
  obtain ⟨c, hc, h1⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [kry_mulVec] at h1
  have e : aeval (Matrix.toLin' g) (pol c) = Matrix.toLin' (aeval g (pol c)) :=
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)) g (pol c)
  have h2 : pol c ∈ LinearMap.ker (LinearMap.toSpanSingleton K[X] _ (Module.AEval'.of (Matrix.toLin' g) v)) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul, e]
    simp [h1]
  rw [hx, ← span_minpoly_eq_annihilator, Ideal.mem_span_singleton, minpoly.dvd_iff, e,
    LinearEquiv.map_eq_zero_iff] at h2
  have h3 := dvd_of_aeval g h _ h2
  have h4 : pol c = 0 := eq_zero_of_dvd_of_degree_lt h3 (by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]; exact degree_pol c)
  apply hc
  funext i
  rw [← coeff_pol c i, h4, coeff_zero, Pi.zero_apply]

end

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.G8.exists_kry g h`.
-/
private theorem exists_kry {R : Type} [CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (h : g.charpoly.Separable) : ∃ v, IsUnit (kry g v).det :=
  _root_.UpperTheory.Reformulated.B.G8.exists_kry g h

end UpperTheory.ConvolutionTheory.D

open UpperTheory.ConvolutionTheory.D in
/- English proof (translation)
Introduce `k R _ _ _ _ _ n g h`. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Conclude with `⟨fun g' _ => ⟨1, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩, fun p => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩⟩`. Use `PositivityTheory.UnitarySelfGeneration.free_semilocal k R` as an intermediate fact. Take `⟨v, hv⟩` from `exists_kry g h`.

Take `⟨P, hP⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hv`. Use `⟨fun g' hg => ?_, fun y hy => ?_, fun p => ⟨fun hp => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨v', hv'⟩` from `exists_kry g' (hg ▸ h)`. Take `⟨Q, hQ⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hv'`. Establish `h1` using `mul_kry g v`.

Establish `h2` using `mul_kry g' v'`. Rewrite `h2` using `[hg, ← hQ]`. Rewrite `h1` using `[← hP]`. Use `⟨P * Q⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← mul_assoc, h1, mul_assoc, mul_assoc]`.

Use `congr 1`. Rewrite using `[Units.mul_inv_eq_iff_eq_mul, mul_assoc, h2, Units.inv_mul_cancel_left]`. Set `c` to `(P⁻¹).val *ᵥ (y *ᵥ v)`. Establish `h1 : aeval g (pol c) *ᵥ v = y *ᵥ v`. Rewrite using `[← kry_mulVec, ← hP, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.

Use `⟨pol c, (Units.mul_left_inj P).1 ?_⟩` and prove the remaining obligations. Rewrite using `[hP]`. Use extensionality with `i j`. Establish `c1 : y * g ^ (j : ℕ) = g ^ (j : ℕ) * y` using `(Commute.pow_right hy j).eq`. Establish `c2 : aeval g (pol c) * g ^ (j : ℕ) = g ^ (j : ℕ) * aeval g (pol c)`.

Rewrite using `[← aeval_X_pow (R := R), ← map_mul, ← map_mul, mul_comm]`. Express the relevant statement in the definitionally equal form `(y *ᵥ (g ^ (j : ℕ) *ᵥ v)) i = (aeval g (pol c) *ᵥ (g ^ (j : ℕ) *ᵥ v)) i`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c1, c2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]`. Establish `h1` using `aeval_mulVec g v p`. Rewrite `h1` using `[hp, Matrix.zero_mulVec, ← hP]`.

Establish `h2` using `congrArg (fun z => (P⁻¹).val *ᵥ z) h1`. Simplify using `only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2`. Rewrite using `[← modByMonic_eq_zero_iff_dvd g.charpoly_monic]`. Establish `h3` using `degree_modByMonic_lt p g.charpoly_monic`. Rewrite `h3` using `[Matrix.charpoly_degree_eq_dim, Fintype.card_fin]`.

Rewrite using `[← pol_coeff _ h3, ← h2]`. Simplify using `[pol]`. Introduce and unpack `⟨q, rfl⟩`. Rewrite using `[map_mul, Matrix.aeval_self_charpoly, zero_mul]`.
-/
theorem UpperTheory.ConvolutionTheory.D.conjSep :
    UpperTheory.ConvolutionTheory.D.ConjSep := by
  intro k R _ _ _ _ _ n g h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨fun g' _ => ⟨1, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩,
      fun p => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩⟩
  have := PositivityTheory.UnitarySelfGeneration.free_semilocal k R
  obtain ⟨v, hv⟩ := exists_kry g h
  obtain ⟨P, hP⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv
  refine ⟨fun g' hg => ?_, fun y hy => ?_, fun p => ⟨fun hp => ?_, ?_⟩⟩
  · obtain ⟨v', hv'⟩ := exists_kry g' (hg ▸ h)
    obtain ⟨Q, hQ⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv'
    have h1 := mul_kry g v
    have h2 := mul_kry g' v'
    rw [hg, ← hQ] at h2
    rw [← hP] at h1
    refine ⟨P * Q⁻¹, ?_⟩
    rw [Units.val_mul, ← mul_assoc, h1, mul_assoc, mul_assoc]
    congr 1
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h2, Units.inv_mul_cancel_left]
  · let c := (P⁻¹).val *ᵥ (y *ᵥ v)
    have h1 : aeval g (pol c) *ᵥ v = y *ᵥ v := by
      rw [← kry_mulVec, ← hP, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    refine ⟨pol c, (Units.mul_left_inj P).1 ?_⟩
    rw [hP]
    ext i j
    have c1 : y * g ^ (j : ℕ) = g ^ (j : ℕ) * y := (Commute.pow_right hy j).eq
    have c2 : aeval g (pol c) * g ^ (j : ℕ) = g ^ (j : ℕ) * aeval g (pol c) := by
      rw [← aeval_X_pow (R := R), ← map_mul, ← map_mul, mul_comm]
    change (y *ᵥ (g ^ (j : ℕ) *ᵥ v)) i = (aeval g (pol c) *ᵥ (g ^ (j : ℕ) *ᵥ v)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c1, c2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
  · have h1 := aeval_mulVec g v p
    rw [hp, Matrix.zero_mulVec, ← hP] at h1
    have h2 := congrArg (fun z => (P⁻¹).val *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [← modByMonic_eq_zero_iff_dvd g.charpoly_monic]
    have h3 := degree_modByMonic_lt p g.charpoly_monic
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at h3
    rw [← pol_coeff _ h3, ← h2]
    simp [pol]
  · rintro ⟨q, rfl⟩
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
