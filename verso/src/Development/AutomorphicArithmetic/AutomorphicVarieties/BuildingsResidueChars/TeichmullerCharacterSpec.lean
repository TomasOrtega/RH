import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Introduce `l _ c x m hcop hx hres`. Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨-, -, -, -, -, -, -, -, hunit⟩` from `dvrFacts l c.O`. Establish `hnd : ¬ l ∣ m` using `fun h => (Nat.Prime.one_lt (Fact.out : l.Prime)).ne' (Nat.Coprime.eq_one_of_dvd hcop h)`.

Establish `hm` using `hunit m hnd`. Establish `hX : (x : c.O) ^ m = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, hx, Units.val_one]`. Establish `hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0`. Rewrite using `[geom_sum_mul, hX, sub_self]`.

Establish `hres' : residue c.O (∑ i ∈ Finset.range m, (x : c.O) ^ i) = residue c.O (m : c.O)`. Simplify using `[map_sum, map_pow, hres]`. Establish `hS : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i)`. Rewrite using `[← isUnit_map_iff (residue c.O), hres', isUnit_map_iff]`. Conclude with `hm`.

Establish `h0 : (x : c.O) - 1 = 0` using `hS.mul_right_eq_zero.mp hgeom`. Conclude with `Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)`.
-/
theorem UpperTheory.teichmuller_character_spec :
    UpperTheory.V.Sd.S3.Teich := by
  intro l _ c x m hcop hx hres
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l c.O
  have hnd : ¬ l ∣ m := fun h =>
    (Nat.Prime.one_lt (Fact.out : l.Prime)).ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hm := hunit m hnd
  have hX : (x : c.O) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0 := by
    rw [geom_sum_mul, hX, sub_self]
  have hres' : residue c.O (∑ i ∈ Finset.range m, (x : c.O) ^ i) = residue c.O (m : c.O) := by
    simp [map_sum, map_pow, hres]
  have hS : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i) := by
    rw [← isUnit_map_iff (residue c.O), hres', isUnit_map_iff]
    exact hm
  have h0 : (x : c.O) - 1 = 0 := hS.mul_right_eq_zero.mp hgeom
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)
