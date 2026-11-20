import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatement
import ReciprocityTheory.DualLattices.ProdEraseUpdate
import ReciprocityTheory.DualLattices.IsLocalOfIntegers

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def uR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R :=
  (hv.exists_of_le_one (D.u_int j y)).choose

/- English proof (translation)
The claim follows from `(hv.exists_of_le_one (D.u_int j y)).choose_spec`.
-/
theorem uR_spec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    algebraMap R C (uR hv D j y) = D.u j y :=
  (hv.exists_of_le_one (D.u_int j y)).choose_spec

def MuR (hv : v.Integers R) (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) R :=
  Matrix.of fun y α => ∏ j, uR hv D j y ^ (α j).val

/- English proof (translation)
Conclude with `(f.map_det M).symm`.
-/
theorem det_map' {S : Type} [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (M.map f).det = f M.det := by
  exact (f.map_det M).symm

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Rewrite `hx` using `[hv.isUnit_iff_valuation_eq_one.mp hu]`. Conclude with `lt_irrefl _ hx`.
-/
theorem mem_max_of_lt (hv : v.Integers R) [IsLocalRing R] {x : R} (hx : v (algebraMap R C x) < 1) :
    x ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [hv.isUnit_iff_valuation_eq_one.mp hu] at hx
  exact lt_irrefl _ hx

/- English proof (translation)
Rewrite using `[← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]`. Conclude with `mem_max_of_lt hv hp1`.
-/
theorem residue_p (hv : v.Integers R) [IsLocalRing R] (hp1 : v (algebraMap R C (p : R)) < 1) :
    ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := by
  rw [← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]
  exact mem_max_of_lt hv hp1

/- English proof (translation)
Establish `h` using `D.u_cong j y`. Rewrite `h` using `[← uR_spec hv D j y, ← map_sub]`. Establish `hm` using `mem_max_of_lt hv h`. Rewrite `hm` using `[← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]`. Rewrite using `[hm, lam]`.

Simplify using `only [map_sum, map_mul, map_natCast, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[xc, ZMod.castHom_apply, ZMod.natCast_val]`.
-/
theorem residue_uR (hv : v.Integers R) [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    IsLocalRing.residue R (uR hv D j y) = lam (D.Λ.map (IsLocalRing.residue R)) j y := by
  have h := D.u_cong j y
  rw [← uR_spec hv D j y, ← map_sub] at h
  have hm := mem_max_of_lt hv h
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
  rw [hm, lam]
  simp only [map_sum, map_mul, map_natCast, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xc, ZMod.castHom_apply, ZMod.natCast_val]

/- English proof (translation)
Use `haveI : Nontrivial R := (algebraMap R C).domain_nontrivial`. Establish `hlt : ∀ x : R, x ∈ nonunits R → v (algebraMap R C x) < 1` using `fun x hx => lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_iff_valuation_eq_one.mpr h)`. Use `letI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb hu => by`. Establish `h1` using `hv.isUnit_iff_valuation_eq_one.mp hu`. Establish `h2 : v (algebraMap R C (a + b)) < 1`.

Rewrite using `[map_add]`. Conclude with `v.map_add_lt (hlt a ha) (hlt b hb)`. Rewrite `h2` using `[h1]`. Conclude with `lt_irrefl _ h2`. Use `haveI : CharP (IsLocalRing.ResidueField R) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (residue_p hv hp1)`.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Establish `hM : (IsLocalRing.residue R).mapMatrix (MuR hv D) = Matrix.of fun (x α : Nb p g) => monF (p` using `p) (D.Λ.map (IsLocalRing.residue R)) α x := by`. Use extensionality with `y α`. Simplify using `[MuR, monF, residue_uR hv D]`. Rewrite using `[hM]`.

Use `det_monF_ne_zero _ ?_` and prove the remaining obligations. Rewrite using `[det_map']`. Conclude with `D.Λ_det.map _`.
-/
theorem isUnit_det_MuR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1)
    (D : Lifts H U X) : IsUnit (MuR hv D).det := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hlt : ∀ x : R, x ∈ nonunits R → v (algebraMap R C x) < 1 := fun x hx =>
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_iff_valuation_eq_one.mpr h)
  letI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb hu => by
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hu
    have h2 : v (algebraMap R C (a + b)) < 1 := by
      rw [map_add]; exact v.map_add_lt (hlt a ha) (hlt b hb)
    rw [h1] at h2
    exact lt_irrefl _ h2
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (residue_p hv hp1)
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hM : (IsLocalRing.residue R).mapMatrix (MuR hv D) =
      Matrix.of fun (x α : Nb p g) => monF (p := p) (D.Λ.map (IsLocalRing.residue R)) α x := by
    ext y α
    simp [MuR, monF, residue_uR hv D]
  rw [hM]
  refine det_monF_ne_zero _ ?_
  rw [det_map']
  exact D.Λ_det.map _

/- English proof (translation)
Use extensionality with `y α`. Simplify using `only [valM, monX, xL, MuR, Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply, map_prod, map_pow, uR_spec, mul_pow, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valM_eq (hv : v.Integers R) (D : Lifts H U X) :
    valM D = (MuR hv D).map (algebraMap R C) *
      Matrix.diagonal fun α : Nb p g => algebraMap R C (∏ j, D.ε j ^ (α j).val) := by
  ext y α
  simp only [valM, monX, xL, MuR, Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply,
    map_prod, map_pow, uR_spec, mul_pow, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Rewrite using `[valM_eq hv D, Matrix.det_mul, det_map', Matrix.det_diagonal]`. Use `mul_ne_zero ((isUnit_det_MuR hv hp1 D).map (algebraMap R C)).ne_zero ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.mpr fun α _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_ne_zero_iff.mpr fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ ((map_ne_zero_iff _ hv.hom_inj).mpr (D.ε_ne j))`.
-/
theorem det_valM_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X) :
    (valM D).det ≠ 0 := by
  rw [valM_eq hv D, Matrix.det_mul, det_map', Matrix.det_diagonal]
  refine mul_ne_zero ((isUnit_det_MuR hv hp1 D).map (algebraMap R C)).ne_zero ?_
  refine Finset.prod_ne_zero_iff.mpr fun α _ => ?_
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [map_pow]
  exact pow_ne_zero _ ((map_ne_zero_iff _ hv.hom_inj).mpr (D.ε_ne j))

end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X D`. Conclude with `FrobeniusValuationMatrix.det_valM_ne hS.integers hS.p_lt D`.
-/
theorem liftMonomialDeterminantStatement_holds : LiftMonomialDeterminantStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X D
  exact FrobeniusValuationMatrix.det_valM_ne hS.integers hS.p_lt D

end ReciprocityTheory.PGsh.Up
