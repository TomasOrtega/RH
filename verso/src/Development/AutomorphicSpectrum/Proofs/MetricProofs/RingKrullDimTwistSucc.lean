import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def baseD (p : ℕ) (W : Ideal (MRing ι)) : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Ideal.Quotient.lift W ((Ideal.Quotient.mk (twist p W)).comp inc) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

def baseP (p : ℕ) (W : Ideal (MRing ι)) :
    Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Polynomial.eval₂RingHom (baseD p W) (Ideal.Quotient.mk (twist p W) yN)

def quadP (p : ℕ) (W : Ideal (MRing ι)) : Polynomial (Polynomial (MRing ι ⧸ W)) :=
  Polynomial.X ^ 2 + Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quadraticPolynomial_monic (p : ℕ) (W : Ideal (MRing ι)) : (quadP p W).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quadraticPolynomial_natDegree (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] : (quadP p W).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_add_C

def coordA (p : ℕ) (W : Ideal (MRing ι)) : (Σ o, Tb ι o) → AdjoinRoot (quadP p W)
  | ⟨none, j⟩ => (![AdjoinRoot.root _, AdjoinRoot.of _ Polynomial.X] : Fin 2 → _) j
  | ⟨some k, i⟩ => AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩)))

def toA (p : ℕ) (W : Ideal (MRing ι)) : MRing (Tb ι) →+* AdjoinRoot (quadP p W) :=
  (aeval (coordA p W) : MRing (Tb ι) →ₐ[ℤ] AdjoinRoot (quadP p W)).toRingHom

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem toA_inc (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    toA p W (inc f) = AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W f)) := by
  have h : (toA p W).comp inc =
      (AdjoinRoot.of (quadP p W)).comp (Polynomial.C.comp (Ideal.Quotient.mk W)) := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · intro i
      simp only [RingHom.comp_apply, toA, inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        aeval_X]
      rfl
  exact RingHom.congr_fun h f

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem toA_xN (p : ℕ) (W : Ideal (MRing ι)) : toA p W xN = AdjoinRoot.root _ := by
  simp only [toA, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem toA_yN (p : ℕ) (W : Ideal (MRing ι)) : toA p W yN = AdjoinRoot.of _ Polynomial.X := by
  simp only [toA, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem toA_quad (p : ℕ) (W : Ideal (MRing ι)) : toA p W (quad p) = 0 := by
  have h : AdjoinRoot.mk (quadP p W) (Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_intCast,
    Int.cast_natCast, map_natCast] at h
  have hC : toA p W (MvPolynomial.C (p : ℤ)) = (p : AdjoinRoot (quadP p W)) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quad, map_add, map_mul, map_pow, toA_xN, toA_yN, hC]
  linear_combination h

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem twist_le_ker_toA (p : ℕ) (W : Ideal (MRing ι)) : twist p W ≤ RingHom.ker (toA p W) := by
  unfold twist
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, toA_inc, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero,
      map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 (toA_quad p W)

def quotA (p : ℕ) (W : Ideal (MRing ι)) : (MRing (Tb ι) ⧸ twist p W) →+* AdjoinRoot (quadP p W) :=
  Ideal.Quotient.lift _ (toA p W) fun _ ha => twist_le_ker_toA p W ha

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quotA_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing (Tb ι)) :
    quotA p W (Ideal.Quotient.mk _ f) = toA p W f := by
  exact Ideal.Quotient.lift_mk _ _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem baseD_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    baseD p W (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (inc f) := by
  exact Ideal.Quotient.lift_mk _ _ _

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem baseP_C (p : ℕ) (W : Ideal (MRing ι)) (a : MRing ι ⧸ W) :
    baseP p W (Polynomial.C a) = baseD p W a := by
  simp [baseP]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem baseP_X (p : ℕ) (W : Ideal (MRing ι)) :
    baseP p W Polynomial.X = Ideal.Quotient.mk _ yN := by
  simp [baseP]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quotA_baseP (p : ℕ) (W : Ideal (MRing ι)) (g : Polynomial (MRing ι ⧸ W)) :
    quotA p W (baseP p W g) = AdjoinRoot.of _ g := by
  have h : (quotA p W).comp (baseP p W) = AdjoinRoot.of (quadP p W) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [RingHom.comp_apply, baseP_C, baseD_mk, quotA_mk, toA_inc]
    · rw [RingHom.comp_apply, baseP_X, quotA_mk, toA_yN]
  exact RingHom.congr_fun h g

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem baseMap_injective (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] :
    Function.Injective (baseP p W) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h0 : AdjoinRoot.of (quadP p W) g = 0 := by
    rw [← quotA_baseP, hg, map_zero]
  rw [← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at h0
  obtain ⟨q, hq⟩ := h0
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, Polynomial.C_eq_zero] at hq
    exact hq
  · have h1 := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_C, (quadraticPolynomial_monic p W).natDegree_mul' hq0, quadraticPolynomial_natDegree] at h1
    omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mk_quad_eq_zero (p : ℕ) (W : Ideal (MRing ι)) :
    Ideal.Quotient.mk (twist p W) (quad p) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem baseMap_isIntegralElem_xN (p : ℕ) (W : Ideal (MRing ι)) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) xN) := by
  refine ⟨quadP p W, quadraticPolynomial_monic p W, ?_⟩
  rw [← mk_quad_eq_zero p W]
  have hp : (Ideal.Quotient.mk (twist p W)) (MvPolynomial.C (p : ℤ)) =
      (p : MRing (Tb ι) ⧸ twist p W) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quadP, quad, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_add, baseP_X, map_intCast,
    Int.cast_natCast, hp, map_natCast, Polynomial.eval₂_natCast]

/- English proof (translation)
Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem baseMap_isIntegralElem_X (p : ℕ) (W : Ideal (MRing ι)) (q : Σ o, Tb ι o) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) (X q)) := by
  obtain ⟨o, j⟩ := q
  cases o with
  | none =>
    revert j
    change ∀ j : Fin 2, _
    intro j
    fin_cases j
    · exact baseMap_isIntegralElem_xN p W
    · have h := RingHom.isIntegralElem_map (baseP p W) (x := Polynomial.X)
      rw [baseP_X] at h
      exact h
  | some k =>
    have h : Ideal.Quotient.mk (twist p W) (X ⟨some k, j⟩ : MRing (Tb ι)) =
        baseP p W (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, j⟩))) := by
      rw [baseP_C, baseD_mk]
      simp [inc, oldIdx]
    rw [h]
    exact RingHom.isIntegralElem_map _

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem baseMap_isIntegral (p : ℕ) (W : Ideal (MRing ι)) (b : MRing (Tb ι) ⧸ twist p W) :
    (baseP p W).IsIntegralElem b := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction f using MvPolynomial.induction_on
  · rw [eq_intCast MvPolynomial.C, map_intCast, ← map_intCast (baseP p W)]
    exact RingHom.isIntegralElem_map _
  · rw [map_add]
    exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  · rw [map_mul]
    exact RingHom.IsIntegralElem.mul _ ‹_› (baseMap_isIntegralElem_X p W _)

/- English proof (translation)
Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ringKrullDim_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  haveI : W.IsPrime := hW
  haveI : Nontrivial (MRing ι ⧸ W) := inferInstance
  haveI : IsNoetherianRing (MRing ι) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial ((k : K) × ι k) ℤ))
  letI : Algebra (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) := (baseP p W).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) :=
    ⟨fun b => baseMap_isIntegral p W b⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (baseMap_injective p W),
    Polynomial.ringKrullDim_of_isNoetherianRing]

end GlobalTheory.CompanionTheory.Ar.Tw
