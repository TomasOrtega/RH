import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Proceed by induction on `m using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i m hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]`.
-/
private theorem cpRed_prod_scaleRoots {k ι : Type} [Field k] (m : Finset ι) (a : ι → k) (s : k) :
    (∏ i ∈ m, (Polynomial.X - C (a i))).scaleRoots s = ∏ i ∈ m, (Polynomial.X - C (a i * s)) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp
  | insert i m hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K X n g`. Establish `hc` using `X.cp_red (resLe T.F_le g)`. Unfold `UpperTheory.V.Ws.Tower.fr at hc`. Establish `hlead : (res c'.O X.B : X.B →+* ResidueField c'.O) (X.cp (resLe T.F_le g)).leadingCoeff ≠ 0`. Rewrite using `[(phiCpMap K X n g).1.leadingCoeff, map_one]`.

Conclude with `one_ne_zero`. Unfold `Link.cpT`. Rewrite using `[map_scaleRoots _ _ _ hlead, hc, cpRed_prod_scaleRoots]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[K.chib i g]`.

Establish `hal : (res c'.O X.B : X.B →+* ResidueField c'.O) (algebraMap c'.O X.B (K.sc n g)) = residue c'.O (K.sc n g)`. Rewrite using `[RingHom.coe_coe, AlgHom.commutes]`. Both sides reduce to the same expression. Rewrite using `[hal]`. Unfold `Link.sc`.

Use `congr 2`. Rewrite using `[(residue c'.O).map_mul (K.κ g : c'.O), (residue c'.O).map_pow, K.β_red, one_pow, mul_one, (residue c'.O).map_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Ws.phiCpRed :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, (K.cpT X n g).map (res c'.O X.B : X.B →+* ResidueField c'.O) = ∏ i, (Polynomial.X - C (K.r.chib i (K.V.pr g) : ResidueField c'.O)) := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  have hc := X.cp_red (resLe T.F_le g)
  unfold UpperTheory.V.Ws.Tower.fr at hc
  have hlead : (res c'.O X.B : X.B →+* ResidueField c'.O) (X.cp (resLe T.F_le g)).leadingCoeff ≠ 0 := by
    rw [(phiCpMap K X n g).1.leadingCoeff, map_one]
    exact one_ne_zero
  unfold Link.cpT
  rw [map_scaleRoots _ _ _ hlead, hc, cpRed_prod_scaleRoots]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [K.chib i g]
  have hal : (res c'.O X.B : X.B →+* ResidueField c'.O) (algebraMap c'.O X.B (K.sc n g)) =
      residue c'.O (K.sc n g) := by
    rw [RingHom.coe_coe, AlgHom.commutes]
    rfl
  rw [hal]
  unfold Link.sc
  congr 2
  rw [(residue c'.O).map_mul (K.κ g : c'.O), (residue c'.O).map_pow, K.β_red, one_pow, mul_one,
    (residue c'.O).map_mul, mul_comm]
  rfl
