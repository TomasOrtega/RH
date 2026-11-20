import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

/- English proof (translation)
Simplify using `[UpperTheory.Gal.GamX.lp]`.
-/
private theorem lp_zero' : UpperTheory.Gal.GamX.lp (0 : Multiset ℂˣ) = 1 := by
  simp [UpperTheory.Gal.GamX.lp]

/- English proof (translation)
Simplify using `[UpperTheory.Gal.GamX.lp]`.
-/
private theorem lp_cons' (a : ℂˣ) (A : Multiset ℂˣ) :
    UpperTheory.Gal.GamX.lp (a ::ₘ A) = (1 - Polynomial.C (a : ℂ) * Polynomial.X) * UpperTheory.Gal.GamX.lp A := by
  simp [UpperTheory.Gal.GamX.lp]

/- English proof (translation)
Proceed by induction on `A using Multiset.induction_on with`. Consider the case `empty => simp [lp_zero']`. Consider the case `cons a A ih => rw [lp_cons', Polynomial.eval_mul, ih]`. Simplify using the standard rewrite rules.
-/
private theorem lp_eval_zero (A : Multiset ℂˣ) : (UpperTheory.Gal.GamX.lp A).eval 0 = 1 := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih => rw [lp_cons', Polynomial.eval_mul, ih]; simp

/- English proof (translation)
Introduce `h`. Establish `h1` using `lp_eval_zero A`. Rewrite `h1` using `[h]`. Simplify using `at h1`.
-/
private theorem lp_ne_zero (A : Multiset ℂˣ) : UpperTheory.Gal.GamX.lp A ≠ 0 := by
  intro h
  have h1 := lp_eval_zero A
  rw [h] at h1
  simp at h1

/- English proof (translation)
Establish `ha : (a : ℂ) ≠ 0` using `a.ne_zero`. Rewrite using `[Units.val_inv_eq_inv_val, mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha, Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lin_eq (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]) =
      Polynomial.C (-(a : ℂ)) * (Polynomial.X - Polynomial.C ((a⁻¹ : ℂˣ) : ℂ)) := by
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  rw [Units.val_inv_eq_inv_val, mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha,
    Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]
  ring

/- English proof (translation)
Rewrite using `[lin_eq, Polynomial.roots_C_mul _ (by simp), Polynomial.roots_X_sub_C]`.
-/
private theorem lin_roots (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]).roots = {((a⁻¹ : ℂˣ) : ℂ)} := by
  rw [lin_eq, Polynomial.roots_C_mul _ (by simp), Polynomial.roots_X_sub_C]

/- English proof (translation)
Proceed by induction on `A using Multiset.induction_on with`. Consider the case `empty => simp [lp_zero']`. Consider the case `cons a A ih`. Rewrite using `[lp_cons', Polynomial.roots_mul (by rw [← lp_cons']; exact lp_ne_zero _), lin_roots, ih, Multiset.map_cons, Multiset.singleton_add]`.
-/
private theorem lp_roots (A : Multiset ℂˣ) :
    (UpperTheory.Gal.GamX.lp A).roots = A.map (fun a => ((a⁻¹ : ℂˣ) : ℂ)) := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih =>
    rw [lp_cons', Polynomial.roots_mul (by rw [← lp_cons']; exact lp_ne_zero _), lin_roots, ih,
      Multiset.map_cons, Multiset.singleton_add]

/- English proof (translation)
Introduce `A B h`. Establish `h1` using `congrArg Polynomial.roots h`. Rewrite `h1` using `[lp_roots, lp_roots]`. Conclude with `Multiset.map_injective (fun a b hab => inv_injective (Units.ext hab)) h1`.
-/
theorem UpperTheory.Gal.GamX.lpInj :
    UpperTheory.Gal.GamX.LpInj := by
  intro A B h
  have h1 := congrArg Polynomial.roots h
  rw [lp_roots, lp_roots] at h1
  exact Multiset.map_injective (fun a b hab => inv_injective (Units.ext hab)) h1
