import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.Proof.BlockDeterminant

/- English proof (translation)
Apply `hφ` to reduce the goal to its premises. Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, mul_comm _ P.det]`. Establish `h2` using `hP.mul_left_cancel h1`. Rewrite using `[RingHom.map_det, RingHom.map_det]`.

Conclude with `h2`.
-/
theorem det_eq_of_conj {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (M M' : Matrix ι ι A) (P : Matrix ι ι B)
    (hP : IsUnit P.det) (h : P * M.map φ = M'.map φ * P) : M.det = M'.det := by
  apply hφ
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm _ P.det] at h1
  have h2 := hP.mul_left_cancel h1
  rw [RingHom.map_det, RingHom.map_det]
  exact h2

/- English proof (translation)
Establish `e : ∀ M : κ → Matrix ι ι A, (∑ k, c k • M k).map φ = ∑ k, φ (c k) • (M k).map φ`. Introduce `M`. Use extensionality with `a b`. Simplify using `[Matrix.sum_apply, map_sum]`. Rewrite using `[e, e, Matrix.mul_sum, Matrix.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, h]`.
-/
theorem conj_sum {ι κ A B : Type} [Fintype ι] [Fintype κ] [CommRing A] [CommRing B]
    (φ : A →+* B) (c : κ → A) (M M' : κ → Matrix ι ι A) (P : Matrix ι ι B)
    (h : ∀ k, P * (M k).map φ = (M' k).map φ * P) :
    P * (∑ k, c k • M k).map φ = (∑ k, c k • M' k).map φ * P := by
  have e : ∀ M : κ → Matrix ι ι A, (∑ k, c k • M k).map φ = ∑ k, φ (c k) • (M k).map φ := by
    intro M
    ext a b
    simp [Matrix.sum_apply, map_sum]
  rw [e, e, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, h]

/- English proof (translation)
Use `det_eq_of_conj (MvPolynomial.map φ) (MvPolynomial.map_injective φ hφ) _ _ (P.map (MvPolynomial.C : B →+* MvPolynomial κ B)) ?_ ?_` and prove the remaining obligations. Use `hP.map (MvPolynomial.C : B →+* MvPolynomial κ B)` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Use `conj_sum _ _ _ _ _ fun k => ?_` and prove the remaining obligations. Establish `e : ∀ Q : Matrix ι ι A, (Q.map (MvPolynomial.C : A →+* MvPolynomial κ A)).map (MvPolynomial.map φ) = (Q.map φ).map (MvPolynomial.C : B →+* MvPolynomial κ B)`.

Introduce `Q`. Use `ext1 a b`. Simplify using the standard rewrite rules. Rewrite using `[e, e, ← Matrix.map_mul, ← Matrix.map_mul, h]`.
-/
theorem det_generic_eq {ι κ A B : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (M M' : κ → Matrix ι ι A) (P : Matrix ι ι B)
    (hP : IsUnit P.det) (h : ∀ k, P * (M k).map φ = (M' k).map φ * P) :
    (∑ k, (MvPolynomial.X k : MvPolynomial κ A) • (M k).map (MvPolynomial.C : A →+* MvPolynomial κ A)).det =
      (∑ k, (MvPolynomial.X k : MvPolynomial κ A) • (M' k).map (MvPolynomial.C : A →+* MvPolynomial κ A)).det := by
  refine det_eq_of_conj (MvPolynomial.map φ) (MvPolynomial.map_injective φ hφ) _ _
    (P.map (MvPolynomial.C : B →+* MvPolynomial κ B)) ?_ ?_
  · have := hP.map (MvPolynomial.C : B →+* MvPolynomial κ B)
    rwa [RingHom.map_det] at this
  · refine conj_sum _ _ _ _ _ fun k => ?_
    have e : ∀ Q : Matrix ι ι A, (Q.map (MvPolynomial.C : A →+* MvPolynomial κ A)).map (MvPolynomial.map φ) =
        (Q.map φ).map (MvPolynomial.C : B →+* MvPolynomial κ B) := by
      intro Q
      ext1 a b
      simp
    rw [e, e, ← Matrix.map_mul, ← Matrix.map_mul, h]

/- English proof (translation)
Use `det_eq_of_conj φ hφ _ _ (Matrix.kroneckerMap (· * ·) (1 : Matrix κ κ B) P) ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_kronecker]`. Simplify using `using hP.pow _`. Use extensionality with `⟨k, a⟩ ⟨l, b⟩`. Use `congrFun (congrFun (h k l) a) b` as an intermediate fact.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply] at this`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_ite_eq, this]`.
-/
theorem det_block_eq {ι κ A B : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (M M' : κ → κ → Matrix ι ι A) (P : Matrix ι ι B)
    (hP : IsUnit P.det) (h : ∀ k l, P * (M k l).map φ = (M' k l).map φ * P) :
    (Matrix.of fun (pa qb : κ × ι) => M pa.1 qb.1 pa.2 qb.2).det =
      (Matrix.of fun (pa qb : κ × ι) => M' pa.1 qb.1 pa.2 qb.2).det := by
  refine det_eq_of_conj φ hφ _ _ (Matrix.kroneckerMap (· * ·) (1 : Matrix κ κ B) P) ?_ ?_
  · rw [Matrix.det_kronecker]
    simpa using hP.pow _
  · ext ⟨k, a⟩ ⟨l, b⟩
    have := congrFun (congrFun (h k l) a) b
    simp only [Matrix.mul_apply, Matrix.map_apply] at this
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_ite_eq, this]

/- English proof (translation)
Introduce `R H what₂ N i r r' Pm hPm X' p T'`. Establish `key : ∀ (m : ℕ) (f : Fin m → X' → N.O i) (g : Fin m → GE N) (y : X'), (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * ((∑ k, fun x' => f k x' • rO N i r (p x') (g k)) y).map (toK N i) = ((∑ k, fun x' => f k x' • rO N i r' (p x') (g k)) y).map (toK N i) * (Pm (p y) : Matrix ( …`. Introduce `m f g y`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Conclude with `conj_sum _ _ _ _ _ fun k => hPm _ _`.

Establish `back : ∀ a', InSpan N i T' (fun y => rO N i r' (p y)) a' → ∃ a, InSpan N i T' (fun y => rO N i r (p y)) a ∧ ∀ y, (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (a y).map (toK N i) = (a' y).map (toK N i) * (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i))`. Introduce and unpack `a' ⟨m, f, g, hf, rfl⟩`. Conclude with `⟨_, ⟨m, f, g, hf, rfl⟩, key m f g⟩`. Establish `hinj : Function.Injective (toK N i)` using `IsFractionRing.injective _ _`. Establish `hU : ∀ x, IsUnit (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i)).det` using `fun x => (Matrix.isUnit_iff_isUnit_det _).1 (Pm x).isUnit`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨m, f, g, hf, rfl⟩`. Conclude with `⟨_, ⟨m, f, g, hf, rfl⟩, key m f g⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun m a' ha' d => ?_, fun g Θ' hΘ' => ?_⟩` and prove the remaining obligations.

Use `choose a ha hc using fun k => back (a' k) (ha' k)`. Use `h1 m a ha d` as an intermediate fact. Use `this using 2 with y` and compare the differences between its conclusion and the goal. Rewrite using `[det_generic_eq (toK N i) hinj (fun k => a k y) (fun k => a' k y) _ (hU (p y)) (fun k => hc k y)]`. Use `choose Θ hΘ hc using fun k l => back (Θ' k l) (hΘ' k l)`.

Use `h2 g Θ hΘ` as an intermediate fact. Use `this using 2 with y` and compare the differences between its conclusion and the goal. Conclude with `(det_block_eq (toK N i) hinj (fun k l => Θ k l y) (fun k l => Θ' k l y) _ (hU (p y)) (fun k l => hc k l y)).symm`.
-/
theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (Pm : N.X i → GL (Fin R.nV) (KK N i)), (∀ x g, (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → ∀ (X' : Type) (p : X' → N.X i) (T' : Subalgebra (N.O i) (X' → N.O i)), (∀ a, InSpan N i T' (fun y => rO N i r (p y)) a → ∃ a', InSpan N i T' (fun y => rO N i r' (p y)) a' ∧ ∀ y, (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (a y).map (toK N i) = (a' y).map (toK N i) * (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) ∧ (CharpolyCoeffsInSubalgebra N i T' (fun y => rO N i r (p y)) → CharpolyCoeffsInSubalgebra N i T' (fun y => rO N i r' (p y))) := by
  intro R H what₂ N i r r' Pm hPm X' p T'
  have key : ∀ (m : ℕ) (f : Fin m → X' → N.O i) (g : Fin m → GE N) (y : X'),
      (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) *
        ((∑ k, fun x' => f k x' • rO N i r (p x') (g k)) y).map (toK N i) =
      ((∑ k, fun x' => f k x' • rO N i r' (p x') (g k)) y).map (toK N i) *
        (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) := by
    intro m f g y
    rw [Finset.sum_apply, Finset.sum_apply]
    exact conj_sum _ _ _ _ _ fun k => hPm _ _
  have back : ∀ a', InSpan N i T' (fun y => rO N i r' (p y)) a' →
      ∃ a, InSpan N i T' (fun y => rO N i r (p y)) a ∧ ∀ y,
        (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (a y).map (toK N i) =
          (a' y).map (toK N i) * (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) := by
    rintro a' ⟨m, f, g, hf, rfl⟩
    exact ⟨_, ⟨m, f, g, hf, rfl⟩, key m f g⟩
  have hinj : Function.Injective (toK N i) := IsFractionRing.injective _ _
  have hU : ∀ x, IsUnit (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i)).det := fun x =>
    (Matrix.isUnit_iff_isUnit_det _).1 (Pm x).isUnit
  refine ⟨?_, ?_⟩
  · rintro a ⟨m, f, g, hf, rfl⟩
    exact ⟨_, ⟨m, f, g, hf, rfl⟩, key m f g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun m a' ha' d => ?_, fun g Θ' hΘ' => ?_⟩
    · choose a ha hc using fun k => back (a' k) (ha' k)
      have := h1 m a ha d
      convert this using 2 with y
      rw [det_generic_eq (toK N i) hinj (fun k => a k y) (fun k => a' k y) _ (hU (p y))
        (fun k => hc k y)]
    · choose Θ hΘ hc using fun k l => back (Θ' k l) (hΘ' k l)
      have := h2 g Θ hΘ
      convert this using 2 with y
      exact (det_block_eq (toK N i) hinj (fun k l => Θ k l y) (fun k l => Θ' k l y) _ (hU (p y))
        (fun k l => hc k l y)).symm

end GlobalTheory.Proof.BlockDeterminant
