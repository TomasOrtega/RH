import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Take `⟨N, hN⟩` from `hQ`. Establish `hpow : ∀ (n : ℕ) x, (T ^ n) (mk x) = mk ((D ^ n) x)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`.

Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `x`. Rewrite using `[pow_succ, pow_succ, End.mul_apply, End.mul_apply, hTD, ih]`. Establish `key : ∀ (R' : Polynomial R) x, Polynomial.aeval T (R'.map φ) (mk x) = mk (Polynomial.aeval D R' x)`.

Introduce `R' x`. Proceed by induction on `R' using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Simplify using `only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, hadd]`. Consider the case `monomial n a`.

Rewrite using `[Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, End.mul_apply, End.mul_apply, hpow, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hsmul]`. Use `⟨N, hext _ _ fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← Polynomial.map_pow, key, map_pow, hN]`. Simplify using `[hzero]`.
-/
private theorem nil_transfer {R S M W : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module S W] (φ : R →+* S) (mk : M → W) (hzero : mk 0 = 0)
    (hadd : ∀ x y, mk (x + y) = mk x + mk y) (hsmul : ∀ (a : R) x, mk (a • x) = φ a • mk x)
    (hext : ∀ f g : End S W, (∀ x, f (mk x) = g (mk x)) → f = g)
    (T : End S W) (D : End R M) (hTD : ∀ x, T (mk x) = mk (D x)) (Q : Polynomial R)
    (hQ : IsNilpotent (Polynomial.aeval D Q)) : IsNilpotent (Polynomial.aeval T (Q.map φ)) := by
  obtain ⟨N, hN⟩ := hQ
  have hpow : ∀ (n : ℕ) x, (T ^ n) (mk x) = mk ((D ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, hTD, ih]
  have key : ∀ (R' : Polynomial R) x,
      Polynomial.aeval T (R'.map φ) (mk x) = mk (Polynomial.aeval D R' x) := by
    intro R' x
    induction R' using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, hadd]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        End.mul_apply, End.mul_apply, hpow, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, hsmul]
  refine ⟨N, hext _ _ fun x => ?_⟩
  rw [← map_pow, ← Polynomial.map_pow, key, map_pow, hN]
  simp [hzero]

/- English proof (translation)
Introduce `l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV Q g`. Use `haveI := hV.finite`. Conclude with `nil_transfer (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (wdMk P ι ρ) (wdMk_zero P ι ρ) (wdMk_add P ι ρ) (wdMk_smul P ι ρ) (fun _ _ => wd_ext P ι ρ) _ _ (wdRho_mk P ι Bw h hj ρ g) Q`.
-/
theorem UpperTheory.Gal.crystallineComparison.nilRho_of :
    NilRho := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV Q g
  haveI := hV.finite
  exact nil_transfer (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (wdMk P ι ρ) (wdMk_zero P ι ρ)
    (wdMk_add P ι ρ) (wdMk_smul P ι ρ) (fun _ _ => wd_ext P ι ρ) _ _
    (wdRho_mk P ι Bw h hj ρ g) Q
