import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.OneAddPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.LowCoeff

def genChar {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] (u : ι → T) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* T where
  toFun g := ∏ q, u q ^ (g.toAdd q).val
  map_one' := by simp
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]

open Classical in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q`. Rewrite using `[Finset.prod_eq_single q]`. Simplify using `[ZMod.val_one]`. Introduce `p _ hp`. Simplify using `[Pi.single_eq_of_ne hp]`.

Simplify using the standard rewrite rules.
-/
theorem genChar_single {T ι : Type} [CommMonoid T] [Fintype ι] (n : ℕ) [NeZero n] [Fact (1 < n)] (u : ι → T)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : genChar n u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

/- English proof (translation)
Introduce `D N X i M ι _ I _ hM h4 F hF m hm`. Establish `hp : (X.l i).Prime` using `(X.lPrime i).out`. Set `J : Ideal (MvPolynomial ι (X.O0 i))` to `I.map (MvPolynomial.C : X.O0 i →+* MvPolynomial ι (X.O0 i)) ⊔ MvPolynomial.idealOfVars ι (X.O0 i) ^ (X.l i ^ (M - nu X i - 1))`. Set `π : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] (MvPolynomial ι (X.O0 i) ⧸ J)` to `Ideal.Quotient.mkₐ (X.O0 i) J`. Establish `hI : ∀ a ∈ I, algebraMap (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) a = 0`.

Introduce `a ha`. Rewrite using `[← π.commutes]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))`. Establish `h4' : ((X.l i : ℕ) : MvPolynomial ι (X.O0 i) ⧸ J) ^ (nu X i + 1) = 0`. Use `hI _ h4` as an intermediate fact.

Rewrite `this` using `[map_pow, map_natCast]`. Then use the resulting hypothesis. Establish `h1 : 1 < X.l i ^ M` using `Nat.one_lt_pow (by omega) hp.one_lt`. Use `haveI : Fact (1 < X.l i ^ M) := ⟨h1⟩`. Use `haveI : NeZero (X.l i ^ M) := ⟨by omega⟩`. Establish `hu : ∀ q, (1 + π (MvPolynomial.X q)) ^ (X.l i ^ M) = 1`.

Introduce `q`. Use `KStar.Tree.one_add_pow_prime_pow_eq_one hp h4' hM ?_` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self q)) _))`. Set `L` to `MonoidAlgebra.lift (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) (Del X i M ι) (genChar (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu)`.

Establish `hc : L.comp (toLam X i M ι) = π`. Use `MvPolynomial.algHom_ext fun q => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, MonoidAlgebra.lift_of]`. Use `genChar_single (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu q` as an intermediate fact. Rewrite using `[sub_eq_iff_eq_add']`.

Use `this` and compare the differences between its conclusion and the goal. Establish `hker : I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ RingHom.ker L`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, L.commutes]`.

Conclude with `hI a ha`. Establish `hFJ : F ∈ J`. Establish `h0 : L (toLam X i M ι F) = 0` using `hker hF`. Establish `: π F = 0` using `by rw [← hc]; exact h0`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hFJ`. Establish `hb0 : b.coeff m = 0` using `(MvPolynomial.mem_pow_idealOfVars_iff' _ b).1 hb m hm`. Rewrite using `[MvPolynomial.coeff_add, hb0, add_zero]`. Conclude with `MvPolynomial.mem_map_C_iff.1 ha m`.
-/
theorem coeff_mem_of_toLam_mem : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (I : Ideal (X.O0 i)), 0 < nu X i → nu X i + 1 ≤ M → (X.l i : X.O0 i) ^ (nu X i + 1) ∈ I → ∀ F : MvPolynomial ι (X.O0 i), toLam X i M ι F ∈ I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) → ∀ m : ι →₀ ℕ, m.degree < X.l i ^ (M - nu X i - 1) → F.coeff m ∈ I := by
  intro D N X i M ι _ I _ hM h4 F hF m hm
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  let J : Ideal (MvPolynomial ι (X.O0 i)) :=
    I.map (MvPolynomial.C : X.O0 i →+* MvPolynomial ι (X.O0 i)) ⊔ MvPolynomial.idealOfVars ι (X.O0 i) ^ (X.l i ^ (M - nu X i - 1))
  let π : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] (MvPolynomial ι (X.O0 i) ⧸ J) := Ideal.Quotient.mkₐ (X.O0 i) J
  have hI : ∀ a ∈ I, algebraMap (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) a = 0 := by
    intro a ha
    rw [← π.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  have h4' : ((X.l i : ℕ) : MvPolynomial ι (X.O0 i) ⧸ J) ^ (nu X i + 1) = 0 := by
    have := hI _ h4
    rwa [map_pow, map_natCast] at this
  have h1 : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : Fact (1 < X.l i ^ M) := ⟨h1⟩
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + π (MvPolynomial.X q)) ^ (X.l i ^ M) = 1 := by
    intro q
    refine KStar.Tree.one_add_pow_prime_pow_eq_one hp h4' hM ?_
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_right (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self q)) _))
  let L := MonoidAlgebra.lift (X.O0 i) (MvPolynomial ι (X.O0 i) ⧸ J) (Del X i M ι)
    (genChar (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu)
  have hc : L.comp (toLam X i M ι) = π := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, MonoidAlgebra.lift_of]
    have := genChar_single (X.l i ^ M) (fun q => 1 + π (MvPolynomial.X q)) hu q
    rw [sub_eq_iff_eq_add']
    convert this
  have hker : I.map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ RingHom.ker L := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, L.commutes]
    exact hI a ha
  have hFJ : F ∈ J := by
    have h0 : L (toLam X i M ι F) = 0 := hker hF
    have : π F = 0 := by rw [← hc]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hFJ
  have hb0 : b.coeff m = 0 := (MvPolynomial.mem_pow_idealOfVars_iff' _ b).1 hb m hm
  rw [MvPolynomial.coeff_add, hb0, add_zero]
  exact MvPolynomial.mem_map_C_iff.1 ha m

end GlobalTheory.StepTwo.LowCoeff

end
