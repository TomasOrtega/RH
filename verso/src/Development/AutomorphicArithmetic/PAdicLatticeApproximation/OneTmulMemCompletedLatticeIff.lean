import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

/- English proof (translation)
Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]`. Introduce `hp`. Apply `v.2` to reduce the goal to its premises. Establish `hprime : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible`.

Conclude with `(hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hp)).symm`.
-/
private theorem val_p_eq_one {p : ℕ} [Fact p.Prime] (v : AwayP p) :
    v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hp
  apply v.2
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  exact (hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hp)).symm

/- English proof (translation)
Introduce `v`. Rewrite using `[AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hc : v.1.valuation ℚ (c : ℚ) ≤ 1`. Simplify using `using v.1.valuation_le_one (K := ℚ) c`. Establish `hp : v.1.valuation ℚ ((p ^ r : ℕ) : ℚ) = 1`.

Establish `h1` using `val_p_eq_one v`. Rewrite `h1` using `[eq_intCast]`. Move the coercions through the operations in `at h1 ⊢`. Rewrite using `[map_pow, h1, one_pow]`. Establish `hq : v.1.valuation ℚ q ≤ 1`.

Establish `h2` using `congrArg (v.1.valuation ℚ) h`. Rewrite `h2` using `[map_mul, hp, _root_.one_mul]`. Rewrite using `[h2]`. Conclude with `hc`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]`.

Conclude with `hq`.
-/
private theorem isIntAf_of_pow_mul {p : ℕ} [Fact p.Prime] (q : ℚ) (r : ℕ) (c : ℤ)
    (h : ((p ^ r : ℕ) : ℚ) * q = c) : IsIntAf (algebraMap ℚ (AfP p) q) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hc : v.1.valuation ℚ (c : ℚ) ≤ 1 := by
    simpa using v.1.valuation_le_one (K := ℚ) c
  have hp : v.1.valuation ℚ ((p ^ r : ℕ) : ℚ) = 1 := by
    have h1 := val_p_eq_one v
    rw [eq_intCast] at h1
    push_cast at h1 ⊢
    rw [map_pow, h1, one_pow]
  have hq : v.1.valuation ℚ q ≤ 1 := by
    have h2 := congrArg (v.1.valuation ℚ) h
    rw [map_mul, hp, _root_.one_mul] at h2
    rw [h2]
    exact hc
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  exact hq

/- English proof (translation)
Introduce `p _ D z`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Set `b` to `Module.Free.chooseBasis ℤ D.La`. Set `bQ` to `Algebra.TensorProduct.basis ℚ b`.

Establish `key : ∀ i, (KNLevel.bA b).repr ((1 : AfP p) ⊗ₜ[ℚ] z) i = algebraMap ℚ (AfP p) (bQ.repr z i)`. Introduce `i`. Simplify using `[KNLevel.bA, Algebra.TensorProduct.basis_repr_tmul, bQ]`. Establish `hsm : ∀ (r : ℕ) i, bQ.repr (p ^ r • z) i = ((p ^ r : ℕ) : ℚ) * bQ.repr z i`. Introduce `r i`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]`. Establish `htm : ∀ (x : D.La) i, bQ.repr ((1 : ℚ) ⊗ₜ[ℤ] x) i = (b.repr x i : ℚ)`. Introduce `x i`. Simplify using `[bQ, Algebra.TensorProduct.basis_repr_tmul]`. Rewrite using `[KNLevel.mem_laHat_iff b]`.

Simplify using `only [key]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose k a hka using fun i => T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p (bQ.repr z i) (h i)`. Set `r` to `∑ i, k i`. Set `c : _ → ℤ` to `fun i => (p : ℤ) ^ (r - k i) * a i`.

Establish `hc : ∀ i, ((p ^ r : ℕ) : ℚ) * bQ.repr z i = (c i : ℚ)`. Introduce `i`. Establish `hk : k i ≤ r` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - k i) * (p : ℚ) ^ (k i)`. Rewrite using `[← pow_add, Nat.sub_add_cancel hk]`.

Establish `ha` using `hka i`. Move the coercions through the operations in `at ha ⊢`. Rewrite using `[hpow, _root_.mul_assoc, ha]`. Simplify using `[c]`. Use `⟨r, b.equivFun.symm c, ?_⟩` and prove the remaining obligations.

Apply `bQ.ext_elem` to reduce the goal to its premises. Introduce `i`. Establish `hb : b.repr (b.equivFun.symm c) i = c i`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[hsm, htm, hb]`.

Conclude with `hc i`. Introduce and unpack `⟨r, x, hx⟩ i`. Apply `isIntAf_of_pow_mul _ r (b.repr x i)` to reduce the goal to its premises. Rewrite using `[← hsm, hx, htm]`.
-/
theorem UpperTheory.one_tmul_mem_completedLattice_iff :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (z : VQ D), (1 : AfP p) ⊗ₜ[ℚ] z ∈ LaHat D ↔ ∃ (r : ℕ) (x : D.La), p ^ r • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  intro p _ D z
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  have key : ∀ i, (KNLevel.bA b).repr ((1 : AfP p) ⊗ₜ[ℚ] z) i = algebraMap ℚ (AfP p) (bQ.repr z i) := by
    intro i
    simp [KNLevel.bA, Algebra.TensorProduct.basis_repr_tmul, bQ]
  have hsm : ∀ (r : ℕ) i, bQ.repr (p ^ r • z) i = ((p ^ r : ℕ) : ℚ) * bQ.repr z i := by
    intro r i
    rw [← Nat.cast_smul_eq_nsmul ℚ, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have htm : ∀ (x : D.La) i, bQ.repr ((1 : ℚ) ⊗ₜ[ℤ] x) i = (b.repr x i : ℚ) := by
    intro x i
    simp [bQ, Algebra.TensorProduct.basis_repr_tmul]
  rw [KNLevel.mem_laHat_iff b]
  simp only [key]
  constructor
  · intro h
    choose k a hka using fun i => T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p (bQ.repr z i) (h i)
    let r := ∑ i, k i
    let c : _ → ℤ := fun i => (p : ℤ) ^ (r - k i) * a i
    have hc : ∀ i, ((p ^ r : ℕ) : ℚ) * bQ.repr z i = (c i : ℚ) := by
      intro i
      have hk : k i ≤ r := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - k i) * (p : ℚ) ^ (k i) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      have ha := hka i
      push_cast at ha ⊢
      rw [hpow, _root_.mul_assoc, ha]
      simp [c]
    refine ⟨r, b.equivFun.symm c, ?_⟩
    apply bQ.ext_elem
    intro i
    have hb : b.repr (b.equivFun.symm c) i = c i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hsm, htm, hb]
    exact hc i
  · rintro ⟨r, x, hx⟩ i
    apply isIntAf_of_pow_mul _ r (b.repr x i)
    rw [← hsm, hx, htm]
