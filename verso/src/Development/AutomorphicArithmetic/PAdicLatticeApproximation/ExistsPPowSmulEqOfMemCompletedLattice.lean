import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowMulIntOfIsIntAfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
Introduce `p _ D w hw`. Use `D.freeLa` as an intermediate fact. Use `D.finLa` as an intermediate fact. Set `b` to `Module.Free.chooseBasis ℤ D.La`. Set `B` to `b.baseChange ℚ`.

Establish `hint : ∀ i, IsIntAf (algebraMap ℚ (AfP p) (B.repr w i))`. Introduce `i`. Establish `h` using `GlobalTheory.LKGeo.LatDvd.isIntAf_adBasis_repr b i hw`. Establish `e : (GlobalTheory.LKGeo.LatDvd.adBasis b).repr ((1 : AfP p) ⊗ₜ[ℚ] w) i = algebraMap ℚ (AfP p) (B.repr w i)`. Simplify using `only [GlobalTheory.LKGeo.LatDvd.adBasis, Module.Basis.baseChange_repr_tmul]`.

Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Use `choose r z hz using fun i => UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p (B.repr w i) (hint i)`. Set `R : ℕ` to `Finset.univ.sup r`. Establish `hR : ∀ i, r i ≤ R` using `fun i => Finset.le_sup (Finset.mem_univ i)`.

Set `a : D.La` to `∑ i, ((p : ℤ) ^ (R - r i) * z i) • b i`. Use `⟨R, a, B.ext_elem fun i => ?_⟩` and prove the remaining obligations. Establish `ha : b.repr a i = (p : ℤ) ^ (R - r i) * z i`. Simplify using `[a, map_sum, Finsupp.single_apply]`. Establish `e2 : B.repr ((1 : ℚ) ⊗ₜ[ℤ] a) i = ((b.repr a i : ℤ) : ℚ)`.

Simplify using `[B, Module.Basis.baseChange_repr_tmul]`. Rewrite using `[e2, ha, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]`. Use `push_cast`. Rewrite using `[← hz i]`. Establish `: (p : ℚ) ^ R = (p : ℚ) ^ (R - r i) * (p : ℚ) ^ r i`.

Rewrite using `[← pow_add, Nat.sub_add_cancel (hR i)]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w : VQ D), (1 : AfP p) ⊗ₜ[ℚ] w ∈ LaHat D → ∃ (r : ℕ) (a : D.La), p ^ r • w = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D w hw
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := b.baseChange ℚ
  have hint : ∀ i, IsIntAf (algebraMap ℚ (AfP p) (B.repr w i)) := by
    intro i
    have h := GlobalTheory.LKGeo.LatDvd.isIntAf_adBasis_repr b i hw
    have e : (GlobalTheory.LKGeo.LatDvd.adBasis b).repr ((1 : AfP p) ⊗ₜ[ℚ] w) i
        = algebraMap ℚ (AfP p) (B.repr w i) := by
      simp only [GlobalTheory.LKGeo.LatDvd.adBasis, Module.Basis.baseChange_repr_tmul]
      rw [Algebra.algebraMap_eq_smul_one]
    rwa [e] at h
  choose r z hz using fun i => UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p (B.repr w i) (hint i)
  let R : ℕ := Finset.univ.sup r
  have hR : ∀ i, r i ≤ R := fun i => Finset.le_sup (Finset.mem_univ i)
  let a : D.La := ∑ i, ((p : ℤ) ^ (R - r i) * z i) • b i
  refine ⟨R, a, B.ext_elem fun i => ?_⟩
  have ha : b.repr a i = (p : ℤ) ^ (R - r i) * z i := by
    simp [a, map_sum, Finsupp.single_apply]
  have e2 : B.repr ((1 : ℚ) ⊗ₜ[ℤ] a) i = ((b.repr a i : ℤ) : ℚ) := by
    simp [B, Module.Basis.baseChange_repr_tmul]
  rw [e2, ha, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  rw [← hz i]
  have : (p : ℚ) ^ R = (p : ℚ) ^ (R - r i) * (p : ℚ) ^ r i := by
    rw [← pow_add, Nat.sub_add_cancel (hR i)]
  rw [this]
  ring
