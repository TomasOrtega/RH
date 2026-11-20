import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowSmulEqOfMemCompletedLattice
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorRationalTensor
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh61.exists_den_finset D s`.
-/
private lemma exists_den_finset {p : ℕ} [Fact p.Prime] (D : Datum p) (s : Finset (VQ D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ s, ∃ a : D.La, k • x = (1 : ℚ) ⊗ₜ[ℤ] a :=
  _root_.UpperTheory.Reformulated.B.Qh61.exists_den_finset D s

/- English proof (translation)
Take `⟨k, hk, hs⟩` from `exists_den_finset D s`. Use `⟨k, hk, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [smul_add, ha, hb, TensorProduct.tmul_add]⟩`. Consider the case `neg x _ hx`.

Take `⟨a, ha⟩` from `hx`. Conclude with `⟨-a, by rw [smul_neg, ha, TensorProduct.tmul_neg]⟩`.
-/
private lemma exists_den_closure {p : ℕ} [Fact p.Prime] (D : Datum p) (s : Finset (VQ D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ AddSubgroup.closure (s : Set (VQ D)),
      ∃ a : D.La, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  obtain ⟨k, hk, hs⟩ := exists_den_finset D s
  refine ⟨k, hk, fun x hx => ?_⟩
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [smul_add, ha, hb, TensorProduct.tmul_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨-a, by rw [smul_neg, ha, TensorProduct.tmul_neg]⟩

/- English proof (translation)
Introduce `p _ D X`. Take `⟨-, s, -, hmem⟩` from `X.hM`. Take `⟨k, hk, hkc⟩` from `exists_den_closure D s`. Take `⟨j, hj, -, hjS⟩` from `GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem p D X.S`. Use `⟨k * j, Nat.mul_pos hk hj, fun w hw => ?_⟩` and prove the remaining obligations.

Take `⟨m, hm, hc⟩` from `(hmem w).1 hw.1`. Take `⟨a₁, ha₁⟩` from `hkc _ hc`. Establish `hST : X.S (X.r w) = (1 : AfP p) ⊗ₜ[ℚ] w`. Establish `h` using `congrArg (fun f => f ((1 : AfP p) ⊗ₜ[ℚ] w)) X.ST`. Simplify `h` using `[UpperTheory.Gal.W2.Wit.Sys.r_apply]`.

Establish `hin : (1 : AfP p) ⊗ₜ[ℚ] (j • w) ∈ LaHat D`. Establish `h` using `hjS _ hw.2`. Rewrite `h` using `[hST]`. Rewrite using `[TensorProduct.tmul_smul]` and apply the resulting hypothesis. Take `⟨r, a₂, ha₂⟩` from `UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice p D (j • w) hin`.

Establish `hcop : IsCoprime (m : ℤ) ((p ^ r : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hm)`. Take `⟨u, v, huv⟩` from `hcop`. Use `⟨(u * j) • a₁ + (v * k) • a₂, ?_⟩` and prove the remaining obligations. Establish `e₁ : ((k : ℤ) * m) • w = (1 : ℚ) ⊗ₜ[ℤ] a₁`. Rewrite using `[← ha₁, smul_smul, ← Nat.cast_mul, natCast_zsmul]`.

Establish `e₂ : (((p ^ r : ℕ) : ℤ) * j) • w = (1 : ℚ) ⊗ₜ[ℤ] a₂`. Rewrite using `[← ha₂, smul_smul, ← Nat.cast_mul, natCast_zsmul]`. Rewrite using `[TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← e₁, ← e₂, smul_smul, smul_smul, ← add_smul, ← natCast_zsmul]`. Use `congr 1`. Move the coercions through the operations in `at huv ⊢`.

Take the linear combination `(-(k : ℤ) * j) * huv`.
-/
theorem UpperTheory.exists_denominator_of_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), ∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D X
  obtain ⟨-, s, -, hmem⟩ := X.hM
  obtain ⟨k, hk, hkc⟩ := exists_den_closure D s
  obtain ⟨j, hj, -, hjS⟩ := GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem p D X.S
  refine ⟨k * j, Nat.mul_pos hk hj, fun w hw => ?_⟩
  obtain ⟨m, hm, hc⟩ := (hmem w).1 hw.1
  obtain ⟨a₁, ha₁⟩ := hkc _ hc
  have hST : X.S (X.r w) = (1 : AfP p) ⊗ₜ[ℚ] w := by
    have h := congrArg (fun f => f ((1 : AfP p) ⊗ₜ[ℚ] w)) X.ST
    simpa [UpperTheory.Gal.W2.Wit.Sys.r_apply] using h
  have hin : (1 : AfP p) ⊗ₜ[ℚ] (j • w) ∈ LaHat D := by
    have h := hjS _ hw.2
    rw [hST] at h
    rwa [TensorProduct.tmul_smul]
  obtain ⟨r, a₂, ha₂⟩ := UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice p D (j • w) hin
  have hcop : IsCoprime (m : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hm)
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(u * j) • a₁ + (v * k) • a₂, ?_⟩
  have e₁ : ((k : ℤ) * m) • w = (1 : ℚ) ⊗ₜ[ℤ] a₁ := by
    rw [← ha₁, smul_smul, ← Nat.cast_mul, natCast_zsmul]
  have e₂ : (((p ^ r : ℕ) : ℤ) * j) • w = (1 : ℚ) ⊗ₜ[ℤ] a₂ := by
    rw [← ha₂, smul_smul, ← Nat.cast_mul, natCast_zsmul]
  rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← e₁, ← e₂,
    smul_smul, smul_smul, ← add_smul, ← natCast_zsmul]
  congr 1
  push_cast at huv ⊢
  linear_combination (-(k : ℤ) * j) * huv
