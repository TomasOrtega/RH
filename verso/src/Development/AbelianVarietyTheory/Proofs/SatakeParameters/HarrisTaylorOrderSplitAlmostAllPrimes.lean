import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfCentralIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapFCoe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoinStatement

namespace GlobalTheory.UPel.HT.Gen.SplitAE
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

/- English proof (translation)
Use `haveI := G.freeO`. Use `haveI := G.finO`. Establish `h1 : Module.finrank ℚ (ℚ ⊗[ℤ] G.O) = Module.finrank ℤ G.O` using `Module.finrank_baseChange`. Use `haveI : Module.Finite ℚ (ℚ ⊗[ℤ] G.O) := inferInstance`. Use `haveI : Module.Finite G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _`.

Establish `h2` using `Module.finrank_mul_finrank ℚ G.F (ℚ ⊗[ℤ] G.O)`. Rewrite `h2` using `[h1, G.rankO]`. Establish `hd : 0 < Module.finrank ℚ G.F` using `Module.finrank_pos`. Establish `: Module.finrank ℚ G.F * Module.finrank G.F (ℚ ⊗[ℤ] G.O) = Module.finrank ℚ G.F * G.m ^ 2`. Rewrite using `[h2, mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_left hd this`.
-/
theorem finrank_eq (G : GDatum) : Module.finrank G.F (ℚ ⊗[ℤ] G.O) = G.m ^ 2 := by
  haveI := G.freeO
  haveI := G.finO
  have h1 : Module.finrank ℚ (ℚ ⊗[ℤ] G.O) = Module.finrank ℤ G.O := Module.finrank_baseChange
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] G.O) := inferInstance
  haveI : Module.Finite G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  have h2 := Module.finrank_mul_finrank ℚ G.F (ℚ ⊗[ℤ] G.O)
  rw [h1, G.rankO] at h2
  have hd : 0 < Module.finrank ℚ G.F := Module.finrank_pos
  have : Module.finrank ℚ G.F * Module.finrank G.F (ℚ ⊗[ℤ] G.O) = Module.finrank ℚ G.F * G.m ^ 2 := by
    rw [h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hd this

/- English proof (translation)
Use `⟨fun z hz => ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[Subalgebra.mem_center_iff]`. Take `⟨N, hN, x, hx⟩` from `GDatum.exists_smul_eq_tmul G z`. Establish `hxc : ∀ y : G.O, x * y = y * x`. Introduce `y`.

Apply `GDatum.tmul_one_injective G` to reduce the goal to its premises. Establish `e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (z * (1 ⊗ₜ y))`. Rewrite using `[← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Establish `e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * z)`. Rewrite using `[← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.

Use `show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)`. Rewrite using `[e1, e2, hz]`. Take `⟨c, e, he, hec⟩` from `G.central x hxc`. Establish `hM : ((e * N : ℤ) : ℚ) • z = algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)`. Rewrite using `[algebraMap_F_coe, ← hec, Int.cast_smul_eq_zsmul, mul_smul, hx, TensorProduct.tmul_smul]`.

Establish `hq : ((e * N : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast mul_ne_zero he hN`. Use `⟨((e * N : ℤ) : ℚ)⁻¹ • (c : G.F), ?_⟩` and prove the remaining obligations. Use `show algebraMap G.F (ℚ ⊗[ℤ] G.O) (((e * N : ℤ) : ℚ)⁻¹ • (c : G.F)) = z`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← hM, smul_smul, inv_mul_cancel₀ hq, one_smul]`.
-/
theorem isCentral (G : GDatum) : Algebra.IsCentral G.F (ℚ ⊗[ℤ] G.O) := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (z * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * z) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hz]
  obtain ⟨c, e, he, hec⟩ := G.central x hxc
  have hM : ((e * N : ℤ) : ℚ) • z = algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) := by
    rw [algebraMap_F_coe, ← hec, Int.cast_smul_eq_zsmul, mul_smul, hx, TensorProduct.tmul_smul]
  have hq : ((e * N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero he hN
  refine ⟨((e * N : ℤ) : ℚ)⁻¹ • (c : G.F), ?_⟩
  show algebraMap G.F (ℚ ⊗[ℤ] G.O) (((e * N : ℤ) : ℚ)⁻¹ • (c : G.F)) = z
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← hM, smul_smul, inv_mul_cancel₀ hq, one_smul]

/- English proof (translation)
Use `haveI := G.finO`. Set `f` to `(Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom`. Conclude with `Module.Finite.of_surjective f.rangeRestrict.toIntAlgHom.toLinearMap f.rangeRestrict_surjective`.
-/
theorem ordB_finite (G : GDatum) : Module.Finite ℤ (ordB G) := by
  haveI := G.finO
  let f := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom
  exact Module.Finite.of_surjective f.rangeRestrict.toIntAlgHom.toLinearMap f.rangeRestrict_surjective

/- English proof (translation)
Take `⟨N, hN, x, hx⟩` from `GDatum.exists_smul_eq_tmul G b`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg N`. Use `⟨n, by omega, x, ?_⟩ show (1 : ℚ) ⊗ₜ[ℤ] x = _` and prove the remaining obligations. Rewrite using `[← hx, natCast_zsmul, nsmul_eq_mul]`. Use `⟨n, by omega, -x, ?_⟩ show (1 : ℚ) ⊗ₜ[ℤ] (-x) = _` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_neg, ← hx, neg_smul, neg_neg, natCast_zsmul, nsmul_eq_mul]`.
-/
theorem ordB_denom (G : GDatum) (b : ℚ ⊗[ℤ] G.O) : ∃ n : ℕ, 0 < n ∧ (n : ℚ ⊗[ℤ] G.O) * b ∈ ordB G := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G b
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · refine ⟨n, by omega, x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] x = _
    rw [← hx, natCast_zsmul, nsmul_eq_mul]
  · refine ⟨n, by omega, -x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] (-x) = _
    rw [TensorProduct.tmul_neg, ← hx, neg_smul, neg_neg, natCast_zsmul, nsmul_eq_mul]

/- English proof (translation)
Introduce `G`. Use `haveI := G.freeO`. Use `haveI := G.finO`. Use `haveI := isCentral G`. Use `haveI := GDatum.isSimpleRing G`.

Use `haveI : FiniteDimensional G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _`. Take `⟨N, hN, hloc⟩` from `GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F (ℚ ⊗[ℤ] G.O) G.m (finrank_eq G) (ordB G) (ordB_finite G) (ordB_denom G)`. Use `⟨N, hN, fun p _ hp => ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `hloc p hp`. Take `⟨ι, hι⟩ : ∃ ι : G.O ⊗[ℤ] ℤ_[p] ≃+* locOrder p (ordB G), ∀ o : G.O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = (1 : ℚ_[p]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)` from `GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite G.O p`.

Take `⟨κ, hκ⟩` from `GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin G.F p`. Set `Φ : G.O ⊗[ℤ] ℤ_[p] ≃+* Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])` to `ι.trans (ψ.toRingEquiv.trans κ.symm.mapMatrix)`. Use `⟨AlgEquiv.ofRingEquiv (f := Φ) fun c => ?_⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `hψ (κ (c ⊗ₜ[ℤ] 1))`. Establish `e1 : ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) = ⟨_, h⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = cenMap p G.F (ℚ ⊗[ℤ] G.O) (κ (c ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] G.F)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, hι, hκ, cenMap, Algebra.TensorProduct.map_tmul]`. Use `show _ = (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)`. Rewrite using `[algebraMap_F_coe]`.

Use `show κ.symm.mapMatrix (ψ (ι _)) = _`. Rewrite using `[e1]`. Use `erw [hh]`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]`.

Apply the tactic sequence `split_ifs <;> simp [RingEquiv.symm_apply_apply]`.
-/
theorem splitAE : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
    Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  intro G
  haveI := G.freeO
  haveI := G.finO
  haveI := isCentral G
  haveI := GDatum.isSimpleRing G
  haveI : FiniteDimensional G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  obtain ⟨N, hN, hloc⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F (ℚ ⊗[ℤ] G.O) G.m (finrank_eq G) (ordB G) (ordB_finite G) (ordB_denom G)
  refine ⟨N, hN, fun p _ hp => ?_⟩
  obtain ⟨ψ, hψ⟩ := hloc p hp
  obtain ⟨ι, hι⟩ : ∃ ι : G.O ⊗[ℤ] ℤ_[p] ≃+* locOrder p (ordB G),
      ∀ o : G.O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = (1 : ℚ_[p]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) :=
    GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite G.O p
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin G.F p
  let Φ : G.O ⊗[ℤ] ℤ_[p] ≃+* Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p]) :=
    ι.trans (ψ.toRingEquiv.trans κ.symm.mapMatrix)
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) fun c => ?_⟩
  obtain ⟨h, hh⟩ := hψ (κ (c ⊗ₜ[ℤ] 1))
  have e1 : ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) = ⟨_, h⟩ := by
    apply Subtype.ext
    show (ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) =
      cenMap p G.F (ℚ ⊗[ℤ] G.O) (κ (c ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] G.F)
    rw [Algebra.TensorProduct.algebraMap_apply, hι, hκ, cenMap, Algebra.TensorProduct.map_tmul]
    show _ = (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)
    rw [algebraMap_F_coe]
  show κ.symm.mapMatrix (ψ (ι _)) = _
  rw [e1]
  erw [hh]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]
  split_ifs <;> simp [RingEquiv.symm_apply_apply]

end GlobalTheory.UPel.HT.Gen.SplitAE
