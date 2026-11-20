import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim
open UpperTheory.Gal.W2

/- English proof (translation)
Set `jL : N →ₗ[ℤ] ℚ ⊗[ℤ] M` to `j.toIntLinearMap`. Establish `hloc : IsLocalizedModule (nonZeroDivisors ℤ) jL`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[Module.End.isUnit_iff]`.

Establish `hx : ((x : ℤ) : ℚ) ≠ 0` using `Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero x.2)`. Establish `hsm : ∀ v : ℚ ⊗[ℤ] M, (algebraMap ℤ (Module.End ℤ (ℚ ⊗[ℤ] M)) x) v = ((x : ℤ) : ℚ) • v`. Introduce `v`. Rewrite using `[Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]`. Use `⟨fun v w h => ?_, fun v => ⟨((x : ℤ) : ℚ)⁻¹ • v, ?_⟩⟩` and prove the remaining obligations.

Rewrite `h` using `[hsm, hsm]`. Conclude with `smul_right_injective _ hx h`. Rewrite using `[hsm, smul_smul, mul_inv_cancel₀ hx, one_smul]`. Introduce `w`. Take `⟨m, u, hm, h⟩` from `hs w`.

Use `⟨⟨u, ⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩⟩, ?_⟩` and prove the remaining obligations. Use `show (m : ℤ) • w = j u`. Rewrite using `[natCast_zsmul]`. Conclude with `h`. Introduce `x1 x2 h`.

Conclude with `⟨1, by rw [one_smul, one_smul]; exact hj h⟩`. Establish `hb : IsBaseChange ℚ jL` using `IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ jL`. Establish `hrank : Module.finrank ℤ N = Module.finrank ℤ M`. Rewrite using `[← Module.finrank_of_isLocalizedModule_of_free ℚ (nonZeroDivisors ℤ) jL, Module.finrank_baseChange]`. Set `e : N ≃ₗ[ℤ] M` to `LinearEquiv.ofFinrankEq N M hrank`.

Use `⟨e.toAddEquiv, (LinearEquiv.baseChange ℤ ℚ N M e).symm.trans hb.equiv, fun u => ?_⟩` and prove the remaining obligations. Establish `h1 : (LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u) = (1 : ℚ) ⊗ₜ[ℤ] u`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Use `show hb.equiv ((LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u)) = j u`.

Rewrite using `[h1, hb.equiv_tmul, one_smul]`. Both sides reduce to the same expression.
-/
private theorem exists_lattice_basis_of_rational {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (j : N →+ ℚ ⊗[ℤ] M) (hj : Function.Injective j)
    (hs : ∀ w, ∃ (m : ℕ) (u : N), m ≠ 0 ∧ m • w = j u) :
    ∃ (ψ : N ≃+ M) (T : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M)), ∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u := by
  classical
  let jL : N →ₗ[ℤ] ℚ ⊗[ℤ] M := j.toIntLinearMap
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) jL := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [Module.End.isUnit_iff]
      have hx : ((x : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero x.2)
      have hsm : ∀ v : ℚ ⊗[ℤ] M,
          (algebraMap ℤ (Module.End ℤ (ℚ ⊗[ℤ] M)) x) v = ((x : ℤ) : ℚ) • v := by
        intro v
        rw [Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
      refine ⟨fun v w h => ?_, fun v => ⟨((x : ℤ) : ℚ)⁻¹ • v, ?_⟩⟩
      · rw [hsm, hsm] at h
        exact smul_right_injective _ hx h
      · rw [hsm, smul_smul, mul_inv_cancel₀ hx, one_smul]
    · intro w
      obtain ⟨m, u, hm, h⟩ := hs w
      refine ⟨⟨u, ⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩⟩, ?_⟩
      show (m : ℤ) • w = j u
      rw [natCast_zsmul]
      exact h
    · intro x1 x2 h
      exact ⟨1, by rw [one_smul, one_smul]; exact hj h⟩
  have hb : IsBaseChange ℚ jL := IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ jL
  have hrank : Module.finrank ℤ N = Module.finrank ℤ M := by
    rw [← Module.finrank_of_isLocalizedModule_of_free ℚ (nonZeroDivisors ℤ) jL,
      Module.finrank_baseChange]
  let e : N ≃ₗ[ℤ] M := LinearEquiv.ofFinrankEq N M hrank
  refine ⟨e.toAddEquiv, (LinearEquiv.baseChange ℤ ℚ N M e).symm.trans hb.equiv, fun u => ?_⟩
  have h1 : (LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u) = (1 : ℚ) ⊗ₜ[ℤ] u := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show hb.equiv ((LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u)) = j u
  rw [h1, hb.equiv_tmul, one_smul]
  rfl

/- English proof (translation)
Introduce `p _ D G L β D' j h`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Conclude with `exists_lattice_basis_of_rational j h.1 h.2.2.1`.
-/
theorem UpperTheory.exists_rational_equiv_of_isPlace :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ} {D' : PLat D.O D.inv} {j : D'.La →+ VQ D}, IsPlace L β D' j →
        ∃ (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D), ∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u := by
  intro p _ D G L β D' j h
  haveI := D.freeLa
  haveI := D.finLa
  exact exists_lattice_basis_of_rational j h.1 h.2.2.1
