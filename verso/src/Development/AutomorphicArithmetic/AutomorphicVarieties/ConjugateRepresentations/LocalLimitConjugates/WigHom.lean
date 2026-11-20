import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HomId

section SlopeTestRemainingChoices
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

private def UpperTheory.V.Cj.H.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add, AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

/- English proof (translation)
Introduce `E _ _ _ a M _ _ _ _ L α z hlie hretr`. Use `⟨fun ω h0 h1 Y => ?_, fun q ω h0 h1 => ?_⟩` and prove the remaining obligations. Establish `key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0`. Introduce `X`. Set `Z : Matrix (Fin a) (Fin a) (Cinf E)` to `(1 / 2 : ℝ) • (X - star X)`.

Establish `hZ : star Z = -Z`. Simplify using `only [Z]`. Rewrite using `[star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]`. Establish `hX : toL X = toL (hp (toL X)).1 + toL Z`. Establish `h : X = (hp (toL X)).1 + Z`.

Rewrite using `[hp_val]`. Simplify using `only [Z]`. Use `module`. Conclude with `congrArg toL h`. Establish `h3` using `DFunLike.congr_fun h1 fun _ => hp (toL X)`.

Rewrite `h3` using `[dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y]`. Establish `h4 : L (toL (hp (toL X)).1) (ω Y) = 0` using `by simpa using h3`. Rewrite using `[congrArg L hX, map_add, LinearMap.add_apply, h4, h0 Z hZ Y]`. Simplify using the standard rewrite rules. Rewrite using `[← hretr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero]`.

Set `F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M)` to `UpperTheory.V.Cj.H.altFlip (ω.curryLeft ∘ₗ hp)`. Set `ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a` to `fun Y => { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y) map_add' := fun X X' => by`. Establish `h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y = (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y)` using `by noncomm_ring`. Conclude with `congrArg toL h`. Use the proof step `map_smul' := fun c X => by`.

Establish `h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y)`. Rewrite using `[smul_sub, mul_smul_comm, smul_mul_assoc]`. Conclude with `congrArg toL h }`. Use `⟨α.compAlternatingMap F, fun Y => ?_⟩` and prove the remaining obligations. Set `G : Fin (q + 1) → Lie E a →ₗ[ℝ] M` to `fun i => (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1`.

Establish `h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i)` using `fun i => hlie _ _ _ fun X => (sub_add_cancel _ _).symm`. Rewrite using `[dCo_apply, ← hretr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← h3]`. Both sides reduce to the same expression.

Rewrite using `[LinearMap.sum_apply]`. Conclude with `homId E a M L q ω h1 h0 (Matrix.of X) Y`.
-/
private theorem UpperTheory.V.Cj.H.wigner_homomorphism : UpperTheory.V.Cj.H.WigHom := by
  intro E _ _ _ a M _ _ _ _ L α z hlie hretr
  refine ⟨fun ω h0 h1 Y => ?_, fun q ω h0 h1 => ?_⟩
  · have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add, LinearMap.add_apply, h4, h0 Z hZ Y]
      simp
    rw [← hretr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := UpperTheory.V.Cj.H.altFlip (ω.curryLeft ∘ₗ hp)
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine ⟨α.compAlternatingMap F, fun Y => ?_⟩
    let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
      (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
    have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
      hlie _ _ _ fun X => (sub_add_cancel _ _).symm
    rw [dCo_apply, ← hretr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← h3]
      rfl
    · rw [LinearMap.sum_apply]
      exact homId E a M L q ω h1 h0 (Matrix.of X) Y

end SlopeTestRemainingChoices

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
The claim follows from `UpperTheory.V.Cj.H.wigner_homomorphism`.
-/
theorem UpperTheory.V.Cj.H.wigHom :
    UpperTheory.V.Cj.H.WigHom :=
  UpperTheory.V.Cj.H.wigner_homomorphism
