import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HomId
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def UpperTheory.V.AlgRepEndIrreducible.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add, AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

/- English proof (translation)
Introduce `E _ _ _ a M _ _ _ _ κ L α hα hinf`. Introduce and unpack `(⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)`. Use `h2 (AlternatingMap.ext fun Y => ?_)` and prove the remaining obligations. Establish `key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0`. Introduce `X`.

Set `Z : Matrix (Fin a) (Fin a) (Cinf E)` to `(1 / 2 : ℝ) • (X - star X)`. Establish `hZ : star Z = -Z`. Simplify using `only [Z]`. Rewrite using `[star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]`. Establish `hX : toL X = toL (hp (toL X)).1 + toL Z`.

Establish `h : X = (hp (toL X)).1 + Z`. Rewrite using `[hp_val]`. Simplify using `only [Z]`. Use `module`. Conclude with `congrArg toL h`.

Establish `h3` using `DFunLike.congr_fun h1 fun _ => hp (toL X)`. Rewrite `h3` using `[dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y]`. Establish `h4 : L (toL (hp (toL X)).1) (ω Y) = 0` using `by simpa using h3`. Rewrite using `[congrArg L hX, map_add, LinearMap.add_apply, h4, hinf 0 ω h0 Z hZ Y]`. Simplify using the standard rewrite rules.

Rewrite using `[← hα.retr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero, AlternatingMap.zero_apply]`. Set `F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M)` to `altFlip (ω.curryLeft ∘ₗ hp)`. Establish `hF : ∀ Y X, F Y X = ω (Matrix.vecCons (hp X) Y)` using `fun _ _ => rfl`. Set `ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a` to `fun Y => { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y) map_add' := fun X X' => by`. Establish `h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y = (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y)` using `by noncomm_ring`.

Conclude with `congrArg toL h`. Use the proof step `map_smul' := fun c X => by`. Establish `h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y)`. Rewrite using `[smul_sub, mul_smul_comm, smul_mul_assoc]`. Conclude with `congrArg toL h }`.

Use `h2 (α.compAlternatingMap F) (fun k Y => ?_) (AlternatingMap.ext fun Y => ?_)` and prove the remaining obligations. Use `(hα.cpt k (F Y) (F fun i => adHerm k (Y i)) fun X => ?_).symm` and prove the remaining obligations. Establish `e : hp (toL (k.1 * X * star k.1)) = adHerm k (hp (toL X))`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ = k.1 * (hp (toL X)).1 * star k.1`.

Rewrite using `[hp_val, hp_val, star_mul, star_mul, star_star, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc k.1 (star X)]`. Rewrite using `[hF, hF, ← h0, e]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp`.

Set `G : Fin (q + 1) → Lie E a →ₗ[ℝ] M` to `fun i => (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1`. Establish `h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i)` using `fun i => hα.lie _ _ _ fun X => (sub_add_cancel _ _).symm`. Rewrite using `[dCo_apply, ← hα.retr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← h3]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.sum_apply]`. Conclude with `homId E a M L q ω h1 (hinf _ ω h0) (Matrix.of X) Y`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.homot :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M),
      IsRetr κ L α → (∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω) → ¬ HasCohomology κ L := by
  intro E _ _ _ a M _ _ _ _ κ L α hα hinf
  rintro (⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)
  · refine h2 (AlternatingMap.ext fun Y => ?_)
    have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
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
      rw [congrArg L hX, map_add, LinearMap.add_apply, h4, hinf 0 ω h0 Z hZ Y]
      simp
    rw [← hα.retr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero, AlternatingMap.zero_apply]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := altFlip (ω.curryLeft ∘ₗ hp)
    have hF : ∀ Y X, F Y X = ω (Matrix.vecCons (hp X) Y) := fun _ _ => rfl
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
    refine h2 (α.compAlternatingMap F) (fun k Y => ?_) (AlternatingMap.ext fun Y => ?_)
    · refine (hα.cpt k (F Y) (F fun i => adHerm k (Y i)) fun X => ?_).symm
      have e : hp (toL (k.1 * X * star k.1)) = adHerm k (hp (toL X)) := by
        apply Subtype.ext
        change _ = k.1 * (hp (toL X)).1 * star k.1
        rw [hp_val, hp_val, star_mul, star_mul, star_star, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
          mul_assoc k.1 (star X)]
      rw [hF, hF, ← h0, e]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    · let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
        (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
      have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
        hα.lie _ _ _ fun X => (sub_add_cancel _ _).symm
      rw [dCo_apply, ← hα.retr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, ← h3]
        rfl
      · rw [LinearMap.sum_apply]
        exact homId E a M L q ω h1 (hinf _ ω h0) (Matrix.of X) Y
