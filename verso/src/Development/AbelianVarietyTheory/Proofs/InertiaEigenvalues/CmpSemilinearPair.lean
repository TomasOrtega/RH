import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hC μ hμ hL σA σW σB h F lam Γ h1 h2 h3 h4 h5`. Establish `hmapB : ∀ (r : OB l O) (z : TW (OB l O) T), TensorProduct.map σB.toLinearMap h (r • z) = σB r • TensorProduct.map σB.toLinearMap h z`. Introduce `r z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [smul_zero, map_zero]`.

Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`. Consider the case `tmul b x => simp [TensorProduct.smul_tmul', TensorProduct.map_tmul]`. Establish `hmapW : ∀ z : TW (OA l O) T, TensorProduct.map σW.toLinearMap h (TWincl (inclO l O) T z) = TWincl (inclO l O) T (TensorProduct.map σA.toLinearMap h z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul b x => simp [TWincl, TensorProduct.map_tmul, h1]`. Establish `hmapBA : ∀ z : TW (OA l O) T, TensorProduct.map σB.toLinearMap h (TWincl (toB l O) T z) = TWincl (toB l O) T (TensorProduct.map σA.toLinearMap h z)`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul b x => simp [TWincl, TensorProduct.map_tmul, h2]`. Establish `hsmulL : ∀ (m : OA l O) (c : ι → OA l O), inclO l O m • inclL t ϖ P c = inclL t ϖ P (m • c)`.

Introduce `m c`. Rewrite using `[inclL_apply, inclL_apply, ← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `[map_mul]`.

Establish `htoB : ∀ (m : OA l O) (c : ι → OA l O), (fun k => toB l O ((m • c) k)) = toB l O m • fun k => toB l O (c k)`. Introduce `m c`. Use function extensionality and compare the values at `k`. Simplify using `[map_mul]`. Establish `key : ∀ i : ι, jB (fun k => toB l O (Γ k i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB (Pi.single i 1))`.

Introduce `i`. Use `set c : ι → OA l O := Pi.single i 1 with hc`. Establish `hcB : (fun k => toB l O (c k)) = (Pi.single i 1 : ι → OB l O)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[hc]`. Simplify using `[hc, Pi.single_apply, hk]`. Take `⟨z, hz⟩` from `hL (inclL t ϖ P c) ⟨c, rfl⟩`. Rewrite `hz` using `[hsmulL]`.

Establish `hz1 : toB l O μ • jB (Pi.single i 1) = TWincl (toB l O) T z`. Rewrite using `[← hC _ _ hz, htoB, hcB, map_smul]`. Establish `hσc : (fun k => σA ((μ • c) k)) = σA μ • c`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[hc]`. Simplify using `[hc, Pi.single_apply, hk]`. Establish `hF : I.j (inclL t ϖ P (σA μ • (Γ *ᵥ c))) = TWincl (inclO l O) T (lam • TensorProduct.map σA.toLinearMap h z)`. Rewrite using `[← Matrix.mulVec_smul, ← hσc, ← h5, map_smul, h3, hz, hmapW, GlobalTheory.Cyc.Decomp.TWincl_smul]`.

Establish `h6` using `hC _ _ hF`. Rewrite `h6` using `[htoB, GlobalTheory.Cyc.Decomp.TWincl_smul, ← hmapBA, ← hz1, hmapB, h2, map_smul]`. Establish `hΓ : (fun k => toB l O ((Γ *ᵥ c) k)) = fun k => toB l O (Γ k i)`. Use function extensionality and compare the values at `k`. Simplify using `[hc, Matrix.mulVec_single]`.

Rewrite `h6` using `[hΓ, smul_comm (toB l O lam)]`. Conclude with `((hμ.map σB).smul_left_cancel).1 h6`. Introduce `v`. Set `Pr : (ι → OB l O) → Prop` to `fun v => jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v)`. Establish `h0 : Pr 0`.

Establish `h00 : (fun i => σB ((0 : ι → OB l O) i)) = 0` using `by funext i; simp`. Simplify using `only [Pr]`. Rewrite using `[h00, Matrix.mulVec_zero, map_zero, map_zero, smul_zero]`. Establish `hadd : ∀ v w, Pr v → Pr w → Pr (v + w)`. Introduce `v w hv hw`.

Simplify using `only [Pr] at hv hw ⊢`. Establish `: (fun i => σB ((v + w) i)) = (fun i => σB (v i)) + fun i => σB (w i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.mulVec_add, map_add, hv, hw, map_add, map_add, smul_add]`.

Establish `hsm : ∀ (r : OB l O) v, Pr v → Pr (r • v)`. Introduce `r v hv`. Simplify using `only [Pr] at hv ⊢`. Establish `: (fun i => σB ((r • v) i)) = σB r • fun i => σB (v i)`. Use function extensionality and compare the values at `i`.

Simplify using `[map_mul]`. Rewrite using `[this]`. Rewrite using `[Matrix.mulVec_smul]`. Rewrite using `[map_smul, hv, map_smul, hmapB]`. Rewrite using `[smul_smul, smul_smul, mul_comm]`.

Establish `hbas : ∀ i, Pr (Pi.single i 1)`. Introduce `i`. Simplify using `only [Pr]`. Establish `: (fun k => σB ((Pi.single i 1 : ι → OB l O) k)) = Pi.single i 1`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Rewrite using `[this, Matrix.mulVec_single]`.

Use `key i using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `hv : v = ∑ i, v i • (Pi.single i 1 : ι → OB l O)`. Use function extensionality and compare the values at `k`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `Finset.sum_induction (s := Finset.univ) (fun i => v i • (Pi.single i 1 : ι → OB l O)) Pr hadd h0 (fun i _ => hsm _ _ (hbas i))` as an intermediate fact. Rewrite `this` using `[← hv]`. Conclude with `this`.
-/
theorem cmp_semilinear_pair : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (μ : OA l O), IsUnit (toB l O μ) → (∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O μ • v) = TWincl (inclO l O) T z) → ∀ (σA : OA l O →ₐ[O] OA l O) (σW : OW l O →ₐ[O] OW l O) (σB : OB l O →ₐ[O] OB l O) (h : ↥T.L.T →ₗ[O] ↥T.L.T) (F : (ι → OW l O) →ₗ[O] (ι → OW l O)) (lam : OA l O) (Γ : Matrix ι ι (OA l O)), (∀ x, inclO l O (σA x) = σW (inclO l O x)) → (∀ x, toB l O (σA x) = σB (toB l O x)) → (∀ v, I.j (F v) = TensorProduct.map σW.toLinearMap h (I.j v)) → (∀ (r : OW l O) v, F (r • v) = σW r • F v) → (∀ c, inclO l O lam • F (inclL t ϖ P c) = inclL t ϖ P (Γ *ᵥ fun i => σA (c i))) → ∀ v : ι → OB l O, jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hC μ hμ hL σA σW σB h F lam Γ h1 h2 h3 h4 h5

  have hmapB : ∀ (r : OB l O) (z : TW (OB l O) T),
      TensorProduct.map σB.toLinearMap h (r • z) = σB r • TensorProduct.map σB.toLinearMap h z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul b x => simp [TensorProduct.smul_tmul', TensorProduct.map_tmul]
  have hmapW : ∀ z : TW (OA l O) T, TensorProduct.map σW.toLinearMap h (TWincl (inclO l O) T z) =
      TWincl (inclO l O) T (TensorProduct.map σA.toLinearMap h z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x => simp [TWincl, TensorProduct.map_tmul, h1]
  have hmapBA : ∀ z : TW (OA l O) T, TensorProduct.map σB.toLinearMap h (TWincl (toB l O) T z) =
      TWincl (toB l O) T (TensorProduct.map σA.toLinearMap h z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x => simp [TWincl, TensorProduct.map_tmul, h2]
  have hsmulL : ∀ (m : OA l O) (c : ι → OA l O), inclO l O m • inclL t ϖ P c = inclL t ϖ P (m • c) := by
    intro m c
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext k
    simp [map_mul]
  have htoB : ∀ (m : OA l O) (c : ι → OA l O), (fun k => toB l O ((m • c) k)) = toB l O m • fun k => toB l O (c k) := by
    intro m c; funext k; simp [map_mul]

  have key : ∀ i : ι, jB (fun k => toB l O (Γ k i)) =
      toB l O lam • TensorProduct.map σB.toLinearMap h (jB (Pi.single i 1)) := by
    intro i
    set c : ι → OA l O := Pi.single i 1 with hc
    have hcB : (fun k => toB l O (c k)) = (Pi.single i 1 : ι → OB l O) := by
      funext k; by_cases hk : k = i
      · subst hk; simp [hc]
      · simp [hc, Pi.single_apply, hk]
    obtain ⟨z, hz⟩ := hL (inclL t ϖ P c) ⟨c, rfl⟩
    rw [hsmulL] at hz
    have hz1 : toB l O μ • jB (Pi.single i 1) = TWincl (toB l O) T z := by
      rw [← hC _ _ hz, htoB, hcB, map_smul]
    have hσc : (fun k => σA ((μ • c) k)) = σA μ • c := by
      funext k; by_cases hk : k = i
      · subst hk; simp [hc]
      · simp [hc, Pi.single_apply, hk]
    have hF : I.j (inclL t ϖ P (σA μ • (Γ *ᵥ c))) =
        TWincl (inclO l O) T (lam • TensorProduct.map σA.toLinearMap h z) := by
      rw [← Matrix.mulVec_smul, ← hσc, ← h5, map_smul, h3, hz, hmapW, GlobalTheory.Cyc.Decomp.TWincl_smul]
    have h6 := hC _ _ hF
    rw [htoB, GlobalTheory.Cyc.Decomp.TWincl_smul, ← hmapBA, ← hz1, hmapB, h2, map_smul] at h6
    have hΓ : (fun k => toB l O ((Γ *ᵥ c) k)) = fun k => toB l O (Γ k i) := by
      funext k; simp [hc, Matrix.mulVec_single]
    rw [hΓ, smul_comm (toB l O lam)] at h6
    exact ((hμ.map σB).smul_left_cancel).1 h6
  intro v
  let Pr : (ι → OB l O) → Prop := fun v =>
    jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v)
  have h0 : Pr 0 := by
    have h00 : (fun i => σB ((0 : ι → OB l O) i)) = 0 := by funext i; simp
    simp only [Pr]
    rw [h00, Matrix.mulVec_zero, map_zero, map_zero, smul_zero]
  have hadd : ∀ v w, Pr v → Pr w → Pr (v + w) := by
    intro v w hv hw
    simp only [Pr] at hv hw ⊢
    have : (fun i => σB ((v + w) i)) = (fun i => σB (v i)) + fun i => σB (w i) := by
      funext i; simp
    rw [this, Matrix.mulVec_add, map_add, hv, hw, map_add, map_add, smul_add]
  have hsm : ∀ (r : OB l O) v, Pr v → Pr (r • v) := by
    intro r v hv
    simp only [Pr] at hv ⊢
    have : (fun i => σB ((r • v) i)) = σB r • fun i => σB (v i) := by
      funext i; simp [map_mul]
    rw [this]
    rw [Matrix.mulVec_smul]
    rw [map_smul, hv, map_smul, hmapB]
    rw [smul_smul, smul_smul, mul_comm]
  have hbas : ∀ i, Pr (Pi.single i 1) := by
    intro i
    simp only [Pr]
    have : (fun k => σB ((Pi.single i 1 : ι → OB l O) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [this, Matrix.mulVec_single]
    convert key i using 2
    funext k; simp
  have hv : v = ∑ i, v i • (Pi.single i 1 : ι → OB l O) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  have := Finset.sum_induction (s := Finset.univ) (fun i => v i • (Pi.single i 1 : ι → OB l O)) Pr hadd h0
    (fun i _ => hsm _ _ (hbas i))
  rw [← hv] at this
  exact this

end GlobalTheory.BKGal
