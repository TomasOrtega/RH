import ReciprocityTheory.DualLattices.ThetaQSurj

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hdet hbasis τ N z hN hNsq hz`. Establish `hv : v.Integers R` using `hS.integers`. Establish `hinj : Function.Injective (algebraMap R C)` using `hv.hom_inj`. Establish `hsqle : sqIdeal (augIdeal H.AA.carrier) ≤ augIdeal H.AA.carrier`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `h ⟨f, hf, f', hf', rfl⟩`. Rewrite using `[SetLike.mem_coe]`. Take `⟨hfA, hf0⟩` from `Submodule.mem_inf.1 hf`. Take `⟨hfA', -⟩` from `Submodule.mem_inf.1 hf'`. Use `Submodule.mem_inf.2 ⟨H.AA.mul_mem f f' hfA hfA', ?_⟩` and prove the remaining obligations.

Rewrite `hf0`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [LinearMap.proj_apply, Pi.mul_apply] at hf0 ⊢`. Rewrite using `[hf0, zero_mul]`. Establish `hkill : ∀ k, D.κ k ≠ τ → thetaQ U τ (H.φ ⟨xL D k, D.x_mem k⟩) = 0`. Introduce `k hk`.

Take `⟨l, hl⟩` from `Submodule.Quotient.mk_surjective _ (H.φ ⟨xL D k, D.x_mem k⟩)`. Establish `hg` using `phi_x_grade hS D k τ (Ne.symm hk) l hl.symm`. Take `⟨w', hw'⟩` from `(mem_pP _).1 hg`. Rewrite using `[← hl]`. Express the relevant statement in the definitionally equal form `redP (U.r τ) (thetaL U τ l) = 0`.

Establish `hl_sum : ∑ i, (U.εL i)ᵀ *ᵥ l = l`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul]`.

Establish `h1 : ∀ k', ∑ i, U.εL i k' j = (1 : Matrix (Fin g) (Fin g) R) k' j` using `fun k' => by`. Rewrite using `[← U.εL_sum, Matrix.sum_apply]`. Simplify using `[h1, Matrix.one_apply]`. Establish `hθ : thetaL U τ l = (p : R) • thetaL U τ w'`. Rewrite using `[← hl_sum, map_sum, Finset.sum_eq_single τ (fun i _ hi => theta_kill U hi l) (by simp), hw', map_smul]`.

Rewrite using `[hθ]`. Conclude with `redP_pP ((mem_pP _).2 ⟨_, rfl⟩)`. Establish `hsx : ∀ d : Ix g → R, sumX D d = ∑ k, d k • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier)`. Introduce `d`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[sumX]`. Set `π : (blockL D τ ⧸ N.comap (blockL D τ).subtype) →ₗ[R] (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)})` to `(N.comap (blockL D τ).subtype).liftQ (thetaQ U τ ∘ₗ H.φ ∘ₗ sumX D ∘ₗ (blockL D τ).subtype) (by`. Introduce `c hc`. Rewrite `hc` using `[Submodule.mem_comap, Submodule.subtype_apply]`. Take `⟨f, hf, hfc⟩` from `hNsq _ hc`.

Take `⟨c', hc', hsub⟩` from `sub_lin_mem_sq hv D hdet hbasis (hsqle hf)`. Establish `hcc : c' = (c : Ix g → R)` using `funext fun k => hinj ((hc' k).trans (hfc k).symm)`. Rewrite `hsub` using `[hcc]`. Establish `hmem : sumX D (c : Ix g → R) ∈ LinearMap.ker H.φ`. Rewrite using `[H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]`.

Establish `h2` using `Submodule.sub_mem _ hf hsub`. Rewrite `h2` using `[sub_sub_cancel]`. Simplify `h2` using `[sumX]`. Rewrite `hmem`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, hmem, map_zero])`.

Establish `hsurj : Function.Surjective π`. Introduce `w`. Take `⟨y, rfl⟩` from `thetaQ_surj U τ w`. Take `⟨f, rfl⟩` from `H.cotangent_surjective y`. Take `⟨c0, -, hsub0⟩` from `sub_lin_mem_sq hv D hdet hbasis f.2`.

Set `c : blockL D τ` to `⟨fun k => if D.κ k = τ then c0 k else 0, fun k hk => by simp [hk]⟩`. Use `⟨Submodule.Quotient.mk c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `thetaQ U τ (H.φ (sumX D (c : Ix g → R))) = thetaQ U τ (H.φ f)`. Establish `hf0 : H.φ f = H.φ (sumX D c0)`. Rewrite using `[← sub_eq_zero, ← map_sub]`.

Apply `LinearMap.mem_ker.1` to reduce the goal to its premises. Rewrite using `[H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]`. Simplify `hsub0` using `[sumX]`. Rewrite using `[hf0]`. Establish `hzero : thetaQ U τ (H.φ (sumX D (c0 - (c : Ix g → R)))) = 0`.

Rewrite using `[hsx, map_sum, map_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[map_smul, map_smul]`. Distinguish the cases in `hk : D.κ k = τ`.

Establish `hck : (c0 - (c : Ix g → R)) k = 0` using `by simp [c, hk]`. Rewrite using `[hck, zero_smul]`. Rewrite using `[hkill k hk, smul_zero]`. Rewrite `hzero` using `[map_sub, map_sub, map_sub, sub_eq_zero]`. Conclude with `hzero.symm`.

Conclude with `hasLen_le_of_surj hv hz (p : R) (U.r τ) π hsurj`.
-/
theorem u7F3 : FrobeniusLengthBoundStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hdet hbasis τ N z hN hNsq hz
  have hv : v.Integers R := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj

  have hsqle : sqIdeal (augIdeal H.AA.carrier) ≤ augIdeal H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro h ⟨f, hf, f', hf', rfl⟩
    rw [SetLike.mem_coe]
    obtain ⟨hfA, hf0⟩ := Submodule.mem_inf.1 hf
    obtain ⟨hfA', -⟩ := Submodule.mem_inf.1 hf'
    refine Submodule.mem_inf.2 ⟨H.AA.mul_mem f f' hfA hfA', ?_⟩
    rw [LinearMap.mem_ker] at hf0 ⊢
    simp only [LinearMap.proj_apply, Pi.mul_apply] at hf0 ⊢
    rw [hf0, zero_mul]

  have hkill : ∀ k, D.κ k ≠ τ → thetaQ U τ (H.φ ⟨xL D k, D.x_mem k⟩) = 0 := by
    intro k hk
    obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (H.φ ⟨xL D k, D.x_mem k⟩)
    have hg := phi_x_grade hS D k τ (Ne.symm hk) l hl.symm
    obtain ⟨w', hw'⟩ := (mem_pP _).1 hg
    rw [← hl]
    change redP (U.r τ) (thetaL U τ l) = 0
    have hl_sum : ∑ i, (U.εL i)ᵀ *ᵥ l = l := by
      funext j
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      have h1 : ∀ k', ∑ i, U.εL i k' j = (1 : Matrix (Fin g) (Fin g) R) k' j := fun k' => by
        rw [← U.εL_sum, Matrix.sum_apply]
      simp [h1, Matrix.one_apply]
    have hθ : thetaL U τ l = (p : R) • thetaL U τ w' := by
      rw [← hl_sum, map_sum,
        Finset.sum_eq_single τ (fun i _ hi => theta_kill U hi l) (by simp), hw', map_smul]
    rw [hθ]
    exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩)
  have hsx : ∀ d : Ix g → R,
      sumX D d = ∑ k, d k • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) := by
    intro d
    apply Subtype.ext
    simp [sumX]
  let π : (blockL D τ ⧸ N.comap (blockL D τ).subtype) →ₗ[R]
      (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
    (N.comap (blockL D τ).subtype).liftQ
      (thetaQ U τ ∘ₗ H.φ ∘ₗ sumX D ∘ₗ (blockL D τ).subtype) (by
        intro c hc
        rw [Submodule.mem_comap, Submodule.subtype_apply] at hc
        obtain ⟨f, hf, hfc⟩ := hNsq _ hc
        obtain ⟨c', hc', hsub⟩ := sub_lin_mem_sq hv D hdet hbasis (hsqle hf)
        have hcc : c' = (c : Ix g → R) := funext fun k => hinj ((hc' k).trans (hfc k).symm)
        rw [hcc] at hsub
        have hmem : sumX D (c : Ix g → R) ∈ LinearMap.ker H.φ := by
          rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
          have h2 := Submodule.sub_mem _ hf hsub
          rw [sub_sub_cancel] at h2
          simpa [sumX] using h2
        rw [LinearMap.mem_ker] at hmem ⊢
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, hmem, map_zero])
  have hsurj : Function.Surjective π := by
    intro w
    obtain ⟨y, rfl⟩ := thetaQ_surj U τ w
    obtain ⟨f, rfl⟩ := H.cotangent_surjective y
    obtain ⟨c0, -, hsub0⟩ := sub_lin_mem_sq hv D hdet hbasis f.2
    let c : blockL D τ :=
      ⟨fun k => if D.κ k = τ then c0 k else 0, fun k hk => by simp [hk]⟩
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    change thetaQ U τ (H.φ (sumX D (c : Ix g → R))) = thetaQ U τ (H.φ f)
    have hf0 : H.φ f = H.φ (sumX D c0) := by
      rw [← sub_eq_zero, ← map_sub]
      apply LinearMap.mem_ker.1
      rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
      simpa [sumX] using hsub0
    rw [hf0]
    have hzero : thetaQ U τ (H.φ (sumX D (c0 - (c : Ix g → R)))) = 0 := by
      rw [hsx, map_sum, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_smul, map_smul]
      by_cases hk : D.κ k = τ
      · have hck : (c0 - (c : Ix g → R)) k = 0 := by simp [c, hk]
        rw [hck, zero_smul]
      · rw [hkill k hk, smul_zero]
    rw [map_sub, map_sub, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  exact hasLen_le_of_surj hv hz (p : R) (U.r τ) π hsurj

end ReciprocityTheory.PGsh.Up
