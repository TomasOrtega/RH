import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.SplitUnipFrame

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hJ r X hX hrn v t hcm B hB i g hg j`. Use `set y : GL (Fin n) (Fv F v) := B * g * B⁻¹ with hy`. Use `set x := (splitEquiv hcm hJ t).symm y with hx`. Use `set M := (matHom _ σ J x).1 with hM`. Use `set Y : Fin r → Fin n → Fv F v ⊗[F] E := fun l a => inclR (F := F) (Fv F v) (X a l) with hY`.

Establish `h1 : M.map (splitProj t) = y.1`. Use `congrArg Units.val ((splitEquiv hcm hJ t).apply_symm_apply y)` as an intermediate fact. Rewrite `this` using `[splitEquiv_val]`. Then use the resulting hypothesis. Establish `h2 : M.map (splitProj (t.comp σ)) = (dualConj (splitGram hJ t) y).1`. Rewrite using `[hM, ← splitHom_val, splitHom_comp hJ, ← splitEquiv_apply hcm hJ, hx, (splitEquiv hcm hJ t).apply_symm_apply]`.

Establish `hYt : ∀ l : Fin r, splitVec t (Y l) = fun a => B.1 a (Fin.castLE hrn l)` using `fun l =>`. Use function extensionality and compare the values at `fun a => by simp only [splitVec, hY, splitProj_inclR, hB l (Fin.castLE hrn l) rfl a]`. Establish `hYc : ∀ l : Fin r, splitVec (t.comp σ) (Y l) = fun a => t (σ (X a l))` using `fun l =>`. Use function extensionality and compare the values at `fun a => by simp only [splitVec, hY, splitProj_inclR, AlgHom.comp_apply]`. Establish `hsub : ∀ (τ : E →ₐ[F] Fv F v) (p q : Fin n → Fv F v ⊗[F] E), splitVec τ (p - q) = splitVec τ p - splitVec τ q` using `fun τ p q => funext fun _ => map_sub _ _ _`.

Establish `hsum : ∀ (τ : E →ₐ[F] Fv F v) (c : Fin r → Fv F v ⊗[F] E), splitVec τ (∑ l, c l • Y l) = ∑ l, splitProj τ (c l) • splitVec τ (Y l)` using `fun τ c => by`. Use function extensionality and compare the values at `a`. Simplify using `[splitVec, Finset.sum_apply, map_sum]`. Use `set j' : Fin n := Fin.castLE hrn j with hj'`. Use `set c : Fin r → Fv F v ⊗[F] E := fun l => (g.1 - 1) (Fin.castLE hrn l) j' • splitIdem hcm t with hc`.

Establish `key : M *ᵥ Y j - Y j = ∑ l, c l • Y l`. Apply `splitVec_ext hcm t` to reduce the goal to its premises. Rewrite using `[hsub, hsum, splitVec_mulVec, h1, hYt]`. Establish `hu : (fun a => B.1 a j') = B.1 *ᵥ Pi.single j' 1`. Use function extensionality and compare the values at `a`.

Simplify using `[Matrix.mulVec_single_one]`. Establish `hyB : y.1 * B.1 = B.1 * g.1`. Rewrite using `[hy, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`.

Establish `hcs : ∀ l, splitProj t (c l) = (g.1 - 1) (Fin.castLE hrn l) j'` using `fun l => by`. Simplify using `[hc, map_smul]`. Simplify using `only [hcs, hYt]`. Rewrite using `[hu, Matrix.mulVec_mulVec, hyB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, show g.1 *ᵥ Pi.single j' 1 - Pi.single j' (1 : Fv F v) = (g.1 - 1) *ᵥ Pi.single j' 1 by`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec], Matrix.mulVec_single_one]`.

Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hrn) (Fin.castLE_injective hrn) _ _ ?_ ?_` and prove the remaining obligations.

Introduce `k hk`. Establish `: (g.1 - 1) k j' = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hk ⟨⟨k, lt_of_le_of_lt (hg _ _ hne).1 i.2⟩, rfl⟩`. Simplify using `[this]`.

Introduce `l`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Rewrite using `[hsub, hsum, splitVec_mulVec, h2, hYc]`. Establish `hcs' : ∀ l, splitProj (t.comp σ) (c l) = 0` using `fun l => by`.

Simplify using `[hc, map_smul]`. Simplify using `only [hcs', zero_smul, Finset.sum_const_zero]`. Rewrite using `[sub_eq_zero, dualConj_val, Matrix.mulVec_transpose, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]`. Use `set u' : Fin n → Fv F v := fun a => t (σ (X a j)) with hu'`. Use `set w := u' ᵥ* (splitGram hJ t).1 with hw`.

Establish `hz0 : ∀ l : Fin n, (l : ℕ) < r → (w ᵥ* B.1) l = 0`. Introduce `l hl`. Establish `e : t ((Formalism.UG.cT (σ : E →+* E) X * J * X) j ⟨l, hl⟩) = 0` using `by rw [hX]; simp`. Rewrite using `[← e]`. Simplify using `only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hw, hu', Matrix.vecMul, dotProduct, splitGram_val, hB ⟨l, hl⟩ l rfl, RingHom.coe_coe, Finset.sum_mul]`.

Establish `hzg : (w ᵥ* B.1) ᵥ* g.1 = w ᵥ* B.1`. Establish `h0 : (w ᵥ* B.1) ᵥ* (g.1 - 1) = 0`. Use function extensionality and compare the values at `k`. Use `show ∑ l, (w ᵥ* B.1) l * (g.1 - 1) l k = 0`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : (g.1 - 1) l k = 0`. Rewrite using `[hl, mul_zero]`. Rewrite using `[hz0 l (lt_of_le_of_lt (hg l k hl).1 i.2), zero_mul]`. Rewrite `h0` using `[Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero]`. Conclude with `h0`.

Establish `hzg' : (w ᵥ* B.1) ᵥ* (g⁻¹).1 = w ᵥ* B.1` using `by conv_lhs => rw [← hzg]`. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Establish `hyi : y⁻¹ = B * (g⁻¹ * B⁻¹)` using `by rw [hy]; group`. Establish `hwy : w ᵥ* (y⁻¹).1 = w`. Rewrite using `[hyi, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hzg', Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`.

Rewrite using `[hwy, hw, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Rewrite using `[key]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : (g.1 - 1) (Fin.castLE hrn l) j' = 0`. Establish `h0 : c l = 0` using `by simp only [hc, hl, zero_smul]`.

Rewrite using `[h0, zero_smul]`. Conclude with `zero_mem _`. Take `⟨hli, hlj⟩` from `hg _ _ hl`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ⟨hlj, hli⟩, rfl⟩)`.
-/
theorem mulVec_sub_mem_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X : Matrix (Fin n) (Fin r) E), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → r ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (B : GL (Fin n) (Fv F v)),
    (∀ (j : Fin r) (k : Fin n), (k : ℕ) = j → ∀ a, B.1 a k = t (X a j)) → ∀ (i : Fin r) (g : GL (Fin n) (Fv F v)),
    (∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j) → ∀ j : Fin r,
    (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * g * B⁻¹))).1 *ᵥ (fun a => inclR (F := F) (Fv F v) (X a j)) -
        (fun a => inclR (F := F) (Fv F v) (X a j)) ∈
      Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' {l : Fin r | l < j ∧ l ≤ i}) := by
  intro F E _ _ _ _ _ σ n J hJ r X hX hrn v t hcm B hB i g hg j
  set y : GL (Fin n) (Fv F v) := B * g * B⁻¹ with hy
  set x := (splitEquiv hcm hJ t).symm y with hx
  set M := (matHom _ σ J x).1 with hM
  set Y : Fin r → Fin n → Fv F v ⊗[F] E := fun l a => inclR (F := F) (Fv F v) (X a l) with hY
  have h1 : M.map (splitProj t) = y.1 := by
    have := congrArg Units.val ((splitEquiv hcm hJ t).apply_symm_apply y)
    rwa [splitEquiv_val] at this
  have h2 : M.map (splitProj (t.comp σ)) = (dualConj (splitGram hJ t) y).1 := by
    rw [hM, ← splitHom_val, splitHom_comp hJ, ← splitEquiv_apply hcm hJ, hx,
      (splitEquiv hcm hJ t).apply_symm_apply]
  have hYt : ∀ l : Fin r, splitVec t (Y l) = fun a => B.1 a (Fin.castLE hrn l) := fun l =>
    funext fun a => by simp only [splitVec, hY, splitProj_inclR, hB l (Fin.castLE hrn l) rfl a]
  have hYc : ∀ l : Fin r, splitVec (t.comp σ) (Y l) = fun a => t (σ (X a l)) := fun l =>
    funext fun a => by simp only [splitVec, hY, splitProj_inclR, AlgHom.comp_apply]
  have hsub : ∀ (τ : E →ₐ[F] Fv F v) (p q : Fin n → Fv F v ⊗[F] E),
      splitVec τ (p - q) = splitVec τ p - splitVec τ q := fun τ p q => funext fun _ => map_sub _ _ _
  have hsum : ∀ (τ : E →ₐ[F] Fv F v) (c : Fin r → Fv F v ⊗[F] E),
      splitVec τ (∑ l, c l • Y l) = ∑ l, splitProj τ (c l) • splitVec τ (Y l) := fun τ c => by
    funext a
    simp [splitVec, Finset.sum_apply, map_sum]
  set j' : Fin n := Fin.castLE hrn j with hj'
  set c : Fin r → Fv F v ⊗[F] E := fun l => (g.1 - 1) (Fin.castLE hrn l) j' • splitIdem hcm t with hc
  have key : M *ᵥ Y j - Y j = ∑ l, c l • Y l := by
    apply splitVec_ext hcm t
    · rw [hsub, hsum, splitVec_mulVec, h1, hYt]
      have hu : (fun a => B.1 a j') = B.1 *ᵥ Pi.single j' 1 := by
        funext a; simp [Matrix.mulVec_single_one]
      have hyB : y.1 * B.1 = B.1 * g.1 := by
        rw [hy, ← Units.val_mul, ← Units.val_mul]; congr 1; group
      have hcs : ∀ l, splitProj t (c l) = (g.1 - 1) (Fin.castLE hrn l) j' := fun l => by
        simp [hc, map_smul]
      simp only [hcs, hYt]
      rw [hu, Matrix.mulVec_mulVec, hyB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub,
        show g.1 *ᵥ Pi.single j' 1 - Pi.single j' (1 : Fv F v) = (g.1 - 1) *ᵥ Pi.single j' 1 by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec], Matrix.mulVec_single_one]
      funext a
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      symm
      refine Fintype.sum_of_injective (Fin.castLE hrn) (Fin.castLE_injective hrn) _ _ ?_ ?_
      · intro k hk
        have : (g.1 - 1) k j' = 0 := by
          by_contra hne
          exact hk ⟨⟨k, lt_of_le_of_lt (hg _ _ hne).1 i.2⟩, rfl⟩
        simp [this]
      · intro l; rw [mul_comm]; rfl
    · rw [hsub, hsum, splitVec_mulVec, h2, hYc]
      have hcs' : ∀ l, splitProj (t.comp σ) (c l) = 0 := fun l => by
        simp [hc, map_smul]
      simp only [hcs', zero_smul, Finset.sum_const_zero]
      rw [sub_eq_zero, dualConj_val, Matrix.mulVec_transpose, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      set u' : Fin n → Fv F v := fun a => t (σ (X a j)) with hu'
      set w := u' ᵥ* (splitGram hJ t).1 with hw
      have hz0 : ∀ l : Fin n, (l : ℕ) < r → (w ᵥ* B.1) l = 0 := by
        intro l hl
        have e : t ((Formalism.UG.cT (σ : E →+* E) X * J * X) j ⟨l, hl⟩) = 0 := by rw [hX]; simp
        rw [← e]
        simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hw, hu',
          Matrix.vecMul, dotProduct, splitGram_val, hB ⟨l, hl⟩ l rfl, RingHom.coe_coe, Finset.sum_mul]
      have hzg : (w ᵥ* B.1) ᵥ* g.1 = w ᵥ* B.1 := by
        have h0 : (w ᵥ* B.1) ᵥ* (g.1 - 1) = 0 := by
          funext k
          show ∑ l, (w ᵥ* B.1) l * (g.1 - 1) l k = 0
          refine Finset.sum_eq_zero fun l _ => ?_
          by_cases hl : (g.1 - 1) l k = 0
          · rw [hl, mul_zero]
          · rw [hz0 l (lt_of_le_of_lt (hg l k hl).1 i.2), zero_mul]
        rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at h0
        exact h0
      have hzg' : (w ᵥ* B.1) ᵥ* (g⁻¹).1 = w ᵥ* B.1 := by
        conv_lhs => rw [← hzg]
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
      have hyi : y⁻¹ = B * (g⁻¹ * B⁻¹) := by rw [hy]; group
      have hwy : w ᵥ* (y⁻¹).1 = w := by
        rw [hyi, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hzg',
          Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
      rw [hwy, hw, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  rw [key]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : (g.1 - 1) (Fin.castLE hrn l) j' = 0
  · have h0 : c l = 0 := by simp only [hc, hl, zero_smul]
    rw [h0, zero_smul]
    exact zero_mem _
  · obtain ⟨hli, hlj⟩ := hg _ _ hl
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ⟨hlj, hli⟩, rfl⟩)

end GlobalTheory.SplitUnipFrame
