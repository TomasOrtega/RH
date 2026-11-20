import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

/- English proof (translation)
Introduce `n ι _ _ Φ hΦ S v B F hF hS`. Use `choose Q hQ using hΦ.poly`. Set `M : ℂ → Matrix (Fin n) (Fin n) ℂ` to `fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)`. Set `x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ` to `fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)`. Set `g : ℂ → ι → ℂ` to `fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j`.

Establish `hMc : Continuous M` using `by fun_prop`. Establish `hdetB : IsUnit (B.val).det` using `(Matrix.isUnit_iff_isUnit_det _).1 B.isUnit`. Establish `hM0 : M 0 = B.val` using `by simp [M]`. Establish `hinvc : ContinuousAt (fun s => (M s)⁻¹) 0`. Establish `h1 : ContinuousAt Inv.inv (M 0)`.

Apply `continuousAt_matrix_inv` to reduce the goal to its premises. Rewrite using `[hM0]`. Conclude with `NormedRing.inverse_continuousAt hdetB.unit`. Conclude with `h1.comp hMc.continuousAt`. Establish `hxc : ContinuousAt x 0`.

Rewrite using `[continuousAt_pi]`. Introduce and unpack `(p | p)`. Conclude with `((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt`. Conclude with `((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc`. Establish `hgc : ContinuousAt g 0`.

Rewrite using `[continuousAt_pi]`. Introduce `i`. Apply `tendsto_finset_sum` to reduce the goal to its premises. Introduce `j _`. Conclude with `(((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const`.

Establish `hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v`. Introduce `s C hC`. Use function extensionality and compare the values at `i`. Simplify using `only [g, Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hQ i j C]`. Establish `hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2)`. Use function extensionality and compare the values at `q`. Break down `q with p | p` into its components or cases. Simplify using `[x, hC]`.

Simplify using `[x, Matrix.coe_units_inv, hC]`. Rewrite using `[hx]`. Establish `hg0 : g 0 = Φ B *ᵥ v` using `hgC 0 B hM0.symm`. Establish `hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det`. Establish `hc : ContinuousAt (fun s => (M s).det) 0` using `hMc.matrix_det.continuousAt`.

Establish `: IsOpen {z : ℂ | z ≠ 0}` using `isOpen_ne`. Establish `hne : (M 0).det ≠ 0` using `by rw [hM0]; exact hdetB.ne_zero`. Use `filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs`. Conclude with `isUnit_iff_ne_zero.2 hs`. Establish `hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F`.

Establish `hcl : IsClosed (F \ {0})` using `(hF.diff).isClosed`. Establish `hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ)` using `hcl.isOpen_compl.mem_nhds (by simp)`. Use `filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2`. Introduce `hsF`. Conclude with `hs1 ⟨hsF, hs2⟩`.

Establish `hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S` using `by filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet`. Rewrite using `[hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]`. Conclude with `hS s hs _ rfl`. Establish `ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v))`. Rewrite using `[← hg0]`.

Conclude with `hgc.tendsto.mono_left nhdsWithin_le_nhds`. Conclude with `(Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev`.
-/
theorem mulVec_mem_of_cofinite_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ)
    (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite →
    (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) →
    Φ B *ᵥ v ∈ S := by
  intro n ι _ _ Φ hΦ S v B F hF hS
  choose Q hQ using hΦ.poly
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
    fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)
  let g : ℂ → ι → ℂ := fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j
  have hMc : Continuous M := by
    fun_prop
  have hdetB : IsUnit (B.val).det := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hM0 : M 0 = B.val := by simp [M]
  have hinvc : ContinuousAt (fun s => (M s)⁻¹) 0 := by
    have h1 : ContinuousAt Inv.inv (M 0) := by
      apply continuousAt_matrix_inv
      rw [hM0]
      exact NormedRing.inverse_continuousAt hdetB.unit
    exact h1.comp hMc.continuousAt
  have hxc : ContinuousAt x 0 := by
    rw [continuousAt_pi]
    rintro (p | p)
    · exact ((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt
    · exact ((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc
  have hgc : ContinuousAt g 0 := by
    rw [continuousAt_pi]
    intro i
    apply tendsto_finset_sum
    intro j _
    exact (((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const

  have hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v := by
    intro s C hC
    funext i
    simp only [g, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ i j C]
    have hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2) := by
      funext q
      rcases q with p | p
      · simp [x, hC]
      · simp [x, Matrix.coe_units_inv, hC]
    rw [hx]
  have hg0 : g 0 = Φ B *ᵥ v := hgC 0 B hM0.symm
  have hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det := by
    have hc : ContinuousAt (fun s => (M s).det) 0 := hMc.matrix_det.continuousAt
    have : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hne : (M 0).det ≠ 0 := by rw [hM0]; exact hdetB.ne_zero
    filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs
    exact isUnit_iff_ne_zero.2 hs
  have hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F := by
    have hcl : IsClosed (F \ {0}) := (hF.diff).isClosed
    have hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2
    intro hsF
    exact hs1 ⟨hsF, hs2⟩
  have hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S := by
    filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet
    rw [hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]
    exact hS s hs _ rfl
  have ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v)) := by
    rw [← hg0]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact (Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev

end GlobalTheory.AlgWtHW
