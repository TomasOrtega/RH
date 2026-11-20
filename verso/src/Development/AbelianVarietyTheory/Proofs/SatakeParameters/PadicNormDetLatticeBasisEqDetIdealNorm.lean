import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne

noncomputable section

namespace GlobalTheory.DetBasisNorm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Establish `hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]`.

Rewrite using `[hs, one_mul]`. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _`.
-/
theorem norm_det_le_one {p : ℕ} [Fact p.Prime] {N : ℕ} {C : Matrix (Fin N) (Fin N) ℂ_[p]}
    (h : ∀ a b, ‖C a b‖ ≤ 1) : ‖C.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [hs, one_mul]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _

/- English proof (translation)
Use `hA (Pi.single b 1) ((h₀ _).2 fun k => by` as an intermediate fact. Distinguish the cases in `hk : k = b`. Substitute `hk` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero)` using `[Pi.single_eq_of_ne hk]`.

Rewrite `this` using `[Matrix.mulVec_single_one]`. Then use the resulting hypothesis.
-/
theorem col_mem {E : Type} [Field E] {N : ℕ} {L₀ L : Submodule (𝓞 E) (Fin N → E)}
    (h₀ : ∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) {A : Matrix (Fin N) (Fin N) E}
    (hA : ∀ v ∈ L₀, A.mulVec v ∈ L) (b : Fin N) : (fun i => A i b) ∈ L := by
  have := hA (Pi.single b 1) ((h₀ _).2 fun k => by
    by_cases hk : k = b
    · subst hk; simpa using isIntegral_one
    · simpa [Pi.single_eq_of_ne hk] using isIntegral_zero)
  rwa [Matrix.mulVec_single_one] at this

/- English proof (translation)
Introduce `v hv`. Establish `e : A.mulVec v = ∑ b, (⟨v b, (h₀ v).1 hv b⟩ : 𝓞 E) • (fun i => A i b)`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = v b * A i b`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hA b)`.
-/
theorem mulVec_mem {E : Type} [Field E] {N : ℕ} {L₀ L : Submodule (𝓞 E) (Fin N → E)}
    (h₀ : ∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) {A : Matrix (Fin N) (Fin N) E}
    (hA : ∀ b, (fun i => A i b) ∈ L) : ∀ v ∈ L₀, A.mulVec v ∈ L := by
  intro v hv
  have e : A.mulVec v = ∑ b, (⟨v b, (h₀ v).1 hv b⟩ : 𝓞 E) • (fun i => A i b) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    change _ = v b * A i b
    ring
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hA b)

/- English proof (translation)
Introduce `D p _ lam τ N L0 L B h0 hdet hup hlow`. Use `set ψ := GlobalTheory.KernelScalarUnit.lamTau D lam τ with hψdef`. Establish `hψ : ∀ x, tauEmb D lam τ x = ψ x` using `fun x => congrFun (GlobalTheory.KernelScalarUnit.tauEmb_eq D lam τ) x`. Establish `hn : (fun x : D.host.E => ‖lamC lam (embT D τ x)‖) = fun x => ‖ψ x‖` using `funext fun x => by`. Rewrite using `[← hψ]`.

Both sides reduce to the same expression. Establish `hgen : ∀ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L0, A.mulVec v ∈ L) → ‖ψ A.det‖ ≤ ‖B.det‖`. Introduce `A hA`. Establish `hC : ∀ a b, ‖(B⁻¹ * A.map ψ) a b‖ ≤ 1` using `fun a b => by`. Use `hup _ (col_mem h0 hA b) a` as an intermediate fact.

Simplify using `only [hψ] at this`. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `e : A.map ψ = B * (B⁻¹ * A.map ψ)`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul]`. Establish `e2 : ψ A.det = (A.map ψ).det` using `ψ.map_det A`.

Rewrite using `[e2, e, Matrix.det_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_det_le_one hC)`. Establish `hall : ∀ x ∈ detId D L0 L, ‖ψ x‖ ≤ ‖B.det‖`. Establish `: detId D L0 L ≤ GlobalTheory.KernelScalarUnit.ball ψ ‖B.det‖ (norm_nonneg _)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨A, hA, rfl⟩`. Conclude with `hgen A hA`. Conclude with `fun x hx => this hx`. Establish `hbdd : BddAbove ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E))`. Use `⟨‖B.det‖, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hall x hx`. Establish `hne : ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)).Nonempty` using `⟨_, 0, Submodule.zero_mem _, rfl⟩`. Establish `hS0 : 0 ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E))` using `(norm_nonneg _).trans (le_csSup hbdd ⟨0, Submodule.zero_mem _, rfl⟩)`. Use `choose n r x hr hx hB using hlow`.

Establish `hlow : ‖B.det‖ ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E))`. Set `f` to `(Matrix.detRowAlternating : (Fin N → ℂ_[p]) [⋀^Fin N]→ₗ[ℂ_[p]] ℂ_[p]).toMultilinearMap`. Establish `e1 : B.det = f (fun a => ∑ k, r a k • fun i => ψ (x a k i))`. Rewrite using `[← Matrix.det_transpose]`. Express the relevant statement in the definitionally equal form `Matrix.detRowAlternating _ = Matrix.detRowAlternating _`.

Use `congr 1`. Use function extensionality and compare the values at `a i`. Simplify using `only [Matrix.transpose_apply, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ]`. Rewrite using `[e1, f.map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hS0 fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[f.map_smul_univ, smul_eq_mul, norm_mul, norm_prod]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun a _ => hr a (c a))).trans ?_` and prove the remaining obligations. Set `A : Matrix (Fin N) (Fin N) D.host.E` to `Matrix.of fun i a => x a (c a) i`. Establish `hA : ∀ v ∈ L0, A.mulVec v ∈ L` using `mulVec_mem h0 fun b => hx b (c b)`. Establish `e3 : f (fun a i => ψ (x a (c a) i)) = ψ A.det`.

Rewrite using `[ψ.map_det A, ← Matrix.det_transpose]`. Both sides reduce to the same expression. Rewrite using `[e3]`. Conclude with `le_csSup hbdd ⟨A.det, Submodule.subset_span ⟨A, hA, rfl⟩, rfl⟩`. Unfold `nrmId`.

Rewrite using `[hn]`. Conclude with `le_antisymm hlow (csSup_le hne fun _ ⟨y, hy, e⟩ => e ▸ hall y hy)`.
-/
theorem norm_det_eq_nrmId : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (N : ℕ) (L0 L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]), (∀ x, x ∈ L0 ↔ ∀ k, IsIntegral ℤ (x k)) → B.det ≠ 0 → (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) → (∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧ ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)) → ‖B.det‖ = nrmId D lam τ (detId D L0 L) := by
  intro D p _ lam τ N L0 L B h0 hdet hup hlow
  set ψ := GlobalTheory.KernelScalarUnit.lamTau D lam τ with hψdef
  have hψ : ∀ x, tauEmb D lam τ x = ψ x := fun x => congrFun (GlobalTheory.KernelScalarUnit.tauEmb_eq D lam τ) x
  have hn : (fun x : D.host.E => ‖lamC lam (embT D τ x)‖) = fun x => ‖ψ x‖ := funext fun x => by
    rw [← hψ]; rfl

  have hgen : ∀ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L0, A.mulVec v ∈ L) → ‖ψ A.det‖ ≤ ‖B.det‖ := by
    intro A hA
    have hC : ∀ a b, ‖(B⁻¹ * A.map ψ) a b‖ ≤ 1 := fun a b => by
      have := hup _ (col_mem h0 hA b) a
      simp only [hψ] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have e : A.map ψ = B * (B⁻¹ * A.map ψ) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul]
    have e2 : ψ A.det = (A.map ψ).det := ψ.map_det A
    rw [e2, e, Matrix.det_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_det_le_one hC)
  have hall : ∀ x ∈ detId D L0 L, ‖ψ x‖ ≤ ‖B.det‖ := by
    have : detId D L0 L ≤ GlobalTheory.KernelScalarUnit.ball ψ ‖B.det‖ (norm_nonneg _) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨A, hA, rfl⟩
      exact hgen A hA
    exact fun x hx => this hx
  have hbdd : BddAbove ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) := by
    refine ⟨‖B.det‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hall x hx
  have hne : ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)).Nonempty :=
    ⟨_, 0, Submodule.zero_mem _, rfl⟩
  have hS0 : 0 ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) :=
    (norm_nonneg _).trans (le_csSup hbdd ⟨0, Submodule.zero_mem _, rfl⟩)

  choose n r x hr hx hB using hlow
  have hlow : ‖B.det‖ ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) := by
    let f := (Matrix.detRowAlternating : (Fin N → ℂ_[p]) [⋀^Fin N]→ₗ[ℂ_[p]] ℂ_[p]).toMultilinearMap
    have e1 : B.det = f (fun a => ∑ k, r a k • fun i => ψ (x a k i)) := by
      rw [← Matrix.det_transpose]
      change Matrix.detRowAlternating _ = Matrix.detRowAlternating _
      congr 1
      funext a i
      simp only [Matrix.transpose_apply, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ]
    rw [e1, f.map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hS0 fun c _ => ?_
    rw [f.map_smul_univ, smul_eq_mul,
      norm_mul, norm_prod]
    refine (mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun a _ => hr a (c a))).trans ?_
    let A : Matrix (Fin N) (Fin N) D.host.E := Matrix.of fun i a => x a (c a) i
    have hA : ∀ v ∈ L0, A.mulVec v ∈ L := mulVec_mem h0 fun b => hx b (c b)
    have e3 : f (fun a i => ψ (x a (c a) i)) = ψ A.det := by
      rw [ψ.map_det A, ← Matrix.det_transpose]
      rfl
    rw [e3]
    exact le_csSup hbdd ⟨A.det, Submodule.subset_span ⟨A, hA, rfl⟩, rfl⟩
  unfold nrmId
  rw [hn]
  exact le_antisymm hlow (csSup_le hne fun _ ⟨y, hy, e⟩ => e ▸ hall y hy)

end GlobalTheory.DetBasisNorm
