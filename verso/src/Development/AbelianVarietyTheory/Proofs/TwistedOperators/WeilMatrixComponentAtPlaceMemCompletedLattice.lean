import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeLocal

section
variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Use `show (singleV F v 1 : Af F) v = 1`. Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_same _ v 1`.
-/
theorem ev_self (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 := by
  classical
  show (singleV F v 1 : Af F) v = 1
  unfold singleV
  exact RestrictedProduct.single_eq_same _ v 1

/- English proof (translation)
Use `show (singleV F v 1 : Af F) w = 0`. Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_of_ne _ 1 h`.
-/
theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 := by
  classical
  show (singleV F v 1 : Af F) w = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ 1 h

/- English proof (translation)
Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `w`. Conclude with `h w`.
-/
theorem af_ext {α β : Af F} (h : ∀ w, evalV F w α = evalV F w β) : α = β := by
  apply RestrictedProduct.ext
  intro w
  exact h w

end

variable {D : D7}

/- English proof (translation)
Establish `key : pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 α = pairA D.host.F 0 (singleV D.host.F v 1 * α)` using `Prod.ext (mul_zero _) rfl`. Simplify using `only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, key]`.
-/
theorem idem_inl_mul (v : FinPl D) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inl v) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] m := by
  have key : pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) := Prod.ext (mul_zero _) rfl
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, key]

/- English proof (translation)
Establish `key : pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0 * pairA D.host.F 0 α = 0` using `Prod.ext (mul_zero _) (zero_mul _)`. Simplify using `only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, key, TensorProduct.zero_tmul]`.
-/
theorem idem_inr_mul (τ : D.what₂.Tau) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inr τ) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = 0 := by
  have key : pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0 * pairA D.host.F 0 α = 0 :=
    Prod.ext (mul_zero _) (zero_mul _)
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, key, TensorProduct.zero_tmul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[wAt, mul_add]`.
-/
theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  ext i j
  simp [wAt, mul_add]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[wAt]`.
-/
theorem wAt_neg {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (-x) = -wAt p x := by
  ext i j
  simp [wAt]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[wAt]`.
-/
theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  ext i j
  simp [wAt]

/- English proof (translation)
Introduce `D S T ΛS ΛT P u hu p`. Unfold `latO at hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, hv, a, ha, s, hs, t, ht, hw⟩` from `hw`.

Take `⟨X, hX⟩ : ∃ X : Fin T.rank → Fin S.rank → D.host.E, X = fun i j => a * t i * ∑ k, star (s k) * S.gram k j` from `⟨_, rfl⟩`. Establish `gen : ∀ (Q : FinPl D → Prop) (β : Af D.host.F), β ∈ intAf D.host.F → (∀ v, ¬ Q v → evalV D.host.F v β = 0) → (Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] X i j) ∈ latO S T ΛS ΛT Q`. Introduce `Q β hβ hQ`. Unfold `latO`. Use `AddSubgroup.subset_closure ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨β, hβ, hQ, a, ha, s, hs, t, ht, by subst hX; rfl⟩`. Establish `hw' : w = Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j`. Substitute `hX` using the available equality. Conclude with `hw`.

Substitute `hw'` using the available equality. Break down `p with v | τ` into its components or cases. Establish `hs1 : ∀ v', evalV D.host.F v' (singleV D.host.F v 1) ∈ v'.adicCompletionIntegers D.host.F`. Introduce `v'`. Distinguish the cases in `h : v' = v`.

Rewrite using `[h, ev_self]`. Conclude with `one_mem _`. Rewrite using `[ev_ne _ h]`. Conclude with `zero_mem _`. Establish `e1 : wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = Matrix.of fun i j => pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j`.

Use extensionality with `i j`. Simplify using `only [wAt, Matrix.of_apply, idem_inl_mul]`. Establish `e2 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) - wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = Matrix.of fun i j => pairA D.host.F 0 (α - singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j`. Rewrite using `[e1]`. Use extensionality with `i j`.

Simplify using `only [Matrix.sub_apply, Matrix.of_apply, ← TensorProduct.sub_tmul]`. Use `congr 1`. Conclude with `Prod.ext (sub_self _) rfl`. Use `⟨?_, ?_, fun hp => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Use `gen _ _ (fun v' => ?_) (fun v' hv' => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_mem (hs1 v') (hα v')`. Distinguish the cases in `h : v' = v`. Rewrite `hv'`, the goal using `[h]`.

Establish `hPv : ¬ P v` using `fun hP => hv' ⟨hP, rfl⟩`. Rewrite using `[map_mul, hv v hPv, mul_zero]`. Rewrite using `[map_mul, ev_ne _ h, zero_mul]`. Rewrite using `[e2]`. Use `gen _ _ (fun v' => ?_) (fun v' hv' => ?_)` and prove the remaining obligations.

Rewrite using `[map_sub, map_mul]`. Conclude with `sub_mem (hα v') (mul_mem (hs1 v') (hα v'))`. Distinguish the cases in `h : v' = v`. Rewrite using `[h, map_sub, map_mul, ev_self, one_mul, sub_self]`. Establish `hPv : ¬ P v'` using `fun hP => hv' ⟨hP, fun e => h (Sum.inl_injective e)⟩`.

Rewrite using `[map_sub, map_mul, hv v' hPv, mul_zero, sub_zero]`. Establish `hPv : ¬ P v` using `fun hP => hp v hP rfl`. Establish `h0 : singleV D.host.F v 1 * α = 0`. Apply `af_ext` to reduce the goal to its premises. Introduce `v'`.

Distinguish the cases in `h : v' = v`. Rewrite using `[h, map_mul, hv v hPv, mul_zero, map_zero]`. Rewrite using `[map_mul, ev_ne _ h, zero_mul, map_zero]`. Rewrite using `[e1, h0]`. Use extensionality with `i j`.

Simplify using `only [Matrix.of_apply, Matrix.zero_apply]`. Rewrite using `[show pairA D.host.F 0 0 = 0 from Prod.ext rfl rfl, TensorProduct.zero_tmul]`. Establish `e0 : wAt (.inr τ) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = 0`. Use extensionality with `i j`. Simplify using `only [wAt, Matrix.of_apply, Matrix.zero_apply, idem_inr_mul]`.

Use `⟨?_, ?_, fun _ => e0⟩` and prove the remaining obligations. Rewrite using `[e0]`. Conclude with `zero_mem _`. Rewrite using `[e0, sub_zero]`. Conclude with `gen _ _ hα (fun v' hv' => hv v' (fun hP => hv' ⟨hP, Sum.inl_ne_inr⟩))`.

Consider the case `zero`. Rewrite using `[wAt_zero, sub_zero]`. Conclude with `⟨zero_mem _, zero_mem _, fun _ => rfl⟩`. Consider the case `add x y _ _ ihx ihy`. Take `⟨hx1, hx2, hx3⟩` from `ihx`.

Take `⟨hy1, hy2, hy3⟩` from `ihy`. Rewrite using `[wAt_add]`. Use `⟨add_mem hx1 hy1, ?_, fun hp => by rw [hx3 hp, hy3 hp, add_zero]⟩` and prove the remaining obligations. Rewrite using `[add_sub_add_comm]`. Conclude with `add_mem hx2 hy2`.

Consider the case `neg x _ ih`. Take `⟨h1, h2, h3⟩` from `ih`. Rewrite using `[wAt_neg]`. Use `⟨neg_mem h1, ?_, fun hp => by rw [h3 hp, neg_zero]⟩` and prove the remaining obligations. Rewrite using `[neg_sub_neg, ← neg_sub]`.

Conclude with `neg_mem h2`.
-/
theorem wAt_mem_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  intro D S T ΛS ΛT P u hu p
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, hw⟩ := hw

    obtain ⟨X, hX⟩ : ∃ X : Fin T.rank → Fin S.rank → D.host.E,
        X = fun i j => a * t i * ∑ k, star (s k) * S.gram k j := ⟨_, rfl⟩

    have gen : ∀ (Q : FinPl D → Prop) (β : Af D.host.F), β ∈ intAf D.host.F →
        (∀ v, ¬ Q v → evalV D.host.F v β = 0) →
        (Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] X i j) ∈ latO S T ΛS ΛT Q := by
      intro Q β hβ hQ
      unfold latO
      refine AddSubgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq]
      exact ⟨β, hβ, hQ, a, ha, s, hs, t, ht, by subst hX; rfl⟩
    have hw' : w = Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j := by
      subst hX
      exact hw
    subst hw'
    rcases p with v | τ
    ·
      have hs1 : ∀ v', evalV D.host.F v' (singleV D.host.F v 1) ∈ v'.adicCompletionIntegers D.host.F := by
        intro v'
        by_cases h : v' = v
        · rw [h, ev_self]
          exact one_mem _
        · rw [ev_ne _ h]
          exact zero_mem _
      have e1 : wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        ext i j
        simp only [wAt, Matrix.of_apply, idem_inl_mul]
      have e2 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) -
            wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (α - singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        rw [e1]
        ext i j
        simp only [Matrix.sub_apply, Matrix.of_apply, ← TensorProduct.sub_tmul]
        congr 1
        exact Prod.ext (sub_self _) rfl
      refine ⟨?_, ?_, fun hp => ?_⟩
      · rw [e1]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_mul]
          exact mul_mem (hs1 v') (hα v')
        · by_cases h : v' = v
          · rw [h] at hv' ⊢
            have hPv : ¬ P v := fun hP => hv' ⟨hP, rfl⟩
            rw [map_mul, hv v hPv, mul_zero]
          · rw [map_mul, ev_ne _ h, zero_mul]
      · rw [e2]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_sub, map_mul]
          exact sub_mem (hα v') (mul_mem (hs1 v') (hα v'))
        · by_cases h : v' = v
          · rw [h, map_sub, map_mul, ev_self, one_mul, sub_self]
          · have hPv : ¬ P v' := fun hP => hv' ⟨hP, fun e => h (Sum.inl_injective e)⟩
            rw [map_sub, map_mul, hv v' hPv, mul_zero, sub_zero]
      · have hPv : ¬ P v := fun hP => hp v hP rfl
        have h0 : singleV D.host.F v 1 * α = 0 := by
          apply af_ext
          intro v'
          by_cases h : v' = v
          · rw [h, map_mul, hv v hPv, mul_zero, map_zero]
          · rw [map_mul, ev_ne _ h, zero_mul, map_zero]
        rw [e1, h0]
        ext i j
        simp only [Matrix.of_apply, Matrix.zero_apply]
        rw [show pairA D.host.F 0 0 = 0 from Prod.ext rfl rfl, TensorProduct.zero_tmul]
    ·
      have e0 : wAt (.inr τ) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = 0 := by
        ext i j
        simp only [wAt, Matrix.of_apply, Matrix.zero_apply, idem_inr_mul]
      refine ⟨?_, ?_, fun _ => e0⟩
      · rw [e0]
        exact zero_mem _
      · rw [e0, sub_zero]
        exact gen _ _ hα (fun v' hv' => hv v' (fun hP => hv' ⟨hP, Sum.inl_ne_inr⟩))
  | zero =>
    rw [wAt_zero, sub_zero]
    exact ⟨zero_mem _, zero_mem _, fun _ => rfl⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨hx1, hx2, hx3⟩ := ihx
    obtain ⟨hy1, hy2, hy3⟩ := ihy
    rw [wAt_add]
    refine ⟨add_mem hx1 hy1, ?_, fun hp => by rw [hx3 hp, hy3 hp, add_zero]⟩
    rw [add_sub_add_comm]
    exact add_mem hx2 hy2
  | neg x _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [wAt_neg]
    refine ⟨neg_mem h1, ?_, fun hp => by rw [h3 hp, neg_zero]⟩
    rw [neg_sub_neg, ← neg_sub]
    exact neg_mem h2

end GlobalTheory.LatticeLocal
