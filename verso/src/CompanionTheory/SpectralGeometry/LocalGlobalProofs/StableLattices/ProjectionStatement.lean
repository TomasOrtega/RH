import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI

open scoped InnerProductSpace
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted

namespace GlobalTheory.CompanionTheory.FixedProj

/- English proof (translation)
Unfold `StProj`. Introduce `G H _ _ _ _ σ hiso K`. Set `V : Submodule ℂ H` to `{ carrier := {v | ∀ k ∈ K, σ k v = v} add_mem' := fun {a b} ha hb k hk => by`. Simplify using `only [Set.mem_ofPred_eq] at ha hb ⊢`. Rewrite using `[map_add, ha k hk, hb k hk]`.

Use the proof step `zero_mem' := fun k _ => map_zero _`. Use the proof step `smul_mem' := fun c v hv k hk => by`. Simplify using `only [Set.mem_ofPred_eq] at hv ⊢`. Rewrite using `[map_smul, hv k hk] }`. Establish `hmem : ∀ v, v ∈ V ↔ ∀ k ∈ K, σ k v = v` using `fun v => Iff.rfl`.

Establish `hVc : IsClosed (V : Set H)`. Establish `hV : (V : Set H) = ⋂ k ∈ K, {v | σ k v = v}`. Use extensionality with `v`. Simplify using `only [Set.mem_iInter]`. Conclude with `hmem v`.

Rewrite using `[hV]`. Conclude with `isClosed_biInter fun k _ => isClosed_eq (σ k).continuous continuous_id`. Use `haveI : CompleteSpace V := hVc.completeSpace_coe`. Establish `hin : ∀ g v w, inner ℂ (σ g v) w = inner ℂ v (σ g⁻¹ w)` using `CompanionTheory.D.gk.admitted.FinOfPIAux.inner_left σ hiso`. Use `⟨V.starProjection, ?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `IsAvg`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v k hk`. Conclude with `(hmem _).1 (V.starProjection_apply_mem v) k hk`. Introduce `v hv`.

Conclude with `Submodule.starProjection_eq_self_iff.2 ((hmem v).2 hv)`. Introduce `v k hk`. Establish `horth : σ k v - v ∈ Vᗮ`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Establish `h1 : inner ℂ u (σ k v) = inner ℂ u v`. Establish `h` using `hin k⁻¹ u v`. Rewrite `h` using `[inv_inv, (hmem u).1 hu k⁻¹ (K.inv_mem hk)]`. Conclude with `h.symm`. Rewrite using `[inner_sub_right, h1, sub_self]`.

Establish `h0` using `(Submodule.starProjection_apply_eq_zero_iff V).2 horth`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Conclude with `h0`. Introduce `u w`. Conclude with `Submodule.inner_starProjection_left_eq_right (K := V) u w`.

Introduce `T hT`. Establish `hTσ : ∀ g v, T (σ g v) = σ g (T v)` using `fun g v => congrArg (fun S : H →L[ℂ] H => S v) (hT g)`. Establish `hTV : ∀ v ∈ V, T v ∈ V` using `fun v hv k hk => by`. Rewrite using `[← hTσ, (hmem v).1 hv k hk]`. Establish `hadj : ∀ w ∈ V, ContinuousLinearMap.adjoint T w ∈ V`.

Introduce `w hw k hk`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `z`. Rewrite using `[hin, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hTσ, ← hin, (hmem w).1 hw k hk]`. Use extensionality with `v`.

Establish `h1 : V.starProjection (T (V.starProjection v)) = T (V.starProjection v)` using `Submodule.starProjection_eq_self_iff.2 (hTV _ (V.starProjection_apply_mem v))`. Establish `hu : v - V.starProjection v ∈ Vᗮ` using `Submodule.sub_starProjection_mem_orthogonal (K := V) v`. Establish `h2 : V.starProjection (T (v - V.starProjection v)) = 0`. Apply `(Submodule.starProjection_apply_eq_zero_iff V).2` to reduce the goal to its premises. Rewrite `hu`, the goal using `[Submodule.mem_orthogonal]`.

Introduce `w hw`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_left]`. Conclude with `hu _ (hadj w hw)`. Establish `hv : v = V.starProjection v + (v - V.starProjection v)` using `by abel`. Use `show T (V.starProjection v) = V.starProjection (T v)`.

Use `conv_rhs => rw [hv]`. Simplify using `only [map_add]`. Rewrite using `[h1, h2, add_zero]`.
-/
theorem stProj : StProj := by
  unfold StProj
  intro G H _ _ _ _ σ hiso K
  let V : Submodule ℂ H :=
    { carrier := {v | ∀ k ∈ K, σ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c v hv k hk => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [map_smul, hv k hk] }
  have hmem : ∀ v, v ∈ V ↔ ∀ k ∈ K, σ k v = v := fun v => Iff.rfl
  have hVc : IsClosed (V : Set H) := by
    have hV : (V : Set H) = ⋂ k ∈ K, {v | σ k v = v} := by
      ext v
      simp only [Set.mem_iInter]
      exact hmem v
    rw [hV]
    exact isClosed_biInter fun k _ => isClosed_eq (σ k).continuous continuous_id
  haveI : CompleteSpace V := hVc.completeSpace_coe
  have hin : ∀ g v w, inner ℂ (σ g v) w = inner ℂ v (σ g⁻¹ w) := CompanionTheory.D.gk.admitted.FinOfPIAux.inner_left σ hiso
  refine ⟨V.starProjection, ?_, ?_, ?_⟩
  · unfold IsAvg
    refine ⟨?_, ?_, ?_⟩
    · intro v k hk
      exact (hmem _).1 (V.starProjection_apply_mem v) k hk
    · intro v hv
      exact Submodule.starProjection_eq_self_iff.2 ((hmem v).2 hv)
    · intro v k hk
      have horth : σ k v - v ∈ Vᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 : inner ℂ u (σ k v) = inner ℂ u v := by
          have h := hin k⁻¹ u v
          rw [inv_inv, (hmem u).1 hu k⁻¹ (K.inv_mem hk)] at h
          exact h.symm
        rw [inner_sub_right, h1, sub_self]
      have h0 := (Submodule.starProjection_apply_eq_zero_iff V).2 horth
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  · intro u w
    exact Submodule.inner_starProjection_left_eq_right (K := V) u w
  · intro T hT
    have hTσ : ∀ g v, T (σ g v) = σ g (T v) := fun g v =>
      congrArg (fun S : H →L[ℂ] H => S v) (hT g)
    have hTV : ∀ v ∈ V, T v ∈ V := fun v hv k hk => by
      rw [← hTσ, (hmem v).1 hv k hk]
    have hadj : ∀ w ∈ V, ContinuousLinearMap.adjoint T w ∈ V := by
      intro w hw k hk
      apply ext_inner_right ℂ
      intro z
      rw [hin, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hTσ, ← hin,
        (hmem w).1 hw k hk]
    ext v
    have h1 : V.starProjection (T (V.starProjection v)) = T (V.starProjection v) :=
      Submodule.starProjection_eq_self_iff.2 (hTV _ (V.starProjection_apply_mem v))
    have hu : v - V.starProjection v ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal (K := V) v
    have h2 : V.starProjection (T (v - V.starProjection v)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).2
      rw [Submodule.mem_orthogonal] at hu ⊢
      intro w hw
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact hu _ (hadj w hw)
    have hv : v = V.starProjection v + (v - V.starProjection v) := by abel
    show T (V.starProjection v) = V.starProjection (T v)
    conv_rhs => rw [hv]
    simp only [map_add]
    rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.FixedProj
