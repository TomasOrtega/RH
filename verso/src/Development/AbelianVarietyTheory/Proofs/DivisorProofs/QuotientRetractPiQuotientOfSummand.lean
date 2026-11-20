import Mathlib
universe u

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ _ I H _ _ _ _ F hIF hEx`. Take `⟨E', M, hc, hF⟩` from `hEx`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' C H`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Set `P : H →ₗ[C] M` to `Submodule.linearProjOfIsCompl M E' hc.symm`.

Set `q : H →ₗ[C] H` to `M.subtype ∘ₗ P`. Establish `hPq : ∀ x, P (q x) = P x` using `fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm (P x)`. Establish `hqq : ∀ x, q (q x) = q x` using `fun x => congrArg Subtype.val (hPq x)`. Establish `hqE : ∀ x ∈ E', q x = 0` using `fun x hx => by`. Establish `h0 : P x = 0` using `(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx`.

Use `show ((P x : M) : H) = 0`. Rewrite using `[h0]`. Both sides reduce to the same expression. Establish `hxq : ∀ x, x - q x ∈ F`. Introduce `x`.

Rewrite using `[← hF]`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Establish `h0 : P (x - q x) = 0` using `by rw [map_sub, hPq, sub_self]`. Conclude with `(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).1 h0`. Establish `hσπ : ∀ x, π (σ x) = x` using `fun x => LinearMap.congr_fun hσ x`.

Set `s0 : H →ₗ[C] (Fin n → C ⧸ I)` to `(LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) ∘ₗ σ ∘ₗ q`. Establish `hs0 : F ≤ LinearMap.ker s0`. Rewrite using `[← hF]`. Use `sup_le (fun x hx => ?_) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker] show (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) (σ (q x)) = 0`.

Rewrite using `[hqE x hx, map_zero, map_zero]`. Use `Submodule.smul_le.2 (fun c hcI y _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_smul]`. Use function extensionality and compare the values at `k`. Use `show c • (Submodule.mkQ I (σ (q y) k)) = 0`.

Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `I.mul_mem_right _ hcI`. Set `s : (H ⧸ F) →ₗ[C] (Fin n → C ⧸ I)` to `F.liftQ s0 hs0`. Set `e : Fin n → (Fin n → C)` to `fun k j => if k = j then 1 else 0`. Establish `hk : ∀ k, I ≤ LinearMap.ker (LinearMap.toSpanSingleton C (H ⧸ F) (F.mkQ (q (π (e k)))))`.

Introduce `k c hcI`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hIF (Submodule.smul_mem_smul hcI Submodule.mem_top)`. Set `g : Fin n → ((C ⧸ I) →ₗ[C] (H ⧸ F))` to `fun k => I.liftQ _ (hk k)`. Set `r : (Fin n → C ⧸ I) →ₗ[C] (H ⧸ F)` to `∑ k, g k ∘ₗ LinearMap.proj k`.

Use `⟨n, s, r, ?_⟩` and prove the remaining obligations. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `x`. Establish `h1 : r (s (F.mkQ x)) = F.mkQ (q (π (σ (q x))))`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ π (σ (q x)), map_sum, map_sum]`.

Simplify using `only [r, s, g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.liftQ_apply, Submodule.mkQ_apply, s0, LinearMap.pi_apply]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, map_smul, ← Submodule.Quotient.mk_smul]`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, h1, hσπ, hqq]`. Use `show F.mkQ (q x) = F.mkQ x`.

Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]`. Conclude with `hxq x`.
-/
theorem quotient_retract_pi_quotient :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
      [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
      (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
      ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
        r ∘ₗ s = LinearMap.id := by
  intro C _ _ I H _ _ _ _ F hIF hEx
  obtain ⟨E', M, hc, hF⟩ := hEx
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' C H
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let P : H →ₗ[C] M := Submodule.linearProjOfIsCompl M E' hc.symm
  let q : H →ₗ[C] H := M.subtype ∘ₗ P
  have hPq : ∀ x, P (q x) = P x := fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm (P x)
  have hqq : ∀ x, q (q x) = q x := fun x => congrArg Subtype.val (hPq x)
  have hqE : ∀ x ∈ E', q x = 0 := fun x hx => by
    have h0 : P x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
    show ((P x : M) : H) = 0
    rw [h0]; rfl
  have hxq : ∀ x, x - q x ∈ F := by
    intro x
    rw [← hF]
    apply Submodule.mem_sup_left
    have h0 : P (x - q x) = 0 := by rw [map_sub, hPq, sub_self]
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).1 h0
  have hσπ : ∀ x, π (σ x) = x := fun x => LinearMap.congr_fun hσ x
  let s0 : H →ₗ[C] (Fin n → C ⧸ I) :=
    (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) ∘ₗ σ ∘ₗ q
  have hs0 : F ≤ LinearMap.ker s0 := by
    rw [← hF]
    refine sup_le (fun x hx => ?_) ?_
    · rw [LinearMap.mem_ker]
      show (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) (σ (q x)) = 0
      rw [hqE x hx, map_zero, map_zero]
    · refine Submodule.smul_le.2 (fun c hcI y _ => ?_)
      rw [LinearMap.mem_ker, map_smul]
      funext k
      show c • (Submodule.mkQ I (σ (q y) k)) = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.mul_mem_right _ hcI
  let s : (H ⧸ F) →ₗ[C] (Fin n → C ⧸ I) := F.liftQ s0 hs0
  let e : Fin n → (Fin n → C) := fun k j => if k = j then 1 else 0
  have hk : ∀ k, I ≤ LinearMap.ker (LinearMap.toSpanSingleton C (H ⧸ F) (F.mkQ (q (π (e k))))) := by
    intro k c hcI
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hIF (Submodule.smul_mem_smul hcI Submodule.mem_top)
  let g : Fin n → ((C ⧸ I) →ₗ[C] (H ⧸ F)) := fun k => I.liftQ _ (hk k)
  let r : (Fin n → C ⧸ I) →ₗ[C] (H ⧸ F) := ∑ k, g k ∘ₗ LinearMap.proj k
  refine ⟨n, s, r, ?_⟩
  apply Submodule.linearMap_qext
  ext x
  have h1 : r (s (F.mkQ x)) = F.mkQ (q (π (σ (q x)))) := by
    rw [LinearMap.pi_apply_eq_sum_univ π (σ (q x)), map_sum, map_sum]
    simp only [r, s, g, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, Submodule.mkQ_apply, s0, LinearMap.pi_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LinearMap.toSpanSingleton_apply, map_smul, ← Submodule.Quotient.mk_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, hσπ, hqq]
  show F.mkQ (q x) = F.mkQ x
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]
  exact hxq x

end GlobalTheory
