import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.FiniteIndexSemisimple

/- English proof (translation)
Introduce `W hW`. Take `⟨W', hW', hc⟩` from `h W (fun g v hv => hW g v hv)`. Set `ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k)` to `fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin`. Establish `hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v`. Introduce `g h v`.

Simplify using `[ρ, Matrix.mulVec_mulVec, map_mul]`. Establish `hρ1 : ∀ v, ρ 1 v = v` using `by intro v; simp [ρ]`. Establish `hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W` using `fun g v hv => hW g v hv`. Set `p : (Fin n → k) →ₗ[k] (Fin n → k)` to `W.subtype ∘ₗ W.linearProjOfIsCompl W' hc`. Establish `hpW : ∀ v, p v ∈ W` using `fun v => (W.linearProjOfIsCompl W' hc v).2`.

Establish `hpl : ∀ w ∈ W, p w = w` using `fun w hw => by`. Establish `e` using `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)`. Conclude with `e`. Establish `hpr : ∀ w ∈ W', p w = 0` using `fun w hw => by`. Establish `e` using `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)`.

Conclude with `e`. Establish `hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v)`. Introduce `m hm v`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')`. Establish `hb' : ρ m b ∈ W'` using `hW' ⟨m, hm⟩ b hb`.

Rewrite using `[show p (a + b) = a by rw [map_add, hpl a ha, hpr b hb, add_zero], map_add, map_add, hpl _ (hWρ m a ha), hpr _ hb', add_zero]`. Set `T : Γ → (Fin n → k) →ₗ[k] (Fin n → k)` to `fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹`. Establish `hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g`. Introduce `g m hm`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Simplify using `only [T, LinearMap.comp_apply]`. Rewrite using `[mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]`. Establish `hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v)`. Introduce `h g v`. Simplify using `only [T, LinearMap.comp_apply]`.

Rewrite using `[hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]`. Establish `hTW : ∀ g v, T g v ∈ W` using `fun g v => hWρ g _ (hpW _)`. Establish `hTfix : ∀ g, ∀ w ∈ W, T g w = w`. Introduce `g w hw`. Simplify using `only [T, LinearMap.comp_apply]`.

Rewrite using `[hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]`. Use `haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _`. Set `S : (Fin n → k) →ₗ[k] (Fin n → k)` to `∑ q : Γ ⧸ N, T q.out`. Establish `hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out)`. Introduce `h q`.

Establish `e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q` using `by conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Establish `hm : (h * q.out)⁻¹ * (h • q).out ∈ N` using `QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)`. Rewrite using `[← hTN (h * q.out) _ hm, mul_inv_cancel_left]`. Establish `hS : ∀ h v, ρ h (S v) = S (ρ h v)`.

Introduce `h v`. Simplify using `only [S, LinearMap.sum_apply, map_sum, hTc h]`. Rewrite using `[← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [MulAction.toPerm_apply]`.

Rewrite using `[hout]`. Use `set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def`. Establish `hc0 : c ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Set `P : (Fin n → k) →ₗ[k] (Fin n → k)` to `c⁻¹ • S`. Establish `hPW : ∀ v, P v ∈ W` using `fun v => by`.

Simplify using `only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]`. Conclude with `W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)`. Establish `hPfix : ∀ w ∈ W, P w = w` using `fun w hw => by`. Simplify using `only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.

Establish `hP : ∀ h v, ρ h (P v) = P (ρ h v)` using `fun h v => by`. Simplify using `only [P, LinearMap.smul_apply, map_smul, hS]`. Use `⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩` and prove the remaining obligations. Use `show P (ρ g v) = 0`. Rewrite using `[← hP, LinearMap.mem_ker.mp hv, map_zero]`.

Use `⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩` and prove the remaining obligations. Rewrite using `[← hPfix v hv]`. Conclude with `hv'`. Establish `: v = P v + (v - P v)` using `by abel`. Rewrite using `[this]`.

Use `Submodule.add_mem_sup (hPW v) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]`.
-/
theorem isSSRep_of_finiteIndex {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (N : Subgroup Γ) [N.FiniteIndex] (h : IsSSRep (r.comp N.subtype)) : IsSSRep r := by
  classical
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W (fun g v hv => hW g v hv)
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin
  have hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v := by
    intro g h v; simp [ρ, Matrix.mulVec_mulVec, map_mul]
  have hρ1 : ∀ v, ρ 1 v = v := by intro v; simp [ρ]
  have hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv => hW g v hv
  let p : (Fin n → k) →ₗ[k] (Fin n → k) := W.subtype ∘ₗ W.linearProjOfIsCompl W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (W.linearProjOfIsCompl W' hc v).2
  have hpl : ∀ w ∈ W, p w = w := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
    exact e
  have hpr : ∀ w ∈ W', p w = 0 := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)
    exact e
  have hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v) := by
    intro m hm v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
    have hb' : ρ m b ∈ W' := hW' ⟨m, hm⟩ b hb
    rw [show p (a + b) = a by rw [map_add, hpl a ha, hpr b hb, add_zero], map_add, map_add, hpl _ (hWρ m a ha),
      hpr _ hb', add_zero]
  let T : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹
  have hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g := by
    intro g m hm; refine LinearMap.ext fun v => ?_
    simp only [T, LinearMap.comp_apply]
    rw [mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]
  have hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v) := by
    intro h g v
    simp only [T, LinearMap.comp_apply]
    rw [hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]
  have hTW : ∀ g v, T g v ∈ W := fun g v => hWρ g _ (hpW _)
  have hTfix : ∀ g, ∀ w ∈ W, T g w = w := by
    intro g w hw
    simp only [T, LinearMap.comp_apply]
    rw [hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  let S : (Fin n → k) →ₗ[k] (Fin n → k) := ∑ q : Γ ⧸ N, T q.out
  have hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out) := by
    intro h q
    have e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hm : (h * q.out)⁻¹ * (h • q).out ∈ N := QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)
    rw [← hTN (h * q.out) _ hm, mul_inv_cancel_left]
  have hS : ∀ h v, ρ h (S v) = S (ρ h v) := by
    intro h v
    simp only [S, LinearMap.sum_apply, map_sum, hTc h]
    rw [← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [hout]
  set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • S
  have hPW : ∀ v, P v ∈ W := fun v => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    exact W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)
  have hPfix : ∀ w ∈ W, P w = w := fun w hw => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hP : ∀ h v, ρ h (P v) = P (ρ h v) := fun h v => by
    simp only [P, LinearMap.smul_apply, map_smul, hS]
  refine ⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩
  · show P (ρ g v) = 0
    rw [← hP, LinearMap.mem_ker.mp hv, map_zero]
  · refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩
    · rw [← hPfix v hv]; exact hv'
    · have : v = P v + (v - P v) := by abel
      rw [this]
      refine Submodule.add_mem_sup (hPW v) ?_
      rw [LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]

end GlobalTheory.FiniteIndexSemisimple
