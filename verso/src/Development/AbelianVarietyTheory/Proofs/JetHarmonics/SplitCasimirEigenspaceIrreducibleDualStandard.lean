import Mathlib
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HwComponentTensorDualStandard
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDualStandardRel
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ n E Et Om β L l hH hA hEt hOm`. Take `⟨hgl, hAt, -, hcomm⟩` from `tensor_dual_standard_rel V n E Et Om hH.gl hA hEt hOm`. Use `set S := Module.End.eigenspace Om (β + L l + (n : ℂ)) with hS`. Establish `hstab : Stab Et S`. Introduce `a b v hv`.

Rewrite `hv`, the goal using `[hS, Module.End.mem_eigenspace_iff]`. Use `LinearMap.congr_fun (hcomm a b) v` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hv, map_smul]`. Establish `hdec : SDec (shf β L)`.

Introduce `a b hab`. Establish `h` using `hH.anti hab`. Use `⟨(L a - L b - 1).toNat, ?_⟩` and prove the remaining obligations. Establish `h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1` using `Int.toNat_of_nonneg (by omega)`. Establish `h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1` using `by exact_mod_cast h2`.

Rewrite using `[h3]`. Simplify using `only [shf]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwt : ∀ (ν : Fin (n + 1) → ℂ) (v : V), v ≠ 0 → IsHW E ν v → ∀ j, ν j = β + L j + ((j : ℕ) : ℂ)`. Introduce `ν v hv hw j`.

Establish `hm : v ∈ CapSp E (shf β L)` using `mem_CapSp.mpr fun w => hH.cap w v`. Establish `hne : CapSp E (shf β L) ≠ ⊥` using `fun h => hv (by rw [h] at hm; simpa using hm)`. Conclude with `(Formalism.FourierDecayAlt.P.capelli_singular V (n + 1) E _ hH.gl hne).2 hdec ν v hm hv hw j`. Establish `hkey : ∀ (θ : Fin (n + 1) → ℂ) (y : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S → y ≠ 0 → IsHW Et θ y → y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧ θ = fun j => β + L j + ((j : ℕ) : ℂ) - if j = l then 1 else 0`. Introduce `θ y hy hy0 hw`.

Rewrite `hy` using `[hS, Module.End.mem_eigenspace_iff]`. Take `⟨c, hc, hwc, hlam⟩` from `hw_component_tensor_dual_standard V n E Et Om θ _ y hEt hOm hy0 hw hy`. Establish `h1` using `hwt _ _ hc hwc`. Establish `h2` using `h1 c`. Simplify using `only [if_true] at h2`.

Establish `h3 : (L l : ℂ) = L c` using `by linear_combination hlam + h2`. Establish `h4 : l = c` using `hH.anti.injective (by exact_mod_cast h3)`. Substitute `h4` using the available equality. Use `⟨hc, ?_, ?_⟩` and prove the remaining obligations. Establish `: (fun j => β + L j + ((j : ℕ) : ℂ)) = fun a => θ a + if a = l then 1 else 0`.

Use function extensionality and compare the values at `fun j => (h1 j).symm`. Rewrite using `[this]`. Conclude with `hwc`. Use function extensionality and compare the values at `j`. Rewrite using `[← h1 j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsub : ∀ (ν : Fin (n + 1) → ℂ) (v : V), IsHW E ν v → IsHW (subA E) (fun a => ν a.castSucc) v`. Introduce `ν v hw`. Conclude with `⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩`. Establish `hprop : ∀ (θ θ' : Fin (n + 1) → ℂ) (y y' : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S → y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' → ∃ t : ℂ, y' = t • y`.

Introduce `θ θ' y y' hy hy0 hw hy' hy0' hw'`. Take `⟨a1, a2, a3⟩` from `hkey θ y hy hy0 hw`. Take `⟨b1, b2, b3⟩` from `hkey θ' y' hy' hy0' hw'`. Take `⟨t, ht⟩` from `Formalism.FourierDecayAlt.P.multiplicity_one V n E _ _ _ hH.gl hH.irr (hsub _ _ a2) (hsub _ _ b2) a1`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `hθ : θ' = θ` using `b3.trans a3.symm`. Rewrite `hw'` using `[hθ]`. Establish `hz : IsHW Et θ (y' - t • y)`. Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]`. Rewrite using `[map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab, smul_zero, sub_zero]`. Use `(hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) (sub_ne_zero.mpr hne) hz).1` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[PiLp.sub_apply, PiLp.smul_apply, ht, sub_self]`.

Establish `hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S`. Introduce `S' hle hst`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨h0, h1⟩` from `hcon`.

Establish `hT : S'ᗮ ⊓ S ≠ ⊥`. Introduce `h`. Use `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle` as an intermediate fact. Rewrite `this` using `[h, sup_bot_eq]`. Conclude with `h1 this`.

Establish `hTs : Stab Et (S'ᗮ ⊓ S)`. Introduce `a b v hv`. Use `⟨?_, hstab a b v hv.2⟩` and prove the remaining obligations. Establish `hv1 : v ∈ S'ᗮ` using `hv.1`. Express the relevant statement in the definitionally equal form `Et a b v ∈ S'ᗮ`.

Rewrite `hv1`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← hAt]`. Conclude with `hv1 _ (hst b a u hu)`. Take `⟨θ, y, hy, hy0, hw, -⟩` from `Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S' hst h0`.

Take `⟨θ', y', hy', hy0', hw', -⟩` from `Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl _ hTs hT`. Take `⟨t, ht⟩` from `hprop θ θ' y y' (hle hy) hy0 hw hy'.2 hy0' hw'`. Establish `hm : y' ∈ S'` using `ht ▸ S'.smul_mem t hy`. Establish `hm2 : y' ∈ S'ᗮ` using `hy'.1`. Conclude with `hy0' (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hm2 y' hm))`.

Use `⟨hstab, hirr, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : S = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`. Take `⟨θ, y, hy, hy0, hw, -⟩` from `Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S hstab h0`.

Take `⟨-, -, hθ⟩` from `hkey θ y hy hy0 hw`. Establish `hcap : y ∈ CapSp Et (shf β (Function.update L l (L l - 1)))`. Rewrite using `[mem_CapSp]`. Introduce `w`. Rewrite using `[qDetHW _ (n + 1) Et θ y hgl hw w]`.

Use `congr 1`. Unfold `cpol shf`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hθ]`. Distinguish the cases in `hk : k = l`.

Substitute `hk` using the available equality. Simplify using `only [if_true, Function.update_self]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hk, if_false, Function.update_of_ne hk]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcs` using `(Formalism.FourierDecayAlt.P.capelli_stabilizer _ (n + 1) Et (shf β (Function.update L l (L l - 1))) hgl).1`. Break down `hirr (CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S) inf_le_right (fun a b v hv => ⟨hcs a b v hv.1, hstab a b v hv.2⟩) with h | h` into its components or cases. Establish `: y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S` using `⟨hcap, hy⟩`. Rewrite `this` using `[h]`.

Conclude with `absurd (by simpa using this) hy0`. Conclude with `inf_eq_right.mp h`.
-/
theorem casimir_eigenspace_irred_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + (n : ℂ)) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ Module.End.eigenspace Om (β + L l + (n : ℂ)) ≤ CapSp Et (shf β (Function.update L l (L l - 1))) := by
  intro V _ _ _ n E Et Om β L l hH hA hEt hOm
  classical
  obtain ⟨hgl, hAt, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hH.gl hA hEt hOm
  set S := Module.End.eigenspace Om (β + L l + (n : ℂ)) with hS
  have hstab : Stab Et S := by
    intro a b v hv
    rw [hS, Module.End.mem_eigenspace_iff] at hv ⊢
    have := LinearMap.congr_fun (hcomm a b) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  have hdec : SDec (shf β L) := by
    intro a b hab
    have h := hH.anti hab
    refine ⟨(L a - L b - 1).toNat, ?_⟩
    have h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1 := by exact_mod_cast h2
    rw [h3]; simp only [shf]; ring
  have hwt : ∀ (ν : Fin (n + 1) → ℂ) (v : V), v ≠ 0 → IsHW E ν v →
      ∀ j, ν j = β + L j + ((j : ℕ) : ℂ) := by
    intro ν v hv hw j
    have hm : v ∈ CapSp E (shf β L) := mem_CapSp.mpr fun w => hH.cap w v
    have hne : CapSp E (shf β L) ≠ ⊥ := fun h => hv (by rw [h] at hm; simpa using hm)
    exact (Formalism.FourierDecayAlt.P.capelli_singular V (n + 1) E _ hH.gl hne).2 hdec ν v hm hv hw j
  have hkey : ∀ (θ : Fin (n + 1) → ℂ) (y : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S → y ≠ 0 →
      IsHW Et θ y → y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧
        θ = fun j => β + L j + ((j : ℕ) : ℂ) - if j = l then 1 else 0 := by
    intro θ y hy hy0 hw
    rw [hS, Module.End.mem_eigenspace_iff] at hy
    obtain ⟨c, hc, hwc, hlam⟩ :=
      hw_component_tensor_dual_standard V n E Et Om θ _ y hEt hOm hy0 hw hy
    have h1 := hwt _ _ hc hwc
    have h2 := h1 c
    simp only [if_true] at h2
    have h3 : (L l : ℂ) = L c := by linear_combination hlam + h2
    have h4 : l = c := hH.anti.injective (by exact_mod_cast h3)
    subst h4
    refine ⟨hc, ?_, ?_⟩
    · have : (fun j => β + L j + ((j : ℕ) : ℂ)) = fun a => θ a + if a = l then 1 else 0 :=
        funext fun j => (h1 j).symm
      rw [this]; exact hwc
    · funext j
      rw [← h1 j]; ring
  have hsub : ∀ (ν : Fin (n + 1) → ℂ) (v : V), IsHW E ν v →
      IsHW (subA E) (fun a => ν a.castSucc) v := by
    intro ν v hw
    exact ⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩
  have hprop : ∀ (θ θ' : Fin (n + 1) → ℂ) (y y' : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S →
      y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' → ∃ t : ℂ, y' = t • y := by
    intro θ θ' y y' hy hy0 hw hy' hy0' hw'
    obtain ⟨a1, a2, a3⟩ := hkey θ y hy hy0 hw
    obtain ⟨b1, b2, b3⟩ := hkey θ' y' hy' hy0' hw'
    obtain ⟨t, ht⟩ := Formalism.FourierDecayAlt.P.multiplicity_one V n E _ _ _ hH.gl hH.irr (hsub _ _ a2)
      (hsub _ _ b2) a1
    refine ⟨t, ?_⟩
    by_contra hne
    have hθ : θ' = θ := b3.trans a3.symm
    rw [hθ] at hw'
    have hz : IsHW Et θ (y' - t • y) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · rw [map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]
      · rw [map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab, smul_zero, sub_zero]
    have := (hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) (sub_ne_zero.mpr hne) hz).1
    apply this
    rw [PiLp.sub_apply, PiLp.smul_apply, ht, sub_self]
  have hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' →
      S' = ⊥ ∨ S' = S := by
    intro S' hle hst
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hT : S'ᗮ ⊓ S ≠ ⊥ := by
      intro h
      have := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
      rw [h, sup_bot_eq] at this
      exact h1 this
    have hTs : Stab Et (S'ᗮ ⊓ S) := by
      intro a b v hv
      refine ⟨?_, hstab a b v hv.2⟩
      have hv1 : v ∈ S'ᗮ := hv.1
      change Et a b v ∈ S'ᗮ
      rw [Submodule.mem_orthogonal] at hv1 ⊢
      intro u hu
      rw [← hAt]
      exact hv1 _ (hst b a u hu)
    obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S' hst h0
    obtain ⟨θ', y', hy', hy0', hw', -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl _ hTs hT
    obtain ⟨t, ht⟩ := hprop θ θ' y y' (hle hy) hy0 hw hy'.2 hy0' hw'
    have hm : y' ∈ S' := ht ▸ S'.smul_mem t hy
    have hm2 : y' ∈ S'ᗮ := hy'.1
    exact hy0' (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hm2 y' hm))
  refine ⟨hstab, hirr, ?_⟩
  by_cases h0 : S = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
    Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S hstab h0
  obtain ⟨-, -, hθ⟩ := hkey θ y hy hy0 hw
  have hcap : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) := by
    rw [mem_CapSp]
    intro w
    rw [qDetHW _ (n + 1) Et θ y hgl hw w]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hθ]
    by_cases hk : k = l
    · subst hk
      simp only [if_true, Function.update_self]
      push_cast; ring
    · simp only [hk, if_false, Function.update_of_ne hk]
      ring
  have hcs := (Formalism.FourierDecayAlt.P.capelli_stabilizer _ (n + 1) Et
    (shf β (Function.update L l (L l - 1))) hgl).1
  rcases hirr (CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S) inf_le_right
    (fun a b v hv => ⟨hcs a b v hv.1, hstab a b v hv.2⟩) with h | h
  · have : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S := ⟨hcap, hy⟩
    rw [h] at this
    exact absurd (by simpa using this) hy0
  · exact inf_eq_right.mp h

end GlobalTheory
