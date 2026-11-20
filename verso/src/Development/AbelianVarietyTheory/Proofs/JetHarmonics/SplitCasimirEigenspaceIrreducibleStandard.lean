import Mathlib
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HighestWeightTensorStandard
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ n E Et Om β L l hyp hadj hEt hOm`. Take `⟨hgl, hadjt, -, hcomm⟩` from `tensorStd_rel_adjoint_splitCasimir V n E Et Om hyp.gl hadj hEt hOm`. Use `set S := Module.End.eigenspace Om (β + L l + 0) with hS`. Establish `hmemS : ∀ y, y ∈ S ↔ Om y = (β + L l + 0) • y` using `fun y => Module.End.mem_eigenspace_iff`. Establish `hstab : Stab Et S`.

Introduce `a b v hv`. Rewrite `hv`, the goal using `[hmemS]`. Establish `h` using `LinearMap.congr_fun (hcomm a b) v`. Simplify using `only [Module.End.mul_apply] at h`. Rewrite using `[h, hv, map_smul]`.

Establish `hcapV : ∀ v, v ∈ CapSp E (shf β L)` using `fun v => mem_CapSp.2 fun w => hyp.cap w v`. Establish `hsdec : SDec (shf β L)`. Introduce `a b hab`. Establish `h` using `hyp.anti hab`. Use `⟨(L a - L b - 1).toNat, ?_⟩` and prove the remaining obligations.

Establish `h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1` using `Int.toNat_of_nonneg (by omega)`. Establish `h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1`. Conclude with `congrArg (Int.cast : ℤ → ℂ) h2` after adjusting the coercions. Rewrite using `[h3]`. Simplify using `only [shf]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hwtV : ∀ ν v, v ≠ 0 → IsHW E ν v → ∀ j, ν j = β + L j + ((j : ℕ) : ℂ)`. Introduce `ν v hv hw j`. Establish `hne : CapSp E (shf β L) ≠ ⊥` using `fun h => hv ((Submodule.mem_bot ℂ).1 (h ▸ hcapV v))`. Conclude with `(capelli_singular V (n + 1) E _ hyp.gl hne).2 hsdec ν v (hcapV v) hv hw j`.

Establish `hkey : ∀ θ y, y ∈ S → y ≠ 0 → IsHW Et θ y → y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧ θ = fun j => β + L j + ((j : ℕ) : ℂ) + if j = l then 1 else 0`. Introduce `θ y hy hy0 hw`. Take `⟨c, hc0, hcw, hlam⟩` from `highestWeight_tensor_standard V n E Et Om θ _ y hEt hOm hy0 hw ((hmemS y).1 hy)`. Establish `hν` using `hwtV _ _ hc0 hcw`. Establish `hcl : c = l`.

Establish `h1` using `hν c`. Simplify using `only [if_true] at h1`. Establish `h2 : (L c : ℂ) = L l` using `by linear_combination -h1 - hlam`. Conclude with `hyp.anti.injective (by exact_mod_cast h2)`. Substitute `hcl` using the available equality.

Use `⟨hc0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← funext hν]`. Conclude with `hcw`. Use function extensionality and compare the values at `j`. Rewrite using `[← hν j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsub : ∀ ν v, IsHW E ν v → IsHW (subA E) (fun j => ν j.castSucc) v`. Introduce `ν v hw`. Conclude with `⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (by simpa using hab)⟩`. Establish `hprop : ∀ θ y θ' y', y ∈ S → y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' → ∃ t : ℂ, y' = t • y`.

Introduce `θ y θ' y' hy hy0 hw hy' hy0' hw'`. Take `⟨h1, h2, h3⟩` from `hkey θ y hy hy0 hw`. Take `⟨-, h2', h3'⟩` from `hkey θ' y' hy' hy0' hw'`. Establish `hθ : θ' = θ` using `h3'.trans h3.symm`. Rewrite `hw'` using `[hθ]`.

Take `⟨t, ht⟩` from `multiplicity_one V n E _ (y l) (y' l) hyp.gl hyp.irr (hsub _ _ h2) (hsub _ _ h2') h1`. Use `⟨t, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hz0 : y' - t • y ≠ 0` using `sub_ne_zero.2 hne`. Establish `hzw : IsHW Et θ (y' - t • y)`.

Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]`. Rewrite using `[map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab]`. Simplify using the standard rewrite rules. Apply `(hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) hz0 hzw).1` to reduce the goal to its premises.

Simplify using `[ht]`. Establish `hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S`. Introduce `S' hle hst`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Take `⟨hb, hne⟩` from `hcon`. Establish `hst2 : Stab Et (S'ᗮ ⊓ S)`. Introduce `a b v hv`. Use `⟨?_, hstab a b v hv.2⟩` and prove the remaining obligations. Establish `hv1 : v ∈ S'ᗮ` using `hv.1`.

Express the relevant statement in the definitionally equal form `Et a b v ∈ S'ᗮ`. Rewrite `hv1`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← hadjt]`. Conclude with `hv1 _ (hst b a u hu)`.

Establish `hb2 : S'ᗮ ⊓ S ≠ ⊥`. Introduce `h`. Establish `h2` using `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle`. Rewrite `h2` using `[h, sup_bot_eq]`. Conclude with `hne h2`.

Take `⟨θ, y, hy, hy0, hw, -⟩` from `exists_singular_maximal_vector _ _ Et hgl S' hst hb`. Take `⟨θ', y', hy', hy0', hw', -⟩` from `exists_singular_maximal_vector _ _ Et hgl _ hst2 hb2`. Take `⟨t, ht⟩` from `hprop θ y θ' y' (hle hy) hy0 hw hy'.2 hy0' hw'`. Establish `hmem : y' ∈ S'` using `ht ▸ S'.smul_mem t hy`. Establish `hy1 : y' ∈ S'ᗮ` using `hy'.1`.

Conclude with `hy0' (inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hy1 y' hmem))`. Use `⟨hstab, hirr, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : S = ⊥`. Rewrite using `[hb]`. Conclude with `bot_le`.

Take `⟨θ, y, hy, hy0, hw, -⟩` from `exists_singular_maximal_vector _ _ Et hgl S hstab hb`. Take `⟨-, -, h3⟩` from `hkey θ y hy hy0 hw`. Establish `hyc : y ∈ CapSp Et (shf β (Function.update L l (L l + 1)))`. Rewrite using `[mem_CapSp]`. Introduce `w`.

Rewrite using `[qDetHW _ _ Et θ y hgl hw w, h3]`. Use `congr 1`. Unfold `cpol shf`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = l`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hk]`. Establish `hst3 : Stab Et (CapSp Et (shf β (Function.update L l (L l + 1))) ⊓ S)` using `fun a b v hv => ⟨(capelli_stabilizer _ _ Et _ hgl).1 a b v hv.1, hstab a b v hv.2⟩`.

Break down `hirr _ inf_le_right hst3 with h | h` into its components or cases. Conclude with `absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hyc, hy⟩ : y ∈ _ ⊓ S))) hy0`. Conclude with `h ▸ inf_le_left`.
-/
theorem splitCasimir_eigenspace_irreducible_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + 0)) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + 0) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + 0)) ∧ Module.End.eigenspace Om (β + L l + 0) ≤ CapSp Et (shf β (Function.update L l (L l + 1))) := by
  classical
  intro V _ _ _ n E Et Om β L l hyp hadj hEt hOm
  obtain ⟨hgl, hadjt, -, hcomm⟩ :=
    tensorStd_rel_adjoint_splitCasimir V n E Et Om hyp.gl hadj hEt hOm
  set S := Module.End.eigenspace Om (β + L l + 0) with hS
  have hmemS : ∀ y, y ∈ S ↔ Om y = (β + L l + 0) • y := fun y => Module.End.mem_eigenspace_iff
  have hstab : Stab Et S := by
    intro a b v hv
    rw [hmemS] at hv ⊢
    have h := LinearMap.congr_fun (hcomm a b) v
    simp only [Module.End.mul_apply] at h
    rw [h, hv, map_smul]
  have hcapV : ∀ v, v ∈ CapSp E (shf β L) := fun v => mem_CapSp.2 fun w => hyp.cap w v
  have hsdec : SDec (shf β L) := by
    intro a b hab
    have h := hyp.anti hab
    refine ⟨(L a - L b - 1).toNat, ?_⟩
    have h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h2
    rw [h3]
    simp only [shf]
    ring
  have hwtV : ∀ ν v, v ≠ 0 → IsHW E ν v → ∀ j, ν j = β + L j + ((j : ℕ) : ℂ) := by
    intro ν v hv hw j
    have hne : CapSp E (shf β L) ≠ ⊥ := fun h =>
      hv ((Submodule.mem_bot ℂ).1 (h ▸ hcapV v))
    exact (capelli_singular V (n + 1) E _ hyp.gl hne).2 hsdec ν v (hcapV v) hv hw j
  have hkey : ∀ θ y, y ∈ S → y ≠ 0 → IsHW Et θ y →
      y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧
        θ = fun j => β + L j + ((j : ℕ) : ℂ) + if j = l then 1 else 0 := by
    intro θ y hy hy0 hw
    obtain ⟨c, hc0, hcw, hlam⟩ := highestWeight_tensor_standard V n E Et Om θ _ y hEt hOm hy0 hw
      ((hmemS y).1 hy)
    have hν := hwtV _ _ hc0 hcw
    have hcl : c = l := by
      have h1 := hν c
      simp only [if_true] at h1
      have h2 : (L c : ℂ) = L l := by linear_combination -h1 - hlam
      exact hyp.anti.injective (by exact_mod_cast h2)
    subst hcl
    refine ⟨hc0, ?_, ?_⟩
    · rw [← funext hν]; exact hcw
    · funext j
      rw [← hν j]; ring
  have hsub : ∀ ν v, IsHW E ν v → IsHW (subA E) (fun j => ν j.castSucc) v := by
    intro ν v hw
    exact ⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (by simpa using hab)⟩
  have hprop : ∀ θ y θ' y', y ∈ S → y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' →
      ∃ t : ℂ, y' = t • y := by
    intro θ y θ' y' hy hy0 hw hy' hy0' hw'
    obtain ⟨h1, h2, h3⟩ := hkey θ y hy hy0 hw
    obtain ⟨-, h2', h3'⟩ := hkey θ' y' hy' hy0' hw'
    have hθ : θ' = θ := h3'.trans h3.symm
    rw [hθ] at hw'
    obtain ⟨t, ht⟩ := multiplicity_one V n E _ (y l) (y' l) hyp.gl hyp.irr (hsub _ _ h2)
      (hsub _ _ h2') h1
    refine ⟨t, ?_⟩
    by_contra hne
    have hz0 : y' - t • y ≠ 0 := sub_ne_zero.2 hne
    have hzw : IsHW Et θ (y' - t • y) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · rw [map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]
      · rw [map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab]; simp
    apply (hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) hz0 hzw).1
    simp [ht]
  have hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' →
      S' = ⊥ ∨ S' = S := by
    intro S' hle hst
    by_contra hcon
    push_neg at hcon
    obtain ⟨hb, hne⟩ := hcon
    have hst2 : Stab Et (S'ᗮ ⊓ S) := by
      intro a b v hv
      refine ⟨?_, hstab a b v hv.2⟩
      have hv1 : v ∈ S'ᗮ := hv.1
      change Et a b v ∈ S'ᗮ
      rw [Submodule.mem_orthogonal] at hv1 ⊢
      intro u hu
      rw [← hadjt]
      exact hv1 _ (hst b a u hu)
    have hb2 : S'ᗮ ⊓ S ≠ ⊥ := by
      intro h
      have h2 := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
      rw [h, sup_bot_eq] at h2
      exact hne h2
    obtain ⟨θ, y, hy, hy0, hw, -⟩ := exists_singular_maximal_vector _ _ Et hgl S' hst hb
    obtain ⟨θ', y', hy', hy0', hw', -⟩ := exists_singular_maximal_vector _ _ Et hgl _ hst2 hb2
    obtain ⟨t, ht⟩ := hprop θ y θ' y' (hle hy) hy0 hw hy'.2 hy0' hw'
    have hmem : y' ∈ S' := ht ▸ S'.smul_mem t hy
    have hy1 : y' ∈ S'ᗮ := hy'.1
    exact hy0' (inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hy1 y' hmem))
  refine ⟨hstab, hirr, ?_⟩
  by_cases hb : S = ⊥
  · rw [hb]; exact bot_le
  obtain ⟨θ, y, hy, hy0, hw, -⟩ := exists_singular_maximal_vector _ _ Et hgl S hstab hb
  obtain ⟨-, -, h3⟩ := hkey θ y hy hy0 hw
  have hyc : y ∈ CapSp Et (shf β (Function.update L l (L l + 1))) := by
    rw [mem_CapSp]
    intro w
    rw [qDetHW _ _ Et θ y hgl hw w, h3]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : k = l
    · subst hk; simp; ring
    · simp [hk]
  have hst3 : Stab Et (CapSp Et (shf β (Function.update L l (L l + 1))) ⊓ S) := fun a b v hv =>
    ⟨(capelli_stabilizer _ _ Et _ hgl).1 a b v hv.1, hstab a b v hv.2⟩
  rcases hirr _ inf_le_right hst3 with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hyc, hy⟩ : y ∈ _ ⊓ S))) hy0
  · exact h ▸ inf_le_left

end GlobalTheory
