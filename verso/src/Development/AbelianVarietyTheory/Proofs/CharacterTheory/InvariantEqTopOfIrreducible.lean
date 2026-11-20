import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentral
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

/- English proof (translation)
Break down `h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H` into its components or cases. Establish `H' : U = ⊥` using `congrArg Subrepresentation.toSubmodule H`. Conclude with `absurd (by simpa [H'] using hv) hv0`. Conclude with `congrArg Subrepresentation.toSubmodule H`.
-/
theorem invariant_eq_top_of_irreducible {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H
  · have H' : U = ⊥ := congrArg Subrepresentation.toSubmodule H
    exact absurd (by simpa [H'] using hv) hv0
  · exact congrArg Subrepresentation.toSubmodule H

/- English proof (translation)
Introduce `k _ G _ _ V _ _ _ ρ _ hG hirr`. Use `haveI : Nontrivial V := by`. Establish `h1 : (⊥ : Subrepresentation ρ) ≠ ⊤` using `bot_ne_top`. Establish `h2 : (⊥ : Submodule k V) ≠ ⊤` using `fun H => h1 (Subrepresentation.ext H)`. Conclude with `(Submodule.nontrivial_iff k).1 ⟨_, _, h2⟩`.

Distinguish the cases in `hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a`. Use `left`. Take `⟨v, hv0, hv⟩` from `GlobalTheory.exists_common_eigenvector_of_commute (fun g : G => ρ g) hc`. Establish `htop` using `invariant_eq_top_of_irreducible ρ hirr (Submodule.span k {v}) (by`. Introduce `g w hw`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Take `⟨m, hm⟩` from `hv g`. Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hm' : ρ g v = m • v` using `hm`.

Rewrite using `[hm']`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))`. Use `v (Submodule.mem_span_singleton_self v) hv0`. Rewrite using `[← finrank_top, ← htop, finrank_span_singleton hv0]`. Use `right`.

Establish `hB : ¬ ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) → ∀ b ∈ B, ∀ g : G, ρ b * ρ g = ρ g * ρ b` using `fun H => hc (commute_all G _ ρ hG H)`. Use `push Not at hB`. Take `⟨B, hBn, hBc, b₀, hb₀, g₀, hne⟩` from `hB`. Take `⟨v, hv0, hv⟩` from `GlobalTheory.exists_common_eigenvector_of_commute (fun b : B => ρ b) (fun a b => hBc a a.2 b b.2)`. Use `choose μ hμ using hv`.

Set `c : G →* MulAut B` to `MulAut.conjNormal`. Establish `hcv : ∀ (g : G) (b : B), ((c g b : B) : G) = g * b * g⁻¹` using `fun g b => rfl`. Set `E : (B → k) → Submodule k V` to `fun χ => ⨅ b : B, Module.End.eigenspace (ρ b) (χ b)`. Establish `hE : ∀ χ w, w ∈ E χ ↔ ∀ b : B, ρ b w = χ b • w`. Introduce `χ w`.

Simplify using `only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Establish `hind : iSupIndep E` using `(Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => ρ b) fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hBc j j.2 i i.2) φ).mono fun _ => iInf_mono fun i => (Module.End.genEigenspace (ρ i) _).monotone le_top`. Establish `hmap : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ E (fun b => μ (c g⁻¹ b))`. Introduce `g w hw`. Rewrite `hw`, the goal using `[hE]`.

Introduce `b`. Rewrite using `[← map_smul, ← hw, hcv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Use `group`. Set `T : Subgroup G` to `{ carrier := {g | ∀ b, μ (c g b) = μ b} one_mem' := fun b => by simp mul_mem' := fun {x y} hx hy b => by`.

Rewrite using `[map_mul, MulAut.mul_apply, hx, hy]`. Use the proof step `inv_mem' := fun {x} hx b => by`. Rewrite using `[← hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }`. Establish `hT : ∀ g, g ∈ T ↔ ∀ b, μ (c g b) = μ b` using `fun g => Iff.rfl`. Establish `hstab : ∀ t ∈ T, ∀ w ∈ E μ, ρ t w ∈ E μ`.

Introduce `t ht w hw`. Establish `h1` using `hmap t w hw`. Establish `h2 : (fun b => μ (c t⁻¹ b)) = μ` using `funext ((hT _).1 (T.inv_mem ht))`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Establish `hvE : v ∈ E μ` using `(hE _ _).2 hμ`.

Use `⟨T, E μ, ?_, hstab, ?_, ?_⟩` and prove the remaining obligations. Introduce `hTop`. Establish `htop` using `invariant_eq_top_of_irreducible ρ hirr (E μ) (fun g w hw => hstab g (hTop ▸ Subgroup.mem_top g) w hw) v hvE hv0`. Establish `hs : ∀ w, ρ b₀ w = μ ⟨b₀, hb₀⟩ • w` using `fun w => (hE μ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩`. Apply `hne` to reduce the goal to its premises.

Use extensionality with `w`. Simplify using `only [Module.End.mul_apply, hs, map_smul]`. Establish `hinj : Function.Injective fun q : G ⧸ T => fun b => μ (c q.out⁻¹ b)`. Introduce `q q' hq`. Rewrite using `[← q.out_eq, ← q'.out_eq]`.

Use `QuotientGroup.eq.2 ((hT _).2 fun b => ?_)` and prove the remaining obligations. Establish `h1 : μ (c q.out⁻¹ (c q'.out b)) = μ (c q'.out⁻¹ (c q'.out b))` using `congrFun hq _`. Rewrite using `[map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]`. Use `(hind.comp hinj).mono fun q => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Conclude with `hmap _ w hw`. Establish `hmem : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ ⨆ q : G ⧸ T, (E μ).map (ρ q.out)`. Introduce `g w hw`. Take `⟨t, ht⟩` from `QuotientGroup.mk_out_eq_mul T g`. Use `Submodule.mem_iSup_of_mem (g : G ⧸ T) ⟨ρ (t⁻¹ : G) w, hstab _ (T.inv_mem t.2) w hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[ht, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]`. Use `invariant_eq_top_of_irreducible ρ hirr _ ?_ v (by simpa using hmem 1 v hvE) hv0` and prove the remaining obligations. Introduce `g w hw`. Establish `hle : (⨆ q : G ⧸ T, (E μ).map (ρ q.out)) ≤ (⨆ q : G ⧸ T, (E μ).map (ρ q.out)).comap (ρ g)`. Use `iSup_le fun q => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, hu, rfl⟩`. Rewrite using `[Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]`. Conclude with `hmem _ u hu`. Conclude with `hle hw`.
-/
theorem finrank_eq_one_or_imprimitive : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → ρ.IsIrreducible → Module.finrank k V = 1 ∨ ∃ (T : Subgroup G) (W : Submodule k V), T ≠ ⊤ ∧ (∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W) ∧ iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)) ∧ ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤ := by
  intro k _ G _ _ V _ _ _ ρ _ hG hirr
  haveI : Nontrivial V := by
    have h1 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    have h2 : (⊥ : Submodule k V) ≠ ⊤ := fun H => h1 (Subrepresentation.ext H)
    exact (Submodule.nontrivial_iff k).1 ⟨_, _, h2⟩
  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · left
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun g : G => ρ g) hc
    have htop := invariant_eq_top_of_irreducible ρ hirr (Submodule.span k {v}) (by
      intro g w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      obtain ⟨m, hm⟩ := hv g
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hm' : ρ g v = m • v := hm
      rw [hm']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      v (Submodule.mem_span_singleton_self v) hv0
    rw [← finrank_top, ← htop, finrank_span_singleton hv0]
  right
  have hB : ¬ ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) →
      ∀ b ∈ B, ∀ g : G, ρ b * ρ g = ρ g * ρ b := fun H => hc (commute_all G _ ρ hG H)
  push Not at hB
  obtain ⟨B, hBn, hBc, b₀, hb₀, g₀, hne⟩ := hB
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun b : B => ρ b)
    (fun a b => hBc a a.2 b b.2)
  choose μ hμ using hv
  let c : G →* MulAut B := MulAut.conjNormal
  have hcv : ∀ (g : G) (b : B), ((c g b : B) : G) = g * b * g⁻¹ := fun g b => rfl
  let E : (B → k) → Submodule k V := fun χ => ⨅ b : B, Module.End.eigenspace (ρ b) (χ b)
  have hE : ∀ χ w, w ∈ E χ ↔ ∀ b : B, ρ b w = χ b • w := by
    intro χ w
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hind : iSupIndep E :=
    (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => ρ b)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hBc j j.2 i i.2) φ).mono fun _ =>
        iInf_mono fun i => (Module.End.genEigenspace (ρ i) _).monotone le_top
  have hmap : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ E (fun b => μ (c g⁻¹ b)) := by
    intro g w hw
    rw [hE] at hw ⊢
    intro b
    rw [← map_smul, ← hw, hcv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul]
    congr 2
    group
  let T : Subgroup G :=
    { carrier := {g | ∀ b, μ (c g b) = μ b}
      one_mem' := fun b => by simp
      mul_mem' := fun {x y} hx hy b => by
        rw [map_mul, MulAut.mul_apply, hx, hy]
      inv_mem' := fun {x} hx b => by
        rw [← hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }
  have hT : ∀ g, g ∈ T ↔ ∀ b, μ (c g b) = μ b := fun g => Iff.rfl
  have hstab : ∀ t ∈ T, ∀ w ∈ E μ, ρ t w ∈ E μ := by
    intro t ht w hw
    have h1 := hmap t w hw
    have h2 : (fun b => μ (c t⁻¹ b)) = μ := funext ((hT _).1 (T.inv_mem ht))
    rwa [h2] at h1
  have hvE : v ∈ E μ := (hE _ _).2 hμ
  refine ⟨T, E μ, ?_, hstab, ?_, ?_⟩
  · intro hTop
    have htop := invariant_eq_top_of_irreducible ρ hirr (E μ)
      (fun g w hw => hstab g (hTop ▸ Subgroup.mem_top g) w hw) v hvE hv0
    have hs : ∀ w, ρ b₀ w = μ ⟨b₀, hb₀⟩ • w := fun w =>
      (hE μ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
    apply hne
    ext w
    simp only [Module.End.mul_apply, hs, map_smul]
  · have hinj : Function.Injective fun q : G ⧸ T => fun b => μ (c q.out⁻¹ b) := by
      intro q q' hq
      rw [← q.out_eq, ← q'.out_eq]
      refine QuotientGroup.eq.2 ((hT _).2 fun b => ?_)
      have h1 : μ (c q.out⁻¹ (c q'.out b)) = μ (c q'.out⁻¹ (c q'.out b)) := congrFun hq _
      rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    refine (hind.comp hinj).mono fun q => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hmap _ w hw
  · have hmem : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ ⨆ q : G ⧸ T, (E μ).map (ρ q.out) := by
      intro g w hw
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T g
      refine Submodule.mem_iSup_of_mem (g : G ⧸ T) ⟨ρ (t⁻¹ : G) w, hstab _ (T.inv_mem t.2) w hw, ?_⟩
      rw [ht, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    refine invariant_eq_top_of_irreducible ρ hirr _ ?_ v (by simpa using hmem 1 v hvE) hv0
    intro g w hw
    have hle : (⨆ q : G ⧸ T, (E μ).map (ρ q.out)) ≤
        (⨆ q : G ⧸ T, (E μ).map (ρ q.out)).comap (ρ g) := by
      refine iSup_le fun q => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact hmem _ u hu
    exact hle hw

end GlobalTheory.BI
