import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubFamilyTwistPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Take `⟨sF, hsF⟩` from `hF`. Take `⟨sQ, hsQ⟩` from `hQ`. Use `⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Rewrite `hz` using `[Finset.coe_image₂]`. Take `⟨q, hq, y, hy, rfl⟩` from `hz`. Conclude with `Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩`. Express the relevant statement in the definitionally equal form `Submodule.span _ _ ≤ _`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`. Rewrite `hq` using `[← hsQ]`. Rewrite `hy` using `[← hsF]`. Use `Submodule.span_induction (p := fun q _ => q • y ∈ Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq` and prove the remaining obligations.

Introduce `q hq`. Use `Submodule.span_induction (p := fun y _ => q • y ∈ Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce `y hy`. Conclude with `Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a z _ hz`.

Rewrite using `[Subalgebra.smul_def, smul_comm]`. Conclude with `Submodule.smul_mem _ a hz`. Rewrite using `[zero_smul]`. Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`.

Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a q _ hq`. Rewrite using `[smul_assoc]`. Conclude with `Submodule.smul_mem _ a hq`.
-/
theorem SubSystem.twist_sub_fg (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by
  obtain ⟨sF, hsF⟩ := hF
  obtain ⟨sQ, hsQ⟩ := hQ
  classical
  refine ⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Finset.coe_image₂] at hz
    obtain ⟨q, hq, y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩
  · change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hsQ] at hq
    rw [← hsF] at hy
    refine Submodule.span_induction (p := fun q _ => q • y ∈
      Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq
    · intro q hq
      refine Submodule.span_induction (p := fun y _ => q • y ∈
        Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)
      · rw [smul_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        rw [Subalgebra.smul_def, smul_comm]
        exact Submodule.smul_mem _ a hz
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq
      rw [smul_assoc]
      exact Submodule.smul_mem _ a hq

end

/- English proof (translation)
Introduce `S _ Ω _ _ N x E _ _ _ _ F Q hF`. Conclude with `⟨F.twistFam Q.toSubFamily, rfl, fun I => SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩`.
-/
theorem SubFamilyTwist.proof : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
