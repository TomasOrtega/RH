import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Conclude with `entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hM.2) i j`.
-/
theorem inK_entry_le (M : M2 n) (hM : InK M) (i j : Fin n ⊕ Fin n) : ‖M i j‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hM.2) i j

/- English proof (translation)
Establish `hB : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `hB.of_isClosed_subset ?_ ?_` and prove the remaining obligations. Establish `c1 : Continuous fun M : M2 n => Mᴴ * JJ n * M` using `(continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id`. Establish `c2 : Continuous fun M : M2 n => Mᴴ * M` using `continuous_id.matrix_conjTranspose.matrix_mul continuous_id`. Conclude with `(isClosed_eq c1 continuous_const).inter (isClosed_eq c2 continuous_const)`.

Introduce `M hM`. Simplify using `only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]`. Introduce `i j`. Conclude with `inK_entry_le M hM i j`.
-/
theorem isCompact_inK : IsCompact {M : M2 n | InK M} := by
  have hB : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset ?_ ?_
  · have c1 : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
    have c2 : Continuous fun M : M2 n => Mᴴ * M := continuous_id.matrix_conjTranspose.matrix_mul continuous_id
    exact (isClosed_eq c1 continuous_const).inter (isClosed_eq c2 continuous_const)
  · intro M hM
    simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact inK_entry_le M hM i j

def embK (k : KR n) : M2 n × (M2 n)ᵐᵒᵖ := Units.embedProduct (M2 n) (k : GR n).1

/- English proof (translation)
The claim follows from `Units.isEmbedding_embedProduct.comp (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)`.
-/
theorem isEmbedding_embK : Topology.IsEmbedding (embK (n := n)) :=
  Units.isEmbedding_embedProduct.comp (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)

/- English proof (translation)
Use extensionality with `⟨A, B⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Establish `hK : InK (mR (k : GR n))` using `k.2`. Establish `hinv : ((((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) = (mR (k : GR n))ᴴ` using `Units.inv_eq_of_mul_eq_one_left hK.2`.

Use `⟨mR (k : GR n), hK, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk]`. Simplify using `only [embK, Units.embedProduct_apply, hinv]`. Both sides reduce to the same expression. Introduce and unpack `⟨M, hM, hMAB⟩`.

Establish `hM' : M * Mᴴ = 1` using `mul_eq_one_comm.1 hM.2`. Set `u : GL (Fin n ⊕ Fin n) ℂ` to `⟨M, Mᴴ, hM', hM.2⟩`. Set `g : GR n` to `⟨u, hM.1⟩`. Establish `hg : g ∈ KR n` using `hM`. Use `⟨⟨g, hg⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hMAB]`. Both sides reduce to the same expression.
-/
theorem range_embK : Set.range (embK (n := n)) = (fun M : M2 n => (M, MulOpposite.op Mᴴ)) '' {M | InK M} := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨k, hk⟩
    have hK : InK (mR (k : GR n)) := k.2
    have hinv : ((((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) =
        (mR (k : GR n))ᴴ :=
      Units.inv_eq_of_mul_eq_one_left hK.2
    refine ⟨mR (k : GR n), hK, ?_⟩
    rw [← hk]
    simp only [embK, Units.embedProduct_apply, hinv]
    rfl
  · rintro ⟨M, hM, hMAB⟩
    have hM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hM.2
    let u : GL (Fin n ⊕ Fin n) ℂ := ⟨M, Mᴴ, hM', hM.2⟩
    let g : GR n := ⟨u, hM.1⟩
    have hg : g ∈ KR n := hM
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [← hMAB]
    rfl

/- English proof (translation)
Rewrite using `[isEmbedding_embK.isCompact_iff, Set.image_univ, range_embK]`. Conclude with `isCompact_inK.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose))`.
-/
theorem isCompact_KR : IsCompact (univ : Set (KR n)) := by
  rw [isEmbedding_embK.isCompact_iff, Set.image_univ, range_embK]
  exact isCompact_inK.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose))

end PositivityTheory.Rg.Sw.AbsSt
