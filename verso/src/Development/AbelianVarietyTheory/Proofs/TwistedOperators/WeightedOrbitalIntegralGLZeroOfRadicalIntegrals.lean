import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralEqZeroOfNormalisedCosetIntegralsStatement
open MeasureTheory GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

/- English proof (translation)
Establish `hX` using `(hN a).1 ha`. Establish `hY` using `(hN b).1 hb`. Establish `h0 : (1 - ε) * ε = 0` using `by rw [sub_mul, one_mul, hε, sub_self]`. Establish `hXY : (a.1 - 1) * (b.1 - 1) = 0`. Rewrite using `[← hX, ← hY]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hYX : (b.1 - 1) * (a.1 - 1) = 0`. Rewrite using `[← hX, ← hY]`. Combine the equalities or inequalities in the displayed calculation. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul, ← sub_eq_zero]`. Establish `: a.1 * b.1 - b.1 * a.1 = (a.1 - 1) * (b.1 - 1) - (b.1 - 1) * (a.1 - 1)` using `by noncomm_ring`. Rewrite using `[this, hXY, hYX, sub_self]`.
-/
theorem mul_comm_of_mem {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {a b : GL (Fin r) k} (ha : a ∈ N) (hb : b ∈ N) :
    a * b = b * a := by
  have hX := (hN a).1 ha
  have hY := (hN b).1 hb
  have h0 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  have hXY : (a.1 - 1) * (b.1 - 1) = 0 := by
    rw [← hX, ← hY]
    calc ε * (a.1 - 1) * (1 - ε) * (ε * (b.1 - 1) * (1 - ε))
        = ε * (a.1 - 1) * ((1 - ε) * ε) * (b.1 - 1) * (1 - ε) := by simp only [mul_assoc]
      _ = 0 := by rw [h0]; simp
  have hYX : (b.1 - 1) * (a.1 - 1) = 0 := by
    rw [← hX, ← hY]
    calc ε * (b.1 - 1) * (1 - ε) * (ε * (a.1 - 1) * (1 - ε))
        = ε * (b.1 - 1) * ((1 - ε) * ε) * (a.1 - 1) * (1 - ε) := by simp only [mul_assoc]
      _ = 0 := by rw [h0]; simp
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ← sub_eq_zero]
  have : a.1 * b.1 - b.1 * a.1 = (a.1 - 1) * (b.1 - 1) - (b.1 - 1) * (a.1 - 1) := by noncomm_ring
  rw [this, hXY, hYX, sub_self]

/- English proof (translation)
Establish `h0 : (1 - ε) * ε = 0` using `by rw [sub_mul, one_mul, hε, sub_self]`. Establish `h1 : (M - 1) * ε = 0`. Rewrite using `[← hM, mul_assoc, h0, mul_zero]`. Establish `h2 : (1 - ε) * (M - 1) = 0`. Rewrite using `[← hM, ← mul_assoc, ← mul_assoc, h0, zero_mul, zero_mul]`.

Prove the components needed by the constructor for the conclusion. Establish `: M * ε = (M - 1) * ε + ε` using `by noncomm_ring`. Rewrite using `[this, h1, zero_add]`. Establish `: (1 - ε) * M = (1 - ε) * (M - 1) + (1 - ε)` using `by noncomm_ring`. Rewrite using `[this, h2, zero_add]`.
-/
theorem mul_idem_eq {ε M : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) (hM : ε * (M - 1) * (1 - ε) = M - 1) :
    M * ε = ε ∧ (1 - ε) * M = 1 - ε := by
  have h0 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  have h1 : (M - 1) * ε = 0 := by
    rw [← hM, mul_assoc, h0, mul_zero]
  have h2 : (1 - ε) * (M - 1) = 0 := by
    rw [← hM, ← mul_assoc, ← mul_assoc, h0, zero_mul, zero_mul]
  constructor
  · have : M * ε = (M - 1) * ε + ε := by noncomm_ring
    rw [this, h1, zero_add]
  · have : (1 - ε) * M = (1 - ε) * (M - 1) + (1 - ε) := by noncomm_ring
    rw [this, h2, zero_add]

def diagPart (ε A : Matrix (Fin r) (Fin r) k) : Matrix (Fin r) (Fin r) k := ε * A * ε + (1 - ε) * A * (1 - ε)

/- English proof (translation)
Take `⟨h1, h2⟩` from `mul_idem_eq hε hM`. Establish `hA' : A * (1 - ε) = (1 - ε) * A` using `by rw [mul_sub, sub_mul, mul_one, one_mul, hA]`. Establish `hε' : (1 - ε) * (1 - ε) = 1 - ε`. Rewrite using `[sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]`. Establish `h3 : ε * M * ε = ε` using `by rw [mul_assoc, h1, hε]`.

Establish `hAε : ε * A = A * ε` using `hA.symm`. Establish `hA'' : (1 - ε) * A = A * (1 - ε)` using `hA'.symm`. Prove the components needed by the constructor for the conclusion. Establish `s1 : ε * (M * A) * ε = ε * A`. Combine the equalities or inequalities in the displayed calculation.

Establish `s2 : (1 - ε) * (M * A) * (1 - ε) = (1 - ε) * A`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[diagPart, s1, s2]`. Use `noncomm_ring`. Establish `s1 : ε * (A * M) * ε = A * ε`.

Combine the equalities or inequalities in the displayed calculation. Establish `s2 : (1 - ε) * (A * M) * (1 - ε) = A * (1 - ε)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[diagPart, s1, s2]`. Use `noncomm_ring`.
-/
theorem diagPart_mul {ε M A : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) (hM : ε * (M - 1) * (1 - ε) = M - 1)
    (hA : A * ε = ε * A) : diagPart ε (M * A) = A ∧ diagPart ε (A * M) = A := by
  obtain ⟨h1, h2⟩ := mul_idem_eq hε hM
  have hA' : A * (1 - ε) = (1 - ε) * A := by rw [mul_sub, sub_mul, mul_one, one_mul, hA]
  have hε' : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]
  have h3 : ε * M * ε = ε := by rw [mul_assoc, h1, hε]
  have hAε : ε * A = A * ε := hA.symm
  have hA'' : (1 - ε) * A = A * (1 - ε) := hA'.symm
  constructor
  · have s1 : ε * (M * A) * ε = ε * A := by
      calc ε * (M * A) * ε = ε * M * (A * ε) := by simp only [mul_assoc]
        _ = ε * (M * ε) * A := by rw [hA]; simp only [mul_assoc]
        _ = ε * A := by rw [h1, hε]
    have s2 : (1 - ε) * (M * A) * (1 - ε) = (1 - ε) * A := by
      calc (1 - ε) * (M * A) * (1 - ε) = (1 - ε) * M * (A * (1 - ε)) := by simp only [mul_assoc]
        _ = (1 - ε) * M * (1 - ε) * A := by rw [hA']; simp only [mul_assoc]
        _ = (1 - ε) * A := by rw [h2, hε']
    rw [diagPart, s1, s2]
    noncomm_ring
  · have s1 : ε * (A * M) * ε = A * ε := by
      calc ε * (A * M) * ε = (ε * A) * M * ε := by simp only [mul_assoc]
        _ = A * (ε * M * ε) := by rw [hAε]; simp only [mul_assoc]
        _ = A * ε := by rw [h3]
    have s2 : (1 - ε) * (A * M) * (1 - ε) = A * (1 - ε) := by
      calc (1 - ε) * (A * M) * (1 - ε) = ((1 - ε) * A) * M * (1 - ε) := by simp only [mul_assoc]
        _ = A * ((1 - ε) * M * (1 - ε)) := by rw [hA'']; simp only [mul_assoc]
        _ = A * (1 - ε) := by rw [h2, hε']
    rw [diagPart, s1, s2]
    noncomm_ring

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

/- English proof (translation)
The claim follows from `(((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).add ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)`.
-/
theorem continuous_diagPart [TopologicalSpace k] [IsTopologicalRing k] (ε : Matrix (Fin r) (Fin r) k) :
    Continuous (diagPart ε) :=
  (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

/- English proof (translation)
Establish `hdiag : ∀ (n : N) (t : T), diagPart ε ((n : GL (Fin r) k) * t).1 = (t : GL (Fin r) k).1 ∧ diagPart ε ((n : GL (Fin r) k) * t)⁻¹.1 = (t : GL (Fin r) k)⁻¹.1` using `fun n t => by`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Units.val_mul]`. Conclude with `(diagPart_mul hε ((hN _).1 n.2) (hTε _ t.2)).1`. Rewrite using `[mul_inv_rev, Units.val_mul]`.

Conclude with `(diagPart_mul hε ((hN _).1 (inv_mem n.2)) (hTε _ (inv_mem t.2))).2`. Establish `hD` using `continuous_diagPart ε`. Establish `hm : Continuous (fun p : N × T => (p.1 : GL (Fin r) k) * p.2)` using `by fun_prop`. Set `F : GL (Fin r) k → GL (Fin r) k × (Matrix (Fin r) (Fin r) k × (Matrix (Fin r) (Fin r) k)ᵐᵒᵖ)` to `fun g => (g, diagPart ε g.1, MulOpposite.op (diagPart ε g⁻¹.1))`. Establish `hF : Continuous F` using `continuous_id.prodMk ((hD.comp Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hD.comp Units.continuous_coe_inv)))`.

Establish `hFm : F ∘ (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) = Prod.map id (Units.embedProduct (Matrix (Fin r) (Fin r) k)) ∘ (fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) ∘ Prod.map Subtype.val Subtype.val`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, F, Prod.map_apply, id_eq, Units.embedProduct_apply, (hdiag p.1 p.2).1, (hdiag p.1 p.2).2]`. Both sides reduce to the same expression. Establish `hΦ : Topology.IsInducing (fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2))`.

Use `Topology.IsInducing.of_comp (g := fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2⁻¹, q.2)) (by fun_prop) (by fun_prop) ?_` and prove the remaining obligations. Establish `: ((fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2⁻¹, q.2)) ∘ fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) = id`. Use function extensionality and compare the values at `q`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Topology.IsInducing.id`. Establish `hind : Topology.IsInducing (fun p : N × T => (p.1 : GL (Fin r) k) * p.2)`. Use `Topology.IsInducing.of_comp hm hF ?_` and prove the remaining obligations. Rewrite using `[hFm]`. Conclude with `(Topology.IsInducing.id.prodMap Units.isEmbedding_embedProduct.isInducing).comp (hΦ.comp (Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal))`.

Establish `hinj : Function.Injective (fun p : N × T => (p.1 : GL (Fin r) k) * p.2)`. Introduce `p q h`. Simplify using `only at h`. Establish `ht : (p.2 : GL (Fin r) k) = q.2` using `Units.ext (by rw [← (hdiag p.1 p.2).1, ← (hdiag q.1 q.2).1, h])`. Establish `hn : (p.1 : GL (Fin r) k) = q.1` using `by rw [ht] at h; exact mul_right_cancel h`.

Conclude with `Prod.ext (Subtype.ext hn) (Subtype.ext ht)`. Establish `hrange : Set.range (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) = (fun g : GL (Fin r) k => (diagPart ε g.1, MulOpposite.op (diagPart ε g⁻¹.1))) ⁻¹' (Units.embedProduct (Matrix (Fin r) (Fin r) k) '' (T : Set (GL (Fin r) k))) ∩ {g | ε * (g.1 * diagPart ε g⁻¹.1 - 1) * (1 - ε) = g.1 …`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨n, t⟩, rfl⟩`.

Use `⟨⟨t, t.2, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Units.embedProduct_apply, (hdiag n t).1, (hdiag n t).2]`. Simplify using `only [Set.mem_setOf_eq, (hdiag n t).2]`. Rewrite using `[← Units.val_mul, mul_inv_cancel_right]`. Conclude with `(hN _).1 n.2`.

Introduce and unpack `⟨⟨t, ht, he⟩, hg⟩`. Simplify using `only [Units.embedProduct_apply, Prod.mk.injEq, MulOpposite.op_inj] at he`. Simplify using `only [Set.mem_setOf_eq, ← he.2, ← Units.val_mul] at hg`. Conclude with `⟨(⟨g * t⁻¹, (hN _).2 hg⟩, ⟨t, ht⟩), by simp⟩`. Use `⟨⟨hind, hinj⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrange]`. Use `IsClosed.inter ((Units.isClosedEmbedding_embedProduct.isClosedMap _ hT).preimage ?_) ?_` and prove the remaining obligations. Conclude with `(hD.comp Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hD.comp Units.continuous_coe_inv))`. Conclude with `isClosed_eq (by fun_prop) (by fun_prop)`.
-/
theorem isClosedEmbedding_mul [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N T : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) (hT : IsClosed (T : Set (GL (Fin r) k)))
    (hTε : ∀ t ∈ T, t.1 * ε = ε * t.1) :
    Topology.IsClosedEmbedding (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by
  have hdiag : ∀ (n : N) (t : T), diagPart ε ((n : GL (Fin r) k) * t).1 = (t : GL (Fin r) k).1 ∧
      diagPart ε ((n : GL (Fin r) k) * t)⁻¹.1 = (t : GL (Fin r) k)⁻¹.1 := fun n t => by
    constructor
    · rw [Units.val_mul]; exact (diagPart_mul hε ((hN _).1 n.2) (hTε _ t.2)).1
    · rw [mul_inv_rev, Units.val_mul]
      exact (diagPart_mul hε ((hN _).1 (inv_mem n.2)) (hTε _ (inv_mem t.2))).2
  have hD := continuous_diagPart ε
  have hm : Continuous (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by fun_prop
  let F : GL (Fin r) k → GL (Fin r) k × (Matrix (Fin r) (Fin r) k × (Matrix (Fin r) (Fin r) k)ᵐᵒᵖ) :=
    fun g => (g, diagPart ε g.1, MulOpposite.op (diagPart ε g⁻¹.1))
  have hF : Continuous F :=
    continuous_id.prodMk ((hD.comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp (hD.comp Units.continuous_coe_inv)))
  have hFm : F ∘ (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) =
      Prod.map id (Units.embedProduct (Matrix (Fin r) (Fin r) k)) ∘
        (fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) ∘ Prod.map Subtype.val Subtype.val := by
    funext p
    simp only [Function.comp_apply, F, Prod.map_apply, id_eq, Units.embedProduct_apply, (hdiag p.1 p.2).1,
      (hdiag p.1 p.2).2]
    rfl
  have hΦ : Topology.IsInducing (fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) := by
    refine Topology.IsInducing.of_comp (g := fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2⁻¹, q.2))
      (by fun_prop) (by fun_prop) ?_
    have : ((fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2⁻¹, q.2)) ∘
        fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) = id := by
      funext q; simp
    rw [this]; exact Topology.IsInducing.id
  have hind : Topology.IsInducing (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by
    refine Topology.IsInducing.of_comp hm hF ?_
    rw [hFm]
    exact (Topology.IsInducing.id.prodMap Units.isEmbedding_embedProduct.isInducing).comp
      (hΦ.comp (Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal))
  have hinj : Function.Injective (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by
    intro p q h
    simp only at h
    have ht : (p.2 : GL (Fin r) k) = q.2 :=
      Units.ext (by rw [← (hdiag p.1 p.2).1, ← (hdiag q.1 q.2).1, h])
    have hn : (p.1 : GL (Fin r) k) = q.1 := by rw [ht] at h; exact mul_right_cancel h
    exact Prod.ext (Subtype.ext hn) (Subtype.ext ht)
  have hrange : Set.range (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) =
      (fun g : GL (Fin r) k => (diagPart ε g.1, MulOpposite.op (diagPart ε g⁻¹.1))) ⁻¹'
          (Units.embedProduct (Matrix (Fin r) (Fin r) k) '' (T : Set (GL (Fin r) k))) ∩
        {g | ε * (g.1 * diagPart ε g⁻¹.1 - 1) * (1 - ε) = g.1 * diagPart ε g⁻¹.1 - 1} := by
    ext g
    constructor
    · rintro ⟨⟨n, t⟩, rfl⟩
      refine ⟨⟨t, t.2, ?_⟩, ?_⟩
      · simp only [Units.embedProduct_apply, (hdiag n t).1, (hdiag n t).2]
      · simp only [Set.mem_setOf_eq, (hdiag n t).2]
        rw [← Units.val_mul, mul_inv_cancel_right]
        exact (hN _).1 n.2
    · rintro ⟨⟨t, ht, he⟩, hg⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq, MulOpposite.op_inj] at he
      simp only [Set.mem_setOf_eq, ← he.2, ← Units.val_mul] at hg
      exact ⟨(⟨g * t⁻¹, (hN _).2 hg⟩, ⟨t, ht⟩), by simp⟩
  refine ⟨⟨hind, hinj⟩, ?_⟩
  rw [hrange]
  refine IsClosed.inter ((Units.isClosedEmbedding_embedProduct.isClosedMap _ hT).preimage ?_) ?_
  · exact (hD.comp Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hD.comp Units.continuous_coe_inv))
  · exact isClosed_eq (by fun_prop) (by fun_prop)

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

/- English proof (translation)
Establish `h0 : (1 - ε) * ε = 0` using `by rw [sub_mul, one_mul, hε, sub_self]`. Rewrite using `[← hX, ← hY]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = 0 := by rw [hA, ← mul_assoc (1 - ε), h0]; simp`.
-/
theorem mul_mul_eq_zero {ε X Y A : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) (hX : ε * X * (1 - ε) = X)
    (hY : ε * Y * (1 - ε) = Y) (hA : A * ε = ε * A) : X * A * Y = 0 := by
  have h0 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  rw [← hX, ← hY]
  calc ε * X * (1 - ε) * A * (ε * Y * (1 - ε)) = ε * X * ((1 - ε) * (A * ε)) * Y * (1 - ε) := by
        simp only [mul_assoc]
    _ = 0 := by rw [hA, ← mul_assoc (1 - ε), h0]; simp

/- English proof (translation)
Rewrite `hn`, the goal using `[hN]`. Establish `h1 : (s * n * s⁻¹).1 - 1 = s.1 * (n.1 - 1) * s⁻¹.1`. Rewrite using `[Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]`. Establish `h2 : s⁻¹.1 * ε = ε * s⁻¹.1` using `(Commute.units_inv_left (u := s) hs).eq`. Establish `h2' : s⁻¹.1 * (1 - ε) = (1 - ε) * s⁻¹.1` using `by rw [mul_sub, sub_mul, mul_one, one_mul, h2]`.

Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = s.1 * (ε * (n.1 - 1) * (1 - ε)) * s⁻¹.1 := by rw [← hs, h2']; simp only [mul_assoc]`. Use `_ = s.1 * (n.1 - 1) * s⁻¹.1 := by rw [hn]`.
-/
theorem conj_mem {ε : Matrix (Fin r) (Fin r) k} {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {s : GL (Fin r) k} (hs : s.1 * ε = ε * s.1)
    {n : GL (Fin r) k} (hn : n ∈ N) : s * n * s⁻¹ ∈ N := by
  rw [hN] at hn ⊢
  have h1 : (s * n * s⁻¹).1 - 1 = s.1 * (n.1 - 1) * s⁻¹.1 := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  have h2 : s⁻¹.1 * ε = ε * s⁻¹.1 := (Commute.units_inv_left (u := s) hs).eq
  have h2' : s⁻¹.1 * (1 - ε) = (1 - ε) * s⁻¹.1 := by rw [mul_sub, sub_mul, mul_one, one_mul, h2]
  rw [h1]
  calc ε * (s.1 * (n.1 - 1) * s⁻¹.1) * (1 - ε) = (ε * s.1) * (n.1 - 1) * (s⁻¹.1 * (1 - ε)) := by
        simp only [mul_assoc]
    _ = s.1 * (ε * (n.1 - 1) * (1 - ε)) * s⁻¹.1 := by rw [← hs, h2']; simp only [mul_assoc]
    _ = s.1 * (n.1 - 1) * s⁻¹.1 := by rw [hn]

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

/- English proof (translation)
Establish `hX` using `(hN n).1 hn`. Establish `h` using `mul_mul_eq_zero (A := 1) hε hX hX (by rw [one_mul, mul_one])`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_val {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {n : GL (Fin r) k} (hn : n ∈ N) :
    (n⁻¹).1 = 1 - (n.1 - 1) := by
  have hX := (hN n).1 hn
  have h := mul_mul_eq_zero (A := 1) hε hX hX (by rw [one_mul, mul_one])
  refine Units.inv_eq_of_mul_eq_one_right ?_
  calc n.1 * (1 - (n.1 - 1)) = 1 - (n.1 - 1) * 1 * (n.1 - 1) := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

/- English proof (translation)
Establish `h` using `mul_mul_eq_zero (A := 1) hε ((hN a).1 ha) ((hN b).1 hb) (by rw [one_mul, mul_one])`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul]`. Use `noncomm_ring`. Use `_ = _ := by rw [h, add_zero]`.
-/
theorem mul_val {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {a b : GL (Fin r) k} (ha : a ∈ N) (hb : b ∈ N) :
    (a * b).1 - 1 = (a.1 - 1) + (b.1 - 1) := by
  have h := mul_mul_eq_zero (A := 1) hε ((hN a).1 ha) ((hN b).1 hb) (by rw [one_mul, mul_one])
  calc (a * b).1 - 1 = (a.1 - 1) + (b.1 - 1) + (a.1 - 1) * 1 * (b.1 - 1) := by
        rw [Units.val_mul]; noncomm_ring
    _ = _ := by rw [h, add_zero]

/- English proof (translation)
Establish `hX` using `(hN n).1 hn`. Establish `h` using `mul_mul_eq_zero hε hX hX hs`. Establish `hss : s⁻¹.1 * s.1 = 1` using `Units.inv_mul s`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul, inv_val hε hN hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem twist_val {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {s : GL (Fin r) k} (hs : s.1 * ε = ε * s.1)
    {n : GL (Fin r) k} (hn : n ∈ N) :
    (s⁻¹ * n⁻¹ * s * n).1 - 1 = (n.1 - 1) - s⁻¹.1 * (n.1 - 1) * s.1 := by
  have hX := (hN n).1 hn
  have h := mul_mul_eq_zero hε hX hX hs
  have hss : s⁻¹.1 * s.1 = 1 := Units.inv_mul s
  rw [Units.val_mul, Units.val_mul, Units.val_mul, inv_val hε hN hn]
  calc s⁻¹.1 * (1 - (n.1 - 1)) * s.1 * n.1 - 1
      = (s⁻¹.1 * s.1 - 1) + (s⁻¹.1 * s.1) * (n.1 - 1) - s⁻¹.1 * (n.1 - 1) * s.1
          - s⁻¹.1 * ((n.1 - 1) * s.1 * (n.1 - 1)) := by noncomm_ring
    _ = _ := by rw [hss, h]; noncomm_ring

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

def radSub (ε : Matrix (Fin r) (Fin r) k) : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ε * X * (1 - ε) = X}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [mul_add, add_mul, hX, hY]
  zero_mem' := by simp
  smul_mem' c X hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [Matrix.mul_smul, Matrix.smul_mul, hX]

/- English proof (translation)
Establish `hg' : γ⁻¹.1 * ε = ε * γ⁻¹.1` using `(Commute.units_inv_left (u := γ) hγε).eq`. Set `L : Matrix (Fin r) (Fin r) k →ₗ[k] Matrix (Fin r) (Fin r) k` to `LinearMap.id - (LinearMap.mulLeft k γ⁻¹.1) ∘ₗ (LinearMap.mulRight k γ.1)`. Establish `hL : ∀ X, L X = X - γ⁻¹.1 * X * γ.1` using `fun X => by`. Simplify using `[L, mul_assoc]`. Establish `hmap : ∀ X ∈ radSub ε, L X ∈ radSub ε` using `fun X hX => by`.

Express the relevant statement in the definitionally equal form `ε * X * (1 - ε) = X at hX`. Express the relevant statement in the definitionally equal form `ε * L X * (1 - ε) = L X`. Establish `h1 : γ.1 * (1 - ε) = (1 - ε) * γ.1` using `by rw [mul_sub, sub_mul, mul_one, one_mul, hγε]`. Rewrite using `[hL, mul_sub ε, sub_mul _ _ (1 - ε), hX]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Set `L'` to `L.restrict hmap`. Establish `hinj : Function.Injective L'`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `X hX`.

Establish `h` using `congrArg Subtype.val hX`. Simplify using `only [L', LinearMap.restrict_coe_apply, ZeroMemClass.coe_zero] at h`. Rewrite `h` using `[hL]`. Conclude with `Subtype.ext (hcore X.1 X.2 h)`. Take `⟨X, hX⟩` from `(LinearMap.injective_iff_surjective.1 hinj) ⟨Y, hY⟩`.

Establish `h` using `congrArg Subtype.val hX`. Simplify using `only [L', LinearMap.restrict_coe_apply] at h`. Conclude with `⟨X.1, X.2, (hL X.1).symm.trans h⟩`.
-/
theorem exists_twist_eq {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {γ : GL (Fin r) k} (hγ : IsRegSS γ.1)
    (hγε : γ.1 * ε = ε * γ.1) (hcore : ∀ Z, ε * Z * (1 - ε) = Z → Z - γ⁻¹.1 * Z * γ.1 = 0 → Z = 0)
    {Y : Matrix (Fin r) (Fin r) k} (hY : ε * Y * (1 - ε) = Y) :
    ∃ X, ε * X * (1 - ε) = X ∧ X - γ⁻¹.1 * X * γ.1 = Y := by
  have hg' : γ⁻¹.1 * ε = ε * γ⁻¹.1 := (Commute.units_inv_left (u := γ) hγε).eq
  let L : Matrix (Fin r) (Fin r) k →ₗ[k] Matrix (Fin r) (Fin r) k :=
    LinearMap.id - (LinearMap.mulLeft k γ⁻¹.1) ∘ₗ (LinearMap.mulRight k γ.1)
  have hL : ∀ X, L X = X - γ⁻¹.1 * X * γ.1 := fun X => by
    simp [L, mul_assoc]
  have hmap : ∀ X ∈ radSub ε, L X ∈ radSub ε := fun X hX => by
    change ε * X * (1 - ε) = X at hX
    change ε * L X * (1 - ε) = L X
    have h1 : γ.1 * (1 - ε) = (1 - ε) * γ.1 := by rw [mul_sub, sub_mul, mul_one, one_mul, hγε]
    rw [hL, mul_sub ε, sub_mul _ _ (1 - ε), hX]
    congr 1
    calc ε * (γ⁻¹.1 * X * γ.1) * (1 - ε) = (ε * γ⁻¹.1) * X * (γ.1 * (1 - ε)) := by simp only [mul_assoc]
      _ = γ⁻¹.1 * (ε * X * (1 - ε)) * γ.1 := by rw [← hg', h1]; simp only [mul_assoc]
      _ = _ := by rw [hX]
  let L' := L.restrict hmap
  have hinj : Function.Injective L' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h := congrArg Subtype.val hX
    simp only [L', LinearMap.restrict_coe_apply, ZeroMemClass.coe_zero] at h
    rw [hL] at h
    exact Subtype.ext (hcore X.1 X.2 h)
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨Y, hY⟩
  have h := congrArg Subtype.val hX
  simp only [L', LinearMap.restrict_coe_apply] at h
  exact ⟨X.1, X.2, (hL X.1).symm.trans h⟩

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

/- English proof (translation)
Use `haveI : T2Space k := GlobalTheory.LocAtTopology.t2Space_of_nonarchimedeanLocalField k`. Use `haveI : SecondCountableTopology k := GlobalTheory.LocAtTopology.secondCountable_localField k`. Establish `hNc : IsClosed (N : Set (GL (Fin r) k))`. Establish `: (N : Set (GL (Fin r) k)) = {g | ε * (g.1 - 1) * (1 - ε) = g.1 - 1}` using `Set.ext fun g => hN g`. Rewrite using `[this]`.

Conclude with `isClosed_eq (by fun_prop) (by fun_prop)`. Use `haveI : LocallyCompactSpace N := hNc.locallyCompactSpace`. Establish `hg' : γ⁻¹.1 * ε = ε * γ⁻¹.1` using `(Commute.units_inv_left (u := γ) hγε).eq`. Establish `hmem : ∀ n ∈ N, γ⁻¹ * n⁻¹ * γ * n ∈ N` using `fun n hn => by`. Use `conj_mem hN hg' (inv_mem hn)` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Conclude with `mul_mem this hn`. Establish `hcore : ∀ Z, ε * Z * (1 - ε) = Z → Z - γ⁻¹.1 * Z * γ.1 = 0 → Z = 0` using `fun Z hZ h => by`. Establish `h1 : Z = γ⁻¹.1 * Z * γ.1` using `sub_eq_zero.1 h`. Establish `h2 : Z * γ.1 = γ.1 * Z`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : Z * ε = ε * Z` using `hγ.commute h2 hγε.symm`. Rewrite using `[← hZ, ← h3, mul_assoc, mul_sub, mul_one, hε, sub_self, mul_zero]`. Set `ψ : N →* N` to `{ toFun := fun n => ⟨γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n, hmem n n.2⟩ map_one' := Subtype.ext (by simp) map_mul' := fun a b => by`. Use `Subtype.ext (Units.ext ((sub_left_inj (a := (1 : Matrix (Fin r) (Fin r) k))).1 ?_))` and prove the remaining obligations.

Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[twist_val hε hN hγε (mul_mem a.2 b.2), mul_val hε hN (hmem _ a.2) (hmem _ b.2), twist_val hε hN hγε a.2, twist_val hε hN hγε b.2, mul_val hε hN a.2 b.2]`. Use `noncomm_ring }`. Establish `hψ : ∀ n : N, ((ψ n : N) : GL (Fin r) k) = γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n` using `fun n => rfl`. Establish `hψc : Continuous ψ`.

Express the relevant statement in the definitionally equal form `Continuous fun n : N => (⟨γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n, hmem n n.2⟩ : N)`. Conclude with `Continuous.subtype_mk (by fun_prop) _`. Establish `hinj : Function.Injective ψ`. Introduce `a b h`. Establish `h1` using `congrArg (fun u : N => (u : GL (Fin r) k).1 - 1) h`.

Simplify using `only [hψ, twist_val hε hN hγε a.2, twist_val hε hN hγε b.2] at h1`. Establish `hZ : ε * (a.1.1 - b.1.1) * (1 - ε) = a.1.1 - b.1.1`. Establish `ha` using `(hN _).1 a.2`. Establish `hb` using `(hN _).1 b.2`. Combine the equalities or inequalities in the displayed calculation.

Use `hcore _ hZ (by rw [← sub_eq_zero] at h1; rw [← h1]; noncomm_ring)` as an intermediate fact. Conclude with `Subtype.ext (Units.ext (sub_eq_zero.1 this))`. Establish `hsurj : Function.Surjective ψ`. Introduce `m`. Take `⟨X, hX, hXY⟩` from `exists_twist_eq hε hγ hγε hcore ((hN _).1 m.2)`.

Establish `hXX` using `mul_mul_eq_zero (A := 1) hε hX hX (by rw [one_mul, mul_one])`. Rewrite `hXX` using `[mul_one]`. Set `u : GL (Fin r) k` to `⟨1 + X, 1 - X, by noncomm_ring; rw [hXX]; simp, by noncomm_ring; rw [hXX]; simp⟩`. Establish `hu : u ∈ N` using `(hN u).2 (by simp only [u, add_sub_cancel_left]; exact hX)`. Use `⟨⟨u, hu⟩, Subtype.ext (Units.ext ((sub_left_inj (a := (1 : Matrix (Fin r) (Fin r) k))).1 ?_))⟩` and prove the remaining obligations.

Rewrite using `[hψ, twist_val hε hN hγε hu]`. Simplify using `only [u, add_sub_cancel_left]`. Conclude with `hXY`. Establish `hopen : IsOpenMap ψ` using `MonoidHom.isOpenMap_of_sigmaCompact ψ hsurj hψc`. Set `hom` to `(Equiv.ofBijective ψ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hψc hopen`.

Set `e : N ≃ₜ* N` to `{ toMulEquiv := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩ continuous_toFun := hom.continuous_toFun continuous_invFun := hom.continuous_invFun }`. Establish `he : ∀ n : N, ((e n : N) : GL (Fin r) k) = γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n` using `fun n => rfl`. Establish `hemb : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`. Use `haveI : (dn.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map dn e.toMulEquiv e.continuous e.symm.continuous`. Combine the equalities or inequalities in the displayed calculation.

Use `integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Simplify using `only [he]`. Use `congr 1`. Use `group`. Use `_ = ∫ u : N, f (x⁻¹ * γ * u * x) ∂(dn.map e) := (hemb.integral_map (fun u : N => f (x⁻¹ * γ * u * x))).symm`.

Use `_ = 0 := hf _ _ _`.
-/
theorem integral_twist [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)]
    {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) (f : GL (Fin r) k → ℂ)
    (hf : ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0)
    {γ : GL (Fin r) k} (hγ : IsRegSS γ.1) (hγε : γ.1 * ε = ε * γ.1) (dn : Measure N) [dn.IsHaarMeasure]
    (x : GL (Fin r) k) : ∫ n : N, f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) ∂dn = 0 := by
  haveI : T2Space k := GlobalTheory.LocAtTopology.t2Space_of_nonarchimedeanLocalField k
  haveI : SecondCountableTopology k := GlobalTheory.LocAtTopology.secondCountable_localField k
  have hNc : IsClosed (N : Set (GL (Fin r) k)) := by
    have : (N : Set (GL (Fin r) k)) = {g | ε * (g.1 - 1) * (1 - ε) = g.1 - 1} := Set.ext fun g => hN g
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  have hg' : γ⁻¹.1 * ε = ε * γ⁻¹.1 := (Commute.units_inv_left (u := γ) hγε).eq
  have hmem : ∀ n ∈ N, γ⁻¹ * n⁻¹ * γ * n ∈ N := fun n hn => by
    have := conj_mem hN hg' (inv_mem hn)
    rw [inv_inv] at this
    exact mul_mem this hn
  have hcore : ∀ Z, ε * Z * (1 - ε) = Z → Z - γ⁻¹.1 * Z * γ.1 = 0 → Z = 0 := fun Z hZ h => by
    have h1 : Z = γ⁻¹.1 * Z * γ.1 := sub_eq_zero.1 h
    have h2 : Z * γ.1 = γ.1 * Z := by
      calc Z * γ.1 = (γ.1 * γ⁻¹.1) * Z * γ.1 := by rw [Units.mul_inv, one_mul]
        _ = γ.1 * (γ⁻¹.1 * Z * γ.1) := by simp only [mul_assoc]
        _ = γ.1 * Z := by rw [← h1]
    have h3 : Z * ε = ε * Z := hγ.commute h2 hγε.symm
    rw [← hZ, ← h3, mul_assoc, mul_sub, mul_one, hε, sub_self, mul_zero]
  let ψ : N →* N :=
    { toFun := fun n => ⟨γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n, hmem n n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        refine Subtype.ext (Units.ext ((sub_left_inj (a := (1 : Matrix (Fin r) (Fin r) k))).1 ?_))
        simp only [Subgroup.coe_mul]
        rw [twist_val hε hN hγε (mul_mem a.2 b.2), mul_val hε hN (hmem _ a.2) (hmem _ b.2),
          twist_val hε hN hγε a.2, twist_val hε hN hγε b.2, mul_val hε hN a.2 b.2]
        noncomm_ring }
  have hψ : ∀ n : N, ((ψ n : N) : GL (Fin r) k) = γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n := fun n => rfl
  have hψc : Continuous ψ := by
    change Continuous fun n : N => (⟨γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n, hmem n n.2⟩ : N)
    exact Continuous.subtype_mk (by fun_prop) _
  have hinj : Function.Injective ψ := by
    intro a b h
    have h1 := congrArg (fun u : N => (u : GL (Fin r) k).1 - 1) h
    simp only [hψ, twist_val hε hN hγε a.2, twist_val hε hN hγε b.2] at h1
    have hZ : ε * (a.1.1 - b.1.1) * (1 - ε) = a.1.1 - b.1.1 := by
      have ha := (hN _).1 a.2
      have hb := (hN _).1 b.2
      calc ε * (a.1.1 - b.1.1) * (1 - ε) = ε * (a.1.1 - 1) * (1 - ε) - ε * (b.1.1 - 1) * (1 - ε) := by
            noncomm_ring
        _ = _ := by rw [ha, hb]; abel
    have := hcore _ hZ (by rw [← sub_eq_zero] at h1; rw [← h1]; noncomm_ring)
    exact Subtype.ext (Units.ext (sub_eq_zero.1 this))
  have hsurj : Function.Surjective ψ := by
    intro m
    obtain ⟨X, hX, hXY⟩ := exists_twist_eq hε hγ hγε hcore ((hN _).1 m.2)
    have hXX := mul_mul_eq_zero (A := 1) hε hX hX (by rw [one_mul, mul_one])
    rw [mul_one] at hXX
    let u : GL (Fin r) k := ⟨1 + X, 1 - X, by noncomm_ring; rw [hXX]; simp, by noncomm_ring; rw [hXX]; simp⟩
    have hu : u ∈ N := (hN u).2 (by simp only [u, add_sub_cancel_left]; exact hX)
    refine ⟨⟨u, hu⟩, Subtype.ext (Units.ext ((sub_left_inj (a := (1 : Matrix (Fin r) (Fin r) k))).1 ?_))⟩
    rw [hψ, twist_val hε hN hγε hu]
    simp only [u, add_sub_cancel_left]
    exact hXY
  have hopen : IsOpenMap ψ := MonoidHom.isOpenMap_of_sigmaCompact ψ hsurj hψc
  let hom := (Equiv.ofBijective ψ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hψc hopen
  let e : N ≃ₜ* N :=
    { toMulEquiv := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
      continuous_toFun := hom.continuous_toFun
      continuous_invFun := hom.continuous_invFun }
  have he : ∀ n : N, ((e n : N) : GL (Fin r) k) = γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n := fun n => rfl
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  haveI : (dn.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map dn e.toMulEquiv e.continuous e.symm.continuous
  calc ∫ n : N, f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) ∂dn
      = ∫ n : N, f (x⁻¹ * γ * ((e n : N) : GL (Fin r) k) * x) ∂dn := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
        simp only [he]
        congr 1
        group
    _ = ∫ u : N, f (x⁻¹ * γ * u * x) ∂(dn.map e) := (hemb.integral_map (fun u : N => f (x⁻¹ * γ * u * x))).symm
    _ = 0 := hf _ _ _

end GlobalTheory.RadicalOrb

open GlobalTheory.RadicalOrb in
/- English proof (translation)
Introduce `k _ _ _ _ r _ _ μ _ ε N hε hN f hf hfc hnv γ hγ hγε b hb hbT hbN dt _`. Use `haveI : T2Space k := GlobalTheory.LocAtTopology.t2Space_of_nonarchimedeanLocalField k`. Use `haveI : SecondCountableTopology k := GlobalTheory.LocAtTopology.secondCountable_localField k`. Establish `hTε : ∀ t ∈ cent γ, t.1 * ε = ε * t.1` using `fun t ht => hγ.commute (congrArg Units.val (mem_cent.1 ht)) hγε.symm`. Establish `hTc : IsMulCommutative (cent γ)` using `isMulCommutative_cent_GL hγ`.

Use `haveI : dt.IsMulRightInvariant := ⟨fun g => by`. Establish `: (fun x : cent γ => x * g) = (fun x => g * x)` using `funext fun x => hTc.is_comm.comm x g`. Rewrite using `[this, map_mul_left_eq_self]⟩`. Establish `hNc : IsClosed (N : Set (GL (Fin r) k))`. Establish `: (N : Set (GL (Fin r) k)) = {g | ε * (g.1 - 1) * (1 - ε) = g.1 - 1}` using `Set.ext fun g => hN g`.

Rewrite using `[this]`. Conclude with `isClosed_eq (by fun_prop) (by fun_prop)`. Use `haveI : LocallyCompactSpace N := hNc.locallyCompactSpace`. Set `dn : Measure N` to `Measure.haar`. Use `haveI : dn.IsMulRightInvariant := ⟨fun g => by`.

Establish `: (fun x : N => x * g) = (fun x => g * x)`. Use function extensionality and compare the values at `fun x => Subtype.ext (mul_comm_of_mem hε hN x.2 g.2)`. Rewrite using `[this, map_mul_left_eq_self]⟩`. Establish `hφi : LeftInv (cent γ) (fun x => b x * f (x⁻¹ * γ * x))` using `fun t ht x => by`. Simplify using `only [hbT t ht x]`.

Conclude with `congrArg _ (leftInv_conjFn le_rfl f t ht x)`. Establish `hφc : Continuous (fun x => b x * f (x⁻¹ * γ * x))` using `hb.mul (hf.comp (by fun_prop))`. Take `⟨C, hC, h0⟩` from `isProperOrbit_GL hγ _ hfc`. Establish `hint : Integrable (descend (cent γ) (fun x => b x * f (x⁻¹ * γ * x))) (quotMeas (cent γ) dt μ)` using `integrable_descend (isClosed_cent γ) hφi hφc hC fun x hx => h0 x (subset_tsupport f (right_ne_zero_of_mul hx))`. Use `⟨hint, ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals (GL (Fin r) k) (cent γ) N (isClosed_cent γ) hNc hTc (fun t ht n hn => conj_mem hN (hTε t ht) hn) (isClosedEmbedding_mul hε hN (isClosed_cent γ) hTε) μ dt dn _ hφc.measurable hφi hint fun x => ?_` and prove the remaining obligations. Establish `e : ∀ n : N, b ((n : GL (Fin r) k) * x) * f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) = b x * f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x))` using `fun n => by rw [hbN _ n.2 x]`. Simplify using `only [e]`. Rewrite using `[integral_const_mul, integral_twist hε hN f hnv hγ hγε dn x, mul_zero]`.
-/
theorem GlobalTheory.RadicalOrb.hasQuotInt_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure] (ε : Matrix (Fin r) (Fin r) k) (N : Subgroup (GL (Fin r) k)), ε * ε = ε → (∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) → ∀ f : GL (Fin r) k → ℂ, Continuous f → HasCompactSupport f → (∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0) → ∀ γ : GL (Fin r) k, IsRegSS γ.1 → γ.1 * ε = ε * γ.1 → ∀ b : GL (Fin r) k → ℂ, Continuous b → LeftInv (cent γ) b → LeftInv N b → ∀ (dt : Measure (cent γ)) [dt.IsHaarMeasure], HasQuotInt (cent γ) dt μ (fun x => b x * f (x⁻¹ * γ * x)) 0 := by
  intro k _ _ _ _ r _ _ μ _ ε N hε hN f hf hfc hnv γ hγ hγε b hb hbT hbN dt _
  haveI : T2Space k := GlobalTheory.LocAtTopology.t2Space_of_nonarchimedeanLocalField k
  haveI : SecondCountableTopology k := GlobalTheory.LocAtTopology.secondCountable_localField k
  have hTε : ∀ t ∈ cent γ, t.1 * ε = ε * t.1 := fun t ht =>
    hγ.commute (congrArg Units.val (mem_cent.1 ht)) hγε.symm
  have hTc : IsMulCommutative (cent γ) := isMulCommutative_cent_GL hγ
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent γ => x * g) = (fun x => g * x) := funext fun x => hTc.is_comm.comm x g
    rw [this, map_mul_left_eq_self]⟩
  have hNc : IsClosed (N : Set (GL (Fin r) k)) := by
    have : (N : Set (GL (Fin r) k)) = {g | ε * (g.1 - 1) * (1 - ε) = g.1 - 1} := Set.ext fun g => hN g
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  let dn : Measure N := Measure.haar
  haveI : dn.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : N => x * g) = (fun x => g * x) :=
      funext fun x => Subtype.ext (mul_comm_of_mem hε hN x.2 g.2)
    rw [this, map_mul_left_eq_self]⟩
  have hφi : LeftInv (cent γ) (fun x => b x * f (x⁻¹ * γ * x)) := fun t ht x => by
    simp only [hbT t ht x]
    exact congrArg _ (leftInv_conjFn le_rfl f t ht x)
  have hφc : Continuous (fun x => b x * f (x⁻¹ * γ * x)) := hb.mul (hf.comp (by fun_prop))
  obtain ⟨C, hC, h0⟩ := isProperOrbit_GL hγ _ hfc
  have hint : Integrable (descend (cent γ) (fun x => b x * f (x⁻¹ * γ * x))) (quotMeas (cent γ) dt μ) :=
    integrable_descend (isClosed_cent γ) hφi hφc hC fun x hx =>
      h0 x (subset_tsupport f (right_ne_zero_of_mul hx))
  refine ⟨hint, ?_⟩
  refine GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals (GL (Fin r) k) (cent γ) N (isClosed_cent γ) hNc hTc
    (fun t ht n hn => conj_mem hN (hTε t ht) hn) (isClosedEmbedding_mul hε hN (isClosed_cent γ) hTε) μ dt dn _ hφc.measurable hφi hint
    fun x => ?_
  · have e : ∀ n : N, b ((n : GL (Fin r) k) * x) * f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) =
        b x * f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) := fun n => by rw [hbN _ n.2 x]
    simp only [e]
    rw [integral_const_mul, integral_twist hε hN f hnv hγ hγε dn x, mul_zero]
