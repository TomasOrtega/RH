import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetParam
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetCover
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneNull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)

section OneBlock

variable {n : ℕ}

/- English proof (translation)
Simplify using `[segre]`.
-/
theorem segre_pblk_apply (z : (Σ k, PBlk n k) → ℂ) (i : (k : Unit) → PBlk n k) :
    segre z i = z ⟨(), i ()⟩ := by
  simp [segre]

/- English proof (translation)
Introduce `z z' h`. Use function extensionality and compare the values at `p`. Take `⟨⟨⟩, i⟩` from `p`. Use `congrFun h fun _ => i` as an intermediate fact. Simplify `this` using `[segre_pblk_apply]`.
-/
theorem segre_pblk_injective : Function.Injective (segre : ((Σ k, PBlk n k) → ℂ) → _) := by
  intro z z' h
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  have := congrFun h fun _ => i
  simpa [segre_pblk_apply] using this

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[segre_pblk_apply]`.
-/
theorem segre_pblk_smul (t : ℂ) (z : (Σ k, PBlk n k) → ℂ) :
    segre (fun p => t * z p) = t • segre z := by
  funext i
  simp [segre_pblk_apply]

/- English proof (translation)
Rewrite using `[map_rename, eval_rename]`. Both sides reduce to the same expression.
-/
theorem eval_map_rename_pblk (z' : (Σ k, PBlk n k) → ℂ) (g : MvPolynomial (Fin n) ℤ) :
    eval z' (map (Int.castRingHom ℂ) (rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k)) g)) =
      eval (fun i => z' ⟨(), i⟩) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]
  rfl

/- English proof (translation)
Introduce `q hq`. Establish `hle : complexFibreIdeal P ≤ RingHom.ker (eval fun i => z' ⟨(), i⟩)`. Unfold `complexFibreIdeal`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← eval_map_rename_pblk]`. Conclude with `hz _ hg`. Conclude with `hle hq`.
-/
theorem eval_complexFibreIdeal_of_forall {P : Ideal (MRing (PBlk n))} {z' : (Σ k, PBlk n k) → ℂ}
    (hz : ∀ f ∈ P, eval z' (map (Int.castRingHom ℂ) f) = 0) :
    ∀ q ∈ complexFibreIdeal P, eval (fun i => z' ⟨(), i⟩) q = 0 := by
  intro q hq
  have hle : complexFibreIdeal P ≤ RingHom.ker (eval fun i => z' ⟨(), i⟩) := by
    unfold complexFibreIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, ← eval_map_rename_pblk]
    exact hz _ hg
  exact hle hq

/- English proof (translation)
Introduce `f hf`. Establish `hre : rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k)) (rename (fun p : Σ k, PBlk n k => p.2) f) = f`. Rewrite using `[rename_rename]`. Conclude with `rename_id_apply f`. Establish `hg : rename (fun p : Σ k, PBlk n k => p.2) f ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P`.

Rewrite using `[IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, hre]`. Conclude with `hf`. Establish `h` using `hz _ (Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℂ)) hg)`. Rewrite using `[← hre, eval_map_rename_pblk]`. Conclude with `h`.
-/
theorem forall_eval_of_complexFibreIdeal {P : Ideal (MRing (PBlk n))} {z : Fin n → ℂ}
    (hz : ∀ q ∈ complexFibreIdeal P, eval z q = 0) :
    ∀ f ∈ P, eval (fun p : Σ k, PBlk n k => z p.2) (map (Int.castRingHom ℂ) f) = 0 := by
  intro f hf
  have hre : rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k))
      (rename (fun p : Σ k, PBlk n k => p.2) f) = f := by
    rw [rename_rename]
    exact rename_id_apply f
  have hg : rename (fun p : Σ k, PBlk n k => p.2) f ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, hre]
    exact hf
  have h := hz _ (Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℂ)) hg)
  rw [← hre, eval_map_rename_pblk]
  exact h

end OneBlock

/- English proof (translation)
Introduce `n e S hS P Ψ hP hΨ`. Take `⟨U, D, N, s, hUD, hdisj, hnull, hfib, hrest⟩` from `hCov n e P Ψ hP hΨ`. Establish `hhyp` using `hHyp n e P Ψ hP hΨ`. Establish `hMH : IsMultiHomogIdeal P` using `hP.2.1.2.1`. Establish `hdet : IsUnit S.det` using `(Matrix.isUnit_iff_isUnit_det S).mp hS`.

Establish `hval : ∀ k j x, x ∈ U k → Ψ (segre (s k j x)) = Fin.cons 1 x ∧ s k j x ∈ mcPts P`. Introduce `k j x hx`. Establish `h2` using `(((hfib k x hx).2.2 j).1).2.self_of_nhds`. Conclude with `⟨h2.2.2, h2.2.1⟩`. Establish `hpt : ∀ (t : ℂ) (v : Fin n → ℂ), (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ v)) = t • v`.

Introduce `t v`. Simplify using `only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose]`. Express the relevant statement in the definitionally equal form `S⁻¹ *ᵥ (t • (S *ᵥ v)) = t • v`. Rewrite using `[mulVec_smul, mulVec_mulVec, nonsing_inv_mul S hdet, one_mulVec]`. Use `⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨k, j⟩, x, t⟩ ⟨hx, ht⟩ ⟨⟨k', j'⟩, x', t'⟩ ⟨hx', ht'⟩ heq`. Simplify using `only at hx ht hx' ht' heq`. Establish `hv` using `congrArg (ObjectsHeight.ofPointMatrix S hS).pointOf heq`. Rewrite `hv` using `[hpt, hpt]`. Establish `hz : (fun p : Σ k, PBlk n k => t * s k j x p) = fun p => t' * s k' j' x' p`.

Use function extensionality and compare the values at `p`. Take `⟨⟨⟩, i⟩` from `p`. Conclude with `congrFun hv i`. Establish `hΨz` using `congrArg (fun z => Ψ (segre z)) hz`. Simplify using `only [segre_pblk_smul, map_smul, (hval k j x ((hUD k).2.2.1 hx)).1, (hval k' j' x' ((hUD k').2.2.1 hx')).1] at hΨz`.

Establish `htt : t = t'` using `by simpa using congrFun hΨz 0`. Substitute `htt` using the available equality. Establish `hxx : x = x'`. Use function extensionality and compare the values at `i`. Use `congrFun hΨz i.succ` as an intermediate fact.

Simplify using `only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at this`. Conclude with `mul_left_cancel₀ ht this`. Substitute `hxx` using the available equality. Establish `hss : s k j x = s k' j' x`. Use function extensionality and compare the values at `p`.

Conclude with `mul_left_cancel₀ ht (congrFun hz p)`. Establish `hkk : k = k'`. Assume the negation of the conclusion as `hk`. Conclude with `Set.disjoint_left.1 (hdisj hk) hx hx'`. Substitute `hkk` using the available equality.

Establish `hjj : j = j'` using `(hfib k x ((hUD k).2.2.1 hx)).2.1 (congrArg segre hss)`. Substitute `hjj` using the available equality. Both sides reduce to the same expression. Introduce and unpack `y ⟨⟨⟨k, j⟩, x, t⟩, ⟨hx, ht⟩, rfl⟩`. Simplify using `only at hx ht`.

Introduce `q hq`. Rewrite using `[hpt]`. Establish `hm : (fun p : Σ k, PBlk n k => t * s k j x p) ∈ mcPts P` using `mcPts_smul hMH (fun _ => t) (fun _ => ht) (hval k j x ((hUD k).2.2.1 hx)).2`. Conclude with `eval_complexFibreIdeal_of_forall hm.2 q hq`. Use `set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩) with hF`.

Set `Lₗ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)` to `{ toFun := fun z => WithLp.toLp 2 (S *ᵥ fun i => z i) map_add' := by`. Introduce `a b`. Express the relevant statement in the definitionally equal form `WithLp.toLp 2 (S *ᵥ (fun i => a i + b i)) = _`. Rewrite using `[show (fun i => a i + b i) = (fun i => a i) + fun i => b i from rfl, mulVec_add]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := by`. Introduce `c a`. Express the relevant statement in the definitionally equal form `WithLp.toLp 2 (S *ᵥ (c • fun i => a i)) = _`. Rewrite using `[mulVec_smul]`. Use `rfl }`.

Set `L` to `LinearMap.toContinuousLinearMap Lₗ`. Use `set A1 := {z : EuclideanSpace ℂ (Fin n) | (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧ Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} with hA1`. Use `set A2 := {z : EuclideanSpace ℂ (Fin n) | (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧ Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 ≠ 0 ∧ (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ • Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∉ ⋃ k, D k} with hA2`. Establish `hsub : coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) \ F '' {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆ L '' (A1 ∪ A2)`. Introduce and unpack `y ⟨hyC, hyF⟩`.

Use `set z : Fin n → ℂ := S⁻¹ *ᵥ fun i => y i with hz`. Establish `hyz : y = L (WithLp.toLp 2 z)`. Express the relevant statement in the definitionally equal form `y = WithLp.toLp 2 (S *ᵥ (S⁻¹ *ᵥ fun i => y i))`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv S hdet, one_mulVec]`. Establish `hzC : ∀ q ∈ complexFibreIdeal P, eval z q = 0`.

Introduce `q hq`. Use `hyC q hq` as an intermediate fact. Simplify `this` using `[HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose]`. Use `⟨WithLp.toLp 2 z, ?_, hyz.symm⟩` and prove the remaining obligations. Distinguish the cases in `h0 : Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0`.

Conclude with `Or.inl ⟨hzC, h0⟩`. Distinguish the cases in `hxD : (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ • Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∈ ⋃ k, D k`. Use `swap`. Conclude with `Or.inr ⟨hzC, h0, hxD⟩`. It suffices to derive a contradiction.

Apply `hyF` to reduce the goal to its premises. Establish `hzm : (fun p : Σ k, PBlk n k => z p.2) ∈ mcPts P`. Use `⟨fun _ => ?_, forall_eval_of_complexFibreIdeal hzC⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Apply `h0` to reduce the goal to its premises. Establish `: (fun p : Σ k, PBlk n k => z p.2) = 0`. Use function extensionality and compare the values at `p`. Take `⟨⟨⟩, i⟩` from `p`. Conclude with `hne i`.

Rewrite using `[this]`. Establish `hs0 : segre (0 : (Σ k, PBlk n k) → ℂ) = 0`. Use function extensionality and compare the values at `i`. Simplify using `[segre_pblk_apply]`. Rewrite using `[hs0, map_zero]`.

Both sides reduce to the same expression. Use `set t := Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 with ht`. Use `set x := t⁻¹ • Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) with hx`. Take `⟨k, hk⟩` from `mem_iUnion.1 hxD`. Establish `hwm : (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ mcPts P` using `mcPts_smul hMH (fun _ => t⁻¹) (fun _ => inv_ne_zero h0) hzm`.

Establish `hwΨ : Ψ (segre fun p : Σ k, PBlk n k => t⁻¹ * z p.2) = Fin.cons 1 x`. Rewrite using `[segre_pblk_smul, map_smul]`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul]`.

Conclude with `inv_mul_cancel₀ h0`. Simplify using `only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul, hx, Fin.tail]`. Establish `hwf : segre (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ fibre P Ψ x` using `⟨_, hwm, rfl, hwΨ⟩`. Rewrite `hwf` using `[(hfib k x ((hUD k).2.2.1 hk)).1]`. Take `⟨j, hj⟩` from `hwf`.

Establish `hsj : s k j x = fun p : Σ k, PBlk n k => t⁻¹ * z p.2` using `segre_pblk_injective hj`. Use `⟨⟨⟨k, j⟩, x, t⟩, ⟨hk, h0⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hyz]`. Simplify using `only [hF, hsj]`. Express the relevant statement in the definitionally equal form `t • WithLp.toLp 2 (S *ᵥ (t⁻¹ • z)) = WithLp.toLp 2 (S *ᵥ z)`.

Rewrite using `[mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]`. Establish `hA : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) = 0` using `measure_union_null hhyp hrest`. Use `measure_mono_null hsub ?_` and prove the remaining obligations. Use `le_antisymm ?_ zero_le` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ConeSheetParam.proof (hCov : ConeSheetCover.Statement)
    (hHyp : ConeProjHyperplaneNull.Statement) : ConeSheetParam.Statement := by
  classical
  intro n e S hS P Ψ hP hΨ
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hrest⟩ := hCov n e P Ψ hP hΨ
  have hhyp := hHyp n e P Ψ hP hΨ
  have hMH : IsMultiHomogIdeal P := hP.2.1.2.1
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS

  have hval : ∀ k j x, x ∈ U k → Ψ (segre (s k j x)) = Fin.cons 1 x ∧ s k j x ∈ mcPts P := by
    intro k j x hx
    have h2 := (((hfib k x hx).2.2 j).1).2.self_of_nhds
    exact ⟨h2.2.2, h2.2.1⟩

  have hpt : ∀ (t : ℂ) (v : Fin n → ℂ),
      (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ v)) = t • v := by
    intro t v
    simp only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose]
    change S⁻¹ *ᵥ (t • (S *ᵥ v)) = t • v
    rw [mulVec_smul, mulVec_mulVec, nonsing_inv_mul S hdet, one_mulVec]
  refine ⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨k, j⟩, x, t⟩ ⟨hx, ht⟩ ⟨⟨k', j'⟩, x', t'⟩ ⟨hx', ht'⟩ heq
    simp only at hx ht hx' ht' heq
    have hv := congrArg (ObjectsHeight.ofPointMatrix S hS).pointOf heq
    rw [hpt, hpt] at hv
    have hz : (fun p : Σ k, PBlk n k => t * s k j x p) = fun p => t' * s k' j' x' p := by
      funext p
      obtain ⟨⟨⟩, i⟩ := p
      exact congrFun hv i
    have hΨz := congrArg (fun z => Ψ (segre z)) hz
    simp only [segre_pblk_smul, map_smul, (hval k j x ((hUD k).2.2.1 hx)).1,
      (hval k' j' x' ((hUD k').2.2.1 hx')).1] at hΨz
    have htt : t = t' := by simpa using congrFun hΨz 0
    subst htt
    have hxx : x = x' := by
      funext i
      have := congrFun hΨz i.succ
      simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at this
      exact mul_left_cancel₀ ht this
    subst hxx
    have hss : s k j x = s k' j' x := by
      funext p
      exact mul_left_cancel₀ ht (congrFun hz p)
    have hkk : k = k' := by
      by_contra hk
      exact Set.disjoint_left.1 (hdisj hk) hx hx'
    subst hkk
    have hjj : j = j' := (hfib k x ((hUD k).2.2.1 hx)).2.1 (congrArg segre hss)
    subst hjj
    rfl
  ·
    rintro y ⟨⟨⟨k, j⟩, x, t⟩, ⟨hx, ht⟩, rfl⟩
    simp only at hx ht
    intro q hq
    rw [hpt]
    have hm : (fun p : Σ k, PBlk n k => t * s k j x p) ∈ mcPts P :=
      mcPts_smul hMH (fun _ => t) (fun _ => ht) (hval k j x ((hUD k).2.2.1 hx)).2
    exact eval_complexFibreIdeal_of_forall hm.2 q hq
  ·
    set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
      q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩) with hF
    let Lₗ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
      { toFun := fun z => WithLp.toLp 2 (S *ᵥ fun i => z i)
        map_add' := by
          intro a b
          change WithLp.toLp 2 (S *ᵥ (fun i => a i + b i)) = _
          rw [show (fun i => a i + b i) = (fun i => a i) + fun i => b i from rfl, mulVec_add]
          rfl
        map_smul' := by
          intro c a
          change WithLp.toLp 2 (S *ᵥ (c • fun i => a i)) = _
          rw [mulVec_smul]
          rfl }
    let L := LinearMap.toContinuousLinearMap Lₗ
    set A1 := {z : EuclideanSpace ℂ (Fin n) |
      (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
        Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} with hA1
    set A2 := {z : EuclideanSpace ℂ (Fin n) |
      (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
        Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 ≠ 0 ∧
        (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
            Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∉ ⋃ k, D k} with hA2
    have hsub : coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) \ F ''
        {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆ L '' (A1 ∪ A2) := by
      rintro y ⟨hyC, hyF⟩
      set z : Fin n → ℂ := S⁻¹ *ᵥ fun i => y i with hz
      have hyz : y = L (WithLp.toLp 2 z) := by
        change y = WithLp.toLp 2 (S *ᵥ (S⁻¹ *ᵥ fun i => y i))
        rw [mulVec_mulVec, mul_nonsing_inv S hdet, one_mulVec]
      have hzC : ∀ q ∈ complexFibreIdeal P, eval z q = 0 := by
        intro q hq
        have := hyC q hq
        simpa [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose] using this
      refine ⟨WithLp.toLp 2 z, ?_, hyz.symm⟩
      by_cases h0 : Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0
      · exact Or.inl ⟨hzC, h0⟩
      by_cases hxD : (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
          Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∈ ⋃ k, D k
      swap
      · exact Or.inr ⟨hzC, h0, hxD⟩
      exfalso
      apply hyF

      have hzm : (fun p : Σ k, PBlk n k => z p.2) ∈ mcPts P := by
        refine ⟨fun _ => ?_, forall_eval_of_complexFibreIdeal hzC⟩
        by_contra hne
        push Not at hne
        apply h0
        have : (fun p : Σ k, PBlk n k => z p.2) = 0 := by
          funext p
          obtain ⟨⟨⟩, i⟩ := p
          exact hne i
        rw [this]
        have hs0 : segre (0 : (Σ k, PBlk n k) → ℂ) = 0 := by
          funext i
          simp [segre_pblk_apply]
        rw [hs0, map_zero]
        rfl
      set t := Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 with ht
      set x := t⁻¹ • Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) with hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hxD

      have hwm : (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ mcPts P :=
        mcPts_smul hMH (fun _ => t⁻¹) (fun _ => inv_ne_zero h0) hzm
      have hwΨ : Ψ (segre fun p : Σ k, PBlk n k => t⁻¹ * z p.2) = Fin.cons 1 x := by
        rw [segre_pblk_smul, map_smul]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul]
          exact inv_mul_cancel₀ h0
        · simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul, hx, Fin.tail]
      have hwf : segre (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ fibre P Ψ x :=
        ⟨_, hwm, rfl, hwΨ⟩
      rw [(hfib k x ((hUD k).2.2.1 hk)).1] at hwf
      obtain ⟨j, hj⟩ := hwf
      have hsj : s k j x = fun p : Σ k, PBlk n k => t⁻¹ * z p.2 := segre_pblk_injective hj
      refine ⟨⟨⟨k, j⟩, x, t⟩, ⟨hk, h0⟩, ?_⟩
      rw [hyz]
      simp only [hF, hsj]
      change t • WithLp.toLp 2 (S *ᵥ (t⁻¹ • z)) = WithLp.toLp 2 (S *ᵥ z)
      rw [mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]
    have hA : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) = 0 :=
      measure_union_null hhyp hrest
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ zero_le
    calc Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (L '' (A1 ∪ A2))
        ≤ (‖L‖₊ : ENNReal) ^ (((2 * (e + 1) : ℕ) : ℝ)) *
            Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) :=
          L.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg _) _
      _ = 0 := by rw [hA, mul_zero]

end GroundTheory.Heights₂.Heights
