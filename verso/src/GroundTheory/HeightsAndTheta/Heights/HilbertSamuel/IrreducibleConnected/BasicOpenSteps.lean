import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

/- English proof (translation)
Establish `h : ∀ i, eval x (ComplexSets.linPoly A i) = A.mulVec x i`. Introduce `i`. Simplify using `[ComplexSets.linPoly, Matrix.mulVec, dotProduct, map_sum]`. Rewrite using `[ComplexSets.pullback, aeval_eq_bind₁]`. Express the relevant statement in the definitionally equal form `eval₂Hom (RingHom.id ℂ) x (bind₁ (ComplexSets.linPoly A) P) = eval₂Hom (RingHom.id ℂ) (A.mulVec x) P`.

Rewrite using `[eval₂Hom_bind₁]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `h i`.
-/
theorem IrreducibleBasicOpenConnected.eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (x : Fin n → ℂ) :
    eval x (ComplexSets.pullback A P) = eval (A.mulVec x) P := by
  have h : ∀ i, eval x (ComplexSets.linPoly A i) = A.mulVec x i := by
    intro i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, map_sum]
  rw [ComplexSets.pullback, aeval_eq_bind₁]
  change eval₂Hom (RingHom.id ℂ) x (bind₁ (ComplexSets.linPoly A) P) =
    eval₂Hom (RingHom.id ℂ) (A.mulVec x) P
  rw [eval₂Hom_bind₁]
  congr 2
  funext i
  exact h i

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ComplexSets.linPoly, Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem IrreducibleBasicOpenConnected.eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) : (fun i => eval x (ComplexSets.linPoly A i)) = A.mulVec x := by
  funext i
  simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ W)` using `Ideal.Quotient.nontrivial_iff.mpr hW.ne_top`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ n`. Use `ringKrullDim_le_of_surjective (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective` as an intermediate fact. Rewrite `this` using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]`. Simplify `this` using `[Nat.card_eq_fintype_card]`.

Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h0 hle`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h0 (by simp)`. Consider the case `coe e`.

Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top => exact absurd hle (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))`. Consider the case `coe d => exact ⟨d, rfl⟩`.
-/
theorem IrreducibleBasicOpenConnected.exists_dim {n : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W.IsPrime) : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.nontrivial_iff.mpr hW.ne_top
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ n := by
    have := ringKrullDim_le_of_surjective (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at this
    simpa [Nat.card_eq_fintype_card] using this
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h0 hle
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hle (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))
    | coe d => exact ⟨d, rfl⟩

/- English proof (translation)
Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `U hU ⟨y₀, hy₀⟩`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hU y₀ hy₀`.

Apply `hR` to reduce the goal to its premises. Use `funext_set (fun j => Metric.ball (y₀ j) ε) (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[← ball_pi y₀ hε]`. Rewrite using `[map_zero]`. Assume the negation of the conclusion as `hyR`.

Conclude with `(Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hball hy, hyR⟩`.
-/
theorem IrreducibleBasicOpenConnected.dense_ne_zero {d : ℕ} {R : MvPolynomial (Fin d) ℂ} (hR : R ≠ 0) :
    Dense {y : Fin d → ℂ | eval y R ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  apply hR
  refine funext_set (fun j => Metric.ball (y₀ j) ε)
    (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_
  rw [← ball_pi y₀ hε] at hy
  rw [map_zero]
  by_contra hyR
  exact (Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hball hy, hyR⟩

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `U hU`. Establish `hN` using `IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof n d W (ComplexSets.linPoly A) hW hA.injective hA.finite x hx U hU`. Establish `hfun : (fun z : Fin n → ℂ => fun i => eval z (ComplexSets.linPoly A i)) = fun z => A.mulVec z`.

Use function extensionality and compare the values at `fun z => IrreducibleBasicOpenConnected.eval_linPoly A z`. Rewrite `hN` using `[hfun, IrreducibleBasicOpenConnected.eval_linPoly]`. Take `⟨y, ⟨z, ⟨hzW, hzU⟩, rfl⟩, hyR⟩` from `mem_closure_iff_nhds.mp (IrreducibleBasicOpenConnected.dense_ne_zero hR (A.mulVec x)) _ hN`. Conclude with `⟨z, hzU, hzW, hyR⟩`.
-/
theorem IrreducibleBasicOpenConnected.zeroSet_subset_closure {n d : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hW : W.IsPrime) (hA : ComplexSets.IsFiniteProjection W A)
    {R : MvPolynomial (Fin d) ℂ} (hR : R ≠ 0) :
    ComplexSets.zeroSet W ⊆ closure {x | x ∈ ComplexSets.zeroSet W ∧ eval (A.mulVec x) R ≠ 0} := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro U hU
  have hN := IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof n d W (ComplexSets.linPoly A) hW hA.injective
    hA.finite x hx U hU
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (ComplexSets.linPoly A i)) = fun z => A.mulVec z :=
    funext fun z => IrreducibleBasicOpenConnected.eval_linPoly A z
  rw [hfun, IrreducibleBasicOpenConnected.eval_linPoly] at hN
  obtain ⟨y, ⟨z, ⟨hzW, hzU⟩, rfl⟩, hyR⟩ :=
    mem_closure_iff_nhds.mp (IrreducibleBasicOpenConnected.dense_ne_zero hR (A.mulVec x)) _ hN
  exact ⟨z, hzU, hzW, hyR⟩

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) := (ComplexSets.projHom W A).toRingHom.toAlgebra`. Establish `: IsDomain (MvPolynomial (Fin n) ℂ ⧸ W)` using `Ideal.Quotient.isDomain W`. Establish `hne : Ideal.Quotient.mk W g ≠ 0` using `fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `hcomap` using `Ideal.comap_ne_bot_of_integral_mem hne (Ideal.mem_span_singleton_self _) (hA.finite.to_isIntegral _)`. Take `⟨Q, hQmem, hQ⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hcomap`.

Use `⟨Q, hQ, fun x hx hgx => ?_⟩` and prove the remaining obligations. Rewrite `hQmem` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `hQmem`. Take `⟨h, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hmem : ComplexSets.pullback A Q - h * g ∈ W`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc]`. Conclude with `sub_eq_zero.mpr rfl`. Establish `hev` using `hx _ hmem`. Rewrite `hev` using `[map_sub, map_mul, hgx, mul_zero, sub_zero, IrreducibleBasicOpenConnected.eval_pullback]`. Conclude with `hev`.
-/
theorem IrreducibleBasicOpenConnected.exists_base_vanishing {n d : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hW : W.IsPrime) (hA : ComplexSets.IsFiniteProjection W A)
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ W) :
    ∃ Q : MvPolynomial (Fin d) ℂ, Q ≠ 0 ∧
      ∀ x ∈ ComplexSets.zeroSet W, eval x g = 0 → eval (A.mulVec x) Q = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.isDomain W
  have hne : Ideal.Quotient.mk W g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcomap := Ideal.comap_ne_bot_of_integral_mem hne (Ideal.mem_span_singleton_self _)
    (hA.finite.to_isIntegral _)
  obtain ⟨Q, hQmem, hQ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  refine ⟨Q, hQ, fun x hx hgx => ?_⟩
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hQmem
  obtain ⟨c, hc⟩ := hQmem
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : ComplexSets.pullback A Q - h * g ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc]
    exact sub_eq_zero.mpr rfl
  have hev := hx _ hmem
  rw [map_sub, map_mul, hgx, mul_zero, sub_zero, IrreducibleBasicOpenConnected.eval_pullback] at hev
  exact hev

end GroundTheory.Heights₂.Heights.HilbertSamuel
