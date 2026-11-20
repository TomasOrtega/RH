import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbeddingTypeJumps

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory (SS intOE intAd)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev swp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Af F ⊗[F] E ≃ₐ[F] E ⊗[F] Af F :=
  Algebra.TensorProduct.comm F (Af F) E

def SI (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Af F ⊗[F] E) :=
  (SS F E).comap (swp F E).toRingEquiv.toRingHom

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_SI {x : Af F ⊗[F] E} : x ∈ SI F E ↔ swp F E x ∈ SS F E := Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨x, h⟩, rfl⟩`.
-/
theorem intOE_of_isIntegral {x : E} (h : IsIntegral ℤ x) : x ∈ intOE E := ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Take `⟨y, rfl⟩` from `h`. Conclude with `y.isIntegral_coe`.
-/
theorem isIntegral_of_intOE {x : E} (h : x ∈ intOE E) : IsIntegral ℤ x := by
  obtain ⟨y, rfl⟩ := h
  exact y.isIntegral_coe

/- English proof (translation)
Set `_` to `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)`. Take `⟨d, hd, h⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact (F := F) (E := E) (Set.range fun i => swp F E (f i)) (Set.finite_range _).isCompact`. Conclude with `⟨d, hd, fun i => by rw [mem_SI, map_smul]; exact h _ ⟨i, rfl⟩⟩`.
-/
theorem den_fin {ι : Type*} [Finite ι] (f : ι → Af F ⊗[F] E) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, (d : F) • f i ∈ SI F E := by
  let _ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  obtain ⟨d, hd, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact (F := F) (E := E)
    (Set.range fun i => swp F E (f i)) (Set.finite_range _).isCompact
  exact ⟨d, hd, fun i => by rw [mem_SI, map_smul]; exact h _ ⟨i, rfl⟩⟩

/- English proof (translation)
Take `⟨D, hD, h⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E`. Use `⟨D, hD, fun e he => isIntegral_of_intOE (h e ?_)⟩` and prove the remaining obligations. Rewrite `he` using `[mem_SI, Algebra.TensorProduct.comm_tmul]`. Conclude with `he`.
-/
theorem incl_den : ∃ D : 𝓞 F, D ≠ 0 ∧
    ∀ e : E, (1 : Af F) ⊗ₜ[F] e ∈ SI F E → IsIntegral ℤ ((D : F) • e) := by
  obtain ⟨D, hD, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  refine ⟨D, hD, fun e he => isIntegral_of_intOE (h e ?_)⟩
  rw [mem_SI, Algebra.TensorProduct.comm_tmul] at he
  exact he

/- English proof (translation)
Rewrite using `[← mul_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem coe_mul_smul (a b : 𝓞 F) (x : E) : ((a * b : 𝓞 F) : F) • x = (a : F) • (b : F) • x := by
  rw [← mul_smul]; push_cast; rfl

/- English proof (translation)
Take `⟨d, hd, h⟩` from `den_fin (F := F) (E := E) fun i => (1 : Af F) ⊗ₜ[F] e i`. Take `⟨D, hD, h'⟩` from `incl_den (F := F) (E := E)`. Use `⟨D * d, mul_ne_zero hD hd, fun i => ?_⟩` and prove the remaining obligations. Use `h' ((d : F) • e i) (by rw [TensorProduct.tmul_smul]; exact h i)` as an intermediate fact. Rewrite using `[coe_mul_smul]` and apply the resulting hypothesis.
-/
theorem den_E {ι : Type*} [Finite ι] (e : ι → E) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, IsIntegral ℤ ((d : F) • e i) := by
  obtain ⟨d, hd, h⟩ := den_fin (F := F) (E := E) fun i => (1 : Af F) ⊗ₜ[F] e i
  obtain ⟨D, hD, h'⟩ := incl_den (F := F) (E := E)
  refine ⟨D * d, mul_ne_zero hD hd, fun i => ?_⟩
  have := h' ((d : F) • e i) (by rw [TensorProduct.tmul_smul]; exact h i)
  rwa [coe_mul_smul]

/- English proof (translation)
Use `set z : Fin M → Af F ⊗[F] E := fun k => (d1 : F) • Gi k j with hz`. Establish `hy : (c' : F) • z ∈ Λ` using `hlow z fun k => hd1 k j`. Establish `hv` using `hC _ hy`. Use `set v := (Gi * C * Gm).mulVec ((c' : F) • z) with hv'`. Establish `hz' : z = (d1 : F) • Gi.mulVec (Pi.single j 1)`.

Use extensionality with `k`. Simplify using `[hz]`. Establish `hM : Gm * (Gi * C * Gm * Gi) = C`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[hGG, Matrix.one_mul, Matrix.mul_assoc, hGG, Matrix.mul_one]`.

Establish `hGv : Gm.mulVec v = ((c' : F) * (d1 : F)) • C.mulVec (Pi.single j 1)`. Rewrite using `[hv', hz']`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mulVec_smul]`. Rewrite using `[hM, smul_smul]`. Establish `hvk : ∀ k, (c : F) • v k ∈ SI F E` using `hup v hv`.

Establish `key : ((c : F) * (d2 : F)) • (Gm.mulVec v) i ∈ SI F E`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.smul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `e : ((c : F) * (d2 : F)) • (Gm i k * v k) = ((d2 : F) • Gm i k) * ((c : F) • v k)`. Rewrite using `[smul_mul_smul_comm, mul_comm (d2 : F)]`.

Rewrite using `[e]`. Conclude with `mul_mem (hd2 i k) (hvk k)`. Establish `e2 : (((c' : F) * (d1 : F)) • C.mulVec (Pi.single j 1)) i = ((c' : F) * (d1 : F)) • C i j`. Simplify using the standard rewrite rules. Rewrite `key` using `[hGv, e2, smul_smul]`.

Conclude with `key`.
-/
theorem core {M : ℕ} (Λ : AddSubgroup (Fin M → Af F ⊗[F] E)) (c c' d1 d2 : 𝓞 F)
    (hup : ∀ y ∈ Λ, ∀ i, (c : F) • y i ∈ SI F E)
    (hlow : ∀ z : Fin M → Af F ⊗[F] E, (∀ i, z i ∈ SI F E) → (c' : F) • z ∈ Λ)
    (Gm Gi : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (hGG : Gm * Gi = 1)
    (hd1 : ∀ i j, (d1 : F) • Gi i j ∈ SI F E) (hd2 : ∀ i j, (d2 : F) • Gm i j ∈ SI F E)
    (C : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (hC : ∀ y ∈ Λ, (Gi * C * Gm).mulVec y ∈ Λ)
    (i j : Fin M) : ((c : F) * (d2 : F) * ((c' : F) * (d1 : F))) • C i j ∈ SI F E := by
  classical
  set z : Fin M → Af F ⊗[F] E := fun k => (d1 : F) • Gi k j with hz
  have hy : (c' : F) • z ∈ Λ := hlow z fun k => hd1 k j
  have hv := hC _ hy
  set v := (Gi * C * Gm).mulVec ((c' : F) • z) with hv'
  have hz' : z = (d1 : F) • Gi.mulVec (Pi.single j 1) := by
    ext k; simp [hz]
  have hM : Gm * (Gi * C * Gm * Gi) = C := by
    simp only [← Matrix.mul_assoc]
    rw [hGG, Matrix.one_mul, Matrix.mul_assoc, hGG, Matrix.mul_one]
  have hGv : Gm.mulVec v = ((c' : F) * (d1 : F)) • C.mulVec (Pi.single j 1) := by
    rw [hv', hz']
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    rw [hM, smul_smul]
  have hvk : ∀ k, (c : F) • v k ∈ SI F E := hup v hv
  have key : ((c : F) * (d2 : F)) • (Gm.mulVec v) i ∈ SI F E := by
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have e : ((c : F) * (d2 : F)) • (Gm i k * v k) = ((d2 : F) • Gm i k) * ((c : F) • v k) := by
      rw [smul_mul_smul_comm, mul_comm (d2 : F)]
    rw [e]
    exact mul_mem (hd2 i k) (hvk k)
  have e2 : (((c' : F) * (d1 : F)) • C.mulVec (Pi.single j 1)) i = ((c' : F) * (d1 : F)) • C i j := by
    simp
  rw [hGv, e2, smul_smul] at key
  exact key

end Gen

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def crd (W : Formalism.BasicNotions.HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

/- English proof (translation)
Set `r : 𝓞 E` to `⟨e, he⟩`. Establish `h` using `W.L0.smul_mem r hw`. Establish `h1 : r • w = e • w` using `(algebraMap_smul E r w).symm`. Rewrite using `[← h1]`. Conclude with `h`.
-/
theorem int_smul_mem (W : Formalism.BasicNotions.HSpace E) {e : E} (he : IsIntegral ℤ e) {w : W.V} (hw : w ∈ W.L0) :
    e • w ∈ W.L0 := by
  let r : 𝓞 E := ⟨e, he⟩
  have h := W.L0.smul_mem r hw
  have h1 : r • w = e • w := (algebraMap_smul E r w).symm
  rw [← h1]; exact h

/- English proof (translation)
Take `⟨s, hs⟩` from `W.standardTuple_isLattice.fg`. Take `⟨c, hc, h⟩` from `den_E (F := F) (E := E) (fun p : s × Fin W.rank => W.frame.repr p.1 p.2)`. Use `⟨c, hc, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hxi : x i = W.frame.repr (∑ k, x k • W.frame k) i`. Rewrite using `[W.frame.repr_sum_self]`.

Establish `key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set W.V), ∀ i, IsIntegral ℤ ((c : F) • W.frame.repr w i)`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy => exact fun i => h (⟨⟨y, hy⟩, i⟩)`. Consider the case `zero => intro i`.

Simplify using `using isIntegral_zero`. Consider the case `add y z _ _ hy hz`. Introduce `i`. Rewrite using `[map_add, Finsupp.add_apply, smul_add]`. Conclude with `(hy i).add (hz i)`.

Consider the case `smul r y _ hy`. Introduce `i`. Establish `e : r • y = (r : E) • y` using `(algebraMap_smul E r y).symm`. Rewrite using `[e, map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_smul_comm]`. Conclude with `r.isIntegral_coe.mul (hy i)`.

Establish `hx' : ∑ k, x k • W.frame k ∈ Submodule.span (𝓞 E) (s : Set W.V)` using `by rw [hs]; exact hx`. Rewrite using `[hxi]`. Conclude with `key _ hx' i`.
-/
theorem crd_up (W : Formalism.BasicNotions.HSpace E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ crd W, ∀ i, IsIntegral ℤ ((c : F) • x i) := by
  classical
  obtain ⟨s, hs⟩ := W.standardTuple_isLattice.fg
  obtain ⟨c, hc, h⟩ := den_E (F := F) (E := E) (fun p : s × Fin W.rank => W.frame.repr p.1 p.2)
  refine ⟨c, hc, fun x hx i => ?_⟩
  have hxi : x i = W.frame.repr (∑ k, x k • W.frame k) i := by
    rw [W.frame.repr_sum_self]
  have key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set W.V), ∀ i, IsIntegral ℤ ((c : F) • W.frame.repr w i) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact fun i => h (⟨⟨y, hy⟩, i⟩)
    | zero => intro i; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro i
      rw [map_add, Finsupp.add_apply, smul_add]
      exact (hy i).add (hz i)
    | smul r y _ hy =>
      intro i
      have e : r • y = (r : E) • y := (algebraMap_smul E r y).symm
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_smul_comm]
      exact r.isIntegral_coe.mul (hy i)
  have hx' : ∑ k, x k • W.frame k ∈ Submodule.span (𝓞 E) (s : Set W.V) := by rw [hs]; exact hx
  rw [hxi]
  exact key _ hx' i

/- English proof (translation)
Rewrite using `[show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul]`.
-/
theorem alg_mul (a b : 𝓞 F) :
    algebraMap F E ((a * b : 𝓞 F) : F) = algebraMap F E (a : F) * algebraMap F E (b : F) := by
  rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low W`.
-/
theorem crd_low (W : Formalism.BasicNotions.HSpace E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ crd W :=
  _root_.UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low W

end Lat

section Bound

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `hY : ∀ τ : E →+* ℂ, ∃ Y : Matrix (Fin W.rank) (Fin W.rank) ℂ, IsUnit Y.det ∧ ∀ y : W.V, ∑ i, ‖(Y.mulVec fun j => τ (W.frame.repr y j)) i‖ ^ 2 = (τ (W.hT y y)).re`. Introduce `τ`. Establish `h` using `hW τ`. Rewrite `h` using `[hsig τ]`. Conclude with `W.frame_of_pos τ (hτs τ) h`.

Use `choose Y hYu hYs using hY`. Set `R : (E →+* ℂ) → Fin W.rank → ℝ` to `fun τ j => Real.sqrt ((τ (W.gram j j)).re)`. Set `Bt : (E →+* ℂ) → ℝ` to `fun τ => (∑ k, ∑ l, ‖(Y τ)⁻¹ k l‖) * ∑ j, R τ j`. Establish `hBt : ∀ τ, 0 ≤ Bt τ` using `fun τ => mul_nonneg (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _)`. Use `⟨∑ τ, Bt τ, Finset.sum_nonneg fun τ _ => hBt τ, fun u hu τ i j => ?_⟩` and prove the remaining obligations.

Use `le_trans ?_ (Finset.single_le_sum (fun τ _ => hBt τ) (Finset.mem_univ τ))` and prove the remaining obligations. Use `set um := (u : Matrix (Fin W.rank) (Fin W.rank) E) with hum`. Establish `hu' : Formalism.UG.cT σ' um * W.gram * um = W.gram` using `hu`. Set `v : W.V` to `∑ k, um k j • W.frame k`. Establish `hrep : ∀ k, W.frame.repr v k = um k j`.

Introduce `k`. Simplify using `only [v, W.frame.repr_sum_self]`. Establish `e1 : W.hT v v = ∑ k, ∑ l, star (um k j) * (um l j * W.gram k l)`. Simplify using `only [v, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (Formalism.UG.cT σ' um * W.gram * um) j j = ∑ l, ∑ k, σ' (um k j) * W.gram k l * um l j`. Simplify using `only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`.

Establish `hform : W.hT v v = W.gram j j`. Establish `h0` using `congrFun (congrFun hu' j) j`. Rewrite `h0` using `[e2]`. Rewrite using `[e1, ← h0, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hσ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ l, ‖((Y τ).mulVec fun k => τ (um k j)) l‖ ^ 2 = (τ (W.gram j j)).re`. Rewrite using `[← hform, ← hYs τ v]`. Simplify using `only [hrep]`.

Use `set w := (Y τ).mulVec fun k => τ (um k j) with hwdef`. Establish `hw : ∀ l, ‖w l‖ ≤ R τ j` using `fun l => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hsum]`. Conclude with `Finset.single_le_sum (f := fun l => ‖w l‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ l))`.

Establish `hzw : (fun k => τ (um k j)) = (Y τ)⁻¹.mulVec w`. Rewrite using `[hwdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec]`. Establish `hi : τ (um i j) = ((Y τ)⁻¹.mulVec w) i` using `congrFun hzw i`. Rewrite using `[hi]`. Establish `h1 : ‖((Y τ)⁻¹.mulVec w) i‖ ≤ ∑ l, ‖(Y τ)⁻¹ i l‖ * ‖w l‖`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)`. Establish `h2 : ∑ l, ‖(Y τ)⁻¹ i l‖ * ‖w l‖ ≤ (∑ l, ‖(Y τ)⁻¹ i l‖) * R τ j`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hw l) (norm_nonneg _)`.

Establish `h3 : (∑ l, ‖(Y τ)⁻¹ i l‖) ≤ ∑ k, ∑ l, ‖(Y τ)⁻¹ k l‖` using `Finset.single_le_sum (f := fun k => ∑ l, ‖(Y τ)⁻¹ k l‖) (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.mem_univ i)`. Establish `h4 : R τ j ≤ ∑ j', R τ j'` using `Finset.single_le_sum (f := R τ) (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ j)`. Conclude with `h1.trans (h2.trans (mul_le_mul h3 h4 (Real.sqrt_nonneg _) (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _)))`.
-/
theorem unit_bound (W : Formalism.BasicNotions.HSpace E) (σ' : E →+* E) (hσ : ∀ a, σ' a = star a)
    (hτs : ∀ τ : E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Formalism.UG.UJ σ' W.gram, ∀ (τ : E →+* ℂ) i j,
      ‖τ ((u : Matrix (Fin W.rank) (Fin W.rank) E) i j)‖ ≤ B := by
  classical
  have hY : ∀ τ : E →+* ℂ, ∃ Y : Matrix (Fin W.rank) (Fin W.rank) ℂ, IsUnit Y.det ∧
      ∀ y : W.V, ∑ i, ‖(Y.mulVec fun j => τ (W.frame.repr y j)) i‖ ^ 2 = (τ (W.hT y y)).re := by
    intro τ
    have h := hW τ
    rw [hsig τ] at h
    exact W.frame_of_pos τ (hτs τ) h
  choose Y hYu hYs using hY
  let R : (E →+* ℂ) → Fin W.rank → ℝ := fun τ j => Real.sqrt ((τ (W.gram j j)).re)
  let Bt : (E →+* ℂ) → ℝ := fun τ => (∑ k, ∑ l, ‖(Y τ)⁻¹ k l‖) * ∑ j, R τ j
  have hBt : ∀ τ, 0 ≤ Bt τ := fun τ =>
    mul_nonneg (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _)
      (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _)
  refine ⟨∑ τ, Bt τ, Finset.sum_nonneg fun τ _ => hBt τ, fun u hu τ i j => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (fun τ _ => hBt τ) (Finset.mem_univ τ))
  set um := (u : Matrix (Fin W.rank) (Fin W.rank) E) with hum
  have hu' : Formalism.UG.cT σ' um * W.gram * um = W.gram := hu
  let v : W.V := ∑ k, um k j • W.frame k
  have hrep : ∀ k, W.frame.repr v k = um k j := by
    intro k; simp only [v, W.frame.repr_sum_self]
  have e1 : W.hT v v = ∑ k, ∑ l, star (um k j) * (um l j * W.gram k l) := by
    simp only [v, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [RingHom.id_apply]; ring
  have e2 : (Formalism.UG.cT σ' um * W.gram * um) j j = ∑ l, ∑ k, σ' (um k j) * W.gram k l * um l j := by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  have hform : W.hT v v = W.gram j j := by
    have h0 := congrFun (congrFun hu' j) j
    rw [e2] at h0
    rw [e1, ← h0, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hσ]; ring
  have hsum : ∑ l, ‖((Y τ).mulVec fun k => τ (um k j)) l‖ ^ 2 = (τ (W.gram j j)).re := by
    rw [← hform, ← hYs τ v]
    simp only [hrep]
  set w := (Y τ).mulVec fun k => τ (um k j) with hwdef
  have hw : ∀ l, ‖w l‖ ≤ R τ j := fun l => by
    calc ‖w l‖ = Real.sqrt (‖w l‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ R τ j := Real.sqrt_le_sqrt (by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun l => ‖w l‖ ^ 2) (fun l _ => by positivity)
            (Finset.mem_univ l))
  have hzw : (fun k => τ (um k j)) = (Y τ)⁻¹.mulVec w := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec]
  have hi : τ (um i j) = ((Y τ)⁻¹.mulVec w) i := congrFun hzw i
  rw [hi]
  have h1 : ‖((Y τ)⁻¹.mulVec w) i‖ ≤ ∑ l, ‖(Y τ)⁻¹ i l‖ * ‖w l‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
  have h2 : ∑ l, ‖(Y τ)⁻¹ i l‖ * ‖w l‖ ≤ (∑ l, ‖(Y τ)⁻¹ i l‖) * R τ j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hw l) (norm_nonneg _)
  have h3 : (∑ l, ‖(Y τ)⁻¹ i l‖) ≤ ∑ k, ∑ l, ‖(Y τ)⁻¹ k l‖ :=
    Finset.single_le_sum (f := fun k => ∑ l, ‖(Y τ)⁻¹ k l‖)
      (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.mem_univ i)
  have h4 : R τ j ≤ ∑ j', R τ j' :=
    Finset.single_le_sum (f := R τ) (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ j)
  exact h1.trans (h2.trans (mul_le_mul h3 h4 (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _)))

end Bound

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

abbrev GamG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) :=
  HFinIn (AF F) σ J

/- English proof (translation)
Introduce `v` and use `ha v`.
-/
theorem intAd_of_intAf {a : Af F} (ha : a ∈ intAf F) : a ∈ intAd F := fun v => ha v

/- English proof (translation)
Take `⟨c, hc, h⟩` from `crd_up (F := F) W`. Use `⟨c, hc, fun y hy => ?_⟩` and prove the remaining obligations. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`.

Introduce `i`. Rewrite using `[← TensorProduct.tmul_smul, mem_SI, Algebra.TensorProduct.comm_tmul]`. Conclude with `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tmul_mem_SS (intOE_of_isIntegral (h x hx i)) (intAd_of_intAf ha)`. Consider the case `zero => intro i`. Simplify using `only [Pi.zero_apply, smul_zero]`.

Conclude with `(SI F E).zero_mem`. Consider the case `add y z _ _ hy hz`. Introduce `i`. Rewrite using `[Pi.add_apply, smul_add]`. Conclude with `(SI F E).add_mem (hy i) (hz i)`.

Consider the case `neg y _ hy`. Introduce `i`. Rewrite using `[Pi.neg_apply, smul_neg]`. Conclude with `(SI F E).neg_mem (hy i)`.
-/
theorem latHat_up (W : Formalism.BasicNotions.HSpace E) : ∃ c : 𝓞 F, c ≠ 0 ∧
    ∀ y ∈ latHat F E (crd W), ∀ i, (c : F) • y i ∈ SI F E := by
  obtain ⟨c, hc, h⟩ := crd_up (F := F) W
  refine ⟨c, hc, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    intro i
    rw [← TensorProduct.tmul_smul, mem_SI, Algebra.TensorProduct.comm_tmul]
    exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tmul_mem_SS (intOE_of_isIntegral (h x hx i)) (intAd_of_intAf ha)
  | zero => intro i; simp only [Pi.zero_apply, smul_zero]; exact (SI F E).zero_mem
  | add y z _ _ hy hz =>
    intro i; rw [Pi.add_apply, smul_add]; exact (SI F E).add_mem (hy i) (hz i)
  | neg y _ hy =>
    intro i; rw [Pi.neg_apply, smul_neg]; exact (SI F E).neg_mem (hy i)

/- English proof (translation)
Take `⟨c, hc, h⟩` from `crd_low (F := F) W`. Use `⟨c, hc, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.univ_sum_single z, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `key : ∀ w ∈ AddSubgroup.closure {y : E ⊗[F] Af F | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a}, ∀ x, swp F E x = w → (c : F) • Pi.single i x ∈ latHat F E (crd W)`.

Introduce `w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨e, he, a, ha, rfl⟩` from `hw`. Introduce `x hx`.

Establish `hxa : x = a ⊗ₜ[F] e` using `(swp F E).injective (by rw [hx, Algebra.TensorProduct.comm_tmul])`. Substitute `hxa` using the available equality. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨a, fun v => ha v, Pi.single i ((c : F) • e), h i e (isIntegral_of_intOE he), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[TensorProduct.tmul_smul]`. Simplify using `[hk]`. Consider the case `zero`.

Introduce `x hx`. Establish `hx0 : x = 0` using `(swp F E).injective (by rw [hx, map_zero])`. Substitute `hx0` using the available equality. Simplify using the standard rewrite rules. Consider the case `add w1 w2 _ _ h1 h2`.

Introduce `x hx`. Establish `hx' : x = (swp F E).symm w1 + (swp F E).symm w2` using `(swp F E).injective (by rw [hx, map_add, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply])`. Rewrite using `[hx', Pi.single_add, smul_add]`. Conclude with `add_mem (h1 _ (AlgEquiv.apply_symm_apply _ _)) (h2 _ (AlgEquiv.apply_symm_apply _ _))`. Consider the case `neg w _ h1`.

Introduce `x hx`. Establish `hx' : x = -(swp F E).symm w` using `(swp F E).injective (by rw [hx, map_neg, AlgEquiv.apply_symm_apply])`. Rewrite using `[hx', Pi.single_neg, smul_neg]`. Conclude with `neg_mem (h1 _ (AlgEquiv.apply_symm_apply _ _))`. Conclude with `key _ (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mem_closure_of_mem_SS (hz i)) _ rfl`.
-/
theorem latHat_low (W : Formalism.BasicNotions.HSpace E) : ∃ c : 𝓞 F, c ≠ 0 ∧
    ∀ z : Fin W.rank → Af F ⊗[F] E, (∀ i, z i ∈ SI F E) → (c : F) • z ∈ latHat F E (crd W) := by
  classical
  obtain ⟨c, hc, h⟩ := crd_low (F := F) W
  refine ⟨c, hc, fun z hz => ?_⟩
  rw [← Finset.univ_sum_single z, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have key : ∀ w ∈ AddSubgroup.closure {y : E ⊗[F] Af F | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a},
      ∀ x, swp F E x = w → (c : F) • Pi.single i x ∈ latHat F E (crd W) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨e, he, a, ha, rfl⟩ := hw
      intro x hx
      have hxa : x = a ⊗ₜ[F] e :=
        (swp F E).injective (by rw [hx, Algebra.TensorProduct.comm_tmul])
      subst hxa
      apply AddSubgroup.subset_closure
      refine ⟨a, fun v => ha v, Pi.single i ((c : F) • e), h i e (isIntegral_of_intOE he), ?_⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp [TensorProduct.tmul_smul]
      · simp [hk]
    | zero =>
      intro x hx
      have hx0 : x = 0 := (swp F E).injective (by rw [hx, map_zero])
      subst hx0
      simp
    | add w1 w2 _ _ h1 h2 =>
      intro x hx
      have hx' : x = (swp F E).symm w1 + (swp F E).symm w2 :=
        (swp F E).injective (by rw [hx, map_add, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply])
      rw [hx', Pi.single_add, smul_add]
      exact add_mem (h1 _ (AlgEquiv.apply_symm_apply _ _)) (h2 _ (AlgEquiv.apply_symm_apply _ _))
    | neg w _ h1 =>
      intro x hx
      have hx' : x = -(swp F E).symm w :=
        (swp F E).injective (by rw [hx, map_neg, AlgEquiv.apply_symm_apply])
      rw [hx', Pi.single_neg, smul_neg]
      exact neg_mem (h1 _ (AlgEquiv.apply_symm_apply _ _))
  exact key _ (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mem_closure_of_mem_SS (hz i)) _ rfl

/- English proof (translation)
Unfold `finMat`. Rewrite using `[← hu]`. Use extensionality with `i j`. Simplify using `[Formalism.UG.bc, inclR, Algebra.TensorProduct.map_tmul]`.
-/
theorem finMat_rat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (u : GL (Fin M) E) (h : HA (AF F) σ J)
    (hu : Formalism.UG.bc (inclR (AF F)) u = HA.mat (AF F) σ J h) :
    finMat σ J h = (u : Matrix (Fin M) (Fin M) E).map fun e => (1 : Af F) ⊗ₜ[F] e := by
  unfold finMat
  rw [← hu]
  ext i j
  simp [Formalism.UG.bc, inclR, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Establish `hmem : ∀ γ : GamG σ W.gram, ∃ u ∈ Formalism.UG.UJ (σ : E →+* E) W.gram, Formalism.UG.bc (inclR (AF F)) u = HA.mat (AF F) σ W.gram (γ : HA (AF F) σ W.gram)` using `fun γ => Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp γ.2)`. Use `choose u hu hbc using hmem`. Use `set Gm := finMat σ W.gram g with hGm`. Use `set Gi := finMat σ W.gram g⁻¹ with hGi`. Establish `hGG : Gm * Gi = 1` using `by rw [hGm, hGi, ← finMat_mul, mul_inv_cancel, finMat_one]`.

Take `⟨d1, hd1n, hd1⟩` from `den_fin (F := F) (E := E) (fun p : Fin W.rank × Fin W.rank => Gi p.1 p.2)`. Take `⟨d2, hd2n, hd2⟩` from `den_fin (F := F) (E := E) (fun p : Fin W.rank × Fin W.rank => Gm p.1 p.2)`. Take `⟨c, hcn, hup⟩` from `latHat_up (F := F) W`. Take `⟨c', hc'n, hlow⟩` from `latHat_low (F := F) W`. Take `⟨Dd, hDn, hD⟩` from `incl_den (F := F) (E := E)`.

Take `⟨B, hB0, hB⟩` from `unit_bound W (σ : E →+* E) hσ hτs hW hsig`. Use `set s : F := (Dd : F) * ((c : F) * (d2 : F) * ((c' : F) * (d1 : F))) with hs`. Establish `hne : ∀ x : 𝓞 F, x ≠ 0 → (x : F) ≠ 0` using `fun x hx h0 => hx (by exact_mod_cast h0)`. Establish `hs0 : s ≠ 0`. Rewrite using `[hs]`.

Conclude with `mul_ne_zero (hne _ hDn) (mul_ne_zero (mul_ne_zero (hne _ hcn) (hne _ hd2n)) (mul_ne_zero (hne _ hc'n) (hne _ hd1n)))`. Establish `hint : ∀ γ ∈ Unfold.stab (GamG σ W.gram) K g, ∀ i j, IsIntegral ℤ (s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j)`. Introduce `γ hγ i j`. Establish `hC : ∀ y ∈ latHat F E (crd W), (Gi * finMat σ W.gram (γ : HA (AF F) σ W.gram) * Gm).mulVec y ∈ latHat F E (crd W)`. Introduce `y hy`.

Establish `h1` using `hK _ hγ y hy`. Rewrite `h1` using `[finMat_mul, finMat_mul, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `h2` using `core _ c c' d1 d2 hup hlow Gm Gi hGG (fun i j => hd1 (i, j)) (fun i j => hd2 (i, j)) _ hC i j`. Rewrite `h2` using `[finMat_rat σ W.gram (u γ) _ (hbc γ), Matrix.map_apply, ← TensorProduct.tmul_smul]`. Establish `h3` using `hD _ h2`.

Rewrite `h3` using `[smul_smul]`. Then use the resulting hypothesis. Establish `hS` using `NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ) ((∑ τ : E →+* ℂ, ‖τ (algebraMap F E s)‖) * B)`. Set `f : GamG σ W.gram → Fin W.rank → Fin W.rank → E` to `fun γ i j => s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j`. Use `Set.Finite.of_finite_image (f := f) ?_ ?_` and prove the remaining obligations. Use `(Set.Finite.pi (fun _ : Fin W.rank => Set.Finite.pi (fun _ : Fin W.rank => hS))).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Introduce `i j`. Use `⟨hint γ hγ i j, fun τ => ?_⟩` and prove the remaining obligations. Use `show ‖τ (s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j)‖ ≤ _`.

Rewrite using `[Algebra.smul_def, map_mul, norm_mul]`. Conclude with `mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (algebraMap F E s)‖) (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)) (hB _ (hu γ) τ i j) (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)`. Introduce `γ _ γ' _ h`. Establish `hu' : (u γ : Matrix (Fin W.rank) (Fin W.rank) E) = u γ'`. Use extensionality with `i j`.

Conclude with `smul_right_injective E hs0 (congrFun (congrFun h i) j)`. Establish `h2 : HA.mat (AF F) σ W.gram (γ : HA (AF F) σ W.gram) = HA.mat (AF F) σ W.gram (γ' : HA (AF F) σ W.gram)`. Rewrite using `[← hbc, ← hbc, Units.ext hu']`. Conclude with `Subtype.ext (Subtype.ext h2)`.
-/
theorem stab_finite (W : Formalism.BasicNotions.HSpace E) (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hτs : ∀ τ : E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (K : Subgroup (HA (AF F) σ W.gram))
    (hK : ∀ k ∈ K, ∀ y ∈ latHat F E (crd W), (finMat σ W.gram k).mulVec y ∈ latHat F E (crd W))
    (g : HA (AF F) σ W.gram) : (Unfold.stab (GamG σ W.gram) K g).Finite := by
  classical
  have hmem : ∀ γ : GamG σ W.gram, ∃ u ∈ Formalism.UG.UJ (σ : E →+* E) W.gram,
      Formalism.UG.bc (inclR (AF F)) u = HA.mat (AF F) σ W.gram (γ : HA (AF F) σ W.gram) :=
    fun γ => Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp γ.2)
  choose u hu hbc using hmem
  set Gm := finMat σ W.gram g with hGm
  set Gi := finMat σ W.gram g⁻¹ with hGi
  have hGG : Gm * Gi = 1 := by rw [hGm, hGi, ← finMat_mul, mul_inv_cancel, finMat_one]
  obtain ⟨d1, hd1n, hd1⟩ := den_fin (F := F) (E := E) (fun p : Fin W.rank × Fin W.rank => Gi p.1 p.2)
  obtain ⟨d2, hd2n, hd2⟩ := den_fin (F := F) (E := E) (fun p : Fin W.rank × Fin W.rank => Gm p.1 p.2)
  obtain ⟨c, hcn, hup⟩ := latHat_up (F := F) W
  obtain ⟨c', hc'n, hlow⟩ := latHat_low (F := F) W
  obtain ⟨Dd, hDn, hD⟩ := incl_den (F := F) (E := E)
  obtain ⟨B, hB0, hB⟩ := unit_bound W (σ : E →+* E) hσ hτs hW hsig
  set s : F := (Dd : F) * ((c : F) * (d2 : F) * ((c' : F) * (d1 : F))) with hs
  have hne : ∀ x : 𝓞 F, x ≠ 0 → (x : F) ≠ 0 := fun x hx h0 => hx (by exact_mod_cast h0)
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (hne _ hDn) (mul_ne_zero (mul_ne_zero (hne _ hcn) (hne _ hd2n))
      (mul_ne_zero (hne _ hc'n) (hne _ hd1n)))
  have hint : ∀ γ ∈ Unfold.stab (GamG σ W.gram) K g, ∀ i j,
      IsIntegral ℤ (s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j) := by
    intro γ hγ i j
    have hC : ∀ y ∈ latHat F E (crd W),
        (Gi * finMat σ W.gram (γ : HA (AF F) σ W.gram) * Gm).mulVec y ∈ latHat F E (crd W) := by
      intro y hy
      have h1 := hK _ hγ y hy
      rwa [finMat_mul, finMat_mul, ← Matrix.mul_assoc] at h1
    have h2 := core _ c c' d1 d2 hup hlow Gm Gi hGG (fun i j => hd1 (i, j)) (fun i j => hd2 (i, j)) _ hC i j
    rw [finMat_rat σ W.gram (u γ) _ (hbc γ), Matrix.map_apply, ← TensorProduct.tmul_smul] at h2
    have h3 := hD _ h2
    rwa [smul_smul] at h3
  have hS := NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ)
    ((∑ τ : E →+* ℂ, ‖τ (algebraMap F E s)‖) * B)
  let f : GamG σ W.gram → Fin W.rank → Fin W.rank → E :=
    fun γ i j => s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j
  refine Set.Finite.of_finite_image (f := f) ?_ ?_
  · refine (Set.Finite.pi (fun _ : Fin W.rank => Set.Finite.pi (fun _ : Fin W.rank => hS))).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i j
    refine ⟨hint γ hγ i j, fun τ => ?_⟩
    show ‖τ (s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j)‖ ≤ _
    rw [Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (algebraMap F E s)‖)
      (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)) (hB _ (hu γ) τ i j) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  · intro γ _ γ' _ h
    have hu' : (u γ : Matrix (Fin W.rank) (Fin W.rank) E) = u γ' := by
      ext i j
      exact smul_right_injective E hs0 (congrFun (congrFun h i) j)
    have h2 : HA.mat (AF F) σ W.gram (γ : HA (AF F) σ W.gram) =
        HA.mat (AF F) σ W.gram (γ' : HA (AF F) σ W.gram) := by
      rw [← hbc, ← hbc, Units.ext hu']
    exact Subtype.ext (Subtype.ext h2)

end Gen2

section Open

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isModTopF : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩

/- English proof (translation)
Use `isModTopF (F := F) (E := E)` as an intermediate fact. Conclude with `IsModuleTopology.topologicalAddGroup (R := Af F) _`.
-/
theorem addGrpF : IsTopologicalAddGroup (Af F ⊗[F] E) := by
  have := isModTopF (F := F) (E := E)
  exact IsModuleTopology.topologicalAddGroup (R := Af F) _

def crdF {ι : Type} (b : Module.Basis ι F E) (i : ι) : Af F ⊗[F] E →ₗ[Af F] Af F where
  toFun := (TensorProduct.rid F (Af F)).toLinearMap ∘ₗ LinearMap.lTensor (Af F) (b.coord i)
  map_add' := map_add _
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e =>
      rw [TensorProduct.smul_tmul']
      simp [smul_eq_mul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/- English proof (translation)
Simplify using `[crdF]`.
-/
theorem crdF_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (a : Af F) (e : E) :
    crdF b i (a ⊗ₜ[F] e) = b.repr e i • a := by
  simp [crdF]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `only [crdF_tmul, TensorProduct.smul_tmul]`. Rewrite using `[← TensorProduct.tmul_sum, Module.Basis.sum_repr]`.

Consider the case `add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]`.
-/
theorem sum_crdF {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (x : Af F ⊗[F] E) :
    ∑ i, crdF b i x ⊗ₜ[F] b i = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [crdF_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, Module.Basis.sum_repr]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

/- English proof (translation)
Use `isModTopF (F := F) (E := E)` as an intermediate fact. Use `addGrpF (F := F) (E := E)` as an intermediate fact. Take `⟨n, b, -, -, hb, -⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_basis F E`. Set `O : Set (Af F ⊗[F] E)` to `⋂ i, (crdF b i) ⁻¹' (intAd F : Set (Af F))`. Establish `hO : IsOpen O` using `isOpen_iInter_of_finite fun i => (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd (F := F)).preimage (IsModuleTopology.continuous_of_linearMap (crdF b i))`.

Establish `hOS : O ⊆ SI F E`. Introduce `x hx`. Rewrite using `[← sum_crdF b x]`. Use `Subring.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mem_SI, Algebra.TensorProduct.comm_tmul]`.

Conclude with `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tmul_mem_SS (hb i) (Set.mem_iInter.mp hx i)`. Establish `h0 : (0 : Af F ⊗[F] E) ∈ O` using `Set.mem_iInter.mpr fun i => by`. Simplify using `only [Set.mem_preimage, map_zero]`. Conclude with `(intAd F).zero_mem`. Conclude with `AddSubgroup.isOpen_of_mem_nhds (SI F E).toAddSubgroup (Filter.mem_of_superset (hO.mem_nhds h0) hOS)`.
-/
theorem isOpen_SI : IsOpen (SI F E : Set (Af F ⊗[F] E)) := by
  have := isModTopF (F := F) (E := E)
  have := addGrpF (F := F) (E := E)
  obtain ⟨n, b, -, -, hb, -⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_basis F E
  let O : Set (Af F ⊗[F] E) := ⋂ i, (crdF b i) ⁻¹' (intAd F : Set (Af F))
  have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
    (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd (F := F)).preimage
      (IsModuleTopology.continuous_of_linearMap (crdF b i))
  have hOS : O ⊆ SI F E := by
    intro x hx
    rw [← sum_crdF b x]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mem_SI, Algebra.TensorProduct.comm_tmul]
    exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tmul_mem_SS (hb i) (Set.mem_iInter.mp hx i)
  have h0 : (0 : Af F ⊗[F] E) ∈ O := Set.mem_iInter.mpr fun i => by
    simp only [Set.mem_preimage, map_zero]; exact (intAd F).zero_mem
  exact AddSubgroup.isOpen_of_mem_nhds (SI F E).toAddSubgroup
    (Filter.mem_of_superset (hO.mem_nhds h0) hOS)

/- English proof (translation)
Use `isModTopF (F := F) (E := E)` as an intermediate fact. Establish `e : (fun x : Af F ⊗[F] E => r • x) = fun x => algebraMap F (Af F) r • x`. Use function extensionality and compare the values at `fun x => (algebraMap_smul (Af F) r x).symm`. Establish `hc : Continuous fun x : Af F ⊗[F] E => r • x` using `by rw [e]; exact continuous_const_smul _`. Conclude with `isOpen_SI.preimage hc`.
-/
theorem isOpen_SIm (r : F) : IsOpen {x : Af F ⊗[F] E | r • x ∈ SI F E} := by
  have := isModTopF (F := F) (E := E)
  have e : (fun x : Af F ⊗[F] E => r • x) = fun x => algebraMap F (Af F) r • x :=
    funext fun x => (algebraMap_smul (Af F) r x).symm
  have hc : Continuous fun x : Af F ⊗[F] E => r • x := by rw [e]; exact continuous_const_smul _
  exact isOpen_SI.preimage hc

def finPr : AF F ⊗[F] E →ₛₗ[(sndA F : AF F →+* Af F)] Af F ⊗[F] E where
  toFun := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
  map_add' := map_add _
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e =>
      rw [TensorProduct.smul_tmul']
      simp [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/- English proof (translation)
Use `Unfold.isModTop (F := F) (E := E)` as an intermediate fact. Use `isModTopF (F := F) (E := E)` as an intermediate fact. Use `addGrpF (F := F) (E := E)` as an intermediate fact. Conclude with `IsModuleTopology.continuous_of_linearMapₛₗ (by exact continuous_snd) finPr`.
-/
theorem continuous_finPr : Continuous (finPr (F := F) (E := E)) := by
  have := Unfold.isModTop (F := F) (E := E)
  have := isModTopF (F := F) (E := E)
  have := addGrpF (F := F) (E := E)
  exact IsModuleTopology.continuous_of_linearMapₛₗ (by exact continuous_snd) finPr

/- English proof (translation)
Establish `h1 : Continuous fun h : HA (AF F) σ J => ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j` using `(continuous_apply j).comp ((continuous_apply i).comp ((Units.continuous_val : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).comp continuous_subtype_val))`. Conclude with `continuous_finPr.comp h1`.
-/
theorem continuous_finMat_entry (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (i j : Fin M) :
    Continuous fun h : HA (AF F) σ J => finMat σ J h i j := by
  have h1 : Continuous fun h : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j :=
    (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) =>
        (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).comp continuous_subtype_val))
  exact continuous_finPr.comp h1

def SFin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) :
    Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  mul_mem' := by
    intro h h' hh hh' y
    rw [finMat_mul, ← Matrix.mulVec_mulVec, hh' y]
    exact hh _
  one_mem' := by intro y; rw [finMat_one, Matrix.one_mulVec]
  inv_mem' := by
    intro h hh y
    have e : (finMat σ J h).mulVec ((finMat σ J h⁻¹).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]
    have := hh ((finMat σ J h⁻¹).mulVec y)
    rw [e] at this
    exact this.symm

variable [StarRing E]

/- English proof (translation)
Establish `e1 : X.mulVec y = y + (X - 1).mulVec y`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Set `z : Fin W.rank → Af F ⊗[F] E` to `fun i => ∑ k, (((c : F) * (c' : F))⁻¹ • (X - 1) i k) * ((c : F) • y k)`. Establish `hz : ∀ i, z i ∈ SI F E` using `fun i => Subring.sum_mem _ fun k _ => mul_mem (by rw [Matrix.sub_apply]; exact hX i k) (hup y hy k)`.

Establish `e2 : (X - 1).mulVec y = (c' : F) • z`. Use function extensionality and compare the values at `i`. Simplify using `only [z, Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, smul_smul]`.

Establish `: (c' : F) * (((c : F) * (c' : F))⁻¹ * (c : F)) = 1` using `by field_simp`. Rewrite using `[this, one_smul]`. Rewrite using `[e1, e2]`. Conclude with `add_mem hy (hlow z hz)`.
-/
theorem near (W : Formalism.BasicNotions.HSpace E) (c c' : 𝓞 F) (hc0 : (c : F) ≠ 0) (hc0' : (c' : F) ≠ 0)
    (hup : ∀ y ∈ latHat F E (crd W), ∀ i, (c : F) • y i ∈ SI F E)
    (hlow : ∀ z : Fin W.rank → Af F ⊗[F] E, (∀ i, z i ∈ SI F E) → (c' : F) • z ∈ latHat F E (crd W))
    (X : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E))
    (hX : ∀ i j, ((c : F) * (c' : F))⁻¹ • (X i j - (1 : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E)) i j) ∈ SI F E)
    (y : Fin W.rank → Af F ⊗[F] E) (hy : y ∈ latHat F E (crd W)) : X.mulVec y ∈ latHat F E (crd W) := by
  have e1 : X.mulVec y = y + (X - 1).mulVec y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  let z : Fin W.rank → Af F ⊗[F] E := fun i =>
    ∑ k, (((c : F) * (c' : F))⁻¹ • (X - 1) i k) * ((c : F) • y k)
  have hz : ∀ i, z i ∈ SI F E := fun i =>
    Subring.sum_mem _ fun k _ => mul_mem (by rw [Matrix.sub_apply]; exact hX i k) (hup y hy k)
  have e2 : (X - 1).mulVec y = (c' : F) • z := by
    funext i
    simp only [z, Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_smul_comm, smul_smul]
    have : (c' : F) * (((c : F) * (c' : F))⁻¹ * (c : F)) = 1 := by field_simp
    rw [this, one_smul]
  rw [e1, e2]
  exact add_mem hy (hlow z hz)

/- English proof (translation)
Use `Unfold.topGroupHA σ W.gram` as an intermediate fact. Use `addGrpF (F := F) (E := E)` as an intermediate fact. Take `⟨c, hc, hup⟩` from `latHat_up (F := F) W`. Take `⟨c', hc', hlow⟩` from `latHat_low (F := F) W`. Establish `hne : ∀ x : 𝓞 F, x ≠ 0 → (x : F) ≠ 0` using `fun x hx h0 => hx (by exact_mod_cast h0)`.

Set `r : F` to `((c : F) * (c' : F))⁻¹`. Set `N1 : Set (HA (AF F) σ W.gram)` to `⋂ p : Fin W.rank × Fin W.rank, (fun h => finMat σ W.gram h p.1 p.2 - (1 : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E)) p.1 p.2) ⁻¹' {x | r • x ∈ SI F E}`. Apply the tactic sequence `have hN1o : IsOpen N1 := isOpen_iInter_of_finite fun p => (isOpen_SIm r).preimage ((continuous_finMat_entry σ W.gram p.1 p.2).sub continuous_const)`. Establish `h1N1 : (1 : HA (AF F) σ W.gram) ∈ N1` using `Set.mem_iInter.mpr fun p => by`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, finMat_one, sub_self, smul_zero]`.

Conclude with `(SI F E).zero_mem`. Establish `hN1 : N1 ∈ nhds (1 : HA (AF F) σ W.gram)` using `hN1o.mem_nhds h1N1`. Establish `hN1i : (fun h : HA (AF F) σ W.gram => h⁻¹) ⁻¹' N1 ∈ nhds (1 : HA (AF F) σ W.gram)`. Use `continuous_inv.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[inv_one]`.

Conclude with `hN1`. Establish `hnear : ∀ h ∈ N1, ∀ y ∈ latHat F E (crd W), (finMat σ W.gram h).mulVec y ∈ latHat F E (crd W)` using `fun h hh y hy => near W c c' (hne c hc) (hne c' hc') hup hlow _ (fun i j => Set.mem_iInter.mp hh (i, j)) y hy`. Use `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (Filter.inter_mem hN1 hN1i) ?_)` and prove the remaining obligations. Introduce and unpack `h ⟨hh, hhi⟩ y`. Use `⟨fun hy => hnear h hh y hy, fun hy => ?_⟩` and prove the remaining obligations.

Use `hnear h⁻¹ hhi _ hy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem isOpen_SFin (W : Formalism.BasicNotions.HSpace E) (σ : E →ₐ[F] E) :
    IsOpen (SFin σ W.gram (crd W) : Set (HA (AF F) σ W.gram)) := by
  have := Unfold.topGroupHA σ W.gram
  have := addGrpF (F := F) (E := E)
  obtain ⟨c, hc, hup⟩ := latHat_up (F := F) W
  obtain ⟨c', hc', hlow⟩ := latHat_low (F := F) W
  have hne : ∀ x : 𝓞 F, x ≠ 0 → (x : F) ≠ 0 := fun x hx h0 => hx (by exact_mod_cast h0)
  let r : F := ((c : F) * (c' : F))⁻¹
  let N1 : Set (HA (AF F) σ W.gram) := ⋂ p : Fin W.rank × Fin W.rank,
    (fun h => finMat σ W.gram h p.1 p.2 - (1 : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E)) p.1 p.2) ⁻¹'
      {x | r • x ∈ SI F E}
  have hN1o : IsOpen N1 := isOpen_iInter_of_finite fun p =>
    (isOpen_SIm r).preimage ((continuous_finMat_entry σ W.gram p.1 p.2).sub continuous_const)
  have h1N1 : (1 : HA (AF F) σ W.gram) ∈ N1 := Set.mem_iInter.mpr fun p => by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, finMat_one, sub_self, smul_zero]
    exact (SI F E).zero_mem
  have hN1 : N1 ∈ nhds (1 : HA (AF F) σ W.gram) := hN1o.mem_nhds h1N1
  have hN1i : (fun h : HA (AF F) σ W.gram => h⁻¹) ⁻¹' N1 ∈ nhds (1 : HA (AF F) σ W.gram) := by
    refine continuous_inv.continuousAt.preimage_mem_nhds ?_
    rw [inv_one]; exact hN1
  have hnear : ∀ h ∈ N1, ∀ y ∈ latHat F E (crd W), (finMat σ W.gram h).mulVec y ∈ latHat F E (crd W) :=
    fun h hh y hy => near W c c' (hne c hc) (hne c' hc') hup hlow _
      (fun i j => Set.mem_iInter.mp hh (i, j)) y hy
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (Filter.inter_mem hN1 hN1i) ?_)
  rintro h ⟨hh, hhi⟩ y
  refine ⟨fun hy => hnear h hh y hy, fun hy => ?_⟩
  have := hnear h⁻¹ hhi _ hy
  rwa [Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec] at this

end Open

section Inf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

/- English proof (translation)
Use `(NumberField.InfiniteAdeleRing.denseRange_algebraMap (K := F)).induction_on (p := fun b => starRingEnd ℂ (θ (b ⊗ₜ[F] (1 : E))) = θ (b ⊗ₜ[F] (1 : E))) a (isClosed_eq (Complex.continuous_conj.comp hθ.2) hθ.2) (fun x => ?_)` and prove the remaining obligations. Establish `e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E x`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Use `show starRingEnd ℂ (θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))) = θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))`. Rewrite using `[e, hθ.1, ← hτs, hfix]`.
-/
theorem infEmb_real (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hθ : IsInfEmb τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine (NumberField.InfiniteAdeleRing.denseRange_algebraMap (K := F)).induction_on
    (p := fun b => starRingEnd ℂ (θ (b ⊗ₜ[F] (1 : E))) = θ (b ⊗ₜ[F] (1 : E))) a
    (isClosed_eq (Complex.continuous_conj.comp hθ.2) hθ.2) (fun x => ?_)
  have e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show starRingEnd ℂ (θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))) = θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))
  rw [e, hθ.1, ← hτs, hfix]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Establish `h1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e')` using `fun e' => by`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[h1 (σ e), h1 e]`. Simplify using `only [map_mul]`. Rewrite using `[hθ.1, hθ.1, hσ, hτs, infEmb_real hfix τ hτs θ hθ a]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem infEmb_sig (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hθ : IsInfEmb τ θ) (x : Ainf F ⊗[F] E) :
    θ (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ x) = starRingEnd ℂ (θ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have h1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := fun e' => by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1 (σ e), h1 e]
    simp only [map_mul]
    rw [hθ.1, hθ.1, hσ, hτs, infEmb_real hfix τ hτs θ hθ a]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Set `ψ : AF F ⊗[F] E →+* ℂ` to `θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom`. Establish `hψs : ∀ x, ψ (sigR (AF F) σ x) = starRingEnd ℂ (ψ x)`. Introduce `x`. Establish `e : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (sigR (AF F) σ x) = Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x)`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Use `show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (sigR (AF F) σ x)) = _`. Rewrite using `[e, infEmb_sig σ hσ hfix τ hτs θ hθ]`.

Both sides reduce to the same expression. Establish `hψi : ∀ j, ψ (inclR (AF F) j) = τ j`. Introduce `j`. Use `show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] j)) = τ j`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, hθ.1]`.

Use `set H := ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hH`. Establish `hU : Formalism.UG.cT (sigR (AF F) σ) H * JR (AF F) J * H = JR (AF F) J` using `h.2`. Establish `hX : infMat σ J θ h = H.map ψ` using `rfl`. Establish `h1` using `congrArg (fun Z => Z.map ψ) hU`. Simplify using `only [Matrix.map_mul] at h1`.

Establish `e1 : (Formalism.UG.cT (sigR (AF F) σ) H).map ψ = (H.map ψ).conjTranspose`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply, hψs]`. Establish `e2 : (JR (AF F) J).map ψ = J.map τ`. Use extensionality with `i j`.

Simplify using `[JR, hψi]`. Rewrite `h1` using `[e1, e2]`. Rewrite using `[hX]`. Conclude with `h1`.
-/
theorem infMat_unitary (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hθ : IsInfEmb τ θ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) :
    (infMat σ J θ h).conjTranspose * J.map τ * infMat σ J θ h = J.map τ := by
  let ψ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hψs : ∀ x, ψ (sigR (AF F) σ x) = starRingEnd ℂ (ψ x) := by
    intro x
    have e : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (sigR (AF F) σ x) =
        Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ
          (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a e => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (sigR (AF F) σ x)) = _
    rw [e, infEmb_sig σ hσ hfix τ hτs θ hθ]
    rfl
  have hψi : ∀ j, ψ (inclR (AF F) j) = τ j := by
    intro j
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] j)) = τ j
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, hθ.1]
  set H := ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hH
  have hU : Formalism.UG.cT (sigR (AF F) σ) H * JR (AF F) J * H = JR (AF F) J := h.2
  have hX : infMat σ J θ h = H.map ψ := rfl
  have h1 := congrArg (fun Z => Z.map ψ) hU
  simp only [Matrix.map_mul] at h1
  have e1 : (Formalism.UG.cT (sigR (AF F) σ) H).map ψ = (H.map ψ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hψs]
  have e2 : (JR (AF F) J).map ψ = J.map τ := by
    ext i j; simp [JR, hψi]
  rw [e1, e2] at h1
  rw [hX]; exact h1

/- English proof (translation)
Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`.

Conclude with `i.elim0`.
-/
theorem Jpq_zero (P : ℕ) : Formalism.UG.Jpq P 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

/- English proof (translation)
Rewrite `hA` using `[Jpq_zero, Matrix.mul_one]`. Set `L : Matrix (Fin P) (Fin P ⊕ Fin 0) ℂ` to `Jt⁻¹ * A.conjTranspose`. Establish `hLA : L * A = 1`. Simplify using `only [L, Matrix.mul_assoc, hA]`. Conclude with `Matrix.nonsing_inv_mul _ hJ`.

Establish `hAL : A * L = 1` using `(Matrix.mul_eq_one_comm_of_equiv (A := A) (B := L) (Equiv.sumEmpty (Fin P) (Fin 0))).mpr hLA`. Set `bm : Matrix (Fin P ⊕ Fin 0) (Fin P ⊕ Fin 0) ℂ` to `A * X * L`. Establish `hbb : bm.conjTranspose * bm = 1`. Establish `: bm.conjTranspose * bm = L.conjTranspose * (X.conjTranspose * (A.conjTranspose * A) * X) * L`. Simplify using `only [bm, Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[this, hA, hX, ← hA]`. Rewrite using `[show L.conjTranspose * (A.conjTranspose * A) * L = (A * L).conjTranspose * (A * L) by`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]`. Rewrite using `[hAL, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `hbb' : bm * bm.conjTranspose = 1` using `(Matrix.mul_eq_one_comm_of_equiv (A := bm.conjTranspose) (B := bm) (Equiv.refl _)).mp hbb`.

Set `g : GL (Fin P ⊕ Fin 0) ℂ` to `⟨bm, bm.conjTranspose, hbb', hbb⟩`. Establish `hg : g ∈ Formalism.UG.Upq P 0` using `by show Formalism.UG.cT (starRingEnd ℂ) bm * Formalism.UG.Jpq P 0 * bm = Formalism.UG.Jpq P 0`. Establish `e : Formalism.UG.cT (starRingEnd ℂ) bm = bm.conjTranspose`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`.

Rewrite using `[e, Jpq_zero, Matrix.mul_one, hbb]`. Use `⟨(⟨g, hg⟩ : Formalism.UG.Upq P 0), ?_⟩` and prove the remaining obligations. Use `show bm * A = A * X`. Simplify using `only [bm, Matrix.mul_assoc, hLA, Matrix.mul_one]`.
-/
theorem upq_of_unitary {P : ℕ} (A : Matrix (Fin P ⊕ Fin 0) (Fin P) ℂ) (Jt X : Matrix (Fin P) (Fin P) ℂ)
    (hJ : IsUnit Jt.det) (hA : A.conjTranspose * Formalism.UG.Jpq P 0 * A = Jt)
    (hX : X.conjTranspose * Jt * X = Jt) : ∃ b : Formalism.BasicNotions.UpqT P 0, Formalism.BasicNotions.UpqT.mat b * A = A * X := by
  rw [Jpq_zero, Matrix.mul_one] at hA
  let L : Matrix (Fin P) (Fin P ⊕ Fin 0) ℂ := Jt⁻¹ * A.conjTranspose
  have hLA : L * A = 1 := by
    simp only [L, Matrix.mul_assoc, hA]
    exact Matrix.nonsing_inv_mul _ hJ
  have hAL : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := A) (B := L) (Equiv.sumEmpty (Fin P) (Fin 0))).mpr hLA
  let bm : Matrix (Fin P ⊕ Fin 0) (Fin P ⊕ Fin 0) ℂ := A * X * L
  have hbb : bm.conjTranspose * bm = 1 := by
    have : bm.conjTranspose * bm = L.conjTranspose * (X.conjTranspose * (A.conjTranspose * A) * X) * L := by
      simp only [bm, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA, hX, ← hA]
    rw [show L.conjTranspose * (A.conjTranspose * A) * L = (A * L).conjTranspose * (A * L) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [hAL, Matrix.conjTranspose_one, Matrix.one_mul]
  have hbb' : bm * bm.conjTranspose = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := bm.conjTranspose) (B := bm) (Equiv.refl _)).mp hbb
  let g : GL (Fin P ⊕ Fin 0) ℂ := ⟨bm, bm.conjTranspose, hbb', hbb⟩
  have hg : g ∈ Formalism.UG.Upq P 0 := by
    show Formalism.UG.cT (starRingEnd ℂ) bm * Formalism.UG.Jpq P 0 * bm = Formalism.UG.Jpq P 0
    have e : Formalism.UG.cT (starRingEnd ℂ) bm = bm.conjTranspose := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [e, Jpq_zero, Matrix.mul_one, hbb]
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P 0), ?_⟩
  show bm * A = A * X
  simp only [bm, Matrix.mul_assoc, hLA, Matrix.mul_one]

/- English proof (translation)
Establish `hJ : IsUnit (W.gram.map τ).det`. Establish `h0` using `hW τ`. Rewrite `h0` using `[hsig]`. Take `⟨e, P', hP⟩` from `h0`. Establish `hd` using `congrArg Matrix.det hP`.

Rewrite `hd` using `[Jpq_zero, Matrix.det_one, Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self]`. Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `hd` using `[h0, mul_zero, zero_mul]`. Conclude with `zero_ne_one hd`. Take `⟨b, hb⟩` from `upq_of_unitary A _ _ hJ hA (infMat_unitary σ hσ hfix τ hτs θ hθ W.gram h)`.

Conclude with `⟨b, Set.mem_univ _, hb⟩`.
-/
theorem inf_all (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (W : Formalism.BasicNotions.HSpace E) (hW : W.SigOK) (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsig : W.sig τ = (W.rank, 0)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : IsInfEmb τ θ)
    (A : Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : A.conjTranspose * Formalism.UG.Jpq W.rank 0 * A = W.gram.map τ) (h : HA (AF F) σ W.gram) :
    ∃ b ∈ (Set.univ : Set (Formalism.BasicNotions.UpqT W.rank 0)),
      Formalism.BasicNotions.UpqT.mat b * A = A * infMat σ W.gram θ h := by
  have hJ : IsUnit (W.gram.map τ).det := by
    have h0 := hW τ
    rw [hsig] at h0
    obtain ⟨e, P', hP⟩ := h0
    have hd := congrArg Matrix.det hP
    rw [Jpq_zero, Matrix.det_one, Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self] at hd
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero, zero_mul] at hd
    exact zero_ne_one hd
  obtain ⟨b, hb⟩ := upq_of_unitary A _ _ hJ hA (infMat_unitary σ hσ hfix τ hτs θ hθ W.gram h)
  exact ⟨b, Set.mem_univ _, hb⟩

end Inf

section Rec

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `stab_finite W D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW hsig _ (fun k hk y hy => ((show k ∈ KSet D W W.rank 0 θ A from hk).1 y).mp hy) g`.
-/
theorem stab_KSub_finite (D : D7) (W : HSpace D.host.E) (hW : W.SigOK)
    (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (g : HA (AF D.host.F) D.sp.cm.sig W.gram) :
    (Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) g).Finite :=
  stab_finite W D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW hsig _
    (fun k hk y hy => ((show k ∈ KSet D W W.rank 0 θ A from hk).1 y).mp hy) g

/- English proof (translation)
Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce `hh`. Conclude with `(show h ∈ KSet D W W.rank 0 θ A from hh).1`. Introduce `hh`.

Use `(show h ∈ KSet D W W.rank 0 θ A from ⟨hh, fun ρ => ?_⟩)` and prove the remaining obligations. Conclude with `inf_all D.sp.cm.sig (fun _ => rfl) (fun x => (D.sp.cm.fixed _).mpr ⟨x, rfl⟩) W hW (embOf D ρ) (D.sp.cm.cmUnram.2.1 _) (hsig _) (θ ρ) (hθ ρ) (A ρ) (hA ρ) h`.
-/
theorem KSub_eq (D : D7) (W : HSpace D.host.E) (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq W.rank 0 * A ρ = W.gram.map (embOf D ρ)) :
    (KSub D W W.rank 0 θ A : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) =
      (SFin D.sp.cm.sig W.gram (crd W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) := by
  ext h
  constructor
  · intro hh; exact (show h ∈ KSet D W W.rank 0 θ A from hh).1
  · intro hh
    refine (show h ∈ KSet D W W.rank 0 θ A from ⟨hh, fun ρ => ?_⟩)
    exact inf_all D.sp.cm.sig (fun _ => rfl) (fun x => (D.sp.cm.fixed _).mpr ⟨x, rfl⟩) W hW (embOf D ρ)
      (D.sp.cm.cmUnram.2.1 _) (hsig _) (θ ρ) (hθ ρ) (A ρ) (hA ρ) h

/- English proof (translation)
Use `Unfold.borelHA D.sp.cm.sig W.gram` as an intermediate fact. Rewrite using `[KSub_eq D W hW hsig θ hθ A hA]`. Conclude with `(isOpen_SFin W D.sp.cm.sig).measurableSet`.
-/
theorem measurableSet_KSub (D : D7) (W : HSpace D.host.E) (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq W.rank 0 * A ρ = W.gram.map (embOf D ρ)) :
    MeasurableSet (KSub D W W.rank 0 θ A : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) := by
  have := Unfold.borelHA D.sp.cm.sig W.gram
  rw [KSub_eq D W hW hsig θ hθ A hA]
  exact (isOpen_SFin W D.sp.cm.sig).measurableSet

end Rec

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DefClassRest (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : StabFin.SFin D.sp.cm.sig W.gram (L0c D W),
        x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) ∧
      (∀ i j (γ γ' : GamA D W) (k k' : StabFin.SFin D.sp.cm.sig W.gram (L0c D W)),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k =
          (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' → i = j) ∧
      ∑ i, ((Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass W.hT W.L0

/- English proof (translation)
Introduce `W hW hsig θ hθ A hA`. Establish `hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W)` using `SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)`. Take `⟨n, g, hcov, hdisj, hsum⟩` from `hR W hW hsig`. Use `Unfold.borelHA D.sp.cm.sig W.gram` as an intermediate fact. Rewrite using `[hK]`.

Conclude with `⟨(StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet, n, g, hcov, hdisj, fun i => StabFin.stab_finite W D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW hsig _ (fun k hk y hy => (hk y).mp hy) (g i), hsum⟩`.
-/
theorem defClassDecomp_of_rest (D : D7) (hR : DefClassRest D) : DefClassDecomp D := by
  intro W hW hsig θ hθ A hA
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨n, g, hcov, hdisj, hsum⟩ := hR W hW hsig
  have := Unfold.borelHA D.sp.cm.sig W.gram
  rw [hK]
  exact ⟨(StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet, n, g, hcov, hdisj,
    fun i => StabFin.stab_finite W D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW hsig _
      (fun k hk y hy => (hk y).mp hy) (g i), hsum⟩

/- English proof (translation)
The claim follows from `mass_volume_identity_of_class_decomp D hT hG (defClassDecomp_of_rest D hR)`.
-/
theorem volume_mass_of_class_rest (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (hR : DefClassRest D) : DefiniteVolumeEqMass D :=
  mass_volume_identity_of_class_decomp D hT hG (defClassDecomp_of_rest D hR)

/- English proof (translation)
The claim follows from `Link2_of_decomp fun eps Fm x i => defClassDecomp_of_rest _ (hR eps Fm x i)`.
-/
theorem Link2_of_rest (hR : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), DefClassRest (Fm.D x i)) :
    Link2 :=
  Link2_of_decomp fun eps Fm x i => defClassDecomp_of_rest _ (hR eps Fm x i)

def ClassFin (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : StabFin.SFin D.sp.cm.sig W.gram (L0c D W),
        x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) ∧
      (∀ i j (γ γ' : GamA D W) (k k' : StabFin.SFin D.sp.cm.sig W.gram (L0c D W)),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k =
          (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' → i = j)

def ClassMass (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∀ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : StabFin.SFin D.sp.cm.sig W.gram (L0c D W),
        x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) →
      (∀ i j (γ γ' : GamA D W) (k k' : StabFin.SFin D.sp.cm.sig W.gram (L0c D W)),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k =
          (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' → i = j) →
      ∑ i, ((Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass W.hT W.L0

/- English proof (translation)
Introduce `W hW hsig`. Take `⟨n, g, hcov, hdisj⟩` from `h2 W hW hsig`. Conclude with `⟨n, g, hcov, hdisj, h4 W hW hsig n g hcov hdisj⟩`.
-/
theorem defClassRest_of (D : D7) (h2 : ClassFin D) (h4 : ClassMass D) : DefClassRest D := by
  intro W hW hsig
  obtain ⟨n, g, hcov, hdisj⟩ := h2 W hW hsig
  exact ⟨n, g, hcov, hdisj, h4 W hW hsig n g hcov hdisj⟩

/- English proof (translation)
The claim follows from `volume_mass_of_class_rest D hT hG (defClassRest_of D h2 h4)`.
-/
theorem volume_mass_of_class_items (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (h2 : ClassFin D)
    (h4 : ClassMass D) : DefiniteVolumeEqMass D :=
  volume_mass_of_class_rest D hT hG (defClassRest_of D h2 h4)

/- English proof (translation)
The claim follows from `Link2_of_rest fun eps Fm x i => defClassRest_of _ (h2 eps Fm x i) (h4 eps Fm x i)`.
-/
theorem Link2_of_items (h2 : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), ClassFin (Fm.D x i))
    (h4 : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), ClassMass (Fm.D x i)) : Link2 :=
  Link2_of_rest fun eps Fm x i => defClassRest_of _ (h2 eps Fm x i) (h4 eps Fm x i)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
