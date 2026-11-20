import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Set `S : Set (AwayP p)` to `{v | K v ⊆ v.1.adicCompletionIntegers ℚ}`. Establish `hS : Filter.cofinite ≤ Filter.principal S` using `Filter.le_principal_iff.2 h`. Set `P` to `RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ) (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (Filter.principal S)`. Establish `h1 : IsCompact {x : P | ∀ v, x v ∈ K v}`. Rewrite using `[RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]`.

Use `isCompact_univ_pi hK` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ v -`. Conclude with `hy v`.

Introduce `hx`. Conclude with `⟨⟨x, fun v hv => hv (hx v trivial)⟩, fun v => hx v trivial, rfl⟩`. Establish `h2` using `h1.image (RestrictedProduct.continuous_inclusion hS)`. Establish `e : {a : AfP p | ∀ v, AfP.eval v a ∈ K v} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ v, x v ∈ K v}`. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨⟨(LevelExists.rp a).1, fun v hv => hv (ha v)⟩, ha, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`.

Rewrite using `[e]`. Conclude with `h2`.
-/
theorem isCompact_box (K : ∀ v : AwayP p, Set (Qv v)) (hK : ∀ v, IsCompact (K v))
    (h : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ) :
    IsCompact {a : AfP p | ∀ v, AfP.eval v a ∈ K v} := by
  let S : Set (AwayP p) := {v | K v ⊆ v.1.adicCompletionIntegers ℚ}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 h
  let P := RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (Filter.principal S)
  have h1 : IsCompact {x : P | ∀ v, x v ∈ K v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hK
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ v -
      exact hy v
    · intro hx
      exact ⟨⟨x, fun v hv => hv (hx v trivial)⟩, fun v => hx v trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : AfP p | ∀ v, AfP.eval v a ∈ K v} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ v, x v ∈ K v} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨(LevelExists.rp a).1, fun v hv => hv (ha v)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

def basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

def tv (v : AwayP p) : AfP p ⊗[ℚ] G.C →+* Qv v ⊗[ℚ] G.C :=
  (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c`. Simplify using `[tv, basV, basA, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem repr_tv (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (tv G v y) i = AfP.eval v ((basA G).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp [tv, basV, basA, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval v`.
-/
theorem continuous_eval (v : AwayP p) : Continuous (AfP.eval (p := p) v) :=
  RestrictedProduct.continuous_eval v

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

/- English proof (translation)
Apply `(basV G v).equivFun.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `i`. Simplify using `only [Module.Basis.equivFun_apply]`. Conclude with `repr_tv G v y i`.
-/
theorem tv_eq (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) :
    tv G v y = (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) := by
  apply (basV G v).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp only [Module.Basis.equivFun_apply]
  exact repr_tv G v y i

/- English proof (translation)
Use `letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousAdd (Qv v) _`.

Establish `h1 : Continuous (basA G).equivFun` using `IsModuleTopology.continuous_of_linearMap (basA G).equivFun.toLinearMap`. Establish `h2 : Continuous (basV G v).equivFun.symm` using `IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.symm.toLinearMap`. Establish `: tv G v = fun y => (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i))`. Use function extensionality and compare the values at `(tv_eq G v)`. Rewrite using `[this]`.

Conclude with `h2.comp (continuous_pi fun i => (continuous_eval v).comp ((continuous_apply i).comp h1))`.
-/
theorem continuous_tv (v : AwayP p) :
    @Continuous _ _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) (tv G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : ContinuousAdd (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousAdd (Qv v) _
  have h1 : Continuous (basA G).equivFun := IsModuleTopology.continuous_of_linearMap (basA G).equivFun.toLinearMap
  have h2 : Continuous (basV G v).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.symm.toLinearMap
  have : tv G v = fun y => (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) :=
    funext (tv_eq G v)
  rw [this]
  exact h2.comp (continuous_pi fun i => (continuous_eval v).comp ((continuous_apply i).comp h1))

/- English proof (translation)
Use `letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)`. Use `letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)`. Establish `ht` using `continuous_tv G v`. Establish `hval : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)` using `Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)`. Establish `hinv : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)` using `Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)`.

Establish `hval2 : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)` using `Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)`. Establish `hinv2 : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)` using `Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Apply `Continuous.prodMk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`.

Conclude with `⟨ht.comp hval, ht.comp hinv⟩`. Rewrite using `[Units.continuous_iff]`. Conclude with `⟨(continuous_eval v).comp hval2, (continuous_eval v).comp hinv2⟩`.
-/
theorem continuous_piV (v : AwayP p) : Continuous (piV G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have ht := continuous_tv G v
  have hval : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hinv : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hval2 : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hinv2 : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · rw [Units.continuous_iff]
    exact ⟨ht.comp hval, ht.comp hinv⟩
  · rw [Units.continuous_iff]
    exact ⟨(continuous_eval v).comp hval2, (continuous_eval v).comp hinv2⟩

end GlobalTheory.OrbFinAf.CompactOrbitVectors

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

open CompactOrbitVectors in

/- English proof (translation)
Introduce `p _ G D hDc hDi`. Use `haveI : T2Space (AfP p) := inferInstanceAs (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))`. Use `letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _`.

Use `haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C`. Set `c1 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v` to `fun v i h => (basV G v).repr (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i`. Set `c2 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v` to `fun v i h => (basV G v).repr ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i`. Set `c3 : ∀ v : AwayP p, Gv G v → Qv v` to `fun v h => (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)`. Set `c4 : ∀ v : AwayP p, Gv G v → Qv v` to `fun v h => ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)`.

Establish `hc : ∀ v, (∀ i, Continuous (c1 v i)) ∧ (∀ i, Continuous (c2 v i)) ∧ Continuous (c3 v) ∧ Continuous (c4 v)`. Introduce `v`. Use `letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩`. Establish `hr : Continuous (basV G v).equivFun` using `IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap`.

Use `⟨fun i => ?_, fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_apply i).comp (hr.comp (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))`. Conclude with `(continuous_apply i).comp (hr.comp (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)))`. Conclude with `Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)`. Conclude with `Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)`.

Set `K : ∀ v : AwayP p, Set (Qv v)` to `fun v => ((⋃ i, c1 v i '' D v) ∪ (⋃ i, c2 v i '' D v)) ∪ (c3 v '' D v ∪ c4 v '' D v)`. Establish `hKc : ∀ v, IsCompact (K v)` using `fun v => ((isCompact_iUnion fun i => (hDc v).image ((hc v).1 i)).union (isCompact_iUnion fun i => (hDc v).image ((hc v).2.1 i))).union (((hDc v).image (hc v).2.2.1).union ((hDc v).image (hc v).2.2.2))`. Establish `hKi : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ` using `by filter_upwards [hDi] with v hv`. Introduce and unpack `y ((hy | hy) | (hy | hy))`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hy`.

Take `⟨h, hh, rfl⟩` from `hi`. Conclude with `(hv hh).1 i`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hy`. Take `⟨h, hh, rfl⟩` from `hi`. Conclude with `(hv hh).2.1 i`.

Take `⟨h, hh, rfl⟩` from `hy`. Conclude with `(hv hh).2.2.1`. Take `⟨h, hh, rfl⟩` from `hy`. Conclude with `(hv hh).2.2.2`. Set `E : Set (AfP p)` to `{a | ∀ v, AfP.eval v a ∈ K v}`.

Establish `hE : IsCompact E` using `isCompact_box K hKc hKi`. Set `Bm : Set (AfP p ⊗[ℚ] G.C)` to `(basA G).equivFun.symm '' Set.univ.pi fun _ => E`. Establish `hBm : IsCompact Bm` using `(isCompact_univ_pi fun _ => hE).image (IsModuleTopology.continuous_of_linearMap (basA G).equivFun.symm.toLinearMap)`. Set `B : Set (((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ))` to `(Bm ×ˢ (MulOpposite.op '' Bm)) ×ˢ (E ×ˢ (MulOpposite.op '' E))`. Establish `hB : IsCompact B` using `(hBm.prod (hBm.image MulOpposite.continuous_op)).prod (hE.prod (hE.image MulOpposite.continuous_op))`.

Establish `hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop)`. Set `σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C)` to `{ toFun := fun y ↦ (starT G.star (AfP p) y).unop map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add] map_smul' := by`. Introduce `r x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a y`. Simplify using `only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]`. Consider the case `add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }`. Conclude with `IsModuleTopology.continuous_of_linearMap σl`. Establish `hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))`.

Establish `hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ))`. Apply `isClosed_eq` to reduce the goal to its premises. Conclude with `(Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst))`. Conclude with `hj.comp (Units.continuous_val.comp continuous_snd)`. Set `emb : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)` to `fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)`.

Establish `hemb : Topology.IsClosedEmbedding emb` using `(Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp hGcl.isClosedEmbedding_subtypeVal`. Establish `hS : IsClosed {g : G.GAf | ∀ v, piV G v g ∈ D v}`. Establish `: {g : G.GAf | ∀ v, piV G v g ∈ D v} = ⋂ v, piV G v ⁻¹' D v`. Use extensionality with `g`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Use `isClosed_iInter fun v => ?_` and prove the remaining obligations. Use `letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _`.

Use `haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C`. Use `haveI : T2Space (Gv G v) := inferInstance`. Conclude with `(hDc v).isClosed.preimage (continuous_piV G v)`. Establish `hsub : emb '' {g : G.GAf | ∀ v, piV G v g ∈ D v} ⊆ B`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `hco : ∀ y : AfP p ⊗[ℚ] G.C, (∀ v i, (basV G v).repr (tv G v y) i ∈ K v) → y ∈ Bm`. Introduce `y hy`. Use `⟨(basA G).equivFun y, fun i _ v => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.equivFun_apply, ← repr_tv]`. Conclude with `hy v i`.

Use `⟨⟨hco _ fun v i => ?_, ⟨_, hco _ fun v i => ?_, rfl⟩⟩, ⟨fun v => ?_, ⟨_, fun v => ?_, rfl⟩⟩⟩` and prove the remaining obligations. Conclude with `Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))`. Conclude with `Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))`. Conclude with `Or.inr (Or.inl ⟨piV G v x, hx v, rfl⟩)`. Conclude with `Or.inr (Or.inr ⟨piV G v x, hx v, rfl⟩)`.

Conclude with `hemb.isInducing.isCompact_iff.2 (hB.of_isClosed_subset (hemb.isClosedMap _ hS) hsub)`.
-/
theorem isCompact_prod_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)),
    (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) →
    IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  intro p _ G D hDc hDi
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C

  let c1 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c2 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c3 : ∀ v : AwayP p, Gv G v → Qv v := fun v h => (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)
  let c4 : ∀ v : AwayP p, Gv G v → Qv v := fun v h =>
    ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)
  have hc : ∀ v, (∀ i, Continuous (c1 v i)) ∧ (∀ i, Continuous (c2 v i)) ∧ Continuous (c3 v) ∧
      Continuous (c4 v) := by
    intro v
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    have hr : Continuous (basV G v).equivFun :=
      IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)))
    · exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    · exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  let K : ∀ v : AwayP p, Set (Qv v) := fun v =>
    ((⋃ i, c1 v i '' D v) ∪ (⋃ i, c2 v i '' D v)) ∪ (c3 v '' D v ∪ c4 v '' D v)
  have hKc : ∀ v, IsCompact (K v) := fun v =>
    ((isCompact_iUnion fun i => (hDc v).image ((hc v).1 i)).union
      (isCompact_iUnion fun i => (hDc v).image ((hc v).2.1 i))).union
      (((hDc v).image (hc v).2.2.1).union ((hDc v).image (hc v).2.2.2))
  have hKi : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ := by
    filter_upwards [hDi] with v hv
    rintro y ((hy | hy) | (hy | hy))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).1 i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).2.1 i
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.1
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.2
  let E : Set (AfP p) := {a | ∀ v, AfP.eval v a ∈ K v}
  have hE : IsCompact E := isCompact_box K hKc hKi
  let Bm : Set (AfP p ⊗[ℚ] G.C) := (basA G).equivFun.symm '' Set.univ.pi fun _ => E
  have hBm : IsCompact Bm := (isCompact_univ_pi fun _ => hE).image
    (IsModuleTopology.continuous_of_linearMap (basA G).equivFun.symm.toLinearMap)
  let B : Set (((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)) :=
    (Bm ×ˢ (MulOpposite.op '' Bm)) ×ˢ (E ×ˢ (MulOpposite.op '' E))
  have hB : IsCompact B := (hBm.prod (hBm.image MulOpposite.continuous_op)).prod
    (hE.prod (hE.image MulOpposite.continuous_op))

  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let emb : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hemb : Topology.IsClosedEmbedding emb :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal

  have hS : IsClosed {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
    have : {g : G.GAf | ∀ v, piV G v g ∈ D v} = ⋂ v, piV G v ⁻¹' D v := by
      ext g; simp
    rw [this]
    refine isClosed_iInter fun v => ?_
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
    haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
    haveI : T2Space (Gv G v) := inferInstance
    exact (hDc v).isClosed.preimage (continuous_piV G v)

  have hsub : emb '' {g : G.GAf | ∀ v, piV G v g ∈ D v} ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hco : ∀ y : AfP p ⊗[ℚ] G.C,
        (∀ v i, (basV G v).repr (tv G v y) i ∈ K v) → y ∈ Bm := by
      intro y hy
      refine ⟨(basA G).equivFun y, fun i _ v => ?_, by simp⟩
      rw [Module.Basis.equivFun_apply, ← repr_tv]
      exact hy v i
    refine ⟨⟨hco _ fun v i => ?_, ⟨_, hco _ fun v i => ?_, rfl⟩⟩, ⟨fun v => ?_, ⟨_, fun v => ?_, rfl⟩⟩⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inr (Or.inl ⟨piV G v x, hx v, rfl⟩)
    · exact Or.inr (Or.inr ⟨piV G v x, hx v, rfl⟩)
  exact hemb.isInducing.isCompact_iff.2 (hB.of_isClosed_subset (hemb.isClosedMap _ hS) hsub)

end GlobalTheory.OrbFinAf
