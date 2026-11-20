import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Establish `hmul : ∀ (g : Γ) (w : Fin a → k), ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec (f ∘ w) = f ∘ ((ρ g : Matrix (Fin a) (Fin a) k).mulVec w)`. Introduce `g w`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec f _ w i).symm`. Set `T : Γ → (Fin a → L) →ₗ[L] (Fin a → L)` to `fun g => Matrix.toLin' ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)`.

Set `A` to `Submodule.span L (Set.range T)`. Set `P : Submodule k (Module.End k W)` to `{ carrier := {E | ∃ M ∈ A, ∀ w : W, M (f ∘ (w : Fin a → k)) = f ∘ ((E w : W) : Fin a → k)} add_mem' := by`. Introduce and unpack `E₁ E₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩`. Use `⟨M₁ + M₂, A.add_mem hM₁ hM₂, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, h₁, h₂]`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Use the proof step `zero_mem' := ⟨0, A.zero_mem, fun w => by funext i; simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c E ⟨M, hM, h⟩`.

Use `⟨f c • M, A.smul_mem _ hM, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, h]`. Use function extensionality and compare the values at `i`. Simplify using `}`. Establish `hP : ∀ E, E ∈ P`.

Establish `hle : Submodule.span k (Set.range fun g => (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) ≤ P`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Use `⟨T g, Submodule.subset_span ⟨g, rfl⟩, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.restrict_coe_apply]`.

Conclude with `hmul g w`. Introduce `E`. Apply `hle` to reduce the goal to its premises. Rewrite using `[hsp]`. Conclude with `Submodule.mem_top`.

Establish `hA : ∀ W' : Submodule L (Fin a → L), _root_.Formalism.MainNotions.N.IsInv (_root_.Formalism.MainNotions.N.mapRep f ρ) W' → ∀ M ∈ A, ∀ v ∈ W', M v ∈ W'`. Introduce `W' hW' M hM`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`.

Introduce `v hv`. Conclude with `hW' g v hv`. Consider the case `zero => intro v _`. Simplify using `using W'.zero_mem`. Consider the case `add x y _ _ hx hy => intro v hv`.

Conclude with `W'.add_mem (hx v hv) (hy v hv)`. Consider the case `smul c x _ hx => intro v hv`. Conclude with `W'.smul_mem c (hx v hv)`. Unfold `_root_.Formalism.MainNotions.N.IsIrrSub`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Introduce `h`. Apply `hw0` to reduce the goal to its premises. Establish `hfw : f ∘ w ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))` using `Submodule.subset_span ⟨w, hw, rfl⟩`. Rewrite `hfw` using `[h, Submodule.mem_bot]`.

Use function extensionality and compare the values at `i`. Simplify using `using congrFun hfw i`. Introduce `g v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨w, hw, rfl⟩` from `hx`. Rewrite using `[hmul]`. Conclude with `Submodule.subset_span ⟨_, hW g w hw, rfl⟩`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Introduce `W' hle hst`.

Distinguish the cases in `h0 : W' = ⊥`. Conclude with `Or.inl h0`. Use `right`. Apply `le_antisymm hle` to reduce the goal to its premises. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx0 (funext h)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨w₀, hw₀, rfl⟩`. Use `show f ∘ w₀ ∈ W'`. Set `φ : W →ₗ[k] k` to `(LinearMap.proj i : (Fin a → k) →ₗ[k] k).comp W.subtype`. Set `E : Module.End k W` to `φ.smulRight ⟨w₀, hw₀⟩`. Take `⟨M, hMA, hM⟩` from `hP E`.

Establish `key : ∀ y ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))), M y = y i • (f ∘ w₀)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨w, hw, rfl⟩` from `hy`.

Rewrite using `[hM ⟨w, hw⟩]`. Use function extensionality and compare the values at `j`. Simplify using `[E, φ]`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add, hy, hz, Pi.add_apply, add_smul]`.

Consider the case `smul c y _ hy => rw [map_smul, hy, Pi.smul_apply, smul_eq_mul, mul_smul]`. Establish `hmem : M x ∈ W'` using `hA W' hst M hMA x hx`. Rewrite `hmem` using `[key x (hle hx)]`. Establish `hsm` using `W'.smul_mem (x i)⁻¹ hmem`. Rewrite `hsm` using `[smul_smul, inv_mul_cancel₀ hi, one_smul]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top {k Γ : Type} [Field k] [Group Γ] {L : Type}
    [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : _root_.Formalism.MainNotions.N.Stable (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ)) W) (hne : W ≠ ⊥)
    (hsp : Submodule.span k (Set.range fun g =>
      (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤) :
    _root_.Formalism.MainNotions.N.IsIrrSub (_root_.Formalism.MainNotions.N.mapRep f ρ)
      (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  classical
  have hmul : ∀ (g : Γ) (w : Fin a → k),
      ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec (f ∘ w) =
        f ∘ ((ρ g : Matrix (Fin a) (Fin a) k).mulVec w) := by
    intro g w
    funext i
    exact (RingHom.map_mulVec f _ w i).symm
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.toLin' ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  let A := Submodule.span L (Set.range T)
  let P : Submodule k (Module.End k W) :=
    { carrier := {E | ∃ M ∈ A, ∀ w : W, M (f ∘ (w : Fin a → k)) = f ∘ ((E w : W) : Fin a → k)}
      add_mem' := by
        rintro E₁ E₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
        refine ⟨M₁ + M₂, A.add_mem hM₁ hM₂, fun w => ?_⟩
        rw [LinearMap.add_apply, h₁, h₂]
        funext i
        simp
      zero_mem' := ⟨0, A.zero_mem, fun w => by funext i; simp⟩
      smul_mem' := by
        rintro c E ⟨M, hM, h⟩
        refine ⟨f c • M, A.smul_mem _ hM, fun w => ?_⟩
        rw [LinearMap.smul_apply, h]
        funext i
        simp }
  have hP : ∀ E, E ∈ P := by
    have hle : Submodule.span k (Set.range fun g =>
        (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      refine ⟨T g, Submodule.subset_span ⟨g, rfl⟩, fun w => ?_⟩
      rw [LinearMap.restrict_coe_apply]
      exact hmul g w
    intro E
    apply hle
    rw [hsp]
    exact Submodule.mem_top
  have hA : ∀ W' : Submodule L (Fin a → L), _root_.Formalism.MainNotions.N.IsInv (_root_.Formalism.MainNotions.N.mapRep f ρ) W' →
      ∀ M ∈ A, ∀ v ∈ W', M v ∈ W' := by
    intro W' hW' M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hW' g v hv
    | zero => intro v _; simpa using W'.zero_mem
    | add x y _ _ hx hy => intro v hv; exact W'.add_mem (hx v hv) (hy v hv)
    | smul c x _ hx => intro v hv; exact W'.smul_mem c (hx v hv)
  unfold _root_.Formalism.MainNotions.N.IsIrrSub
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    apply hw0
    have hfw : f ∘ w ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at hfw
    funext i
    simpa using congrFun hfw i
  · intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, hW g w hw, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro W' hle hst
    by_cases h0 : W' = ⊥
    · exact Or.inl h0
    right
    apply le_antisymm hle
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    rw [Submodule.span_le]
    rintro _ ⟨w₀, hw₀, rfl⟩
    show f ∘ w₀ ∈ W'
    let φ : W →ₗ[k] k := (LinearMap.proj i : (Fin a → k) →ₗ[k] k).comp W.subtype
    let E : Module.End k W := φ.smulRight ⟨w₀, hw₀⟩
    obtain ⟨M, hMA, hM⟩ := hP E
    have key : ∀ y ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))),
        M y = y i • (f ∘ w₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hM ⟨w, hw⟩]
        funext j
        simp [E, φ]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, Pi.add_apply, add_smul]
      | smul c y _ hy => rw [map_smul, hy, Pi.smul_apply, smul_eq_mul, mul_smul]
    have hmem : M x ∈ W' := hA W' hst M hMA x hx
    rw [key x (hle hx)] at hmem
    have hsm := W'.smul_mem (x i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at hsm

end GlobalTheory
