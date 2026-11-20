import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
open scoped Matrix

namespace GlobalTheory.AugSpan

/- English proof (translation)
Introduce `K _ _ Γ _ m S P hst hirrP hnt`. Use `set J := Submodule.span K (Set.range fun g => S g - 1) with hJ`. Take `⟨g₀, v₀, hv₀, hne⟩` from `hnt`. Establish `hP : P ≠ ⊥`. Introduce `h`.

Rewrite `hv₀` using `[h, Submodule.mem_bot]`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hv₀, Matrix.mulVec_zero]`. Establish `hinv : ∀ g, ∀ v ∈ P, (Matrix.toLin' (S g)) v ∈ P` using `fun g v hv => by rw [Matrix.toLin'_apply]; exact hst g v hv`. Set `r : Representation K Γ P` to `{ toFun := fun g => (Matrix.toLin' (S g)).restrict (hinv g) map_one' := by`.

Use extensionality with `v i`. Simplify using `[LinearMap.restrict_apply]`. Use the proof step `map_mul' := fun g g' => by`. Use extensionality with `v i`. Simplify using `[LinearMap.restrict_apply, Matrix.mulVec_mulVec] }`.

Establish `hr : ∀ g (v : P), ((r g v : P) : Fin m → K) = S g *ᵥ (v : Fin m → K)` using `fun g v => by simp [r, LinearMap.restrict_apply]`. Establish `hirr : r.IsIrreducible`. Establish `hnt : Nontrivial (Subrepresentation r)`. Use `⟨⊥, ⊤, fun hbt => hP ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Subrepresentation.toSubmodule hbt`.

Express the relevant statement in the definitionally equal form `(⊥ : Submodule K P) = ⊤ at h2`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Establish `: (⟨v, hv⟩ : P) ∈ (⊥ : Submodule K P)` using `by rw [h2]; trivial`. Rewrite `this` using `[Submodule.mem_bot]`.

Simplify using `using congrArg Subtype.val this`. Use `⟨fun W => ?_⟩` and prove the remaining obligations. Establish `hle : W.toSubmodule.map P.subtype ≤ P`. Introduce and unpack `_ ⟨v, _, rfl⟩`. Conclude with `v.2`.

Establish `hinvW : ∀ g, ∀ v ∈ W.toSubmodule.map P.subtype, S g *ᵥ v ∈ W.toSubmodule.map P.subtype`. Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Use `⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩` and prove the remaining obligations. Simplify using `[hr]`. Break down `hirrP _ hle hinvW with h1 | h1` into its components or cases.

Use `left`. Use `Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)` and prove the remaining obligations. Establish `: (v : Fin m → K) ∈ W.toSubmodule.map P.subtype` using `⟨v, hv, rfl⟩`. Rewrite `this` using `[h1, Submodule.mem_bot]`. Use `show v ∈ (⊥ : Submodule K P)`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Use `right`. Use `Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)` and prove the remaining obligations. Establish `: (v : Fin m → K) ∈ W.toSubmodule.map P.subtype` using `by rw [h1]; exact v.2`.

Take `⟨w, hw, hwv⟩` from `this`. Rewrite `hw` using `[show w = v from Subtype.ext hwv]`. Then use the resulting hypothesis. Establish `hs` using `GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr`. Establish `hJl : ∀ g, ∀ T ∈ J, S g * T ∈ J`. Introduce `g T hT`.

Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`. Establish `: S g * (S h - 1) = (S (g * h) - 1) - (S g - 1)`. Rewrite using `[map_mul, mul_sub, mul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [Matrix.mul_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `hJr : ∀ g, ∀ T ∈ J, T * S g ∈ J`. Introduce `g T hT`.

Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`. Establish `: (S h - 1) * S g = (S (h * g) - 1) - (S g - 1)`. Rewrite using `[map_mul, sub_mul, one_mul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [Matrix.smul_mul]`. Conclude with `Submodule.smul_mem _ c hx`. Set `J' : Submodule K (Module.End K P)` to `{ carrier := {f | ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w} add_mem' := by`. Introduce and unpack `f f' ⟨T, hT, hTf⟩ ⟨T', hT', hTf'⟩`.

Conclude with `⟨T + T', J.add_mem hT hT', fun w => by`. Rewrite using `[Matrix.add_mulVec, hTf, hTf']`. Use the proof step `simp⟩`. Use the proof step `zero_mem' := ⟨0, J.zero_mem, fun w => by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c f ⟨T, hT, hTf⟩`. Conclude with `⟨c • T, J.smul_mem c hT, fun w => by`. Rewrite using `[Matrix.smul_mulVec, hTf]`. Use the proof step `simp⟩ }`. Establish `hmem : ∀ f, f ∈ J' ↔ ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w` using `fun f => Iff.rfl`.

Establish `hl : ∀ a : Module.End K P, ∀ f ∈ J', a * f ∈ J'`. Introduce `a f hf`. Establish `ha : a ∈ Submodule.span K (Set.range r)` using `by rw [hs]; trivial`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Take `⟨T, hT, hTf⟩` from `(hmem f).1 hf`. Use `(hmem _).2 ⟨S g * T, hJl g T hT, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, hTf, Module.End.mul_apply, hr]`. Consider the case `zero => rw [zero_mul]`.

Conclude with `J'.zero_mem`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `J'.add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `J'.smul_mem c hx`.

Establish `hrt : ∀ a : Module.End K P, ∀ f ∈ J', f * a ∈ J'`. Introduce `a f hf`. Establish `ha : a ∈ Submodule.span K (Set.range r)` using `by rw [hs]; trivial`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Take `⟨T, hT, hTf⟩` from `(hmem f).1 hf`. Use `(hmem _).2 ⟨T * S g, hJr g T hT, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← hr, hTf, Module.End.mul_apply]`. Consider the case `zero => rw [mul_zero]`.

Conclude with `J'.zero_mem`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `J'.add_mem hx hy`. Consider the case `smul c x _ hx => rw [mul_smul_comm]`. Conclude with `J'.smul_mem c hx`.

Use `set f₀ : Module.End K P := r g₀ - 1 with hf₀def`. Establish `hf₀ : f₀ ∈ J'` using `(hmem _).2 ⟨S g₀ - 1, Submodule.subset_span ⟨g₀, rfl⟩, fun w => by`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr]`. Use the proof step `rfl⟩`. Use `set w₀ : P := ⟨v₀, hv₀⟩ with hw₀`.

Establish `hfw : f₀ w₀ ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Establish `h'` using `congrArg Subtype.val h`. Rewrite `h'` using `[hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr, Submodule.coe_zero, sub_eq_zero]`.

Conclude with `h'`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K P, ψ (f₀ w₀) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hfw ((Module.forall_dual_apply_eq_zero_iff K _).1 hc)`.

Set `b` to `Module.finBasis K P`. Establish `hid : (1 : Module.End K P) ∈ J'`. Establish `heq : (1 : Module.End K P) = ∑ i, ((ψ (f₀ w₀))⁻¹ • ψ.smulRight (b i)) * f₀ * ((b.coord i).smulRight w₀)` using `by ext1 w`. Rewrite using `[LinearMap.sum_apply, Module.End.one_apply]`. Use `conv_lhs => rw [← b.sum_repr w]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul, Module.Basis.coord_apply]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`.

Conclude with `J'.sum_mem fun i _ => hrt _ _ (hl _ _ hf₀)`. Take `⟨T, hT, hTid⟩` from `(hmem _).1 hid`. Conclude with `⟨T, hT, fun v hv => hTid ⟨v, hv⟩⟩`.
-/
theorem exists_mem_span_sub_one_eq_id_on :
    ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ}
      (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)),
      (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) →
      (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) →
      (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) →
      ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  intro K _ _ Γ _ m S P hst hirrP hnt
  classical
  set J := Submodule.span K (Set.range fun g => S g - 1) with hJ
  obtain ⟨g₀, v₀, hv₀, hne⟩ := hnt
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hv₀
    apply hne
    rw [hv₀, Matrix.mulVec_zero]
  have hinv : ∀ g, ∀ v ∈ P, (Matrix.toLin' (S g)) v ∈ P :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact hst g v hv
  let r : Representation K Γ P :=
    { toFun := fun g => (Matrix.toLin' (S g)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : P), ((r g v : P) : Fin m → K) = S g *ᵥ (v : Fin m → K) :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => hP ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule K P) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : P) ∈ (⊥ : Submodule K P) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map P.subtype ≤ P := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : ∀ g, ∀ v ∈ W.toSubmodule.map P.subtype, S g *ᵥ v ∈ W.toSubmodule.map P.subtype := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases hirrP _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule K P)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  have hJl : ∀ g, ∀ T ∈ J, S g * T ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : S g * (S h - 1) = (S (g * h) - 1) - (S g - 1) := by
        rw [map_mul, mul_sub, mul_one]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
  have hJr : ∀ g, ∀ T ∈ J, T * S g ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : (S h - 1) * S g = (S (h * g) - 1) - (S g - 1) := by
        rw [map_mul, sub_mul, one_mul]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  let J' : Submodule K (Module.End K P) :=
    { carrier := {f | ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w}
      add_mem' := by
        rintro f f' ⟨T, hT, hTf⟩ ⟨T', hT', hTf'⟩
        exact ⟨T + T', J.add_mem hT hT', fun w => by
          rw [Matrix.add_mulVec, hTf, hTf']; simp⟩
      zero_mem' := ⟨0, J.zero_mem, fun w => by simp⟩
      smul_mem' := by
        rintro c f ⟨T, hT, hTf⟩
        exact ⟨c • T, J.smul_mem c hT, fun w => by
          rw [Matrix.smul_mulVec, hTf]; simp⟩ }
  have hmem : ∀ f, f ∈ J' ↔ ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w := fun f => Iff.rfl
  have hl : ∀ a : Module.End K P, ∀ f ∈ J', a * f ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨S g * T, hJl g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, hTf, Module.End.mul_apply, hr]
    | zero => rw [zero_mul]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact J'.smul_mem c hx
  have hrt : ∀ a : Module.End K P, ∀ f ∈ J', f * a ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨T * S g, hJr g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, ← hr, hTf, Module.End.mul_apply]
    | zero => rw [mul_zero]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact J'.smul_mem c hx
  set f₀ : Module.End K P := r g₀ - 1 with hf₀def
  have hf₀ : f₀ ∈ J' := (hmem _).2 ⟨S g₀ - 1, Submodule.subset_span ⟨g₀, rfl⟩, fun w => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr]; rfl⟩
  set w₀ : P := ⟨v₀, hv₀⟩ with hw₀
  have hfw : f₀ w₀ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr, Submodule.coe_zero, sub_eq_zero] at h'
    exact h'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K P, ψ (f₀ w₀) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hfw ((Module.forall_dual_apply_eq_zero_iff K _).1 hc)
  let b := Module.finBasis K P
  have hid : (1 : Module.End K P) ∈ J' := by
    have heq : (1 : Module.End K P) = ∑ i, ((ψ (f₀ w₀))⁻¹ • ψ.smulRight (b i)) * f₀ *
        ((b.coord i).smulRight w₀) := by
      ext1 w
      rw [LinearMap.sum_apply, Module.End.one_apply]
      conv_lhs => rw [← b.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        smul_eq_mul, smul_smul, Module.Basis.coord_apply]
      congr 1
      field_simp
    rw [heq]
    exact J'.sum_mem fun i _ => hrt _ _ (hl _ _ hf₀)
  obtain ⟨T, hT, hTid⟩ := (hmem _).1 hid
  exact ⟨T, hT, fun v hv => hTid ⟨v, hv⟩⟩

end GlobalTheory.AugSpan
