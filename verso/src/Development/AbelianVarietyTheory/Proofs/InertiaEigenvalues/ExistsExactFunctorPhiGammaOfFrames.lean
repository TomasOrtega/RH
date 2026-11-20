import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

noncomputable section

namespace GlobalTheory.RedFun

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

section

variable {k : Type} [Field k] {Rk : Type} [CommRing Rk] [Algebra k Rk] {κ : k⸨X⸩ →+* Rk}

/- English proof (translation)
The claim follows from `funext fun j => const_smul_eq k c (x j)`.
-/
theorem vc_const_smul {m : ℕ} (c : k) (x : Vc k m) : c • x = algebraMap k k⸨X⸩ c • x :=
  funext fun j => const_smul_eq k c (x j)

/- English proof (translation)
Use `choose u hu using hst`. Use `⟨AddMonoidHom.mk' u fun x y => h'.1 ?_, hu, fun c x => h'.1 ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hu, hu, hu, map_add, map_add]`. Express the relevant statement in the definitionally equal form `β' (u _) = β' (s c • u x)`. Rewrite using `[h'.2.1, hu, hu, h.2.1, hT]`.
-/
theorem frame_transport {ε ε' : Rk} {m m' : ℕ} {β : Vc k m →+ Rk ⊗[k] (Fin m → k)}
    {β' : Vc k m' →+ Rk ⊗[k] (Fin m' → k)} (h : IsFrame κ ε β) (h' : IsFrame κ ε' β')
    (T : Rk ⊗[k] (Fin m → k) →+ Rk ⊗[k] (Fin m' → k)) (s : k⸨X⸩ → k⸨X⸩)
    (hT : ∀ c y, T (κ c • y) = κ (s c) • T y) (hst : ∀ x, ∃ y, β' y = T (β x)) :
    ∃ u : Vc k m →+ Vc k m', (∀ x, β' (u x) = T (β x)) ∧ ∀ c x, u (c • x) = s c • u x := by
  choose u hu using hst
  refine ⟨AddMonoidHom.mk' u fun x y => h'.1 ?_, hu, fun c x => h'.1 ?_⟩
  · rw [map_add, hu, hu, hu, map_add, map_add]
  · change β' (u _) = β' (s c • u x)
    rw [h'.2.1, hu, hu, h.2.1, hT]

/- English proof (translation)
Take `⟨u, hu, hs⟩` from `frame_transport h h' T.toAddMonoidHom s hT hst`. Use `⟨{ toFun := u, map_add' := map_add u, map_smul' := fun c x => ?_ }, hu, hs⟩` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, vc_const_smul, vc_const_smul, hs, AlgHom.commutes]`.
-/
theorem frame_transport_semi {ε ε' : Rk} {m m' : ℕ} {β : Vc k m →+ Rk ⊗[k] (Fin m → k)}
    {β' : Vc k m' →+ Rk ⊗[k] (Fin m' → k)} (h : IsFrame κ ε β) (h' : IsFrame κ ε' β')
    (T : Rk ⊗[k] (Fin m → k) →ₗ[k] Rk ⊗[k] (Fin m' → k)) (s : k⸨X⸩ →ₐ[k] k⸨X⸩)
    (hT : ∀ c y, T (κ c • y) = κ (s c) • T y) (hst : ∀ x, ∃ y, β' y = T (β x)) :
    ∃ u : Vc k m →ₗ[k] Vc k m', (∀ x, β' (u x) = T (β x)) ∧ Semi s u := by
  obtain ⟨u, hu, hs⟩ := frame_transport h h' T.toAddMonoidHom s hT hst
  refine ⟨{ toFun := u, map_add' := map_add u, map_smul' := fun c x => ?_ }, hu, hs⟩
  rw [RingHom.id_apply, vc_const_smul, vc_const_smul, hs, AlgHom.commutes]

/- English proof (translation)
Use `set W := Submodule.span k⸨X⸩ S with hW`. Set `b` to `Module.finBasis k⸨X⸩ W`. Establish `key : ∀ x : W, β x ∈ Submodule.span Rk (Set.range fun j => β (b j))`. Introduce `x`. Rewrite using `[← b.sum_repr x, Submodule.coe_sum, map_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, h.2.1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hle : m ≤ Module.finrank k⸨X⸩ W`. Use `card_le_of_span hε h0 (fun j => β (b j)) (Pi.basisFun k (Fin m)) (Pi.basisFun k (Fin m)).linearIndependent fun j => ?_` and prove the remaining obligations.

Use `Submodule.span_le.2 ?_ (hS _)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `key ⟨x, Submodule.subset_span hx⟩`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use `le_antisymm (Submodule.finrank_le W) ?_` and prove the remaining obligations.

Simplify using `using hle`.
-/
theorem frame_span_top {ε : Rk} (hε : IsIdempotentElem ε) (h0 : ε ≠ 0) {m : ℕ}
    {β : Vc k m →+ Rk ⊗[k] (Fin m → k)} (h : IsFrame κ ε β) (S : Set (Vc k m))
    (hS : ∀ t, ε ⊗ₜ[k] t ∈ Submodule.span Rk (β '' S)) : Submodule.span k⸨X⸩ S = ⊤ := by
  set W := Submodule.span k⸨X⸩ S with hW
  let b := Module.finBasis k⸨X⸩ W
  have key : ∀ x : W, β x ∈ Submodule.span Rk (Set.range fun j => β (b j)) := by
    intro x
    rw [← b.sum_repr x, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul, h.2.1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle : m ≤ Module.finrank k⸨X⸩ W := by
    refine card_le_of_span hε h0 (fun j => β (b j)) (Pi.basisFun k (Fin m))
      (Pi.basisFun k (Fin m)).linearIndependent fun j => ?_
    refine Submodule.span_le.2 ?_ (hS _)
    rintro _ ⟨x, hx, rfl⟩
    exact key ⟨x, Submodule.subset_span hx⟩
  apply Submodule.eq_top_of_finrank_eq
  refine le_antisymm (Submodule.finrank_le W) ?_
  simpa using hle

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨x, rfl⟩ := hy`. Conclude with `Submodule.subset_span ⟨u x, ⟨x, rfl⟩, hu x⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul w y _ hy => rw [hT]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem frame_map_span {m m' : ℕ} (β : Vc k m →+ Rk ⊗[k] (Fin m → k))
    (β' : Vc k m' →+ Rk ⊗[k] (Fin m' → k))
    (T : Rk ⊗[k] (Fin m → k) →+ Rk ⊗[k] (Fin m' → k)) (s : Rk → Rk)
    (hT : ∀ r y, T (r • y) = s r • T y) (u : Vc k m → Vc k m') (hu : ∀ x, β' (u x) = T (β x))
    {y} (hy : y ∈ Submodule.span Rk (Set.range β)) : T y ∈ Submodule.span Rk (β' '' Set.range u) := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact Submodule.subset_span ⟨u x, ⟨x, rfl⟩, hu x⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul w y _ hy => rw [hT]; exact Submodule.smul_mem _ _ hy

end

section

variable {k G : Type} [Field k] [Group G] {Rk : Type} [CommRing Rk] [Algebra k Rk] {l n : ℕ} [NeZero n]
  {R : RingPG k l} {κ : k⸨X⸩ →+* Rk} {φ : Rk →ₐ[k] Rk} {a : G → (Rk →ₐ[k] Rk)} {g₀ : G} {ε : ZMod n → Rk}
  {Obj : Ob k G → Prop} {β : ∀ A : Ob k G, ZMod n → (Vc k A.m →+ Rk ⊗[k] (Fin A.m → k))}

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t => simp [hc]`. Consider the case `add a b ha hb => simp [ha, hb]`.
-/
theorem Phi_Act (hc : ∀ x, φ (a g₀ x) = a g₀ (φ x)) (A : Ob k G) (y : Rk ⊗[k] (Fin A.m → k)) :
    Phi φ A.m (Act a A g₀ y) = Act a A g₀ (Phi φ A.m y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [hc]
  | add a b ha hb => simp [ha, hb]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t => simp`. Consider the case `add a b ha hb => simp [ha, hb]`.
-/
theorem baseChange_Phi {m m' : ℕ} (f : (Fin m → k) →ₗ[k] (Fin m' → k)) (y : Rk ⊗[k] (Fin m → k)) :
    f.baseChange Rk (Phi φ m y) = Phi φ m' (f.baseChange Rk y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp
  | add a b ha hb => simp [ha, hb]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a t => simp [hf g t]`. Consider the case `add a b ha hb => simp [ha, hb]`.
-/
theorem baseChange_Act {A B : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)} (hf : IsHom A B f) (g : G)
    (y : Rk ⊗[k] (Fin A.m → k)) : f.baseChange Rk (Act a A g y) = Act a B g (f.baseChange Rk y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [hf g t]
  | add a b ha hb => simp [ha, hb]

/- English proof (translation)
Use `choose p hp hps using fun i => frame_transport_semi (H.frame A hA (i - 1)) (H.frame A hA i) (Phi φ A.m) R.φ (fun c y => by rw [Phi_smul, H.κ_φ]) (H.st_φ A hA i)`. Use `choose g hg hgs using fun i => frame_transport_semi (H.frame A hA i) (H.frame A hA i) (Act a A g₀) R.γ (fun c y => by rw [Act_smul, H.κ_γ]) (H.st_γ A hA i)`. Use `⟨{ φ := p, γ := g, φ_semi := hps, γ_semi := hgs, etale := fun i => ?_, γ_bij := fun i => ⟨?_, ?_⟩, comm := fun i x => (H.frame A hA i).1 ?_ }, hp, hg⟩` and prove the remaining obligations. Use `frame_span_top (H.ε_idem i) (H.ε_ne i) (H.frame A hA i) _ fun t => ?_` and prove the remaining obligations. Use `frame_map_span (β A (i - 1)) (β A i) (Phi φ A.m).toAddMonoidHom φ (Phi_smul φ A.m) (p i) (hp i) ((H.frame A hA (i - 1)).2.2.2 t)` as an intermediate fact.

Rewrite using `[← H.ε_φ i]`. Conclude with `this`. Introduce `x y e`. Use `(H.frame A hA i).1 (H.γ_inj A ?_)` and prove the remaining obligations. Rewrite using `[← hg, ← hg, e]`.

Introduce `y`. Take `⟨x, hx⟩` from `H.γ_surj A hA i y`. Conclude with `⟨x, (H.frame A hA i).1 (by rw [hg, hx])⟩`. Rewrite using `[hp, hg, hg, hp, Phi_Act H.comm]`.
-/
theorem IsFrames.exists_mod (H : IsFrames R κ φ a g₀ ε Obj β) (A : Ob k G) (hA : Obj A) :
    ∃ D : ModPG R n (Vc k A.m), (∀ i x, β A i (D.φ i x) = Phi φ A.m (β A (i - 1) x)) ∧
      ∀ i x, β A i (D.γ i x) = Act a A g₀ (β A i x) := by
  choose p hp hps using fun i => frame_transport_semi (H.frame A hA (i - 1)) (H.frame A hA i) (Phi φ A.m) R.φ
    (fun c y => by rw [Phi_smul, H.κ_φ]) (H.st_φ A hA i)
  choose g hg hgs using fun i => frame_transport_semi (H.frame A hA i) (H.frame A hA i) (Act a A g₀) R.γ
    (fun c y => by rw [Act_smul, H.κ_γ]) (H.st_γ A hA i)
  refine ⟨{ φ := p, γ := g, φ_semi := hps, γ_semi := hgs, etale := fun i => ?_, γ_bij := fun i => ⟨?_, ?_⟩,
            comm := fun i x => (H.frame A hA i).1 ?_ }, hp, hg⟩
  · refine frame_span_top (H.ε_idem i) (H.ε_ne i) (H.frame A hA i) _ fun t => ?_
    have := frame_map_span (β A (i - 1)) (β A i) (Phi φ A.m).toAddMonoidHom φ (Phi_smul φ A.m) (p i) (hp i)
      ((H.frame A hA (i - 1)).2.2.2 t)
    rw [← H.ε_φ i]
    exact this
  · intro x y e
    refine (H.frame A hA i).1 (H.γ_inj A ?_)
    rw [← hg, ← hg, e]
  · intro y
    obtain ⟨x, hx⟩ := H.γ_surj A hA i y
    exact ⟨x, (H.frame A hA i).1 (by rw [hg, hx])⟩
  · rw [hp, hg, hg, hp, Phi_Act H.comm]

/- English proof (translation)
Introduce `h`. Use `congrArg (fun y => TensorProduct.rid k Rk (LinearMap.lTensor Rk (LinearMap.proj 0 : (Fin 1 → k) →ₗ[k] k) y)) h` as an intermediate fact. Simplify using `at this`. Conclude with `H.ε_ne i this`.
-/
theorem IsFrames.unit_ne (H : IsFrames R κ φ a g₀ ε Obj β) (i : ZMod n) :
    (ε i ⊗ₜ[k] (fun _ => 1) : Rk ⊗[k] (Fin 1 → k)) ≠ 0 := by
  intro h
  have := congrArg (fun y => TensorProduct.rid k Rk
    (LinearMap.lTensor Rk (LinearMap.proj 0 : (Fin 1 → k) →ₗ[k] k) y)) h
  simp at this
  exact H.ε_ne i this

/- English proof (translation)
Rewrite using `[Act_tmul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `((1 : G →* kˣ) g : k) • t = t`. Simplify using the standard rewrite rules.
-/
theorem Act_chr_one (g : G) (r : Rk) (t : Fin 1 → k) :
    Act a (chr (1 : G →* kˣ)) g (r ⊗ₜ[k] t) = a g r ⊗ₜ[k] t := by
  rw [Act_tmul]
  congr 1
  change ((1 : G →* kˣ) g : k) • t = t
  simp

/- English proof (translation)
Use `⟨RingHom.injective R.γ.toRingHom, fun c => ?_⟩` and prove the remaining obligations. Take `⟨D, -, hg⟩` from `H.exists_mod (chr 1) H.obj_one`. Take `⟨u, hu⟩` from `H.unit 0`. Establish `hinj` using `(H.frame _ H.obj_one 0).1`. Establish `hγ : D.γ 0 u = u` using `hinj (by rw [hg, hu, Act_chr_one, H.ε_γ])`.

Establish `hu0 : u 0 ≠ 0`. Introduce `h0`. Establish `: u = 0` using `funext fun j => by rw [Subsingleton.elim j 0]; exact h0`. Conclude with `H.unit_ne 0 (by rw [← hu, this, map_zero])`. Take `⟨x, hx⟩` from `(D.γ_bij 0).2 (c • u)`.

Establish `hxu : x = (x 0 / u 0) • u` using `funext fun j => by`. Rewrite using `[Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hu0]`. Rewrite `hx` using `[hxu, D.γ_semi, hγ]`. Use `⟨x 0 / u 0, mul_right_cancel₀ hu0 ?_⟩` and prove the remaining obligations. Conclude with `congrFun hx 0`.
-/
theorem IsFrames.γ_bijective (H : IsFrames R κ φ a g₀ ε Obj β) : Function.Bijective R.γ := by
  refine ⟨RingHom.injective R.γ.toRingHom, fun c => ?_⟩
  obtain ⟨D, -, hg⟩ := H.exists_mod (chr 1) H.obj_one
  obtain ⟨u, hu⟩ := H.unit 0
  have hinj := (H.frame _ H.obj_one 0).1
  have hγ : D.γ 0 u = u := hinj (by rw [hg, hu, Act_chr_one, H.ε_γ])
  have hu0 : u 0 ≠ 0 := by
    intro h0
    have : u = 0 := funext fun j => by rw [Subsingleton.elim j 0]; exact h0
    exact H.unit_ne 0 (by rw [← hu, this, map_zero])
  obtain ⟨x, hx⟩ := (D.γ_bij 0).2 (c • u)
  have hxu : x = (x 0 / u 0) • u := funext fun j => by
    rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hu0]
  rw [hxu, D.γ_semi, hγ] at hx
  refine ⟨x 0 / u 0, mul_right_cancel₀ hu0 ?_⟩
  exact congrFun hx 0

/- English proof (translation)
Distinguish the cases in `h : Obj A ∧ Obj B ∧ IsHom A B f`. Take `⟨hA, hB, hf⟩` from `h`. Take `⟨u, hu, hs⟩` from `frame_transport (H.frame A hA i) (H.frame B hB i) (f.baseChange Rk).toAddMonoidHom id (fun c y => map_smul (f.baseChange Rk) _ _) (H.st_map A B f hA hB hf i)`. Conclude with `⟨{ toFun := u, map_add' := map_add u, map_smul' := hs }, fun _ _ _ => hu⟩`. Conclude with `⟨0, fun hA hB hf => (h ⟨hA, hB, hf⟩).elim⟩`.
-/
theorem IsFrames.exists_map (H : IsFrames R κ φ a g₀ ε Obj β) (A B : Ob k G)
    (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (i : ZMod n) :
    ∃ u : Vc k A.m →ₗ[k⸨X⸩] Vc k B.m, Obj A → Obj B → IsHom A B f →
      ∀ x, β B i (u x) = f.baseChange Rk (β A i x) := by
  by_cases h : Obj A ∧ Obj B ∧ IsHom A B f
  · obtain ⟨hA, hB, hf⟩ := h
    obtain ⟨u, hu, hs⟩ := frame_transport (H.frame A hA i) (H.frame B hB i) (f.baseChange Rk).toAddMonoidHom id
      (fun c y => map_smul (f.baseChange Rk) _ _) (H.st_map A B f hA hB hf i)
    exact ⟨{ toFun := u, map_add' := map_add u, map_smul' := hs }, fun _ _ _ => hu⟩
  · exact ⟨0, fun hA hB hf => (h ⟨hA, hB, hf⟩).elim⟩

end

/- English proof (translation)
Establish `hD : ∀ A : Ob k G, ∃ D : ModPG R n (Vc k A.m), Obj A → (∀ i x, β A i (D.φ i x) = Phi φ A.m (β A (i - 1) x)) ∧ ∀ i x, β A i (D.γ i x) = Act a A g₀ (β A i x)`. Introduce `A`. Distinguish the cases in `hA : Obj A`. Take `⟨D, h⟩` from `H.exists_mod A hA`. Conclude with `⟨D, fun _ => h⟩`.

Conclude with `⟨Inh.powMod R H.γ_bijective n A.m, fun h => (hA h).elim⟩`. Use `choose D hD using hD`. Use `choose M hM using H.exists_map`. Use `choose u hu using H.unit`. Establish `inj : ∀ A, Obj A → ∀ i, Function.Injective (β A i)` using `fun A hA i => (H.frame A hA i).1`.

Establish `hid : ∀ A : Ob k G, IsHom A A LinearMap.id` using `fun _ _ _ => rfl`. Use `⟨{ Obj := Obj, obj_sub := H.obj_sub, obj_quot := H.obj_quot, obj_sum := H.obj_sum, obj_one := H.obj_one, D := D, map := M, unit := u, map_φ := fun A B f hA hB hf i x => inj B hB i ?_ map_γ := fun A B f hA hB hf i x => inj B hB i ?_ map_id := fun A hA i => LinearMap.ext fun x => i …` and prove the remaining obligations. Rewrite using `[hM A B f i hA hB hf, (hD A hA).1, (hD B hB).1, hM A B f _ hA hB hf, baseChange_Phi]`. Rewrite using `[hM A B f i hA hB hf, (hD A hA).2, (hD B hB).2, hM A B f _ hA hB hf, baseChange_Act hf]`. Rewrite using `[hM A A _ i hA hA (hid A), LinearMap.baseChange_id]`.

Both sides reduce to the same expression. Establish `hgf : IsHom A C (g ∘ₗ f)` using `fun s y => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hf, hg]`. Rewrite using `[hM A C _ i hA hC hgf, LinearMap.comp_apply, hM B C g i hB hC hg, hM A B f i hA hB hf, LinearMap.baseChange_comp]`. Both sides reduce to the same expression.

Establish `hfg : IsHom A B (f + g)` using `fun s y => by`. Rewrite using `[LinearMap.add_apply, LinearMap.add_apply, hf, hg, map_add]`. Rewrite using `[hM A B _ i hA hB hfg, map_add, hM A B f i hA hB hf, hM A B g i hA hB hg, LinearMap.baseChange_add]`. Both sides reduce to the same expression. Establish `hcf : IsHom A B (c • f)` using `fun s y => by`.

Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul]`. Rewrite using `[hM A B _ i hA hB hcf, vc_const_smul c (M A B f i x), (H.frame B hB i).2.1, H.κ_k, hM A B f i hA hB hf, LinearMap.baseChange_smul, algebraMap_smul]`. Both sides reduce to the same expression. Establish `hb : Function.Injective (f.baseChange Rk)` using `Module.Flat.lTensor_preserves_injective_linearMap f hi`. Apply `hb` to reduce the goal to its premises.

Rewrite using `[← hM A B f i hA hB hf, ← hM A B f i hA hB hf, e]`. Rewrite using `[← LinearMap.range_eq_top, ← Submodule.span_eq (LinearMap.range (M A B f i))]`. Use `frame_span_top (H.ε_idem i) (H.ε_ne i) (H.frame B hB i) _ fun t => ?_` and prove the remaining obligations. Take `⟨t, rfl⟩` from `hs t`. Conclude with `frame_map_span (β A i) (β B i) (f.baseChange Rk).toAddMonoidHom id (fun c y => map_smul (f.baseChange Rk) _ _) (M A B f i) (hM A B f i hA hB hf) ((H.frame A hA i).2.2.2 t)`.

Rewrite using `[← hu, h, map_zero]`. Rewrite using `[(hD _ H.obj_one).1, hu, hu, Phi_tmul, H.ε_φ]`. Rewrite using `[(hD _ H.obj_one).2, hu, Act_chr_one, H.ε_γ]`. Establish `he : ∀ i, β A i (x i) = ε i • ∑ j, β A j (x j)`. Introduce `i`.

Rewrite using `[Finset.smul_sum, Finset.sum_eq_single i, (H.frame A hA i).2.2.1]`. Introduce `j _ hj`. Rewrite using `[← (H.frame A hA j).2.2.1, smul_smul, H.ε_orth i j hj.symm, zero_smul]`. Introduce `h`. Conclude with `(h (Finset.mem_univ _)).elim`.

Take `⟨t, ht, hfix⟩` from `H.fix A hA (∑ j, β A j (x j)) (by`. Rewrite using `[map_sum, ← Equiv.sum_comp (Equiv.subRight (1 : ZMod n))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.subRight_apply, ← (hD A hA).1, hφ]) (by`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← (hD A hA).2, hγ]) (fun i => ⟨x i, he i⟩)`. Set `f : (Fin 1 → k) →ₗ[k] (Fin A.m → k)` to `(LinearMap.proj 0 : (Fin 1 → k) →ₗ[k] k).smulRight t`. Establish `hf : IsHom (chr 1) A f` using `fun g y => by`. Express the relevant statement in the definitionally equal form `(((1 : G →* kˣ) g : k) • y) 0 • t = A.ρ g (y 0 • t)`.

Rewrite using `[map_smul, hfix]`. Simplify using the standard rewrite rules. Use `⟨f, hf, fun i => inj A hA i ?_⟩` and prove the remaining obligations. Rewrite using `[hM _ A f i H.obj_one hA hf, hu, he, ht, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `(1 : k) • t = t`. Conclude with `one_smul _ _`.
-/
theorem exists_dfun_of_frames {k G : Type} [Field k] [Group G] {Rk : Type} [CommRing Rk] [Algebra k Rk] {l n : ℕ}
    [NeZero n] (R : RingPG k l) (κ : k⸨X⸩ →+* Rk) (φ : Rk →ₐ[k] Rk) (a : G → (Rk →ₐ[k] Rk)) (g₀ : G)
    (ε : ZMod n → Rk) (Obj : Ob k G → Prop)
    (β : ∀ A : Ob k G, ZMod n → (Vc k A.m →+ Rk ⊗[k] (Fin A.m → k))) (H : IsFrames R κ φ a g₀ ε Obj β) :
    ∃ F : DFun R n G, F.Obj = Obj ∧
      (∀ A, Obj A → ∀ i x, β A i ((F.D A).φ i x) = Phi φ A.m (β A (i - 1) x)) ∧
      (∀ A, Obj A → ∀ i x, β A i ((F.D A).γ i x) = Act a A g₀ (β A i x)) ∧
      (∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, β B i (F.map A B f i x) = f.baseChange Rk (β A i x)) ∧
      ∀ i, β (chr 1) i (F.unit i) = ε i ⊗ₜ[k] (fun _ => 1) := by
  classical
  have hD : ∀ A : Ob k G, ∃ D : ModPG R n (Vc k A.m), Obj A →
      (∀ i x, β A i (D.φ i x) = Phi φ A.m (β A (i - 1) x)) ∧ ∀ i x, β A i (D.γ i x) = Act a A g₀ (β A i x) := by
    intro A
    by_cases hA : Obj A
    · obtain ⟨D, h⟩ := H.exists_mod A hA
      exact ⟨D, fun _ => h⟩
    · exact ⟨Inh.powMod R H.γ_bijective n A.m, fun h => (hA h).elim⟩
  choose D hD using hD
  choose M hM using H.exists_map
  choose u hu using H.unit
  have inj : ∀ A, Obj A → ∀ i, Function.Injective (β A i) := fun A hA i => (H.frame A hA i).1
  have hid : ∀ A : Ob k G, IsHom A A LinearMap.id := fun _ _ _ => rfl
  refine ⟨{ Obj := Obj, obj_sub := H.obj_sub, obj_quot := H.obj_quot, obj_sum := H.obj_sum,
            obj_one := H.obj_one, D := D, map := M, unit := u,
            map_φ := fun A B f hA hB hf i x => inj B hB i ?_
            map_γ := fun A B f hA hB hf i x => inj B hB i ?_
            map_id := fun A hA i => LinearMap.ext fun x => inj A hA i ?_
            map_comp := fun A B C f g hA hB hC hf hg i => LinearMap.ext fun x => inj C hC i ?_
            map_add := fun A B f g hA hB hf hg i x => inj B hB i ?_
            map_smul := fun A B f c hA hB hf i x => inj B hB i ?_
            map_inj := fun A B f hA hB hf hi i x y e => inj A hA i ?_
            map_surj := fun A B f hA hB hf hs i => ?_
            unit_ne := fun i h => H.unit_ne i ?_
            unit_φ := fun i => inj _ H.obj_one i ?_
            unit_γ := fun i => inj _ H.obj_one i ?_
            fix := fun A hA x hφ hγ => ?_ },
    rfl, fun A hA => (hD A hA).1, fun A hA => (hD A hA).2, fun A B f hA hB hf i => hM A B f i hA hB hf, hu⟩
  · rw [hM A B f i hA hB hf, (hD A hA).1, (hD B hB).1, hM A B f _ hA hB hf, baseChange_Phi]
  · rw [hM A B f i hA hB hf, (hD A hA).2, (hD B hB).2, hM A B f _ hA hB hf, baseChange_Act hf]
  · rw [hM A A _ i hA hA (hid A), LinearMap.baseChange_id]; rfl
  · have hgf : IsHom A C (g ∘ₗ f) := fun s y => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hg]
    rw [hM A C _ i hA hC hgf, LinearMap.comp_apply, hM B C g i hB hC hg, hM A B f i hA hB hf,
      LinearMap.baseChange_comp]; rfl
  · have hfg : IsHom A B (f + g) := fun s y => by
      rw [LinearMap.add_apply, LinearMap.add_apply, hf, hg, map_add]
    rw [hM A B _ i hA hB hfg, map_add, hM A B f i hA hB hf, hM A B g i hA hB hg, LinearMap.baseChange_add]; rfl
  · have hcf : IsHom A B (c • f) := fun s y => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul]
    rw [hM A B _ i hA hB hcf, vc_const_smul c (M A B f i x), (H.frame B hB i).2.1, H.κ_k,
      hM A B f i hA hB hf, LinearMap.baseChange_smul, algebraMap_smul]; rfl
  · have hb : Function.Injective (f.baseChange Rk) := Module.Flat.lTensor_preserves_injective_linearMap f hi
    apply hb
    rw [← hM A B f i hA hB hf, ← hM A B f i hA hB hf, e]
  · rw [← LinearMap.range_eq_top, ← Submodule.span_eq (LinearMap.range (M A B f i))]
    refine frame_span_top (H.ε_idem i) (H.ε_ne i) (H.frame B hB i) _ fun t => ?_
    obtain ⟨t, rfl⟩ := hs t
    exact frame_map_span (β A i) (β B i) (f.baseChange Rk).toAddMonoidHom id
      (fun c y => map_smul (f.baseChange Rk) _ _) (M A B f i) (hM A B f i hA hB hf) ((H.frame A hA i).2.2.2 t)
  · rw [← hu, h, map_zero]
  · rw [(hD _ H.obj_one).1, hu, hu, Phi_tmul, H.ε_φ]
  · rw [(hD _ H.obj_one).2, hu, Act_chr_one, H.ε_γ]
  · have he : ∀ i, β A i (x i) = ε i • ∑ j, β A j (x j) := by
      intro i
      rw [Finset.smul_sum, Finset.sum_eq_single i, (H.frame A hA i).2.2.1]
      · intro j _ hj
        rw [← (H.frame A hA j).2.2.1, smul_smul, H.ε_orth i j hj.symm, zero_smul]
      · intro h; exact (h (Finset.mem_univ _)).elim
    obtain ⟨t, ht, hfix⟩ := H.fix A hA (∑ j, β A j (x j)) (by
        rw [map_sum, ← Equiv.sum_comp (Equiv.subRight (1 : ZMod n))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Equiv.subRight_apply, ← (hD A hA).1, hφ]) (by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← (hD A hA).2, hγ]) (fun i => ⟨x i, he i⟩)
    let f : (Fin 1 → k) →ₗ[k] (Fin A.m → k) := (LinearMap.proj 0 : (Fin 1 → k) →ₗ[k] k).smulRight t
    have hf : IsHom (chr 1) A f := fun g y => by
      change (((1 : G →* kˣ) g : k) • y) 0 • t = A.ρ g (y 0 • t)
      rw [map_smul, hfix]; simp
    refine ⟨f, hf, fun i => inj A hA i ?_⟩
    rw [hM _ A f i H.obj_one hA hf, hu, he, ht, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    congr 1
    change (1 : k) • t = t
    exact one_smul _ _

end GlobalTheory.RedFun
