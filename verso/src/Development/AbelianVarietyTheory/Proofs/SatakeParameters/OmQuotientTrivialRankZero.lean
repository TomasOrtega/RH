import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweZero

section Gen

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Take `⟨a, b, hab⟩` from `hσ.toNontrivial.exists_pair_ne`. Conclude with `hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))`.
-/
theorem nontrivial_of_isIrreducible {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := hσ.toNontrivial.exists_pair_ne
  exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

/- English proof (translation)
Set `S : Subrepresentation σ` to `⟨ℂ ∙ v, fun g x hx => by`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Rewrite using `[map_smul, hfix]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩`. Establish `hS : S = ⊤`.

Break down `hσ.eq_bot_or_eq_top S with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hv` to reduce the goal to its premises. Establish `: v ∈ S.toSubmodule` using `Submodule.mem_span_singleton_self v`. Rewrite `this` using `[h]`.

Conclude with `(Submodule.mem_bot ℂ).1 this`. Conclude with `h`. Establish `htop : (ℂ ∙ v) = ⊤` using `congrArg Subrepresentation.toSubmodule hS`. Establish `hall : ∀ g (x : V), σ g x = x`. Introduce `g x`.

Establish `: x ∈ ℂ ∙ v` using `htop ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 this`. Rewrite using `[map_smul, hfix]`. Set `e : ℂ ≃ₗ[ℂ] V` to `(LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)`. Conclude with `⟨Representation.Equiv.mk e.symm fun g => by`.

Use extensionality with `x`. Simplify using `[hall]⟩`.
-/
theorem equiv_trivial_of_fixed {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {v : V} (hv : v ≠ 0)
    (hfix : ∀ g, σ g v = v) : Nonempty (σ.Equiv (Representation.trivial ℂ G ℂ)) := by
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g x hx => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hS : S = ⊤ := by
    rcases hσ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hv
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have htop : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
  have hall : ∀ g (x : V), σ g x = x := by
    intro g x
    have : x ∈ ℂ ∙ v := htop ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [map_smul, hfix]
  let e : ℂ ≃ₗ[ℂ] V := (LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)
  exact ⟨Representation.Equiv.mk e.symm fun g => by
    ext x
    simp [hall]⟩

/- English proof (translation)
Set `L : V ⊗[ℂ] W ≃ₗ[ℂ] W` to `(TensorProduct.congr e (LinearEquiv.refl ℂ W)).trans (TensorProduct.lid ℂ W)`. Use `⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun h => ?_⟩` and prove the remaining obligations. Establish `key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (1 : Module.End ℂ V) (τ h) s) = τ h (L s)`. Introduce `s`. Proceed by induction on `s using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => simp [L]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[← key, ht]`.
-/
theorem fixed_of_tensor_left (e : V ≃ₗ[ℂ] ℂ) (τ : Representation ℂ H W) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) t = t) : ∃ w : W, w ≠ 0 ∧ ∀ h, τ h w = w := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] W := (TensorProduct.congr e (LinearEquiv.refl ℂ W)).trans (TensorProduct.lid ℂ W)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun h => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (1 : Module.End ℂ V) (τ h) s) = τ h (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, ht]

/- English proof (translation)
Set `L : V ⊗[ℂ] W ≃ₗ[ℂ] V` to `(TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)`. Use `⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun g => ?_⟩` and prove the remaining obligations. Establish `key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (σ g) (1 : Module.End ℂ W) s) = σ g (L s)`. Introduce `s`. Proceed by induction on `s using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => simp [L]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[← key, ht]`.
-/
theorem fixed_of_tensor_right (e : W ≃ₗ[ℂ] ℂ) (σ : Representation ℂ G V) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) t = t) : ∃ v : V, v ≠ 0 ∧ ∀ g, σ g v = v := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] V := (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun g => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (σ g) (1 : Module.End ℂ W) s) = σ g (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, ht]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun i => Fin.elim0 i)`.
-/
theorem gl_zero_eq_one (g : GL (Fin 0) k) : g = 1 :=
  Units.ext (Matrix.ext fun i => Fin.elim0 i)

/- English proof (translation)
Simplify using `[nabs]`.
-/
theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

/- English proof (translation)
Unfold `detRep ofChar detChar`. Rewrite using `[MonoidHom.one_comp, twist_one]`.
-/
theorem detRep_one (m : ℕ) : detRep (Fin m) (1 : kˣ →* ℂˣ) = Representation.trivial ℂ (GL (Fin m) k) ℂ := by
  unfold detRep ofChar detChar
  rw [MonoidHom.one_comp, twist_one]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[om, nabs_one']`. Conclude with `congrArg Φ (Matrix.ext fun i j => Fin.elim0 j)`.
-/
theorem om_left (n : ℕ) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin 0) k → ℂ) :
    om (1 : kˣ →* ℂˣ) (1 : GL (Fin 0) k) h Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 j)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[om, nabs_one']`. Conclude with `congrArg Φ (Matrix.ext fun i j => Fin.elim0 i)`.
-/
theorem om_right (r : ℕ) (g : GL (Fin r) k) (Φ : Matrix (Fin 0) (Fin r) k → ℂ) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin 0) k) Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 i)

/- English proof (translation)
Introduce `k _ _ _ _ r n V W _ _ _ _ σ τ hrn hσ hτ hq`. Take `⟨f, hf0, hf⟩` from `hq`. Choose the witnesses or unpack the hypotheses as in `⟨Φ, hΦ⟩ : ∃ Φ, f Φ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hf0 (LinearMap.ext hc)`. Rewrite using `[detRep_one, detRep_one]`. Break down `hrn with rfl | rfl` into its components or cases. Use `haveI := nontrivial_of_isIrreducible hσ`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`.

Take `⟨eσ⟩` from `equiv_trivial_of_fixed hσ hv (fun g => by rw [gl_zero_eq_one g, map_one]; rfl)`. Establish `ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) (f Φ) = f Φ` using `fun h => by`. Use `hf 1 h Φ Φ (om_left n h Φ).symm` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `this.symm`.

Take `⟨w, hw0, hw⟩` from `fixed_of_tensor_left eσ.toLinearEquiv τ _ hΦ ht`. Conclude with `⟨⟨eσ⟩, equiv_trivial_of_fixed hτ hw0 hw⟩`. Use `haveI := nontrivial_of_isIrreducible hτ`. Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Take `⟨eτ⟩` from `equiv_trivial_of_fixed hτ hw (fun h => by rw [gl_zero_eq_one h, map_one]; rfl)`.

Establish `ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) (f Φ) = f Φ` using `fun g => by`. Use `hf g 1 Φ Φ (om_right r g Φ).symm` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `this.symm`. Take `⟨v, hv0, hv⟩` from `fixed_of_tensor_right eτ.toLinearEquiv σ _ hΦ ht`.

Conclude with `⟨equiv_trivial_of_fixed hσ hv0 hv, ⟨eτ⟩⟩`.
-/
theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), r = 0 ∨ n = 0 → σ.IsIrreducible → τ.IsIrreducible → OmQuot 1 σ τ → Nonempty (σ.Equiv (detRep (Fin r) (1 : kˣ →* ℂˣ))) ∧ Nonempty (τ.Equiv (detRep (Fin n) (1 : kˣ →* ℂˣ))) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ hrn hσ hτ hq
  obtain ⟨f, hf0, hf⟩ := hq
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, f Φ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  rw [detRep_one, detRep_one]
  rcases hrn with rfl | rfl
  · haveI := nontrivial_of_isIrreducible hσ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨eσ⟩ := equiv_trivial_of_fixed hσ hv (fun g => by rw [gl_zero_eq_one g, map_one]; rfl)
    have ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) (f Φ) = f Φ := fun h => by
      have := hf 1 h Φ Φ (om_left n h Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨w, hw0, hw⟩ := fixed_of_tensor_left eσ.toLinearEquiv τ _ hΦ ht
    exact ⟨⟨eσ⟩, equiv_trivial_of_fixed hτ hw0 hw⟩
  · haveI := nontrivial_of_isIrreducible hτ
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨eτ⟩ := equiv_trivial_of_fixed hτ hw (fun h => by rw [gl_zero_eq_one h, map_one]; rfl)
    have ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) (f Φ) = f Φ := fun g => by
      have := hf g 1 Φ Φ (om_right r g Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨v, hv0, hv⟩ := fixed_of_tensor_right eτ.toLinearEquiv σ _ hΦ ht
    exact ⟨equiv_trivial_of_fixed hσ hv0 hv, ⟨eτ⟩⟩

end GlobalTheory.HoweZero
