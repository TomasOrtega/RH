import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open NumberField
open scoped TensorProduct

namespace GlobalTheory.CM.TenExp

/- English proof (translation)
Use `choose l hl hW using h`. Use `hΛ.to_subtype` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨z, z', hne, e⟩ : ∃ z z' : ℂ, z ≠ z' ∧ l z = l z' := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Establish `hi : Function.Injective fun z => (⟨l z, hl z⟩ : Λ)` using `fun z z' e => by`. Assume the negation of the conclusion as `h0`. Conclude with `hc z z' h0 (congrArg Subtype.val e)`. Conclude with `not_countable (α := ℝ) (hi.comp Complex.ofReal_injective).countable`. Establish `h1` using `W.sub_mem (hW z) (hW z')`.

Rewrite `h1` using `[e, sub_sub_sub_cancel_right, ← sub_smul]`. Conclude with `(W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1`.
-/
theorem mem_of_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {Λ : Set V} (hΛ : Λ.Countable)
    (W : Submodule ℂ V) {v : V} (h : ∀ z : ℂ, ∃ l ∈ Λ, z • v - l ∈ W) : v ∈ W := by
  choose l hl hW using h
  have := hΛ.to_subtype
  obtain ⟨z, z', hne, e⟩ : ∃ z z' : ℂ, z ≠ z' ∧ l z = l z' := by
    by_contra hc
    push Not at hc
    have hi : Function.Injective fun z => (⟨l z, hl z⟩ : Λ) := fun z z' e => by
      by_contra h0
      exact hc z z' h0 (congrArg Subtype.val e)
    exact not_countable (α := ℝ) (hi.comp Complex.ofReal_injective).countable
  have h1 := W.sub_mem (hW z) (hW z')
  rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
  exact (W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[← sub_eq_zero, ← Submodule.mem_bot ℂ]`. Use `mem_of_countable hΛ ⊥ fun z => ⟨_, h (z • u), ?_⟩` and prove the remaining obligations. Simplify using `[smul_sub]`.
-/
theorem linear_eq_of_countable {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {Λ : Set V} (hΛ : Λ.Countable) {F F' : U →ₗ[ℂ] V} (h : ∀ u, F u - F' u ∈ Λ) : F = F' := by
  ext u
  rw [← sub_eq_zero, ← Submodule.mem_bot ℂ]
  refine mem_of_countable hΛ ⊥ fun z => ⟨_, h (z • u), ?_⟩
  simp [smul_sub]

section Tensor

variable {O M : Type} [CommRing O] [Algebra O ℂ] [AddCommGroup M] [Module O M]

/- English proof (translation)
Use `letI : Module O V := Module.compHom V (algebraMap O ℂ)`. Use `haveI : IsScalarTower O ℂ V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Set `f' : M →ₗ[O] V` to `{ f with map_smul' := hf }`. Conclude with `⟨f'.liftBaseChange ℂ, fun z a => rfl⟩`.
-/
theorem exists_lift {V : Type} [AddCommGroup V] [Module ℂ V] (f : M →+ V)
    (hf : ∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) :
    ∃ F : ℂ ⊗[O] M →ₗ[ℂ] V, ∀ z a, F (z ⊗ₜ a) = z • f a := by
  letI : Module O V := Module.compHom V (algebraMap O ℂ)
  haveI : IsScalarTower O ℂ V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f' : M →ₗ[O] V := { f with map_smul' := hf }
  exact ⟨f'.liftBaseChange ℂ, fun z a => rfl⟩

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `exists_lift P hP`. Establish `hc : ∀ t, ex (Φ t) = eqv (TensorProduct.comm O X M (e₀.rTensor M t))` using `fun t => by`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `tmul z a => simp [hΦ, hex]`.

Consider the case `add x y hx hy => simp [hx, hy]`. Establish `hker : ∀ t, ex (Φ t) = 0 → ∃ a, t = 1 ⊗ₜ a` using `fun t ht => by`. Rewrite `ht` using `[hc, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]`. Take `⟨s, rfl⟩` from `(rTensor_exact M (f := Algebra.linearMap O ℂ) hk hs t).1 ht`. Take `⟨a, rfl⟩` from `(TensorProduct.lid O M).symm.surjective s`.

Conclude with `⟨a, by simp⟩`. Establish `hsurj : Function.Surjective Φ` using `fun v => by`. Use `mem_of_countable hΛ (LinearMap.range Φ) fun z => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `(eqv.surjective.comp ((TensorProduct.comm O X M).surjective.comp (LinearMap.rTensor_surjective M hs))) (ex (z • v))`. Use `⟨z • v - Φ t, ?_, t, by simp⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, map_sub, hc, ← ht]`. Conclude with `sub_self _`. Establish `hinj : Function.Injective Φ` using `(injective_iff_map_eq_zero _).2 fun t ht => by`. Take `⟨a, rfl⟩` from `hker t (by rw [ht, map_zero])`. Rewrite `ht` using `[hΦ, one_smul, map_eq_zero_iff _ hi]`.

Simplify using `[ht]`. Use `⟨eq_top_iff.2 fun v _ => ?_, fun v => ⟨fun hv => ?_, ?_⟩, fun V' _ _ f hf => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `hsurj v`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `tmul z a => rw [hΦ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ (hx trivial) (hy trivial)`. Take `⟨t, rfl⟩` from `hsurj v`.

Take `⟨a, rfl⟩` from `hker t hv`. Conclude with `⟨a, by rw [hΦ, one_smul]⟩`. Introduce and unpack `⟨a, rfl⟩`. Rewrite using `[← one_smul ℂ (P a), hex, (hk 1).2 ⟨1, map_one _⟩]`. Simplify using the standard rewrite rules.

Take `⟨F, hF⟩` from `exists_lift f hf`. Use `⟨F ∘ₗ (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm.toLinearMap, fun a => ?_⟩` and prove the remaining obligations. Establish `: P a = LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩ (1 ⊗ₜ a)` using `((hΦ 1 a).trans (one_smul _ _)).symm`. Rewrite using `[this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hF, one_smul]`.
-/
theorem tensor_unif {X Y V : Type} [AddCommGroup X] [Module O X]
    [AddCommGroup Y] [Module O Y] [AddCommGroup V] [Module ℂ V] (eqv : M ⊗[O] X ≃ₗ[O] Y) (e₀ : ℂ →ₗ[O] X)
    (hs : Function.Surjective e₀) (hk : ∀ z, e₀ z = 0 ↔ z ∈ Set.range (algebraMap O ℂ)) (ex : V →+ Y)
    (hΛ : Set.Countable {v | ex v = 0}) (P : M →+ V) (hP : ∀ (o : O) a, P (o • a) = algebraMap O ℂ o • P a)
    (hi : Function.Injective P) (hex : ∀ (z : ℂ) a, ex (z • P a) = eqv (a ⊗ₜ e₀ z)) :
    Submodule.span ℂ (Set.range P) = ⊤ ∧ (∀ v, ex v = 0 ↔ v ∈ P.range) ∧
      ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (f : M →+ V'), (∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) →
        ∃ F : V →ₗ[ℂ] V', ∀ a, F (P a) = f a := by
  obtain ⟨Φ, hΦ⟩ := exists_lift P hP
  have hc : ∀ t, ex (Φ t) = eqv (TensorProduct.comm O X M (e₀.rTensor M t)) := fun t => by
    induction t with
    | zero => simp
    | tmul z a => simp [hΦ, hex]
    | add x y hx hy => simp [hx, hy]
  have hker : ∀ t, ex (Φ t) = 0 → ∃ a, t = 1 ⊗ₜ a := fun t ht => by
    rw [hc, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at ht
    obtain ⟨s, rfl⟩ := (rTensor_exact M (f := Algebra.linearMap O ℂ) hk hs t).1 ht
    obtain ⟨a, rfl⟩ := (TensorProduct.lid O M).symm.surjective s
    exact ⟨a, by simp⟩
  have hsurj : Function.Surjective Φ := fun v => by
    refine mem_of_countable hΛ (LinearMap.range Φ) fun z => ?_
    obtain ⟨t, ht⟩ := (eqv.surjective.comp ((TensorProduct.comm O X M).surjective.comp
      (LinearMap.rTensor_surjective M hs))) (ex (z • v))
    refine ⟨z • v - Φ t, ?_, t, by simp⟩
    simp only [Set.mem_setOf_eq, map_sub, hc, ← ht]
    exact sub_self _
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun t ht => by
    obtain ⟨a, rfl⟩ := hker t (by rw [ht, map_zero])
    rw [hΦ, one_smul, map_eq_zero_iff _ hi] at ht
    simp [ht]
  refine ⟨eq_top_iff.2 fun v _ => ?_, fun v => ⟨fun hv => ?_, ?_⟩, fun V' _ _ f hf => ?_⟩
  · obtain ⟨t, rfl⟩ := hsurj v
    induction t with
    | zero => simp
    | tmul z a => rw [hΦ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  · obtain ⟨t, rfl⟩ := hsurj v
    obtain ⟨a, rfl⟩ := hker t hv
    exact ⟨a, by rw [hΦ, one_smul]⟩
  · rintro ⟨a, rfl⟩
    rw [← one_smul ℂ (P a), hex, (hk 1).2 ⟨1, map_one _⟩]
    simp
  · obtain ⟨F, hF⟩ := exists_lift f hf
    refine ⟨F ∘ₗ (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm.toLinearMap, fun a => ?_⟩
    have : P a = LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩ (1 ⊗ₜ a) :=
      ((hΦ 1 a).trans (one_smul _ _)).symm
    rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hF, one_smul]

end Tensor

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hs : EigenSplit.IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)`. Take `⟨b⟩` from `EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)`. Conclude with `EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b) (by simpa using NumberField.discr_ne_zero E)`. Set `b` to `(EigenSplit.isInternal_eigenSub hs r).collectedBasis fun φ => Module.finBasis ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))`. Set `e` to `Fintype.equivFin (Σ φ : E →+* ℂ, Fin (Module.finrank ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))))`.

Establish `hb : ∀ a j, r a (b.reindex e j) = (e.symm j).1 (a : E) • b.reindex e j` using `fun a j => by`. Rewrite using `[Module.Basis.reindex_apply]`. Conclude with `EigenSplit.mem_eigenSub.1 ((EigenSplit.isInternal_eigenSub hs r).collectedBasis_mem _ (e.symm j)) a`. Use `⟨_, (b.reindex e).equivFun, fun j => (e.symm j).1, fun a v j => ?_⟩` and prove the remaining obligations. Generalize the expression as in `b.reindex e = b' at hb`.

Take `⟨z, rfl⟩` from `b'.equivFun.symm.surjective v`. Establish `: r a (b'.equivFun.symm z) = b'.equivFun.symm fun j => (e.symm j).1 (a : E) * z j`. Simplify using `only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hb, smul_smul, mul_comm]`. Rewrite using `[this]`. Simplify using `only [LinearEquiv.apply_symm_apply]`.
-/
theorem exists_diagonal_coordinates {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (r : 𝓞 E →+* Module.End ℂ V) :
    ∃ (g : ℕ) (B : V ≃ₗ[ℂ] (Fin g → ℂ)) (ty : Fin g → (E →+* ℂ)), ∀ (a : 𝓞 E) v j, B (r a v) j = ty j (a : E) * B v j := by
  classical
  have hs : EigenSplit.IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  let b := (EigenSplit.isInternal_eigenSub hs r).collectedBasis
    fun φ => Module.finBasis ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))
  let e := Fintype.equivFin (Σ φ : E →+* ℂ,
    Fin (Module.finrank ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))))
  have hb : ∀ a j, r a (b.reindex e j) = (e.symm j).1 (a : E) • b.reindex e j := fun a j => by
    rw [Module.Basis.reindex_apply]
    exact EigenSplit.mem_eigenSub.1 ((EigenSplit.isInternal_eigenSub hs r).collectedBasis_mem _ (e.symm j)) a
  refine ⟨_, (b.reindex e).equivFun, fun j => (e.symm j).1, fun a v j => ?_⟩
  generalize b.reindex e = b' at hb
  obtain ⟨z, rfl⟩ := b'.equivFun.symm.surjective v
  have : r a (b'.equivFun.symm z) = b'.equivFun.symm fun j => (e.symm j).1 (a : E) * z j := by
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hb, smul_smul, mul_comm]
  rw [this]
  simp only [LinearEquiv.apply_symm_apply]

/- English proof (translation)
Establish `ext : ∀ F F' : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ a, F (P a) = F' (P a)) → F = F'` using `fun F F' h => LinearMap.ext_on_range hs h`. Use `⟨fun hτ => ?_, fun hτ => ?_⟩` and prove the remaining obligations. Use `letI : Algebra (𝓞 E) ℂ := (τ.comp (algebraMap (𝓞 E) E)).toAlgebra`. Establish `hsm : ∀ (s : 𝓞 E) (z : ℂ), s • z = τ s * z` using `fun _ _ => rfl`. Use `haveI : FaithfulSMul (𝓞 E) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 (τ.injective.comp (IsFractionRing.injective (𝓞 E) E))`.

Set `f : {i // ty i = τ} → (M →ₗ[𝓞 E] ℂ)` to `fun i => { toFun := fun a => P a i, map_add' := fun a b => by simp, map_smul' := fun s a => by simp [hP, hsm, i.2] }`. Establish `hli : LinearIndependent ℂ f`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Use `ext (∑ j : {i // ty i = τ}, c j • LinearMap.proj j.1) 0 fun a => by` as an intermediate fact.

Simplify `DFunLike.congr_fun hc a` using `[f]`. Use `DFunLike.congr_fun this (Pi.single i.1 1)` as an intermediate fact. Simplify `this` using `[Pi.single_apply, Subtype.val_inj]`. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range f)` using `fun φ _ => by`. Take `⟨F, hF⟩` from `hu φ.toAddMonoidHom fun a => by simp [hsm, hτ]`.

Establish `h0 : ∀ i, ty i ≠ τ → F (Pi.single i 1) = 0` using `fun i hi => by`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : 𝓞 E, ty i s ≠ τ s := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hi (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))`.

Use `ext (F ∘ₗ LinearMap.pi fun j => ty j (s : E) • LinearMap.proj j) (τ s • F) fun a => by` as an intermediate fact. Establish `e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R` using `ℂ) (φ := fun _ => ℂ) j) (P a) = P (s • a) := funext fun j => by simp [hP]`. Rewrite using `[LinearMap.comp_apply, e, hF, LinearMap.smul_apply, hF]`. Simplify using `[hsm]`. Use `DFunLike.congr_fun this (Pi.single i 1)` as an intermediate fact.

Establish `e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R` using `ℂ) (φ := fun _ => ℂ) j) (Pi.single i 1) = ty i s • Pi.single i 1 := funext fun j => by`. Apply the tactic sequence `by_cases h : j = i <;> simp [h]`. Rewrite `this` using `[LinearMap.comp_apply, e, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Conclude with `(mul_eq_mul_right_iff.1 this).resolve_left hs`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`.

Use `⟨fun i => F (Pi.single i.1 1), LinearMap.ext fun a => ?_⟩` and prove the remaining obligations. Establish `e` using `hF a`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ, ← Fintype.sum_subtype_add_sum_subtype (fun i => ty i = τ), Finset.sum_eq_zero (s := Finset.univ (α := {i // ¬ ty i = τ})) fun i _ => by`. Use `h0 i.1 i.2` as an intermediate fact. Rewrite using `[show (fun j => if i.1 = j then (1 : ℂ) else 0) = Pi.single i.1 1 from by`.

Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm], this, smul_zero], add_zero] at e`. Use `Eq.trans ?_ e` and prove the remaining obligations. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), (LinearMap.liftBaseChangeEquiv ℂ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) M ℂ).finrank_eq]`.

Conclude with `Subspace.dual_finrank_eq`. Rewrite using `[Nat.card_eq_zero]`. Use `Or.inl ⟨fun i => hτ ?_⟩` and prove the remaining obligations. Use `ext (τ w • LinearMap.proj i.1) (ω • LinearMap.proj i.1) fun a => by` as an intermediate fact. Use `congrFun (hw a) i.1` as an intermediate fact.

Rewrite `this` using `[hP, i.2]`. Simplify using `using this`. Simplify using `using DFunLike.congr_fun this (Pi.single i.1 1)`.
-/
theorem card_type {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : M →+ (Fin g → ℂ)} (hP : ∀ (s : 𝓞 E) a i, P (s • a) i = ty i (s : E) * P a i)
    (hs : Submodule.span ℂ (Set.range P) = ⊤) {w : 𝓞 E} {ω : ℂ} (hw : ∀ a, P (w • a) = ω • P a)
    (hu : ∀ f : M →+ ℂ, (∀ a, f (w • a) = ω • f a) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ a, F (P a) = f a)
    (τ : E →+* ℂ) : (τ w = ω → Nat.card {i // ty i = τ} = Module.finrank (𝓞 E) M) ∧
      (τ w ≠ ω → Nat.card {i // ty i = τ} = 0) := by
  classical
  have ext : ∀ F F' : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ a, F (P a) = F' (P a)) → F = F' := fun F F' h =>
    LinearMap.ext_on_range hs h
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · letI : Algebra (𝓞 E) ℂ := (τ.comp (algebraMap (𝓞 E) E)).toAlgebra
    have hsm : ∀ (s : 𝓞 E) (z : ℂ), s • z = τ s * z := fun _ _ => rfl
    haveI : FaithfulSMul (𝓞 E) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2
      (τ.injective.comp (IsFractionRing.injective (𝓞 E) E))
    let f : {i // ty i = τ} → (M →ₗ[𝓞 E] ℂ) := fun i =>
      { toFun := fun a => P a i, map_add' := fun a b => by simp, map_smul' := fun s a => by simp [hP, hsm, i.2] }
    have hli : LinearIndependent ℂ f := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := ext (∑ j : {i // ty i = τ}, c j • LinearMap.proj j.1) 0 fun a => by
        simpa [f] using DFunLike.congr_fun hc a
      have := DFunLike.congr_fun this (Pi.single i.1 1)
      simpa [Pi.single_apply, Subtype.val_inj] using this
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := fun φ _ => by
      obtain ⟨F, hF⟩ := hu φ.toAddMonoidHom fun a => by simp [hsm, hτ]
      have h0 : ∀ i, ty i ≠ τ → F (Pi.single i 1) = 0 := fun i hi => by
        obtain ⟨s, hs⟩ : ∃ s : 𝓞 E, ty i s ≠ τ s := by
          by_contra hc
          push Not at hc
          exact hi (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
        have := ext (F ∘ₗ LinearMap.pi fun j => ty j (s : E) • LinearMap.proj j) (τ s • F) fun a => by
          have e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j) (P a) =
              P (s • a) := funext fun j => by simp [hP]
          rw [LinearMap.comp_apply, e, hF, LinearMap.smul_apply, hF]
          simp [hsm]
        have := DFunLike.congr_fun this (Pi.single i 1)
        have e : (LinearMap.pi fun j => ty j (s : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) j)
            (Pi.single i 1) = ty i s • Pi.single i 1 := funext fun j => by
          by_cases h : j = i <;> simp [h]
        rw [LinearMap.comp_apply, e, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
        exact (mul_eq_mul_right_iff.1 this).resolve_left hs
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => F (Pi.single i.1 1), LinearMap.ext fun a => ?_⟩
      have e := hF a
      rw [LinearMap.pi_apply_eq_sum_univ, ← Fintype.sum_subtype_add_sum_subtype (fun i => ty i = τ),
        Finset.sum_eq_zero (s := Finset.univ (α := {i // ¬ ty i = τ})) fun i _ => by
          have := h0 i.1 i.2
          rw [show (fun j => if i.1 = j then (1 : ℂ) else 0) = Pi.single i.1 1 from by
            funext j; simp [Pi.single_apply, eq_comm], this, smul_zero], add_zero] at e
      refine Eq.trans ?_ e
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      congr 2
      funext j; simp [Pi.single_apply, eq_comm]
    rw [Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis (Module.Basis.mk hli hsp),
      (LinearMap.liftBaseChangeEquiv ℂ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) M ℂ).finrank_eq]
    exact Subspace.dual_finrank_eq
  · rw [Nat.card_eq_zero]
    refine Or.inl ⟨fun i => hτ ?_⟩
    have := ext (τ w • LinearMap.proj i.1) (ω • LinearMap.proj i.1) fun a => by
      have := congrFun (hw a) i.1
      rw [hP, i.2] at this
      simpa using this
    simpa using DFunLike.congr_fun this (Pi.single i.1 1)

end GlobalTheory.CM.TenExp
