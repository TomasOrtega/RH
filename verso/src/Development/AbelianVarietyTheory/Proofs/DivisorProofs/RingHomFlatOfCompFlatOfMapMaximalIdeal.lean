import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

open TensorProduct LinearMap IsLocalRing

namespace GlobalTheory

namespace LocalFlatMax

universe u

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

/- English proof (translation)
Set `p : (M →₀ A) →ₗ[A] M` to `Finsupp.linearCombination A id`. Establish `hp : Function.Surjective p` using `Finsupp.linearCombination_id_surjective A M`. Establish `h1 : Function.Injective ((ker p).subtype.lTensor (A ⧸ I))` using `lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_mkQ I) (Submodule.mkQ_surjective I) (exact_subtype_ker_map p) hp ((lTensor_inj_iff_rTensor_inj _ _).mp h) (Module.Flat.lTensor_preserves_injective_linearMap _ (ker p).injective_subtype)`. Establish `htors : Module.IsTorsionBySet A (F ⧸ N) I`. Introduce `x a`.

Take `⟨x, rfl⟩` from `N.mkQ_surjective x`. Express the relevant statement in the definitionally equal form `N.mkQ (a.1 • x) = 0`. Conclude with `(Submodule.Quotient.mk_eq_zero N).mpr (hN (Submodule.smul_mem_smul a.2 trivial))`. Use `letI : Module (A ⧸ I) (F ⧸ N) := htors.module`. Use `haveI : IsScalarTower A (A ⧸ I) (F ⧸ N) := htors.isScalarTower`.

Use `letI : Field (A ⧸ I) := Ideal.Quotient.field I`. Establish `h2 : Function.Injective ((ker p).subtype.lTensor (F ⧸ N))`. Establish `h3 : Function.Injective ((AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N))` using `Module.Flat.lTensor_preserves_injective_linearMap _ h1`. Establish `: AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype = (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).toLinearMap ∘ₗ (AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N) ∘ₗ (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ …`. Use `ext`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `Function.Injective (AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype)`. Rewrite using `[this]`. Simplify using `using h3`. Conclude with `lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_ker_map p) hp (exact_subtype_mkQ N) (Submodule.mkQ_surjective N) ((lTensor_inj_iff_rTensor_inj _ _).mp h2) (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)`.
-/
theorem lTensor_injective_of_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (N : Submodule A F)
    (hN : I • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  let p : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective A M
  have h1 : Function.Injective ((ker p).subtype.lTensor (A ⧸ I)) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_mkQ I)
      (Submodule.mkQ_surjective I) (exact_subtype_ker_map p) hp
      ((lTensor_inj_iff_rTensor_inj _ _).mp h)
      (Module.Flat.lTensor_preserves_injective_linearMap _ (ker p).injective_subtype)
  have htors : Module.IsTorsionBySet A (F ⧸ N) I := by
    intro x a
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    change N.mkQ (a.1 • x) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hN (Submodule.smul_mem_smul a.2 trivial))
  letI : Module (A ⧸ I) (F ⧸ N) := htors.module
  haveI : IsScalarTower A (A ⧸ I) (F ⧸ N) := htors.isScalarTower
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  have h2 : Function.Injective ((ker p).subtype.lTensor (F ⧸ N)) := by
    have h3 : Function.Injective
        ((AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h1
    have : AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype =
        (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).toLinearMap ∘ₗ
          (AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N) ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).symm.toLinearMap := by
      ext
      simp
    change Function.Injective (AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype)
    rw [this]
    simpa using h3
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_ker_map p) hp
    (exact_subtype_mkQ N) (Submodule.mkQ_surjective N) ((lTensor_inj_iff_rTensor_inj _ _).mp h2)
    (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)

/- English proof (translation)
Proceed by induction on `n generalizing N with`. Consider the case `zero => exact lTensor_injective_of_smul_le I h N (le_top.trans (by simpa using hN))`. Consider the case `succ n ih`. Set `N' : Submodule A F` to `N ⊔ I ^ n • ⊤`. Establish `h1` using `ih N' le_sup_right`.

Establish `h2` using `lTensor_injective_of_smul_le I h (N.comap N'.subtype) (by`. Rewrite using `[← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_subtype_top, Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']`. Conclude with `sup_le Submodule.smul_le_right hN)`. Establish `: N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ (Submodule.comapSubtypeEquivOfLe (le_sup_left : N ≤ N')).symm.toLinearMap`. Use `ext`.

Both sides reduce to the same expression. Rewrite using `[this, lTensor_comp, lTensor_comp]`. Conclude with `h1.comp (h2.comp (LinearEquiv.lTensor M _).injective)`.
-/
theorem lTensor_injective_of_pow_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (n : ℕ) (N : Submodule A F)
    (hN : I ^ n • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  induction n generalizing N with
  | zero => exact lTensor_injective_of_smul_le I h N (le_top.trans (by simpa using hN))
  | succ n ih =>
    let N' : Submodule A F := N ⊔ I ^ n • ⊤
    have h1 := ih N' le_sup_right
    have h2 := lTensor_injective_of_smul_le I h (N.comap N'.subtype) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_subtype_top,
        Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
      exact sup_le Submodule.smul_le_right hN)
    have : N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe (le_sup_left : N ≤ N')).symm.toLinearMap := by
      ext
      rfl
    rw [this, lTensor_comp, lTensor_comp]
    exact h1.comp (h2.comp (LinearEquiv.lTensor M _).injective)

/- English proof (translation)
Introduce `F _ _ f x hx`. Establish `hy : ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) = TensorProduct.rid A M (f.lTensor M x)`. Use `Submodule.smul_induction_on (p := fun d => ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) = d) hx ?_ ?_` and prove the remaining obligations. Introduce `r hr m _`. Conclude with `⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩`.

Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a + b, by simp⟩`. Take `⟨y, hy⟩` from `hy`. Use `replace hy := (TensorProduct.rid A M).injective hy`. Set `g : F × K →ₗ[A] A` to `f.coprod (-K.subtype)`.

Set `z : M ⊗[A] (F × K)` to `(inl A F K).lTensor M x + (inr A F K).lTensor M y`. Establish `hgz : g.lTensor M z = 0`. Simplify using `only [z, g, map_add, ← lTensor_comp_apply, coprod_inl, coprod_inr, lTensor_neg, LinearMap.neg_apply, hy, add_neg_cancel]`. Establish `hL : K ≤ range g` using `fun a ha => ⟨(0, ⟨-a, neg_mem ha⟩), by simp [g]⟩`. Establish `hz : g.rangeRestrict.lTensor M z = 0`.

Apply `h _ hL` to reduce the goal to its premises. Rewrite using `[← lTensor_comp_apply, map_zero]`. Conclude with `hgz`. Take `⟨w, hw⟩` from `(lTensor_exact M (exact_subtype_ker_map g.rangeRestrict) g.surjective_rangeRestrict z).mp hz`. Use `LocalFlat.range_lTensor_le (fst A F K ∘ₗ (ker g.rangeRestrict).subtype) _ ?_ ⟨w, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨v, k⟩, hv⟩`. Establish `: f v + -(k : A) = 0` using `congrArg Subtype.val hv`. Express the relevant statement in the definitionally equal form `f v ∈ K`. Rewrite using `[add_neg_eq_zero.mp this]`. Conclude with `k.2`.

Rewrite using `[lTensor_comp_apply, hw]`. Simplify using `only [z, map_add, ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr, lTensor_id, lTensor_zero, LinearMap.zero_apply, add_zero, id_apply]`.
-/
theorem relationsLift_of_lTensor_injective (K : Ideal A)
    (h : ∀ L : Ideal A, K ≤ L → Function.Injective (L.subtype.lTensor M)) :
    LocalFlat.RelationsLift K M := by
  intro F _ _ f x hx
  have hy : ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) =
      TensorProduct.rid A M (f.lTensor M x) := by
    refine Submodule.smul_induction_on (p := fun d => ∃ y : M ⊗[A] K,
      TensorProduct.rid A M (K.subtype.lTensor M y) = d) hx ?_ ?_
    · intro r hr m _
      exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp⟩
  obtain ⟨y, hy⟩ := hy
  replace hy := (TensorProduct.rid A M).injective hy
  let g : F × K →ₗ[A] A := f.coprod (-K.subtype)
  let z : M ⊗[A] (F × K) := (inl A F K).lTensor M x + (inr A F K).lTensor M y
  have hgz : g.lTensor M z = 0 := by
    simp only [z, g, map_add, ← lTensor_comp_apply, coprod_inl, coprod_inr, lTensor_neg,
      LinearMap.neg_apply, hy, add_neg_cancel]
  have hL : K ≤ range g := fun a ha => ⟨(0, ⟨-a, neg_mem ha⟩), by simp [g]⟩
  have hz : g.rangeRestrict.lTensor M z = 0 := by
    apply h _ hL
    rw [← lTensor_comp_apply, map_zero]
    exact hgz
  obtain ⟨w, hw⟩ := (lTensor_exact M (exact_subtype_ker_map g.rangeRestrict)
    g.surjective_rangeRestrict z).mp hz
  refine LocalFlat.range_lTensor_le (fst A F K ∘ₗ (ker g.rangeRestrict).subtype) _ ?_ ⟨w, ?_⟩
  · rintro ⟨⟨v, k⟩, hv⟩
    have : f v + -(k : A) = 0 := congrArg Subtype.val hv
    change f v ∈ K
    rw [add_neg_eq_zero.mp this]
    exact k.2
  · rw [lTensor_comp_apply, hw]
    simp only [z, map_add, ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr, lTensor_id,
      lTensor_zero, LinearMap.zero_apply, add_zero, id_apply]

/- English proof (translation)
The claim follows from `LocalFlat.flat_of_relationsLift B hI fun n => relationsLift_of_lTensor_injective _ fun L hL => lTensor_injective_of_pow_smul_le I h n L (by simpa using hL)`.
-/
theorem flat_of_lTensor_injective [IsNoetherianRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] (I : Ideal A)
    [I.IsMaximal] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    relationsLift_of_lTensor_injective _ fun L hL =>
      lTensor_injective_of_pow_smul_le I h n L (by simpa using hL)

/- English proof (translation)
Set `j : J →ₗ[O] J.map (algebraMap O A)` to `{ toFun := fun a => ⟨algebraMap O A a, Ideal.mem_map_of_mem _ a.2⟩ map_add' := fun a b => Subtype.ext (by simp) map_smul' := fun a b => Subtype.ext (by simp [Algebra.smul_def]) }`. Set `t : M ⊗[O] J →ₗ[O] M ⊗[A] J.map (algebraMap O A)` to `mapOfCompatibleSMul A O O M _ ∘ₗ j.lTensor M`. Establish `ht : ∀ x, ∃ y, t y = x`. Introduce `x`. Proceed by induction on `x with`.

Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add a b ha hb`. Take `⟨a, rfl⟩` from `ha`. Take `⟨b, rfl⟩` from `hb`. Conclude with `⟨a + b, map_add _ _ _⟩`.

Consider the case `tmul m r`. Take `⟨r, hr⟩` from `r`. Proceed by induction on `hr using Submodule.span_induction generalizing m with`. Consider the case `mem r hr`. Take `⟨a, ha, rfl⟩` from `hr`.

Conclude with `⟨m ⊗ₜ ⟨a, ha⟩, rfl⟩`. Consider the case `zero => exact ⟨0, (map_zero _).trans (tmul_zero _ _).symm⟩`. Consider the case `add a b ha hb iha ihb`. Take `⟨a', ha'⟩` from `iha m`. Take `⟨b', hb'⟩` from `ihb m`.

Conclude with `⟨a' + b', by rw [map_add, ha', hb', ← tmul_add]; rfl⟩`. Consider the case `smul c a ha iha`. Take `⟨a', ha'⟩` from `iha (c • m)`. Conclude with `⟨a', by rw [ha', smul_tmul]; rfl⟩`. Establish `hc : ∀ y, TensorProduct.rid A M ((J.map (algebraMap O A)).subtype.lTensor M (t y)) = TensorProduct.rid O M (J.subtype.lTensor M y)`.

Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul m a => simp [t, j]`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨y, rfl⟩` from `ht x`. Establish `h0` using `hc y`. Rewrite `h0` using `[hx, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff]`.

Establish `h1 : y = 0` using `Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype (h0.trans (map_zero _).symm)`. Rewrite using `[h1, map_zero]`.
-/
theorem lTensor_map_injective {O : Type*} [CommRing O] [Algebra O A] [Module O M]
    [IsScalarTower O A M] [Module.Flat O M] (J : Ideal O) :
    Function.Injective ((J.map (algebraMap O A)).subtype.lTensor M) := by
  let j : J →ₗ[O] J.map (algebraMap O A) :=
    { toFun := fun a => ⟨algebraMap O A a, Ideal.mem_map_of_mem _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun a b => Subtype.ext (by simp [Algebra.smul_def]) }
  let t : M ⊗[O] J →ₗ[O] M ⊗[A] J.map (algebraMap O A) :=
    mapOfCompatibleSMul A O O M _ ∘ₗ j.lTensor M
  have ht : ∀ x, ∃ y, t y = x := by
    intro x
    induction x with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | tmul m r =>
      obtain ⟨r, hr⟩ := r
      induction hr using Submodule.span_induction generalizing m with
      | mem r hr =>
        obtain ⟨a, ha, rfl⟩ := hr
        exact ⟨m ⊗ₜ ⟨a, ha⟩, rfl⟩
      | zero => exact ⟨0, (map_zero _).trans (tmul_zero _ _).symm⟩
      | add a b ha hb iha ihb =>
        obtain ⟨a', ha'⟩ := iha m
        obtain ⟨b', hb'⟩ := ihb m
        exact ⟨a' + b', by rw [map_add, ha', hb', ← tmul_add]; rfl⟩
      | smul c a ha iha =>
        obtain ⟨a', ha'⟩ := iha (c • m)
        exact ⟨a', by rw [ha', smul_tmul]; rfl⟩
  have hc : ∀ y, TensorProduct.rid A M ((J.map (algebraMap O A)).subtype.lTensor M (t y)) =
      TensorProduct.rid O M (J.subtype.lTensor M y) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m a => simp [t, j]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ht x
  have h0 := hc y
  rw [hx, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at h0
  have h1 : y = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype
      (h0.trans (map_zero _).symm)
  rw [h1, map_zero]

end LocalFlatMax

/- English proof (translation)
Introduce `O R' E _ _ _ _ _ _ _ _ _ φ' b _ hm hb hc`. Use `algebraize [φ', b, b.comp φ']`. Use `LocalFlatMax.flat_of_lTensor_injective E (maximalIdeal R') ?_ ?_` and prove the remaining obligations. Establish `h : (maximalIdeal R').map b ≤ maximalIdeal E` using `((local_hom_TFAE b).out 0 2).mp hb`. Conclude with `h.trans (maximalIdeal_le_jacobson _)`.

Rewrite using `[← hm]`. Conclude with `LocalFlatMax.lTensor_map_injective (maximalIdeal O)`.
-/
theorem ringHom_flat_of_comp_flat_of_map_maximalIdeal :
    ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
      [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E]
      (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' →
      IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  intro O R' E _ _ _ _ _ _ _ _ _ φ' b _ hm hb hc
  algebraize [φ', b, b.comp φ']
  refine LocalFlatMax.flat_of_lTensor_injective E (maximalIdeal R') ?_ ?_
  · have h : (maximalIdeal R').map b ≤ maximalIdeal E := ((local_hom_TFAE b).out 0 2).mp hb
    exact h.trans (maximalIdeal_le_jacobson _)
  · rw [← hm]
    exact LocalFlatMax.lTensor_map_injective (maximalIdeal O)

end GlobalTheory
