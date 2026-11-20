import Mathlib

namespace GlobalTheory

namespace ScalarSnakeLength

variable {A : Type} [CommRing A]

/- English proof (translation)
The claim follows from `Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict Subtype.val_injective φ.surjective_rangeRestrict (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))`.
-/
lemma length_eq_ker_add_range {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (φ : M →ₗ[A] P) :
    Module.length A M =
      Module.length A (LinearMap.ker φ) + Module.length A (LinearMap.range φ) :=
  Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    Subtype.val_injective φ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))

/- English proof (translation)
Rewrite using `[length_eq_ker_add_range g, LinearMap.exact_iff.mp h]`.
-/
lemma length_mid {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (h : Function.Exact f g) :
    Module.length A N₂ =
      Module.length A (LinearMap.range f) + Module.length A (LinearMap.range g) := by
  rw [length_eq_ker_add_range g, LinearMap.exact_iff.mp h]

/- English proof (translation)
The claim follows from `(LinearEquiv.ofInjective f hf).length_eq`.
-/
lemma length_of_injective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (f : N₁ →ₗ[A] N₂) (hf : Function.Injective f) :
    Module.length A N₁ = Module.length A (LinearMap.range f) :=
  (LinearEquiv.ofInjective f hf).length_eq

/- English proof (translation)
Rewrite using `[LinearMap.range_eq_top.mpr hg, Module.length_top]`.
-/
lemma length_of_surjective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (g : N₁ →ₗ[A] N₂) (hg : Function.Surjective g) :
    Module.length A (LinearMap.range g) = Module.length A N₂ := by
  rw [LinearMap.range_eq_top.mpr hg, Module.length_top]

variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

def kerMap (f : M₁ →ₗ[A] M₂) (b : A) :
    LinearMap.ker (LinearMap.lsmul A M₁ b) →ₗ[A] LinearMap.ker (LinearMap.lsmul A M₂ b) :=
  f.restrict (fun x hx => by
    simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [← map_smul, hx, map_zero])

def quotMap (f : M₁ →ₗ[A] M₂) (b : A) :
    (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) →ₗ[A]
      (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)

end ScalarSnakeLength

end GlobalTheory

namespace GlobalTheory

namespace ScalarSnakeLength

variable {A : Type} [CommRing A]
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

/- English proof (translation)
Introduce `x y hxy` and use `Subtype.ext (hf (congrArg Subtype.val hxy))`.
-/
lemma kerMap_injective (f : M₁ →ₗ[A] M₂) (hf : Function.Injective f) (b : A) :
    Function.Injective (kerMap f b) := fun x y hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

/- English proof (translation)
Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : g x.1 = 0` using `congrArg Subtype.val hx`. Take `⟨y, hy⟩` from `(hfg _).1 hx'`.

Use `⟨⟨y, ?_⟩, Subtype.ext hy⟩` and prove the remaining obligations. Use `show b • y = 0`. Apply `hf` to reduce the goal to its premises. Rewrite using `[map_smul, hy, map_zero]`. Conclude with `x.2`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `Subtype.ext ((hfg _).2 ⟨y.1, rfl⟩)`.
-/
lemma exact_kerMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (kerMap f b) (kerMap g b) := by
  intro x
  constructor
  · intro hx
    have hx' : g x.1 = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hfg _).1 hx'
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show b • y = 0
    apply hf
    rw [map_smul, hy, map_zero]
    exact x.2
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((hfg _).2 ⟨y.1, rfl⟩)

/- English proof (translation)
Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g x) = 0` using `hx`.

Rewrite `hx'` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨w, hw⟩` from `hx'`. Take `⟨z, rfl⟩` from `hg w`. Establish `hw' : b • g z = g x` using `hw`. Establish `h0 : g (x - b • z) = 0` using `by rw [map_sub, map_smul, hw', sub_self]`.

Take `⟨y, hy⟩` from `(hfg _).1 h0`. Use `⟨(LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ y, ?_⟩` and prove the remaining obligations. Use `show (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (f y) = _`. Rewrite using `[hy, map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨z, rfl⟩`.

Introduce and unpack `⟨y, hy⟩`. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective _ y`. Rewrite using `[← hy]`. Use `show (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g (f y)) = 0`. Rewrite using `[(hfg _).2 ⟨y, rfl⟩, map_zero]`.
-/
lemma exact_quotMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (quotMap f b) (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  constructor
  · intro hx
    have hx' : (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g x) = 0 := hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨w, hw⟩ := hx'
    obtain ⟨z, rfl⟩ := hg w
    have hw' : b • g z = g x := hw
    have h0 : g (x - b • z) = 0 := by rw [map_sub, map_smul, hw', sub_self]
    obtain ⟨y, hy⟩ := (hfg _).1 h0
    refine ⟨(LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ y, ?_⟩
    show (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (f y) = _
    rw [hy, map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hy]
    show (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g (f y)) = 0
    rw [(hfg _).2 ⟨y, rfl⟩, map_zero]

/- English proof (translation)
Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ x`. Take `⟨y, rfl⟩` from `hg x`. Conclude with `⟨(LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ y, rfl⟩`.
-/
lemma quotMap_surjective (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g) (b : A) :
    Function.Surjective (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := hg x
  exact ⟨(LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ y, rfl⟩

noncomputable def delta (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    LinearMap.ker (LinearMap.lsmul A M₃ b) →ₗ[A] (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) :=
  SnakeLemma.δ' (LinearMap.lsmul A M₁ b) (LinearMap.lsmul A M₂ b) (LinearMap.lsmul A M₃ b)
    f g hfg f g hfg (by ext x; simp) (by ext x; simp)
    (LinearMap.ker (LinearMap.lsmul A M₃ b)).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    hg hf

/- English proof (translation)
The claim follows from `SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _ (LinearMap.ker (LinearMap.lsmul A M₂ b)).subtype (LinearMap.exact_subtype_ker_map _) _ _ _ _ _ _ (kerMap g b) (by ext x; rfl) Subtype.val_injective`.
-/
lemma exact_kerMap_delta (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (kerMap g b) (delta f g hf hg hfg b) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.ker (LinearMap.lsmul A M₂ b)).subtype (LinearMap.exact_subtype_ker_map _)
    _ _ _ _ _ _ (kerMap g b) (by ext x; rfl) Subtype.val_injective

/- English proof (translation)
The claim follows from `SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (LinearMap.exact_map_mkQ_range _) _ _ (quotMap f b) (by ext x; rfl) (Submodule.mkQ_surjective _)`.
-/
lemma exact_delta_quotMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (delta f g hf hg hfg b) (quotMap f b) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    _ _ (quotMap f b) (by ext x; rfl) (Submodule.mkQ_surjective _)

end ScalarSnakeLength

/- English proof (translation)
Introduce `A _ M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg b`. Use `open ScalarSnakeLength in`. Establish `e1` using `length_of_injective (kerMap f b) (kerMap_injective f hf b)`. Establish `e2` using `length_mid (kerMap f b) (kerMap g b) (exact_kerMap f g hf hfg b)`. Establish `e3` using `length_mid (kerMap g b) (delta f g hf hg hfg b) (exact_kerMap_delta f g hf hg hfg b)`.

Establish `e4` using `length_mid (delta f g hf hg hfg b) (quotMap f b) (exact_delta_quotMap f g hf hg hfg b)`. Establish `e5` using `length_mid (quotMap f b) (quotMap g b) (exact_quotMap f g hg hfg b)`. Establish `e6` using `length_of_surjective (quotMap g b) (quotMap_surjective g hg b)`. Rewrite using `[e1, e2, e3, e4, e5, ← e6]`. Prove the components needed by the constructor for the conclusion.

The two sides agree by associativity and commutativity. Conclude with `add_le_add le_rfl le_self_add`.
-/
theorem scalar_snake_length :
    ∀ (A : Type) [CommRing A] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [AddCommGroup M₂]
      [AddCommGroup M₃] [Module A M₁] [Module A M₂] [Module A M₃] (f : M₁ →ₗ[A] M₂)
      (g : M₂ →ₗ[A] M₃), Function.Injective f → Function.Surjective g → Function.Exact f g →
      ∀ b : A,
        Module.length A (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) =
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) +
            Module.length A (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) +
            Module.length A (M₃ ⧸ LinearMap.range (LinearMap.lsmul A M₃ b)) ∧
        Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) ≤
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) := by
  intro A _ M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg b
  open ScalarSnakeLength in
  have e1 := length_of_injective (kerMap f b) (kerMap_injective f hf b)
  have e2 := length_mid (kerMap f b) (kerMap g b) (exact_kerMap f g hf hfg b)
  have e3 := length_mid (kerMap g b) (delta f g hf hg hfg b) (exact_kerMap_delta f g hf hg hfg b)
  have e4 := length_mid (delta f g hf hg hfg b) (quotMap f b)
    (exact_delta_quotMap f g hf hg hfg b)
  have e5 := length_mid (quotMap f b) (quotMap g b) (exact_quotMap f g hg hfg b)
  have e6 := length_of_surjective (quotMap g b) (quotMap_surjective g hg b)
  rw [e1, e2, e3, e4, e5, ← e6]
  constructor
  · ac_rfl
  · exact add_le_add le_rfl le_self_add

end GlobalTheory
