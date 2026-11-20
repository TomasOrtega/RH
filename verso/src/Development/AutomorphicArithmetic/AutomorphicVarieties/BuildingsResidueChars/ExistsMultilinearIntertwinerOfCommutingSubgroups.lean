import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicOfJointlyInjectiveIntoIsotypic
open GlobalTheory.CuspRep

private def eqv {Γ X Y : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ Γ X) (ρ : Representation ℂ Γ Y) : Submodule ℂ (X →ₗ[ℂ] Y) where
  carrier := {f | ∀ g v, f (σ g v) = ρ g (f v)}
  add_mem' := by
    intro a b ha hb g v
    simp only [LinearMap.add_apply, map_add, ha g v, hb g v]
  zero_mem' := by intro g v; simp
  smul_mem' := by
    intro c a ha g v
    simp only [LinearMap.smul_apply, map_smul, ha g v]

private def eqvRep {Γ Δ X Y : Type} [Group Γ] [Group Δ] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (σ : Representation ℂ Γ X) (ρ : Representation ℂ Γ Y) (τ : Representation ℂ Δ Y)
    (h : ∀ a b y, τ a (ρ b y) = ρ b (τ a y)) : Representation ℂ Δ (eqv σ ρ) where
  toFun a :=
    { toFun := fun f => ⟨(τ a).comp f.1, fun g v => by
        simp only [LinearMap.comp_apply]; rw [f.2 g v, h]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.ext fun v => by simp)
      map_smul' := fun c f => Subtype.ext (LinearMap.ext fun v => by simp) }
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => by simp)
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem eqvRep_apply {Γ Δ X Y : Type} [Group Γ] [Group Δ] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ Γ X) (ρ : Representation ℂ Γ Y)
    (τ : Representation ℂ Δ Y) (h : ∀ a b y, τ a (ρ b y) = ρ b (τ a y)) (a : Δ) (f : eqv σ ρ) (v : X) :
    (eqvRep σ ρ τ h a f).1 v = τ a (f.1 v) := rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `Γ _ X _ _ _ σ _ Y _ _ _ ρ _ _`. Take `⟨y, hy⟩` from `exists_ne (0 : Y)`. Use `⟨MultilinearMap.constOfIsEmpty ℂ X y, fun h => hy ?_, fun i => i.elim0⟩` and prove the remaining obligations.

Simplify using `using DFunLike.congr_fun h 0`. Consider the case `succ n ih`. Introduce `Γ _ X _ _ _ σ hσ Y _ _ _ ρ hc hiso`. Establish `hc' : ∀ k : Fin n, ∀ a b y, ρ k.castSucc a (ρ (Fin.last n) b y) = ρ (Fin.last n) b (ρ k.castSucc a y)` using `fun k => hc _ _ (Fin.castSucc_lt_last k).ne`. Use `haveI : Nontrivial (eqv (σ (Fin.last n)) (ρ (Fin.last n))) := by`.

Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `h1` using `hiso (Fin.last n)`. Use `(bot_ne_top (α := Submodule ℂ Y)) (h1 ▸ (iSup_eq_bot.2 fun f => ?_).symm)` and prove the remaining obligations. Establish `h2 : (⟨f.1, f.2⟩ : eqv (σ (Fin.last n)) (ρ (Fin.last n))) = 0` using `Subsingleton.elim _ _`.

Rewrite using `[LinearMap.range_eq_bot]`. Conclude with `congrArg Subtype.val h2`. Set `b` to `Module.finBasis ℂ (X (Fin.last n))`. Take `⟨μ, hμ, hμe⟩` from `ih (fun k => Γ k.castSucc) (fun k => X k.castSucc) (fun k => σ k.castSucc) (fun k => hσ _) (eqv (σ (Fin.last n)) (ρ (Fin.last n))) (fun k => eqvRep _ _ (ρ k.castSucc) (hc' k)) (fun i j hij a c f => Subtype.ext (LinearMap.ext fun v => by`. Simplify using `only [eqvRep_apply]`.

Conclude with `hc _ _ (fun h => hij (Fin.castSucc_injective n h)) _ _ _))`. Use the proof step `(fun k => UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ Y (σ k.castSucc) (ρ k.castSucc) (hσ _) (hiso _) _ _ _ (fun t => (LinearMap.applyₗ (b t)).comp (eqv (σ (Fin.last n)) (ρ (Fin.last n))).subtype) (fun t g f => rfl) (fun f hf => Subtype.ext (b.ext fun t => hf t)))`. Use `⟨((eqv (σ (Fin.last n)) (ρ (Fin.last n))).subtype.compMultilinearMap μ).uncurryRight, fun h => hμ ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x v`. Use `DFunLike.congr_fun h (Fin.snoc x v)` as an intermediate fact.

Simplify using `using this`. Introduce `i`. Use `Fin.lastCases ?_ (fun k => ?_) i` and prove the remaining obligations. Introduce `g x`. Simplify using `only [MultilinearMap.uncurryRight_apply, Fin.init_update_last, Function.update_self, LinearMap.compMultilinearMap_apply, Submodule.subtype_apply]`.

Conclude with `(μ (Fin.init x)).2 g _`. Introduce `g x`. Simplify using `only [MultilinearMap.uncurryRight_apply, Fin.init_update_castSucc, LinearMap.compMultilinearMap_apply, Submodule.subtype_apply]`. Rewrite using `[Function.update_of_ne (Fin.castSucc_lt_last k).ne']`. Use `hμe k g (Fin.init x)` as an intermediate fact.

Conclude with `congrArg (fun f : eqv (σ (Fin.last n)) (ρ (Fin.last n)) => f.1 (x (Fin.last n))) this`.
-/
private theorem multi_fin (n : ℕ) : ∀ (Γ : Fin n → Type) [∀ i, Group (Γ i)] (X : Fin n → Type)
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, FiniteDimensional ℂ (X i)]
    (σ : ∀ i, Representation ℂ (Γ i) (X i)), (∀ i, (σ i).IsIrreducible) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (ρ : ∀ i, Representation ℂ (Γ i) Y),
    (∀ i j, i ≠ j → ∀ a b y, ρ i a (ρ j b y) = ρ j b (ρ i a y)) →
    (∀ i, (⨆ f : {f : X i →ₗ[ℂ] Y // ∀ g v, f (σ i g v) = ρ i g (f v)}, LinearMap.range f.1) = ⊤) →
    ∃ μ : MultilinearMap ℂ X Y, μ ≠ 0 ∧
      ∀ i g (x : ∀ i, X i), μ (Function.update x i (σ i g (x i))) = ρ i g (μ x) := by
  induction n with
  | zero =>
    intro Γ _ X _ _ _ σ _ Y _ _ _ ρ _ _
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    refine ⟨MultilinearMap.constOfIsEmpty ℂ X y, fun h => hy ?_, fun i => i.elim0⟩
    simpa using DFunLike.congr_fun h 0
  | succ n ih =>
    intro Γ _ X _ _ _ σ hσ Y _ _ _ ρ hc hiso
    have hc' : ∀ k : Fin n, ∀ a b y, ρ k.castSucc a (ρ (Fin.last n) b y) =
        ρ (Fin.last n) b (ρ k.castSucc a y) := fun k => hc _ _ (Fin.castSucc_lt_last k).ne
    haveI : Nontrivial (eqv (σ (Fin.last n)) (ρ (Fin.last n))) := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have h1 := hiso (Fin.last n)
      refine (bot_ne_top (α := Submodule ℂ Y)) (h1 ▸ (iSup_eq_bot.2 fun f => ?_).symm)
      have h2 : (⟨f.1, f.2⟩ : eqv (σ (Fin.last n)) (ρ (Fin.last n))) = 0 := Subsingleton.elim _ _
      rw [LinearMap.range_eq_bot]
      exact congrArg Subtype.val h2
    let b := Module.finBasis ℂ (X (Fin.last n))
    obtain ⟨μ, hμ, hμe⟩ := ih (fun k => Γ k.castSucc) (fun k => X k.castSucc) (fun k => σ k.castSucc)
      (fun k => hσ _) (eqv (σ (Fin.last n)) (ρ (Fin.last n)))
      (fun k => eqvRep _ _ (ρ k.castSucc) (hc' k))
      (fun i j hij a c f => Subtype.ext (LinearMap.ext fun v => by
        simp only [eqvRep_apply]
        exact hc _ _ (fun h => hij (Fin.castSucc_injective n h)) _ _ _))
      (fun k => UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ Y (σ k.castSucc) (ρ k.castSucc) (hσ _) (hiso _) _ _ _
        (fun t => (LinearMap.applyₗ (b t)).comp (eqv (σ (Fin.last n)) (ρ (Fin.last n))).subtype)
        (fun t g f => rfl)
        (fun f hf => Subtype.ext (b.ext fun t => hf t)))
    refine ⟨((eqv (σ (Fin.last n)) (ρ (Fin.last n))).subtype.compMultilinearMap μ).uncurryRight,
      fun h => hμ ?_, ?_⟩
    · ext x v
      have := DFunLike.congr_fun h (Fin.snoc x v)
      simpa using this
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · intro g x
        simp only [MultilinearMap.uncurryRight_apply, Fin.init_update_last, Function.update_self,
          LinearMap.compMultilinearMap_apply, Submodule.subtype_apply]
        exact (μ (Fin.init x)).2 g _
      · intro g x
        simp only [MultilinearMap.uncurryRight_apply, Fin.init_update_castSucc,
          LinearMap.compMultilinearMap_apply, Submodule.subtype_apply]
        rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne']
        have := hμe k g (Fin.init x)
        exact congrArg (fun f : eqv (σ (Fin.last n)) (ρ (Fin.last n)) => f.1 (x (Fin.last n))) this

/- English proof (translation)
Introduce `G I _ _ _ H hH X _ _ _ σ hσ Y _ _ _ ρ hiso`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin I`. Take `⟨μ, hμ, hμe⟩` from `multi_fin n (fun k => H (e.symm k)) (fun k => X (e.symm k)) (fun k => σ (e.symm k)) (fun k => hσ _) Y (fun k => ρ.comp (H (e.symm k)).subtype) (fun i j hij a b y => by`. Express the relevant statement in the definitionally equal form `ρ a.1 (ρ b.1 y) = ρ b.1 (ρ a.1 y)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hH _ _ (fun h => hij (e.symm.injective h)) _ a.2 _ b.2, map_mul, Module.End.mul_apply])`.

Use the proof step `(fun k => hiso _)`. Use `⟨(MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ X Y e).symm μ, fun h => hμ ((LinearEquiv.map_eq_zero_iff _).1 h), fun i => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩` from `e.symm.surjective i`. Introduce `g x`. Express the relevant statement in the definitionally equal form `μ (fun j => Function.update x (e.symm k) (σ _ g (x _)) (e.symm j)) = ρ g (μ fun j => x (e.symm j))`.

Rewrite using `[Function.update_comp_eq_of_injective' x e.symm.injective]`. Conclude with `hμe k g _`.
-/
theorem UpperTheory.exists_multilinear_intertwiner_of_commuting_subgroups :
    ∀ (G I : Type) [Group G] [Finite I] [DecidableEq I] (H : I → Subgroup G), (∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) → ∀ (X : I → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, FiniteDimensional ℂ (X i)] (σ : ∀ i, Representation ℂ (H i) (X i)), (∀ i, (σ i).IsIrreducible) → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (ρ : Representation ℂ G Y), (∀ i, (⨆ f : {f : X i →ₗ[ℂ] Y // ∀ (g : H i) v, f (σ i g v) = ρ g (f v)}, LinearMap.range f.1) = ⊤) → ∃ μ : MultilinearMap ℂ X Y, μ ≠ 0 ∧ ∀ i (g : H i) (x : ∀ i, X i), μ (Function.update x i (σ i g (x i))) = ρ g (μ x) := by
  intro G I _ _ _ H hH X _ _ _ σ hσ Y _ _ _ ρ hiso
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨μ, hμ, hμe⟩ := multi_fin n (fun k => H (e.symm k)) (fun k => X (e.symm k))
    (fun k => σ (e.symm k)) (fun k => hσ _) Y (fun k => ρ.comp (H (e.symm k)).subtype)
    (fun i j hij a b y => by
      change ρ a.1 (ρ b.1 y) = ρ b.1 (ρ a.1 y)
      rw [← Module.End.mul_apply, ← map_mul, hH _ _ (fun h => hij (e.symm.injective h)) _ a.2 _ b.2,
        map_mul, Module.End.mul_apply])
    (fun k => hiso _)
  refine ⟨(MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ X Y e).symm μ,
    fun h => hμ ((LinearEquiv.map_eq_zero_iff _).1 h), fun i => ?_⟩
  obtain ⟨k, rfl⟩ := e.symm.surjective i
  intro g x
  change μ (fun j => Function.update x (e.symm k) (σ _ g (x _)) (e.symm j)) = ρ g (μ fun j => x (e.symm j))
  rw [Function.update_comp_eq_of_injective' x e.symm.injective]
  exact hμe k g _
