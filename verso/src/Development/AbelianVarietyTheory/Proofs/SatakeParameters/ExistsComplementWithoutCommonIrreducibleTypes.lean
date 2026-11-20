import Mathlib

namespace GlobalTheory

namespace TypeComplement

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

def supRep (P : Subrepresentation ρ → Prop) : Subrepresentation ρ where
  toSubmodule := ⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule
  apply_mem_toSubmodule k := by
    have h : (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule) ≤
        (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule).comap (ρ k) := by
      refine iSup₂_le fun S hS x hx => ?_
      exact (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : P S) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun v hv => h hv

def imRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map f
  apply_mem_toSubmodule k := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨ρ k s, S.apply_mem_toSubmodule k hs, hf k s⟩

def preRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S C : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule ⊓ C.toSubmodule.comap f
  apply_mem_toSubmodule k := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨S.apply_mem_toSubmodule k hv1, ?_⟩
    show f (ρ k v) ∈ C.toSubmodule
    rw [hf k v]
    exact C.apply_mem_toSubmodule k hv2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h h'`. Conclude with `h (Subrepresentation.toSubmodule_injective h')`. Introduce and unpack `h rfl`. Conclude with `h rfl`.
-/
theorem ne_bot_iff_toSubmodule {S : Subrepresentation ρ} : S ≠ ⊥ ↔ S.toSubmodule ≠ ⊥ := by
  constructor
  · intro h h'
    exact h (Subrepresentation.toSubmodule_injective h')
  · rintro h rfl
    exact h rfl

end TypeComplement

end GlobalTheory

namespace GlobalTheory
namespace TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

/- English proof (translation)
Take `⟨s₀, hs₀, hfs₀⟩` from `hne`. Establish `hinj : Function.Injective (f ∘ₗ S.toSubmodule.subtype)`. Set `Kr : Subrepresentation ρ` to `preRep f hf S ⊥`. Establish `hK : Kr ≤ S` using `fun v hv => hv.1`. Break down `hS.le_iff.mp hK with h | h` into its components or cases.

Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Establish `hx' : (x : V) ∈ Kr.toSubmodule`. Use `⟨x.2, ?_⟩` and prove the remaining obligations. Use `show f x ∈ (⊥ : Submodule ℂ V)`.

Simplify using `using hx`. Rewrite `hx'` using `[h]`. Simplify using `only [toSubmodule_bot, Submodule.mem_bot] at hx'`. Simplify using `using Subtype.ext hx'`. It suffices to derive a contradiction.

Establish `: s₀ ∈ Kr.toSubmodule` using `by rw [h]; exact hs₀`. Conclude with `hfs₀ ((Submodule.mem_bot ℂ).mp (show f s₀ ∈ (⊥ : Submodule ℂ V) from this.2))`. Use `⟨⟨?_, fun C hC => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ne_bot_iff_toSubmodule]`. Introduce `h`.

Establish `: f s₀ ∈ (imRep f hf S).toSubmodule` using `⟨s₀, hs₀, rfl⟩`. Rewrite `this` using `[h]`. Conclude with `hfs₀ ((Submodule.mem_bot ℂ).mp this)`. Assume the negation of the conclusion as `hC0`. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_iff_toSubmodule.mp hC0)`.

Take `⟨s, hs, rfl⟩ : c ∈ (imRep f hf S).toSubmodule` from `hC.le hc`. Establish `hB : preRep f hf S C ≤ S` using `fun v hv => hv.1`. Break down `hS.le_iff.mp hB with h | h` into its components or cases. Establish `: s ∈ (preRep f hf S C).toSubmodule` using `⟨hs, hc⟩`. Rewrite `this` using `[h]`.

Simplify using `only [toSubmodule_bot, Submodule.mem_bot] at this`. Conclude with `hc0 (by simp [this])`. Establish `hle : imRep f hf S ≤ C`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Establish `: t ∈ (preRep f hf S C).toSubmodule` using `by rw [h]; exact ht`.

Conclude with `this.2`. Conclude with `lt_irrefl _ (lt_of_lt_of_le hC hle)`. Establish `hr : LinearMap.range (f ∘ₗ S.toSubmodule.subtype) = (imRep f hf S).toSubmodule`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Both sides reduce to the same expression.

Set `e : S.toSubmodule ≃ₗ[ℂ] (imRep f hf S).toSubmodule` to `(LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hr)`. Use `⟨Representation.Equiv.mk e fun k => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[e, Subrepresentation.toRepresentation, hf]`.
-/
theorem imRep_atom (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) {S : Subrepresentation ρ}
    (hS : IsAtom S) (hne : ∃ s ∈ S.toSubmodule, f s ≠ 0) :
    IsAtom (imRep f hf S) ∧
      Nonempty (S.toRepresentation.Equiv (imRep f hf S).toRepresentation) := by
  obtain ⟨s₀, hs₀, hfs₀⟩ := hne

  have hinj : Function.Injective (f ∘ₗ S.toSubmodule.subtype) := by
    let Kr : Subrepresentation ρ := preRep f hf S ⊥
    have hK : Kr ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hK with h | h
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hx' : (x : V) ∈ Kr.toSubmodule := by
        refine ⟨x.2, ?_⟩
        show f x ∈ (⊥ : Submodule ℂ V)
        simpa using hx
      rw [h] at hx'
      simp only [toSubmodule_bot, Submodule.mem_bot] at hx'
      simpa using Subtype.ext hx'
    · exfalso
      have : s₀ ∈ Kr.toSubmodule := by rw [h]; exact hs₀
      exact hfs₀ ((Submodule.mem_bot ℂ).mp (show f s₀ ∈ (⊥ : Submodule ℂ V) from this.2))
  refine ⟨⟨?_, fun C hC => ?_⟩, ?_⟩
  · rw [ne_bot_iff_toSubmodule]
    intro h
    have : f s₀ ∈ (imRep f hf S).toSubmodule := ⟨s₀, hs₀, rfl⟩
    rw [h] at this
    exact hfs₀ ((Submodule.mem_bot ℂ).mp this)
  · by_contra hC0
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_iff_toSubmodule.mp hC0)
    obtain ⟨s, hs, rfl⟩ : c ∈ (imRep f hf S).toSubmodule := hC.le hc
    have hB : preRep f hf S C ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hB with h | h
    · have : s ∈ (preRep f hf S C).toSubmodule := ⟨hs, hc⟩
      rw [h] at this
      simp only [toSubmodule_bot, Submodule.mem_bot] at this
      exact hc0 (by simp [this])
    · have hle : imRep f hf S ≤ C := by
        rintro _ ⟨t, ht, rfl⟩
        have : t ∈ (preRep f hf S C).toSubmodule := by rw [h]; exact ht
        exact this.2
      exact lt_irrefl _ (lt_of_lt_of_le hC hle)
  · have hr : LinearMap.range (f ∘ₗ S.toSubmodule.subtype) = (imRep f hf S).toSubmodule := by
      rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
    let e : S.toSubmodule ≃ₗ[ℂ] (imRep f hf S).toSubmodule :=
      (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hr)
    refine ⟨Representation.Equiv.mk e fun k => ?_⟩
    ext x
    simp [e, Subrepresentation.toRepresentation, hf]

end TypeComplement
end GlobalTheory

namespace GlobalTheory
namespace TypeComplement

/- English proof (translation)
Introduce `K V _ _ _ ρ hss hsum X hcl`. Use `haveI : ComplementedLattice (Subrepresentation ρ) := hss`. Set `Y : Subrepresentation ρ` to `supRep (fun S => IsAtom S ∧ ¬ S ≤ X)`. Establish `hYle : ∀ S : Subrepresentation ρ, IsAtom S → ¬ S ≤ X → S.toSubmodule ≤ Y.toSubmodule` using `fun S hA hn => le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ ¬ S ≤ X) => S.toSubmodule) S ⟨hA, hn⟩`. Take `⟨Y₀, hY₀⟩` from `exists_isCompl X`.

Establish `hXY₀ : IsCompl X.toSubmodule Y₀.toSubmodule`. Prove the components needed by the constructor for the conclusion. Rewrite using `[disjoint_iff]`. Conclude with `congrArg Subrepresentation.toSubmodule hY₀.inf_eq_bot`. Rewrite using `[codisjoint_iff]`.

Conclude with `congrArg Subrepresentation.toSubmodule hY₀.sup_eq_top`. Set `p : V →ₗ[ℂ] V` to `X.toSubmodule.projection Y₀.toSubmodule hXY₀`. Establish `hp : ∀ k v, p (ρ k v) = ρ k (p v)`. Introduce `k v`. Establish `hv : v ∈ X.toSubmodule ⊔ Y₀.toSubmodule` using `by rw [hXY₀.sup_eq_top]; trivial`.

Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.mp hv`. Establish `h1 : ∀ {a b : V}, a ∈ X.toSubmodule → b ∈ Y₀.toSubmodule → p (a + b) = a`. Introduce `a b ha hb`. Rewrite using `[map_add, Submodule.projection_apply_of_mem_left _ ha]`. Establish `: p b = 0` using `(Submodule.projection_apply_eq_zero_iff hXY₀).mpr hb`.

Rewrite using `[this, add_zero]`. Rewrite using `[map_add, h1 (X.apply_mem_toSubmodule k hx) (Y₀.apply_mem_toSubmodule k hy), h1 hx hy]`. Establish `hYY₀ : Y.toSubmodule ≤ Y₀.toSubmodule`. Use `iSup₂_le fun S ⟨hA, hn⟩ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Establish `hne : ∃ s ∈ S.toSubmodule, p s ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc fun s hs => (Submodule.projection_apply_eq_zero_iff hXY₀).mp (h s hs)`. Take `⟨_, ⟨e⟩⟩` from `imRep_atom p hp hA hne`.

Establish `hle : imRep p hp S ≤ X`. Introduce and unpack `_ ⟨s, _, rfl⟩`. Conclude with `Submodule.projection_apply_mem hXY₀ s`. Conclude with `hn (hcl S _ hA hle ⟨e⟩)`. Establish `hdisj : X.toSubmodule ⊓ Y.toSubmodule = ⊥` using `eq_bot_iff.mpr ((inf_le_inf_left _ hYY₀).trans (disjoint_iff.mp hXY₀.disjoint).le)`.

Use `⟨Y, ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `eq_top_iff.mpr ?_` and prove the remaining obligations. Use `show (⊤ : Subrepresentation ρ).toSubmodule ≤ _`. Use `(hsum ⊤).le.trans (iSup₂_le fun S ⟨hA, _⟩ => ?_)` and prove the remaining obligations. Distinguish the cases in `hSX : S ≤ X`.

Conclude with `le_sup_of_le_left hSX`. Conclude with `le_sup_of_le_right (hYle S hA hSX)`. Introduce `S₁ S₂ hS₁ _ hY hX`. Use `⟨fun e => ?_⟩` and prove the remaining obligations. Establish `h₁ : S₁ ≤ X` using `hcl S₁ S₂ hS₁ hX ⟨e⟩`.

Apply `hS₁.1` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[toSubmodule_bot, eq_bot_iff, ← hdisj]`. Conclude with `le_inf h₁ hY`. Introduce `T hT`.

Use `⟨fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hX : X.toSubmodule ≤ X.toSubmodule.comap T`. Use `(hsum X).le.trans (iSup₂_le fun S ⟨hA, hSX⟩ => ?_)` and prove the remaining obligations. Distinguish the cases in `hne : ∃ s ∈ S.toSubmodule, T s ≠ 0`. Take `⟨hA', ⟨e⟩⟩` from `imRep_atom T hT hA hne`.

Establish `hle : imRep T hT S ≤ X` using `hcl _ S hA' hSX ⟨e.symm⟩`. Conclude with `fun s hs => hle ⟨s, hs, rfl⟩`. Use `push_neg at hne`. Introduce `s hs`. Use `show T s ∈ X.toSubmodule`.

Rewrite using `[hne s hs]`. Conclude with `zero_mem _`. Conclude with `hX hv`. Establish `hY : Y.toSubmodule ≤ Y.toSubmodule.comap T`. Use `iSup₂_le fun S ⟨hA, hn⟩ => ?_` and prove the remaining obligations.

Distinguish the cases in `hne : ∃ s ∈ S.toSubmodule, T s ≠ 0`. Take `⟨hA', ⟨e⟩⟩` from `imRep_atom T hT hA hne`. Establish `hnX : ¬ imRep T hT S ≤ X` using `fun hle => hn (hcl S _ hA hle ⟨e⟩)`. Conclude with `fun s hs => hYle _ hA' hnX ⟨s, hs, rfl⟩`. Use `push_neg at hne`.

Introduce `s hs`. Use `show T s ∈ Y.toSubmodule`. Rewrite using `[hne s hs]`. Conclude with `zero_mem _`. Conclude with `hY hv`.
-/
theorem exists_typeComplement : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  intro K V _ _ _ ρ hss hsum X hcl
  haveI : ComplementedLattice (Subrepresentation ρ) := hss
  let Y : Subrepresentation ρ := supRep (fun S => IsAtom S ∧ ¬ S ≤ X)
  have hYle : ∀ S : Subrepresentation ρ, IsAtom S → ¬ S ≤ X → S.toSubmodule ≤ Y.toSubmodule :=
    fun S hA hn => le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ ¬ S ≤ X) =>
      S.toSubmodule) S ⟨hA, hn⟩

  obtain ⟨Y₀, hY₀⟩ := exists_isCompl X
  have hXY₀ : IsCompl X.toSubmodule Y₀.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.inf_eq_bot
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.sup_eq_top
  let p : V →ₗ[ℂ] V := X.toSubmodule.projection Y₀.toSubmodule hXY₀
  have hp : ∀ k v, p (ρ k v) = ρ k (p v) := by
    intro k v
    have hv : v ∈ X.toSubmodule ⊔ Y₀.toSubmodule := by rw [hXY₀.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : ∀ {a b : V}, a ∈ X.toSubmodule → b ∈ Y₀.toSubmodule → p (a + b) = a := by
      intro a b ha hb
      rw [map_add, Submodule.projection_apply_of_mem_left _ ha]
      have : p b = 0 := (Submodule.projection_apply_eq_zero_iff hXY₀).mpr hb
      rw [this, add_zero]
    rw [map_add, h1 (X.apply_mem_toSubmodule k hx) (Y₀.apply_mem_toSubmodule k hy), h1 hx hy]

  have hYY₀ : Y.toSubmodule ≤ Y₀.toSubmodule := by
    refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
    by_contra hc
    have hne : ∃ s ∈ S.toSubmodule, p s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc fun s hs => (Submodule.projection_apply_eq_zero_iff hXY₀).mp (h s hs)
    obtain ⟨_, ⟨e⟩⟩ := imRep_atom p hp hA hne
    have hle : imRep p hp S ≤ X := by
      rintro _ ⟨s, _, rfl⟩
      exact Submodule.projection_apply_mem hXY₀ s
    exact hn (hcl S _ hA hle ⟨e⟩)
  have hdisj : X.toSubmodule ⊓ Y.toSubmodule = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hYY₀).trans (disjoint_iff.mp hXY₀.disjoint).le)
  refine ⟨Y, ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩, ?_, ?_⟩
  ·
    refine eq_top_iff.mpr ?_
    show (⊤ : Subrepresentation ρ).toSubmodule ≤ _
    refine (hsum ⊤).le.trans (iSup₂_le fun S ⟨hA, _⟩ => ?_)
    by_cases hSX : S ≤ X
    · exact le_sup_of_le_left hSX
    · exact le_sup_of_le_right (hYle S hA hSX)
  ·
    intro S₁ S₂ hS₁ _ hY hX
    refine ⟨fun e => ?_⟩
    have h₁ : S₁ ≤ X := hcl S₁ S₂ hS₁ hX ⟨e⟩
    apply hS₁.1
    apply Subrepresentation.toSubmodule_injective
    rw [toSubmodule_bot, eq_bot_iff, ← hdisj]
    exact le_inf h₁ hY
  · intro T hT
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hX : X.toSubmodule ≤ X.toSubmodule.comap T := by
        refine (hsum X).le.trans (iSup₂_le fun S ⟨hA, hSX⟩ => ?_)
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hle : imRep T hT S ≤ X := hcl _ S hA' hSX ⟨e.symm⟩
          exact fun s hs => hle ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ X.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hX hv
    · have hY : Y.toSubmodule ≤ Y.toSubmodule.comap T := by
        refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hnX : ¬ imRep T hT S ≤ X := fun hle => hn (hcl S _ hA hle ⟨e⟩)
          exact fun s hs => hYle _ hA' hnX ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ Y.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hY hv

end TypeComplement
end GlobalTheory
