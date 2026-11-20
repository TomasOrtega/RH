import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.Pass.LocDirect

/- English proof (translation)
Introduce `D i w hw r Xs k M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂`. Use `set L₁ : (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) →ₗ[D.nd.O i] (Fin a₁ → Fin D.R.nV → KK D.nd i) := LinearMap.funLeft _ _ (Fin.castAdd a₂) with hL₁`. Use `set L₂ : (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) →ₗ[D.nd.O i] (Fin a₂ → Fin D.R.nV → KK D.nd i) := LinearMap.funLeft _ _ (Fin.natAdd a₁) with hL₂`. Use `set x : Fin (a₁ + a₂) → D.nd.X i := Fin.append x₁ x₂ with hx`. Use `set E : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i := Fin.append E₁ E₂ with hEdef`.

Use `set Y : Submodule (D.nd.O i) (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) := Y₁.comap L₁ ⊓ Y₂.comap L₂ with hY`. Establish `hL₁a : ∀ (γ : GE D.nd) (v : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i), L₁ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (v j)) = fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (L₁ v j)`. Introduce `γ v`. Use function extensionality and compare the values at `j`. Simplify using `[hL₁, LinearMap.funLeft_apply, hx, Fin.append_left]`.

Establish `hL₂a : ∀ (γ : GE D.nd) (v : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i), L₂ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (v j)) = fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (L₂ v j)`. Introduce `γ v`. Use function extensionality and compare the values at `j`. Simplify using `[hL₂, LinearMap.funLeft_apply, hx, Fin.append_right]`. Establish `hL₁E : ∀ γ : GE D.nd, L₁ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) = fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (E₁ j) - E₁ j`.

Introduce `γ`. Use function extensionality and compare the values at `j`. Simplify using `[hL₁, LinearMap.funLeft_apply, hx, hEdef, Fin.append_left]`. Establish `hL₂E : ∀ γ : GE D.nd, L₂ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) = fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (E₂ j) - E₂ j`. Introduce `γ`.

Use function extensionality and compare the values at `j`. Simplify using `[hL₂, LinearMap.funLeft_apply, hx, hEdef, Fin.append_right]`. Establish `hst : ∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y`. Introduce `γ y hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show L₁ _ ∈ Y₁`. Rewrite using `[hL₁a]`. Conclude with `hst₁ γ _ hy.1`. Use `show L₂ _ ∈ Y₂`. Rewrite using `[hL₂a]`.

Conclude with `hst₂ γ _ hy.2`. Establish `hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y`. Introduce `γ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show L₁ _ ∈ Y₁`.

Rewrite using `[hL₁E]`. Conclude with `hE₁ γ`. Use `show L₂ _ ∈ Y₂`. Rewrite using `[hL₂E]`. Conclude with `hE₂ γ`.

Establish `hFG : Y.FG`. Set `A : ((Fin a₁ → Fin D.R.nV → KK D.nd i) × (Fin a₂ → Fin D.R.nV → KK D.nd i)) →ₗ[D.nd.O i] (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i)` to `{ toFun := fun p => Fin.append p.1 p.2 map_add' := by`. Introduce `p q`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Fin.append_left, Fin.append_right]`.

Use the proof step `map_smul' := by`. Introduce `c p`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Fin.append_left, Fin.append_right] }`. Establish `hYeq : Y = (Y₁.prod Y₂).map A`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨(L₁ y, L₂ y), ⟨hy.1, hy.2⟩, ?_⟩` and prove the remaining obligations. Use `show Fin.append (L₁ y) (L₂ y) = y`.

Simplify using `only [hL₁, hL₂, LinearMap.funLeft_apply]`. Conclude with `Fin.append_castAdd_natAdd`. Introduce and unpack `⟨p, ⟨hp1, hp2⟩, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show L₁ (Fin.append p.1 p.2) ∈ Y₁`.

Establish `: L₁ (Fin.append p.1 p.2) = p.1`. Use function extensionality and compare the values at `j`. Simplify using `[hL₁, LinearMap.funLeft_apply, Fin.append_left]`. Rewrite using `[this]`. Conclude with `hp1`.

Use `show L₂ (Fin.append p.1 p.2) ∈ Y₂`. Establish `: L₂ (Fin.append p.1 p.2) = p.2`. Use function extensionality and compare the values at `j`. Simplify using `[hL₂, LinearMap.funLeft_apply, Fin.append_right]`. Rewrite using `[this]`.

Conclude with `hp2`. Rewrite using `[hYeq]`. Conclude with `(hY₁.prod hY₂).map A`. Establish `hxs : ∀ j, x j ∈ Xs`. Introduce `j`.

Use `Fin.addCases (fun j => ?_) (fun j => ?_) j` and prove the remaining obligations. Simplify using `only [hx, Fin.append_left]`. Conclude with `hx₁ j`. Simplify using `only [hx, Fin.append_right]`. Conclude with `hx₂ j`.

Use `⟨a₁ + a₂, x, hxs, E, Y, hFG, hst, hE, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `c ⟨φ₁, hφ₁, rfl⟩`. Set `ρ : ↥Y →ₗ[D.nd.O i] ↥Y₁` to `L₁.restrict (p := Y) (q := Y₁) (fun y hy => hy.1)`. Use `⟨φ₁ ∘ₗ ρ, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ y`.

Establish `h` using `hφ₁ γ (ρ y)`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[← h]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[ρ, LinearMap.restrict_apply, hL₁a]`. Use function extensionality and compare the values at `g`. Simplify using `only [LinearMap.comp_apply]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[ρ, LinearMap.restrict_apply, hL₁E]`. Introduce and unpack `c ⟨φ₂, hφ₂, rfl⟩`. Set `ρ : ↥Y →ₗ[D.nd.O i] ↥Y₂` to `L₂.restrict (p := Y) (q := Y₂) (fun y hy => hy.2)`. Use `⟨φ₂ ∘ₗ ρ, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ y`.

Establish `h` using `hφ₂ γ (ρ y)`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[← h]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[ρ, LinearMap.restrict_apply, hL₂a]`. Use function extensionality and compare the values at `g`. Simplify using `only [LinearMap.comp_apply]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[ρ, LinearMap.restrict_apply, hL₂E]`.
-/
theorem pushSet_merge : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (a₁ : ℕ) (x₁ : Fin a₁ → D.nd.X i), (∀ j, x₁ j ∈ Xs) → ∀ (E₁ : Fin a₁ → Fin D.R.nV → KK D.nd i) (Y₁ : Submodule (D.nd.O i) (Fin a₁ → Fin D.R.nV → KK D.nd i)), Y₁.FG → ∀ (hst₁ : (∀ γ : GE D.nd, ∀ y ∈ Y₁, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (y j)) ∈ Y₁)) (hE₁ : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (E₁ j) - E₁ j) ∈ Y₁)) (a₂ : ℕ) (x₂ : Fin a₂ → D.nd.X i), (∀ j, x₂ j ∈ Xs) → ∀ (E₂ : Fin a₂ → Fin D.R.nV → KK D.nd i) (Y₂ : Submodule (D.nd.O i) (Fin a₂ → Fin D.R.nV → KK D.nd i)), Y₂.FG → ∀ (hst₂ : (∀ γ : GE D.nd, ∀ y ∈ Y₂, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (y j)) ∈ Y₂)) (hE₂ : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (E₂ j) - E₂ j) ∈ Y₂)), ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG) (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)) (hE : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)), GlobalTheory.Pass.LocDirect.pushSet i w hw r M x₁ E₁ Y₁ hst₁ hE₁ ⊆ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE ∧ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x₂ E₂ Y₂ hst₂ hE₂ ⊆ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE := by
  intro D i w hw r Xs k M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂
  set L₁ : (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) →ₗ[D.nd.O i] (Fin a₁ → Fin D.R.nV → KK D.nd i) :=
    LinearMap.funLeft _ _ (Fin.castAdd a₂) with hL₁
  set L₂ : (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) →ₗ[D.nd.O i] (Fin a₂ → Fin D.R.nV → KK D.nd i) :=
    LinearMap.funLeft _ _ (Fin.natAdd a₁) with hL₂
  set x : Fin (a₁ + a₂) → D.nd.X i := Fin.append x₁ x₂ with hx
  set E : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i := Fin.append E₁ E₂ with hEdef
  set Y : Submodule (D.nd.O i) (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) := Y₁.comap L₁ ⊓ Y₂.comap L₂ with hY
  have hL₁a : ∀ (γ : GE D.nd) (v : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i),
      L₁ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (v j)) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (L₁ v j) := by
    intro γ v; funext j; simp [hL₁, LinearMap.funLeft_apply, hx, Fin.append_left]
  have hL₂a : ∀ (γ : GE D.nd) (v : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i),
      L₂ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (v j)) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (L₂ v j) := by
    intro γ v; funext j; simp [hL₂, LinearMap.funLeft_apply, hx, Fin.append_right]
  have hL₁E : ∀ γ : GE D.nd,
      L₁ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (E₁ j) - E₁ j := by
    intro γ; funext j; simp [hL₁, LinearMap.funLeft_apply, hx, hEdef, Fin.append_left]
  have hL₂E : ∀ γ : GE D.nd,
      L₂ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (E₂ j) - E₂ j := by
    intro γ; funext j; simp [hL₂, LinearMap.funLeft_apply, hx, hEdef, Fin.append_right]
  have hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y := by
    intro γ y hy
    refine ⟨?_, ?_⟩
    · show L₁ _ ∈ Y₁
      rw [hL₁a]; exact hst₁ γ _ hy.1
    · show L₂ _ ∈ Y₂
      rw [hL₂a]; exact hst₂ γ _ hy.2
  have hE : ∀ γ : GE D.nd,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y := by
    intro γ
    refine ⟨?_, ?_⟩
    · show L₁ _ ∈ Y₁
      rw [hL₁E]; exact hE₁ γ
    · show L₂ _ ∈ Y₂
      rw [hL₂E]; exact hE₂ γ
  have hFG : Y.FG := by
    let A : ((Fin a₁ → Fin D.R.nV → KK D.nd i) × (Fin a₂ → Fin D.R.nV → KK D.nd i)) →ₗ[D.nd.O i]
        (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) :=
      { toFun := fun p => Fin.append p.1 p.2
        map_add' := by
          intro p q; funext j
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Fin.append_left, Fin.append_right]
        map_smul' := by
          intro c p; funext j
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Fin.append_left, Fin.append_right] }
    have hYeq : Y = (Y₁.prod Y₂).map A := by
      ext y
      constructor
      · intro hy
        refine ⟨(L₁ y, L₂ y), ⟨hy.1, hy.2⟩, ?_⟩
        show Fin.append (L₁ y) (L₂ y) = y
        simp only [hL₁, hL₂, LinearMap.funLeft_apply]
        exact Fin.append_castAdd_natAdd
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · show L₁ (Fin.append p.1 p.2) ∈ Y₁
          have : L₁ (Fin.append p.1 p.2) = p.1 := by
            funext j; simp [hL₁, LinearMap.funLeft_apply, Fin.append_left]
          rw [this]; exact hp1
        · show L₂ (Fin.append p.1 p.2) ∈ Y₂
          have : L₂ (Fin.append p.1 p.2) = p.2 := by
            funext j; simp [hL₂, LinearMap.funLeft_apply, Fin.append_right]
          rw [this]; exact hp2
    rw [hYeq]
    exact (hY₁.prod hY₂).map A
  have hxs : ∀ j, x j ∈ Xs := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [hx, Fin.append_left]; exact hx₁ j
    · simp only [hx, Fin.append_right]; exact hx₂ j
  refine ⟨a₁ + a₂, x, hxs, E, Y, hFG, hst, hE, ?_, ?_⟩
  · rintro c ⟨φ₁, hφ₁, rfl⟩
    let ρ : ↥Y →ₗ[D.nd.O i] ↥Y₁ := L₁.restrict (p := Y) (q := Y₁) (fun y hy => hy.1)
    refine ⟨φ₁ ∘ₗ ρ, ?_, ?_⟩
    · intro γ y
      have h := hφ₁ γ (ρ y)
      simp only [LinearMap.comp_apply]
      rw [← h]
      congr 1
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₁a]
    · funext g
      simp only [LinearMap.comp_apply]
      congr 2
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₁E]
  · rintro c ⟨φ₂, hφ₂, rfl⟩
    let ρ : ↥Y →ₗ[D.nd.O i] ↥Y₂ := L₂.restrict (p := Y) (q := Y₂) (fun y hy => hy.2)
    refine ⟨φ₂ ∘ₗ ρ, ?_, ?_⟩
    · intro γ y
      have h := hφ₂ γ (ρ y)
      simp only [LinearMap.comp_apply]
      rw [← h]
      congr 1
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₂a]
    · funext g
      simp only [LinearMap.comp_apply]
      congr 2
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₂E]

end GlobalTheory.Pass.LocDirect
