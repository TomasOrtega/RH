import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

attribute [local instance] algMdl

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M) f]`. Conclude with `he _`.
-/
private theorem e_model (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (f : topF X M) :
    e (algebraMap (topF X M) (topBar X M) f) = io X f := by
  rw [IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M) f]
  exact he _

/- English proof (translation)
Establish `hex : ∃ g : topGal X M, ∀ z, e (g z) = σ (e z)`. Use `⟨AlgEquiv.ofRingEquiv (f := e.trans (σ.trans e.symm)) ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Simplify using `only [RingEquiv.trans_apply]`. Rewrite using `[e_model X M e he f, hσ f f.2, ← e_model X M e he f, RingEquiv.symm_apply_apply]`.

Introduce `w`. Simplify using `[AlgEquiv.ofRingEquiv_apply]`. Conclude with `Classical.epsilon_spec (p := fun g : topGal X M => ∀ w, e (g w) = σ (e w)) hex z`.
-/
private theorem cj_spec (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (σ : RingAut (Kb X))
    (hσ : FixF X M σ) (z : topBar X M) : e (cj X M e σ z) = σ (e z) := by
  have hex : ∃ g : topGal X M, ∀ z, e (g z) = σ (e z) := by
    refine ⟨AlgEquiv.ofRingEquiv (f := e.trans (σ.trans e.symm)) ?_, ?_⟩
    · intro f
      simp only [RingEquiv.trans_apply]
      rw [e_model X M e he f, hσ f f.2, ← e_model X M e he f, RingEquiv.symm_apply_apply]
    · intro w
      simp [AlgEquiv.ofRingEquiv_apply]
  exact Classical.epsilon_spec (p := fun g : topGal X M => ∀ w, e (g w) = σ (e w)) hex z

/- English proof (translation)
Introduce `f hf` and use `by show σ (τ (io X f)) = io X f rw [hτ f hf, hσ f hf]`.
-/
private theorem fix_mul (X : Tower Ω ε) (M : ℕ) {σ τ : RingAut (Kb X)} (hσ : FixF X M σ) (hτ : FixF X M τ) :
    FixF X M (σ * τ) := fun f hf => by
  show σ (τ (io X f)) = io X f
  rw [hτ f hf, hσ f hf]

/- English proof (translation)
Introduce `f hf` and use `by show σ.symm (io X f) = io X f rw [RingEquiv.symm_apply_eq] exact (hσ f hf).symm`.
-/
private theorem fix_inv (X : Tower Ω ε) (M : ℕ) {σ : RingAut (Kb X)} (hσ : FixF X M σ) : FixF X M σ⁻¹ := fun f hf => by
  show σ.symm (io X f) = io X f
  rw [RingEquiv.symm_apply_eq]
  exact (hσ f hf).symm

/- English proof (translation)
Use extensionality with `z`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[cj_spec X M e he _ (fix_mul X M hσ hτ), AlgEquiv.mul_apply, cj_spec X M e he _ hσ, cj_spec X M e he _ hτ]`. Both sides reduce to the same expression.
-/
private theorem cj_mul (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) {σ τ : RingAut (Kb X)}
    (hσ : FixF X M σ) (hτ : FixF X M τ) : cj X M e (σ * τ) = cj X M e σ * cj X M e τ := by
  ext z
  apply e.injective
  rw [cj_spec X M e he _ (fix_mul X M hσ hτ), AlgEquiv.mul_apply, cj_spec X M e he _ hσ, cj_spec X M e he _ hτ]
  rfl

/- English proof (translation)
Use extensionality with `z`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[cj_spec X M e he _ (fun f _ => rfl)]`. Both sides reduce to the same expression.
-/
private theorem cj_one (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) :
    cj X M e 1 = 1 := by
  ext z
  apply e.injective
  rw [cj_spec X M e he _ (fun f _ => rfl)]
  rfl

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← cj_mul X M e he (fix_inv X M hσ) hσ, inv_mul_cancel, cj_one X M e he]`.
-/
private theorem cj_inv (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) {σ : RingAut (Kb X)}
    (hσ : FixF X M σ) : cj X M e σ⁻¹ = (cj X M e σ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← cj_mul X M e he (fix_inv X M hσ) hσ, inv_mul_cancel, cj_one X M e he]

/- English proof (translation)
Unfold `topZeta zt`. Rewrite using `[he]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem e_zeta (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (l n : ℕ) :
    e (topZeta X M l n) = zt X (l ^ n) := by
  unfold topZeta zt
  rw [he]
  push_cast
  rfl

/- English proof (translation)
Introduce `Ω _ _ _ ε X M e he`. Use `⟨fun σ hσ z => cj_spec X M e he σ hσ z, fun σ τ hσ hτ => ⟨fix_mul X M hσ hτ, fix_inv X M hσ, cj_mul X M e he hσ hτ, cj_inv X M e he hσ⟩, fun σ hσ => ?_, fun l n => e_zeta X M e he l n, ?_⟩` and prove the remaining obligations. Establish `hF : FixF X M σ` using `fun f hf => hσ f (mdl_le_lev X _ _ hf)`. Establish `key : ∀ f : topL X M, cj X M e σ (algebraMap (topL X M) (topBar X M) f) = algebraMap (topL X M) (topBar X M) f`. Introduce `f`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[cj_spec X M e he σ hF, he]`. Conclude with `hσ _ f.2`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, f, rfl⟩`.

Conclude with `key f`. Introduce `l n hl σ _ a b hb i hab`. Establish `hm : 0 < l ^ n` using `pow_pos (Nat.pos_of_ne_zero hl) n`. Use `(lgB Ω ε X (l ^ n) hm).2.2.1 (e a) (e b) i (by simpa using hb) ?_` and prove the remaining obligations. Rewrite using `[hab, map_mul, map_pow, e_zeta X M e he l n]`.
-/
theorem cjB : CjB := by
  intro Ω _ _ _ ε X M e he
  refine ⟨fun σ hσ z => cj_spec X M e he σ hσ z, fun σ τ hσ hτ =>
    ⟨fix_mul X M hσ hτ, fix_inv X M hσ, cj_mul X M e he hσ hτ, cj_inv X M e he hσ⟩, fun σ hσ => ?_,
    fun l n => e_zeta X M e he l n, ?_⟩
  · have hF : FixF X M σ := fun f hf => hσ f (mdl_le_lev X _ _ hf)
    have key : ∀ f : topL X M, cj X M e σ (algebraMap (topL X M) (topBar X M) f) = algebraMap (topL X M) (topBar X M) f := by
      intro f
      apply e.injective
      rw [cj_spec X M e he σ hF, he]
      exact hσ _ f.2
    refine ⟨hF, ?_⟩
    rintro ⟨_, f, rfl⟩
    exact key f
  · intro l n hl σ _ a b hb i hab
    have hm : 0 < l ^ n := pow_pos (Nat.pos_of_ne_zero hl) n
    refine (lgB Ω ε X (l ^ n) hm).2.2.1 (e a) (e b) i (by simpa using hb) ?_
    rw [hab, map_mul, map_pow, e_zeta X M e he l n]

end UpperTheory.V.Z.Kato.Sym.PT

end
