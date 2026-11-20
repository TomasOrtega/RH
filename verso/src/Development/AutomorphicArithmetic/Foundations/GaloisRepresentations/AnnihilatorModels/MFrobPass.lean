import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable def frPt {κ Λ Λ' : Type} [Field κ] [CommRing Λ] [CommRing Λ'] [Algebra κ Λ] [Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ') : algPt κ Λ' ⟶ algPt κ Λ :=
  Over.homMk (spMap σ) (by
    change spMap σ ≫ spMap (algebraMap κ Λ) = spMap (algebraMap κ Λ')
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ])

/- English proof (translation)
Set `ε'' : Λ' →ₐ[κ] κ` to `{ ε' with commutes' := h1 }`. Establish `hfl : (frPt σ hσ).left = spMap σ` using `rfl`. Establish `hone : ∀ {X Y A : Over (Sp κ)} [GrpObj A] (f : X ⟶ Y), f ≫ (1 : Y ⟶ A) = 1`. Introduce `X Y A _ f`. Simplify using `[Hom.one_def]`.

Establish `hcomp : spMap ε''.toRingHom ≫ spMap σ = spMap ε.toRingHom`. Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h2]`. Establish `hgψ : (frPt σ hσ ≫ g) ≫ ψ = 1`. Rewrite using `[← hone (frPt σ hσ)]`. Use `ext1`.

Simplify using `only [Over.comp_left] at hker ⊢`. Rewrite using `[hfl, Category.assoc]`. Conclude with `hker`. Take `⟨e, he⟩` from `hK`. Establish `hP : UKer r o ψ (algPt κ Λ') (frPt σ hσ ≫ g)`.

Use `⟨hgψ, e, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[Category.assoc, he a ha, hone]`. Establish `hinf' : Inf ε'' (frPt σ hσ ≫ g)`. Unfold `Inf at hinf ⊢`.

Rewrite using `[Over.comp_left, hfl, ← Category.assoc, hcomp]`. Conclude with `hinf`. Establish `h0` using `hI κ o.A (UKer r o ψ) d hrep hcard Λ' ε'' (frPt σ hσ ≫ g) hP hinf'`. Establish `h0'` using `congrArg Over.Hom.left (h0.trans (hone (frPt σ hσ)).symm)`. Simplify using `only [Over.comp_left] at h0'`.

Conclude with `h0'`.
-/
private theorem frob_mid (hI : InfE) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {r : ℤ} {κ : Type} [Field κ] {s : Sp κ ⟶ Sp R} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} {d : ℕ}
    (hrep : RepAlg o.A (UKer r o ψ) d)
    (hcard : Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [IsLocalRing Λ'] [Algebra κ Λ] [algΛ' : Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ')
    (ε : Λ →ₐ[κ] κ) (ε' : Λ' →+* κ) (h1 : ∀ c, ε' (algebraMap κ Λ' c) = c)
    (h2 : ε'.comp σ = ε.toRingHom) (g : algPt κ Λ ⟶ o.A)
    (hK : ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) (hinf : Inf ε g)
    (hker : spMap σ ≫ (g ≫ ψ).left = spMap σ ≫ (1 : algPt κ Λ ⟶ o'.A).left) :
    spMap σ ≫ g.left = spMap σ ≫ (1 : algPt κ Λ ⟶ o.A).left := by
  let ε'' : Λ' →ₐ[κ] κ := { ε' with commutes' := h1 }
  have hfl : (frPt σ hσ).left = spMap σ := rfl
  have hone : ∀ {X Y A : Over (Sp κ)} [GrpObj A] (f : X ⟶ Y), f ≫ (1 : Y ⟶ A) = 1 := by
    intro X Y A _ f
    simp [Hom.one_def]
  have hcomp : spMap ε''.toRingHom ≫ spMap σ = spMap ε.toRingHom := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h2]
  have hgψ : (frPt σ hσ ≫ g) ≫ ψ = 1 := by
    rw [← hone (frPt σ hσ)]
    ext1
    simp only [Over.comp_left] at hker ⊢
    rw [hfl, Category.assoc]
    exact hker
  obtain ⟨e, he⟩ := hK
  have hP : UKer r o ψ (algPt κ Λ') (frPt σ hσ ≫ g) := by
    refine ⟨hgψ, e, ?_⟩
    intro a ha
    rw [Category.assoc, he a ha, hone]
  have hinf' : Inf ε'' (frPt σ hσ ≫ g) := by
    unfold Inf at hinf ⊢
    rw [Over.comp_left, hfl, ← Category.assoc, hcomp]
    exact hinf
  have h0 := hI κ o.A (UKer r o ψ) d hrep hcard Λ' ε'' (frPt σ hσ ≫ g) hP hinf'
  have h0' := congrArg Over.Hom.left (h0.trans (hone (frPt σ hσ)).symm)
  simp only [Over.comp_left] at h0'
  exact h0'

/- English proof (translation)
Introduce `hI p _ D R _ b N r f κ _ _ _ s o o' ψ hψ d hrep hcard`. Use `haveI := hψ`. Establish `hp : Nat.Prime p` using `Fact.out`. Establish `hone' : ∀ {X A B : Over (Sp κ)} [GrpObj A] [GrpObj B] (h : A ⟶ B) [IsMonHom h], (1 : X ⟶ A) ≫ h = 1`. Introduce `X A B _ _ h _`.

Simplify using `[Hom.one_def]`. Set `φ : κ ≃+* κ` to `iterateFrobeniusEquiv κ p f`. Establish `hφ : ∀ c : κ, φ c = c ^ p ^ f` using `fun c => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Establish `h0` using `GlobalTheory.SS.FrobField.cast_zero_sp κ (CharP.cast_eq_zero κ p)`. Establish `e` using `GlobalTheory.SS.FrobField.absFrob_spec κ p f hp h0 φ.toRingHom hφ`. Establish `hk : spMap φ.toRingHom ≫ g.left = spMap φ.toRingHom ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left`. Rewrite using `[← e]`. Conclude with `hg h0`.

Establish `hinv : spMap φ.symm.toRingHom ≫ spMap φ.toRingHom = 𝟙 _`. Rewrite using `[spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Simplify using the standard rewrite rules. Use `ext1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Category.assoc, hk, ← Category.assoc]`. Use `_ = _ := by rw [hinv, Category.id_comp]`. Introduce `Λ _ _ _ ε g hK hinf`. Establish `hΛ : (p : Λ) = 0`. Rewrite using `[← map_natCast (algebraMap κ Λ), CharP.cast_eq_zero, map_zero]`.

Set `τ` to `GlobalTheory.SS.FrobField.powHom Λ p f hp hΛ`. Establish `hτ : ∀ c : Λ, τ c = c ^ p ^ f` using `fun c => rfl`. Set `ε' : Λ →+* κ` to `φ.symm.toRingHom.comp ε.toRingHom`. Establish `h2 : ε'.comp τ = ε.toRingHom`. Use extensionality with `x`.

Use `show φ.symm (ε (x ^ p ^ f)) = ε x`. Rewrite using `[map_pow, ← hφ, RingEquiv.symm_apply_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hk h`. Establish `e` using `GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h τ hτ`.

Establish `hker : spMap τ ≫ (g ≫ ψ).left = spMap τ ≫ (1 : algPt κ Λ ⟶ o'.A).left`. Rewrite using `[← e]`. Conclude with `hk h`. Establish `h1 : ∀ c : κ, ε' (@algebraMap κ Λ _ _ (τ.comp (algebraMap κ Λ)).toAlgebra c) = c`. Introduce `c`.

Use `show (ε'.comp τ) (algebraMap κ Λ c) = c`. Rewrite using `[h2]`. Conclude with `ε.commutes c`. Use `frob_mid hI hrep hcard (Λ' := Λ) (algΛ' := (τ.comp (algebraMap κ Λ)).toAlgebra) τ rfl ε ε' h1 h2 g ⟨hK.choose, hK.choose_spec⟩ hinf hker` as an intermediate fact. Rewrite `this` using `[← e]`.

Conclude with `this`. Introduce `hk h`. Establish `h'` using `hk h`. Rewrite using `[Over.comp_left, ← Category.assoc, h', Category.assoc, ← Over.comp_left, hone']`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.frobPass_of :
    InfE → FrobPass := by
  intro hI p _ D R _ b N r f κ _ _ _ s o o' ψ hψ d hrep hcard
  haveI := hψ
  have hp : Nat.Prime p := Fact.out
  have hone' : ∀ {X A B : Over (Sp κ)} [GrpObj A] [GrpObj B] (h : A ⟶ B) [IsMonHom h], (1 : X ⟶ A) ≫ h = 1 := by
    intro X A B _ _ h _
    simp [Hom.one_def]
  let φ : κ ≃+* κ := iterateFrobeniusEquiv κ p f
  have hφ : ∀ c : κ, φ c = c ^ p ^ f := fun c => rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    have h0 := GlobalTheory.SS.FrobField.cast_zero_sp κ (CharP.cast_eq_zero κ p)
    have e := GlobalTheory.SS.FrobField.absFrob_spec κ p f hp h0 φ.toRingHom hφ
    have hk : spMap φ.toRingHom ≫ g.left = spMap φ.toRingHom ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
      rw [← e]
      exact hg h0
    have hinv : spMap φ.symm.toRingHom ≫ spMap φ.toRingHom = 𝟙 _ := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      simp
    ext1
    calc g.left = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ g.left := by rw [hinv, Category.id_comp]
      _ = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
        rw [Category.assoc, hk, ← Category.assoc]
      _ = _ := by rw [hinv, Category.id_comp]
  · intro Λ _ _ _ ε g hK hinf
    have hΛ : (p : Λ) = 0 := by
      rw [← map_natCast (algebraMap κ Λ), CharP.cast_eq_zero, map_zero]
    let τ := GlobalTheory.SS.FrobField.powHom Λ p f hp hΛ
    have hτ : ∀ c : Λ, τ c = c ^ p ^ f := fun c => rfl
    let ε' : Λ →+* κ := φ.symm.toRingHom.comp ε.toRingHom
    have h2 : ε'.comp τ = ε.toRingHom := by
      ext x
      show φ.symm (ε (x ^ p ^ f)) = ε x
      rw [map_pow, ← hφ, RingEquiv.symm_apply_apply]
    constructor
    · intro hk h
      have e := GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h τ hτ
      have hker : spMap τ ≫ (g ≫ ψ).left = spMap τ ≫ (1 : algPt κ Λ ⟶ o'.A).left := by
        rw [← e]
        exact hk h
      have h1 : ∀ c : κ, ε' (@algebraMap κ Λ _ _ (τ.comp (algebraMap κ Λ)).toAlgebra c) = c := by
        intro c
        show (ε'.comp τ) (algebraMap κ Λ c) = c
        rw [h2]
        exact ε.commutes c
      have := frob_mid hI hrep hcard (Λ' := Λ) (algΛ' := (τ.comp (algebraMap κ Λ)).toAlgebra) τ rfl ε ε' h1 h2 g
        ⟨hK.choose, hK.choose_spec⟩ hinf hker
      rw [← e] at this
      exact this
    · intro hk h
      have h' := hk h
      rw [Over.comp_left, ← Category.assoc, h', Category.assoc, ← Over.comp_left, hone']
