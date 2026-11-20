import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics

open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i⟩`. Use `⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩` and prove the remaining obligations. Rewrite using `[FDRep.Iso.conj_ρ i γ, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`. Introduce and unpack `⟨e, he⟩`.

Establish `h1 : ∀ g, e.toLinearMap ∘ₗ τ.ρ g = σ.ρ g ∘ₗ e.toLinearMap` using `fun g => LinearMap.ext fun v => he g v`. Establish `h2 : ∀ g, e.symm.toLinearMap ∘ₗ σ.ρ g = τ.ρ g ∘ₗ e.symm.toLinearMap`. Introduce `g`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use `show e.symm (σ.ρ g v) = τ.ρ g (e.symm v)`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Use `⟨{ hom := basicsMk e.toLinearMap h1 inv := basicsMk e.symm.toLinearMap h2 hom_inv_id := ?_ inv_hom_id := ?_ }⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using `[basicsMk]`.

Use extensionality with `v`. Simplify using `[basicsMk]`.
-/
theorem nonempty_iso_iff_intertwiner {Γ : Type} [Group Γ] (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v) := by
  constructor
  · rintro ⟨i⟩
    refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
    rw [FDRep.Iso.conj_ρ i γ, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨e, he⟩
    have h1 : ∀ g, e.toLinearMap ∘ₗ τ.ρ g = σ.ρ g ∘ₗ e.toLinearMap :=
      fun g => LinearMap.ext fun v => he g v
    have h2 : ∀ g, e.symm.toLinearMap ∘ₗ σ.ρ g = τ.ρ g ∘ₗ e.symm.toLinearMap := by
      intro g
      refine LinearMap.ext fun v => ?_
      show e.symm (σ.ρ g v) = τ.ρ g (e.symm v)
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine ⟨{ hom := basicsMk e.toLinearMap h1
              inv := basicsMk e.symm.toLinearMap h2
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
    · ext v
      simp [basicsMk]
    · ext v
      simp [basicsMk]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Use `⟨?_, fun W hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`.

Apply `Simple.not_isZero τ` to reduce the goal to its premises. Rewrite using `[Limits.IsZero.iff_id_eq_zero]`. Apply `basics_hom_ext` to reduce the goal to its premises. Rewrite using `[basics_lin_id, basics_lin_zero]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Conclude with `@Subsingleton.elim _ hnt _ _`. Use `haveI hmono : Mono (basicsIncl τ W hW) := basics_mono_of_inj _ (fun x y hxy => Subtype.ext hxy)`. Break down `eq_or_ne (basicsIncl τ W hW) 0 with h0 | h0` into its components or cases. Use `left`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `w hw`. Establish `h1 : basicsLin (basicsIncl τ W hW) (⟨w, hw⟩ : W) = w` using `rfl`. Establish `h2` using `congrArg (fun f => basicsLin f (⟨w, hw⟩ : W)) h0`. Simplify using `only [basics_lin_zero, LinearMap.zero_apply] at h2`. Rewrite using `[← h1]`.

Conclude with `h2`. Use `right haveI hiso : IsIso (basicsIncl τ W hW) := (Simple.mono_isIso_iff_nonzero (basicsIncl τ W hW)).mpr h0`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `h3 : basicsLin (inv (basicsIncl τ W hW) ≫ basicsIncl τ W hW) v = v`.

Rewrite using `[IsIso.inv_hom_id, basics_lin_id]`. Both sides reduce to the same expression. Rewrite `h3` using `[basics_lin_comp]`. Rewrite using `[← h3]`. Conclude with `(basicsLin (inv (basicsIncl τ W hW)) v).2`.

Introduce and unpack `⟨hnt, hirr⟩`. Use `⟨fun {Y} f hf => ⟨fun hiso h0 => ?_, fun h0 => ?_⟩⟩` and prove the remaining obligations. Substitute `h0` using the available equality. Establish `h1 : 𝟙 τ = 0`. Rewrite using `[← IsIso.inv_hom_id (0 : Y ⟶ τ), Limits.comp_zero]`.

Establish `h2 : basicsLin (𝟙 τ) = 0`. Rewrite using `[h1, basics_lin_zero]`. Rewrite `h2` using `[basics_lin_id]`. Take `⟨⟨x, y, hxy⟩⟩` from `hnt`. Apply `hxy` to reduce the goal to its premises.

Establish `hx` using `LinearMap.congr_fun h2 x`. Establish `hy` using `LinearMap.congr_fun h2 y`. Simplify using `only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy`. Rewrite using `[hx, hy]`. Establish `hinj` using `basics_inj_of_mono f`.

Establish `hinv : ∀ g : Γ, ∀ v ∈ LinearMap.range (basicsLin f), τ.ρ g v ∈ LinearMap.range (basicsLin f)`. Introduce and unpack `g v ⟨y, rfl⟩`. Use `⟨Y.ρ g y, ?_⟩` and prove the remaining obligations. Conclude with `LinearMap.congr_fun (basics_lin_comm f g) y`. Break down `hirr _ hinv with hbot | htop` into its components or cases.

It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises. Apply `basics_hom_ext` to reduce the goal to its premises. Rewrite using `[basics_lin_zero]`. Conclude with `LinearMap.range_eq_bot.mp hbot`.

Establish `hsurj : Function.Surjective (basicsLin f)` using `LinearMap.range_eq_top.mp htop`. Set `e` to `LinearEquiv.ofBijective (basicsLin f) ⟨hinj, hsurj⟩`. Establish `hcomm : ∀ g : Γ, e.symm.toLinearMap ∘ₗ τ.ρ g = Y.ρ g ∘ₗ e.symm.toLinearMap`. Introduce `g`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Use `show e.symm (τ.ρ g v) = Y.ρ g (e.symm v)`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `show τ.ρ g v = basicsLin f (Y.ρ g (e.symm v))`. Rewrite using `[← LinearMap.comp_apply (basicsLin f), basics_lin_comm f g, LinearMap.comp_apply]`.

Use `congr 1`. Conclude with `(e.apply_symm_apply v).symm`. Use `⟨⟨basicsMk e.symm.toLinearMap hcomm, ?_, ?_⟩⟩` and prove the remaining obligations. Apply `basics_hom_ext` to reduce the goal to its premises. Rewrite using `[basics_lin_comp, basics_lin_id]`.

Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Conclude with `e.symm_apply_apply y`. Apply `basics_hom_ext` to reduce the goal to its premises. Rewrite using `[basics_lin_comp, basics_lin_id]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Conclude with `e.apply_symm_apply v`.
-/
private theorem simple_iff_isIrr {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) :
    CategoryTheory.Simple τ ↔ ReciprocityTheory.Ty.Fin.IsIrr τ.ρ := by
  constructor
  · intro hs
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply Simple.not_isZero τ
      rw [Limits.IsZero.iff_id_eq_zero]
      apply basics_hom_ext
      rw [basics_lin_id, basics_lin_zero]
      refine LinearMap.ext fun v => ?_
      exact @Subsingleton.elim _ hnt _ _
    · haveI hmono : Mono (basicsIncl τ W hW) :=
        basics_mono_of_inj _ (fun x y hxy => Subtype.ext hxy)
      rcases eq_or_ne (basicsIncl τ W hW) 0 with h0 | h0
      · left
        rw [Submodule.eq_bot_iff]
        intro w hw
        have h1 : basicsLin (basicsIncl τ W hW) (⟨w, hw⟩ : W) = w := rfl
        have h2 := congrArg (fun f => basicsLin f (⟨w, hw⟩ : W)) h0
        simp only [basics_lin_zero, LinearMap.zero_apply] at h2
        rw [← h1]
        exact h2
      · right
        haveI hiso : IsIso (basicsIncl τ W hW) :=
          (Simple.mono_isIso_iff_nonzero (basicsIncl τ W hW)).mpr h0
        rw [eq_top_iff]
        intro v _
        have h3 : basicsLin (inv (basicsIncl τ W hW) ≫ basicsIncl τ W hW) v = v := by
          rw [IsIso.inv_hom_id, basics_lin_id]
          rfl
        rw [basics_lin_comp] at h3
        rw [← h3]
        exact (basicsLin (inv (basicsIncl τ W hW)) v).2
  · rintro ⟨hnt, hirr⟩
    refine ⟨fun {Y} f hf => ⟨fun hiso h0 => ?_, fun h0 => ?_⟩⟩
    · subst h0
      have h1 : 𝟙 τ = 0 := by
        rw [← IsIso.inv_hom_id (0 : Y ⟶ τ), Limits.comp_zero]
      have h2 : basicsLin (𝟙 τ) = 0 := by
        rw [h1, basics_lin_zero]
      rw [basics_lin_id] at h2
      obtain ⟨⟨x, y, hxy⟩⟩ := hnt
      apply hxy
      have hx := LinearMap.congr_fun h2 x
      have hy := LinearMap.congr_fun h2 y
      simp only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy
      rw [hx, hy]
    · have hinj := basics_inj_of_mono f
      have hinv : ∀ g : Γ, ∀ v ∈ LinearMap.range (basicsLin f),
          τ.ρ g v ∈ LinearMap.range (basicsLin f) := by
        rintro g v ⟨y, rfl⟩
        refine ⟨Y.ρ g y, ?_⟩
        exact LinearMap.congr_fun (basics_lin_comm f g) y
      rcases hirr _ hinv with hbot | htop
      · exfalso
        apply h0
        apply basics_hom_ext
        rw [basics_lin_zero]
        exact LinearMap.range_eq_bot.mp hbot
      · have hsurj : Function.Surjective (basicsLin f) := LinearMap.range_eq_top.mp htop
        let e := LinearEquiv.ofBijective (basicsLin f) ⟨hinj, hsurj⟩
        have hcomm : ∀ g : Γ, e.symm.toLinearMap ∘ₗ τ.ρ g = Y.ρ g ∘ₗ e.symm.toLinearMap := by
          intro g
          refine LinearMap.ext fun v => ?_
          show e.symm (τ.ρ g v) = Y.ρ g (e.symm v)
          apply e.injective
          rw [LinearEquiv.apply_symm_apply]
          show τ.ρ g v = basicsLin f (Y.ρ g (e.symm v))
          rw [← LinearMap.comp_apply (basicsLin f), basics_lin_comm f g, LinearMap.comp_apply]
          congr 1
          exact (e.apply_symm_apply v).symm
        refine ⟨⟨basicsMk e.symm.toLinearMap hcomm, ?_, ?_⟩⟩
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          refine LinearMap.ext fun y => ?_
          exact e.symm_apply_apply y
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          refine LinearMap.ext fun v => ?_
          exact e.apply_symm_apply v

/- English proof (translation)
Unfold `ReciprocityTheory.Ty.Fin.St.SimpleIffIrr`. Conclude with `⟨fun Γ _ _ τ => simple_iff_isIrr τ, fun Γ _ _ τ σ => nonempty_iso_iff_intertwiner τ σ⟩`.
-/
theorem simpleIffIrr : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  unfold ReciprocityTheory.Ty.Fin.St.SimpleIffIrr
  exact ⟨fun Γ _ _ τ => simple_iff_isIrr τ, fun Γ _ _ τ σ => nonempty_iso_iff_intertwiner τ σ⟩

end GlobalTheory.CompanionTheory.TyFin
