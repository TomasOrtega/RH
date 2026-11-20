import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevCalc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {d d' d'' : ℕ}

/- English proof (translation)
Take `⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩` from `m`. Take `⟨ψ, hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩` from `m'`. Use `⟨ψ ≫ φ, hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]`. Rewrite using `[Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]`.

Conclude with `(hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))`.
-/
theorem sRel_comp {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨ψ, hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  refine ⟨ψ ≫ φ, hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

/- English proof (translation)
Take `⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩` from `m`. Take `⟨χ, hχ, ⟨χ₂, hs', hw'⟩, hl'⟩` from `m'`. Establish `hp` using `hφ.1`. Set `F : c''.A.left ⟶ c'.A.left` to `hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])`. Establish `hF : F ≫ φ = χ` using `hp.lift_fst _ _ _`.

Establish `hFw : F ≫ c'.A.hom = c''.A.hom ≫ f'` using `hp.lift_snd _ _ _`. Set `U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A` to `lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))`. Set `F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left` to `U.left`. Establish `h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F` using `congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))`. Establish `h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F` using `congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))`.

Establish `h₃ : F₂ ≫ φ₂ = χ₂`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left`. Rewrite using `[Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]`. Use `show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left`.

Rewrite using `[Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]`. Use `⟨F, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨F₂, ⟨h₁, h₂⟩, ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite `hw'` using `[← h₃]`. Conclude with `(hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _) (iso_pull F₂ hw).symm`. Apply `hp.hom_ext` to reduce the goal to its premises.

Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))`. Establish `a₁ : (c''.lev a ^ d'').left ≫ c''.A.hom = 𝟙 S''` using `Over.w (c''.lev a ^ d'')`. Establish `a₂ : (c'.lev a ^ d').left ≫ c'.A.hom = 𝟙 S'` using `Over.w (c'.lev a ^ d')`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))`.
-/
theorem sRel_cancel {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨χ, hχ, ⟨χ₂, hs', hw'⟩, hl'⟩ := m'
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨F₂, ⟨h₁, h₂⟩, ?_⟩, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a ^ d'').left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a ^ d'')
      have a₂ : (c'.lev a ^ d').left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a ^ d')
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

/- English proof (translation)
Take `⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩` from `m`. Take `⟨h₁, h₂⟩` from `hc`. Conclude with `⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩`.
-/
theorem sRel_principal {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f)
    (hc : c.Principal) : c'.Principal := by
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

/- English proof (translation)
Establish `e₁ : x' = SiegelPull.secPull hφ x`. Use `push_injective hφ _ (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Conclude with `e.trans (SiegelPull.secPull_left hφ x).symm`. Establish `e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k)` using `push_injective hφ _ (by`. Rewrite using `[map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])`.

Rewrite using `[e₂, SiegelPull.secPull_left]`.
-/
theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

/- English proof (translation)
Take `⟨φ, pb, sq, hl⟩` from `m`. Use `⟨φ, pb, sq, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul, pow_mul]`. Conclude with `pow_section pb _ _ (hl a) e`.
-/
theorem sRel_mul {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f) (e : ℕ) :
    SRel c' c (d' * e) (d * e) f := by
  obtain ⟨φ, pb, sq, hl⟩ := m
  refine ⟨φ, pb, sq, fun a => ?_⟩
  rw [pow_mul, pow_mul]
  exact pow_section pb _ _ (hl a) e

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m` and use `⟨⟨sRel_comp m, sRel_cancel m⟩, sRel_principal m, sRel_mul m⟩`.
-/
theorem sRel_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m =>
    ⟨⟨sRel_comp m, sRel_cancel m⟩, sRel_principal m, sRel_mul m⟩

end GlobalTheory.SiegLevCalc
