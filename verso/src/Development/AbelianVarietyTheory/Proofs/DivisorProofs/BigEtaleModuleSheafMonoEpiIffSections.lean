import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.MonoEpi

instance wEqLBMonoEpi (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {R : Type} [CommRing R]

/- English proof (translation)
Apply `Sheaf.hom_ext` to reduce the goal to its premises. Use extensionality with `U a`. Conclude with `h (unop U) a`.
-/
theorem sec_ext {F G : Shv R} (φ ψ : F ⟶ G) (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  exact h (unop U) a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h U`. Establish `: Mono φ.hom` using `inferInstanceAs (Mono ((sheafToPresheaf _ _).map φ))`. Establish `: Mono (φ.hom.app (op U))` using `inferInstance`. Conclude with `(ModuleCat.mono_iff_injective _).1 this`.

Introduce `h`. Establish `: Mono φ.hom`. Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `U`. Conclude with `(ModuleCat.mono_iff_injective _).2 (h (unop U))`.

Conclude with `(sheafToPresheaf _ _).mono_of_mono_map this`.
-/
theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := inferInstanceAs (Mono ((sheafToPresheaf _ _).map φ))
    have : Mono (φ.hom.app (op U)) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (ModuleCat.mono_iff_injective _).2 (h (unop U))
    exact (sheafToPresheaf _ _).mono_of_mono_map this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h U a ha`. Establish `: a = 0` using `h U (by rw [ha]; exact (map_zero _).symm)`. Substitute `this` using the available equality. Conclude with `⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => map_zero _⟩`.

Introduce `h U`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨S, hS, hP⟩` from `h U a ha`. Establish `hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _)` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond`.

Use `(hF S hS).isSeparatedFor.ext fun V g hg => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Sec.res g a = Sec.res g (0 : Sec F U)`. Rewrite using `[hP V g hg]`. Conclude with `(map_zero _).symm`.
-/
theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  constructor
  · intro h U a ha
    have : a = 0 := h U (by rw [ha]; exact (map_zero _).symm)
    subst this
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => map_zero _⟩
  · intro h U
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨S, hS, hP⟩ := h U a ha
    have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
      (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond
    refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
    change Sec.res g a = Sec.res g (0 : Sec F U)
    rw [hP V g hg]
    exact (map_zero _).symm

/- English proof (translation)
Rewrite using `[← Sheaf.isLocallySurjective_iff_epi']`. Prove the components needed by the constructor for the conclusion. Introduce `h U b`. Conclude with `⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology φ.hom b, fun V g hg => hg⟩`. Introduce `h`.

Prove the components needed by the constructor for the conclusion. Introduce `U b`. Take `⟨S, hS, hP⟩` from `h U b`. Use `Scheme.etaleTopology.superset_covering ?_ hS` and prove the remaining obligations. Introduce `V g hg`.

Conclude with `hP V g hg`.
-/
theorem epi_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  constructor
  · intro h U b
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology φ.hom b, fun V g hg => hg⟩
  · intro h
    constructor
    intro U b
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    exact hP V g hg

end GlobalTheory.EtC.MonoEpi

open GlobalTheory.EtC.MonoEpi in
/- English proof (translation)
Introduce `R _ F G φ`. Conclude with `⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff_loc φ, fun ψ h => sec_ext φ ψ h⟩`.
-/
theorem GlobalTheory.EtC.mono_epi_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff_loc φ, fun ψ h => sec_ext φ ψ h⟩
