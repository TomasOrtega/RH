import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumCoker

instance instWLBKumCoker (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/- English proof (translation)
The claim follows from `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)`.
-/
theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)

/- English proof (translation)
The claim follows from `map_zero _`.
-/
theorem sec_res_zero {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero _

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Use `((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Sec.res g x = Sec.res g 0`. Rewrite using `[hP V g hg, sec_res_zero]`.
-/
theorem sec_eq_zero {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U)
    (h : Loc U fun _ g => Sec.res g x = 0) : x = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  refine ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g x = Sec.res g 0
  rw [hP V g hg, sec_res_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

/- English proof (translation)
Establish `e` using `congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at e`. Conclude with `e.symm`.
-/
theorem sec_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have e := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

/- English proof (translation)
Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem sec_res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/- English proof (translation)
Simplify using `using hU.map g.appTop.hom`.
-/
theorem unit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

end GlobalTheory.EtC.KumCoker

open GlobalTheory.EtC.KumCoker in

/- English proof (translation)
Introduce `q _ κ h0 H1 H2`. Use `set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb`. Establish `key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b`. Introduce `V b`. Rewrite using `[← sec_map_comp, hqb, cokernel.π_desc]`.

Establish `hls : Sheaf.IsLocallySurjective (cokernel.π κ)` using `(Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance`. Establish `inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U` using `U)) := by`. Introduce `U hU`. Use `(injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)` and prove the remaining obligations. Establish `hc' : Sec.map qb c = 0` using `hc`.

Apply `sec_eq_zero` to reduce the goal to its premises. Use `⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hg`. Establish `hb' : Sec.map (cokernel.π κ) b = Sec.res g c` using `hb`. Establish `hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0`.

Rewrite using `[← key, hb', ← sec_nat, hc', sec_res_zero]`. Take `⟨a, rfl⟩` from `H1 V (unit_res hU g) b hz`. Rewrite using `[← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]`. Introduce `U hU`. Use `⟨inj U hU, fun b => ?_⟩` and prove the remaining obligations.

Take `⟨S, hS, hP⟩` from `H2 U hU b`. Use `choose c hc using hP`. Set `x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows` to `fun V g hg => Sec.map (cokernel.π κ) (c V g hg)`. Establish `hx : x.Compatible`. Introduce `Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w`.

Apply `inj Z (unit_res hU (f₁ ≫ g₁))` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) = Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))`. Rewrite using `[← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]`. Take `⟨t, ht, -⟩` from `isSheaf_forget (cokernel κ) S hS x hx`. Use `⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩` and prove the remaining obligations.

Establish `ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg)` using `ht g hg`. Express the relevant statement in the definitionally equal form `(Gm.obj.map g.op).hom (Sec.map qb t - b) = 0`. Rewrite using `[map_sub]`. Express the relevant statement in the definitionally equal form `Sec.res g (Sec.map qb t) - Sec.res g b = 0`. Rewrite using `[sec_nat, ht', key, hc, sub_self]`.
-/
theorem GlobalTheory.EtC.kumCoker_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  intro q _ κ h0 H1 H2
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b := by
    intro V b
    rw [← sec_map_comp, hqb, cokernel.π_desc]
  have hls : Sheaf.IsLocallySurjective (cokernel.π κ) := (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U := U)) := by
    intro U hU
    refine (injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)
    have hc' : Sec.map qb c = 0 := hc
    apply sec_eq_zero
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩
    obtain ⟨b, hb⟩ := hg
    have hb' : Sec.map (cokernel.π κ) b = Sec.res g c := hb
    have hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 := by
      rw [← key, hb', ← sec_nat, hc', sec_res_zero]
    obtain ⟨a, rfl⟩ := H1 V (unit_res hU g) b hz
    rw [← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]
  intro U hU
  refine ⟨inj U hU, fun b => ?_⟩
  obtain ⟨S, hS, hP⟩ := H2 U hU b
  choose c hc using hP
  let x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows :=
    fun V g hg => Sec.map (cokernel.π κ) (c V g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    apply inj Z (unit_res hU (f₁ ≫ g₁))
    change Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) =
      Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))
    rw [← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]
  obtain ⟨t, ht, -⟩ := isSheaf_forget (cokernel κ) S hS x hx
  refine ⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩
  have ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg) := ht g hg
  change (Gm.obj.map g.op).hom (Sec.map qb t - b) = 0
  rw [map_sub]
  change Sec.res g (Sec.map qb t) - Sec.res g b = 0
  rw [sec_nat, ht', key, hc, sub_self]
