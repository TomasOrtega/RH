import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.WeightedPowerFormIntegrability

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)`.
-/
theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

/- English proof (translation)
The claim follows from `((isSheaf_types G).isSheafFor (⊥ : Presieve Z) (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext (fun _ _ h => h.elim)`.
-/
theorem sec_empty (G : Shv R) (Z : Scheme.{0}) [IsEmpty Z] (a b : Sec G Z) : a = b :=
  ((isSheaf_types G).isSheafFor (⊥ : Presieve Z) (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext
    (fun _ _ h => h.elim)

/- English proof (translation)
Take `⟨hopen, hcov, hdisj⟩` from `hj`. Set `U : X.Cover (Scheme.precoverage @Etale)` to `Scheme.Cover.mkOfCovers (Fin r) Y j (fun x => by obtain ⟨s, y, hy⟩ := hcov x; exact ⟨s, y, hy⟩) (fun s => by have := hopen s; infer_instance)`. Establish `hmem : Sieve.ofArrows Y j ∈ Scheme.etaleTopology X` using `U.mem_grothendieckTopology`. Establish `hsf` using `(isSheaf_types G).isSheafFor _ hmem`. Rewrite `hsf` using `[Presieve.isSheafFor_arrows_iff]`.

Establish `hcomp : ∀ x : ∀ s, Sec G (Y s), Presieve.Arrows.Compatible (G.obj ⋙ forget _) j x`. Introduce `x s t Z gs gt h`. Distinguish the cases in `hst : s = t`. Substitute `hst haveI := hopen s` using the available equality. Rewrite `h` using `[cancel_mono]`.

Rewrite using `[h]`. Use `haveI : IsEmpty Z := ⟨fun z => by`. Establish `h1 : (j s) (gs z) = (j t) (gt z)`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]`. Conclude with `Set.disjoint_left.1 (hdisj s t hst) ⟨gs z, rfl⟩ ⟨gt z, h1.symm⟩⟩`.

Conclude with `sec_empty G Z _ _`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Take `⟨t, -, ht⟩` from `hsf _ (hcomp (fun s => Sec.res (j s) b))`. Conclude with `(ht a fun s => congrFun hab s).trans (ht b fun s => rfl).symm`.

Introduce `x`. Take `⟨t, ht, -⟩` from `hsf x (hcomp x)`. Conclude with `⟨t, funext ht⟩`.
-/
theorem sec_sum (G : Shv R) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) :
    Function.Bijective (fun (y : Sec G X) (s : Fin r) => Sec.res (j s) y) := by
  obtain ⟨hopen, hcov, hdisj⟩ := hj
  let U : X.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers (Fin r) Y j
    (fun x => by obtain ⟨s, y, hy⟩ := hcov x; exact ⟨s, y, hy⟩) (fun s => by have := hopen s; infer_instance)
  have hmem : Sieve.ofArrows Y j ∈ Scheme.etaleTopology X := U.mem_grothendieckTopology
  have hsf := (isSheaf_types G).isSheafFor _ hmem
  rw [Presieve.isSheafFor_arrows_iff] at hsf
  have hcomp : ∀ x : ∀ s, Sec G (Y s), Presieve.Arrows.Compatible (G.obj ⋙ forget _) j x := by
    intro x s t Z gs gt h
    by_cases hst : s = t
    · subst hst
      haveI := hopen s
      rw [cancel_mono] at h
      rw [h]
    · haveI : IsEmpty Z := ⟨fun z => by
        have h1 : (j s) (gs z) = (j t) (gt z) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
        exact Set.disjoint_left.1 (hdisj s t hst) ⟨gs z, rfl⟩ ⟨gt z, h1.symm⟩⟩
      exact sec_empty G Z _ _
  constructor
  · intro a b hab
    obtain ⟨t, -, ht⟩ := hsf _ (hcomp (fun s => Sec.res (j s) b))
    exact (ht a fun s => congrFun hab s).trans (ht b fun s => rfl).symm
  · intro x
    obtain ⟨t, ht, -⟩ := hsf x (hcomp x)
    exact ⟨t, funext ht⟩

end CrystallineSemistableComparison.WeightedPowerFormIntegrability
