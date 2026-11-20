import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `h2 : ((2 : RZ H S A) : ℂ) = 2` using `map_ofNat (RZ H S A).subtype 2`. Unfold `RZ.rt`. Use `push_cast`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RZ.rt_coe (S A : ℕ) : ((RZ.rt H S A : RZ H S A) : ℂ) = H.rt0 := by
  have h2 : ((2 : RZ H S A) : ℂ) = 2 := map_ofNat (RZ H S A).subtype 2
  unfold RZ.rt
  push_cast
  rw [h2]
  ring

/- English proof (translation)
Unfold `IsInc at hβ`. Establish `hρ : β (RZ.rt H n l.A) = (baseKA l).ρ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0`. Rewrite using `[← RZ.rt_coe (H := H) n l.A]`.

Conclude with `hβ (RZ.rt H n l.A)`. Establish `hze : β (RZ.ze H n l.A) = (baseKA l).ζ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((β (RZ.ze H n l.A) : ℂ)) = zeta l.A`. Conclude with `hβ (RZ.ze H n l.A)`.

Use `⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩` and prove the remaining obligations. Introduce `k _ _ _ x β' hx`. Choose the witnesses or unpack the hypotheses as in `⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by`. Use `⟨(Spec.preimage (x ≫ s)).hom, ?_⟩` and prove the remaining obligations. Unfold `spMap`.

Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Establish `hb : β' = g0.comp β`. Establish `h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β))`. Unfold `spMap at hx hg0`. Rewrite using `[← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Substitute `hb` using the available equality. Take `⟨hdet, I, hI1, hI2, -⟩` from `o.geom k x g0 hg0`. Use `⟨?_, I, ?_, hI2⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hρ]`.

Conclude with `hdet`. Rewrite using `[RingHom.comp_apply, hze]`. Conclude with `hI1`.
-/
theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (KA l))
    (o : Obj D l (baseKA l) s) (β : RZ H n l.A →+* KA l) (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) :
    FullObj D (s ≫ spMap β) o.t o.etaA := by
  unfold IsInc at hβ
  have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := by
    apply Subtype.ext
    show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0
    rw [← RZ.rt_coe (H := H) n l.A]
    exact hβ (RZ.rt H n l.A)
  have hze : β (RZ.ze H n l.A) = (baseKA l).ζ := by
    apply Subtype.ext
    show ((β (RZ.ze H n l.A) : ℂ)) = zeta l.A
    exact hβ (RZ.ze H n l.A)
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩
  intro k _ _ _ x β' hx
  obtain ⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by
    refine ⟨(Spec.preimage (x ≫ s)).hom, ?_⟩
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : β' = g0.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β)) := by
      unfold spMap at hx hg0
      rw [← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hb
  obtain ⟨hdet, I, hI1, hI2, -⟩ := o.geom k x g0 hg0
  refine ⟨?_, I, ?_, hI2⟩
  · rw [RingHom.comp_apply, hρ]
    exact hdet
  · rw [RingHom.comp_apply, hze]
    exact hI1

end GlobalTheory.Models
