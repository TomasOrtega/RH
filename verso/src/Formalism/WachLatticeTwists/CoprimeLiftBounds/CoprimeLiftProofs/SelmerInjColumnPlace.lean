import Formalism.WachLatticeTwists.CoprimeLiftBounds.SelmerInjColumnPlace
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Imports

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

/- English proof (translation)
Introduce `O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q tens htens hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 x m hx a`. Use `choose y hy using fun b => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (x b)`. Establish `hsum : ∀ g, q (∑ b, y b • i ((κ b : D → L) g)) = ρM g m - m`. Introduce `g`. Rewrite using `[← hx g, map_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hy b, htens]`. Establish `key` using `c3 O D L V M ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 y m hsum a`. Rewrite using `[← hy a]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr key`.
-/
theorem selmer_inj_tensor_form : SelmerInjTensorForm := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q tens htens hi hq hker hsat hiρ hqρ Ff j κ
    hF1 hF2 hF3 hF4 x m hx a
  choose y hy using fun b => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (x b)
  have hsum : ∀ g, q (∑ b, y b • i ((κ b : D → L) g)) = ρM g m - m := by
    intro g
    rw [← hx g, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hy b, htens]
  have key := c3 O D L V M ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 y m hsum a
  rw [← hy a]
  exact (Submodule.Quotient.mk_eq_zero _).mpr key

/- English proof (translation)
Introduce `O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ _ V _ _ _ _ _ _ r χ Dl i q tens hiA hqA htens hi hq hker hsat Ff j κ κz hκ hF1 hF2 hF3 hF4 x hx`. Take `⟨m, hm⟩` from `LinearMap.mem_range.mp hx`. Use `selmer_inj_tensor_form O Dl L V M (resRep (uRep O (M := L) r χ) Dl) (resRep (uRep (FractionRing O) (M := V) r χ) Dl) (resRep (uRep O (M := M) r χ) Dl) i q tens htens hi hq hker hsat ?_ ?_ Ff j κz hF1 hF2 hF3 hF4 x m ?_` and prove the remaining obligations. Introduce `g v`. Conclude with `hiA (uElt r χ (g : G)) v`.

Introduce `g v`. Conclude with `hqA (uElt r χ (g : G)) v`. Introduce `g`. Establish `h1` using `congrFun hm g`. Simplify using `only [hκ]`.

Conclude with `h1.symm`.
-/
theorem selmer_inj_column_place : SelmerInjColumnPlace := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ _ V _ _ _ _ _ _ r χ Dl i q tens hiA hqA htens hi hq
    hker hsat Ff j κ κz hκ hF1 hF2 hF3 hF4 x hx
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hx
  refine selmer_inj_tensor_form O Dl L V M (resRep (uRep O (M := L) r χ) Dl)
    (resRep (uRep (FractionRing O) (M := V) r χ) Dl) (resRep (uRep O (M := M) r χ) Dl) i q tens
    htens hi hq hker hsat ?_ ?_ Ff j κz hF1 hF2 hF3 hF4 x m ?_
  · intro g v
    exact hiA (uElt r χ (g : G)) v
  · intro g v
    exact hqA (uElt r χ (g : G)) v
  · intro g
    have h1 := congrFun hm g
    simp only [hκ]
    exact h1.symm

end Formalism.RepresentationBoundsCohomology.BR
