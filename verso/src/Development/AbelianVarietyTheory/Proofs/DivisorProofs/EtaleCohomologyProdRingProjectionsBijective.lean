import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSpecProdBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafBiprodDescIsIsoOfResBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdCoh

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨cpull (inv c) I n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[BiprodCls.cpull_cpull, IsIso.inv_hom_id, BiprodCls.cpull_id]`. Rewrite using `[BiprodCls.cpull_cpull, IsIso.hom_inv_id, BiprodCls.cpull_id]`.
-/
theorem cpull_bijective_of_isIso {R : Type} [CommRing R] {K L : Cx R} (c : K ⟶ L) [IsIso c] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull c I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull (inv c) I n, fun x => ?_, fun x => ?_⟩
  · rw [BiprodCls.cpull_cpull, IsIso.inv_hom_id, BiprodCls.cpull_id]
  · rw [BiprodCls.cpull_cpull, IsIso.hom_inv_id, BiprodCls.cpull_id]

/- English proof (translation)
Rewrite using `[show f = g from funext h]`. Conclude with `hg`.
-/
theorem bij_of_eq {α β : Sort*} {f g : α → β} (h : ∀ x, f x = g x) (hg : Function.Bijective g) :
    Function.Bijective f := by
  rw [show f = g from funext h]; exact hg

/- English proof (translation)
Introduce `q A B _ _ n i`. Establish `h2` using `GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective (ZMod q) _ _ (GlobalTheory.T.etaleSheafSections_specProd_bijective (ZMod q) A B)`. Establish `h3` using `GlobalTheory.T.etaleChains_disc_biprod_desc_isIso (ZMod q) _ _ h2`. Establish `hc` using `@cpull_bijective_of_isIso _ _ _ _ _ h3 (res (ZMod q) (tw q i)) n`. Use `(cpull_biprod_bijective (ZMod q) _ _ (res (ZMod q) (tw q i)) n).comp hc` as an intermediate fact.

Use `bij_of_eq (fun x => ?_) this` and prove the remaining obligations. Simplify using `only [Function.comp]`. Use `erw [BiprodCls.cpull_cpull, BiprodCls.cpull_cpull, biprod.inl_desc, biprod.inr_desc]`. Both sides reduce to the same expression.
-/
theorem ht_prod_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ),
    Function.Bijective (fun x : Ht q (sp (A × B)) n i =>
      (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective (ZMod q) _ _ (GlobalTheory.T.etaleSheafSections_specProd_bijective (ZMod q) A B)
  have h3 := GlobalTheory.T.etaleChains_disc_biprod_desc_isIso (ZMod q) _ _ h2
  have hc := @cpull_bijective_of_isIso _ _ _ _ _ h3 (res (ZMod q) (tw q i)) n
  have := (cpull_biprod_bijective (ZMod q) _ _ (res (ZMod q) (tw q i)) n).comp hc
  refine bij_of_eq (fun x => ?_) this
  dsimp only [Function.comp]
  erw [BiprodCls.cpull_cpull, BiprodCls.cpull_cpull, biprod.inl_desc, biprod.inr_desc]
  rfl

end GlobalTheory.EtC.ProdCoh
