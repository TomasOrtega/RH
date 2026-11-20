import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSchemeRepresentingEtaleLevelsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}

/- English proof (translation)
Simplify using `only [IsEtLevOver, wSub, pow_one]`.
-/
private theorem isEtLevOver_iff_pow (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : IsEtLevOver o 𝔞 r l ↔ IsEtLevOver o (𝔞 ^ r) 1 l := by
  simp only [IsEtLevOver, wSub, pow_one]

/- English proof (translation)
Unfold `RepLev`. Simplify using `only [isEtLevOver_iff_pow o 𝔞 r]`.
-/
private theorem repLev_iff_pow (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) :
    RepLev o 𝔞 r ↔ RepLev o (𝔞 ^ r) 1 := by
  unfold RepLev
  simp only [isEtLevOver_iff_pow o 𝔞 r]

/- English proof (translation)
Use `Submodule.subset_span ⟨1, by simp, z, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem mem_wSub_top (z : D.La) : z ∈ wSub D ⊤ 1 := by
  refine Submodule.subset_span ⟨1, by simp, z, ?_⟩
  simp

/- English proof (translation)
Use `⟨S, 𝟙 S, fun _ => 1, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun _ _ => (mul_one 1).symm, fun c _ => ?_, fun _ _ => by rfl, fun k _ _ x => ⟨fun y _ => mem_wSub_top y, fun g hg => ⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Use `haveI := o.act.hom c`. Conclude with `(MonObj.one_comp _).symm`. Establish `h1` using `hg 1 (by simp)`.

Rewrite `h1` using `[map_one, o.act.one, Category.comp_id]`. Rewrite using `[h1, MonObj.comp_one]`. Introduce `T l hl`. Use `⟨Over.mkIdTerminal.from T, fun y => ?_, fun f _ => Over.mkIdTerminal.hom_ext _ _⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_one, hl.2.2.1 y (mem_wSub_top y)]`.
-/
private theorem repLev_top (o : Obj b N s) : RepLev o ⊤ 1 := by
  refine ⟨S, 𝟙 S, fun _ => 1, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨fun _ _ => (mul_one 1).symm, fun c _ => ?_, fun _ _ => by rfl, fun k _ _ x => ⟨fun y _ => mem_wSub_top y, fun g hg => ⟨0, ?_⟩⟩⟩
    · haveI := o.act.hom c
      exact (MonObj.one_comp _).symm
    · have h1 := hg 1 (by simp)
      rw [map_one, o.act.one, Category.comp_id] at h1
      rw [h1, MonObj.comp_one]
  · intro T l hl
    refine ⟨Over.mkIdTerminal.from T, fun y => ?_, fun f _ => Over.mkIdTerminal.hom_ext _ _⟩
    rw [MonObj.comp_one, hl.2.2.1 y (mem_wSub_top y)]

/- English proof (translation)
Introduce `hI hM p _ D R _ b N 𝔞 r hN h𝔞 S _ s o`. Establish `key : ∀ k, RepLev o 𝔞 k`. Use `hI (𝓞 D.F) (fun w => IsEtPlace b w) (fun 𝔟 => ∀ k, RepLev o 𝔟 k) ?_ ?_ ?_ 𝔞 h𝔞.1 h𝔞.2` and prove the remaining obligations. Introduce `k`. Rewrite using `[repLev_iff_pow, Ideal.top_pow]`.

Conclude with `repLev_top o`. Introduce `w j _ hQ k`. Rewrite using `[repLev_iff_pow, ← pow_mul]`. Conclude with `(repLev_iff_pow o w (j * k)).mp (GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels p D R b N w (j * k) hN hQ S s o)`. Introduce `𝔞' 𝔟 hcop h1 h2 k`.

Rewrite using `[repLev_iff_pow, mul_pow]`. Use `hM p D R b N S s o (𝔞' ^ k) (𝔟 ^ k) ?_ ((repLev_iff_pow o 𝔞' k).mp (h1 k)) ((repLev_iff_pow o 𝔟 k).mp (h2 k))` and prove the remaining obligations. Conclude with `Ideal.pow_sup_eq_top (Ideal.sup_pow_eq_top hcop)`. Conclude with `key r`.
-/
theorem repAll_holds : IdealInd → RepMul → RepAll := by
  intro hI hM p _ D R _ b N 𝔞 r hN h𝔞 S _ s o
  have key : ∀ k, RepLev o 𝔞 k := by
    refine hI (𝓞 D.F) (fun w => IsEtPlace b w) (fun 𝔟 => ∀ k, RepLev o 𝔟 k) ?_ ?_ ?_ 𝔞 h𝔞.1 h𝔞.2
    · intro k
      rw [repLev_iff_pow, Ideal.top_pow]
      exact repLev_top o
    · intro w j _ hQ k
      rw [repLev_iff_pow, ← pow_mul]
      exact (repLev_iff_pow o w (j * k)).mp (GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels p D R b N w (j * k) hN hQ S s o)
    · intro 𝔞' 𝔟 hcop h1 h2 k
      rw [repLev_iff_pow, mul_pow]
      refine hM p D R b N S s o (𝔞' ^ k) (𝔟 ^ k) ?_
        ((repLev_iff_pow o 𝔞' k).mp (h1 k)) ((repLev_iff_pow o 𝔟 k).mp (h2 k))
      exact Ideal.pow_sup_eq_top (Ideal.sup_pow_eq_top hcop)
  exact key r

end UpperTheory.Gal.FiniteEtaleModels
