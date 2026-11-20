import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Rewrite `hx` using `[wSub]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c, hc, z', rfl⟩` from `hz`. Rewrite using `[smul_smul, ← map_mul]`.

Use `Submodule.subset_span ⟨e * c, ?_, z', rfl⟩` and prove the remaining obligations. Rewrite `hc`, the goal using `[pow_one]`. Rewrite using `[mul_comm]`. Conclude with `Ideal.mul_mem_mul he hc`. Consider the case `zero => rw [smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[smul_smul, Algebra.commutes, mul_smul]`.

Conclude with `Submodule.smul_mem _ c ha`.
-/
private lemma smul_mem_prod {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {𝔞 𝔟 : Ideal (𝓞 D.F)}
    {e : 𝓞 D.F} (he : e ∈ 𝔟) {x : D.La} (hx : x ∈ wSub D 𝔞 1) :
    algebraMap (𝓞 D.F) D.O e • x ∈ wSub D (𝔞 * 𝔟) 1 := by
  rw [wSub] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [smul_smul, ← map_mul]
    refine Submodule.subset_span ⟨e * c, ?_, z', rfl⟩
    rw [pow_one] at hc ⊢
    rw [mul_comm]
    exact Ideal.mul_mem_mul he hc
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_smul, Algebra.commutes, mul_smul]
    exact Submodule.smul_mem _ c ha

/- English proof (translation)
The claim follows from `Ideal.mul_le_left h`.
-/
private lemma mem_of_mem_mul {A : Type} [CommRing A] {I J : Ideal A} {c : A} (h : c ∈ I * J) : c ∈ I :=
  Ideal.mul_le_left h

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `z ⟨c, hc, z', rfl⟩`. Rewrite `hc` using `[pow_one]`. Conclude with `⟨c, by rw [pow_one]; exact mem_of_mem_mul hc, z', rfl⟩`.
-/
private lemma wSub_mul_le {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (𝔞 𝔟 : Ideal (𝓞 D.F)) :
    wSub D (𝔞 * 𝔟) 1 ≤ wSub D 𝔞 1 := by
  refine Submodule.span_mono ?_
  rintro z ⟨c, hc, z', rfl⟩
  rw [pow_one] at hc
  exact ⟨c, by rw [pow_one]; exact mem_of_mem_mul hc, z', rfl⟩

/- English proof (translation)
Introduce `p _ D R _ b N S s o 𝔞 𝔟 e he he' T l h`. Take `⟨h1, h2, h3, h4⟩` from `h`. Establish `hcomm : ∀ (c : D.O) (x : D.La), algebraMap (𝓞 D.F) D.O e • c • x = c • algebraMap (𝓞 D.F) D.O e • x` using `fun c x => by`. Rewrite using `[smul_smul, Algebra.commutes, mul_smul]`. Establish `he1 : 1 - e ∈ 𝔞 ^ 1` using `by rwa [pow_one]`.

Unfold `IsEtLevOver`. Use `beta_reduce`. Use `⟨fun x y => ?_, fun c x => ?_, fun x hx => h3 _ (smul_mem_prod he hx), fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[smul_add, h1]`. Rewrite using `[hcomm, h2]`.

Establish `hE` using `wSub_mul_le D 𝔞 𝔟 ((h4 k x).1 _ hy)`. Establish `hy' : y = algebraMap (𝓞 D.F) D.O (1 - e) • y + algebraMap (𝓞 D.F) D.O e • y`. Rewrite using `[← add_smul, ← map_add, sub_add_cancel, map_one, one_smul]`. Rewrite using `[hy']`. Conclude with `Submodule.add_mem _ (Submodule.subset_span ⟨1 - e, he1, y, rfl⟩) hE`.

Take `⟨y, hy⟩` from `(h4 k x).2 g (fun c hc => hg c (by`. Rewrite `hc`, the goal using `[pow_one]`. Conclude with `mem_of_mem_mul hc))`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ← Category.assoc, hy]`.

Establish `key : g = (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e))) * (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O e))`. Rewrite using `[← MonObj.comp_mul, ← o.act.add, ← map_add, sub_add_cancel, map_one, o.act.one, Category.comp_id]`. Rewrite `key` using `[hg (1 - e) he1, _root_.one_mul]`. Conclude with `key.symm`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.crtProj_holds :
    CrtProj := by
  intro p _ D R _ b N S s o 𝔞 𝔟 e he he' T l h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcomm : ∀ (c : D.O) (x : D.La), algebraMap (𝓞 D.F) D.O e • c • x =
      c • algebraMap (𝓞 D.F) D.O e • x := fun c x => by
    rw [smul_smul, Algebra.commutes, mul_smul]
  have he1 : 1 - e ∈ 𝔞 ^ 1 := by rwa [pow_one]
  unfold IsEtLevOver
  beta_reduce
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => h3 _ (smul_mem_prod he hx),
    fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · rw [smul_add, h1]
  · rw [hcomm, h2]
  · have hE := wSub_mul_le D 𝔞 𝔟 ((h4 k x).1 _ hy)
    have hy' : y = algebraMap (𝓞 D.F) D.O (1 - e) • y + algebraMap (𝓞 D.F) D.O e • y := by
      rw [← add_smul, ← map_add, sub_add_cancel, map_one, one_smul]
    rw [hy']
    exact Submodule.add_mem _ (Submodule.subset_span ⟨1 - e, he1, y, rfl⟩) hE
  · obtain ⟨y, hy⟩ := (h4 k x).2 g (fun c hc => hg c (by
      rw [pow_one] at hc ⊢
      exact mem_of_mem_mul hc))
    refine ⟨y, ?_⟩
    rw [h2, ← Category.assoc, hy]
    have key : g = (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e))) *
        (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O e)) := by
      rw [← MonObj.comp_mul, ← o.act.add, ← map_add, sub_add_cancel, map_one, o.act.one,
        Category.comp_id]
    rw [hg (1 - e) he1, _root_.one_mul] at key
    exact key.symm
