import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

open ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncLocal

/- English proof (translation)
Use `⟨⟨hC.1 i, hC.2.1 ▸ Set.subset_iUnion (fun j => (C j : Set X)) i⟩, fun D hD hiD => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hDz⟩` from `(isIrreducible_iff_sUnion_isClosed.1 hD.1) (Finset.univ.image fun j => (C j : Set X)) (fun z hz => by`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hz`. Conclude with `(C j).isClosed)`. Use the proof step `(by`.

Use `hD.2.trans (hC.2.1 ▸ Set.iUnion_subset fun j => ?_)` and prove the remaining obligations. Conclude with `Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hz`. Establish `hij : i = j` using `hC.2.2 i j (hiD.trans hDz)`. Substitute `hij` using the available equality.

Conclude with `hDz`.
-/
theorem mem_comps_of_compList {X : Scheme.{0}} {B : Set X} {m : ℕ} {C : Fin m → Closeds X}
    (hC : FinalTheorems.CompList B C) (i : Fin m) : (C i : Set X) ∈ ReciprocityTheory.AnForm.R.comps B := by
  classical
  refine ⟨⟨hC.1 i, hC.2.1 ▸ Set.subset_iUnion (fun j => (C j : Set X)) i⟩, fun D hD hiD => ?_⟩
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hD.1)
    (Finset.univ.image fun j => (C j : Set X))
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C j).isClosed)
    (by
      refine hD.2.trans (hC.2.1 ▸ Set.iUnion_subset fun j => ?_)
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  have hij : i = j := hC.2.2 i j (hiD.trans hDz)
  subst hij
  exact hDz

/- English proof (translation)
Take `⟨hreg, U, hx, n, f, J, hrsp, hZU⟩` from `hB x`. Use `haveI := hreg`. Establish `hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) = B` using `by simp`. Take `⟨O, hxO, -, hO⟩` from `exists_open_comps x U hx f J hrsp hZU`. Establish `key : ∀ i : {i : Fin m // x ∈ C i}, ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i.1) ∧ stalkId (Scheme.IdealSheafData.vanishingIdeal (C i.1)) x = Ideal.span {X.presheaf.germ U.1 x hx (f j)}`.

Introduce and unpack `⟨i, hxi⟩`. Establish `hCi : ((C i : Closeds X) : Set X) ∈ ReciprocityTheory.AnForm.R.comps ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X)` using `hs ▸ mem_comps_of_compList hC i`. Establish `hO'` using `hO _ hCi`. Establish `hq : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ (C i : Set X) ↔ ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i) ∧ X.presheaf.germ U.1 x hx (f j) ∈ q.asIdeal`. Introduce `q`.

Establish `hqO : X.fromSpecStalk x q ∈ (O : Set X)`. Establish `h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x)` using `⟨q, rfl⟩`. Rewrite `h` using `[Scheme.range_fromSpecStalk]`. Conclude with `Specializes.mem_open h O.isOpen hxO`. Establish `h` using `Set.ext_iff.1 hO' (X.fromSpecStalk x q)`.

Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and, GlobalTheory.SncComponents.fromSpecStalk_mem_zeroLocus_iff U x hx] at h`. Conclude with `h`. Take `⟨j, hj, hbj, -⟩` from `(hq (IsLocalRing.closedPoint _)).1 (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxi)`. Use `⟨j, hj, hbj, ?_⟩` and prove the remaining obligations. Establish `hCC : (C i).compl.compl = C i` using `SetLike.coe_injective (compl_compl _)`.

Establish `hp : Prime (X.presheaf.germ U.1 x hx (f j))` using `prime_of_regular_params (fun i => X.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 j`. Establish `h` using `GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl (C i).compl x (X.presheaf.germ U.1 x hx (f j)) fun q => by`. Use `not_congr ((hq q).trans ⟨?_, fun h => ⟨j, hj, hbj, h⟩⟩)` and prove the remaining obligations. Introduce and unpack `⟨k, hk, hbk, h⟩`. Distinguish the cases in `hjk : j = k`.

Conclude with `hjk ▸ h`. Conclude with `absurd rfl (branch_ne x U hx f J hrsp hZU hj hk hjk hbj hbk)`. Rewrite `h` using `[hCC]`. Rewrite using `[h]`. Conclude with `((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical`.

Use `choose g hgJ hgb hgs using key`. Use `⟨hreg, n, fun k => X.presheaf.germ U.1 x hx (f k), ⟨g, fun a b hab => ?_⟩, hrsp, hgs⟩` and prove the remaining obligations. Establish `h1` using `hgb a`. Rewrite `h1` using `[hab]`. Take `⟨D, -, hD⟩` from `existsUnique_branch x U hx f J hrsp hZU (g b) (hgJ b)`.

Establish `e : (C a.1 : Set X) = C b.1` using `(hD _ h1).trans (hD _ (hgb b)).symm`. Conclude with `Subtype.ext (hC.2.2 _ _ e.le)`.
-/
theorem lSncAt_of_snc (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X)
    (hB : Snc (Scheme.IdealSheafData.vanishingIdeal B)) (hC : CompList (B : Set X) C) (x : X) :
    LSncAt X C x := by
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hB x
  haveI := hreg
  have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) = B := by simp
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have key : ∀ i : {i : Fin m // x ∈ C i}, ∃ j ∈ J,
      ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i.1) ∧
      stalkId (Scheme.IdealSheafData.vanishingIdeal (C i.1)) x =
        Ideal.span {X.presheaf.germ U.1 x hx (f j)} := by
    rintro ⟨i, hxi⟩
    have hCi : ((C i : Closeds X) : Set X) ∈
        ReciprocityTheory.AnForm.R.comps ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) :=
      hs ▸ mem_comps_of_compList hC i
    have hO' := hO _ hCi
    have hq : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ (C i : Set X) ↔
        ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X)
          (f j) x (C i) ∧ X.presheaf.germ U.1 x hx (f j) ∈ q.asIdeal := by
      intro q
      have hqO : X.fromSpecStalk x q ∈ (O : Set X) := by
        have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
        rw [Scheme.range_fromSpecStalk] at h
        exact Specializes.mem_open h O.isOpen hxO
      have h := Set.ext_iff.1 hO' (X.fromSpecStalk x q)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
        GlobalTheory.SncComponents.fromSpecStalk_mem_zeroLocus_iff U x hx] at h
      exact h
    obtain ⟨j, hj, hbj, -⟩ := (hq (IsLocalRing.closedPoint _)).1
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxi)
    refine ⟨j, hj, hbj, ?_⟩
    have hCC : (C i).compl.compl = C i := SetLike.coe_injective (compl_compl _)
    have hp : Prime (X.presheaf.germ U.1 x hx (f j)) :=
      prime_of_regular_params (fun i => X.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 j
    have h := GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl (C i).compl x
      (X.presheaf.germ U.1 x hx (f j)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨j, hj, hbj, h⟩⟩)
        rintro ⟨k, hk, hbk, h⟩
        by_cases hjk : j = k
        · exact hjk ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hj hk hjk hbj hbk)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  choose g hgJ hgb hgs using key
  refine ⟨hreg, n, fun k => X.presheaf.germ U.1 x hx (f k), ⟨g, fun a b hab => ?_⟩, hrsp, hgs⟩
  have h1 := hgb a
  rw [hab] at h1
  obtain ⟨D, -, hD⟩ := existsUnique_branch x U hx f J hrsp hZU (g b) (hgJ b)
  have e : (C a.1 : Set X) = C b.1 := (hD _ h1).trans (hD _ (hgb b)).symm
  exact Subtype.ext (hC.2.2 _ _ e.le)

/- English proof (translation)
Introduce `X _ B m C hB hC x` and use `lSncAt_of_snc X B m C hB hC x`.
-/
theorem lSncAt_of_snc' : ∀ (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X), Snc (Scheme.IdealSheafData.vanishingIdeal B) → CompList (B : Set X) C → ∀ x : X, LSncAt X C x :=
  fun X _ B m C hB hC x => lSncAt_of_snc X B m C hB hC x

end GlobalTheory.SncLocal
