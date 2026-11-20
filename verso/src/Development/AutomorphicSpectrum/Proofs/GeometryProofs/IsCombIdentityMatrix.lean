import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
The claim follows from `| 0, f => by simp [M.pt_zero] | n + 1, f => by rw [List.ofFn_succ, List.prod_cons, prod_ofFn_lieModel_pt M, Fin.sum_univ_succ, M.add]`.
-/
theorem prod_ofFn_lieModel_pt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => M.pt (f j)).prod = M.pt (∑ j, f j)
  | 0, f => by simp [M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_lieModel_pt M, Fin.sum_univ_succ, M.add]

/- English proof (translation)
Introduce `S G _ _ F _ x n v hv i`. Take `⟨E, _, _, ⟨M⟩⟩` from `lieModel_exists S G F x`. Use `choose e he using fun j => M.onto (v j) (hv j)`. Use `⟨fun j => M.pt ((1 : Matrix (Fin n) (Fin n) F) i j • e j), fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[M.smul, he]`.

Rewrite using `[prod_ofFn_lieModel_pt M, ← he i]`. Use `congr 1`. Simplify using `[Matrix.one_apply, ite_smul]`.
-/
theorem isComb_unit_row : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F]
    (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) →
    ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  intro S G _ _ F _ x n v hv i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  choose e he using fun j => M.onto (v j) (hv j)
  refine ⟨fun j => M.pt ((1 : Matrix (Fin n) (Fin n) F) i j • e j), fun j => ?_, ?_⟩
  · rw [M.smul, he]
  · rw [prod_ofFn_lieModel_pt M, ← he i]
    congr 1
    simp [Matrix.one_apply, ite_smul]

end GlobalTheory.CompanionTheory.Ar.Flat
