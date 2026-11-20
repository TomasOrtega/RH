import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.TorsList

/- English proof (translation)
Extract witnesses or component facts from the available result. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem card_torsion_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {g : ℕ} {K : Type} [Field K]
    {x : Sp K ⟶ S} (hx : PolFib G L g x) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K) {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card {p : Over.mk (t ≫ x) ⟶ G // p ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨P, α, hg, h, -⟩ := hx
  subst hg
  rw [← GlobalTheory.TorsionCover.card_torsion P.A P.isAb P.smoothDim t hn]
  let Φ := GlobalTheory.ObjPull.pushEquiv h (Over.mk t)
  exact (Nat.card_congr (Φ.toEquiv.subtypeEquiv fun y => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  intro S G _ _ L g m K _ _ x hm hx
  have hpow : (m ^ 2) ^ (2 * g) = m ^ (4 * g) := by rw [← pow_mul]; congr 1; ring
  have hm2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hc : Nat.card {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} = m ^ (4 * g) := by
    have := card_torsion_comp G L hx (𝟙 (Sp K)) hm2
    rw [Category.id_comp, hpow] at this
    exact this
  have hfin : Finite {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hm0)
  let e := Finite.equivFinOfCardEq hc
  refine ⟨fun a => (e.symm a).1, fun a b hab => e.symm.injective (Subtype.ext hab), fun a => (e.symm a).2, ?_⟩
  intro K' _ _ i p hp
  have hm' : ((m ^ 2 : ℕ) : K') ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hm2
  have hc' := card_torsion_comp G L hx (spMap i) hm'
  rw [hpow] at hc'
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hepi : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  let F : {q : Over.mk x ⟶ G // q ^ (m ^ 2) = 1} → {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    fun q => ⟨preHom u q.1, by rw [← map_pow, q.2, map_one]⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h1 : spMap i ≫ a.1.left = spMap i ≫ b.1.left := congrArg (fun z => (Subtype.val z).left) hab
    exact (cancel_epi (spMap i)).1 h1
  have hfin' : Finite {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ hm0)
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hF, by rw [hc, hc']⟩).2 ⟨p, hp⟩
  refine ⟨e q, ?_⟩
  show p.left = spMap i ≫ (e.symm (e q)).1.left
  rw [Equiv.symm_apply_apply]
  exact (congrArg (fun z => (Subtype.val z).left) hq).symm

end GlobalTheory.UMin.TorsList
