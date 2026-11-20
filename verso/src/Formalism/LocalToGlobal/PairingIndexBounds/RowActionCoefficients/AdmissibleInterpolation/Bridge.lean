import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems Formalism.MainNotions.FormalGroupSystem.Pf

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

abbrev GlobalTheory : Type := Σ v : Fin P.nV, Fin (P.n' v)

def emP (b : GlobalTheory P) (v : Fin (P.m + 1) × Fin (P.m + 1)) :
    (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) := ⟨b.1, (b.2, v)⟩

def gam (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (b : GlobalTheory P) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf :=
  la_tw (P.ι b.1) (P.σ b.1) b.2.val (g b.1)

def nuB (b : GlobalTheory P) : Fin (P.m + 1) → ℕ := nuOf (lamAt (P.lam0 b.1) b.2)

def eB (b : GlobalTheory P) : ℤ := lamAt (P.lam0 b.1) b.2 (Fin.last P.m)

def sB (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) : Kf := ∏ b : GlobalTheory P, (gam P g b).det ^ (-(eB P b))

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem prod_blocks (c : GlobalTheory P → Kf) (F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    ∏ v, P.vEmb v (∏ s, blockEmb Kf s (c ⟨v, s⟩ • F ⟨v, s⟩)) = (∏ b, c b) • ∏ b, rename (emP P b) (F b) := by
  have e1 : ∀ (b : GlobalTheory P) (G : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf),
      P.vEmb b.1 (blockEmb Kf b.2 G) = rename (emP P b) G := by
    intro b G
    simp only [Places.vEmb, blockEmb]
    rw [rename_rename]
    rfl
  rw [show (∏ b, c b) • ∏ b, rename (emP P b) (F b) = ∏ b : GlobalTheory P, c b • rename (emP P b) (F b) by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]]
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_smul, map_smul, e1 ⟨v, s⟩]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem delta_zero_eq_twisted_delta (hinj : Function.Injective (algebraMap O Kf)) (v : Fin P.nV) (s : Fin (P.n' v))
    (g : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : IsUnit g.det) :
    Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) =
      deltaLTw O Kf P.m (lamAt (P.lam0 v) s) (la_tw (P.ι v) (P.σ v) s.val g) := by
  have hd : Antitone (lamAt (P.lam0 v) s) := by
    unfold lamAt
    split_ifs
    · exact P.dom v s
    · intro i j hij
      exact neg_le_neg (P.dom v s (Fin.rev_le_rev.2 hij))
  rw [la_extO (P.ι v) (P.σ v) (P.j v)
    (fun x => by obtain ⟨y, hy⟩ := (P.setting v).frob x; exact ⟨_, hy⟩) (P.setting v).ι_comp s.val g]
  have hg' := la_tw_det (P.ι v) (P.σ v) s.val g hg
  refine le_antisymm (lowest_invariant_le_delta _ _ hd _ hg') ?_
  unfold Dl0
  rw [if_pos hd]
  refine le_iInf₂ fun h hh => ?_
  exact dl_indep O Kf hinj _ _ _ h hg' hh.2

variable (g : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hg : ∀ v, IsUnit (g v).det)

include hg in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem htupW_le (hinj : Function.Injective (algebraMap O Kf)) (T : Submodule O P.Xsp)
    (hT : ∀ F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
      (∀ b, F b ∈ deltaL O Kf (P.m + 1) (nuB P b) (gam P g b)) → sB P g • ∏ b, rename (emP P b) (F b) ∈ T) :
    P.HtupW (fun v => colSpan (P.W v) (g v)) ≤ T := by
  have key : ∀ S : Fin P.nV → Set P.Xsp,
      (∀ f : Fin P.nV → P.Xsp, (∀ v, f v ∈ S v) → ∏ v, f v ∈ T) →
      ∀ f : Fin P.nV → P.Xsp, (∀ v, f v ∈ Submodule.span O (S v)) → ∏ v, f v ∈ T := by
    intro S h f hf
    classical
    suffices H : ∀ A : Finset (Fin P.nV), ∀ f : Fin P.nV → P.Xsp,
        (∀ i ∈ A, f i ∈ Submodule.span O (S i)) → (∀ i ∉ A, f i ∈ S i) → ∏ i, f i ∈ T from
      H Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro f _ h2
      exact h f (fun i => h2 i (by simp))
    · intro a A ha ih f h1 h2
      have hR : ∀ x ∈ Submodule.span O (S a), x * ∏ j ∈ Finset.univ \ {a}, f j ∈ T := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          have h3 := ih (Function.update f a y) (fun i hi => ?_) (fun i hi => ?_)
          · rwa [Finset.prod_update_of_mem (Finset.mem_univ a)] at h3
          · have hia : i ≠ a := by rintro rfl; exact ha hi
            simp only [Function.update_apply, hia, if_false]
            exact h1 i (Finset.mem_insert_of_mem hi)
          · by_cases hia : i = a
            · subst hia
              simp only [Function.update_apply, if_true]
              exact hy
            · simp only [Function.update_apply, hia, if_false]
              exact h2 i (by simp [hia, hi])
        | zero => rw [zero_mul]; exact T.zero_mem
        | add x y _ _ hx hy => rw [add_mul]; exact T.add_mem hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact T.smul_mem c hx
      have h4 := Finset.prod_update_of_mem (Finset.mem_univ a) f (f a)
      rw [Function.update_eq_self] at h4
      rw [h4]
      exact hR _ (h1 a (Finset.mem_insert_self a A))
  unfold Places.HtupW Places.tenV
  rw [Submodule.span_le]
  rintro X ⟨F, hF, rfl⟩
  have hF' : ∀ v, P.vEmb v (F v) ∈ Submodule.span O
      (((P.vEmb v).toLinearMap.restrictScalars O) '' {Q | ∃ G : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf,
        (∀ s, G s ∈ deltaLTw O Kf P.m (lamAt (P.lam0 v) s) (la_tw (P.ι v) (P.σ v) s.val (g v))) ∧
          Q = ∏ s, blockEmb Kf s (G s)}) := by
    intro v
    rw [Submodule.span_image]
    refine Submodule.mem_map_of_mem ?_
    have h := hF v
    unfold HtenW tensorLat at h
    simp only [delta_zero_eq_twisted_delta P hinj v _ (g v) (hg v)] at h
    exact h
  refine key _ ?_ (fun v => P.vEmb v (F v)) hF'
  intro f hf
  choose Q hQ hfQ using hf
  choose G hG hQG using hQ
  have hG' : ∀ v s, ∃ H, H ∈ deltaL O Kf (P.m + 1) (nuB P ⟨v, s⟩) (gam P g ⟨v, s⟩) ∧
      (gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • H = G v s := fun v s => Submodule.mem_map.1 (hG v s)
  choose H hH hHG using hG'
  have e : ∏ v, f v = sB P g • ∏ b : GlobalTheory P, rename (emP P b) (H b.1 b.2) := by
    rw [show sB P g • ∏ b : GlobalTheory P, rename (emP P b) (H b.1 b.2) = _ from
      (prod_blocks P (fun b => (gam P g b).det ^ (-(eB P b))) (fun b => H b.1 b.2)).symm]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← hfQ v, hQG v]
    show P.vEmb v _ = _
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← hHG v s]
  rw [e]
  exact hT (fun b => H b.1 b.2) (fun b => hH b.1 b.2)

include hg in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_htupW (hinj : Function.Injective (algebraMap O Kf)) (F : GlobalTheory P → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (hF : ∀ b, F b ∈ deltaL O Kf (P.m + 1) (nuB P b) (gam P g b)) :
    sB P g • ∏ b, rename (emP P b) (F b) ∈ P.HtupW (fun v => colSpan (P.W v) (g v)) := by
  rw [show sB P g • ∏ b, rename (emP P b) (F b) = _ from
    (prod_blocks P (fun b => (gam P g b).det ^ (-(eB P b))) F).symm]
  unfold Places.HtupW Places.tenV
  apply Submodule.subset_span
  refine ⟨fun v => ∏ s, blockEmb Kf s ((gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • F ⟨v, s⟩), fun v => ?_, rfl⟩
  unfold HtenW tensorLat
  apply Submodule.subset_span
  refine ⟨fun s => (gam P g ⟨v, s⟩).det ^ (-(eB P ⟨v, s⟩)) • F ⟨v, s⟩, fun s => ?_, rfl⟩
  show _ ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) (g v)))
  rw [delta_zero_eq_twisted_delta P hinj v s (g v) (hg v)]
  exact Submodule.mem_map.2 ⟨F ⟨v, s⟩, hF ⟨v, s⟩, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
