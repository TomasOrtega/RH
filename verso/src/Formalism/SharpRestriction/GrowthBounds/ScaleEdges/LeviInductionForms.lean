import Formalism.SharpRestriction.GrowthBounds.PathWeight.Lemma4OfRemainingStatements
import Formalism.SharpRestriction.GrowthBounds.PathWeight.MdWeightMapDomain
import Formalism.SharpRestriction.GrowthBounds.PathWeight.LeadingDepthOneMemClosure
import Formalism.SharpRestriction.GrowthBounds.PathWeight.CoeUntopDLeAlt
import Formalism.SharpRestriction.GrowthBounds.PathWeight.LetterWeightPos
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableBound

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section XX

variable {O : Type} [CommRing O] [IsDomain O] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ)

/- English proof (translation)
Unfold `XX'`. Apply `inf_le_inf_right` to reduce the goal to its premises. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `P ⟨A, G, M, hA, hG, hc, rfl⟩`. Use `⟨A, G, M, hA, hG, fun x hx hW => ?_, rfl⟩` and prove the remaining obligations.

Take `⟨h1, h2, h3⟩` from `hc x hx hW`. Establish `key : ∀ v : WithTop ℤ, ((M x + mg x : ℤ) : WithTop ℤ) ≤ v → ((M x + 0 : ℤ) : WithTop ℤ) ≤ v` using `fun v hv => le_trans (WithTop.coe_le_coe.mpr (by linarith [hmg x])) hv`. Conclude with `⟨fun he => ⟨(h1 he).1, key _ (h1 he).2⟩, fun he => ⟨(h2 he).1, key _ (h2 he).2⟩, h3⟩`.
-/
theorem xx_mono (mg : ℤ → ℤ) (th o : ℤ → ℝ) (hmg : ∀ x, 0 ≤ mg x) :
    XX' O r K F j mg th o ≤ XX' O r K F j (fun _ => 0) th o := by
  unfold XX'
  apply inf_le_inf_right
  apply Submodule.span_mono
  rintro P ⟨A, G, M, hA, hG, hc, rfl⟩
  refine ⟨A, G, M, hA, hG, fun x hx hW => ?_, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hc x hx hW
  have key : ∀ v : WithTop ℤ, ((M x + mg x : ℤ) : WithTop ℤ) ≤ v → ((M x + 0 : ℤ) : WithTop ℤ) ≤ v :=
    fun v hv => le_trans (WithTop.coe_le_coe.mpr (by linarith [hmg x])) hv
  exact ⟨fun he => ⟨(h1 he).1, key _ (h1 he).2⟩, fun he => ⟨(h2 he).1, key _ (h2 he).2⟩, h3⟩

def segW : ℤ × Fin (r + K) → (ℤ → ℕ) := fun v => Pi.single v.1 1

end XX

section Comp

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  {w : O} {Fr : Frames n' r} {Q : ℕ} {g : Matrix (Fin k) (Fin k) (WF p n')}

local notation "PP" => MvPolynomial (TV n' k) (KK O)

/- English proof (translation)
Proceed by induction on `hZ using AddSubmonoid.closure_induction with`. Consider the case `mem P hP`. Take `⟨o', hS⟩` from `hP`. Establish `hh : IsWeightedHomogeneous (normalVariableWeight n' k r) P o'` using `(hom_iff P o').mp hS.1`. Establish `hm : IsWeightedHomogeneous (normalVariableWeight n' k r) (P * H0) o'` using `by simpa using hh.mul hH0`.

Distinguish the cases in `he : o = o'`. Substitute `he` using the available equality. Conclude with `⟨P, SyS_of_Sy hS, hm.weightedHomogeneousComponent_same⟩`. Conclude with `⟨0, zero_mem _, by rw [hm.weightedHomogeneousComponent_ne o he, zero_mul]⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨Za, hZa, ea⟩` from `ha`. Take `⟨Zb, hZb, eb⟩` from `hb`. Conclude with `⟨Za + Zb, add_mem hZa hZb, by rw [add_mul, map_add, ea, eb, add_mul]⟩`.
-/
theorem SyS_compZ {H0 : PP} (hH0 : IsWeightedHomogeneous (normalVariableWeight n' k r) H0 0) {Z : PP} (hZ : Z ∈ SyS w Fr Q g) (o : ℕ) :
    ∃ FinalForm ∈ SyS w Fr Q g, weightedHomogeneousComponent (normalVariableWeight n' k r) o (Z * H0) = FinalForm * H0 := by
  induction hZ using AddSubmonoid.closure_induction with
  | mem P hP =>
    obtain ⟨o', hS⟩ := hP
    have hh : IsWeightedHomogeneous (normalVariableWeight n' k r) P o' := (hom_iff P o').mp hS.1
    have hm : IsWeightedHomogeneous (normalVariableWeight n' k r) (P * H0) o' := by simpa using hh.mul hH0
    by_cases he : o = o'
    · subst he
      exact ⟨P, SyS_of_Sy hS, hm.weightedHomogeneousComponent_same⟩
    · exact ⟨0, zero_mem _, by rw [hm.weightedHomogeneousComponent_ne o he, zero_mul]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨Za, hZa, ea⟩ := ha
    obtain ⟨Zb, hZb, eb⟩ := hb
    exact ⟨Za + Zb, add_mem hZa hZb, by rw [add_mul, map_add, ea, eb, add_mul]⟩

end Comp

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_weightedHomogeneousComponent]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hd`.

Both sides reduce to the same expression. Use `symm`. Assume the negation of the conclusion as `hne`. Conclude with `hd (Finset.mem_range.mpr (Nat.lt_succ_of_le (h d (mem_support_iff.mpr hne))))`.
-/
theorem sum_comp_range {R σ : Type*} [CommSemiring R] (wt : σ → ℕ) (φ : MvPolynomial σ R) (T : ℕ)
    (h : ∀ m ∈ φ.support, Finsupp.weight wt m ≤ T) :
    ∑ o ∈ Finset.range (T + 1), weightedHomogeneousComponent wt o φ = φ := by
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with hd
  · rfl
  · symm
    by_contra hne
    exact hd (Finset.mem_range.mpr (Nat.lt_succ_of_le (h d (mem_support_iff.mpr hne))))

/- English proof (translation)
Unfold `normDeg vsDeg`. Rewrite using `[Finset.sum_subset (Finset.subset_univ m.support) (fun v _ hv => by simp [Finsupp.notMem_support_iff.mp hv])]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_add]`.

Distinguish the cases in `ht : Even t.val`. Simplify using `only [IsNormal, ht, if_true]`. Simplify using the standard rewrite rules. Simplify using `only [IsNormal, ht, if_false]`. Simplify using the standard rewrite rules.
-/
theorem normDeg_eq_vsDeg {n' r K : ℕ} (m : Fin n' × Fin (r + K) →₀ ℕ) : normDeg r m = vsDeg m := by
  unfold normDeg vsDeg
  rw [Finset.sum_subset (Finset.subset_univ m.support)
    (fun v _ hv => by simp [Finsupp.notMem_support_iff.mp hv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_add]
  by_cases ht : Even t.val
  · simp only [IsNormal, ht, if_true]
    simp
  · simp only [IsNormal, ht, if_false]
    simp

end Formalism.MainNotions.Pf14
