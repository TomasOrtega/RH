import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open RingTheory.Sequence in

/- English proof (translation)
Introduce `O _ g`. Proceed by induction on `g with`. Consider the case `zero`. Introduce `f _ a _`. Conclude with `⟨0, by simp, by simp, funext fun i => i.elim0⟩`.

Consider the case `succ g ih`. Introduce `f hf a ha`. Establish `hsplit : List.ofFn f = List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)]`. Rewrite using `[List.ofFn_succ_last]`. Rewrite `hf` using `[hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff]`.

Take `⟨hf1, hf2⟩` from `hf`. Rewrite `ha` using `[Fin.sum_univ_castSucc]`. Establish `hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) = Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc)`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Establish `hmem : a (Fin.last g) ∈ (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O)`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Apply `hf2` to reduce the goal to its premises. Simplify using `only [smul_zero]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm, eq_neg_of_add_eq_zero_right ha, neg_mem_iff]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`.

Rewrite `hmem` using `[hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc} = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn], Ideal.mem_span_range_iff_exists_fun]`. Take `⟨b, hb⟩` from `hmem`. Take `⟨c', hc0, hcs, hca⟩` from `ih (fun i => f i.castSucc) hf1 (fun i => a i.castSucc + b i * f (Fin.last g)) (by`. Simplify using `only [add_mul, Finset.sum_add_distrib]`. Rewrite using `[← ha, ← hb, Finset.sum_mul, add_right_inj]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring)`. Use `⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j) (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Consider the cases of `i using Fin.lastCases with`. Consider the case `last => simp`.

Consider the case `cast i => simp [hc0]`. Introduce `i j`. Apply the tactic sequence `cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _`. Use function extensionality and compare the values at `i`. Consider the cases of `i using Fin.lastCases with`.

Consider the case `last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]`. Consider the case `cast i`. Use `congrFun hca i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last]`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weaklyRegular_relations_koszul :
    ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  intro O _ g
  induction g with
  | zero =>
    intro f _ a _
    exact ⟨0, by simp, by simp, funext fun i => i.elim0⟩
  | succ g ih =>
    intro f hf a ha
    have hsplit : List.ofFn f =
        List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)] := by
      rw [List.ofFn_succ_last]
    rw [hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Fin.sum_univ_castSucc] at ha
    have hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) =
        Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) := by
      rw [smul_eq_mul, Ideal.mul_top]
    have hmem : a (Fin.last g) ∈
        (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hf2
      simp only [smul_zero]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm,
        eq_neg_of_add_eq_zero_right ha, neg_mem_iff]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    rw [hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc}
        = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn],
      Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c', hc0, hcs, hca⟩ := ih (fun i => f i.castSucc) hf1
      (fun i => a i.castSucc + b i * f (Fin.last g)) (by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb, Finset.sum_mul, add_right_inj]
        exact Finset.sum_congr rfl fun i _ => by ring)
    refine ⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j)
      (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp [hc0]
    · intro i j
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _
    · funext i
      cases i using Fin.lastCases with
      | last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]
      | cast i =>
        have := congrFun hca i
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        rw [← this]
        ring

end GlobalTheory
