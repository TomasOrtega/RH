import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.C2ConvergenceHypothesesNonempty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_update)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errorWithLinear)

noncomputable section

/- English proof (translation)
Establish `key : ∀ S : Finset ι, (∀ i ∈ S, i ∉ J) → regMax e (fun i => if i ∈ S then v i else u i) = regMax e u`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules.

Consider the case `insert j S hjS ih`. Introduce `hS`. Establish `hjJ : j ∉ J` using `hS j (Finset.mem_insert_self j S)`. Establish `ih'` using `ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))`. Use `set w : ι → ℝ := fun i => if i ∈ S then v i else u i with hw`.

Establish `hwJ : ∀ k ∈ J, w k = u k`. Introduce `k hk`. Establish `: k ∉ S` using `fun h => hS k (Finset.mem_insert_of_mem h) hk`. Simplify using `[hw, this]`. Establish `hwj : w j = u j` using `by simp [hw, hjS]`.

Take `⟨k1, hk1J, hk1⟩` from `hu j hjJ`. Take `⟨k2, hk2J, hk2⟩` from `hv j hjJ`. Establish `hk1j : k1 ≠ j` using `fun h => hjJ (h ▸ hk1J)`. Establish `hk2j : k2 ≠ j` using `fun h => hjJ (h ▸ hk2J)`. Establish `e1 : regMax e (Function.update w j (min (u j) (v j))) = regMax e w`.

Apply `regMax_update he w j k1 _ hk1j` to reduce the goal to its premises. Rewrite using `[hwj, hwJ k1 hk1J]`. Conclude with `hk1`. Rewrite using `[hwJ k1 hk1J]`. Combine the linear relations using `[min_le_left (u j) (v j)]`.

Establish `e2 : regMax e (Function.update (Function.update w j (min (u j) (v j))) j (v j)) = regMax e (Function.update w j (min (u j) (v j)))`. Apply `regMax_update he _ j k2 _ hk2j` to reduce the goal to its premises. Rewrite using `[Function.update_self, Function.update_of_ne hk2j, hwJ k2 hk2J]`. Combine the linear relations using `[min_le_right (u j) (v j), hJ k2 hk2J]`. Rewrite using `[Function.update_of_ne hk2j, hwJ k2 hk2J, hJ k2 hk2J]`.

Conclude with `hk2`. Establish `hfun : (fun i => if i ∈ insert j S then v i else u i) = Function.update (Function.update w j (min (u j) (v j))) j (v j)`. Use function extensionality and compare the values at `i`. Rewrite using `[Function.update_idem]`. Distinguish the cases in `hi : i = j`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hi]`. Simplify using `[hw, Finset.mem_insert, hi]`. Rewrite using `[hfun, e2, e1, ih']`.

Establish `hall` using `key (Finset.univ.filter (fun i => i ∉ J)) (fun i hi => (Finset.mem_filter.1 hi).2)`. Rewrite using `[← hall]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i ∈ J`.

Simplify using `[hi, hJ i hi]`. Simplify using `[hi]`.
-/
theorem regMax_eq_of_agree_dominated {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {e : ℝ} (he : 0 ≤ e) (J : Finset ι) (u v : ι → ℝ)
    (hJ : ∀ j ∈ J, u j = v j)
    (hu : ∀ j ∉ J, ∃ k ∈ J, u j + e ≤ u k)
    (hv : ∀ j ∉ J, ∃ k ∈ J, v j + e ≤ v k) :
    regMax e u = regMax e v := by
  have key : ∀ S : Finset ι, (∀ i ∈ S, i ∉ J) →
      regMax e (fun i => if i ∈ S then v i else u i) = regMax e u := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert j S hjS ih =>
      intro hS
      have hjJ : j ∉ J := hS j (Finset.mem_insert_self j S)
      have ih' := ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
      set w : ι → ℝ := fun i => if i ∈ S then v i else u i with hw
      have hwJ : ∀ k ∈ J, w k = u k := by
        intro k hk
        have : k ∉ S := fun h => hS k (Finset.mem_insert_of_mem h) hk
        simp [hw, this]
      have hwj : w j = u j := by simp [hw, hjS]
      obtain ⟨k1, hk1J, hk1⟩ := hu j hjJ
      obtain ⟨k2, hk2J, hk2⟩ := hv j hjJ
      have hk1j : k1 ≠ j := fun h => hjJ (h ▸ hk1J)
      have hk2j : k2 ≠ j := fun h => hjJ (h ▸ hk2J)
      have e1 : regMax e (Function.update w j (min (u j) (v j))) = regMax e w := by
        apply regMax_update he w j k1 _ hk1j
        · rw [hwj, hwJ k1 hk1J]; exact hk1
        · rw [hwJ k1 hk1J]; linarith [min_le_left (u j) (v j)]
      have e2 : regMax e (Function.update (Function.update w j (min (u j) (v j))) j (v j)) =
          regMax e (Function.update w j (min (u j) (v j))) := by
        apply regMax_update he _ j k2 _ hk2j
        · rw [Function.update_self, Function.update_of_ne hk2j, hwJ k2 hk2J]
          linarith [min_le_right (u j) (v j), hJ k2 hk2J]
        · rw [Function.update_of_ne hk2j, hwJ k2 hk2J, hJ k2 hk2J]; exact hk2
      have hfun : (fun i => if i ∈ insert j S then v i else u i) =
          Function.update (Function.update w j (min (u j) (v j))) j (v j) := by
        funext i
        rw [Function.update_idem]
        by_cases hi : i = j
        · subst hi; simp
        · rw [Function.update_of_ne hi]; simp [hw, Finset.mem_insert, hi]
      rw [hfun, e2, e1, ih']
  have hall := key (Finset.univ.filter (fun i => i ∉ J)) (fun i hi => (Finset.mem_filter.1 hi).2)
  rw [← hall]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · simp [hi, hJ i hi]
  · simp [hi]

/- English proof (translation)
Introduce `X _ _ D A R ρ Cη η hη x₀`. Establish `hV''V' : ∀ j x, x ∈ R.V'' j → x ∈ R.V' j` using `fun j x hx => ⟨hx.1, R.closure_W''_subset j (subset_closure hx.2)⟩`. Establish `hV'open : ∀ j, IsOpen (R.V' j)` using `fun j => (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)`. Use `set c : Fin R.n := (R.cover x₀).choose with hc`. Establish `hc0 : x₀ ∈ R.V'' c` using `(R.cover x₀).choose_spec`.

Establish `hK : ∀ j, ∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧ ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1` using `fun j => (hη j).2.2.2.1`. Use `choose K hKc hKW hKη using hK`. Establish `hKt : ∀ j, K j ⊆ (R.ψ j).target` using `fun j k hk => R.W_subset j (R.closure_W'_subset j (subset_closure (hKW j hk)))`. Use `set Z : Fin R.n → Set X := fun j => (R.ψ j).symm '' K j with hZ`. Establish `hZclosed : ∀ j, IsClosed (Z j)` using `fun j => ((hKc j).image_of_continuousOn ((R.ψ j).continuousOn_symm.mono (hKt j))).isClosed`.

Establish `memZ : ∀ j x, x ∈ R.V' j → R.ψ j x ∈ K j → x ∈ Z j` using `fun j x hx hk => ⟨R.ψ j x, hk, (R.ψ j).left_inv hx.1⟩`. Use `set J : Finset (Fin R.n) := Finset.univ.filter (fun j => x₀ ∈ R.V' j ∧ R.ψ j x₀ ∈ K j) with hJ`. Establish `hx0Z : ∀ j ∉ J, x₀ ∉ Z j`. Introduce and unpack `j hj ⟨k, hk, hkx⟩`. Apply `hj` to reduce the goal to its premises.

Establish `ht` using `hKt j hk`. Establish `hs : x₀ ∈ (R.ψ j).source` using `by rw [← hkx]; exact (R.ψ j).map_target ht`. Establish `he : R.ψ j x₀ = k` using `by rw [← hkx]; exact (R.ψ j).right_inv ht`. Use `Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hs, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show R.ψ j x₀ ∈ R.W' j`.

Rewrite using `[he]`. Conclude with `hKW j hk`. Rewrite using `[he]`. Conclude with `hk`. Use `set N : Set X := R.V'' c ∩ ⋂ j, (if j ∈ J then R.V' j else (Z j)ᶜ) with hN`.

Establish `hNJ : ∀ x ∈ N, ∀ j ∈ J, x ∈ R.V' j` using `fun x hx j hj => by`. Use `Set.mem_iInter.1 hx.2 j` as an intermediate fact. Rewrite `this` using `[if_pos hj]`. Then use the resulting hypothesis. Establish `hNZ : ∀ x ∈ N, ∀ j ∉ J, x ∉ Z j` using `fun x hx j hj => by`. Use `Set.mem_iInter.1 hx.2 j` as an intermediate fact.

Rewrite `this` using `[if_neg hj]`. Then use the resulting hypothesis. Establish `hNopen : IsOpen N`. Use `((R.ψ c).isOpen_inter_preimage (R.isOpen_alt_alt c)).inter (isOpen_iInter_of_finite fun j => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `hV'open j`.

Conclude with `(hZclosed j).isOpen_compl`. Establish `hx0N : x₀ ∈ N`. Use `⟨hc0, Set.mem_iInter.2 fun j => ?_⟩` and prove the remaining obligations. Use `split_ifs with hj`. Conclude with `(Finset.mem_filter.1 hj).2.1`.

Conclude with `hx0Z j hj`. Establish `inner_mem : ∀ x ∈ N, ∀ j, x ∈ R.V'' j → j ∈ J`. Introduce `x hx j hxj`. Assume the negation of the conclusion as `hj`. Establish `h1 : η j x = -1` using `hKη j x (hV''V' j x hxj) (fun hk => hNZ x hx j hj (memZ j x (hV''V' j x hxj) hk))`.

Establish `h0 : η j x = 0` using `(hη j).2.2.1 x hxj`. Rewrite `h0` using `[h1]`. Evaluate the numerical expressions using `at h0`. Establish `hcJ : c ∈ J` using `inner_mem x₀ hx0N c hc0`. Use `⟨N, J, c, hNopen, hx0N, hcJ, fun j hj x hx => hNJ x hx j hj, fun x hx => hx.1, ?_⟩` and prove the remaining obligations.

Introduce `C t he hcomp x hx`. Establish `: Nonempty (Fin R.n)` using `⟨c⟩`. Establish `hcx : x ∈ R.V'' (R.cover x).choose` using `(R.cover x).choose_spec`. Establish `hcxJ : (R.cover x).choose ∈ J` using `inner_mem x hx _ hcx`. Rewrite using `[RegCharts.glued]`.

Use `congr 1`. Use `regMax_eq_of_agree_dominated he.le J _ _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Rewrite using `[if_pos (hNJ x hx j hj), if_pos hj]`. Introduce `j hj`.

Use `⟨(R.cover x).choose, hcxJ, ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos (hNJ x hx _ hcxJ)]`. Distinguish the cases in `hxj : x ∈ R.V' j`. Rewrite using `[if_pos hxj]`. Establish `h1 : η j x = -1` using `hKη j x hxj (fun hk => hNZ x hx j hj (memZ j x hxj hk))`.

Establish `h0 : η (R.cover x).choose x = 0` using `(hη _).2.2.1 x hcx`. Establish `hcmp` using `(abs_le.1 (hcomp j (R.cover x).choose x hxj (hV''V' _ x hcx))).2`. Simplify using `only [RegCharts.regArg, h1, h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hxj]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j hj`. Use `⟨c, hcJ, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg hj, if_pos hcJ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GluedLocal.proof : GluedLocal.Statement := by
  intro X _ _ D A R ρ Cη η hη x₀
  classical
  have hV''V' : ∀ j x, x ∈ R.V'' j → x ∈ R.V' j := fun j x hx =>
    ⟨hx.1, R.closure_W''_subset j (subset_closure hx.2)⟩
  have hV'open : ∀ j, IsOpen (R.V' j) := fun j => (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)
  set c : Fin R.n := (R.cover x₀).choose with hc
  have hc0 : x₀ ∈ R.V'' c := (R.cover x₀).choose_spec
  have hK : ∀ j, ∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧
      ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1 := fun j => (hη j).2.2.2.1
  choose K hKc hKW hKη using hK
  have hKt : ∀ j, K j ⊆ (R.ψ j).target := fun j k hk =>
    R.W_subset j (R.closure_W'_subset j (subset_closure (hKW j hk)))
  set Z : Fin R.n → Set X := fun j => (R.ψ j).symm '' K j with hZ
  have hZclosed : ∀ j, IsClosed (Z j) := fun j =>
    ((hKc j).image_of_continuousOn ((R.ψ j).continuousOn_symm.mono (hKt j))).isClosed
  have memZ : ∀ j x, x ∈ R.V' j → R.ψ j x ∈ K j → x ∈ Z j := fun j x hx hk =>
    ⟨R.ψ j x, hk, (R.ψ j).left_inv hx.1⟩
  set J : Finset (Fin R.n) := Finset.univ.filter (fun j => x₀ ∈ R.V' j ∧ R.ψ j x₀ ∈ K j) with hJ
  have hx0Z : ∀ j ∉ J, x₀ ∉ Z j := by
    rintro j hj ⟨k, hk, hkx⟩
    apply hj
    have ht := hKt j hk
    have hs : x₀ ∈ (R.ψ j).source := by rw [← hkx]; exact (R.ψ j).map_target ht
    have he : R.ψ j x₀ = k := by rw [← hkx]; exact (R.ψ j).right_inv ht
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hs, ?_⟩, ?_⟩
    · show R.ψ j x₀ ∈ R.W' j
      rw [he]; exact hKW j hk
    · rw [he]; exact hk
  set N : Set X := R.V'' c ∩ ⋂ j, (if j ∈ J then R.V' j else (Z j)ᶜ) with hN
  have hNJ : ∀ x ∈ N, ∀ j ∈ J, x ∈ R.V' j := fun x hx j hj => by
    have := Set.mem_iInter.1 hx.2 j
    rwa [if_pos hj] at this
  have hNZ : ∀ x ∈ N, ∀ j ∉ J, x ∉ Z j := fun x hx j hj => by
    have := Set.mem_iInter.1 hx.2 j
    rwa [if_neg hj] at this
  have hNopen : IsOpen N := by
    refine ((R.ψ c).isOpen_inter_preimage (R.isOpen_alt_alt c)).inter (isOpen_iInter_of_finite fun j => ?_)
    split_ifs
    · exact hV'open j
    · exact (hZclosed j).isOpen_compl
  have hx0N : x₀ ∈ N := by
    refine ⟨hc0, Set.mem_iInter.2 fun j => ?_⟩
    split_ifs with hj
    · exact (Finset.mem_filter.1 hj).2.1
    · exact hx0Z j hj

  have inner_mem : ∀ x ∈ N, ∀ j, x ∈ R.V'' j → j ∈ J := by
    intro x hx j hxj
    by_contra hj
    have h1 : η j x = -1 :=
      hKη j x (hV''V' j x hxj) (fun hk => hNZ x hx j hj (memZ j x (hV''V' j x hxj) hk))
    have h0 : η j x = 0 := (hη j).2.2.1 x hxj
    rw [h1] at h0
    norm_num at h0
  have hcJ : c ∈ J := inner_mem x₀ hx0N c hc0
  refine ⟨N, J, c, hNopen, hx0N, hcJ, fun j hj x hx => hNJ x hx j hj, fun x hx => hx.1, ?_⟩
  intro C t he hcomp x hx
  have : Nonempty (Fin R.n) := ⟨c⟩
  have hcx : x ∈ R.V'' (R.cover x).choose := (R.cover x).choose_spec
  have hcxJ : (R.cover x).choose ∈ J := inner_mem x hx _ hcx
  rw [RegCharts.glued]
  congr 1
  refine regMax_eq_of_agree_dominated he.le J _ _ ?_ ?_ ?_
  · intro j hj
    rw [if_pos (hNJ x hx j hj), if_pos hj]
  · intro j hj
    refine ⟨(R.cover x).choose, hcxJ, ?_⟩
    rw [if_pos (hNJ x hx _ hcxJ)]
    by_cases hxj : x ∈ R.V' j
    · rw [if_pos hxj]
      have h1 : η j x = -1 := hKη j x hxj (fun hk => hNZ x hx j hj (memZ j x hxj hk))
      have h0 : η (R.cover x).choose x = 0 := (hη _).2.2.1 x hcx
      have hcmp := (abs_le.1 (hcomp j (R.cover x).choose x hxj (hV''V' _ x hcx))).2
      simp only [RegCharts.regArg, h1, h0]
      linarith
    · rw [if_neg hxj]
      linarith
  · intro j hj
    refine ⟨c, hcJ, ?_⟩
    rw [if_neg hj, if_pos hcJ]
    linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
