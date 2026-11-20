import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Mathlib.Analysis.LocallyConvex.Separation

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `I F _ _ X A hXk hXc hXn hAc hAv hfin hno`. Set `P : Finset I → Prop` to `fun σ => ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j`. Set `cands` to `hfin.toFinset.powerset.filter P`. Establish `hne : cands.Nonempty`. Use `⟨∅, ?_⟩` and prove the remaining obligations.

Simplify using `only [cands, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]`. Take `⟨x, hx⟩` from `hXn`. Conclude with `⟨x, hx, fun j hj => absurd hj (Finset.notMem_empty j)⟩`. Take `⟨σ, hσ, hmax⟩` from `cands.exists_max_image Finset.card hne`. Simplify using `only [cands, Finset.mem_filter, Finset.mem_powerset] at hσ hmax`.

Take `⟨hσS, x0, hx0X, hx0σ⟩` from `hσ`. Establish `hex : ∃ i, (X ∩ A i).Nonempty ∧ x0 ∉ A i`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hno ⟨x0, hx0X, hc⟩`.

Take `⟨i, hiX, hix0⟩` from `hex`. Establish `hiσ : i ∉ σ` using `fun h => hix0 (hx0σ i h)`. Establish `hempty : ¬ P (insert i σ)`. Introduce `hP`. Establish `hsub : insert i σ ⊆ hfin.toFinset`.

Introduce `j hj`. Break down `Finset.mem_insert.mp hj with rfl | hj` into its components or cases. Simplify using `using hiX`. Conclude with `hσS hj`. Use `hmax (insert i σ) ⟨hsub, hP⟩` as an intermediate fact.

Rewrite `this` using `[Finset.card_insert_of_notMem hiσ]`. Use linear arithmetic over natural numbers and integers. Set `C : Set F` to `X ∩ ⋂ j ∈ σ, A j`. Establish `hCmem : ∀ x, x ∈ C ↔ x ∈ X ∧ ∀ j ∈ σ, x ∈ A j`. Introduce `x`.

Simplify using `[C, Set.mem_iInter₂]`. Establish `hCk : IsCompact C` using `hXk.inter_right (isClosed_biInter fun j _ => hAc j)`. Establish `hCv : Convex ℝ C` using `hXc.inter (convex_iInter₂ fun j _ => hAv j)`. Establish `hDk : IsCompact (X ∩ A i)` using `hXk.inter_right (hAc i)`. Establish `hDv : Convex ℝ (X ∩ A i)` using `hXc.inter (hAv i)`.

Establish `hdis : Disjoint (X ∩ A i) C`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hxC`. Rewrite `hxC` using `[hCmem]`. Apply `hempty` to reduce the goal to its premises.

Use `⟨x, hx.1, fun j hj => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hj with rfl | hj` into its components or cases. Conclude with `hx.2`. Conclude with `hxC.2 j hj`. Take `⟨f, u, v, hfu, huv, hfv⟩` from `geometric_hahn_banach_compact_closed hDv hDk hCv hCk.isClosed hdis`.

Use `⟨f, u, i, σ, hiX, hfu, ⟨x0, hx0X, hx0σ⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx hxσ`. Conclude with `huv.trans (hfv x ((hCmem x).mpr ⟨hx, hxσ⟩))`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.nerve_sep :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F), IsCompact X → Convex ℝ X → X.Nonempty → (∀ i, IsClosed (A i)) → (∀ i, Convex ℝ (A i)) → {i | (X ∩ A i).Nonempty}.Finite → (¬ ∃ x ∈ X, ∀ i, (X ∩ A i).Nonempty → x ∈ A i) → ∃ (f : F →L[ℝ] ℝ) (u : ℝ) (i : I) (σ : Finset I), (X ∩ A i).Nonempty ∧ (∀ x ∈ X ∩ A i, f x < u) ∧ (∃ x ∈ X, ∀ j ∈ σ, x ∈ A j) ∧ (∀ x ∈ X, (∀ j ∈ σ, x ∈ A j) → u < f x) := by
  intro I F _ _ X A hXk hXc hXn hAc hAv hfin hno
  classical
  let P : Finset I → Prop := fun σ => ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j
  let cands := hfin.toFinset.powerset.filter P
  have hne : cands.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [cands, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    obtain ⟨x, hx⟩ := hXn
    exact ⟨x, hx, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  obtain ⟨σ, hσ, hmax⟩ := cands.exists_max_image Finset.card hne
  simp only [cands, Finset.mem_filter, Finset.mem_powerset] at hσ hmax
  obtain ⟨hσS, x0, hx0X, hx0σ⟩ := hσ
  have hex : ∃ i, (X ∩ A i).Nonempty ∧ x0 ∉ A i := by
    by_contra hc
    push_neg at hc
    exact hno ⟨x0, hx0X, hc⟩
  obtain ⟨i, hiX, hix0⟩ := hex
  have hiσ : i ∉ σ := fun h => hix0 (hx0σ i h)
  have hempty : ¬ P (insert i σ) := by
    intro hP
    have hsub : insert i σ ⊆ hfin.toFinset := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hiX
      · exact hσS hj
    have := hmax (insert i σ) ⟨hsub, hP⟩
    rw [Finset.card_insert_of_notMem hiσ] at this
    omega
  let C : Set F := X ∩ ⋂ j ∈ σ, A j
  have hCmem : ∀ x, x ∈ C ↔ x ∈ X ∧ ∀ j ∈ σ, x ∈ A j := by
    intro x
    simp [C, Set.mem_iInter₂]
  have hCk : IsCompact C := hXk.inter_right (isClosed_biInter fun j _ => hAc j)
  have hCv : Convex ℝ C := hXc.inter (convex_iInter₂ fun j _ => hAv j)
  have hDk : IsCompact (X ∩ A i) := hXk.inter_right (hAc i)
  have hDv : Convex ℝ (X ∩ A i) := hXc.inter (hAv i)
  have hdis : Disjoint (X ∩ A i) C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    rw [hCmem] at hxC
    apply hempty
    refine ⟨x, hx.1, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hx.2
    · exact hxC.2 j hj
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed hDv hDk hCv hCk.isClosed hdis
  refine ⟨f, u, i, σ, hiX, hfu, ⟨x0, hx0X, hx0σ⟩, ?_⟩
  intro x hx hxσ
  exact huv.trans (hfv x ((hCmem x).mpr ⟨hx, hxσ⟩))
