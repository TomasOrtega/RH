import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

namespace RootMono

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Finset.card_filter]`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Establish `h` using `Fin.sum_univ_succ (n := l.length) (fun i : Fin (l.length + 1) => if (a :: l).get i = c then 1 else 0)`.

Simplify using `only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ] at h ih`. Simplify using `only [List.get_eq_getElem, List.length_cons]`. Rewrite using `[h, ih, List.count_cons]`. Distinguish the cases in `hac : a = c`. Simplify using `[hac, add_comm]`.

Simplify using `[hac, add_comm]`.
-/
theorem card_fiber {α : Type*} [DecidableEq α] (l : List α) (c : α) :
    Fintype.card {i : Fin l.length // l.get i = c} = l.count c := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := Fin.sum_univ_succ (n := l.length)
      (fun i : Fin (l.length + 1) => if (a :: l).get i = c then 1 else 0)
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at h ih
    simp only [List.get_eq_getElem, List.length_cons]
    rw [h, ih, List.count_cons]
    by_cases hac : a = c
    · simp [hac, add_comm]
    · simp [hac, add_comm]

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hc : ∀ c, Fintype.card {i : Fin l₁.length // l₁.get i = c} = Fintype.card {i : Fin l₂.length // l₂.get i = c}` using `fun c => by`. Rewrite using `[card_fiber, card_fiber, h.count_eq]`. Set `e : Fin l₁.length ≃ Fin l₂.length` to `Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c)`. Establish `he : ∀ i, l₂.get (e i) = l₁.get i` using `Equiv.ofFiberEquiv_map _`.

Use `⟨e.trans (finCongr h.length_eq.symm), fun i h₁ h₂ => ?_⟩` and prove the remaining obligations. Simplify using `using he i`.
-/
theorem exists_perm_fin {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.Perm l₂) {n : ℕ} (hn : l₁.length = n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n) (h₁ : (i : ℕ) < l₁.length) (h₂ : (σ i : ℕ) < l₂.length),
      l₂[(σ i : ℕ)] = l₁[(i : ℕ)] := by
  subst hn
  have hc : ∀ c, Fintype.card {i : Fin l₁.length // l₁.get i = c} =
      Fintype.card {i : Fin l₂.length // l₂.get i = c} := fun c => by
    rw [card_fiber, card_fiber, h.count_eq]
  let e : Fin l₁.length ≃ Fin l₂.length := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c)
  have he : ∀ i, l₂.get (e i) = l₁.get i := Equiv.ofFiberEquiv_map _
  refine ⟨e.trans (finCongr h.length_eq.symm), fun i h₁ h₂ => ?_⟩
  simpa using he i

/- English proof (translation)
Rewrite using `[Multiset.length_toList, Finsupp.card_toMultiset]`. Simplify using `only [Finsupp.sum, id]`. Both sides reduce to the same expression.
-/
theorem length_toList {J : Type} (m : J →₀ ℕ) : (Finsupp.toMultiset m).toList.length = m.degree := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  simp only [Finsupp.sum, id]
  rfl

end RootMono

open RootMono in

/- English proof (translation)
Establish `hn : (m + Finsupp.single r 1).mapDomain some = m.mapDomain some + Finsupp.single (some r) 1`. Rewrite using `[Finsupp.mapDomain_add, Finsupp.mapDomain_single]`. Establish `hdm : (m.mapDomain some).degree = dimFl Ψ N`. Rewrite using `[Finsupp.degree_mapDomain, hm]`. Establish `hdeg : ((m + Finsupp.single r 1).mapDomain some).degree = dimFl Ψ N + 1`.

Rewrite using `[hn, map_add, hdm, Finsupp.degree_single]`. Establish `hnone : ((m + Finsupp.single r 1).mapDomain some) none = 0` using `Finsupp.mapDomain_notin_range _ _ (by simp)`. Establish `hperm : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.Perm ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])`. Rewrite using `[← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList, hn, map_add]`. Simplify using the standard rewrite rules.

Establish `hlen₁ : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length = dimFl Ψ N + 1`. Rewrite using `[length_toList, hdeg]`. Establish `hlen₀ : (Finsupp.toMultiset (m.mapDomain some)).toList.length = dimFl Ψ N`. Rewrite using `[length_toList, hdm]`. Establish `hsm : ∀ o, IsSmoothHerm (M.line t o)`.

Introduce `o`. Consider the cases of `o with`. Consider the case `none => exact M.A_smooth`. Consider the case `some b => exact M.x_smooth t b`. Use `set L : Fin (dimFl Ψ N + 1) → HermLine M.ι := Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r) with hL`.

Establish `hval : ∀ (j : Fin (dimFl Ψ N + 1)) (hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length), L j = M.line t (((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[(j : ℕ)])`. Introduce `j`. Use `Fin.lastCases ?_ (fun k => ?_) j` and prove the remaining obligations. Introduce `hj`. Establish `: ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.last (dimFl Ψ N) : Fin _) : ℕ)] = some r`.

Simplify using `[List.getElem_append, hlen₀]`. Rewrite using `[this, hL, Fin.snoc_last]`. Both sides reduce to the same expression. Introduce `hj`. Establish `hk : (k : ℕ) < (Finsupp.toMultiset (m.mapDomain some)).toList.length`.

Rewrite using `[hlen₀]`. Conclude with `k.2`. Establish `: ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.castSucc k : Fin _) : ℕ)] = (Finsupp.toMultiset (m.mapDomain some)).toList[(k : ℕ)]`. Conclude with `List.getElem_append_left hk`. Rewrite using `[this, hL, Fin.snoc_castSucc]`.

Simplify using `only [monoLines, dif_pos hk]`. Both sides reduce to the same expression. Establish `hLs : ∀ j, IsSmoothHerm (L j)`. Introduce `j`. Establish `hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length`.

Simplify using `[hlen₀, j.2]`. Rewrite using `[hval j hj]`. Conclude with `hsm _`. Take `⟨σ, hσ⟩` from `exists_perm_fin hperm hlen₁`. Establish `hfun : monoLines (M.line t) ((m + Finsupp.single r 1).mapDomain some) (dimFl Ψ N + 1) = L ∘ σ`.

Use function extensionality and compare the values at `i`. Establish `h₁ : (i : ℕ) < (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length`. Rewrite using `[hlen₁]`. Conclude with `i.2`. Establish `h₂ : (σ i : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length`.

Simplify using `[hlen₀, (σ i).2]`. Simplify using `only [monoLines, dif_pos h₁, Function.comp, hval (σ i) h₂, hσ i h₁ h₂]`. Both sides reduce to the same expression. Unfold `RootModel.arMono`. Rewrite using `[if_pos hdeg, hnone, pow_zero, mul_one, hfun]`.

Use `congr 1`. Conclude with `(hII M.K M.ι).1 M.P (dimFl Ψ N + 1) L σ M.arith hLs`.
-/
theorem arMono_add_single (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem)
    (t : ℝ) (m : Ψ × Fin N →₀ ℕ) (r : Ψ × Fin N) (hII : IsIntersectionSystem II) (hm : m.degree = dimFl Ψ N) :
    M.arMono II t ((m + Finsupp.single r 1).mapDomain some) =
      II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r)) / (M.δ : ℝ) := by
  classical
  have hn : (m + Finsupp.single r 1).mapDomain some = m.mapDomain some + Finsupp.single (some r) 1 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hdm : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hdeg : ((m + Finsupp.single r 1).mapDomain some).degree = dimFl Ψ N + 1 := by
    rw [hn, map_add, hdm, Finsupp.degree_single]
  have hnone : ((m + Finsupp.single r 1).mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hperm : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.Perm
      ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList, hn, map_add]
    simp
  have hlen₁ : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length = dimFl Ψ N + 1 := by
    rw [length_toList, hdeg]
  have hlen₀ : (Finsupp.toMultiset (m.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [length_toList, hdm]
  have hsm : ∀ o, IsSmoothHerm (M.line t o) := by
    intro o
    cases o with
    | none => exact M.A_smooth
    | some b => exact M.x_smooth t b
  set L : Fin (dimFl Ψ N + 1) → HermLine M.ι :=
    Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r) with hL
  have hval : ∀ (j : Fin (dimFl Ψ N + 1))
      (hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length),
      L j = M.line t (((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[(j : ℕ)]) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro hj
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.last (dimFl Ψ N) : Fin _) : ℕ)] = some r := by
        simp [List.getElem_append, hlen₀]
      rw [this, hL, Fin.snoc_last]
      rfl
    · intro hj
      have hk : (k : ℕ) < (Finsupp.toMultiset (m.mapDomain some)).toList.length := by
        rw [hlen₀]; exact k.2
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.castSucc k : Fin _) : ℕ)] =
          (Finsupp.toMultiset (m.mapDomain some)).toList[(k : ℕ)] := by
        exact List.getElem_append_left hk
      rw [this, hL, Fin.snoc_castSucc]
      simp only [monoLines, dif_pos hk]
      rfl
  have hLs : ∀ j, IsSmoothHerm (L j) := by
    intro j
    have hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, j.2]
    rw [hval j hj]
    exact hsm _
  obtain ⟨σ, hσ⟩ := exists_perm_fin hperm hlen₁
  have hfun : monoLines (M.line t) ((m + Finsupp.single r 1).mapDomain some) (dimFl Ψ N + 1) = L ∘ σ := by
    funext i
    have h₁ : (i : ℕ) < (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length := by
      rw [hlen₁]; exact i.2
    have h₂ : (σ i : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, (σ i).2]
    simp only [monoLines, dif_pos h₁, Function.comp, hval (σ i) h₂, hσ i h₁ h₂]
    rfl
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one, hfun]
  congr 1
  exact (hII M.K M.ι).1 M.P (dimFl Ψ N + 1) L σ M.arith hLs

end GlobalTheory.CompanionTheory.Ar.Flat
