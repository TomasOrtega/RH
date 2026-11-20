import Mathlib

namespace CrystallineSemistableComparison.Inj

open Submodule

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Use `⟨∅, fun _ => 0, linearIndepOn_empty K id, by simp, ?_⟩` and prove the remaining obligations. Introduce `j hj x hx`.

Rewrite using `[hN j (by omega) x hx]`. Conclude with `zero_mem _`. Consider the case `succ i ih`. Take `⟨s, w, hli, hs, hspan⟩` from `ih`. Distinguish the cases in `hi : N - (i + 1) = N - i`.

Conclude with `⟨s, w, hli, fun v hv => by rw [hi]; exact hs v hv, fun j hj => hspan j (hi ▸ hj)⟩`. Take `⟨b, hbt, hsb, htb, hlib⟩` from `exists_linearIndepOn_extension hli (Set.subset_union_left : s ⊆ s ∪ F (N - (i + 1)))`. Use `⟨b, fun v => if v ∈ s then w v else N - (i + 1), hlib, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Distinguish the cases in `h : v ∈ s`.

Simplify using `only [h, if_true]`. Conclude with `⟨(hs v h).1, by have := (hs v h).2; omega⟩`. Simplify using `only [h, if_false]`. Use `⟨?_, le_rfl⟩` and prove the remaining obligations. Break down `hbt hv with h' | h'` into its components or cases.

Conclude with `absurd h' h`. Conclude with `h'`. Introduce `j hj`. Break down `Nat.eq_or_lt_of_le hj with hjk | hlt` into its components or cases. Substitute `hjk` using the available equality.

Introduce `x hx`. Establish `hx' : x ∈ span K (id '' b)` using `htb ⟨x, Or.inr hx, rfl⟩`. Rewrite `hx'` using `[Set.image_id]`. Use `span_mono ?_ hx'` and prove the remaining obligations. Introduce `v hv`.

Use `⟨hv, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : v ∈ s`. Simplify using `only [h, if_true]`. Use `(hs v h).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `[h]`. Establish `hj' : N - i ≤ j` using `by omega`. Use `(hspan j hj').trans (span_mono ?_)` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hw⟩`. Conclude with `⟨hsb hv, by simp [hv, hw]⟩`.
-/
theorem exists_weight_basis_filtration {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (F : ℕ → Set H) (N : ℕ) (hN : ∀ j, N ≤ j → ∀ x ∈ F j, x = 0) :
    ∀ i, ∃ (s : Set H) (w : H → ℕ), LinearIndepOn K id s ∧
      (∀ v ∈ s, v ∈ F (w v) ∧ N - i ≤ w v) ∧
      ∀ j, N - i ≤ j → F j ⊆ span K {v | v ∈ s ∧ j ≤ w v} := by
  intro i
  induction i with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty K id, by simp, ?_⟩
    intro j hj x hx
    rw [hN j (by omega) x hx]
    exact zero_mem _
  | succ i ih =>
    obtain ⟨s, w, hli, hs, hspan⟩ := ih
    by_cases hi : N - (i + 1) = N - i
    · exact ⟨s, w, hli, fun v hv => by rw [hi]; exact hs v hv, fun j hj => hspan j (hi ▸ hj)⟩
    obtain ⟨b, hbt, hsb, htb, hlib⟩ :=
      exists_linearIndepOn_extension hli (Set.subset_union_left : s ⊆ s ∪ F (N - (i + 1)))
    classical
    refine ⟨b, fun v => if v ∈ s then w v else N - (i + 1), hlib, ?_, ?_⟩
    · intro v hv
      by_cases h : v ∈ s
      · simp only [h, if_true]
        exact ⟨(hs v h).1, by have := (hs v h).2; omega⟩
      · simp only [h, if_false]
        refine ⟨?_, le_rfl⟩
        rcases hbt hv with h' | h'
        · exact absurd h' h
        · exact h'
    · intro j hj
      rcases Nat.eq_or_lt_of_le hj with hjk | hlt
      · subst hjk
        intro x hx
        have hx' : x ∈ span K (id '' b) := htb ⟨x, Or.inr hx, rfl⟩
        rw [Set.image_id] at hx'
        refine span_mono ?_ hx'
        intro v hv
        refine ⟨hv, ?_⟩
        by_cases h : v ∈ s
        · simp only [h, if_true]
          have := (hs v h).2
          omega
        · simp [h]
      · have hj' : N - i ≤ j := by omega
        refine (hspan j hj').trans (span_mono ?_)
        rintro v ⟨hv, hw⟩
        exact ⟨hsb hv, by simp [hv, hw]⟩

/- English proof (translation)
Take `⟨s, w, hli, hs, hspan⟩` from `exists_weight_basis_filtration (K := K) F N (fun j hj x hx => hN x (hF hj hx)) N`. Establish `hli' : LinearIndependent K ((↑) : s → H)` using `hli`. Establish `htop : ⊤ ≤ span K (Set.range ((↑) : s → H))`. Rewrite using `[Subtype.range_coe]`. Introduce `x _`.

Use `hspan 0 (by omega) (h0 ▸ Set.mem_univ x)` as an intermediate fact. Conclude with `span_mono (fun v hv => hv.1) this`. Set `b0` to `Module.Basis.mk hli' htop`. Establish `hb0 : ∀ v, b0 v = (v : H)` using `fun v => Module.Basis.mk_apply hli' htop v`. Establish `: Finite s` using `Module.Finite.finite_basis b0`.

Use `haveI : Fintype s := Fintype.ofFinite s`. Set `e` to `Fintype.equivFin s`. Use `⟨Fintype.card s, b0.reindex e, fun t => w (e.symm t), fun t => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.reindex_apply, hb0]`. Conclude with `(hs _ (e.symm t).2).1`.

Introduce `x hx`. Rewrite using `[Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]`. Establish `hx'` using `hspan (w (e.symm t) + 1) (by omega) hx`. Establish `himg : {v | v ∈ s ∧ w (e.symm t) + 1 ≤ w v} = b0 '' {u : s | w (e.symm t) + 1 ≤ w u}`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, hw⟩`. Conclude with `⟨⟨v, hv⟩, hw, hb0 _⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite using `[hb0]`.

Conclude with `⟨u.2, hu⟩`. Rewrite `hx'` using `[himg, SetLike.mem_coe, Module.Basis.mem_span_image]`. Assume the negation of the conclusion as `hne`. Use `hx' (Finsupp.mem_support_iff.mpr hne)` as an intermediate fact. Simplify using `at this`.
-/
theorem wt_basis {K H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (F : ℕ → Set H) (hF : Antitone F) (h0 : F 0 = Set.univ) (N : ℕ) (hN : ∀ x ∈ F N, x = 0) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) K H) (w : Fin m → ℕ),
      ∀ s, b s ∈ F (w s) ∧ ∀ x ∈ F (w s + 1), b.coord s x = 0 := by
  obtain ⟨s, w, hli, hs, hspan⟩ := exists_weight_basis_filtration (K := K) F N (fun j hj x hx => hN x (hF hj hx)) N
  have hli' : LinearIndependent K ((↑) : s → H) := hli
  have htop : ⊤ ≤ span K (Set.range ((↑) : s → H)) := by
    rw [Subtype.range_coe]
    intro x _
    have := hspan 0 (by omega) (h0 ▸ Set.mem_univ x)
    exact span_mono (fun v hv => hv.1) this
  let b0 := Module.Basis.mk hli' htop
  have hb0 : ∀ v, b0 v = (v : H) := fun v => Module.Basis.mk_apply hli' htop v
  have : Finite s := Module.Finite.finite_basis b0
  haveI : Fintype s := Fintype.ofFinite s
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, b0.reindex e, fun t => w (e.symm t), fun t => ⟨?_, ?_⟩⟩
  · rw [Module.Basis.reindex_apply, hb0]
    exact (hs _ (e.symm t).2).1
  · intro x hx
    rw [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
    have hx' := hspan (w (e.symm t) + 1) (by omega) hx
    have himg : {v | v ∈ s ∧ w (e.symm t) + 1 ≤ w v} = b0 '' {u : s | w (e.symm t) + 1 ≤ w u} := by
      ext v
      constructor
      · rintro ⟨hv, hw⟩
        exact ⟨⟨v, hv⟩, hw, hb0 _⟩
      · rintro ⟨u, hu, rfl⟩
        rw [hb0]
        exact ⟨u.2, hu⟩
    rw [himg, SetLike.mem_coe, Module.Basis.mem_span_image] at hx'
    by_contra hne
    have := hx' (Finsupp.mem_support_iff.mpr hne)
    simp at this

end CrystallineSemistableComparison.Inj
