import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleTypeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermExistsStableSubsetLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBounds

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

open Polynomial Classical in
/- English proof (translation)
Unfold `_root_.GlobalTheory.BadShare.HasDiv at hd`. Take `⟨h, hdvd, hdeg⟩` from `hd`. Take `⟨hmon, -, hsq, hc0⟩` from `(_root_.GlobalTheory.BadShare.mem_sqSet).mp hf`. Establish `hf0 : f ≠ 0` using `hmon.ne_zero`. Establish `hh0 : h ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hf0 (zero_dvd_iff.mp hdvd)`. Establish `hlc : h.leadingCoeff ≠ 0` using `leadingCoeff_ne_zero.mpr hh0`. Take `⟨u, hu⟩ : ∃ u : (ZMod g)[X], u = h * C h.leadingCoeff⁻¹` from `⟨_, rfl⟩`. Establish `hudvd : u ∣ f`.

Use `dvd_trans ⟨C h.leadingCoeff, ?_⟩ hdvd` and prove the remaining obligations. Rewrite using `[hu, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]`. Establish `humon : u.Monic` using `hu ▸ monic_mul_leadingCoeff_inv hh0`. Establish `hudeg : u.natDegree = a` using `by rw [hu, natDegree_mul_C (inv_ne_zero hlc), hdeg]`. Establish `husq : Squarefree u` using `hsq.squarefree_of_dvd hudvd`.

Establish `huc0 : u.coeff 0 ≠ 0`. Introduce `h0`. Apply `hc0` to reduce the goal to its premises. Take `⟨k, hk⟩` from `hudvd`. Rewrite using `[hk, mul_coeff_zero, h0, zero_mul]`.

Establish `hmem : u ∈ _root_.GlobalTheory.BadShare.sqSet g a` using `(_root_.GlobalTheory.BadShare.mem_sqSet).mpr ⟨humon, hudeg, husq, huc0⟩`. Take `⟨k, hk⟩` from `hudvd`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Rewrite `hk` using `[mul_zero]`.

Conclude with `hf0 hk`. Use `⟨_root_.GlobalTheory.BadShare.degType g u, ?_, ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 a u hmem).2.2.1⟩` and prove the remaining obligations. Rewrite using `[hk, ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).2.1 u k humon.ne_zero hk0).1]`. Conclude with `Multiset.le_add_right _ _`.
-/
private lemma exists_le_degType_sum_eq_of_hasDiv {g : ℕ} [Fact g.Prime] {N a : ℕ}
    {f : (ZMod g)[X]} (hf : f ∈ _root_.GlobalTheory.BadShare.sqSet g N) (hd : _root_.GlobalTheory.BadShare.HasDiv g a f) :
    ∃ ν ≤ _root_.GlobalTheory.BadShare.degType g f, ν.sum = a := by
  unfold _root_.GlobalTheory.BadShare.HasDiv at hd
  obtain ⟨h, hdvd, hdeg⟩ := hd
  obtain ⟨hmon, -, hsq, hc0⟩ := (_root_.GlobalTheory.BadShare.mem_sqSet).mp hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hf0 (zero_dvd_iff.mp hdvd)
  have hlc : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hh0
  obtain ⟨u, hu⟩ : ∃ u : (ZMod g)[X], u = h * C h.leadingCoeff⁻¹ := ⟨_, rfl⟩
  have hudvd : u ∣ f := by
    refine dvd_trans ⟨C h.leadingCoeff, ?_⟩ hdvd
    rw [hu, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  have humon : u.Monic := hu ▸ monic_mul_leadingCoeff_inv hh0
  have hudeg : u.natDegree = a := by rw [hu, natDegree_mul_C (inv_ne_zero hlc), hdeg]
  have husq : Squarefree u := hsq.squarefree_of_dvd hudvd
  have huc0 : u.coeff 0 ≠ 0 := by
    intro h0
    apply hc0
    obtain ⟨k, hk⟩ := hudvd
    rw [hk, mul_coeff_zero, h0, zero_mul]
  have hmem : u ∈ _root_.GlobalTheory.BadShare.sqSet g a :=
    (_root_.GlobalTheory.BadShare.mem_sqSet).mpr ⟨humon, hudeg, husq, huc0⟩
  obtain ⟨k, hk⟩ := hudvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hf0 hk
  refine ⟨_root_.GlobalTheory.BadShare.degType g u, ?_,
    ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 a u hmem).2.2.1⟩
  rw [hk, ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).2.1 u k humon.ne_zero hk0).1]
  exact Multiset.le_add_right _ _

open Polynomial Classical in
/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty`. Introduce `ν h`. Rewrite `h` using `[Finset.empty_val, Multiset.map_zero, Multiset.le_zero]`. Conclude with `⟨∅, Finset.empty_subset _, by rw [h]; rfl⟩`.

Consider the case `cons a s ha ih`. Introduce `ν h`. Rewrite `h` using `[Finset.cons_val, Multiset.map_cons]`. Distinguish the cases in `hm : f a ∈ ν`. Take `⟨t, ht, htν⟩` from `ih (ν.erase (f a)) (by rw [← Multiset.cons_le_cons_iff (f a), Multiset.cons_erase hm]; exact h)`.

Use `⟨Finset.cons a t (fun hat => ha (ht hat)), fun x hx => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[Finset.mem_cons]`. Break down `hx with rfl | hx` into its components or cases. Conclude with `Or.inl rfl`. Conclude with `Or.inr (ht hx)`.

Rewrite using `[Finset.cons_val, Multiset.map_cons, htν, Multiset.cons_erase hm]`. Take `⟨t, ht, htν⟩` from `ih ν ((Multiset.le_cons_of_notMem hm).mp h)`. Conclude with `⟨t, fun x hx => Finset.mem_cons.mpr (Or.inr (ht hx)), htν⟩`.
-/
private lemma exists_subset_map_eq_of_le_map {β γ : Type} (f : β → γ) (s : Finset β) :
    ∀ ν : Multiset γ, ν ≤ s.val.map f → ∃ t ⊆ s, t.val.map f = ν := by
  induction s using Finset.cons_induction with
  | empty =>
    intro ν h
    rw [Finset.empty_val, Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨∅, Finset.empty_subset _, by rw [h]; rfl⟩
  | cons a s ha ih =>
    intro ν h
    rw [Finset.cons_val, Multiset.map_cons] at h
    by_cases hm : f a ∈ ν
    · obtain ⟨t, ht, htν⟩ := ih (ν.erase (f a))
        (by rw [← Multiset.cons_le_cons_iff (f a), Multiset.cons_erase hm]; exact h)
      refine ⟨Finset.cons a t (fun hat => ha (ht hat)), fun x hx => ?_, ?_⟩
      · rw [Finset.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (ht hx)
      · rw [Finset.cons_val, Multiset.map_cons, htν, Multiset.cons_erase hm]
    · obtain ⟨t, ht, htν⟩ := ih ν ((Multiset.le_cons_of_notMem hm).mp h)
      exact ⟨t, fun x hx => Finset.mem_cons.mpr (Or.inr (ht hx)), htν⟩

open Polynomial Classical in
/- English proof (translation)
Rewrite `hν` using `[Equiv.Perm.parts_partition]`. Establish `h1 : ν.filter (2 ≤ ·) ≤ σ.cycleType`. Use `(Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Multiset.filter_add, Multiset.filter_eq_self.mpr (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx), Multiset.filter_eq_nil.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), add_zero]`. Establish `h2 : ν.filter (fun x => ¬ 2 ≤ x) ≤ Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1`.

Use `(Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Multiset.filter_add, Multiset.filter_eq_nil.mpr (fun x hx => not_not.mpr (Equiv.Perm.two_le_of_mem_cycleType hx)), Multiset.filter_eq_self.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), zero_add]`. Establish `hν2 : ν.filter (fun x => ¬ 2 ≤ x) = Multiset.replicate (Multiset.card (ν.filter (fun x => ¬ 2 ≤ x))) 1` using `Multiset.eq_replicate_of_mem fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le h2 hb)`. Establish `hk` using `Multiset.card_le_card h2`. Rewrite `hk` using `[Multiset.card_replicate]`.

Rewrite `h1` using `[Equiv.Perm.cycleType_def]`. Take `⟨C, hC, hCν⟩` from `exists_subset_map_eq_of_le_map _ _ _ h1`. Establish `hcompl : (σ.support)ᶜ.card = Fintype.card (Fin n) - σ.support.card` using `Finset.card_compl _`. Take `⟨T, hT, hTc⟩` from `Finset.exists_subset_card_eq (hcompl ▸ hk)`. Establish `hCσ : ∀ c ∈ C, ∀ x ∈ c.support, σ x = c x` using `fun c hc x hx => ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hC hc)).2 x hx).symm`.

Establish `hS1 : ∀ x ∈ C.biUnion (fun c => c.support), σ x ∈ C.biUnion (fun c => c.support) ∧ σ x ≠ x`. Introduce `x hx`. Take `⟨c, hc, hxc⟩` from `Finset.mem_biUnion.mp hx`. Rewrite using `[hCσ c hc x hxc]`. Conclude with `⟨Finset.mem_biUnion.mpr ⟨c, hc, Equiv.Perm.apply_mem_support.mpr hxc⟩, Equiv.Perm.mem_support.mp hxc⟩`.

Establish `hT' : ∀ x ∈ T, σ x = x` using `fun x hx => Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hT hx))`. Establish `hdisj : Disjoint (C.biUnion (fun c => c.support)) T`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hxT`. Conclude with `(hS1 x hx).2 (hT' x hxT)`.

Establish `hcard1 : (C.biUnion (fun c => c.support)).card = (ν.filter (2 ≤ ·)).sum`. Rewrite using `[Finset.card_biUnion, ← hCν, Finset.sum_eq_multiset_sum]`. Both sides reduce to the same expression. Introduce `c hc e he hce`. Conclude with `(Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ (hC hc) (hC he) hce).disjoint_support`.

Use `⟨C.biUnion (fun c => c.support) ∪ T, ?_, ?_⟩` and prove the remaining obligations. Establish `hs2 : (ν.filter (fun x => ¬ 2 ≤ x)).sum = Multiset.card (ν.filter (fun x => ¬ 2 ≤ x))` using `by conv_lhs => rw [hν2]`. Rewrite using `[Multiset.sum_replicate, smul_eq_mul, mul_one]`. Rewrite using `[Finset.card_union_of_disjoint hdisj, hcard1, hTc, ← hs2, ← Multiset.sum_add, Multiset.filter_add_not]`. Use `Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map])` and prove the remaining obligations.

Take `⟨x, hx, rfl⟩` from `Finset.mem_map.mp hy`. Break down `Finset.mem_union.mp hx with hx | hx` into its components or cases. Conclude with `Finset.mem_union_left _ (hS1 x hx).1`. Simplify using `only [Equiv.toEmbedding_apply]`. Rewrite using `[hT' x hx]`.

Conclude with `Finset.mem_union_right _ hx`.
-/
private lemma exists_invariant_finset_card_of_le_cycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) (ν : Multiset ℕ)
    (hν : ν ≤ σ.partition.parts) : ∃ S : Finset (Fin n), S.card = ν.sum ∧ S.map σ.toEmbedding = S := by
  rw [Equiv.Perm.parts_partition] at hν
  have h1 : ν.filter (2 ≤ ·) ≤ σ.cycleType := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx),
      Multiset.filter_eq_nil.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), add_zero]
  have h2 : ν.filter (fun x => ¬ 2 ≤ x) ≤ Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1 := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr (fun x hx => not_not.mpr (Equiv.Perm.two_le_of_mem_cycleType hx)),
      Multiset.filter_eq_self.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), zero_add]
  have hν2 : ν.filter (fun x => ¬ 2 ≤ x) = Multiset.replicate (Multiset.card (ν.filter (fun x => ¬ 2 ≤ x))) 1 :=
    Multiset.eq_replicate_of_mem fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le h2 hb)
  have hk := Multiset.card_le_card h2
  rw [Multiset.card_replicate] at hk
  rw [Equiv.Perm.cycleType_def] at h1
  obtain ⟨C, hC, hCν⟩ := exists_subset_map_eq_of_le_map _ _ _ h1
  have hcompl : (σ.support)ᶜ.card = Fintype.card (Fin n) - σ.support.card := Finset.card_compl _
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (hcompl ▸ hk)
  have hCσ : ∀ c ∈ C, ∀ x ∈ c.support, σ x = c x := fun c hc x hx =>
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hC hc)).2 x hx).symm
  have hS1 : ∀ x ∈ C.biUnion (fun c => c.support), σ x ∈ C.biUnion (fun c => c.support) ∧ σ x ≠ x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    rw [hCσ c hc x hxc]
    exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, Equiv.Perm.apply_mem_support.mpr hxc⟩, Equiv.Perm.mem_support.mp hxc⟩
  have hT' : ∀ x ∈ T, σ x = x := fun x hx => Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hT hx))
  have hdisj : Disjoint (C.biUnion (fun c => c.support)) T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (hS1 x hx).2 (hT' x hxT)
  have hcard1 : (C.biUnion (fun c => c.support)).card = (ν.filter (2 ≤ ·)).sum := by
    rw [Finset.card_biUnion, ← hCν, Finset.sum_eq_multiset_sum]
    · rfl
    · intro c hc e he hce
      exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ (hC hc) (hC he) hce).disjoint_support
  refine ⟨C.biUnion (fun c => c.support) ∪ T, ?_, ?_⟩
  · have hs2 : (ν.filter (fun x => ¬ 2 ≤ x)).sum = Multiset.card (ν.filter (fun x => ¬ 2 ≤ x)) := by
      conv_lhs => rw [hν2]
      rw [Multiset.sum_replicate, smul_eq_mul, mul_one]
    rw [Finset.card_union_of_disjoint hdisj, hcard1, hTc, ← hs2, ← Multiset.sum_add, Multiset.filter_add_not]
  · refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map])
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hS1 x hx).1
    · simp only [Equiv.toEmbedding_apply]
      rw [hT' x hx]
      exact Finset.mem_union_right _ hx

open Polynomial Classical in

/- English proof (translation)
Introduce `g _ N a ha haN`. Establish `hmono` using `(_root_.GlobalTheory.BadShare.mass_union_bounds g N).1`. Use `(hmono _ (fun f => (fun μ : Multiset ℕ => ∃ ν ≤ μ, ν.sum = a) (_root_.GlobalTheory.BadShare.degType g f)) (fun f hf hd => exists_le_degType_sum_eq_of_hasDiv hf hd)).trans ?_` and prove the remaining obligations. Use `(_root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun μ => ∃ ν ≤ μ, ν.sum = a)).trans ?_` and prove the remaining obligations. Establish `h` using `_root_.GlobalTheory.StableSubset.card_exists_stable_subset_le N a ha haN`.

Establish `hc` using `Finset.card_le_card (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ ν ≤ σ.partition.parts, ν.sum = a) (t := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A) (fun σ hσ => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢`. Take `⟨ν, hν, rfl⟩` from `hσ`. Conclude with `exists_invariant_finset_card_of_le_cycleType σ ν hν)`. Establish `hf : (0 : ℝ) < N.factorial` using `by exact_mod_cast N.factorial_pos`.

Rewrite using `[div_le_iff₀ hf]`. Establish `h'` using `(Nat.cast_le (α := ℝ)).mpr h`. Establish `hc'` using `(Nat.cast_le (α := ℝ)).mpr hc`. Move the coercions through the operations in `at h' hc'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.BadShare.mass_hasDiv_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N →
    _root_.GlobalTheory.BadShare.mass g N (_root_.GlobalTheory.BadShare.HasDiv g a) ≤ 7 / 8 := by
  intro g _ N a ha haN
  have hmono := (_root_.GlobalTheory.BadShare.mass_union_bounds g N).1
  refine (hmono _ (fun f => (fun μ : Multiset ℕ => ∃ ν ≤ μ, ν.sum = a) (_root_.GlobalTheory.BadShare.degType g f))
    (fun f hf hd => exists_le_degType_sum_eq_of_hasDiv hf hd)).trans ?_
  refine (_root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun μ => ∃ ν ≤ μ, ν.sum = a)).trans ?_
  have h := _root_.GlobalTheory.StableSubset.card_exists_stable_subset_le N a ha haN
  have hc := Finset.card_le_card (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ ν ≤ σ.partition.parts, ν.sum = a)
    (t := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A)
    (fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      obtain ⟨ν, hν, rfl⟩ := hσ
      exact exists_invariant_finset_card_of_le_cycleType σ ν hν)
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf]
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at h' hc'
  linarith

end GlobalTheory.BadShare
