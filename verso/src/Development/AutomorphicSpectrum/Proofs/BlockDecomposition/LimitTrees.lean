import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.LimT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def lr : {N : ℕ} → Tr E N → ℕ
  | _, .leaf _ _ => 0
  | _, @Tr.node _ _ _ _ r _ _ _ => r

/- English proof (translation)
Consider the cases of `u with`. Consider the case `leaf V z => exact Nat.zero_le _`. Consider the case `node t₁ t₂ => exact Nat.le_add_right _ _`.
-/
theorem lr_le {N : ℕ} (u : Tr E N) : lr u ≤ N := by
  cases u with
  | leaf V z => exact Nat.zero_le _
  | node t₁ t₂ => exact Nat.le_add_right _ _

/- English proof (translation)
Consider the cases of `u with`. Consider the case `leaf V z => exact ⟨V, z, rfl⟩`. Consider the case `node t₁ t₂ => exact absurd (show _ = 0 from h) hr.1.ne'`.
-/
theorem leaf_of {N : ℕ} (u : Tr E N) (h : lr u = 0) (hr : Red u) : ∃ V z, u = .leaf V z := by
  cases u with
  | leaf V z => exact ⟨V, z, rfl⟩
  | node t₁ t₂ => exact absurd (show _ = 0 from h) hr.1.ne'

/- English proof (translation)
Consider the cases of `u with`. Consider the case `leaf V z => exact absurd (show 0 = r from hl) hr.ne`. Consider the case `@node r' s' t₁ t₂`. Establish `hl' : r' = r` using `hl`. Substitute `hl'` using the available equality.

Establish `hs : s' = s` using `by omega`. Substitute `hs` using the available equality. Conclude with `⟨t₁, t₂, rfl, hred.2.2.1, hred.2.2.2⟩`.
-/
theorem node_of {n : ℕ} (u : Tr E n) {r s : ℕ} (h : n = r + s) (hl : lr u = r) (hr : 0 < r) (hred : Red u) :
    ∃ (t₁ : Tr E r) (t₂ : Tr E s), h ▸ u = Tr.node t₁ t₂ ∧ Red t₁ ∧ Red t₂ := by
  cases u with
  | leaf V z => exact absurd (show 0 = r from hl) hr.ne
  | @node r' s' t₁ t₂ =>
    have hl' : r' = r := hl
    subst hl'
    have hs : s' = s := by omega
    subst hs
    exact ⟨t₁, t₂, rfl, hred.2.2.1, hred.2.2.2⟩

/- English proof (translation)
Set `f : ℕ → Fin (n + 1)` to `fun k => ⟨c k, Nat.lt_succ_of_le (h k)⟩`. Take `⟨y, hy⟩` from `Finite.exists_infinite_fiber f`. Establish `hinf : (f ⁻¹' {y}).Infinite` using `Set.infinite_coe_iff.mp hy`. Take `⟨φ, hφ, h2⟩` from `extraction_of_frequently_atTop (P := fun k => f k = y) (Nat.frequently_atTop_iff_infinite.mpr hinf)`. Conclude with `⟨y, φ, hφ, fun k => congrArg Fin.val (h2 k)⟩`.
-/
theorem pigeon {n : ℕ} (c : ℕ → ℕ) (h : ∀ k, c k ≤ n) : ∃ (r : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, c (φ k) = r := by
  let f : ℕ → Fin (n + 1) := fun k => ⟨c k, Nat.lt_succ_of_le (h k)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  obtain ⟨φ, hφ, h2⟩ := extraction_of_frequently_atTop (P := fun k => f k = y)
    (Nat.frequently_atTop_iff_infinite.mpr hinf)
  exact ⟨y, φ, hφ, fun k => congrArg Fin.val (h2 k)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨LinearMap.id, fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩`.
-/
theorem emb_refl {N : ℕ} (V : Submodule ℂ (Sm E N)) : Emb V (· ∈ V) :=
  ⟨LinearMap.id, fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn t R hred hgood hlist hz`. Take `⟨r, φ₀, hφ₀, hr⟩` from `pigeon (n := n) (fun k => lr (t k)) (fun k => lr_le _)`. Distinguish the cases in `h0 : r = 0`.

Substitute `h0 choose V z hVz using fun k => leaf_of (t (φ₀ k)) (hr k) (hred _)` using the available equality. Break down `Nat.eq_zero_or_pos n with rfl | hn0` into its components or cases. Establish `hk : ∀ k, t (φ₀ k) = .leaf ⊤ 0`. Introduce `k`. Establish `h` using `hgood (φ₀ k)`.

Rewrite `h` using `[hVz k]`. Break down `h with ⟨-, hV, hz'⟩ | ⟨h, -, -⟩` into its components or cases. Rewrite using `[hVz k, hV, hz']`. Conclude with `absurd h (lt_irrefl _)`. Use `⟨φ₀, fun _ => .leaf ⊤ 0, .leaf ⊤ 0, hφ₀, Conv.leaf ⊤ (fun _ => 0) 0 tendsto_const_nhds, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[hk k]`. Conclude with `emb_refl _`. Establish `hG : ∀ k, IsDiscrete (V k) ∧ (z k).re = 0`. Introduce `k`. Establish `h` using `hgood (φ₀ k)`.

Rewrite `h` using `[hVz k]`. Break down `h with ⟨h, -, -⟩ | ⟨-, h⟩` into its components or cases. Conclude with `absurd h hn0.ne'`. Conclude with `h`. Establish `hT : ∀ k, ∃ K' ∈ Θs n, ∃ W' ∈ Ωs n, HasType K' W' (V k)`.

Introduce `k`. Establish `h` using `hlist (φ₀ k)`. Rewrite `h` using `[hVz k]`. Break down `h with h | h` into its components or cases. Conclude with `absurd h hn0.ne'`.

Conclude with `h`. Establish `hB : ∀ k, InfBdd R (V k) ∧ ‖z k‖ ≤ R`. Introduce `k`. Establish `h` using `hz (φ₀ k)`. Rewrite `h` using `[hVz k]`.

Conclude with `h hn0`. Take `⟨φ, t', s, hφ, hc', hrs, hgs, hls, hd, he⟩` from `hL n hn0 hn V z R hR (fun k => (hG k).1) (fun k => (hG k).2) hT (fun k => (hB k).1) (fun k => (hB k).2)`. Use `⟨φ₀ ∘ φ, t', s, hφ₀.comp hφ, hc', hrs, hgs, hls, hd, fun k => ?_⟩` and prove the remaining obligations. Establish `e : t ((φ₀ ∘ φ) k) = .leaf (V (φ k)) (z (φ k))` using `hVz _`. Rewrite using `[e]`.

Conclude with `he k`. Establish `hr0 : 0 < r` using `Nat.pos_of_ne_zero h0`. Establish `hrn : r ≤ n`. Use `lr_le (t (φ₀ 0))` as an intermediate fact. Rewrite `this` using `[hr 0]`. Then use the resulting hypothesis.

Take `⟨s, rfl⟩` from `Nat.exists_eq_add_of_le hrn`. Use `choose a b hab ha hb using fun k => node_of (t (φ₀ k)) rfl (hr k) hr0 (hred _)`. Establish `hab' : ∀ k, t (φ₀ k) = .node (a k) (b k)` using `hab`. Establish `hs0 : 0 < s`. Establish `h` using `hred (φ₀ 0)`.

Rewrite `h` using `[hab' 0]`. Conclude with `h.2.1`. Establish `hG : ∀ k, (a k).Good ∧ (b k).Good` using `fun k => by`. Establish `h` using `hgood (φ₀ k)`. Rewrite `h` using `[hab' k]`.

Conclude with `h`. Establish `hT : ∀ k, (a k).AllLeaves (ListLeaf Θs Ωs) ∧ (b k).AllLeaves (ListLeaf Θs Ωs)` using `fun k => by`. Establish `h` using `hlist (φ₀ k)`. Rewrite `h` using `[hab' k]`. Conclude with `h`.

Establish `hB : ∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (a k) ∧ LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (b k)` using `fun k => by`. Establish `h` using `hz (φ₀ k)`. Rewrite `h` using `[hab' k]`. Conclude with `h`. Take `⟨φ₁, a', sa, hφ₁, hca, hra, hga, hla, hda, hea⟩` from `ih r (by omega) (by omega) a R ha (fun k => (hG k).1) (fun k => (hT k).1) (fun k => (hB k).1)`.

Take `⟨φ₂, b', sb, hφ₂, hcb, hrb, hgb, hlb, hdb, heb⟩` from `ih s (by omega) (by omega) (fun k => b (φ₁ k)) R (fun k => hb _) (fun k => (hG _).2) (fun k => (hT _).2) (fun k => (hB _).2)`. Use `⟨φ₀ ∘ φ₁ ∘ φ₂, fun k => .node (a' (φ₂ k)) (b' k), .node sa sb, hφ₀.comp (hφ₁.comp hφ₂), Conv.node (hc E r a' sa φ₂ hca hφ₂) hcb, ⟨hr0, hs0, hra, hrb⟩, ⟨hga, hgb⟩, ⟨hla, hlb⟩, fun k => ⟨hda _, hdb k⟩, fun k => ?_⟩` and prove the remaining obligations. Establish `e : t ((φ₀ ∘ φ₁ ∘ φ₂) k) = .node (a (φ₁ (φ₂ k))) (b (φ₁ (φ₂ k)))` using `hab' _`. Rewrite using `[e]`. Conclude with `hg E r s _ _ _ _ (hs E _ _ (disc_stable (good_disc (hG _).1))) (hs E _ _ (disc_stable (hda _))) (hs E _ _ (disc_stable (good_disc (hG _).2))) (hs E _ _ (disc_stable (hdb _))) (hea (φ₂ k)) (heb k)`.
-/
theorem main (hc : ConvComp) (hs : TrStable) (hg : Graft)
    (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
    (hL : LimLeafP N Θs Ωs Θf Ωf) (hR : ReproAll E) (n : ℕ) : n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) →
    (∀ k, (t k).Good) → (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) →
    (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
    ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn t R hred hgood hlist hz
  obtain ⟨r, φ₀, hφ₀, hr⟩ := pigeon (n := n) (fun k => lr (t k)) (fun k => lr_le _)
  by_cases h0 : r = 0
  · subst h0
    choose V z hVz using fun k => leaf_of (t (φ₀ k)) (hr k) (hred _)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hk : ∀ k, t (φ₀ k) = .leaf ⊤ 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨-, hV, hz'⟩ | ⟨h, -, -⟩
        · rw [hVz k, hV, hz']
        · exact absurd h (lt_irrefl _)
      refine ⟨φ₀, fun _ => .leaf ⊤ 0, .leaf ⊤ 0, hφ₀, Conv.leaf ⊤ (fun _ => 0) 0 tendsto_const_nhds, trivial,
        Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun k => ?_⟩
      rw [hk k]
      exact emb_refl _
    · have hG : ∀ k, IsDiscrete (V k) ∧ (z k).re = 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨h, -, -⟩ | ⟨-, h⟩
        · exact absurd h hn0.ne'
        · exact h
      have hT : ∀ k, ∃ K' ∈ Θs n, ∃ W' ∈ Ωs n, HasType K' W' (V k) := by
        intro k
        have h := hlist (φ₀ k)
        rw [hVz k] at h
        rcases h with h | h
        · exact absurd h hn0.ne'
        · exact h
      have hB : ∀ k, InfBdd R (V k) ∧ ‖z k‖ ≤ R := by
        intro k
        have h := hz (φ₀ k)
        rw [hVz k] at h
        exact h hn0
      obtain ⟨φ, t', s, hφ, hc', hrs, hgs, hls, hd, he⟩ := hL n hn0 hn V z R hR (fun k => (hG k).1)
        (fun k => (hG k).2) hT (fun k => (hB k).1) (fun k => (hB k).2)
      refine ⟨φ₀ ∘ φ, t', s, hφ₀.comp hφ, hc', hrs, hgs, hls, hd, fun k => ?_⟩
      have e : t ((φ₀ ∘ φ) k) = .leaf (V (φ k)) (z (φ k)) := hVz _
      rw [e]
      exact he k
  · have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have hrn : r ≤ n := by
      have := lr_le (t (φ₀ 0))
      rwa [hr 0] at this
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
    choose a b hab ha hb using fun k => node_of (t (φ₀ k)) rfl (hr k) hr0 (hred _)
    have hab' : ∀ k, t (φ₀ k) = .node (a k) (b k) := hab
    have hs0 : 0 < s := by
      have h := hred (φ₀ 0)
      rw [hab' 0] at h
      exact h.2.1
    have hG : ∀ k, (a k).Good ∧ (b k).Good := fun k => by
      have h := hgood (φ₀ k)
      rw [hab' k] at h
      exact h
    have hT : ∀ k, (a k).AllLeaves (ListLeaf Θs Ωs) ∧ (b k).AllLeaves (ListLeaf Θs Ωs) := fun k => by
      have h := hlist (φ₀ k)
      rw [hab' k] at h
      exact h
    have hB : ∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (a k) ∧
        LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (b k) := fun k => by
      have h := hz (φ₀ k)
      rw [hab' k] at h
      exact h
    obtain ⟨φ₁, a', sa, hφ₁, hca, hra, hga, hla, hda, hea⟩ := ih r (by omega) (by omega) a R ha
      (fun k => (hG k).1) (fun k => (hT k).1) (fun k => (hB k).1)
    obtain ⟨φ₂, b', sb, hφ₂, hcb, hrb, hgb, hlb, hdb, heb⟩ := ih s (by omega) (by omega) (fun k => b (φ₁ k)) R
      (fun k => hb _) (fun k => (hG _).2) (fun k => (hT _).2) (fun k => (hB _).2)
    refine ⟨φ₀ ∘ φ₁ ∘ φ₂, fun k => .node (a' (φ₂ k)) (b' k), .node sa sb, hφ₀.comp (hφ₁.comp hφ₂),
      Conv.node (hc E r a' sa φ₂ hca hφ₂) hcb, ⟨hr0, hs0, hra, hrb⟩, ⟨hga, hgb⟩, ⟨hla, hlb⟩,
      fun k => ⟨hda _, hdb k⟩, fun k => ?_⟩
    have e : t ((φ₀ ∘ φ₁ ∘ φ₂) k) = .node (a (φ₁ (φ₂ k))) (b (φ₁ (φ₂ k))) := hab' _
    rw [e]
    exact hg E r s _ _ _ _ (hs E _ _ (disc_stable (good_disc (hG _).1))) (hs E _ _ (disc_stable (hda _)))
      (hs E _ _ (disc_stable (good_disc (hG _).2))) (hs E _ _ (disc_stable (hdb _))) (hea (φ₂ k)) (heb k)

/- English proof (translation)
Introduce `hc hs hg E _ _ _ Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄`. Conclude with `main hc hs hg Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄`.
-/
theorem limTrees : ConvComp → LimTrees := by
  intro hc hs hg E _ _ _ Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄
  exact main hc hs hg Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄

end GlobalTheory.CompanionTheory.EGlue.LimT

end
