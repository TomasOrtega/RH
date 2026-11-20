import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvStripProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def nodeRank : {N : ℕ} → Tr E N → Option ℕ
  | _, .leaf _ _ => none
  | _, @Tr.node _ _ _ _ r _ _ _ => some r

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[eq_of_heq hh]`.
-/
theorem nodeRank_heq {N M : ℕ} (u : Tr E N) (v : Tr E M) (h : N = M) (hh : HEq u v) :
    nodeRank u = nodeRank v := by
  subst h
  rw [eq_of_heq hh]

/- English proof (translation)
Introduce `N u`. Proceed by induction on `u with`. Consider the case `leaf V z => rfl`. Consider the case `node t₁ t₂ i₁ i₂ => simp [Tr.strip, Tr.twists, i₁, i₂]`.
-/
theorem twists_length_strip : ∀ {N : ℕ} (u : Tr E N), u.strip.twists.length = u.twists.length := by
  intro N u
  induction u with
  | leaf V z => rfl
  | node t₁ t₂ i₁ i₂ => simp [Tr.strip, Tr.twists, i₁, i₂]

/- English proof (translation)
Rewrite using `[← twists_length_strip u, h, twists_length_strip]`.
-/
theorem twists_length_eq {N : ℕ} {u v : Tr E N} (h : u.strip = v.strip) :
    u.twists.length = v.twists.length := by
  rw [← twists_length_strip u, h, twists_length_strip]

/- English proof (translation)
Use `revert V w h`. Consider the cases of `u with`. Consider the case `leaf V' z`. Introduce `V w h`. Simplify using `only [Tr.strip] at h`.

Use `injection h with _ h₁`. Conclude with `⟨z, by rw [h₁]⟩`. Consider the case `node a b`. Introduce `V w h`. Use `congrArg nodeRank h` as an intermediate fact.

Simplify using `[Tr.strip, nodeRank] at this`.
-/
theorem leaf_of_strip {N : ℕ} (u : Tr E N) (V : Submodule ℂ (Sm E N)) (w : ℂ)
    (h : u.strip = .leaf V w) : ∃ z, u = .leaf V z := by
  revert V w h
  cases u with
  | leaf V' z =>
    intro V w h
    simp only [Tr.strip] at h
    injection h with _ h₁
    exact ⟨z, by rw [h₁]⟩
  | node a b =>
    intro V w h
    have := congrArg nodeRank h
    simp [Tr.strip, nodeRank] at this

/- English proof (translation)
Introduce `N u`. Consider the cases of `u with`. Consider the case `leaf V z`. Introduce `r s hN x y h`. Substitute `hN` using the available equality.

Use `congrArg nodeRank (eq_of_heq h)` as an intermediate fact. Simplify using `[Tr.strip, nodeRank] at this`. Consider the case `@node r' s' a b`. Introduce `r s hN x y h`. Establish `h₁ : r' = r`.

Use `nodeRank_heq _ _ hN h` as an intermediate fact. Simplify `this` using `[Tr.strip, nodeRank]`. Substitute `h₁` using the available equality. Establish `h₂ : s' = s` using `by omega`. Substitute `h₂` using the available equality.

Establish `h₃` using `eq_of_heq h`. Simplify using `only [Tr.strip] at h₃`. Use `injection h₃ with _ _ e₁ e₂`. Conclude with `⟨a, b, HEq.rfl, e₁, e₂⟩`.
-/
theorem node_of_strip_eq : ∀ {N : ℕ} (u : Tr E N) {r s : ℕ} (_ : N = r + s) (x : Tr E r) (y : Tr E s),
    HEq u.strip (Tr.node x y) →
    ∃ (a : Tr E r) (b : Tr E s), HEq u (Tr.node a b) ∧ a.strip = x ∧ b.strip = y := by
  intro N u
  cases u with
  | leaf V z =>
    intro r s hN x y h
    subst hN
    have := congrArg nodeRank (eq_of_heq h)
    simp [Tr.strip, nodeRank] at this
  | @node r' s' a b =>
    intro r s hN x y h
    have h₁ : r' = r := by
      have := nodeRank_heq _ _ hN h
      simpa [Tr.strip, nodeRank] using this
    subst h₁
    have h₂ : s' = s := by omega
    subst h₂
    have h₃ := eq_of_heq h
    simp only [Tr.strip] at h₃
    injection h₃ with _ _ e₁ e₂
    exact ⟨a, b, HEq.rfl, e₁, e₂⟩

/- English proof (translation)
Take `⟨a, b, e, h₁, h₂⟩` from `node_of_strip_eq u rfl x y (heq_of_eq h)`. Conclude with `⟨a, b, eq_of_heq e, h₁, h₂⟩`.
-/
theorem node_of_strip {r s : ℕ} (u : Tr E (r + s)) (x : Tr E r) (y : Tr E s)
    (h : u.strip = Tr.node x y) :
    ∃ (a : Tr E r) (b : Tr E s), u = Tr.node a b ∧ a.strip = x ∧ b.strip = y := by
  obtain ⟨a, b, e, h₁, h₂⟩ := node_of_strip_eq u rfl x y (heq_of_eq h)
  exact ⟨a, b, eq_of_heq e, h₁, h₂⟩

/- English proof (translation)
Simplify using `[List.getD_eq_getElem?_getD, List.getElem?_append_left h]`.
-/
theorem getD_append_left (A B : List ℂ) {i : ℕ} (h : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/- English proof (translation)
Rewrite using `[List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]`.
-/
theorem getD_append_right (A B : List ℂ) (i : ℕ) :
    (A ++ B).getD (A.length + i) 0 = B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/- English proof (translation)
Simplify using `[List.getD_eq_getElem?_getD, List.getElem?_eq_none h]`.
-/
theorem getD_of_le (A : List ℂ) {i : ℕ} (h : A.length ≤ i) : A.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `leaf V z z₀ h`. Use `⟨fun k => rfl, fun i => ?_⟩` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `zero => simpa [Tr.twists] using h`.

Consider the case `succ i => simp [Tr.twists]`. Consider the case `@node r s t₁ t₂ s₁ s₂ _ _ i₁ i₂`. Use `⟨fun k => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [Tr.strip, i₁.1 k, i₂.1 k]`. Establish `hl : ∀ k, (t₁ k).twists.length = s₁.twists.length` using `fun k => twists_length_eq (i₁.1 k)`.

Simplify using `only [Tr.twists]`. Distinguish the cases in `hi : i < s₁.twists.length`. Rewrite using `[getD_append_left _ _ hi]`. Establish `: (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD i 0) = fun k => (t₁ k).twists.getD i 0`. Use function extensionality and compare the values at `fun k => getD_append_left _ _ (by rw [hl k]; exact hi)`.

Rewrite using `[this]`. Conclude with `i₁.2 i`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le (not_lt.mp hi)`. Rewrite using `[getD_append_right]`. Establish `: (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD (s₁.twists.length + j) 0) = fun k => (t₂ k).twists.getD j 0`.

Use function extensionality and compare the values at `fun k => by rw [← hl k, getD_append_right]`. Rewrite using `[this]`. Conclude with `i₂.2 j`.
-/
theorem conv_forward {N : ℕ} {t : ℕ → Tr E N} {s : Tr E N} (h : Conv t s) :
    (∀ k, (t k).strip = s.strip) ∧
      ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0)) := by
  induction h with
  | leaf V z z₀ h =>
    refine ⟨fun k => rfl, fun i => ?_⟩
    cases i with
    | zero => simpa [Tr.twists] using h
    | succ i => simp [Tr.twists]
  | @node r s t₁ t₂ s₁ s₂ _ _ i₁ i₂ =>
    refine ⟨fun k => ?_, fun i => ?_⟩
    · simp only [Tr.strip, i₁.1 k, i₂.1 k]
    · have hl : ∀ k, (t₁ k).twists.length = s₁.twists.length := fun k => twists_length_eq (i₁.1 k)
      simp only [Tr.twists]
      by_cases hi : i < s₁.twists.length
      · rw [getD_append_left _ _ hi]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD i 0) = fun k => (t₁ k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rw [this]
        exact i₁.2 i
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
        rw [getD_append_right]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD (s₁.twists.length + j) 0) =
            fun k => (t₂ k).twists.getD j 0 :=
          funext fun k => by rw [← hl k, getD_append_right]
        rw [this]
        exact i₂.2 j

/- English proof (translation)
Introduce `N s`. Proceed by induction on `s with`. Consider the case `leaf V z₀`. Introduce `t hs ht`. Use `choose z hz using fun k => leaf_of_strip (t k) V 0 (hs k)`.

Take `rfl : t = fun k => .leaf V (z k)` from `funext hz`. Conclude with `Conv.leaf V z z₀ (by simpa [Tr.twists] using ht 0)`. Consider the case `@node r s s₁ s₂ i₁ i₂`. Introduce `t hs ht`. Use `choose a b hab ha hb using fun k => node_of_strip (t k) s₁.strip s₂.strip (hs k)`.

Take `rfl : t = fun k => .node (a k) (b k)` from `funext hab`. Establish `hl : ∀ k, (a k).twists.length = s₁.twists.length` using `fun k => twists_length_eq (ha k)`. Simplify using `only [Tr.twists] at ht`. Use `Conv.node (i₁ a ha fun i => ?_) (i₂ b hb fun i => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : i < s₁.twists.length`.

Establish `h` using `ht i`. Rewrite `h` using `[getD_append_left _ _ hi]`. Establish `e : (fun k => ((a k).twists ++ (b k).twists).getD i 0) = fun k => (a k).twists.getD i 0`. Use function extensionality and compare the values at `fun k => getD_append_left _ _ (by rw [hl k]; exact hi)`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Establish `e : (fun k => (a k).twists.getD i 0) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `fun k => getD_of_le _ (by rw [hl k]; exact not_lt.mp hi)`. Rewrite using `[e, getD_of_le _ (not_lt.mp hi)]`. Conclude with `tendsto_const_nhds`. Establish `h` using `ht (s₁.twists.length + i)`.

Rewrite `h` using `[getD_append_right]`. Establish `e : (fun k => ((a k).twists ++ (b k).twists).getD (s₁.twists.length + i) 0) = fun k => (b k).twists.getD i 0`. Use function extensionality and compare the values at `fun k => by rw [← hl k, getD_append_right]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem conv_backward : ∀ {N : ℕ} (s : Tr E N) (t : ℕ → Tr E N), (∀ k, (t k).strip = s.strip) →
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))) → Conv t s := by
  intro N s
  induction s with
  | leaf V z₀ =>
    intro t hs ht
    choose z hz using fun k => leaf_of_strip (t k) V 0 (hs k)
    obtain rfl : t = fun k => .leaf V (z k) := funext hz
    exact Conv.leaf V z z₀ (by simpa [Tr.twists] using ht 0)
  | @node r s s₁ s₂ i₁ i₂ =>
    intro t hs ht
    choose a b hab ha hb using fun k => node_of_strip (t k) s₁.strip s₂.strip (hs k)
    obtain rfl : t = fun k => .node (a k) (b k) := funext hab
    have hl : ∀ k, (a k).twists.length = s₁.twists.length := fun k => twists_length_eq (ha k)
    simp only [Tr.twists] at ht
    refine Conv.node (i₁ a ha fun i => ?_) (i₂ b hb fun i => ?_)
    · by_cases hi : i < s₁.twists.length
      · have h := ht i
        rw [getD_append_left _ _ hi] at h
        have e : (fun k => ((a k).twists ++ (b k).twists).getD i 0) = fun k => (a k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rwa [e] at h
      · have e : (fun k => (a k).twists.getD i 0) = fun _ => (0 : ℂ) :=
          funext fun k => getD_of_le _ (by rw [hl k]; exact not_lt.mp hi)
        rw [e, getD_of_le _ (not_lt.mp hi)]
        exact tendsto_const_nhds
    · have h := ht (s₁.twists.length + i)
      rw [getD_append_right] at h
      have e : (fun k => ((a k).twists ++ (b k).twists).getD (s₁.twists.length + i) 0) =
          fun k => (b k).twists.getD i 0 :=
        funext fun k => by rw [← hl k, getD_append_right]
      rwa [e] at h

/- English proof (translation)
Introduce `_ _ _ _ _ t s` and use `⟨conv_forward, fun h => conv_backward s t h.1 h.2⟩`.
-/
theorem convStrip : ConvStrip := fun _ _ _ _ _ t s =>
  ⟨conv_forward, fun h => conv_backward s t h.1 h.2⟩

end GlobalTheory.CompanionTheory.EGlue.ConvStripProof

end
