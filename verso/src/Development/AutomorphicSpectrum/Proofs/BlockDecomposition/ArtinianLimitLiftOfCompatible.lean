import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

open CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.ArtinTower

universe w

/- English proof (translation)
Establish `hanti : Antitone K` using `antitone_nat_of_succ_le hK`. Take `⟨m, hm⟩` from `IsArtinian.monotone_stabilizes (⟨fun k => OrderDual.toDual (K k), hanti.dual_right⟩ : ℕ →o (Submodule W M)ᵒᵈ)`. Establish `hdiff : ∀ k j, c (k + j) - c k ∈ K k`. Introduce `k j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `h1 : c (k + j + 1) - c (k + j) ∈ K k` using `hanti (Nat.le_add_right k j) (hc (k + j))`. Establish `h2` using `add_mem h1 ih`. Rewrite `h2` using `[sub_add_sub_cancel]`.

Conclude with `h2`. Use `⟨c m, fun k => ?_⟩` and prove the remaining obligations. Break down `le_total k m with hkm | hmk` into its components or cases. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hkm`. Conclude with `hdiff k j`.

Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hmk`. Establish `hKeq : K m = K (m + j)` using `hm (m + j) (Nat.le_add_right m j)`. Rewrite using `[← hKeq]`. Establish `h3` using `neg_mem (hdiff m j)`. Rewrite `h3` using `[neg_sub]`.

Conclude with `h3`.
-/
theorem coset_chain {W : Type} [CommRing W] {M : Type w} [AddCommGroup M] [Module W M]
    [IsArtinian W M] (K : ℕ → Submodule W M) (hK : ∀ k, K (k + 1) ≤ K k) (c : ℕ → M)
    (hc : ∀ k, c (k + 1) - c k ∈ K k) : ∃ x, ∀ k, x - c k ∈ K k := by
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  obtain ⟨m, hm⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k => OrderDual.toDual (K k), hanti.dual_right⟩ : ℕ →o (Submodule W M)ᵒᵈ)
  have hdiff : ∀ k j, c (k + j) - c k ∈ K k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : c (k + j + 1) - c (k + j) ∈ K k := hanti (Nat.le_add_right k j) (hc (k + j))
      have h2 := add_mem h1 ih
      rw [sub_add_sub_cancel] at h2
      exact h2
  refine ⟨c m, fun k => ?_⟩
  rcases le_total k m with hkm | hmk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
    exact hdiff k j
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    have hKeq : K m = K (m + j) := hm (m + j) (Nat.le_add_right m j)
    rw [← hKeq]
    have h3 := neg_mem (hdiff m j)
    rw [neg_sub] at h3
    exact h3

section
variable {W : Type} [CommRing W] (S : Sys.{w} W) (N : ∀ n, Submodule W (S.M n))
  (y : ∀ n, S.M n)

noncomputable def imgSub : ℕ → ∀ n, Submodule W (S.M n)
  | 0, n => N n
  | k + 1, n => (imgSub k (n + 1)).map (S.r n)

noncomputable def imgPt : ℕ → ∀ n, S.M n
  | 0, n => y n
  | k + 1, n => S.r n (imgPt k (n + 1))

def stable (n : ℕ) : Set (S.M n) := {x | ∀ k, x - imgPt S y k n ∈ imgSub S N k n}

variable {S N y}

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `n`. Use `show Submodule.map (S.r n) (N (n + 1)) ≤ N n`.

Conclude with `Submodule.map_le_iff_le_comap.mpr (fun u hu => hN n u hu)`. Consider the case `succ k ih`. Introduce `n`. Use `show Submodule.map (S.r n) (imgSub S N (k + 1) (n + 1)) ≤ Submodule.map (S.r n) (imgSub S N k (n + 1))`. Conclude with `Submodule.map_mono (ih (n + 1))`.
-/
theorem imgSub_succ_le (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) :
    ∀ k n, imgSub S N (k + 1) n ≤ imgSub S N k n := by
  intro k
  induction k with
  | zero =>
    intro n
    show Submodule.map (S.r n) (N (n + 1)) ≤ N n
    exact Submodule.map_le_iff_le_comap.mpr (fun u hu => hN n u hu)
  | succ k ih =>
    intro n
    show Submodule.map (S.r n) (imgSub S N (k + 1) (n + 1)) ≤
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    exact Submodule.map_mono (ih (n + 1))

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro n`. Conclude with `hy n`. Consider the case `succ k ih`.

Introduce `n`. Use `show S.r n (imgPt S y (k + 1) (n + 1)) - S.r n (imgPt S y k (n + 1)) ∈ Submodule.map (S.r n) (imgSub S N k (n + 1))`. Rewrite using `[← map_sub]`. Conclude with `Submodule.mem_map_of_mem (ih (n + 1))`.
-/
theorem imgPt_step (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) :
    ∀ k n, imgPt S y (k + 1) n - imgPt S y k n ∈ imgSub S N k n := by
  intro k
  induction k with
  | zero => intro n; exact hy n
  | succ k ih =>
    intro n
    show S.r n (imgPt S y (k + 1) (n + 1)) - S.r n (imgPt S y k (n + 1)) ∈
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    rw [← map_sub]
    exact Submodule.mem_map_of_mem (ih (n + 1))

/- English proof (translation)
Take `⟨x, hx⟩` from `coset_chain (fun k => imgSub S N k n) (fun k => imgSub_succ_le hN k n) (fun k => imgPt S y k n) (fun k => imgPt_step hy k n)`. Conclude with `⟨x, hx⟩`.
-/
theorem stable_nonempty (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) (n : ℕ) [IsArtinian W (S.M n)] :
    ∃ x, x ∈ stable S N y n := by
  obtain ⟨x, hx⟩ := coset_chain (fun k => imgSub S N k n) (fun k => imgSub_succ_le hN k n)
    (fun k => imgPt S y k n) (fun k => imgPt_step hy k n)
  exact ⟨x, hx⟩

/- English proof (translation)
Establish `hxk : ∀ k, x - imgPt S y k n ∈ imgSub S N k n` using `hx`. Establish `hA : ∀ k, ∃ u : S.M (n + 1), S.r n u = x ∧ u - imgPt S y k (n + 1) ∈ imgSub S N k (n + 1)`. Introduce `k`. Establish `h1 : x - imgPt S y (k + 1) n ∈ Submodule.map (S.r n) (imgSub S N k (n + 1))` using `hxk (k + 1)`. Take `⟨v, hv, hve⟩` from `Submodule.mem_map.mp h1`.

Use `⟨v + imgPt S y k (n + 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hve] show x - S.r n (imgPt S y k (n + 1)) + S.r n (imgPt S y k (n + 1)) = x`. Conclude with `sub_add_cancel _ _`. Rewrite using `[add_sub_cancel_right]`. Conclude with `hv`.

Use `choose c hc1 hc2 using hA`. Establish `hKanti : ∀ k, LinearMap.ker (S.r n) ⊓ imgSub S N (k + 1) (n + 1) ≤ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1)` using `fun k => inf_le_inf_left _ (imgSub_succ_le hN k (n + 1))`. Establish `hstep : ∀ k, c (k + 1) - c k ∈ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1)`. Introduce `k`. Rewrite using `[Submodule.mem_inf]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hc1, hc1, sub_self]`. Establish `e : c (k + 1) - c k = (c (k + 1) - imgPt S y (k + 1) (n + 1)) + (imgPt S y (k + 1) (n + 1) - imgPt S y k (n + 1)) - (c k - imgPt S y k (n + 1))`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `sub_mem (add_mem (imgSub_succ_le hN k (n + 1) (hc2 (k + 1))) (imgPt_step hy k (n + 1))) (hc2 k)`. Take `⟨x', hx'⟩` from `coset_chain (fun k => LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1)) hKanti c hstep`. Use `⟨x', fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `e : x' - imgPt S y k (n + 1) = (x' - c k) + (c k - imgPt S y k (n + 1))` using `by abel`. Rewrite using `[e]`.

Conclude with `add_mem (Submodule.mem_inf.mp (hx' k)).2 (hc2 k)`. Establish `h0` using `(Submodule.mem_inf.mp (hx' 0)).1`. Rewrite `h0` using `[LinearMap.mem_ker, map_sub, hc1, sub_eq_zero]`. Conclude with `h0`.
-/
theorem stable_surj (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) {n : ℕ} [IsArtinian W (S.M (n + 1))]
    {x : S.M n} (hx : x ∈ stable S N y n) :
    ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := by
  have hxk : ∀ k, x - imgPt S y k n ∈ imgSub S N k n := hx
  have hA : ∀ k, ∃ u : S.M (n + 1),
      S.r n u = x ∧ u - imgPt S y k (n + 1) ∈ imgSub S N k (n + 1) := by
    intro k
    have h1 : x - imgPt S y (k + 1) n ∈ Submodule.map (S.r n) (imgSub S N k (n + 1)) :=
      hxk (k + 1)
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp h1
    refine ⟨v + imgPt S y k (n + 1), ?_, ?_⟩
    · rw [map_add, hve]
      show x - S.r n (imgPt S y k (n + 1)) + S.r n (imgPt S y k (n + 1)) = x
      exact sub_add_cancel _ _
    · rw [add_sub_cancel_right]
      exact hv
  choose c hc1 hc2 using hA
  have hKanti : ∀ k, LinearMap.ker (S.r n) ⊓ imgSub S N (k + 1) (n + 1) ≤
      LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) :=
    fun k => inf_le_inf_left _ (imgSub_succ_le hN k (n + 1))
  have hstep : ∀ k, c (k + 1) - c k ∈ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) := by
    intro k
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hc1, hc1, sub_self]
    · have e : c (k + 1) - c k = (c (k + 1) - imgPt S y (k + 1) (n + 1)) +
          (imgPt S y (k + 1) (n + 1) - imgPt S y k (n + 1)) - (c k - imgPt S y k (n + 1)) := by
        abel
      rw [e]
      exact sub_mem (add_mem (imgSub_succ_le hN k (n + 1) (hc2 (k + 1)))
        (imgPt_step hy k (n + 1))) (hc2 k)
  obtain ⟨x', hx'⟩ := coset_chain (fun k => LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1))
    hKanti c hstep
  refine ⟨x', fun k => ?_, ?_⟩
  · have e : x' - imgPt S y k (n + 1) = (x' - c k) + (c k - imgPt S y k (n + 1)) := by abel
    rw [e]
    exact add_mem (Submodule.mem_inf.mp (hx' k)).2 (hc2 k)
  · have h0 := (Submodule.mem_inf.mp (hx' 0)).1
    rw [LinearMap.mem_ker, map_sub, hc1, sub_eq_zero] at h0
    exact h0

end

/- English proof (translation)
Introduce `W _ S hA N y hN hy`. Establish `h0 : ∃ x, x ∈ stable S N y 0` using `by haveI := hA 0`. Conclude with `stable_nonempty hN hy 0`. Establish `hs : ∀ n (x : S.M n), x ∈ stable S N y n → ∃ x' ∈ stable S N y (n + 1), S.r n x' = x` using `fun n x hx => by haveI := hA (n + 1)`. Conclude with `stable_surj hN hy hx`.

Set `f : ∀ n, {x : S.M n // x ∈ stable S N y n}` to `fun n => Nat.rec (motive := fun n => {x : S.M n // x ∈ stable S N y n}) ⟨h0.choose, h0.choose_spec⟩ (fun n p => ⟨(hs n p.1 p.2).choose, (hs n p.1 p.2).choose_spec.1⟩) n`. Establish `hf : ∀ n, S.r n (f (n + 1)).1 = (f n).1` using `fun n => (hs n (f n).1 (f n).2).choose_spec.2`. Use `⟨⟨fun n => (f n).1, ?_⟩, fun n => (f n).2 0⟩` and prove the remaining obligations. Unfold `CrystallineSemistableComparison.Sys.lim`. Conclude with `fun n => hf n`.
-/
theorem exists_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W),
    (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n),
    (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) →
    ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  intro W _ S hA N y hN hy
  have h0 : ∃ x, x ∈ stable S N y 0 := by
    haveI := hA 0
    exact stable_nonempty hN hy 0
  have hs : ∀ n (x : S.M n), x ∈ stable S N y n →
      ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := fun n x hx => by
    haveI := hA (n + 1)
    exact stable_surj hN hy hx
  let f : ∀ n, {x : S.M n // x ∈ stable S N y n} := fun n =>
    Nat.rec (motive := fun n => {x : S.M n // x ∈ stable S N y n})
      ⟨h0.choose, h0.choose_spec⟩
      (fun n p => ⟨(hs n p.1 p.2).choose, (hs n p.1 p.2).choose_spec.1⟩) n
  have hf : ∀ n, S.r n (f (n + 1)).1 = (f n).1 := fun n =>
    (hs n (f n).1 (f n).2).choose_spec.2
  refine ⟨⟨fun n => (f n).1, ?_⟩, fun n => (f n).2 0⟩
  unfold CrystallineSemistableComparison.Sys.lim
  exact fun n => hf n

end GlobalTheory.CompanionTheory.ArtinTower
