import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Simplify using `[wd]`.
-/
private lemma wd_zero' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (x : Finset ι → E) (t : Finset ι) : wd (fun _ : ι => (0 : Module.End ℂ E)) x t = 0 := by
  simp [wd]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[GlobalTheory.WH.uni, inrE]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, a, rfl⟩`. Conclude with `⟨a, by simpa using h, rfl⟩`.

Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨by simpa using ha, a, rfl⟩`.
-/
private theorem uni_inter_map_inrE {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ]
    (b : Finset β) (L : Finset κ) :
    uni b L ∩ Finset.map (inrE (β := β)).toEmbedding Finset.univ = L.map (inrE (β := β)).toEmbedding := by
  ext x
  simp [GlobalTheory.WH.uni, inrE]
  constructor
  · rintro ⟨h, a, rfl⟩
    exact ⟨a, by simpa using h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simpa using ha, a, rfl⟩

/- English proof (translation)
Introduce `hU β κ E _ _ _ _ _ _ A w d hK n m hm c hc hlev hcz`. Use `set Q := Finset.map (inrE (β := β) (κ := κ)).toEmbedding Finset.univ with hQ`. Establish `hQc : ∀ (b : Finset β) (L : Finset κ), (uni b L ∩ Q).card = L.card`. Introduce `b L`. Rewrite using `[hQ, uni_inter_map_inrE]`.

Simplify using the standard rewrite rules. Establish `hl : (fun i : β => wOn Q w (inlE i)) = fun _ => 0`. Use function extensionality and compare the values at `i`. Establish `: inlE (κ` using `κ) i ∉ Q := by`. Simplify using `[hQ, inlE, inrE]`.

Simplify using `[wOn, this]`. Establish `hr : (fun l : κ => wOn Q w (inrE l)) = fun l => w (inrE l)`. Use function extensionality and compare the values at `l`. Establish `: inrE (β` using `β) l ∈ Q := by`. Simplify using `[hQ]`.

Simplify using `[wOn, this]`. Establish `hdec : ∀ (x : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Q w) x (uni b L) = (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => x (uni b L')) L`. Introduce `x b L`. Rewrite using `[(hU β κ E (wOn Q w) x b L).1, hl, hr, wd_zero', zero_add]`. Establish `hmem : ∀ s, c s ∈ (if ((s.card : ℕ) : ℤ) = n then A s else ⊥)`.

Introduce `s`. Use `hc` as an intermediate fact. Simplify using `only [acx, Submodule.mem_pi, Set.mem_univ, true_implies] at this`. Conclude with `this s`. Establish `hY : ∀ b : Finset β, ∃ Y ∈ (colA A w b).C (m - 1), wd (fun l => w (inrE l)) Y = fun L => c (uni b L)`.

Introduce `b`. Establish `hz : (fun L => c (uni b L)) ∈ (colA A w b).Z m`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[colA, acx, Submodule.mem_pi]`. Introduce `L _`.

Use `show c (uni b L) ∈ (if ((L.card : ℕ) : ℤ) = m then A (uni b L) else ⊥)`. Distinguish the cases in `hL : ((L.card : ℕ) : ℤ) = m`. Rewrite using `[if_pos hL]`. Establish `h1` using `hmem (uni b L)`. Use `split_ifs at h1 with h2`.

Conclude with `h1`. Rewrite `h1` using `[Submodule.mem_bot]`. Rewrite using `[h1]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[if_neg hL, Submodule.mem_bot]`.

Apply `hlev` to reduce the goal to its premises. Use `show ¬ (((uni b L ∩ Q).card : ℕ) : ℤ) = m`. Rewrite using `[show (uni b L ∩ Q).card = L.card by convert hQc b L]` and apply the resulting hypothesis. Rewrite using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `wd (fun l => w (inrE l)) (fun L => c (uni b L)) = 0`.

Use function extensionality and compare the values at `L`. Establish `h1 : (wd (wOn Q w)) c (uni b L) = 0`. Conclude with `congrFun hcz (uni b L)`. Rewrite `h1` using `[hdec]`. Simplify using `only [Pi.zero_apply]`.

Establish `h2` using `congrArg (fun v => (-1 : ℤ) ^ b.card • v) h1`. Simplify using `only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at h2`. Conclude with `h2`. Take `⟨Y, hY1, hY2⟩` from `hK b m hm hz`. Conclude with `⟨Y, hY1, hY2⟩`.

Use `choose Y hYC hYD using hY`. Establish `hYmem : ∀ b L, Y b L ∈ (if ((L.card : ℕ) : ℤ) = m - 1 then A (uni b L) else ⊥)`. Introduce `b L`. Use `hYC b` as an intermediate fact. Rewrite `this` using `[colA, acx, Submodule.mem_pi]`.

Conclude with `this L (Set.mem_univ _)`. Establish `hU2` using `fun s => (hU β κ E w c (lft s) (rgt s)).2.2.2.2 s`. Establish `hQs : ∀ s, (s ∩ Q).card = (rgt s).card`. Introduce `s`. Use `hQc (lft s) (rgt s)` as an intermediate fact.

Rewrite `this` using `[hU2 s]`. Conclude with `this`. Take `⟨y, hy⟩ : ∃ y : Finset (β ⊕ₗ κ) → E, ∀ s, y s = if (((lft s).card : ℕ) : ℤ) = n - m then (-1 : ℤ) ^ (lft s).card • Y (lft s) (rgt s) else 0` from `⟨_, fun s => rfl⟩`. Use `⟨y, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[acx, Submodule.mem_pi]`.

Introduce `s _`. Use `show y s ∈ (if ((s.card : ℕ) : ℤ) = n - 1 then A s else ⊥)`. Rewrite using `[hy]`. Establish `hs` using `hYmem (lft s) (rgt s)`. Rewrite `hs` using `[hU2 s]`.

Establish `hcard` using `(hU β κ E w c (lft s) (rgt s)).2.2.2.1`. Rewrite `hcard` using `[hU2 s]`. Distinguish the cases in `h1 : (((lft s).card : ℕ) : ℤ) = n - m`. Rewrite using `[if_pos h1]`. Distinguish the cases in `h2 : ((s.card : ℕ) : ℤ) = n - 1`.

Rewrite using `[if_pos h2]`. Distinguish the cases in `h3 : (((rgt s).card : ℕ) : ℤ) = m - 1`. Rewrite `hs` using `[if_pos h3]`. Conclude with `zsmul_mem hs _`. Rewrite `hs` using `[if_neg h3, Submodule.mem_bot]`.

Rewrite using `[hs, smul_zero]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[if_neg h2, Submodule.mem_bot]`. Rewrite `hs` using `[if_neg, Submodule.mem_bot]`. Rewrite using `[hs, smul_zero]`.

Introduce `h3`. Apply `h2` to reduce the goal to its premises. Rewrite using `[hcard]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h1]`. Conclude with `Submodule.zero_mem _`. Introduce `s hs`. Rewrite using `[hy]`. Use `split_ifs with h1`.

Establish `hY0` using `hYmem (lft s) (rgt s)`. Rewrite `hY0` using `[if_neg]`. Rewrite `hY0` using `[Submodule.mem_bot]`. Rewrite using `[hY0, smul_zero]`. Introduce `h3`.

Apply `hs` to reduce the goal to its premises. Use `show (((s ∩ Q).card : ℕ) : ℤ) = m - 1`. Rewrite using `[hQs s]`. Conclude with `h3`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `t`. Take `⟨b, L, rfl⟩ : ∃ b L, t = uni b L` from `⟨lft t, rgt t, (hU2 t).symm⟩`. Use `Eq.trans (b := (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => y (uni b L')) L) ?_ ?_` and prove the remaining obligations. Use `hdec y b L` and compare the differences between its conclusion and the goal. Establish `hb2` using `hU β κ E w c b`.

Establish `hfun : (fun L' => y (uni b L')) = if (((b.card : ℕ) : ℤ) = n - m) then (-1 : ℤ) ^ b.card • Y b else 0`. Use function extensionality and compare the values at `L'`. Rewrite using `[hy, (hb2 L').2.1, (hb2 L').2.2.1]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hfun]`.

Distinguish the cases in `hb : (((b.card : ℕ) : ℤ) = n - m)`. Rewrite using `[if_pos hb, map_zsmul, Pi.smul_apply, hYD, smul_smul, ← mul_pow]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hb, map_zero, Pi.zero_apply, smul_zero]`. Use `symm`.

Distinguish the cases in `hL : ((L.card : ℕ) : ℤ) = m`. Establish `h5` using `hmem (uni b L)`. Rewrite `h5` using `[if_neg]`. Conclude with `(Submodule.mem_bot _).1 h5`. Introduce `hn`.

Apply `hb` to reduce the goal to its premises. Rewrite `hn` using `[(hb2 L).2.2.2.1]`. Move the coercions through the operations in `at hn`. Use linear arithmetic over natural numbers and integers. Apply `hlev show ¬ ((((uni b L ∩ Q).card : ℕ) : ℤ) = m)` to reduce the goal to its premises.

Rewrite using `[show (uni b L ∩ Q).card = L.card by convert hQc b L]` and apply the resulting hypothesis.
-/
theorem UpperTheory.Gal.productCup_of_system.colQEx_of :
    WdUni → ColQEx := by
  intro hU β κ E _ _ _ _ _ _ A w d hK n m hm c hc hlev hcz
  set Q := Finset.map (inrE (β := β) (κ := κ)).toEmbedding Finset.univ with hQ
  have hQc : ∀ (b : Finset β) (L : Finset κ), (uni b L ∩ Q).card = L.card := by
    intro b L
    rw [hQ, uni_inter_map_inrE]
    simp
  have hl : (fun i : β => wOn Q w (inlE i)) = fun _ => 0 := by
    funext i
    have : inlE (κ := κ) i ∉ Q := by
      simp [hQ, inlE, inrE]
    simp [wOn, this]
  have hr : (fun l : κ => wOn Q w (inrE l)) = fun l => w (inrE l) := by
    funext l
    have : inrE (β := β) l ∈ Q := by
      simp [hQ]
    simp [wOn, this]
  have hdec : ∀ (x : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ),
      wd (wOn Q w) x (uni b L) =
        (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => x (uni b L')) L := by
    intro x b L
    rw [(hU β κ E (wOn Q w) x b L).1, hl, hr, wd_zero', zero_add]
  have hmem : ∀ s, c s ∈ (if ((s.card : ℕ) : ℤ) = n then A s else ⊥) := by
    intro s
    have := hc
    simp only [acx, Submodule.mem_pi, Set.mem_univ, true_implies] at this
    exact this s
  have hY : ∀ b : Finset β, ∃ Y ∈ (colA A w b).C (m - 1),
      wd (fun l => w (inrE l)) Y = fun L => c (uni b L) := by
    intro b
    have hz : (fun L => c (uni b L)) ∈ (colA A w b).Z m := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [colA, acx, Submodule.mem_pi]
        intro L _
        show c (uni b L) ∈ (if ((L.card : ℕ) : ℤ) = m then A (uni b L) else ⊥)
        by_cases hL : ((L.card : ℕ) : ℤ) = m
        · rw [if_pos hL]
          have h1 := hmem (uni b L)
          split_ifs at h1 with h2
          · exact h1
          · rw [Submodule.mem_bot] at h1
            rw [h1]
            exact Submodule.zero_mem _
        · rw [if_neg hL, Submodule.mem_bot]
          apply hlev
          show ¬ (((uni b L ∩ Q).card : ℕ) : ℤ) = m
          rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
      · rw [LinearMap.mem_ker]
        change wd (fun l => w (inrE l)) (fun L => c (uni b L)) = 0
        funext L
        have h1 : (wd (wOn Q w)) c (uni b L) = 0 := by
          exact congrFun hcz (uni b L)
        rw [hdec] at h1
        simp only [Pi.zero_apply]
        have h2 := congrArg (fun v => (-1 : ℤ) ^ b.card • v) h1
        simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at h2
        exact h2
    obtain ⟨Y, hY1, hY2⟩ := hK b m hm hz
    exact ⟨Y, hY1, hY2⟩
  choose Y hYC hYD using hY
  have hYmem : ∀ b L, Y b L ∈ (if ((L.card : ℕ) : ℤ) = m - 1 then A (uni b L) else ⊥) := by
    intro b L
    have := hYC b
    rw [colA, acx, Submodule.mem_pi] at this
    exact this L (Set.mem_univ _)
  have hU2 := fun s => (hU β κ E w c (lft s) (rgt s)).2.2.2.2 s
  have hQs : ∀ s, (s ∩ Q).card = (rgt s).card := by
    intro s
    have := hQc (lft s) (rgt s)
    rw [hU2 s] at this
    exact this
  obtain ⟨y, hy⟩ : ∃ y : Finset (β ⊕ₗ κ) → E, ∀ s, y s = if (((lft s).card : ℕ) : ℤ) = n - m then
      (-1 : ℤ) ^ (lft s).card • Y (lft s) (rgt s) else 0 := ⟨_, fun s => rfl⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [acx, Submodule.mem_pi]
    intro s _
    show y s ∈ (if ((s.card : ℕ) : ℤ) = n - 1 then A s else ⊥)
    rw [hy]
    have hs := hYmem (lft s) (rgt s)
    rw [hU2 s] at hs
    have hcard := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rw [hU2 s] at hcard
    by_cases h1 : (((lft s).card : ℕ) : ℤ) = n - m
    · rw [if_pos h1]
      by_cases h2 : ((s.card : ℕ) : ℤ) = n - 1
      · rw [if_pos h2]
        by_cases h3 : (((rgt s).card : ℕ) : ℤ) = m - 1
        · rw [if_pos h3] at hs
          exact zsmul_mem hs _
        · rw [if_neg h3, Submodule.mem_bot] at hs
          rw [hs, smul_zero]
          exact Submodule.zero_mem _
      · rw [if_neg h2, Submodule.mem_bot]
        rw [if_neg, Submodule.mem_bot] at hs
        · rw [hs, smul_zero]
        · intro h3
          apply h2
          rw [hcard]
          push_cast
          omega
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · intro s hs
    rw [hy]
    split_ifs with h1
    · have hY0 := hYmem (lft s) (rgt s)
      rw [if_neg] at hY0
      · rw [Submodule.mem_bot] at hY0
        rw [hY0, smul_zero]
      · intro h3
        apply hs
        show (((s ∩ Q).card : ℕ) : ℤ) = m - 1
        rw [hQs s]
        exact h3
    · rfl
  · funext t
    obtain ⟨b, L, rfl⟩ : ∃ b L, t = uni b L := ⟨lft t, rgt t, (hU2 t).symm⟩
    refine Eq.trans (b := (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => y (uni b L')) L) ?_ ?_
    · convert hdec y b L
    have hb2 := hU β κ E w c b
    have hfun : (fun L' => y (uni b L')) =
        if (((b.card : ℕ) : ℤ) = n - m) then (-1 : ℤ) ^ b.card • Y b else 0 := by
      funext L'
      rw [hy, (hb2 L').2.1, (hb2 L').2.2.1]
      split_ifs <;> rfl
    rw [hfun]
    by_cases hb : (((b.card : ℕ) : ℤ) = n - m)
    · rw [if_pos hb, map_zsmul, Pi.smul_apply, hYD, smul_smul, ← mul_pow]
      simp
    · rw [if_neg hb, map_zero, Pi.zero_apply, smul_zero]
      symm
      by_cases hL : ((L.card : ℕ) : ℤ) = m
      · have h5 := hmem (uni b L)
        rw [if_neg] at h5
        · exact (Submodule.mem_bot _).1 h5
        · intro hn
          apply hb
          rw [(hb2 L).2.2.2.1] at hn
          push_cast at hn
          omega
      · apply hlev
        show ¬ ((((uni b L ∩ Q).card : ℕ) : ℤ) = m)
        rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
