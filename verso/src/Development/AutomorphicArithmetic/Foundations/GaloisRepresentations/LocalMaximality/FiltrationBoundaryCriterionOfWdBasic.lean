import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]

/- English proof (translation)
Simplify using `[wd, LinearMap.pi_apply, LinearMap.sum_apply]`.
-/
private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

/- English proof (translation)
Rewrite using `[wd_apply', wd_apply']`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Break down `h i hi with h | h` into its components or cases. Simplify using `[h]`. Rewrite using `[h]`.
-/
private lemma wd_congr' (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, w i = 0 ∨ c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases h i hi with h | h
  · simp [h]
  · rw [h]

/- English proof (translation)
Establish `h1 : (t.erase i) ∩ Q = (t ∩ Q).erase i`. Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_erase]`. The claim follows by propositional logic. Establish `h2 : i ∈ t ∩ Q` using `Finset.mem_inter.2 ⟨hi, hQ⟩`.

Establish `h3 : 0 < (t ∩ Q).card` using `Finset.card_pos.2 ⟨i, h2⟩`. Rewrite using `[h1, Finset.card_erase_of_mem h2]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma card_erase_mem' {Q t : Finset σ} {i : σ} (hi : i ∈ t) (hQ : i ∈ Q) :
    (((t.erase i) ∩ Q).card : ℤ) = ((t ∩ Q).card : ℤ) - 1 := by
  have h1 : (t.erase i) ∩ Q = (t ∩ Q).erase i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have h2 : i ∈ t ∩ Q := Finset.mem_inter.2 ⟨hi, hQ⟩
  have h3 : 0 < (t ∩ Q).card := Finset.card_pos.2 ⟨i, h2⟩
  rw [h1, Finset.card_erase_of_mem h2]
  omega

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Finset.mem_inter, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, h⟩, h'⟩`. Conclude with `⟨h, h'⟩`.

Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨⟨fun e => hQ (e ▸ h'), h⟩, h'⟩`.
-/
private lemma card_erase_not' {Q t : Finset σ} {i : σ} (hQ : i ∉ Q) :
    (t.erase i) ∩ Q = t ∩ Q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨fun e => hQ (e ▸ h'), h⟩, h'⟩

/- English proof (translation)
Introduce `t ht`. Establish `ht' : ¬ (((t ∩ Q).card : ℤ) = m')` using `ht`. Establish `h0 : wd (wOn Q w) y t = wd (wOn Q w) 0 t`. Use `wd_congr' _ _ _ _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hiQ : i ∈ Q`.

Use `right`. Use `hy _ ?_` and prove the remaining obligations. Establish `h1` using `card_erase_mem' hi hiQ`. Use `show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)`. Use linear arithmetic over natural numbers and integers.

Use `left`. Simplify using `[wOn, hiQ]`. Rewrite using `[h0, map_zero]`. Both sides reduce to the same expression.
-/
private lemma levQ' (w : σ → Module.End ℂ E) (Q : Finset σ) {m m' : ℤ} (hm : m' = m + 1)
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m') (wd (wOn Q w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m') := ht
  have h0 : wd (wOn Q w) y t = wd (wOn Q w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · right
      refine hy _ ?_
      have h1 := card_erase_mem' hi hiQ
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      omega
    · left
      simp [wOn, hiQ]
  rw [h0, map_zero]
  rfl

/- English proof (translation)
Introduce `t ht`. Establish `ht' : ¬ (((t ∩ Q).card : ℤ) = m)` using `ht`. Establish `h0 : wd (wOn Qᶜ w) y t = wd (wOn Qᶜ w) 0 t`. Use `wd_congr' _ _ _ _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hiQ : i ∈ Q`.

Use `left`. Simplify using `[wOn, hiQ]`. Use `right`. Use `hy _ ?_` and prove the remaining obligations. Use `show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)`.

Rewrite using `[card_erase_not' hiQ]`. Conclude with `ht'`. Rewrite using `[h0, map_zero]`. Both sides reduce to the same expression.
-/
private lemma levC' (w : σ → Module.End ℂ E) (Q : Finset σ) {m : ℤ}
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m) (wd (wOn Qᶜ w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m) := ht
  have h0 : wd (wOn Qᶜ w) y t = wd (wOn Qᶜ w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · left
      simp [wOn, hiQ]
    · right
      refine hy _ ?_
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      rw [card_erase_not' hiQ]
      exact ht'
  rw [h0, map_zero]
  rfl

/- English proof (translation)
Establish `h` using `(hW σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w)`. Establish `h2 : wOn Q w + wOn Qᶜ w = w`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i ∈ Q <;> simp [wOn, hi]`. Rewrite `h` using `[h2]`.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
private lemma wd_split' (hW : WdBasic) (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (Q : Finset σ) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = wd (wOn Q w) c t + wd (wOn Qᶜ w) c t := by
  have h := (hW σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w)
  have h2 : wOn Q w + wOn Qᶜ w = w := by
    funext i
    by_cases hi : i ∈ Q <;> simp [wOn, hi]
  rw [h2] at h
  rw [h]
  rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `hcx _ y hy`. Rewrite `h1` using `[sub_add_cancel]`. Take `⟨hc1, hc2⟩` from `Submodule.mem_inf.1 hc`. Use `Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hc1 h1, ?_⟩` and prove the remaining obligations. Establish `h3 : wd w c = 0` using `hc2`.

Establish `h4 : wd w (wd w y) = 0` using `h2`. Use `show wd w (c - wd w y) = 0`. Rewrite using `[map_sub, h3, h4, sub_zero]`.
-/
private lemma sub_cocycle' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (hcx : (acx A w).IsCx) {n : ℤ} {c y : Finset σ → E} (hc : c ∈ (acx A w).Z n)
    (hy : y ∈ (acx A w).C (n - 1)) : c - wd w y ∈ (acx A w).Z n := by
  obtain ⟨h1, h2⟩ := hcx _ y hy
  rw [sub_add_cancel] at h1
  obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hc1 h1, ?_⟩
  have h3 : wd w c = 0 := hc2
  have h4 : wd w (wd w y) = 0 := h2
  show wd w (c - wd w y) = 0
  rw [map_sub, h3, h4, sub_zero]

/- English proof (translation)
Establish `h2 : wd w y ∈ (acx A w).B n` using `Submodule.mem_map_of_mem hy`. Simplify using `using add_mem h h2`.
-/
private lemma of_sub' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c y : Finset σ → E} (hy : y ∈ (acx A w).C (n - 1)) (h : c - wd w y ∈ (acx A w).B n) :
    c ∈ (acx A w).B n := by
  have h2 : wd w y ∈ (acx A w).B n := Submodule.mem_map_of_mem hy
  simpa using add_mem h h2

/- English proof (translation)
Establish `hcx : (acx A w).IsCx` using `(hW σ E A w).2.1 hok`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_ n c hc hl`.

Establish `h0 : c = 0`. Use function extensionality and compare the values at `s`. Use `hl s ?_` and prove the remaining obligations. Use `show ¬ (((s ∩ Q).card : ℤ) ≤ ((0 : ℕ) : ℤ) - 1)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h0]`. Conclude with `zero_mem _`. Consider the case `succ k ih`. Introduce `hk n c hc hl`. Establish `hkd : (k : ℤ) < d` using `by omega`.

Establish `hl' : ∀ s, (k : ℤ) < ((s ∩ Q).card : ℤ) → c s = 0`. Introduce `s hs`. Use `hl s ?_` and prove the remaining obligations. Use `show ¬ (((s ∩ Q).card : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1)`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Take `⟨hc1, hc2⟩` from `Submodule.mem_inf.1 hc`. Establish `hc3 : wd w c = 0` using `hc2`. Set `cm : Finset σ → E` to `fun s => if ((s ∩ Q).card : ℤ) = k then c s else 0`. Establish `hcm : cm ∈ (acx A w).C n`.

Use `Submodule.mem_pi.2 fun s hs => ?_` and prove the remaining obligations. Distinguish the cases in `h : ((s ∩ Q).card : ℤ) = k`. Establish `: cm s = c s` using `if_pos h`. Rewrite using `[this]`. Conclude with `Submodule.mem_pi.1 hc1 s hs`.

Establish `: cm s = 0` using `if_neg h`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `hcl : Lev Q (· = (k : ℤ)) cm` using `fun s hs => if_neg hs`. Establish `hkill : wd (wOn Q w) cm = 0`.

Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : ((t ∩ Q).card : ℤ) = k + 1`. Establish `e1 : wd (wOn Q w) cm t = wd (wOn Q w) c t`. Use `wd_congr' _ _ _ _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hiQ : i ∈ Q`.

Use `right`. Establish `h1` using `card_erase_mem' hi hiQ`. Conclude with `if_pos (by omega)`. Use `left`. Simplify using `[wOn, hiQ]`.

Establish `e2 : wd (wOn Qᶜ w) c t = wd (wOn Qᶜ w) 0 t`. Use `wd_congr' _ _ _ _ fun i hi => ?_` and prove the remaining obligations. Distinguish the cases in `hiQ : i ∈ Q`. Use `left`. Simplify using `[wOn, hiQ]`.

Use `right`. Use `hl' _ ?_` and prove the remaining obligations. Rewrite using `[card_erase_not' hiQ]`. Use linear arithmetic over natural numbers and integers. Establish `e3` using `wd_split' hW A w Q c t`.

Rewrite `e3` using `[hc3, e2, map_zero]`. Rewrite using `[e1]`. Simplify using `using e3.symm`. Conclude with `levQ' w Q rfl hcl t ht`. Take `⟨y, hy, hyl, hyd⟩` from `hq n k hkd cm hcm hcl hkill`.

Use `of_sub' hy (ih (by omega) n _ (sub_cocycle' hcx hc hy) ?_)` and prove the remaining obligations. Introduce `s hs`. Establish `hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (k : ℤ) - 1)` using `hs`. Establish `e1` using `wd_split' hW A w Q y s`. Establish `e2 : wd (wOn Qᶜ w) y s = 0` using `levC' w Q hyl s (by show ¬ (((s ∩ Q).card : ℤ) = (k : ℤ) - 1) omega)`.

Establish `e3 : wd (wOn Q w) y s = cm s` using `congrFun hyd s`. Establish `e4 : cm s = c s`. Distinguish the cases in `h : ((s ∩ Q).card : ℤ) = k`. Conclude with `if_pos h`. Establish `: cm s = 0` using `if_neg h`.

Rewrite using `[this, hl' s (by omega)]`. Use `show c s - wd w y s = 0`. Rewrite using `[e1, e2, e3, e4, add_zero, sub_self]`.
-/
private lemma low' (hW : WdBasic) {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {Q : Finset σ} {d : ℤ} (hok : WOk A w) (hq : QEx A w Q d) :
    ∀ k : ℕ, k ≤ d.toNat → ∀ (n : ℤ) (c : Finset σ → E), c ∈ (acx A w).Z n →
      Lev Q (· ≤ (k : ℤ) - 1) c → c ∈ (acx A w).B n := by
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  intro k
  induction k with
  | zero =>
    intro _ n c hc hl
    have h0 : c = 0 := by
      funext s
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((0 : ℕ) : ℤ) - 1)
      omega
    rw [h0]
    exact zero_mem _
  | succ k ih =>
    intro hk n c hc hl
    have hkd : (k : ℤ) < d := by omega
    have hl' : ∀ s, (k : ℤ) < ((s ∩ Q).card : ℤ) → c s = 0 := by
      intro s hs
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1)
      push_cast
      omega
    obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
    have hc3 : wd w c = 0 := hc2
    let cm : Finset σ → E := fun s => if ((s ∩ Q).card : ℤ) = k then c s else 0
    have hcm : cm ∈ (acx A w).C n := by
      refine Submodule.mem_pi.2 fun s hs => ?_
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · have : cm s = c s := if_pos h
        rw [this]
        exact Submodule.mem_pi.1 hc1 s hs
      · have : cm s = 0 := if_neg h
        rw [this]
        exact zero_mem _
    have hcl : Lev Q (· = (k : ℤ)) cm := fun s hs => if_neg hs
    have hkill : wd (wOn Q w) cm = 0 := by
      funext t
      by_cases ht : ((t ∩ Q).card : ℤ) = k + 1
      · have e1 : wd (wOn Q w) cm t = wd (wOn Q w) c t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · right
            have h1 := card_erase_mem' hi hiQ
            exact if_pos (by omega)
          · left
            simp [wOn, hiQ]
        have e2 : wd (wOn Qᶜ w) c t = wd (wOn Qᶜ w) 0 t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · left
            simp [wOn, hiQ]
          · right
            refine hl' _ ?_
            rw [card_erase_not' hiQ]
            omega
        have e3 := wd_split' hW A w Q c t
        rw [hc3, e2, map_zero] at e3
        rw [e1]
        simpa using e3.symm
      · exact levQ' w Q rfl hcl t ht
    obtain ⟨y, hy, hyl, hyd⟩ := hq n k hkd cm hcm hcl hkill
    refine of_sub' hy (ih (by omega) n _ (sub_cocycle' hcx hc hy) ?_)
    intro s hs
    have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (k : ℤ) - 1) := hs
    have e1 := wd_split' hW A w Q y s
    have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
      show ¬ (((s ∩ Q).card : ℤ) = (k : ℤ) - 1)
      omega)
    have e3 : wd (wOn Q w) y s = cm s := congrFun hyd s
    have e4 : cm s = c s := by
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · exact if_pos h
      · have : cm s = 0 := if_neg h
        rw [this, hl' s (by omega)]
    show c s - wd w y s = 0
    rw [e1, e2, e3, e4, add_zero, sub_self]

end

/- English proof (translation)
Introduce `hW σ E _ _ _ _ A w Q d n hok hq c hc hl hy0`. Take `⟨y, hy, hyl, hyd⟩` from `hy0`. Establish `hcx : (acx A w).IsCx` using `(hW σ E A w).2.1 hok`. Establish `hl' : ∀ s, d < ((s ∩ Q).card : ℤ) → c s = 0`. Introduce `s hs`.

Use `hl s ?_` and prove the remaining obligations. Use `show ¬ (((s ∩ Q).card : ℤ) ≤ d)`. Use linear arithmetic over natural numbers and integers. Use `of_sub' hy (low' hW hok hq d.toNat le_rfl n _ (sub_cocycle' hcx hc hy) ?_)` and prove the remaining obligations. Introduce `s hs`.

Establish `hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (d.toNat : ℤ) - 1)` using `hs`. Establish `hge : d ≤ ((s ∩ Q).card : ℤ)` using `by omega`. Establish `e1` using `wd_split' hW A w Q y s`. Establish `e2 : wd (wOn Qᶜ w) y s = 0` using `levC' w Q hyl s (by show ¬ (((s ∩ Q).card : ℤ) = d - 1) omega)`. Use `show c s - wd w y s = 0`.

Rewrite using `[e1, e2, add_zero]`. Distinguish the cases in `h : ((s ∩ Q).card : ℤ) = d`. Rewrite using `[hyd s h, sub_self]`. Establish `e3 : wd (wOn Q w) y s = 0` using `levQ' w Q (by ring) hyl s h`. Rewrite using `[e3, hl' s (by omega), sub_self]`.
-/
theorem UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic :
    WdBasic → FiltrationBoundaryCriterion := by
  intro hW σ E _ _ _ _ A w Q d n hok hq c hc hl hy0
  obtain ⟨y, hy, hyl, hyd⟩ := hy0
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  have hl' : ∀ s, d < ((s ∩ Q).card : ℤ) → c s = 0 := by
    intro s hs
    refine hl s ?_
    show ¬ (((s ∩ Q).card : ℤ) ≤ d)
    omega
  refine of_sub' hy (low' hW hok hq d.toNat le_rfl n _ (sub_cocycle' hcx hc hy) ?_)
  intro s hs
  have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (d.toNat : ℤ) - 1) := hs
  have hge : d ≤ ((s ∩ Q).card : ℤ) := by omega
  have e1 := wd_split' hW A w Q y s
  have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
    show ¬ (((s ∩ Q).card : ℤ) = d - 1)
    omega)
  show c s - wd w y s = 0
  rw [e1, e2, add_zero]
  by_cases h : ((s ∩ Q).card : ℤ) = d
  · rw [hyd s h, sub_self]
  · have e3 : wd (wOn Q w) y s = 0 := levQ' w Q (by ring) hyl s h
    rw [e3, hl' s (by omega), sub_self]
