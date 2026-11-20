import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleMemSubmodule

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section SlopeTestRemainingChoices

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

section Abstract

variable {K G : Type} [Field K] [Group G]

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem f3 : ∀ i : Fin 3, i ≠ i + 1 ∧ i ≠ i + 2 ∧ ∀ k, k = i ∨ k = i + 1 ∨ k = i + 2 := by decide

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem d hd W hW hv hi`.
-/
private theorem single_mem (d : Fin 3 → K) (hd : Function.Injective d) (W : Submodule K (Fin 3 → K))
    (hW : ∀ v ∈ W, diagonal d *ᵥ v ∈ W) {v : Fin 3 → K} (hv : v ∈ W) {i : Fin 3} (hi : v i ≠ 0) :
    Pi.single i (1 : K) ∈ W :=
  _root_.UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem d hd W hW hv hi

/- English proof (translation)
Introduce `v hv` and use `by rw [pi_eq_sum_univ' v] refine W'.sum_mem fun i _ => ?_ by_cases hi : v i = 0 · rw [hi, zero_smul]; exact W'.zero_mem · exact W'.smul_mem _ (h v hv i hi)`.
-/
private theorem le_of_single {W W' : Submodule K (Fin 3 → K)} (h : ∀ v ∈ W, ∀ i, v i ≠ 0 → Pi.single i (1 : K) ∈ W') :
    W ≤ W' := fun v hv => by
  rw [pi_eq_sum_univ' v]
  refine W'.sum_mem fun i _ => ?_
  by_cases hi : v i = 0
  · rw [hi, zero_smul]; exact W'.zero_mem
  · exact W'.smul_mem _ (h v hv i hi)

set_option synthInstance.maxSize 1000 in
/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem comb' : ∀ P : Fin 3 → Bool, (∃ i, P i = true) → (∃ i, ¬P i = true) → ∀ Q : Fin 3 → Bool, (∃ i, Q i = true) →
    (∃ i, ¬Q i = true) → (∃ i, P i = true ∧ ¬Q i = true) →
    (∃ i, P i = true ∧ ∀ j, j ≠ i → ¬P j = true) ∨ (∃ i, Q i = true ∧ ∀ j, j ≠ i → ¬Q j = true) ∨
      ∃ i, (P i = true ∧ Q i = true) ∧ ∀ j, j ≠ i → ¬(P j = true ∧ Q j = true) := by decide

/- English proof (translation)
Introduce `P Q`. Use `fun h h' => comb' (fun i => decide (P i)) h h' fun i => decide (Q i)` as an intermediate fact. Simplify using `only [decide_eq_true_eq] at this`. Conclude with `this`.
-/
private theorem comb : ∀ P Q : Fin 3 → Prop, (∃ i, P i) → (∃ i, ¬P i) → (∃ i, Q i) → (∃ i, ¬Q i) → (∃ i, P i ∧ ¬Q i) →
    (∃ i, P i ∧ ∀ j, j ≠ i → ¬P j) ∨ (∃ i, Q i ∧ ∀ j, j ≠ i → ¬Q j) ∨ ∃ i, (P i ∧ Q i) ∧ ∀ j, j ≠ i → ¬(P j ∧ Q j) := by
  intro P Q
  classical
  have := fun h h' => comb' (fun i => decide (P i)) h h' fun i => decide (Q i)
  simp only [decide_eq_true_eq] at this
  exact this

/- English proof (translation)
Establish `key : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ U, ∀ v ∈ W, a g *ᵥ v ∈ W) → ∀ v ∈ W, ∀ i, v i ≠ 0 → Pi.single i (1 : K) ∈ W` using `fun W hW v hv i hi => single_mem d hd W (fun v hv => hud ▸ hW u hu v hv) hv hi`. Establish `fin : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ U, ∀ v ∈ W, a g *ᵥ v ∈ W) → (∃ i, Pi.single i (1 : K) ∈ W ∧ ∀ j, j ≠ i → ¬Pi.single j (1 : K) ∈ W) → ∃ i, ∀ s ∈ U, ∀ j, j ≠ i → a s j i = 0` using `fun W hW ⟨i, hi, hi'⟩ => ⟨i, fun s hs j hj => by`. Assume the negation of the conclusion as `hc`. Conclude with `hi' j hj (key W hW _ (hW s hs _ hi) j (by simpa using hc))⟩`. Establish `ne1 : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ U, ∀ v ∈ W, a g *ᵥ v ∈ W) → W ≠ ⊥ → ∃ i, Pi.single i (1 : K) ∈ W` using `fun W hW hb => by`.

Take `⟨v, hv, h0⟩` from `(Submodule.ne_bot_iff W).1 hb`. Take `⟨i, hi⟩` from `Function.ne_iff.1 h0`. Conclude with `⟨i, key W hW v hv i hi⟩`. Establish `ne2 : ∀ W : Submodule K (Fin 3 → K), W ≠ ⊤ → ∃ i, ¬Pi.single i (1 : K) ∈ W` using `fun W ht => by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `ht (top_le_iff.1 (le_of_single fun _ _ i _ => hc i))`. Unfold `MatIrr at hU`. Use `push Not at hU`. Take `⟨W, hW, hb, ht⟩` from `hU`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg, v, hv, hgv⟩ : ∃ g ∈ H, ∃ v ∈ W, a g *ᵥ v ∉ W := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `(hH W hc).elim hb ht`. Establish `hinv : ∀ w, a g *ᵥ (a g⁻¹ *ᵥ w) = w` using `fun w => by`.

Rewrite using `[mulVec_mulVec, ← hm g hg _ (H.inv_mem hg), mul_inv_cancel, h1, one_mulVec]`. Use `set W' := W.comap (mulVecLin (a g)) with hW'`. Establish `hm' : ∀ w, w ∈ W' ↔ a g *ᵥ w ∈ W` using `fun _ => Iff.rfl`. Establish `hs' : ∀ s ∈ U, ∀ w ∈ W', a s *ᵥ w ∈ W'` using `fun s hs w hw => by`. Establish `h2` using `hn.conj_mem s hs g`.

Rewrite using `[hm', mulVec_mulVec, ← hm g hg s (hUH hs), show g * s = g * s * g⁻¹ * g by group, hm _ (hUH h2) g hg, ← mulVec_mulVec]`. Conclude with `hW _ h2 _ hw`. Establish `hb' : W' ≠ ⊥` using `fun h => hb ((Submodule.eq_bot_iff W).2 fun w hw => by`. Establish `: a g⁻¹ *ᵥ w ∈ W'` using `by rw [hm', hinv]; exact hw`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Rewrite using `[← hinv w, this, mulVec_zero])`. Establish `ht' : W' ≠ ⊤` using `fun h => hgv ((hm' v).1 (h ▸ Submodule.mem_top))`. Establish `hle : ∃ i, Pi.single i (1 : K) ∈ W ∧ ¬Pi.single i (1 : K) ∈ W'`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hgv (le_of_single (W' := W') (fun v hv i hi => hc i (key W hW v hv i hi)) hv)`. Break down `comb _ _ (ne1 W hW hb) (ne2 W ht) (ne1 W' hs' hb') (ne2 W' ht') hle with h | h | h` into its components or cases. Conclude with `fin W hW h`. Conclude with `fin W' hs' h`. Conclude with `fin (W ⊓ W') (fun s hs w hw => ⟨hW s hs w hw.1, hs' s hs w hw.2⟩) h`.
-/
private theorem exists_line (H U : Subgroup G) (hUH : U ≤ H) [hn : U.Normal] (a : G → Matrix (Fin 3) (Fin 3) K)
    (hm : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h) (h1 : a 1 = 1) {u : G} (hu : u ∈ U) (d : Fin 3 → K)
    (hd : Function.Injective d) (hud : a u = diagonal d) (hH : MatIrr H a) (hU : ¬MatIrr U a) :
    ∃ i, ∀ s ∈ U, ∀ j, j ≠ i → a s j i = 0 := by
  have key : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ U, ∀ v ∈ W, a g *ᵥ v ∈ W) →
      ∀ v ∈ W, ∀ i, v i ≠ 0 → Pi.single i (1 : K) ∈ W := fun W hW v hv i hi =>
    single_mem d hd W (fun v hv => hud ▸ hW u hu v hv) hv hi
  have fin : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ U, ∀ v ∈ W, a g *ᵥ v ∈ W) →
      (∃ i, Pi.single i (1 : K) ∈ W ∧ ∀ j, j ≠ i → ¬Pi.single j (1 : K) ∈ W) → ∃ i, ∀ s ∈ U, ∀ j, j ≠ i → a s j i = 0 :=
    fun W hW ⟨i, hi, hi'⟩ => ⟨i, fun s hs j hj => by
      by_contra hc
      exact hi' j hj (key W hW _ (hW s hs _ hi) j (by simpa using hc))⟩
  have ne1 : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ U, ∀ v ∈ W, a g *ᵥ v ∈ W) → W ≠ ⊥ →
      ∃ i, Pi.single i (1 : K) ∈ W := fun W hW hb => by
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff W).1 hb
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
    exact ⟨i, key W hW v hv i hi⟩
  have ne2 : ∀ W : Submodule K (Fin 3 → K), W ≠ ⊤ → ∃ i, ¬Pi.single i (1 : K) ∈ W := fun W ht => by
    by_contra hc
    push Not at hc
    exact ht (top_le_iff.1 (le_of_single fun _ _ i _ => hc i))
  unfold MatIrr at hU
  push Not at hU
  obtain ⟨W, hW, hb, ht⟩ := hU
  obtain ⟨g, hg, v, hv, hgv⟩ : ∃ g ∈ H, ∃ v ∈ W, a g *ᵥ v ∉ W := by
    by_contra hc
    push Not at hc
    exact (hH W hc).elim hb ht
  have hinv : ∀ w, a g *ᵥ (a g⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, ← hm g hg _ (H.inv_mem hg), mul_inv_cancel, h1, one_mulVec]
  set W' := W.comap (mulVecLin (a g)) with hW'
  have hm' : ∀ w, w ∈ W' ↔ a g *ᵥ w ∈ W := fun _ => Iff.rfl
  have hs' : ∀ s ∈ U, ∀ w ∈ W', a s *ᵥ w ∈ W' := fun s hs w hw => by
    have h2 := hn.conj_mem s hs g
    rw [hm', mulVec_mulVec, ← hm g hg s (hUH hs), show g * s = g * s * g⁻¹ * g by group, hm _ (hUH h2) g hg,
      ← mulVec_mulVec]
    exact hW _ h2 _ hw
  have hb' : W' ≠ ⊥ := fun h => hb ((Submodule.eq_bot_iff W).2 fun w hw => by
    have : a g⁻¹ *ᵥ w ∈ W' := by rw [hm', hinv]; exact hw
    rw [h, Submodule.mem_bot] at this
    rw [← hinv w, this, mulVec_zero])
  have ht' : W' ≠ ⊤ := fun h => hgv ((hm' v).1 (h ▸ Submodule.mem_top))
  have hle : ∃ i, Pi.single i (1 : K) ∈ W ∧ ¬Pi.single i (1 : K) ∈ W' := by
    by_contra hc
    push Not at hc
    exact hgv (le_of_single (W' := W') (fun v hv i hi => hc i (key W hW v hv i hi)) hv)
  rcases comb _ _ (ne1 W hW hb) (ne2 W ht) (ne1 W' hs' hb') (ne2 W' ht') hle with h | h | h
  · exact fin W hW h
  · exact fin W' hs' h
  · exact fin (W ⊓ W') (fun s hs w hw => ⟨hW s hs w hw.1, hs' s hs w hw.2⟩) h

/- English proof (translation)
Assume the negation of the conclusion as `hj`. Use `hH (Submodule.pi {j | ¬P j} fun _ => ⊥) fun g hg v hv j hj => by` as an intermediate fact. Use `(Submodule.mem_bot K).2 ?_` and prove the remaining obligations. Use `show ∑ i, a g j i * v i = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hi : P i`. Rewrite using `[h g hg i j hi hj, zero_mul]`. Rewrite using `[(Submodule.mem_bot K).1 (hv i hi), mul_zero]`. Break down `this with h0 | h0` into its components or cases. Establish `h1 : Pi.single i (1 : K) ∈ Submodule.pi {j | ¬P j} fun _ => (⊥ : Submodule K K)` using `fun k hk => (Submodule.mem_bot K).2 (Pi.single_eq_of_ne (fun e : k = i => hk (e ▸ hi)) _)`.

Rewrite `h1` using `[h0, Submodule.mem_bot]`. Simplify using `using congrFun h1 i`. Establish `h1 : (fun _ => (1 : K)) ∈ Submodule.pi {j | ¬P j} fun _ => (⊥ : Submodule K K)` using `h0 ▸ Submodule.mem_top`. Simplify using `using h1 j hj`.
-/
private theorem coord {H : Subgroup G} {a : G → Matrix (Fin 3) (Fin 3) K} (hH : MatIrr H a) (P : Fin 3 → Prop)
    (h : ∀ g ∈ H, ∀ i j, P i → ¬P j → a g j i = 0) {i : Fin 3} (hi : P i) (j : Fin 3) : P j := by
  by_contra hj
  have := hH (Submodule.pi {j | ¬P j} fun _ => ⊥) fun g hg v hv j hj => by
    refine (Submodule.mem_bot K).2 ?_
    show ∑ i, a g j i * v i = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : P i
    · rw [h g hg i j hi hj, zero_mul]
    · rw [(Submodule.mem_bot K).1 (hv i hi), mul_zero]
  rcases this with h0 | h0
  · have h1 : Pi.single i (1 : K) ∈ Submodule.pi {j | ¬P j} fun _ => (⊥ : Submodule K K) := fun k hk =>
      (Submodule.mem_bot K).2 (Pi.single_eq_of_ne (fun e : k = i => hk (e ▸ hi)) _)
    rw [h0, Submodule.mem_bot] at h1
    simpa using congrFun h1 i
  · have h1 : (fun _ => (1 : K)) ∈ Submodule.pi {j | ¬P j} fun _ => (⊥ : Submodule K K) := h0 ▸ Submodule.mem_top
    simpa using h1 j hj

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem perm1 : ∀ p : Fin 3 → Fin 3, Function.Injective p → (∀ i, p i ≤ i) → ∀ i, p i = i := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem perm2 : ∀ p : Fin 3 → Fin 3, Function.Injective p → p 0 ≠ 0 → ∀ i, p i = i →
    ∀ q : Fin 3 → Fin 3, Function.Injective q → q i ≠ i → (∀ j, q j ≠ j) ∨ ∀ j, p (q j) ≠ j := by decide

/- English proof (translation)
Take `⟨i₀, hi₀⟩` from `exists_line H U hUH a hm h1 hu d hd hud hH hU`. Use `set L : Fin 3 → Prop := fun i => ∀ s ∈ U, ∀ j, j ≠ i → a s j i = 0 with hL`. Establish `hc : ∀ g ∈ H, ∀ i, L i → ∀ s ∈ U, ∃ c, ∀ k, (a s * a g) k i = a g k i * c` using `fun g hg i hi s hs => by`. Establish `h2` using `hn.conj_mem' s hs g`. Use `⟨a (g⁻¹ * s * g) i i, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hm s (hUH hs) g hg, show s * g = g * (g⁻¹ * s * g) by group, hm g hg _ (hUH h2), mul_apply, Finset.sum_eq_single i (fun b _ hb => by rw [hi _ h2 b hb, mul_zero]) (by simp)]`. Establish `hone : ∀ g ∈ H, ∀ i, L i → ∀ j, a g j i ≠ 0 → ∀ k, k ≠ j → a g k i = 0` using `fun g hg i hi j hj k hk => by`. Assume the negation of the conclusion as `h`. Take `⟨c, e⟩` from `hc g hg i hi u hu`. Simplify using `only [hud, diagonal_mul, mul_comm (d _)] at e`.

Conclude with `hk (hd ((mul_left_cancel₀ h (e k)).trans (mul_left_cancel₀ hj (e j)).symm))`. Establish `hall : ∀ j, L j` using `coord hH L (fun g hg i j hi hj => by`. Assume the negation of the conclusion as `h`. Use `hj fun s hs k hk => ?_` and prove the remaining obligations. Take `⟨c, e⟩` from `hc g hg i hi s hs`.

Establish `e'` using `e k`. Rewrite `e'` using `[hone g hg i hi j h k hk, zero_mul, mul_apply, Finset.sum_eq_single j (fun b _ hb => by rw [hone g hg i hi j h b hb, mul_zero]) (by simp)]`. Conclude with `(mul_eq_zero.1 e').resolve_right h) hi₀`. Establish `hex : ∀ g : G, ∀ i, ∃ j, g ∈ H → a g j i ≠ 0` using `fun g i => by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `hg` using `(h 0).1`. Establish `e` using `congrFun (congrFun (hm _ (H.inv_mem hg) g hg) i) i`. Rewrite `e` using `[inv_mul_cancel, h1, mul_apply]`. Simplify using `[fun j => (h j).2] at e`.

Use `choose σ hσ using hex`. Establish `hiff : ∀ g ∈ H, ∀ i j, a g j i ≠ 0 → σ g i = j` using `fun g hg i j h => by`. Assume the negation of the conclusion as `h'`. Conclude with `hσ g i hg (hone g hg i (hall i) j h _ h')`. Establish `hmul : ∀ g ∈ H, ∀ h ∈ H, ∀ i, σ (g * h) i = σ g (σ h i)` using `fun g hg h hh i => by`.

Use `hiff _ (H.mul_mem hg hh) _ _ ?_` and prove the remaining obligations. Rewrite using `[hm g hg h hh, mul_apply, Finset.sum_eq_single (σ h i) (fun b _ hb => by rw [hone h hh i (hall i) _ (hσ h i hh) b hb, mul_zero]) (by simp)]`. Conclude with `mul_ne_zero (hσ g _ hg) (hσ h i hh)`. Establish `hσ1 : ∀ i, σ 1 i = i` using `fun i => hiff 1 H.one_mem i i (by simp [h1])`. Establish `hinj : ∀ g ∈ H, Function.Injective (σ g)` using `fun g hg => Function.LeftInverse.injective (g := σ g⁻¹) fun i => by`.

Rewrite using `[← hmul _ (H.inv_mem hg) g hg, inv_mul_cancel, hσ1]`. Establish `hmv : ∀ i, ∃ g ∈ H, σ g i ≠ i` using `fun i => by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `coord hH (· = i) (fun g hg k j hk hj => by` as an intermediate fact.

Assume the negation of the conclusion as `h'`. Conclude with `hj ((hiff g hg k j h').symm.trans (by rw [hk, h g hg])) ) rfl (i + 1)`. Conclude with `(f3 i).1 this.symm`. Establish `hx1` using `perm1 _ (hinj x hx) fun i => not_lt.1 fun h => hσ x i hx (hxu _ _ h)`. Establish `hxn : ∀ (n : ℕ) i, σ (x ^ n) i = i` using `fun n i => by`.

Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, hσ1]`. Consider the case `succ n ih => rw [pow_succ, hmul _ (H.pow_mem hx n) x hx, hx1, ih]`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg, hder⟩ : ∃ g ∈ H, ∀ j, σ g j ≠ j := by`. Take `⟨p, hp, hp0⟩` from `hmv 0`.

Distinguish the cases in `h : ∀ j, σ p j ≠ j`. Conclude with `⟨p, hp, h⟩`. Use `push Not at h`. Take `⟨i, hi⟩` from `h`. Take `⟨q, hq, hqi⟩` from `hmv i`.

Break down `perm2 _ (hinj p hp) hp0 i hi _ (hinj q hq) hqi with h | h` into its components or cases. Conclude with `⟨q, hq, h⟩`. Conclude with `⟨p * q, H.mul_mem hp hq, fun j => by rw [hmul p hp q hq]; exact h j⟩`. Use `⟨g, hg, fun n => Finset.sum_eq_zero fun i _ => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Use `hiff _ (H.mul_mem hg (H.pow_mem hx n)) i i h` as an intermediate fact. Rewrite `this` using `[hmul g hg _ (H.pow_mem hx n), hxn]`. Conclude with `hder i this`.
-/
private theorem core (H U : Subgroup G) (hUH : U ≤ H) [hn : U.Normal] (a : G → Matrix (Fin 3) (Fin 3) K)
    (hm : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h) (h1 : a 1 = 1) {u : G} (hu : u ∈ U) (d : Fin 3 → K)
    (hd : Function.Injective d) (hud : a u = diagonal d) (hH : MatIrr H a) (hU : ¬MatIrr U a)
    {x : G} (hx : x ∈ H) (hxu : ∀ i j, j < i → a x i j = 0) : ∃ g ∈ H, ∀ n : ℕ, (a (g * x ^ n)).trace = 0 := by
  obtain ⟨i₀, hi₀⟩ := exists_line H U hUH a hm h1 hu d hd hud hH hU
  set L : Fin 3 → Prop := fun i => ∀ s ∈ U, ∀ j, j ≠ i → a s j i = 0 with hL
  have hc : ∀ g ∈ H, ∀ i, L i → ∀ s ∈ U, ∃ c, ∀ k, (a s * a g) k i = a g k i * c := fun g hg i hi s hs => by
    have h2 := hn.conj_mem' s hs g
    refine ⟨a (g⁻¹ * s * g) i i, fun k => ?_⟩
    rw [← hm s (hUH hs) g hg, show s * g = g * (g⁻¹ * s * g) by group, hm g hg _ (hUH h2), mul_apply,
      Finset.sum_eq_single i (fun b _ hb => by rw [hi _ h2 b hb, mul_zero]) (by simp)]
  have hone : ∀ g ∈ H, ∀ i, L i → ∀ j, a g j i ≠ 0 → ∀ k, k ≠ j → a g k i = 0 := fun g hg i hi j hj k hk => by
    by_contra h
    obtain ⟨c, e⟩ := hc g hg i hi u hu
    simp only [hud, diagonal_mul, mul_comm (d _)] at e
    exact hk (hd ((mul_left_cancel₀ h (e k)).trans (mul_left_cancel₀ hj (e j)).symm))
  have hall : ∀ j, L j := coord hH L (fun g hg i j hi hj => by
    by_contra h
    refine hj fun s hs k hk => ?_
    obtain ⟨c, e⟩ := hc g hg i hi s hs
    have e' := e k
    rw [hone g hg i hi j h k hk, zero_mul, mul_apply,
      Finset.sum_eq_single j (fun b _ hb => by rw [hone g hg i hi j h b hb, mul_zero]) (by simp)] at e'
    exact (mul_eq_zero.1 e').resolve_right h) hi₀
  have hex : ∀ g : G, ∀ i, ∃ j, g ∈ H → a g j i ≠ 0 := fun g i => by
    by_contra h
    push Not at h
    have hg := (h 0).1
    have e := congrFun (congrFun (hm _ (H.inv_mem hg) g hg) i) i
    rw [inv_mul_cancel, h1, mul_apply] at e
    simp [fun j => (h j).2] at e
  choose σ hσ using hex
  have hiff : ∀ g ∈ H, ∀ i j, a g j i ≠ 0 → σ g i = j := fun g hg i j h => by
    by_contra h'
    exact hσ g i hg (hone g hg i (hall i) j h _ h')
  have hmul : ∀ g ∈ H, ∀ h ∈ H, ∀ i, σ (g * h) i = σ g (σ h i) := fun g hg h hh i => by
    refine hiff _ (H.mul_mem hg hh) _ _ ?_
    rw [hm g hg h hh, mul_apply, Finset.sum_eq_single (σ h i)
      (fun b _ hb => by rw [hone h hh i (hall i) _ (hσ h i hh) b hb, mul_zero]) (by simp)]
    exact mul_ne_zero (hσ g _ hg) (hσ h i hh)
  have hσ1 : ∀ i, σ 1 i = i := fun i => hiff 1 H.one_mem i i (by simp [h1])
  have hinj : ∀ g ∈ H, Function.Injective (σ g) := fun g hg =>
    Function.LeftInverse.injective (g := σ g⁻¹) fun i => by
      rw [← hmul _ (H.inv_mem hg) g hg, inv_mul_cancel, hσ1]
  have hmv : ∀ i, ∃ g ∈ H, σ g i ≠ i := fun i => by
    by_contra h
    push Not at h
    have := coord hH (· = i) (fun g hg k j hk hj => by
      by_contra h'
      exact hj ((hiff g hg k j h').symm.trans (by rw [hk, h g hg])) ) rfl (i + 1)
    exact (f3 i).1 this.symm
  have hx1 := perm1 _ (hinj x hx) fun i => not_lt.1 fun h => hσ x i hx (hxu _ _ h)
  have hxn : ∀ (n : ℕ) i, σ (x ^ n) i = i := fun n i => by
    induction n with
    | zero => rw [pow_zero, hσ1]
    | succ n ih => rw [pow_succ, hmul _ (H.pow_mem hx n) x hx, hx1, ih]
  obtain ⟨g, hg, hder⟩ : ∃ g ∈ H, ∀ j, σ g j ≠ j := by
    obtain ⟨p, hp, hp0⟩ := hmv 0
    by_cases h : ∀ j, σ p j ≠ j
    · exact ⟨p, hp, h⟩
    push Not at h
    obtain ⟨i, hi⟩ := h
    obtain ⟨q, hq, hqi⟩ := hmv i
    rcases perm2 _ (hinj p hp) hp0 i hi _ (hinj q hq) hqi with h | h
    · exact ⟨q, hq, h⟩
    · exact ⟨p * q, H.mul_mem hp hq, fun j => by rw [hmul p hp q hq]; exact h j⟩
  refine ⟨g, hg, fun n => Finset.sum_eq_zero fun i _ => ?_⟩
  by_contra h
  have := hiff _ (H.mul_mem hg (H.pow_mem hx n)) i i h
  rw [hmul g hg _ (H.pow_mem hx n), hxn] at this
  exact hder i this

/- English proof (translation)
Introduce `W hW`. Establish `e : ∀ w, M' *ᵥ (M *ᵥ w) = w` using `fun w => by rw [mulVec_mulVec, h', one_mulVec]`. Establish `hm : ∀ w, w ∈ W.comap (mulVecLin M') ↔ M' *ᵥ w ∈ W` using `fun _ => Iff.rfl`. Use `(hH (W.comap (mulVecLin M')) fun g hg v hv => ?_).imp (fun h0 => ?_) fun h0 => ?_` and prove the remaining obligations. Use `hW g hg _ ((hm v).1 hv)` as an intermediate fact.

Rewrite `this` using `[mulVec_mulVec, Matrix.mul_assoc, h, Matrix.mul_one, ← mulVec_mulVec]`. Conclude with `this`. Use `(Submodule.eq_bot_iff W).2 fun w hw => ?_` and prove the remaining obligations. Establish `: M *ᵥ w ∈ W.comap (mulVecLin M')` using `by rw [hm, e]; exact hw`. Rewrite `this` using `[h0, Submodule.mem_bot]`.

Rewrite using `[← e w, this, mulVec_zero]`. Use `top_le_iff.1 fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← e w, ← hm, h0]`. Conclude with `Submodule.mem_top`.
-/
private theorem irr_conj {H : Subgroup G} {a : G → Matrix (Fin 3) (Fin 3) K} (hH : MatIrr H a)
    {M M' : Matrix (Fin 3) (Fin 3) K} (h : M * M' = 1) (h' : M' * M = 1) : MatIrr H fun g => M' * a g * M := by
  intro W hW
  have e : ∀ w, M' *ᵥ (M *ᵥ w) = w := fun w => by rw [mulVec_mulVec, h', one_mulVec]
  have hm : ∀ w, w ∈ W.comap (mulVecLin M') ↔ M' *ᵥ w ∈ W := fun _ => Iff.rfl
  refine (hH (W.comap (mulVecLin M')) fun g hg v hv => ?_).imp (fun h0 => ?_) fun h0 => ?_
  · have := hW g hg _ ((hm v).1 hv)
    rw [mulVec_mulVec, Matrix.mul_assoc, h, Matrix.mul_one, ← mulVec_mulVec] at this
    exact this
  · refine (Submodule.eq_bot_iff W).2 fun w hw => ?_
    have : M *ᵥ w ∈ W.comap (mulVecLin M') := by rw [hm, e]; exact hw
    rw [h0, Submodule.mem_bot] at this
    rw [← e w, this, mulVec_zero]
  · refine top_le_iff.1 fun w _ => ?_
    rw [← e w, ← hm, h0]
    exact Submodule.mem_top

/- English proof (translation)
Establish `h1 : T 1 1 - T 0 0 ≠ 0` using `sub_ne_zero.2 fun h => absurd (hd h) (by decide)`. Establish `h2 : T 2 2 - T 1 1 ≠ 0` using `sub_ne_zero.2 fun h => absurd (hd h) (by decide)`. Establish `h3 : T 2 2 - T 0 0 ≠ 0` using `sub_ne_zero.2 fun h => absurd (hd h) (by decide)`. Establish `z1 : T 1 0 = 0` using `hT (by decide)`. Establish `z2 : T 2 0 = 0` using `hT (by decide)`.

Establish `z3 : T 2 1 = 0` using `hT (by decide)`. Take `⟨p, hp⟩ : ∃ p, p * (T 1 1 - T 0 0) = T 0 1` from `⟨_, div_mul_cancel₀ _ h1⟩`. Take `⟨r, hr⟩ : ∃ r, r * (T 2 2 - T 1 1) = T 1 2` from `⟨_, div_mul_cancel₀ _ h2⟩`. Take `⟨q, hq⟩ : ∃ q, q * (T 2 2 - T 0 0) = T 0 2 + T 0 1 * r` from `⟨_, div_mul_cancel₀ _ h3⟩`. Establish `e : (!![1, -p, p * r - q; 0, 1, -r; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * !![1, p, q; 0, 1, r; 0, 0, 1] = 1`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨!![1, p, q; 0, 1, r; 0, 0, 1], !![1, -p, p * r - q; 0, 1, -r; 0, 0, 1], mul_eq_one_comm.1 e, e, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i j hij fin_cases i <;> fin_cases j <;> simp at hij ⊢`.

Apply the tactic sequence `intro i j hij fin_cases i <;> fin_cases j <;> simp at hij ⊢`. Establish `: T * !![1, p, q; 0, 1, r; 0, 0, 1] = !![1, p, q; 0, 1, r; 0, 0, 1] * diagonal T.diag`. Use extensionality with `i j`. Rewrite using `[mul_diagonal]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, z1, z2, z3]`.

Take the linear combination `-hp`. Take the linear combination `-hq`. Take the linear combination `-hr`. Rewrite using `[Matrix.mul_assoc, this, ← Matrix.mul_assoc, e, Matrix.one_mul]`.
-/
private theorem diagonalise (T : Matrix (Fin 3) (Fin 3) K) (hT : T.BlockTriangular id) (hd : Function.Injective T.diag) :
    ∃ n n' : Matrix (Fin 3) (Fin 3) K, n * n' = 1 ∧ n' * n = 1 ∧ n.BlockTriangular id ∧ n'.BlockTriangular id ∧
      n' * T * n = diagonal T.diag := by
  have h1 : T 1 1 - T 0 0 ≠ 0 := sub_ne_zero.2 fun h => absurd (hd h) (by decide)
  have h2 : T 2 2 - T 1 1 ≠ 0 := sub_ne_zero.2 fun h => absurd (hd h) (by decide)
  have h3 : T 2 2 - T 0 0 ≠ 0 := sub_ne_zero.2 fun h => absurd (hd h) (by decide)
  have z1 : T 1 0 = 0 := hT (by decide)
  have z2 : T 2 0 = 0 := hT (by decide)
  have z3 : T 2 1 = 0 := hT (by decide)
  obtain ⟨p, hp⟩ : ∃ p, p * (T 1 1 - T 0 0) = T 0 1 := ⟨_, div_mul_cancel₀ _ h1⟩
  obtain ⟨r, hr⟩ : ∃ r, r * (T 2 2 - T 1 1) = T 1 2 := ⟨_, div_mul_cancel₀ _ h2⟩
  obtain ⟨q, hq⟩ : ∃ q, q * (T 2 2 - T 0 0) = T 0 2 + T 0 1 * r := ⟨_, div_mul_cancel₀ _ h3⟩
  have e : (!![1, -p, p * r - q; 0, 1, -r; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * !![1, p, q; 0, 1, r; 0, 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
    ring
  refine ⟨!![1, p, q; 0, 1, r; 0, 0, 1], !![1, -p, p * r - q; 0, 1, -r; 0, 0, 1], mul_eq_one_comm.1 e, e, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · have : T * !![1, p, q; 0, 1, r; 0, 0, 1] = !![1, p, q; 0, 1, r; 0, 0, 1] * diagonal T.diag := by
      ext i j
      rw [mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, z1, z2, z3]
      · linear_combination -hp
      · linear_combination -hq
      · linear_combination -hr
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, e, Matrix.one_mul]

/- English proof (translation)
Take `⟨n, n', e, e', t, t', hn⟩` from `diagonalise _ hut hd`. Establish `f : M * n * (n' * M') = 1` using `by rw [Matrix.mul_assoc, ← Matrix.mul_assoc n, e, Matrix.one_mul, h]`. Establish `f' : n' * M' * (M * n) = 1` using `mul_eq_one_comm.1 f`. Establish `as : ∀ X : Matrix (Fin 3) (Fin 3) K, n' * M' * X * (M * n) = n' * (M' * X * M) * n` using `fun X => by`. Simplify using `only [Matrix.mul_assoc]`.

Take `⟨g, hg, hz⟩` from `core H U hUH (fun g => n' * M' * a g * (M * n)) (fun g hg k hk => by`. Rewrite using `[hm g hg k hk, Matrix.mul_assoc _ (M * n), ← Matrix.mul_assoc (M * n), ← Matrix.mul_assoc (M * n), f]`. Simplify using `only [Matrix.mul_assoc, Matrix.one_mul])`. Use the proof step `(by rw [h1, Matrix.mul_one, f']) hu _ hd ((as _).trans hn) (irr_conj hH f f') (fun hc => hU (by`. Use `irr_conj hc f' f` as an intermediate fact.

Use `this using 2 with g` and compare the differences between its conclusion and the goal. Rewrite using `[← Matrix.mul_assoc (M * n), ← Matrix.mul_assoc (M * n), f, Matrix.one_mul, Matrix.mul_assoc, f, Matrix.mul_one]))`. Use `hx (fun i j hij => by rw [as]; exact (t'.mul hxu).mul t hij)`. Use `⟨g, hg, fun k => ?_⟩` and prove the remaining obligations. Use `hz k` as an intermediate fact.

Rewrite `this` using `[trace_mul_cycle, f, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
private theorem core' (H U : Subgroup G) (hUH : U ≤ H) [U.Normal] (a : G → Matrix (Fin 3) (Fin 3) K)
    (hm : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h) (h1 : a 1 = 1) {M M' : Matrix (Fin 3) (Fin 3) K}
    (h : M * M' = 1) (h' : M' * M = 1) {u : G} (hu : u ∈ U) (hut : (M' * a u * M).BlockTriangular id)
    (hd : Function.Injective (M' * a u * M).diag) (hH : MatIrr H a) (hU : ¬MatIrr U a)
    {x : G} (hx : x ∈ H) (hxu : (M' * a x * M).BlockTriangular id) : ∃ g ∈ H, ∀ n : ℕ, (a (g * x ^ n)).trace = 0 := by
  obtain ⟨n, n', e, e', t, t', hn⟩ := diagonalise _ hut hd
  have f : M * n * (n' * M') = 1 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc n, e, Matrix.one_mul, h]
  have f' : n' * M' * (M * n) = 1 := mul_eq_one_comm.1 f
  have as : ∀ X : Matrix (Fin 3) (Fin 3) K, n' * M' * X * (M * n) = n' * (M' * X * M) * n := fun X => by
    simp only [Matrix.mul_assoc]
  obtain ⟨g, hg, hz⟩ := core H U hUH (fun g => n' * M' * a g * (M * n)) (fun g hg k hk => by
      rw [hm g hg k hk, Matrix.mul_assoc _ (M * n), ← Matrix.mul_assoc (M * n), ← Matrix.mul_assoc (M * n), f]
      simp only [Matrix.mul_assoc, Matrix.one_mul])
    (by rw [h1, Matrix.mul_one, f']) hu _ hd ((as _).trans hn) (irr_conj hH f f') (fun hc => hU (by
      have := irr_conj hc f' f
      convert this using 2 with g
      rw [← Matrix.mul_assoc (M * n), ← Matrix.mul_assoc (M * n), f, Matrix.one_mul, Matrix.mul_assoc, f, Matrix.mul_one]))
    hx (fun i j hij => by rw [as]; exact (t'.mul hxu).mul t hij)
  refine ⟨g, hg, fun k => ?_⟩
  have := hz k
  rwa [trace_mul_cycle, f, Matrix.one_mul] at this

end Abstract

/- English proof (translation)
Establish `h' : ∀ n : ℕ, ((a : k) * b ^ n) ^ 2 + a * b ^ n + 1 = 0` using `fun n => by`. Establish `e` using `(a * b ^ n).mul_inv`. Establish `e'` using `h n`. Rewrite `e`, `e'` using `[Units.val_mul, Units.val_pow_eq_pow_val]`. Take the linear combination `((a : k) * b ^ n) * e' - e`.

Assume the negation of the conclusion as `hb`. Establish `hb1 : (b : k) - 1 ≠ 0` using `fun e => hb (by linear_combination ((b : k) + 1) * e)`. Establish `e1 : (a : k) * b + a + 1 = 0` using `mul_left_cancel₀ (mul_ne_zero a.ne_zero hb1) (by linear_combination h' 1 - h' 0)`. Establish `e2 : (a : k) * b ^ 2 + a + 1 = 0` using `mul_left_cancel₀ (mul_ne_zero a.ne_zero hb) (by linear_combination h' 2 - h' 0)`. Conclude with `mul_ne_zero (mul_ne_zero a.ne_zero b.ne_zero) hb1 (by linear_combination e2 - e1)`.
-/
private theorem roots {k : Type} [Field k] (a b : kˣ) (h : ∀ n : ℕ, ((a * b ^ n : kˣ) : k) + 1 + (((a * b ^ n)⁻¹ : kˣ) : k) = 0) :
    (b : k) ^ 2 - 1 = 0 := by
  have h' : ∀ n : ℕ, ((a : k) * b ^ n) ^ 2 + a * b ^ n + 1 = 0 := fun n => by
    have e := (a * b ^ n).mul_inv
    have e' := h n
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at e e'
    linear_combination ((a : k) * b ^ n) * e' - e
  by_contra hb
  have hb1 : (b : k) - 1 ≠ 0 := fun e => hb (by linear_combination ((b : k) + 1) * e)
  have e1 : (a : k) * b + a + 1 = 0 := mul_left_cancel₀ (mul_ne_zero a.ne_zero hb1) (by linear_combination h' 1 - h' 0)
  have e2 : (a : k) * b ^ 2 + a + 1 = 0 := mul_left_cancel₀ (mul_ne_zero a.ne_zero hb) (by linear_combination h' 2 - h' 0)
  exact mul_ne_zero (mul_ne_zero a.ne_zero b.ne_zero) hb1 (by linear_combination e2 - e1)

/- English proof (translation)
Simplify using `[conjBy, GG.mat, hg]`.
-/
private theorem conj_mat {G R : Type} [Group G] [CommRing R] (h : GL (Fin 3) R) (r : G →* GG 3 R) {g : G}
    (hg : (r g).right = 1) : (conjBy h r g).mat = (h : Matrix _ _ R) * (r g).mat * ((h⁻¹ : GL (Fin 3) R) : Matrix _ _ R) := by
  simp [conjBy, GG.mat, hg]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨h, -, htri⟩` from `ht`. Use `set P : GL (Fin 3) K := GeneralLinearGroup.map (j : A →+* K) h⁻¹ with hP`. Establish `em : ∀ s, mats (UpperTheory.V.UnitaryThreeInertia.push j r') s = (r' s).mat.map j` using `fun _ => rfl`. Establish `key : ∀ s : D, η s = 1 → (P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') s * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K) = (conjBy h⁻¹ (r'.comp D.subtype) s).mat.map j` using `fun s hs => by`.

Rewrite using `[conj_mat h⁻¹ (r'.comp D.subtype) (g := s) ((hpt.mult _).trans hs), hP, ← map_inv, em]`. Use `symm`. Use `(Matrix.map_mul (f := (j : A →+* K))).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul]`. Both sides reduce to the same expression.

Establish `tri : ∀ s : D, η s = 1 → ((P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') s * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K)).BlockTriangular id` using `fun s hs i j hij => by`. Rewrite using `[key s hs, map_apply, htri.tri s hs i j (by`. Establish `: (j : ℕ) < i` using `hij`. Simplify using `only [wt, wt1]`. Use the proof step `omega), map_zero]`.

Establish `hu1 : η u = 1` using `hU huU`. Establish `hinj : Function.Injective ((P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') u * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K)).diag`. Introduce `i j hij`. Rewrite `hij` using `[diag_apply, diag_apply, key u hu1, map_apply, map_apply, htri.ine u hu hu1, htri.ine u hu hu1, AlgHom.commutes, AlgHom.commutes]`. Establish `e : Ψ u ^ wt1 i = Ψ u ^ wt1 j` using `Units.ext (FaithfulSMul.algebraMap_injective O K hij)`.

Generalize the expression as in `Ψ u = y at e hu'`. Establish `h1 : y ≠ 1` using `fun h => hu' (by rw [h, one_pow])`. Establish `h2 : y ≠ y⁻¹` using `fun h => hu' (by rw [sq, ← eq_inv_iff_mul_eq_one]; exact h)`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [wt1, h1, h2, h1.symm, h2.symm] at e ⊢`. Take `⟨g, hg, hz⟩` from `core' η.ker U hU (mats (UpperTheory.V.UnitaryThreeInertia.push j r')) (fun a ha b _ => by`.

Establish `: (UpperTheory.V.UnitaryThreeInertia.push j r' a).right = 1` using `(hpt.mult a).trans ha`. Simplify using `only [mats, GG.mat, map_mul, SemidirectProduct.mul_left, this, sgnAct_one, Units.val_mul])`. Use the proof step `(by simp only [mats, GG.mat, map_one, SemidirectProduct.one_left, Units.val_one]) P.inv_mul P.mul_inv huU (tri u hu1) hinj`. Use `hI hc (x := x.1) hx (tri x hx)`. Set `φ : O →+* ResidueField A` to `(residue A).comp (algebraMap O A)`.

Use `(hx'.map φ).ne_zero ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_pow, map_one]`. Use `roots (Units.map φ.toMonoidHom (Ψ g)) (Units.map φ.toMonoidHom (Ψ x)) fun n => ?_` and prove the remaining obligations. Establish `e` using `hz n`. Rewrite using `[← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_inv]`.

Generalize the expression as in `g * x.1 ^ n = y at e`. Establish `e1 : (r' y).mat.trace = 0`. Use `hj ?_` and prove the remaining obligations. Rewrite using `[map_zero, ← e, trace, trace, map_sum]`. Both sides reduce to the same expression.

Establish `e2 : ∀ i, residue A ((r' y).mat i i) = φ ((r0 η Ψ y).mat i i)` using `fun i => Ideal.Quotient.eq.2 (hpt.red y i i)`. Establish `e3` using `congrArg (residue A) e1`. Rewrite `e3` using `[trace_fin_three, map_add, map_add, e2, e2, e2, map_zero]`. Simplify `e3` using `[GG.mat, tor_val, wt1]`.
-/
private theorem frame {O A K G : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Field K]
    [Algebra O K] [FaithfulSMul O K] [Group G] (j : A →ₐ[O] K) (hj : Function.Injective j) (η : G →* ℤˣ) (Ψ : G →* Oˣ)
    (D : Subgroup G) (I : Subgroup D) (r' : G →* GG 3 A) (hpt : Red η Ψ r')
    (ht : CondT (η.comp D.subtype) (Ψ.comp D.subtype) I (r'.comp D.subtype))
    (hI : TypeI η (UpperTheory.V.UnitaryThreeInertia.push j r')) (U : Subgroup G) [U.Normal]
    (hU : U ≤ η.ker) (x : D) (hx : η x = 1) (hx' : IsUnit ((Ψ x : O) ^ 2 - 1))
    (u : D) (hu : u ∈ I) (huU : u.1 ∈ U) (hu' : Ψ u ^ 2 ≠ 1) : MatIrr U (mats (UpperTheory.V.UnitaryThreeInertia.push j r')) := by
  by_contra hc
  obtain ⟨h, -, htri⟩ := ht
  set P : GL (Fin 3) K := GeneralLinearGroup.map (j : A →+* K) h⁻¹ with hP
  have em : ∀ s, mats (UpperTheory.V.UnitaryThreeInertia.push j r') s = (r' s).mat.map j := fun _ => rfl
  have key : ∀ s : D, η s = 1 → (P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') s * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K) =
      (conjBy h⁻¹ (r'.comp D.subtype) s).mat.map j := fun s hs => by
    rw [conj_mat h⁻¹ (r'.comp D.subtype) (g := s) ((hpt.mult _).trans hs), hP, ← map_inv, em]
    symm
    refine (Matrix.map_mul (f := (j : A →+* K))).trans ?_
    rw [Matrix.map_mul]
    rfl
  have tri : ∀ s : D, η s = 1 →
      ((P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') s * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K)).BlockTriangular id :=
    fun s hs i j hij => by
    rw [key s hs, map_apply, htri.tri s hs i j (by
      have : (j : ℕ) < i := hij
      simp only [wt, wt1]
      omega), map_zero]
  have hu1 : η u = 1 := hU huU
  have hinj : Function.Injective
      ((P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') u * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K)).diag := by
    intro i j hij
    rw [diag_apply, diag_apply, key u hu1, map_apply, map_apply, htri.ine u hu hu1, htri.ine u hu hu1,
      AlgHom.commutes, AlgHom.commutes] at hij
    have e : Ψ u ^ wt1 i = Ψ u ^ wt1 j := Units.ext (FaithfulSMul.algebraMap_injective O K hij)
    generalize Ψ u = y at e hu'
    have h1 : y ≠ 1 := fun h => hu' (by rw [h, one_pow])
    have h2 : y ≠ y⁻¹ := fun h => hu' (by rw [sq, ← eq_inv_iff_mul_eq_one]; exact h)
    fin_cases i <;> fin_cases j <;> simp [wt1, h1, h2, h1.symm, h2.symm] at e ⊢
  obtain ⟨g, hg, hz⟩ := core' η.ker U hU (mats (UpperTheory.V.UnitaryThreeInertia.push j r')) (fun a ha b _ => by
      have : (UpperTheory.V.UnitaryThreeInertia.push j r' a).right = 1 := (hpt.mult a).trans ha
      simp only [mats, GG.mat, map_mul, SemidirectProduct.mul_left, this, sgnAct_one, Units.val_mul])
    (by simp only [mats, GG.mat, map_one, SemidirectProduct.one_left, Units.val_one]) P.inv_mul P.mul_inv huU (tri u hu1) hinj
    hI hc (x := x.1) hx (tri x hx)
  let φ : O →+* ResidueField A := (residue A).comp (algebraMap O A)
  refine (hx'.map φ).ne_zero ?_
  rw [map_sub, map_pow, map_one]
  refine roots (Units.map φ.toMonoidHom (Ψ g)) (Units.map φ.toMonoidHom (Ψ x)) fun n => ?_
  have e := hz n
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_inv]
  generalize g * x.1 ^ n = y at e
  have e1 : (r' y).mat.trace = 0 := by
    refine hj ?_
    rw [map_zero, ← e, trace, trace, map_sum]
    rfl
  have e2 : ∀ i, residue A ((r' y).mat i i) = φ ((r0 η Ψ y).mat i i) := fun i =>
    Ideal.Quotient.eq.2 (hpt.red y i i)
  have e3 := congrArg (residue A) e1
  rw [trace_fin_three, map_add, map_add, e2, e2, e2, map_zero] at e3
  simpa [GG.mat, tor_val, wt1] using e3

end SlopeTestRemainingChoices

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

/- English proof (translation)
Introduce `Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ _ B hv A _ _ r hr hI U hU hUη`. Establish `: IsGalois ℚ Ω` using `IsAlgClosure.isGalois ℚ Ω`. Establish `: CompactSpace (G ℚ Ω)` using `inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))`. Establish `: Finite (G ℚ Ω ⧸ U)` using `U.quotient_finite_of_isOpen hU`. Establish `: U.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`.

Take `⟨hη, x, hx, hx'⟩` from `(dat_facts D).2.2.2.2.2.2.2.2.2.2 B hv`. Establish `hu : IsUnit (1 + (l : ℤ_[l]))`. Simplify `PadicInt.prime_p.not_unit)` using `using isUnit_one_sub_self_of_mem_nonunits (-(l : ℤ_[l])) (by simpa`. Take `⟨σ, hσ, hσ'⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B hv hu.unit`. Use `set m := U.normalCore.index * Nat.card (ZMod N)ˣ with hm`.

Establish `hm0 : m ≠ 0` using `mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Nat.card_pos.ne'`. Establish `hσm : σ ^ m ∈ Ine (F` using `ℚ) B := pow_mem hσ m`. Establish `key` using `frame A.val Subtype.val_injective D.η D.Ψ _ _ r hr.red hr.ord hI U.normalCore (U.normalCore_le.trans hUη) ⟨x, Ine_le_Dec B hx⟩ (hη hx) hx' ⟨σ ^ m, Ine_le_Dec B hσm⟩ (by rw [Subgroup.mem_subgroupOf]; exact hσm) (by show σ ^ m ∈ _`. Rewrite using `[hm, pow_mul]`. Conclude with `pow_mem (Subgroup.pow_index_mem _ σ) _)`.

Use the proof step `(by show Chr.Psi l e (Chr.dirG ℚ Ω ψ) (σ ^ m) ^ 2 ≠ 1`. Establish `h1 : Chr.dirG ℚ Ω ψ (σ ^ m) = 1`. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, map_pow, hm, pow_mul', pow_card_eq_one', one_pow, map_one]`. Rewrite using `[Chr.Psi, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, zpow_natCast, map_pow, ← pow_mul, ← pow_mul]`. Introduce `h`.

Establish `h2` using `congrArg (fun y : (c.O)ˣ => ((y : c.O) : PadicAlgCl l)) h`. Simplify using `only [Base.chiO, MonoidHom.comp_apply, hσ', Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec] at h2`. Establish `h3 : (((1 + l) ^ (m * (e * 2)) : ℕ) : PadicAlgCl l) = (1 : ℕ)` using `by simpa using h2`. Establish `h4` using `Nat.cast_injective h3`. Use `D.gd.e_pos` as an intermediate fact.

Use `hl.out.pos` as an intermediate fact. Rewrite `h4` using `[Nat.pow_eq_one]`. Break down `h4 with h4 | h4` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `mul_ne_zero hm0 (by omega) h4)`.

Conclude with `fun W hW => key W fun g hg => hW g (U.normalCore_le hg)`.
-/
theorem UpperTheory.V.Pr.matIrr_open_gd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ →
    ∀ (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), OrdPt l D.η D.Ψ D.cc g₁ B r → TypeI D.η (UnitaryThreeInertia.push A.val r) →
      ∀ V : Subgroup (G ℚ Ω), IsOpen (V : Set (G ℚ Ω)) → V ≤ D.η.ker → MatIrr V (mats (UnitaryThreeInertia.push A.val r)) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ _ B hv A _ _ r hr hI U hU hUη
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  have : Finite (G ℚ Ω ⧸ U) := U.quotient_finite_of_isOpen hU
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨hη, x, hx, hx'⟩ := (dat_facts D).2.2.2.2.2.2.2.2.2.2 B hv
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(l : ℤ_[l])) (by simpa using PadicInt.prime_p.not_unit)
  obtain ⟨σ, hσ, hσ'⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B hv hu.unit
  set m := U.normalCore.index * Nat.card (ZMod N)ˣ with hm
  have hm0 : m ≠ 0 := mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Nat.card_pos.ne'
  have hσm : σ ^ m ∈ Ine (F := ℚ) B := pow_mem hσ m
  have key := frame A.val Subtype.val_injective D.η D.Ψ _ _ r hr.red hr.ord hI U.normalCore
    (U.normalCore_le.trans hUη) ⟨x, Ine_le_Dec B hx⟩ (hη hx) hx' ⟨σ ^ m, Ine_le_Dec B hσm⟩
    (by rw [Subgroup.mem_subgroupOf]; exact hσm)
    (by
      show σ ^ m ∈ _
      rw [hm, pow_mul]
      exact pow_mem (Subgroup.pow_index_mem _ σ) _)
    (by
      show Chr.Psi l e (Chr.dirG ℚ Ω ψ) (σ ^ m) ^ 2 ≠ 1
      have h1 : Chr.dirG ℚ Ω ψ (σ ^ m) = 1 := by
        rw [Chr.dirG, MonoidHom.comp_apply, map_pow, hm, pow_mul', pow_card_eq_one', one_pow, map_one]
      rw [Chr.Psi, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, zpow_natCast, map_pow, ← pow_mul,
        ← pow_mul]
      intro h
      have h2 := congrArg (fun y : (c.O)ˣ => ((y : c.O) : PadicAlgCl l)) h
      simp only [Base.chiO, MonoidHom.comp_apply, hσ', Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec] at h2
      have h3 : (((1 + l) ^ (m * (e * 2)) : ℕ) : PadicAlgCl l) = (1 : ℕ) := by simpa using h2
      have h4 := Nat.cast_injective h3
      have := D.gd.e_pos
      have := hl.out.pos
      rw [Nat.pow_eq_one] at h4
      rcases h4 with h4 | h4
      · omega
      · exact mul_ne_zero hm0 (by omega) h4)
  exact fun W hW => key W fun g hg => hW g (U.normalCore_le hg)
