import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace MaximumPrincipleOneFunction

variable {n : ℕ}

/- English proof (translation)
Take `⟨-, -, hmem, -, -, hX⟩` from `hB3g n ε`. Establish `hXp` using `hX p hp`. Use `hB3 (fun t => u (g0 * NormedSpace.exp (t • Xp p.1 p.2)) - A * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r - η * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1)) (fun t => u' t - A * v' t - η * w' t) _ ?_ ?_ ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun t => ?_` and prove the remaining obligations. Establish `h0 : g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2) = g0` using `by simp`.

Use `show _ ≤ u (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2)) - A * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ r - η * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ (r + 1)`. Rewrite using `[h0]`. Conclude with `hmax _ (hmem g0 hg0 _ hXp t)`. Introduce `t`. Conclude with `((hu' t).sub ((hv' t).const_mul A)).sub ((hw' t).const_mul η)`.

Conclude with `(hd.sub (hv''.const_mul A)).sub (hw''.const_mul η)`.
-/
theorem step (hB3 : B3) (hB3g : UnitaryGroupFacts) (ε : Fin n → Bool) (r : ℕ) (u : Matrix (Fin n) (Fin n) ℂ → ℝ) (A η : ℝ)
    (g0 : Matrix (Fin n) (Fin n) ℂ)
    (hmax : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
      u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1))
    (hg0 : g0 ∈ UJset ε) (p : Fin n × Fin n) (hp : p ∈ nc ε)
    (u' : ℝ → ℝ) (d : ℝ)
    (hu' : ∀ t, HasDerivAt (fun t : ℝ => u (g0 * NormedSpace.exp (t • Xp p.1 p.2))) (u' t) t)
    (hd : HasDerivAt u' d 0)
    (v' : ℝ → ℝ) (v'' : ℝ)
    (hv' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r) (v' t) t)
    (hv'' : HasDerivAt v' v'' 0)
    (w' : ℝ → ℝ) (w'' : ℝ)
    (hw' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1)) (w' t) t)
    (hw'' : HasDerivAt w' w'' 0) :
    d - A * v'' - η * w'' ≤ 0 := by
  obtain ⟨-, -, hmem, -, -, hX⟩ := hB3g n ε
  have hXp := hX p hp
  refine hB3 (fun t => u (g0 * NormedSpace.exp (t • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1))
    (fun t => u' t - A * v' t - η * w' t) _ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    have h0 : g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2) = g0 := by simp
    show _ ≤ u (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ (r + 1)
    rw [h0]
    exact hmax _ (hmem g0 hg0 _ hXp t)
  · intro t
    exact ((hu' t).sub ((hv' t).const_mul A)).sub ((hw' t).const_mul η)
  · exact (hd.sub (hv''.const_mul A)).sub (hw''.const_mul η)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity`.
-/
theorem hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

end MaximumPrincipleOneFunction

open MaximumPrincipleOneFunction in
/- English proof (translation)
Introduce `hB2 hB3 hB3g n ε r`. Use `choose cf hcf0 hcf using hB2`. Establish `hcr0 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) r` using `Finset.sum_nonneg fun p _ => hcf0 _ _ _`. Establish `hcr10 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)` using `Finset.sum_nonneg fun p _ => hcf0 _ _ _`. Use `⟨(∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1, by linarith, ?_⟩` and prove the remaining obligations.

Introduce `u A hA hcont hgrowth hsub`. Take `⟨C, hC⟩` from `hgrowth`. Take `⟨hcpt, h1, hmem, -, hhs, hX⟩` from `hB3g n ε`. Establish `key : ∀ η : ℝ, 0 < η → u 1 ≤ A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r + η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)`. Introduce `η hη`.

Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Establish `hW : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => 1 + hs2 g` using `continuous_const.add hhs`. Establish `hK` using `hcpt (|C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ))`. Establish `hKne : ({g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} : Set _).Nonempty` using `⟨1, h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩`.

Establish `hψc : ContinuousOn (fun g => u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1)) {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)}`. Establish `hu : ContinuousOn u {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)}` using `hcont.mono fun g hg => hg.1`. Conclude with `(hu.sub (continuous_const.mul (hW.pow r)).continuousOn).sub (continuous_const.mul (hW.pow (r + 1))).continuousOn`. Take `⟨g0, hg0K, hg0max⟩` from `hK.exists_isMaxOn hKne hψc`. Establish `hψ1 : u 1 - A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r - η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) ≤ u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1)` using `hg0max ⟨h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩`.

Establish `hglob : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤ u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1)`. Introduce `g hg`. Distinguish the cases in `hgρ : hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)`. Conclude with `hg0max ⟨hg, hgρ⟩`. Use `push Not at hgρ`.

Establish `hs1` using `hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)`. Establish `hsg` using `hilbert_schmidt_nonneg_alt g`. Establish `hlt : |C| / η < 1 + hs2 g` using `by linarith`. Establish `hCl : C < η * (1 + hs2 g)`. Use `(div_lt_iff₀ hη).mp hlt` as an intermediate fact.

Use `le_abs_self C` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hWr : 0 < (1 + hs2 g) ^ r` using `pow_pos (by linarith) r`. Establish `hAW : 0 ≤ A * (1 + hs2 g) ^ r` using `mul_nonneg hA hWr.le`. Establish `hug` using `hC g hg`.

Establish `hprod` using `mul_pos hWr (sub_pos.mpr hCl)`. Rewrite using `[pow_succ]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hg0 : g0 ∈ UJset ε` using `hg0K.1`. Take `⟨d, hd, hdsum⟩` from `hsub g0 hg0`.

Establish `hW0` using `hilbert_schmidt_nonneg_alt g0`. Establish `hWr : 0 < (1 + hs2 g0) ^ r` using `pow_pos (by linarith) r`. Establish `hWr1 : 0 < (1 + hs2 g0) ^ (r + 1)` using `pow_pos (by linarith) (r + 1)`. Establish `hp : ∀ p ∈ nc ε, d p ≤ A * cf n (Xp p.1 p.2) r * (1 + hs2 g0) ^ r + η * cf n (Xp p.1 p.2) (r + 1) * (1 + hs2 g0) ^ (r + 1)`. Introduce `p hp`.

Take `⟨u', hu', hdp⟩` from `hd p hp`. Take `⟨v', v'', hv', hv'', hvb⟩` from `hcf n (Xp p.1 p.2) r g0`. Take `⟨w', w'', hw', hw'', hwb⟩` from `hcf n (Xp p.1 p.2) (r + 1) g0`. Establish `hst` using `step hB3 hB3g ε r u A η g0 hglob hg0 p hp u' (d p) hu' hdp v' v'' hv' hv'' w' w'' hw' hw''`. Establish `h1` using `mul_le_mul_of_nonneg_left hvb hA`.

Establish `h2` using `mul_le_mul_of_nonneg_left hwb hη.le`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum : ∑ p ∈ nc ε, d p ≤ A * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) * (1 + hs2 g0) ^ r + η * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) * (1 + hs2 g0) ^ (r + 1)`. Use `(Finset.sum_le_sum hp).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]`.

Establish `hpos : 0 < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hug0 : A * (1 + hs2 g0) ^ r + η * (1 + hs2 g0) ^ (r + 1) < u g0` using `by linarith`. Establish `hm` using `mul_lt_mul_of_pos_left hug0 hpos`. Establish `e1` using `mul_nonneg hcr10 (mul_nonneg hA hWr.le)`.

Establish `e2` using `mul_pos (by linarith : (0:ℝ) < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + 1) (mul_pos hη hWr1)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hW1 : 0 < (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)` using `pow_pos (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) (r + 1)`. Use `le_of_forall_pos_le_add fun δ hδ => ?_` and prove the remaining obligations. Use `key (δ / (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)) (div_pos hδ hW1)` as an intermediate fact.

Rewrite `this` using `[div_mul_cancel₀ _ hW1.ne']`. Then use the resulting hypothesis.
-/
theorem maximum_principle_of_facts : B2 → B3 → UnitaryGroupFacts → MaximumPrincipleVar := by
  intro hB2 hB3 hB3g n ε r
  choose cf hcf0 hcf using hB2
  have hcr0 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) r := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  have hcr10 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1) := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  refine ⟨(∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1, by linarith, ?_⟩
  intro u A hA hcont hgrowth hsub
  obtain ⟨C, hC⟩ := hgrowth
  obtain ⟨hcpt, h1, hmem, -, hhs, hX⟩ := hB3g n ε
  have key : ∀ η : ℝ, 0 < η → u 1 ≤ A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r +
      η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) := by
    intro η hη
    by_contra hneg
    push Not at hneg
    have hW : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => 1 + hs2 g := continuous_const.add hhs
    have hK := hcpt (|C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ))
    have hKne : ({g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} : Set _).Nonempty :=
      ⟨1, h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hψc : ContinuousOn (fun g => u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1))
        {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} := by
      have hu : ContinuousOn u {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} :=
        hcont.mono fun g hg => hg.1
      exact (hu.sub (continuous_const.mul (hW.pow r)).continuousOn).sub
        (continuous_const.mul (hW.pow (r + 1))).continuousOn
    obtain ⟨g0, hg0K, hg0max⟩ := hK.exists_isMaxOn hKne hψc
    have hψ1 : u 1 - A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r -
        η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) :=
      hg0max ⟨h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hglob : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) := by
      intro g hg
      by_cases hgρ : hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)
      · exact hg0max ⟨hg, hgρ⟩
      · push Not at hgρ
        have hs1 := hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)
        have hsg := hilbert_schmidt_nonneg_alt g
        have hlt : |C| / η < 1 + hs2 g := by linarith
        have hCl : C < η * (1 + hs2 g) := by
          have := (div_lt_iff₀ hη).mp hlt
          have := le_abs_self C
          linarith
        have hWr : 0 < (1 + hs2 g) ^ r := pow_pos (by linarith) r
        have hAW : 0 ≤ A * (1 + hs2 g) ^ r := mul_nonneg hA hWr.le
        have hug := hC g hg
        have hprod := mul_pos hWr (sub_pos.mpr hCl)
        rw [pow_succ]
        nlinarith
    have hg0 : g0 ∈ UJset ε := hg0K.1
    obtain ⟨d, hd, hdsum⟩ := hsub g0 hg0
    have hW0 := hilbert_schmidt_nonneg_alt g0
    have hWr : 0 < (1 + hs2 g0) ^ r := pow_pos (by linarith) r
    have hWr1 : 0 < (1 + hs2 g0) ^ (r + 1) := pow_pos (by linarith) (r + 1)
    have hp : ∀ p ∈ nc ε, d p ≤ A * cf n (Xp p.1 p.2) r * (1 + hs2 g0) ^ r +
        η * cf n (Xp p.1 p.2) (r + 1) * (1 + hs2 g0) ^ (r + 1) := by
      intro p hp
      obtain ⟨u', hu', hdp⟩ := hd p hp
      obtain ⟨v', v'', hv', hv'', hvb⟩ := hcf n (Xp p.1 p.2) r g0
      obtain ⟨w', w'', hw', hw'', hwb⟩ := hcf n (Xp p.1 p.2) (r + 1) g0
      have hst := step hB3 hB3g ε r u A η g0 hglob hg0 p hp u' (d p) hu' hdp v' v'' hv' hv'' w' w'' hw' hw''
      have h1 := mul_le_mul_of_nonneg_left hvb hA
      have h2 := mul_le_mul_of_nonneg_left hwb hη.le
      nlinarith
    have hsum : ∑ p ∈ nc ε, d p ≤ A * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) * (1 + hs2 g0) ^ r +
        η * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) * (1 + hs2 g0) ^ (r + 1) := by
      refine (Finset.sum_le_sum hp).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpos : 0 < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1 := by
      linarith
    have hug0 : A * (1 + hs2 g0) ^ r + η * (1 + hs2 g0) ^ (r + 1) < u g0 := by linarith
    have hm := mul_lt_mul_of_pos_left hug0 hpos
    have e1 := mul_nonneg hcr10 (mul_nonneg hA hWr.le)
    have e2 := mul_pos (by linarith : (0:ℝ) < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + 1) (mul_pos hη hWr1)
    nlinarith
  have hW1 : 0 < (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) :=
    pow_pos (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) (r + 1)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have := key (δ / (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)) (div_pos hδ hW1)
  rwa [div_mul_cancel₀ _ hW1.ne'] at this

end PositivityTheory.CW

end
