import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StMobiusAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

/- English proof (translation)
Introduce `Ω _ Φ _ _ n a p q p' q' ha hdet`. Establish `hden : ∀ j, algebraMap Ω Φ p' + a j * algebraMap Ω Φ q' ≠ 0`. Introduce `j h`. Distinguish the cases in `hq' : q' = 0`. Substitute `hq'` using the available equality.

Establish `hp' : p' = 0` using `by simpa using h`. Conclude with `hdet (by simp [hp'])`. Apply `ha.transcendental j` to reduce the goal to its premises. Establish `hq : algebraMap Ω Φ q' ≠ 0` using `by simpa using hq'`. Establish `: a j = algebraMap Ω Φ (-p' / q')`.

Rewrite using `[map_div₀, map_neg]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Rewrite using `[this]`. Conclude with `isAlgebraic_algebraMap _`.

Use `⟨hden, ?_⟩` and prove the remaining obligations. Use `set b : Fin n → Φ := fun j => (algebraMap Ω Φ p + a j * algebraMap Ω Φ q) / (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') with hb`. Establish `hrel : ∀ j, (algebraMap Ω Φ q' * b j - algebraMap Ω Φ q) * a j = algebraMap Ω Φ p - algebraMap Ω Φ p' * b j`. Introduce `j`. Establish `hbD : b j * (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') = algebraMap Ω Φ p + a j * algebraMap Ω Φ q` using `div_mul_cancel₀ _ (hden j)`.

Take the linear combination `hbD`. Establish `hc : ∀ j, algebraMap Ω Φ q' * b j - algebraMap Ω Φ q ≠ 0`. Introduce `j h`. Establish `h2` using `hrel j`. Rewrite `h2` using `[h, zero_mul]`.

Apply `hdet` to reduce the goal to its premises. Apply `(algebraMap Ω Φ).injective` to reduce the goal to its premises. Simplify using `only [map_sub, map_mul, map_zero]`. Take the linear combination `algebraMap Ω Φ p' * h - algebraMap Ω Φ q' * h2`. Set `S : Set Φ` to `Set.range a ∪ Set.range b`.

Set `A` to `Algebra.adjoin Ω S`. Set `a' : Fin n → A` to `fun j => ⟨a j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩`. Set `b' : Fin n → A` to `fun j => ⟨b j, Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩`. Establish `ha' : AlgebraicIndependent Ω a'` using `AlgebraicIndependent.of_comp A.val ha`. Establish `halg : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range b')) A`.

Use `⟨fun z => ?_⟩` and prove the remaining obligations. Establish `hz : z ∈ Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S)`. Rewrite using `[Algebra.adjoin_adjoin_coe_preimage]`. Discharge the goal by the elementary cases of `trivial`. Use `IsAlgebraic.adjoin_of_forall_isAlgebraic (R := Ω) (s := ((↑) : A → Φ) ⁻¹' S) (t := Set.range b') ?_ (isAlgebraic_algebraMap (⟨z, hz⟩ : Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S)))` and prove the remaining obligations.

Introduce and unpack `x ⟨hxS, hxb⟩`. Break down `hxS with ⟨j, hj⟩ | ⟨j, hj⟩` into its components or cases. Establish `hx : x = a' j` using `Subtype.ext hj.symm`. Substitute `hx` using the available equality. Set `bj : Algebra.adjoin Ω (Set.range b')` to `⟨b' j, Algebra.subset_adjoin ⟨j, rfl⟩⟩`.

Set `c : Algebra.adjoin Ω (Set.range b')` to `algebraMap Ω _ q' * bj - algebraMap Ω _ q`. Set `d : Algebra.adjoin Ω (Set.range b')` to `algebraMap Ω _ p - algebraMap Ω _ p' * bj`. Use `IsAlgebraic.of_mul (y := algebraMap _ A c) ?_ (isAlgebraic_algebraMap c) ?_` and prove the remaining obligations. Apply `mem_nonZeroDivisors_of_ne_zero` to reduce the goal to its premises. Introduce `h0`.

Apply `hc j` to reduce the goal to its premises. Establish `h1` using `congrArg (fun w : A => (w : Φ)) h0`. Conclude with `h1`. Establish `h3 : algebraMap _ A c * a' j = algebraMap _ A d`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `hrel j`. Rewrite using `[h3]`. Conclude with `isAlgebraic_algebraMap d`. Conclude with `absurd ⟨j, Subtype.ext hj⟩ hxb`. Establish `hn : Cardinal.mk (Fin n) ≤ Algebra.trdeg Ω A` using `ha'.cardinalMk_le_trdeg`.

Establish `hT` using `Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω b' hn`. Conclude with `hT.1.map' (f := A.val) Subtype.val_injective`.
-/
theorem MobiusAlgIndep.proof : MobiusAlgIndep.Statement := by
  intro Ω _ Φ _ _ n a p q p' q' ha hdet
  have hden : ∀ j, algebraMap Ω Φ p' + a j * algebraMap Ω Φ q' ≠ 0 := by
    intro j h
    by_cases hq' : q' = 0
    · subst hq'
      have hp' : p' = 0 := by simpa using h
      exact hdet (by simp [hp'])
    · apply ha.transcendental j
      have hq : algebraMap Ω Φ q' ≠ 0 := by simpa using hq'
      have : a j = algebraMap Ω Φ (-p' / q') := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [this]
      exact isAlgebraic_algebraMap _
  refine ⟨hden, ?_⟩
  set b : Fin n → Φ := fun j => (algebraMap Ω Φ p + a j * algebraMap Ω Φ q) /
    (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') with hb

  have hrel : ∀ j, (algebraMap Ω Φ q' * b j - algebraMap Ω Φ q) * a j =
      algebraMap Ω Φ p - algebraMap Ω Φ p' * b j := by
    intro j
    have hbD : b j * (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') =
        algebraMap Ω Φ p + a j * algebraMap Ω Φ q := div_mul_cancel₀ _ (hden j)
    linear_combination hbD
  have hc : ∀ j, algebraMap Ω Φ q' * b j - algebraMap Ω Φ q ≠ 0 := by
    intro j h
    have h2 := hrel j
    rw [h, zero_mul] at h2
    apply hdet
    apply (algebraMap Ω Φ).injective
    simp only [map_sub, map_mul, map_zero]
    linear_combination algebraMap Ω Φ p' * h - algebraMap Ω Φ q' * h2

  let S : Set Φ := Set.range a ∪ Set.range b
  let A := Algebra.adjoin Ω S
  let a' : Fin n → A := fun j => ⟨a j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let b' : Fin n → A := fun j => ⟨b j, Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩
  have ha' : AlgebraicIndependent Ω a' := AlgebraicIndependent.of_comp A.val ha
  have halg : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range b')) A := by
    refine ⟨fun z => ?_⟩
    have hz : z ∈ Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S) := by
      rw [Algebra.adjoin_adjoin_coe_preimage]; trivial
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := Ω) (s := ((↑) : A → Φ) ⁻¹' S)
      (t := Set.range b') ?_ (isAlgebraic_algebraMap (⟨z, hz⟩ : Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S)))
    rintro x ⟨hxS, hxb⟩
    rcases hxS with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hx : x = a' j := Subtype.ext hj.symm
      subst hx
      let bj : Algebra.adjoin Ω (Set.range b') := ⟨b' j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
      let c : Algebra.adjoin Ω (Set.range b') :=
        algebraMap Ω _ q' * bj - algebraMap Ω _ q
      let d : Algebra.adjoin Ω (Set.range b') :=
        algebraMap Ω _ p - algebraMap Ω _ p' * bj
      refine IsAlgebraic.of_mul (y := algebraMap _ A c) ?_ (isAlgebraic_algebraMap c) ?_
      · apply mem_nonZeroDivisors_of_ne_zero
        intro h0
        apply hc j
        have h1 := congrArg (fun w : A => (w : Φ)) h0
        exact h1
      · have h3 : algebraMap _ A c * a' j = algebraMap _ A d := by
          apply Subtype.ext
          exact hrel j
        rw [h3]
        exact isAlgebraic_algebraMap d
    · exact absurd ⟨j, Subtype.ext hj⟩ hxb
  have hn : Cardinal.mk (Fin n) ≤ Algebra.trdeg Ω A := ha'.cardinalMk_le_trdeg
  have hT := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω b' hn
  exact hT.1.map' (f := A.val) Subtype.val_injective

end GroundTheory.Heights₂.Heights.Inter
