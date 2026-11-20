import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection

/- English proof (translation)
Introduce `L _ N j ca cb U X' s hcb hblk hU hT hd hne hX`. Establish `hlt : ca < cb` using `by rw [Fin.lt_def]; omega`. Establish `hne' : cb ≠ ca` using `hlt.ne'`. Establish `hR : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N), (M * Matrix.single cb ca t) r c = if c = ca then M r cb * t else 0`. Introduce `M t r c`.

Distinguish the cases in `h : c = ca`. Substitute `h` using the available equality. Simplify using `[Matrix.mul_apply, Matrix.single_apply]`. Simplify using `[Matrix.mul_apply, h, Ne.symm h]`. Establish `hL : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N), (Matrix.single cb ca t * M) r c = if r = cb then t * M ca c else 0`.

Introduce `M t r c`. Distinguish the cases in `h : r = cb`. Substitute `h` using the available equality. Simplify using `[Matrix.mul_apply, Matrix.single_apply]`. Simplify using `[Matrix.mul_apply, h, Ne.symm h]`.

Establish `hW : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U) r c = U r c + if r = cb then -X' * U ca c else 0`. Introduce `r c`. Rewrite using `[add_mul, one_mul, Matrix.add_apply, hL]`. Establish `hV : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s)) r c = U r c + (if r = cb then -X' * U ca c else 0) + if c = ca then (U r cb + if r = cb then -X' * U ca cb else 0) * s else 0`. Introduce `r c`.

Rewrite using `[mul_add, mul_one, Matrix.add_apply, hR, hW, hW]`. Establish `hTv : ∀ t : L, IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) L)`. Introduce `t a b h`. Establish `hab : a ≠ b`. Introduce and unpack `rfl`.

Conclude with `h Iff.rfl`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, zero_add]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h hblk.symm`.

Use `⟨(1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s), ((hTv _).mul hU).mul (hTv _), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r c hrc`. Establish `hrc' : c < r` using `hrc`. Rewrite using `[hV]`. Distinguish the cases in `hc : c = ca`.

Substitute `hc` using the available equality. Distinguish the cases in `hr : r = cb`. Substitute `hr` using the available equality. Establish `h0 : U r c = 0` using `hT hrc`. Simplify using `only [if_true, h0]`.

Take the linear combination `-hX`. Establish `hcr : cb < r`. Rewrite `hrc'`, the goal using `[Fin.lt_def]`. Establish `: (r : ℕ) ≠ cb` using `fun h => hr (Fin.ext h)`. Use linear arithmetic over natural numbers and integers.

Establish `h0 : U r c = 0` using `hT hrc`. Establish `h1 : U r cb = 0` using `hT hcr`. Simplify using `[hr, h0, h1]`. Distinguish the cases in `hr : r = cb`. Substitute `hr` using the available equality.

Establish `hcca : c < ca`. Rewrite `hrc'`, the goal using `[Fin.lt_def]`. Establish `: (c : ℕ) ≠ ca` using `fun h => hc (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Establish `h0 : U r c = 0` using `hT hrc`.

Establish `h1 : U ca c = 0` using `hT hcca`. Simplify using `[hc, h0, h1]`. Establish `h0 : U r c = 0` using `hT hrc`. Simplify using `[hc, hr, h0]`. Introduce `c hc`.

Rewrite using `[hV]`. Distinguish the cases in `hca : c = ca`. Substitute `hca` using the available equality. Simplify using `only [if_true, if_neg hc, add_zero]`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Take the linear combination `h`. Simplify `hd c` using `[hc, hca]`. Establish `hinv : (1 + Matrix.single cb ca X') * (1 + Matrix.single cb ca (-X')) = (1 : Matrix (Fin N) (Fin N) L)`. Establish `h0 : Matrix.single cb ca X' * Matrix.single cb ca (-X') = (0 : Matrix (Fin N) (Fin N) L)`.

Use extensionality with `r c`. Rewrite using `[hL, Matrix.single_apply]`. Simplify using `[hne']`. Rewrite using `[add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h0, add_zero, add_assoc, ← Matrix.single_add]`. Simplify using the standard rewrite rules.

Rewrite using `[← mul_assoc, ← mul_assoc, hinv, one_mul]`.
-/
theorem exists_conj : ∀ (L : Type) [Field L] (N j : ℕ) (ca cb : Fin N) (U : Matrix (Fin N) (Fin N) L) (X' s : L), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → U ca ca + s * U ca cb ≠ 0 → X' * (U ca ca + s * U ca cb) = s * U cb cb → ∃ V : Matrix (Fin N) (Fin N) L, IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c, c ≠ cb → V c c ≠ 0) ∧ (1 + Matrix.single cb ca X') * V = U * (1 + Matrix.single cb ca s) := by
  intro L _ N j ca cb U X' s hcb hblk hU hT hd hne hX
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne' : cb ≠ ca := hlt.ne'
  have hR : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (M * Matrix.single cb ca t) r c = if c = ca then M r cb * t else 0 := by
    intro M t r c
    by_cases h : c = ca
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hL : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (Matrix.single cb ca t * M) r c = if r = cb then t * M ca c else 0 := by
    intro M t r c
    by_cases h : r = cb
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hW : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U) r c
      = U r c + if r = cb then -X' * U ca c else 0 := by
    intro r c
    rw [add_mul, one_mul, Matrix.add_apply, hL]
  have hV : ∀ r c : Fin N,
      ((1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s)) r c
      = U r c + (if r = cb then -X' * U ca c else 0)
        + if c = ca then (U r cb + if r = cb then -X' * U ca cb else 0) * s else 0 := by
    intro r c
    rw [mul_add, mul_one, Matrix.add_apply, hR, hW, hW]
  have hTv : ∀ t : L, IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) L) := by
    intro t a b h
    have hab : a ≠ b := by
      rintro rfl
      exact h Iff.rfl
    rw [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, zero_add]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h hblk.symm
  refine ⟨(1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s),
    ((hTv _).mul hU).mul (hTv _), ?_, ?_, ?_⟩
  · intro r c hrc
    have hrc' : c < r := hrc
    rw [hV]
    by_cases hc : c = ca
    · subst hc
      by_cases hr : r = cb
      · subst hr
        have h0 : U r c = 0 := hT hrc
        simp only [if_true, h0]
        linear_combination -hX
      · have hcr : cb < r := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (r : ℕ) ≠ cb := fun h => hr (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U r cb = 0 := hT hcr
        simp [hr, h0, h1]
    · by_cases hr : r = cb
      · subst hr
        have hcca : c < ca := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U ca c = 0 := hT hcca
        simp [hc, h0, h1]
      · have h0 : U r c = 0 := hT hrc
        simp [hc, hr, h0]
  · intro c hc
    rw [hV]
    by_cases hca : c = ca
    · subst hca
      simp only [if_true, if_neg hc, add_zero]
      intro h
      apply hne
      linear_combination h
    · simpa [hc, hca] using hd c
  · have hinv : (1 + Matrix.single cb ca X') * (1 + Matrix.single cb ca (-X'))
        = (1 : Matrix (Fin N) (Fin N) L) := by
      have h0 : Matrix.single cb ca X' * Matrix.single cb ca (-X')
          = (0 : Matrix (Fin N) (Fin N) L) := by
        ext r c
        rw [hL, Matrix.single_apply]
        simp [hne']
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h0, add_zero, add_assoc,
        ← Matrix.single_add]
      simp
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection
