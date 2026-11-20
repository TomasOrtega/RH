import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Use `MulChar.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[H.dir_unit, dirChar_unit]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.Comparison₂.prim_read_dir (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) :
    H.dir (chr φ ψ) = dirChar (recH H) ψ := by
  refine MulChar.ext fun u => ?_
  rw [H.dir_unit, dirChar_unit]
  rfl

/- English proof (translation)
Establish `key : ∀ a : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = a`. Introduce `a`. Use `fin_cases a`. Apply the tactic sequence `exact ⟨1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩`. Apply the tactic sequence `exact ⟨-1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩`.

Introduce `x`. Take `⟨s1, hs1⟩` from `key (Multiplicative.toAdd x).1.1`. Take `⟨s2, hs2⟩` from `key (Multiplicative.toAdd x).1.2`. Use `⟨((s2, s1), Multiplicative.ofAdd (Multiplicative.toAdd x).2), ?_⟩` and prove the remaining obligations. Simplify using `only [toE, MonoidHom.coe_mk, OneHom.coe_mk, hs1, hs2]`.

Both sides reduce to the same expression.
-/
private theorem UpperTheory.Comparison₂.prim_read_surj (φ : Frame) : Function.Surjective (toE φ) := by
  have key : ∀ a : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = a := by
    intro a
    fin_cases a
    · exact ⟨1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
    · exact ⟨-1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
  intro x
  obtain ⟨s1, hs1⟩ := key (Multiplicative.toAdd x).1.1
  obtain ⟨s2, hs2⟩ := key (Multiplicative.toAdd x).1.2
  refine ⟨((s2, s1), Multiplicative.ofAdd (Multiplicative.toAdd x).2), ?_⟩
  simp only [toE, MonoidHom.coe_mk, OneHom.coe_mk, hs1, hs2]
  rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `Finset.mem_Icc.mp hn`. Establish `hpos : (0 : ℝ) < n` using `by exact_mod_cast h1`. Establish `hfl : 0 < ⌊y⌋₊` using `by omega`. Establish `hy : 1 ≤ y` using `Nat.floor_pos.mp hfl`. Establish `hny : (n : ℝ) ≤ y` using `(Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))`.

Establish `h1y : 1 ≤ y / n` using `(one_le_div hpos).mpr hny`. Conclude with `max_eq_left (by linarith)`.
-/
private theorem UpperTheory.Comparison₂.prim_read_max (y : ℝ) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊y⌋₊) :
    max (y / n - 1) 0 = y / n - 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hfl : 0 < ⌊y⌋₊ := by omega
  have hy : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  have h1y : 1 ≤ y / n := (one_le_div hpos).mpr hny
  exact max_eq_left (by linarith)

/- English proof (translation)
Unfold `Gz Sz An.G`. Rewrite using `[Finset.sum_congr rfl fun n hn => congrArg (fun t => An.abelian₂ n * t) (UpperTheory.Comparison₂.prim_read_max y n hn)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.Comparison₂.prim_read_Gz (y : ℝ) : Gz y = An.G y := by
  unfold Gz Sz An.G
  rw [Finset.sum_congr rfl fun n hn => congrArg (fun t => An.abelian₂ n * t) (UpperTheory.Comparison₂.prim_read_max y n hn)]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← DirichletCharacter.changeLevel_primitiveCharacter χ, h, map_one]`. Introduce and unpack `rfl`. Conclude with `DirichletCharacter.primitiveCharacter_one`.
-/
private theorem UpperTheory.Comparison₂.prim_read_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

/- English proof (translation)
Introduce `φ H ell hell ψ`. Unfold `HostAddCharCompatible at hell`. Use `set R := H.toHostRaw with hR`. Establish `hdir : R.dir (chr φ ψ) = dirChar (recH R) ψ` using `prim_read_dir φ R ψ`. Establish `hval : ∀ n : ℕ, n ≠ 0 → (R.prim (chr φ ψ)).χ n = primVal (arith R) ψ n`.

Introduce `n hn`. Use `show (R.dir (chr φ ψ)).primitiveCharacter n = _`. Rewrite using `[hdir]`. Conclude with `(primitive_value_primitive (H := φ.A) R.condN R.q R.d (recH R) ψ n (HostRaw.condN_pos R).ne' hn).symm`. Establish `h1 : ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (R.prim (chr φ ψ)).χ` using `fun hψ => @hell ψ hψ _ (R.prim (chr φ ψ)).ne _ (R.prim (chr φ ψ)).prim hval`.

Establish `hone : (R.prim (chr φ ψ)).χ = 1 ↔ ψ = 0` using `by show (R.dir (chr φ ψ)).primitiveCharacter = 1 ↔ ψ = 0`. Rewrite using `[prim_read_one, hdir]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[AddChar.eq_zero_iff]`.

Introduce `x`. Take `⟨g, hg⟩` from `prim_read_surj φ (Multiplicative.ofAdd x)`. Take `⟨u, hu⟩` from `HostDer.art_surj H.der g`. Establish `hu1 : (dirChar (recH R) ψ) u = 1`. Rewrite using `[h]`.

Conclude with `MulChar.one_apply_coe u`. Rewrite `hu1` using `[dirChar_unit]`. Establish `e : recH R u = Multiplicative.ofAdd x` using `by show toE φ (R.art u) = _`. Rewrite using `[hu, hg]`. Rewrite `hu1` using `[e, toAdd_ofAdd]`. Then use the resulting hypothesis.

Introduce and unpack `rfl`. Use `MulChar.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[dirChar_unit, AddChar.zero_apply, MulChar.one_apply_coe]`. Use `⟨h1, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hψ : ψ = 0`.

Establish `hχ : (R.prim (chr φ ψ)).χ = 1` using `hone.mpr hψ`. Unfold `GPsi An.gChi`. Rewrite using `[if_pos hψ, if_pos hχ, prim_read_Gz]`. Establish `hχ : (R.prim (chr φ ψ)).χ ≠ 1` using `fun h => hψ (hone.mp h)`. Unfold `GPsi An.gChi`.

Rewrite using `[if_neg hψ, if_neg hχ, ← h1 hψ, An.sumLamChi]`. Use `congr 1`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Establish `hn0 : n ≠ 0`. Use `(Finset.mem_Icc.mp hn).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hval n hn0, prim_read_max y n hn]`.
-/
theorem UpperTheory.Comparison₂.prim_read :
    ∀ (φ : Frame) (H : HostAx φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), HostAddCharCompatible H.toHostRaw ell → ∀ ψ : AddChar (E0 × φ.A) ℂ,
      (ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (H.toHostRaw.prim (chr φ ψ)).χ) ∧
        ∀ y, GPsi (arith H.toHostRaw) ell ψ y = An.gChi (H.toHostRaw.prim (chr φ ψ)).χ y := by
  intro φ H ell hell ψ
  unfold HostAddCharCompatible at hell
  set R := H.toHostRaw with hR
  have hdir : R.dir (chr φ ψ) = dirChar (recH R) ψ := prim_read_dir φ R ψ
  have hval : ∀ n : ℕ, n ≠ 0 → (R.prim (chr φ ψ)).χ n = primVal (arith R) ψ n := by
    intro n hn
    show (R.dir (chr φ ψ)).primitiveCharacter n = _
    rw [hdir]
    exact (primitive_value_primitive (H := φ.A) R.condN R.q R.d (recH R) ψ n
      (HostRaw.condN_pos R).ne' hn).symm
  have h1 : ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (R.prim (chr φ ψ)).χ := fun hψ =>
    @hell ψ hψ _ (R.prim (chr φ ψ)).ne _ (R.prim (chr φ ψ)).prim hval
  have hone : (R.prim (chr φ ψ)).χ = 1 ↔ ψ = 0 := by
    show (R.dir (chr φ ψ)).primitiveCharacter = 1 ↔ ψ = 0
    rw [prim_read_one, hdir]
    constructor
    · intro h
      rw [AddChar.eq_zero_iff]
      intro x
      obtain ⟨g, hg⟩ := prim_read_surj φ (Multiplicative.ofAdd x)
      obtain ⟨u, hu⟩ := HostDer.art_surj H.der g
      have hu1 : (dirChar (recH R) ψ) u = 1 := by
        rw [h]
        exact MulChar.one_apply_coe u
      rw [dirChar_unit] at hu1
      have e : recH R u = Multiplicative.ofAdd x := by
        show toE φ (R.art u) = _
        rw [hu, hg]
      rwa [e, toAdd_ofAdd] at hu1
    · rintro rfl
      refine MulChar.ext fun u => ?_
      rw [dirChar_unit, AddChar.zero_apply, MulChar.one_apply_coe]
  refine ⟨h1, fun y => ?_⟩
  by_cases hψ : ψ = 0
  · have hχ : (R.prim (chr φ ψ)).χ = 1 := hone.mpr hψ
    unfold GPsi An.gChi
    rw [if_pos hψ, if_pos hχ, prim_read_Gz]
  · have hχ : (R.prim (chr φ ψ)).χ ≠ 1 := fun h => hψ (hone.mp h)
    unfold GPsi An.gChi
    rw [if_neg hψ, if_neg hχ, ← h1 hψ, An.sumLamChi]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [hval n hn0, prim_read_max y n hn]
