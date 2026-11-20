import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem chr_val (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (g : φ.GG) :
    ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g)) := rfl

/- English proof (translation)
Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Establish `h0 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 1) = 0`. Rewrite using `[map_one, toAdd_one]`. Rewrite using `[if_pos h0]`. Simplify using the standard rewrite rules.

Establish `h1 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (-1)) = 1` using `by decide`. Rewrite using `[h1, if_neg (by decide)]`. Simplify using the standard rewrite rules.
-/
private theorem sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · have h0 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 1) = 0 := by
      rw [map_one, toAdd_one]
    rw [if_pos h0]
    simp
  · have h1 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := by decide
    rw [h1, if_neg (by decide)]
    simp

/- English proof (translation)
Introduce `φ`. Take `⟨hbij, hiod, -, htau, -⟩` from `toE_bij φ`. Establish `trivA : ∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)`. Introduce `ψ`. Establish `key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s)`.

Introduce `s`. Rewrite using `[chr_val, htau]`. Both sides reduce to the same expression. Simplify using `only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce `h s hs`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one, key]`. Conclude with `h s hs`. Introduce `h s hs`.

Establish `h2` using `congrArg Units.val (h s hs)`. Rewrite `h2` using `[key, Units.val_one]`. Conclude with `h2`. Set `e` to `MulEquiv.ofBijective (toE φ) hbij`. Establish `he : ∀ g, e g = toE φ g` using `fun g => rfl`.

Use `⟨⟨?_, ?_⟩, ?_, ?_, ?_, chr_val φ, trivA, ?_⟩` and prove the remaining obligations. Introduce `ψ ψ' h`. Apply `AddChar.ext` to reduce the goal to its premises. Introduce `a`. Take `⟨g, hg⟩` from `hbij.2 (Multiplicative.ofAdd a)`.

Establish `h2` using `congrArg (fun θ : φ.Char => ((θ g : ℂˣ) : ℂ)) h`. Simplify using `only [chr_val, hg, toAdd_ofAdd] at h2`. Conclude with `h2`. Introduce `θ`. Set `ψ : AddChar (E0 × φ.A) ℂ` to `{ toFun := fun a => ((θ (e.symm (Multiplicative.ofAdd a)) : ℂˣ) : ℂ) map_zero_eq_one' := by`.

Simplify using `only [ofAdd_zero, map_one, Units.val_one]`. Use the proof step `map_add_eq_mul' := by`. Introduce `a b`. Simplify using `only [ofAdd_add, map_mul, Units.val_mul] }`. Use `⟨ψ, ?_⟩` and prove the remaining obligations.

Use `MonoidHom.ext fun g => Units.ext ?_` and prove the remaining obligations. Rewrite using `[chr_val]`. Use `show ((θ (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (toE φ g)))) : ℂˣ) : ℂ) = _`. Rewrite using `[ofAdd_toAdd, ← he, MulEquiv.symm_apply_apply]`. Use `MonoidHom.ext fun g => Units.ext ?_` and prove the remaining obligations.

Rewrite using `[chr_val, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]`. Use `MonoidHom.ext fun g => Units.ext ?_` and prove the remaining obligations. Rewrite using `[chr_val]`. Use `show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.2) = 0 then (1 : ℂ) else -1) = _`. Rewrite using `[sgn_val]`.

Simplify using `[Frame.chC, Frame.chD]`. Use `MonoidHom.ext fun g => Units.ext ?_` and prove the remaining obligations. Rewrite using `[chr_val]`. Use `show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.1) = 0 then (1 : ℂ) else -1) = _`. Rewrite using `[sgn_val]`.

Simplify using `[Frame.psC, Frame.chQ]`. Introduce `ψ`. Establish `hv : ((chr φ ψ φ.iod : ℂˣ) : ℂ) = ψ sgc0`. Rewrite using `[chr_val, hiod]`. Both sides reduce to the same expression.

Simplify using `only [Frame.Xp, Set.mem_setOf_eq]`. Rewrite using `[← trivA]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hv, h2, Units.val_one]`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hv, h2, Units.val_one]`.
-/
theorem UpperTheory.Comparison₂.chr_bij :
    ∀ φ : Frame, Function.Bijective (chr φ) ∧ chr φ 0 = 1 ∧ chr φ chC = φ.chC ∧ chr φ psC = φ.psC ∧
      (∀ ψ g, ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g))) ∧
      (∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)) ∧ ∀ ψ, chr φ ψ ∈ φ.Xp ↔ (ψ ∈ PsiA φ.A0 ∧ ψ sgc0 = 1) := by
  intro φ
  obtain ⟨hbij, hiod, -, htau, -⟩ := toE_bij φ
  have trivA : ∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ) := by
    intro ψ
    have key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s) := by
      intro s
      rw [chr_val, htau]
      rfl
    simp only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h s hs
      apply Units.ext
      rw [Units.val_one, key]
      exact h s hs
    · intro h s hs
      have h2 := congrArg Units.val (h s hs)
      rw [key, Units.val_one] at h2
      exact h2
  let e := MulEquiv.ofBijective (toE φ) hbij
  have he : ∀ g, e g = toE φ g := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, chr_val φ, trivA, ?_⟩
  · intro ψ ψ' h
    apply AddChar.ext
    intro a
    obtain ⟨g, hg⟩ := hbij.2 (Multiplicative.ofAdd a)
    have h2 := congrArg (fun θ : φ.Char => ((θ g : ℂˣ) : ℂ)) h
    simp only [chr_val, hg, toAdd_ofAdd] at h2
    exact h2
  · intro θ
    let ψ : AddChar (E0 × φ.A) ℂ :=
      { toFun := fun a => ((θ (e.symm (Multiplicative.ofAdd a)) : ℂˣ) : ℂ)
        map_zero_eq_one' := by
          simp only [ofAdd_zero, map_one, Units.val_one]
        map_add_eq_mul' := by
          intro a b
          simp only [ofAdd_add, map_mul, Units.val_mul] }
    refine ⟨ψ, ?_⟩
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show ((θ (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (toE φ g)))) : ℂˣ) : ℂ) = _
    rw [ofAdd_toAdd, ← he, MulEquiv.symm_apply_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.2) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.chC, Frame.chD]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.1) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.psC, Frame.chQ]
  · intro ψ
    have hv : ((chr φ ψ φ.iod : ℂˣ) : ℂ) = ψ sgc0 := by
      rw [chr_val, hiod]
      rfl
    simp only [Frame.Xp, Set.mem_setOf_eq]
    rw [← trivA]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← hv, h2, Units.val_one]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Units.ext ?_⟩
      rw [hv, h2, Units.val_one]
