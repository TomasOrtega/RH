import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.PrimRead
import Development.AutomorphicArithmetic.PrimitiveCosets.PrimInj
import Development.AutomorphicArithmetic.PrimitiveCosets.ChrBij
import Development.AutomorphicArithmetic.PrimitiveCosets.GzEq

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Rewrite using `[← Units.val_eq_one, (chr_bij φ).2.2.2.2.1 ψ (φ.tau1 s)]`. Simplify using `[toE, Frame.tau1, Frame.iotaInv, Frame.iota]`. Conclude with `Iff.rfl`.
-/
private theorem UpperTheory.Comparison₂.character_trivial_on_generator_iff (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (s : φ.A) :
    chr φ ψ (φ.tau1 s) = 1 ↔ ψ (0, s) = 1 := by
  rw [← Units.val_eq_one, (chr_bij φ).2.2.2.2.1 ψ (φ.tau1 s)]
  simp [toE, Frame.tau1, Frame.iotaInv, Frame.iota]
  exact Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hM : ∀ m : φ.MA, θ ((1, 1), m) = 1` using `fun m => h (Multiplicative.toAdd m)`. Establish `hB : ∀ b : ℤˣ, θ ((1, b), 1) = 1`. Introduce `b`.

Break down `Int.units_eq_one_or b with rfl | rfl` into its components or cases. Conclude with `θ.map_one`. Conclude with `hi`. Establish `hred : ∀ (a b : ℤˣ) (m : φ.MA), θ ((a, b), m) = θ ((a, 1), 1)`. Introduce `a b m`.

Establish `e : (((a, b), m) : φ.GG) = ((a, 1), 1) * ((1, b), 1) * ((1, 1), m)`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[e, map_mul, map_mul, hM, hB, mul_one, mul_one]`. Establish `hsq : (θ φ.sg : ℂ) * (θ φ.sg : ℂ) = 1`. Rewrite using `[← Units.val_mul, ← map_mul]`.

Establish `e : φ.sg * φ.sg = 1`. Simplify using `only [Frame.sg]`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[e, map_one, Units.val_one]`. Break down `mul_self_eq_one_iff.mp hsq with h1 | h1` into its components or cases.

Use `left`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Take `⟨⟨a, b⟩, m⟩` from `g`. Rewrite using `[hred]`. Apply `Units.ext` to reduce the goal to its premises.

Break down `Int.units_eq_one_or a with rfl | rfl` into its components or cases. Rewrite using `[hB 1]`. Simplify using the standard rewrite rules. Simplify `h1` using `[Frame.sg]`. Use `right`.

Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Take `⟨⟨a, b⟩, m⟩` from `g`. Rewrite using `[hred]`. Apply `Units.ext` to reduce the goal to its premises. Break down `Int.units_eq_one_or a with rfl | rfl` into its components or cases.

Rewrite using `[hB 1]`. Simplify using `[Frame.psC, Frame.chQ]`. Simplify `h1` using `[Frame.psC, Frame.chQ, Frame.sg]`. Introduce and unpack `(rfl | rfl) h`. Simplify using the standard rewrite rules.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[Frame.psC, Frame.chQ, Frame.tau1]`.
-/
private theorem UpperTheory.Comparison₂.gmA_eq_triv (φ : Frame) (θ : φ.Char) (hi : θ φ.iod = 1) :
    (∀ h : φ.A, θ (φ.tau1 h) = 1) ↔ θ = 1 ∨ θ = φ.psC := by
  constructor
  · intro h
    have hM : ∀ m : φ.MA, θ ((1, 1), m) = 1 := fun m => h (Multiplicative.toAdd m)
    have hB : ∀ b : ℤˣ, θ ((1, b), 1) = 1 := by
      intro b
      rcases Int.units_eq_one_or b with rfl | rfl
      · exact θ.map_one
      · exact hi
    have hred : ∀ (a b : ℤˣ) (m : φ.MA), θ ((a, b), m) = θ ((a, 1), 1) := by
      intro a b m
      have e : (((a, b), m) : φ.GG) = ((a, 1), 1) * ((1, b), 1) * ((1, 1), m) := by
        ext <;> simp
      rw [e, map_mul, map_mul, hM, hB, mul_one, mul_one]
    have hsq : (θ φ.sg : ℂ) * (θ φ.sg : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      have e : φ.sg * φ.sg = 1 := by
        simp only [Frame.sg]
        ext <;> simp
      rw [e, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp
      · simpa [Frame.sg] using h1
    · right
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp [Frame.psC, Frame.chQ]
      · simpa [Frame.psC, Frame.chQ, Frame.sg] using h1
  · rintro (rfl | rfl) h
    · simp
    · apply Units.ext
      simp [Frame.psC, Frame.chQ, Frame.tau1]

/- English proof (translation)
Introduce `Λ φ H TT x eps C ell hE hell y`. Take `⟨hbij, -, -, -, -⟩` from `chr_bij φ`. Take `⟨hpinj, hp1⟩` from `prim_inj φ H`. Establish `hmem : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw ↔ H.prim (chr φ ψ) ∈ Λ.KEPT`. Introduce `ψ`.

Simplify using `[keptA, HostRaw.kept_iff]`. Establish `hXp : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw → chr φ ψ ∈ φ.Xp`. Introduce `ψ hψ`. Take `⟨θ, hθ, hpr⟩` from `hE.kept _ ((hmem ψ).1 hψ)`. Rewrite `hpr` using `[HostRaw.isPrimOf_iff]`.

Establish `e` using `hpinj hpr`. Rewrite using `[e]`. Conclude with `hθ`. Establish `hKimg : Λ.KEPT = (keptA Λ H.toHostRaw).image (fun ψ => H.prim (chr φ ψ))`. Use extensionality with `p`.

Simplify using `only [Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Take `⟨θ, -, hpr⟩` from `hE.kept p hp`. Rewrite `hpr` using `[HostRaw.isPrimOf_iff]`.

Take `⟨ψ, rfl⟩` from `hbij.2 θ`. Use `⟨ψ, (hmem ψ).2 ?_, hpr.symm⟩` and prove the remaining obligations. Rewrite using `[← hpr]`. Conclude with `hp`. Introduce and unpack `⟨ψ, hψ, rfl⟩`.

Conclude with `(hmem ψ).1 hψ`. Establish `hinj : Set.InjOn (fun ψ => H.prim (chr φ ψ)) (keptA Λ H.toHostRaw)` using `fun a _ b _ h => hbij.1 (hpinj h)`. Establish `hw : ∀ ψ ∈ keptA Λ H.toHostRaw, wtA (3 * (Λ.o : ℝ) + 1)⁻¹ ψ = (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ)))`. Introduce `ψ hψ`. Establish `hiod : chr φ ψ φ.iod = 1` using `(hXp ψ hψ).2`.

Establish `htriv : (∀ h : φ.A, ψ (0, h) = 1) ↔ chr φ ψ = 1 ∨ chr φ ψ = φ.psC`. Rewrite using `[← gmA_eq_triv φ (chr φ ψ) hiod]`. Conclude with `forall_congr' fun h => (character_trivial_on_generator_iff φ ψ h).symm`. Take `⟨hps1, hps2⟩` from `hE.ps`. Unfold `wtA`.

Distinguish the cases in `hA : ∀ h : φ.A, ψ (0, h) = 1`. Rewrite using `[if_pos hA]`. Break down `htriv.1 hA with h1 | h1` into its components or cases. Rewrite using `[h1, hp1, if_pos rfl]`. Establish `hK : H.toHostRaw.Kept Λ.KEPT φ.psC`.

Rewrite using `[HostRaw.kept_iff, ← h1]`. Conclude with `(hmem ψ).1 hψ`. Rewrite using `[h1]`. Use `split_ifs with hone`. Both sides reduce to the same expression.

Consider the cases of `hk : Λ.psK with`. Consider the case `none => exact absurd hK (hps2 hk)`. Consider the case `some p`. Establish `e` using `hps1 p hk`. Rewrite `e` using `[HostRaw.isPrimOf_iff]`.

Simplify using `[Level.wt, hk, e]`. Rewrite using `[if_neg hA]`. Establish `hn1 : chr φ ψ ≠ 1` using `fun h => hA (htriv.2 (Or.inl h))`. Establish `hnps : chr φ ψ ≠ φ.psC` using `fun h => hA (htriv.2 (Or.inr h))`. Rewrite using `[if_neg (fun h => hn1 (hpinj (h.trans hp1.symm)))]`.

Unfold `Level.wt`. Rewrite using `[if_neg]`. Introduce `hk`. Establish `e` using `hps1 _ hk`. Rewrite `e` using `[HostRaw.isPrimOf_iff]`.

Conclude with `hnps (hpinj e)`. Establish `hG : ∀ ψ, (GPsi (arith H.toHostRaw) ell ψ y).re = (An.gChi (H.prim (chr φ ψ)).χ y).re`. Introduce `ψ`. Rewrite using `[(prim_read φ H ell hell ψ).2 y]`. Establish `key : ∑ ψ ∈ keptA Λ H.toHostRaw, (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) * (An.gChi (H.prim (chr φ ψ)).χ y).re = ∑ p ∈ Λ.KEPT, (if p = PChar.one then 1 else Λ.wt p) * (An.gChi p.χ y).re`.

Rewrite using `[hKimg, Finset.sum_image hinj]`. Establish `hone : (An.gChi PChar.one.χ y).re = An.G y`. Establish `h1 : PChar.one.χ = 1` using `rfl`. Unfold `An.gChi`. Rewrite using `[if_pos h1]`.

Simplify using the standard rewrite rules. Unfold `GmA Level.Gm Level.Nt`. Rewrite using `[Finset.sum_congr rfl (fun ψ hψ => by rw [hw ψ hψ, hG ψ]), key, ← Finset.add_sum_erase _ _ Λ.one_mem]`. Use `congr 1`. Rewrite using `[if_pos rfl, one_mul, (Gz_eq y).1, hone]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`. Rewrite using `[if_neg (Finset.ne_of_mem_erase hp)]`.
-/
theorem UpperTheory.Comparison₂.gmA_eq :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ),
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell → ∀ y,
        GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y := by
  intro Λ φ H TT x eps C ell hE hell y
  classical
  obtain ⟨hbij, -, -, -, -⟩ := chr_bij φ
  obtain ⟨hpinj, hp1⟩ := prim_inj φ H
  have hmem : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw ↔ H.prim (chr φ ψ) ∈ Λ.KEPT := by
    intro ψ
    simp [keptA, HostRaw.kept_iff]
  have hXp : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw → chr φ ψ ∈ φ.Xp := by
    intro ψ hψ
    obtain ⟨θ, hθ, hpr⟩ := hE.kept _ ((hmem ψ).1 hψ)
    rw [HostRaw.isPrimOf_iff] at hpr
    have e := hpinj hpr
    rw [e]
    exact hθ
  have hKimg : Λ.KEPT = (keptA Λ H.toHostRaw).image (fun ψ => H.prim (chr φ ψ)) := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨θ, -, hpr⟩ := hE.kept p hp
      rw [HostRaw.isPrimOf_iff] at hpr
      obtain ⟨ψ, rfl⟩ := hbij.2 θ
      refine ⟨ψ, (hmem ψ).2 ?_, hpr.symm⟩
      rw [← hpr]
      exact hp
    · rintro ⟨ψ, hψ, rfl⟩
      exact (hmem ψ).1 hψ
  have hinj : Set.InjOn (fun ψ => H.prim (chr φ ψ)) (keptA Λ H.toHostRaw) :=
    fun a _ b _ h => hbij.1 (hpinj h)
  have hw : ∀ ψ ∈ keptA Λ H.toHostRaw, wtA (3 * (Λ.o : ℝ) + 1)⁻¹ ψ =
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) := by
    intro ψ hψ
    have hiod : chr φ ψ φ.iod = 1 := (hXp ψ hψ).2
    have htriv : (∀ h : φ.A, ψ (0, h) = 1) ↔ chr φ ψ = 1 ∨ chr φ ψ = φ.psC := by
      rw [← gmA_eq_triv φ (chr φ ψ) hiod]
      exact forall_congr' fun h => (character_trivial_on_generator_iff φ ψ h).symm
    obtain ⟨hps1, hps2⟩ := hE.ps
    unfold wtA
    by_cases hA : ∀ h : φ.A, ψ (0, h) = 1
    · rw [if_pos hA]
      rcases htriv.1 hA with h1 | h1
      · rw [h1, hp1, if_pos rfl]
      · have hK : H.toHostRaw.Kept Λ.KEPT φ.psC := by
          rw [HostRaw.kept_iff, ← h1]
          exact (hmem ψ).1 hψ
        rw [h1]
        split_ifs with hone
        · rfl
        · cases hk : Λ.psK with
          | none => exact absurd hK (hps2 hk)
          | some p =>
            have e := hps1 p hk
            rw [HostRaw.isPrimOf_iff] at e
            simp [Level.wt, hk, e]
    · rw [if_neg hA]
      have hn1 : chr φ ψ ≠ 1 := fun h => hA (htriv.2 (Or.inl h))
      have hnps : chr φ ψ ≠ φ.psC := fun h => hA (htriv.2 (Or.inr h))
      rw [if_neg (fun h => hn1 (hpinj (h.trans hp1.symm)))]
      unfold Level.wt
      rw [if_neg]
      intro hk
      have e := hps1 _ hk
      rw [HostRaw.isPrimOf_iff] at e
      exact hnps (hpinj e)
  have hG : ∀ ψ, (GPsi (arith H.toHostRaw) ell ψ y).re = (An.gChi (H.prim (chr φ ψ)).χ y).re := by
    intro ψ
    rw [(prim_read φ H ell hell ψ).2 y]
  have key : ∑ ψ ∈ keptA Λ H.toHostRaw,
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) *
        (An.gChi (H.prim (chr φ ψ)).χ y).re =
      ∑ p ∈ Λ.KEPT, (if p = PChar.one then 1 else Λ.wt p) * (An.gChi p.χ y).re := by
    rw [hKimg, Finset.sum_image hinj]
  have hone : (An.gChi PChar.one.χ y).re = An.G y := by
    have h1 : PChar.one.χ = 1 := rfl
    unfold An.gChi
    rw [if_pos h1]
    simp
  unfold GmA Level.Gm Level.Nt
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [hw ψ hψ, hG ψ]), key,
    ← Finset.add_sum_erase _ _ Λ.one_mem]
  congr 1
  · rw [if_pos rfl, one_mul, (Gz_eq y).1, hone]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_neg (Finset.ne_of_mem_erase hp)]
