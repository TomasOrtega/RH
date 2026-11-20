import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.PrimRead
import Development.AutomorphicArithmetic.PrimitiveCosets.PrimInj
import Development.AutomorphicArithmetic.PrimitiveCosets.ChrBij
import Development.AutomorphicArithmetic.PrimitiveCosets.GzEq

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Unfold both sides to obtain the same proposition, which implies itself.
-/
private theorem UpperTheory.Comparison₂.character_trivial_on_generator_iff (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (s : φ.A) :
    chr φ ψ (φ.tau1 s) = 1 ↔ ψ (0, s) = 1 := by
  rw [← Units.val_eq_one, (chr_bij φ).2.2.2.2.1 ψ (φ.tau1 s)]
  simp [toE, Frame.tau1, Frame.iotaInv, Frame.iota]
  exact Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
