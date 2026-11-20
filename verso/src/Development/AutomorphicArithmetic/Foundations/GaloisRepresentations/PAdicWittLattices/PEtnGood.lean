import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem push_one_eq {W Z : Scheme.{0}} (c : W ⟶ Z) (d : ℕ) (hd : d ≠ 0) (h : FEt c d) :
    (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1).push c = UpperTheory.Gal.TranscendenceTraces.Wt.const Z (d : ℤ) := by
  funext Ω _ _ x
  have hx := h.2.2 Ω x
  simp only [UpperTheory.Gal.TranscendenceTraces.Wt.push, UpperTheory.Gal.TranscendenceTraces.Wt.const]
  have hne : Nat.card {y // y ≫ c = x} ≠ 0 := by rw [hx]; exact hd
  have hfin : Finite {y // y ≫ c = x} := Nat.finite_of_card_ne_zero hne
  have hs : (UpperTheory.Gal.TranscendenceTraces.fib c x).Finite := Set.finite_coe_iff.mp hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Set.ncard_eq_toFinset_card _ hs, ← Nat.card_coe_set_eq]
  exact_mod_cast hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G3.pEtnGood :
    FEtBasic → EtTr → EtnGood := by
  intro hF hT l _ B hl n i
  obtain ⟨hW, -, hA⟩ := UpperTheory.Gal.TranscendenceTraces.all_holds
  have hFlat : UpperTheory.Gal.TranscendenceTraces.WtFlat := hW.2.2.2.2.2.2.2.2.2.1
  have hMult : UpperTheory.Gal.TranscendenceTraces.MultBasic := hW.2.2.2.2.2.2.2.1
  have hDeg : UpperTheory.Gal.TranscendenceTraces.TrDegQ := hA.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hG
    have hd : FEt c (Nat.card G) := hF.2.2 c G a hG
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hpush := push_one_eq c _ hpos hd
    obtain ⟨hfin, het, -⟩ := hd
    have hwt : UpperTheory.Gal.TranscendenceTraces.IsWt c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) := by
      have h1 := hFlat c
      rwa [hMult.2.2 c] at h1
    have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
      have := hl.map p.appTop.hom
      simpa using this
    have key := hDeg l n i c _ _ hwt hlZ hpush
    have hne : (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) ≠ 0 := by
      exact_mod_cast hpos
    intro x y hxy
    have hxy' : pullHQ l (sch.map c) n i x = pullHQ l (sch.map c) n i y := hxy
    have e : ∀ t, UpperTheory.Gal.TranscendenceTraces.trHQ l c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) n i (pullHQ l (sch.map c) n i t) =
        (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) • t := fun t => LinearMap.congr_fun key t
    have ex := e x
    rw [hxy', e y] at ex
    exact smul_right_injective _ hne ex.symm
  · intro Z Y p q s _ _ _
    exact ⟨_, hT l B hl n i p q s⟩
