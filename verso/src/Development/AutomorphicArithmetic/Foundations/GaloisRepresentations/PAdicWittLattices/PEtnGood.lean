import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Use function extensionality and compare the values at `Ω _ _ x`. Establish `hx` using `h.2.2 Ω x`. Simplify using `only [UpperTheory.Gal.TranscendenceTraces.Wt.push, UpperTheory.Gal.TranscendenceTraces.Wt.const]`. Establish `hne : Nat.card {y // y ≫ c = x} ≠ 0` using `by rw [hx]; exact hd`. Establish `hfin : Finite {y // y ≫ c = x}` using `Nat.finite_of_card_ne_zero hne`.

Establish `hs : (UpperTheory.Gal.TranscendenceTraces.fib c x).Finite` using `Set.finite_coe_iff.mp hfin`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, nsmul_eq_mul, mul_one, ← Set.ncard_eq_toFinset_card _ hs, ← Nat.card_coe_set_eq]`. Conclude with `hx` after adjusting the coercions.
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
Introduce `hF hT l _ B hl n i`. Take `⟨hW, -, hA⟩` from `UpperTheory.Gal.TranscendenceTraces.all_holds`. Establish `hFlat : UpperTheory.Gal.TranscendenceTraces.WtFlat` using `hW.2.2.2.2.2.2.2.2.2.1`. Establish `hMult : UpperTheory.Gal.TranscendenceTraces.MultBasic` using `hW.2.2.2.2.2.2.2.1`. Establish `hDeg : UpperTheory.Gal.TranscendenceTraces.TrDegQ` using `hA.2.2.2.2.1`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `Z W p r c hc G _ _ a hG`. Establish `hd : FEt c (Nat.card G)` using `hF.2.2 c G a hG`. Establish `hpos : Nat.card G ≠ 0` using `Nat.card_pos.ne'`. Establish `hpush` using `push_one_eq c _ hpos hd`.

Take `⟨hfin, het, -⟩` from `hd`. Establish `hwt : UpperTheory.Gal.TranscendenceTraces.IsWt c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1)`. Establish `h1` using `hFlat c`. Rewrite `h1` using `[hMult.2.2 c]`. Then use the resulting hypothesis. Establish `hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤))`.

Use `hl.map p.appTop.hom` as an intermediate fact. Simplify using `using this`. Establish `key` using `hDeg l n i c _ _ hwt hlZ hpush`. Establish `hne : (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) ≠ 0`. Conclude with `hpos` after adjusting the coercions.

Introduce `x y hxy`. Establish `hxy' : pullHQ l (sch.map c) n i x = pullHQ l (sch.map c) n i y` using `hxy`. Establish `e : ∀ t, UpperTheory.Gal.TranscendenceTraces.trHQ l c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) n i (pullHQ l (sch.map c) n i t) = (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) • t` using `fun t => LinearMap.congr_fun key t`. Establish `ex` using `e x`. Rewrite `ex` using `[hxy', e y]`.

Conclude with `smul_right_injective _ hne ex.symm`. Introduce `Z Y p q s _ _ _`. Conclude with `⟨_, hT l B hl n i p q s⟩`.
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
