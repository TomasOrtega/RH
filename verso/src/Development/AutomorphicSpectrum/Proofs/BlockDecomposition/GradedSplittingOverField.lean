import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrSplitField

/- English proof (translation)
Establish `hQ : (pdP γ (i + 1)).restrictScalars K ≤ (pdP γ i).restrictScalars K` using `fun x hx => (Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, (Nat.le_succ i).trans hr, hz⟩ : pdP γ (i + 1) ≤ pdP γ i) hx`. Take `⟨c, hc⟩` from `exists_isCompl (⟨(pdP γ (i + 1)).restrictScalars K, hQ⟩ : Set.Iic ((pdP γ i).restrictScalars K))`. Establish `hinf : (pdP γ (i + 1)).restrictScalars K ⊓ c.1 = ⊥` using `congrArg Subtype.val hc.inf_eq_bot`. Establish `hsup : (pdP γ (i + 1)).restrictScalars K ⊔ c.1 = (pdP γ i).restrictScalars K` using `congrArg Subtype.val hc.sup_eq_top`. Use `⟨c.1, fun n hn => c.2 hn, fun n hn hn' => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `: n ∈ (pdP γ (i + 1)).restrictScalars K ⊓ c.1` using `⟨hn', hn⟩`. Rewrite `this` using `[hinf]`. Simplify using `using this`. Establish `hx' : x ∈ (pdP γ (i + 1)).restrictScalars K ⊔ c.1`. Rewrite using `[hsup]`.

Conclude with `hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx'`. Conclude with `⟨z, hz, by simpa using hy⟩`.
-/
theorem exists_step {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B}
    (γ : DividedPowers I) (i : ℕ) :
    ∃ C : Submodule K B, (∀ n ∈ C, n ∈ pdP γ i) ∧ (∀ n ∈ C, n ∈ pdP γ (i + 1) → n = 0) ∧
      ∀ x ∈ pdP γ i, ∃ n ∈ C, x - n ∈ pdP γ (i + 1) := by
  have hQ : (pdP γ (i + 1)).restrictScalars K ≤ (pdP γ i).restrictScalars K :=
    fun x hx => (Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, (Nat.le_succ i).trans hr, hz⟩ :
      pdP γ (i + 1) ≤ pdP γ i) hx
  obtain ⟨c, hc⟩ := exists_isCompl
    (⟨(pdP γ (i + 1)).restrictScalars K, hQ⟩ : Set.Iic ((pdP γ i).restrictScalars K))
  have hinf : (pdP γ (i + 1)).restrictScalars K ⊓ c.1 = ⊥ := congrArg Subtype.val hc.inf_eq_bot
  have hsup : (pdP γ (i + 1)).restrictScalars K ⊔ c.1 = (pdP γ i).restrictScalars K :=
    congrArg Subtype.val hc.sup_eq_top
  refine ⟨c.1, fun n hn => c.2 hn, fun n hn hn' => ?_, fun x hx => ?_⟩
  · have : n ∈ (pdP γ (i + 1)).restrictScalars K ⊓ c.1 := ⟨hn', hn⟩
    rw [hinf] at this
    simpa using this
  · have hx' : x ∈ (pdP γ (i + 1)).restrictScalars K ⊔ c.1 := by
      rw [hsup]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    exact ⟨z, hz, by simpa using hy⟩

/- English proof (translation)
Introduce `K B _ _ _ I γ m hm`. Use `choose C hC₁ hC₂ hC₃ using fun i : ℕ => exists_step (K := K) γ i`. Conclude with `⟨{ N := fun i => C i ν := fun i => (C i).subtype mem := fun i n => hC₁ i n n.2 inj := fun i n h => Subtype.ext (hC₂ i n n.2 h) surj := fun i x hx => by`. Take `⟨n, hn, h⟩` from `hC₃ i x hx`. Conclude with `⟨⟨n, hn⟩, h⟩`.

Use `nil := hm }⟩`.
-/
theorem nonempty_grSplit : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  intro K B _ _ _ I γ m hm
  choose C hC₁ hC₂ hC₃ using fun i : ℕ => exists_step (K := K) γ i
  exact ⟨{
    N := fun i => C i
    ν := fun i => (C i).subtype
    mem := fun i n => hC₁ i n n.2
    inj := fun i n h => Subtype.ext (hC₂ i n n.2 h)
    surj := fun i x hx => by
      obtain ⟨n, hn, h⟩ := hC₃ i x hx
      exact ⟨⟨n, hn⟩, h⟩
    nil := hm }⟩

end GlobalTheory.CompanionTheory.GrSplitField
