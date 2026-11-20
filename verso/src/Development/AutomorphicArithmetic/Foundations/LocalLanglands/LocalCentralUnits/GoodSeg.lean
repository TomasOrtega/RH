import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

/- English proof (translation)
Introduce `k _ _ _ _ _`. Establish `huniq : ∀ (x : IrrGL k) (s s' : Multiset (IrrGL k)), HasSupport x.rep s → HasSupport x.rep s' → s = s'` using `fun x s s' hs hs' => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique PositivityTheory.Exh.geometricLemmaGL UpperTheory.Zero.LLC.Pr.bz hs hs'`. Establish `hgood : ∀ (x : IrrGL k) (s : Multiset (IrrGL k)), HasSupport x.rep s → (UpperTheory.Zero.LLC.Good x ↔ ∀ y ∈ s, UpperTheory.Zero.LLC.GoodCusp y)`. Introduce `x s hs`. Unfold `UpperTheory.Zero.LLC.Good`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, hy⟩`. Rewrite using `[huniq x s t hs ht]`. Conclude with `hy`. Introduce `hy`.

Conclude with `⟨s, hs, hy⟩`. Establish `htw : ∀ (y : IrrGL k) (a : ℂ), UpperTheory.Zero.LLC.GoodCusp (y.nu a) ↔ UpperTheory.Zero.LLC.GoodCusp y`. Introduce `y a`. Unfold `IrrGL.nu`. Conclude with `((UpperTheory.Zero.LLC.clBasic k y).2.1 _ _).2.2.1`.

Use `⟨?_, ?_, huniq⟩` and prove the remaining obligations. Introduce `l x hl`. Rewrite using `[hgood x _ (hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel k _ x hl)]`. Unfold `msupp`. Prove the components needed by the constructor for the conclusion.

Introduce `h Δ hΔ`. Establish `hmem : Δ.first.nu ((0 : ℕ) : ℂ) ∈ Δ.ms` using `Segment.mem_ms.mpr (Segment.mem_carrier.mpr ⟨0, Δ.len_pos, rfl⟩)`. Establish `hc` using `h _ (Multiset.mem_bind.mpr ⟨Δ, Multiset.mem_coe.mpr hΔ, hmem⟩)`. Conclude with `(htw _ _).mp hc`. Introduce `h y hy`.

Take `⟨Δ, hΔ, hy⟩` from `Multiset.mem_bind.mp hy`. Take `⟨a, _, rfl⟩` from `Segment.mem_carrier.mp (Segment.mem_ms.mp hy)`. Conclude with `(htw _ _).mpr (h Δ (Multiset.mem_coe.mp hΔ))`. Introduce `x hx`. Rewrite using `[hgood x {x} (hasSupport_self hx)]`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Zero.LLC.goodSeg :
    UpperTheory.Zero.LLC.GoodSeg := by
  intro k _ _ _ _ _
  have huniq : ∀ (x : IrrGL k) (s s' : Multiset (IrrGL k)),
      HasSupport x.rep s → HasSupport x.rep s' → s = s' :=
    fun x s s' hs hs' =>
      GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique PositivityTheory.Exh.geometricLemmaGL UpperTheory.Zero.LLC.Pr.bz hs hs'
  have hgood : ∀ (x : IrrGL k) (s : Multiset (IrrGL k)), HasSupport x.rep s →
      (UpperTheory.Zero.LLC.Good x ↔ ∀ y ∈ s, UpperTheory.Zero.LLC.GoodCusp y) := by
    intro x s hs
    unfold UpperTheory.Zero.LLC.Good
    constructor
    · rintro ⟨t, ht, hy⟩
      rw [huniq x s t hs ht]
      exact hy
    · intro hy
      exact ⟨s, hs, hy⟩
  have htw : ∀ (y : IrrGL k) (a : ℂ),
      UpperTheory.Zero.LLC.GoodCusp (y.nu a) ↔ UpperTheory.Zero.LLC.GoodCusp y := by
    intro y a
    unfold IrrGL.nu
    exact ((UpperTheory.Zero.LLC.clBasic k y).2.1 _ _).2.2.1
  refine ⟨?_, ?_, huniq⟩
  · intro l x hl
    rw [hgood x _ (hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel k _ x hl)]
    unfold msupp
    constructor
    · intro h Δ hΔ
      have hmem : Δ.first.nu ((0 : ℕ) : ℂ) ∈ Δ.ms :=
        Segment.mem_ms.mpr (Segment.mem_carrier.mpr ⟨0, Δ.len_pos, rfl⟩)
      have hc := h _ (Multiset.mem_bind.mpr ⟨Δ, Multiset.mem_coe.mpr hΔ, hmem⟩)
      exact (htw _ _).mp hc
    · intro h y hy
      obtain ⟨Δ, hΔ, hy⟩ := Multiset.mem_bind.mp hy
      obtain ⟨a, _, rfl⟩ := Segment.mem_carrier.mp (Segment.mem_ms.mp hy)
      exact (htw _ _).mpr (h Δ (Multiset.mem_coe.mp hΔ))
  · intro x hx
    rw [hgood x {x} (hasSupport_self hx)]
    simp
