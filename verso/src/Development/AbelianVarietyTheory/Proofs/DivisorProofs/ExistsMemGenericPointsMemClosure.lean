import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastBis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

/- English proof (translation)
Take `⟨u, hu, hxu⟩` from `exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton`. Establish `hc : IsClosed u` using `isClosed_of_mem_irreducibleComponents u hu`. Establish `hi : IsIrreducible u` using `hu.prop`. Establish `hg` using `hi.isGenericPoint_genericPoint_closure`. Rewrite `hg` using `[hc.closure_eq]`.

Use `⟨hi.genericPoint, ?_, ?_⟩` and prove the remaining obligations. Use `show closure {hi.genericPoint} ∈ irreducibleComponents X`. Rewrite using `[hg.def]`. Conclude with `hu`. Rewrite using `[hg.def]`.

Conclude with `hxu rfl`.
-/
theorem exists_mem_genericPoints_mem_closure (X : Scheme.{0}) (x : X) : ∃ η ∈ genericPoints X, x ∈ closure {η} := by
  obtain ⟨u, hu, hxu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  have hc : IsClosed u := isClosed_of_mem_irreducibleComponents u hu
  have hi : IsIrreducible u := hu.prop
  have hg := hi.isGenericPoint_genericPoint_closure
  rw [hc.closure_eq] at hg
  refine ⟨hi.genericPoint, ?_, ?_⟩
  · show closure {hi.genericPoint} ∈ irreducibleComponents X
    rw [hg.def]; exact hu
  · rw [hg.def]; exact hxu rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq l Xo c C x`. Take `⟨η, hη, hx⟩` from `exists_mem_genericPoints_mem_closure (Xo.XF c) x`. Take `⟨X, -, hX⟩` from `GlobalTheory.UPoinc.GSetup.exists_uSetup E H Dw hpq l Xo c C η hη 0`. Establish `hr : Set.range X.π = closure {C.i η}` using `GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X η _ hX rfl`. Establish `hxr : C.i x ∈ Set.range X.π`.

Rewrite using `[hr, ← specializes_iff_mem_closure]`. Conclude with `(specializes_iff_mem_closure.2 hx).map C.i.continuous`. Take `⟨w, hw⟩` from `hxr`. Take `⟨wi⟩` from `nonempty_uWit X`. Take `⟨U, c₀, hc, fg, frac, hth, hev, ρ', u', -, hwU, -, -, ⟨G, _, α, β, hα, hβ, hL, -⟩, hu'⟩` from `GlobalTheory.UPoinc.exists_urechart_affine E H Dw hpq l Xo c C X wi w ⟨x, hw.symm⟩`.

Set `X' : USetup C` to `{ o₁ := X.o₁ Ω₁ := X.Ω₁ S := X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev ρ := ρ' big := X.big u := u' pulled := ⟨G, _, α, β, hα, hβ, hL⟩ gen := fun v => by rw [hu']; exact X.gen v M := X.M normal := X.normal π := X.π fin := X.fin comp := by`. Rewrite using `[← Category.assoc, hu', X.comp]`. Simplify using `only [Category.assoc] }`. Conclude with `⟨X', w, hw, RatModel.ringOn_le_O (M := X.M) hwU⟩`.
-/
theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c),
      ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  intro E _ _ _ H Dw hpq l Xo c C x
  obtain ⟨η, hη, hx⟩ := exists_mem_genericPoints_mem_closure (Xo.XF c) x
  obtain ⟨X, -, hX⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup E H Dw hpq l Xo c C η hη 0
  have hr : Set.range X.π = closure {C.i η} := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X η _ hX rfl
  have hxr : C.i x ∈ Set.range X.π := by
    rw [hr, ← specializes_iff_mem_closure]
    exact (specializes_iff_mem_closure.2 hx).map C.i.continuous
  obtain ⟨w, hw⟩ := hxr
  obtain ⟨wi⟩ := nonempty_uWit X
  obtain ⟨U, c₀, hc, fg, frac, hth, hev, ρ', u', -, hwU, -, -, ⟨G, _, α, β, hα, hβ, hL, -⟩, hu'⟩ :=
    GlobalTheory.UPoinc.exists_urechart_affine E H Dw hpq l Xo c C X wi w ⟨x, hw.symm⟩
  let X' : USetup C :=
    { o₁ := X.o₁
      Ω₁ := X.Ω₁
      S := X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev
      ρ := ρ'
      big := X.big
      u := u'
      pulled := ⟨G, _, α, β, hα, hβ, hL⟩
      gen := fun v => by rw [hu']; exact X.gen v
      M := X.M
      normal := X.normal
      π := X.π
      fin := X.fin
      comp := by
        rw [← Category.assoc, hu', X.comp]
        simp only [Category.assoc] }
  exact ⟨X', w, hw, RatModel.ringOn_le_O (M := X.M) hwU⟩

end GlobalTheory.UPoinc
