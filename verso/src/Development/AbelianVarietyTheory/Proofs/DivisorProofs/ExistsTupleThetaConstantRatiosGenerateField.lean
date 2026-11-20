import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

/- English proof (translation)
Take `⟨s, hs⟩` from `S.fg`. Take `⟨x₀, hx₀⟩` from `S.th_ne`. Set `t₀ : Option s → Ω` to `fun i => match i with | none => 1 | some y => (y : Ω)`. Use `⟨Option s, inferInstance, t₀, ⟨none, one_ne_zero⟩, ?_⟩` and prove the remaining obligations. Use `set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hK`.

Establish `hbase : ∀ a : o, algebraMap o Ω a ∈ K` using `fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)`. Establish `hgen : ∀ y ∈ s, y ∈ K`. Introduce `y hy`. Apply `Subfield.subset_closure` to reduce the goal to its premises. Use `Or.inr ⟨(x₀, none), (x₀, some ⟨y, hy⟩), ?_⟩` and prove the remaining obligations.

Simplify using `only [t₀, mul_one]`. Clear the denominators using the available nonvanishing facts. Set `KA : Subalgebra o Ω` to `{ K.toSubring with algebraMap_mem' := hbase }`. Establish `hR : S.R ≤ KA`. Rewrite using `[← hs]`.

Conclude with `Algebra.adjoin_le (fun y hy => hgen y hy)`. Establish `hall : ∀ x : Ω, x ∈ K`. Introduce `x`. Take `⟨a, ha, b, hb, rfl⟩` from `S.frac x`. Conclude with `K.div_mem (hR ha) (hR hb)`.

Use `⟨⟨{1}, eq_top_iff.mpr fun x _ => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Finset.coe_singleton]`. Rewrite using `[Submodule.mem_span_singleton]`. Conclude with `⟨⟨x, hall x⟩, by simp [Algebra.smul_def]; rfl⟩`.
-/
theorem thetaSys_gen_tuple (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) :
    ∃ (J₀ : Type) (_ : Fintype J₀) (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) ∧
      Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun i => match i with | none => 1 | some y => (y : Ω)
  refine ⟨Option s, inferInstance, t₀, ⟨none, one_ne_zero⟩, ?_⟩
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hK
  have hbase : ∀ a : o, algebraMap o Ω a ∈ K := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hgen : ∀ y ∈ s, y ∈ K := by
    intro y hy
    apply Subfield.subset_closure
    refine Or.inr ⟨(x₀, none), (x₀, some ⟨y, hy⟩), ?_⟩
    simp only [t₀, mul_one]
    field_simp
  let KA : Subalgebra o Ω :=
    { K.toSubring with algebraMap_mem' := hbase }
  have hR : S.R ≤ KA := by
    rw [← hs]
    exact Algebra.adjoin_le (fun y hy => hgen y hy)
  have hall : ∀ x : Ω, x ∈ K := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact K.div_mem (hR ha) (hR hb)
  refine ⟨⟨{1}, eq_top_iff.mpr fun x _ => ?_⟩⟩
  simp only [Finset.coe_singleton]
  rw [Submodule.mem_span_singleton]
  exact ⟨⟨x, hall x⟩, by simp [Algebra.smul_def]; rfl⟩

end GlobalTheory.ZH
