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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
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
