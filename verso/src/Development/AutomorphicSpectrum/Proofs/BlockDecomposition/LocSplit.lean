import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LocSplitProof

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locSplit : CrystallineSemistableComparison.E.LocSplit := by
  intro U hU P hP
  obtain ⟨S, hS, hSP⟩ := hP
  rw [Scheme.etaleTopology, Scheme.mem_grothendieckTopology_iff] at hS
  obtain ⟨𝒰, h𝒰⟩ := hS
  have hsurj : Surjective (Limits.Sigma.desc 𝒰.f) := by
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    refine ⟨(Limits.Sigma.ι 𝒰.X i) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc, hy]
  have het : Etale (Limits.Sigma.desc 𝒰.f) := by
    have := 𝒰.sigma.map_prop ⟨⟩
    simpa [Scheme.Cover.sigma_f] using this
  obtain ⟨s, hs⟩ := hU _ (Limits.Sigma.desc 𝒰.f) het hsurj
  have hlc : IsLocallyConstant (fun u : U => ((sigmaMk 𝒰.X).symm (s u)).1) := by
    intro t
    have hfst : IsOpen (Sigma.fst ⁻¹' t : Set (Σ i, 𝒰.X i)) := by
      rw [isOpen_sigma_iff]
      intro i
      by_cases hi : i ∈ t
      · convert isOpen_univ
        ext
        simp [hi]
      · convert isOpen_empty
        ext
        simp [hi]
    exact hfst.preimage ((sigmaMk 𝒰.X).symm.continuous.comp s.continuous)
  refine ⟨𝒰.I₀, ⟨fun u => ((sigmaMk 𝒰.X).symm (s u)).1, hlc⟩, ?_⟩
  intro V g a hg
  have hrange : Set.range (g ≫ s) ⊆ Set.range (Limits.Sigma.ι 𝒰.X a) := by
    rintro _ ⟨v, rfl⟩
    have h1 : ((sigmaMk 𝒰.X).symm (s (g v))).1 = a := hg v
    rcases hq : (sigmaMk 𝒰.X).symm (s (g v)) with ⟨i, y⟩
    rw [hq] at h1
    subst h1
    refine ⟨y, ?_⟩
    have h2 : sigmaMk 𝒰.X ⟨i, y⟩ = s (g v) := by rw [← hq]; simp
    rw [sigmaMk_mk] at h2
    rw [h2, Scheme.Hom.comp_apply]
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Limits.Sigma.ι 𝒰.X a = g ≫ s :=
    ⟨_, IsOpenImmersion.lift_fac (Limits.Sigma.ι 𝒰.X a) (g ≫ s) hrange⟩
  have hgl : g = l ≫ 𝒰.f a := by
    have h3 : l ≫ 𝒰.f a = l ≫ Limits.Sigma.ι 𝒰.X a ≫ Limits.Sigma.desc 𝒰.f := by simp
    rw [h3, ← Category.assoc, hl, Category.assoc, hs, Category.comp_id]
  rw [hgl]
  exact hSP V _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk a)) l)

end GlobalTheory.CompanionTheory.LocSplitProof
