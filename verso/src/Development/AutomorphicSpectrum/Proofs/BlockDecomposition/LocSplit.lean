import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LocSplitProof

/- English proof (translation)
Introduce `U hU P hP`. Take `⟨S, hS, hSP⟩` from `hP`. Rewrite `hS` using `[Scheme.etaleTopology, Scheme.mem_grothendieckTopology_iff]`. Take `⟨𝒰, h𝒰⟩` from `hS`. Establish `hsurj : Surjective (Limits.Sigma.desc 𝒰.f)`.

Prove the components needed by the constructor for the conclusion. Introduce `x`. Take `⟨i, y, hy⟩` from `𝒰.exists_eq x`. Use `⟨(Limits.Sigma.ι 𝒰.X i) y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc, hy]`.

Establish `het : Etale (Limits.Sigma.desc 𝒰.f)`. Use `𝒰.sigma.map_prop ⟨⟩` as an intermediate fact. Simplify `this` using `[Scheme.Cover.sigma_f]`. Take `⟨s, hs⟩` from `hU _ (Limits.Sigma.desc 𝒰.f) het hsurj`. Establish `hlc : IsLocallyConstant (fun u : U => ((sigmaMk 𝒰.X).symm (s u)).1)`.

Introduce `t`. Establish `hfst : IsOpen (Sigma.fst ⁻¹' t : Set (Σ i, 𝒰.X i))`. Rewrite using `[isOpen_sigma_iff]`. Introduce `i`. Distinguish the cases in `hi : i ∈ t`.

Use `isOpen_univ` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[hi]`. Use `isOpen_empty` and compare the differences between its conclusion and the goal. Use `ext`.

Simplify using `[hi]`. Conclude with `hfst.preimage ((sigmaMk 𝒰.X).symm.continuous.comp s.continuous)`. Use `⟨𝒰.I₀, ⟨fun u => ((sigmaMk 𝒰.X).symm (s u)).1, hlc⟩, ?_⟩` and prove the remaining obligations. Introduce `V g a hg`. Establish `hrange : Set.range (g ≫ s) ⊆ Set.range (Limits.Sigma.ι 𝒰.X a)`.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `h1 : ((sigmaMk 𝒰.X).symm (s (g v))).1 = a` using `hg v`. Break down `hq : (sigmaMk 𝒰.X).symm (s (g v)) with ⟨i, y⟩` into its components or cases. Rewrite `h1` using `[hq]`. Substitute `h1` using the available equality.

Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `h2 : sigmaMk 𝒰.X ⟨i, y⟩ = s (g v)` using `by rw [← hq]; simp`. Rewrite `h2` using `[sigmaMk_mk]`. Rewrite using `[h2, Scheme.Hom.comp_apply]`. Take `⟨l, hl⟩ : ∃ l, l ≫ Limits.Sigma.ι 𝒰.X a = g ≫ s` from `⟨_, IsOpenImmersion.lift_fac (Limits.Sigma.ι 𝒰.X a) (g ≫ s) hrange⟩`.

Establish `hgl : g = l ≫ 𝒰.f a`. Establish `h3 : l ≫ 𝒰.f a = l ≫ Limits.Sigma.ι 𝒰.X a ≫ Limits.Sigma.desc 𝒰.f` using `by simp`. Rewrite using `[h3, ← Category.assoc, hl, Category.assoc, hs, Category.comp_id]`. Rewrite using `[hgl]`. Conclude with `hSP V _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk a)) l)`.
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
