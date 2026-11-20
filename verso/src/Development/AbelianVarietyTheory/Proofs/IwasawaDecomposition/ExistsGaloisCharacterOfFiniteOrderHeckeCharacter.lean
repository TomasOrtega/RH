import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

/- English proof (translation)
Introduce `hGAR D χ n hn hχ hz`. Take `⟨art, ha⟩` from `hGAR D.host.E D.nd.Om`. Establish `h1 : ∀ x, χ.1 x ^ n = 1` using `fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) hχ`. Establish `hko : IsOpen (χ.1.ker : Set (Ideles D.host.E))` using `GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1`. Establish `hkc : IsClosed (χ.1.ker : Set (Ideles D.host.E))` using `Subgroup.isClosed_of_isOpen _ hko`.

Establish `hle : art.ker ≤ χ.1.ker`. Rewrite using `[ha.ker]`. Use `Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `χ.2.2 k`.

Rewrite using `[GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]`. Introduce `y hy`. Establish `hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)))` using `Continuous.units_map _ (continuous_id.prodMk continuous_const)`. Establish `hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing D.host.E)ˣ)` using `⟨hkc.preimage hinl, hko.preimage hinl⟩`. Conclude with `hcl.connectedComponent_subset (Subgroup.one_mem _) hy`.

Set `e` to `QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective`. Set `c : Gab D.host.E D.nd.Om →* ℂˣ` to `(QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom`. Establish `hc : ∀ x, c (art x) = χ.1 x` using `fun x => by show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x`. Establish `: e.symm (art x) = QuotientGroup.mk x` using `e.symm_apply_eq.mpr rfl`. Rewrite using `[this]`.

Both sides reduce to the same expression. Establish `hcc : Continuous c`. Rewrite using `[ha.quot.isQuotientMap.continuous_iff]`. Establish `: (c ∘ art) = χ.1` using `funext hc`. Rewrite using `[this]`.

Conclude with `χ.2.1`. Set `r : G D.host.E D.nd.Om →* ℂˣ` to `c.comp (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)`. Establish `hrc : Continuous r` using `hcc.comp continuous_quot_mk`. Establish `hrn : ∀ g, r g ^ n = 1` using `fun g => by`. Take `⟨x, hx⟩` from `ha.quot.surjective (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om g)`.

Use `show c _ ^ n = 1`. Rewrite using `[← hx, hc, h1]`. Establish `hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om))` using `GlobalTheory.HeckeGal.isOpen_ker_of_pow r hrc hn hrn`. Take `⟨z, hz⟩` from `hz`. Take `⟨ψ, hψ⟩` from `GlobalTheory.TwistChoice.exists_char_descent D.what₂.embLL hn hz r hrn`.

Establish `hψr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ = r` using `MonoidHom.ext fun g => Units.ext (hψ g)`. Establish `hker : ψ.ker = r.ker`. Use extensionality with `g`. Simplify using `only [MonoidHom.mem_ker]`. Rewrite using `[← hψr, MonoidHom.comp_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, map_one]`. Introduce `h`. Apply `Units.ext` to reduce the goal to its premises.

Apply `D.what₂.embLL.injective` to reduce the goal to its premises. Use `congrArg Units.val h` as an intermediate fact. Simplify using `using this`. Use `⟨ψ, ⟨by rw [hker]; exact hro, art, ha, ?_⟩, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hψr]`.

Introduce `x σ hσ`. Use `show χ.1 x = c (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ)`. Rewrite using `[← hσ, hc]`. Apply `Units.ext` to reduce the goal to its premises. Apply `D.what₂.embLL.injective` to reduce the goal to its premises.

Use `congrArg Units.val (hrn g)` as an intermediate fact. Rewrite `this` using `[← hψr]`. Simplify using `using this`.
-/
theorem galOf_of_orderDvd : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  intro hGAR D χ n hn hχ hz
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles D.host.E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles D.host.E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing D.host.E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab D.host.E D.nd.Om →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  let r : G D.host.E D.nd.Om →* ℂˣ := c.comp (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
  have hrc : Continuous r := hcc.comp continuous_quot_mk
  have hrn : ∀ g, r g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := ha.quot.surjective (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om g)
    show c _ ^ n = 1
    rw [← hx, hc, h1]
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hrc hn hrn
  obtain ⟨z, hz⟩ := hz
  obtain ⟨ψ, hψ⟩ := GlobalTheory.TwistChoice.exists_char_descent D.what₂.embLL hn hz r hrn
  have hψr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ = r := MonoidHom.ext fun g => Units.ext (hψ g)
  have hker : ψ.ker = r.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    rw [← hψr, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one]
    · intro h
      apply Units.ext
      apply D.what₂.embLL.injective
      have := congrArg Units.val h
      simpa using this
  refine ⟨ψ, ⟨by rw [hker]; exact hro, art, ha, ?_⟩, fun g => ?_⟩
  · rw [hψr]
    intro x σ hσ
    show χ.1 x = c (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ)
    rw [← hσ, hc]
  · apply Units.ext
    apply D.what₂.embLL.injective
    have := congrArg Units.val (hrn g)
    rw [← hψr] at this
    simpa using this

end GlobalTheory.LevCmp
