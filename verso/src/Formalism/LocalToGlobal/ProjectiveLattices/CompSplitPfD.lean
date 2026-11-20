import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfC

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfD

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

/- English proof (translation)
Establish `h1` using `hW.1.isGenericPoint_genericPoint_closure`. Rewrite `h1` using `[(isClosed_of_mem_irreducibleComponents W hW).closure_eq]`. Then use the resulting hypothesis.
-/
theorem cspD_gen {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by
  have h1 := hW.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents W hW).closure_eq] at h1

/- English proof (translation)
Establish `hWc : closure ({η} : Set X) = W` using `hη`. Establish `h1 : closure ({η} : Set X) ⊆ closure {z}` using `specializes_iff_closure_subset.mp hz`. Establish `hirr : IsIrreducible (closure ({z} : Set X))` using `isIrreducible_singleton.closure`. Establish `h2 : closure ({z} : Set X) ⊆ W` using `hW.2 hirr (hWc ▸ h1)`. Establish `h3 : closure ({z} : Set X) = closure {η}` using `le_antisymm (hWc ▸ h2) h1`.

Conclude with `(inseparable_iff_closure_eq.mpr h3).eq`.
-/
theorem cspD_max {X : Type} [TopologicalSpace X] [T0Space X] {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) (z : X) (hz : z ⤳ η) : z = η := by
  have hWc : closure ({η} : Set X) = W := hη
  have h1 : closure ({η} : Set X) ⊆ closure {z} := specializes_iff_closure_subset.mp hz
  have hirr : IsIrreducible (closure ({z} : Set X)) := isIrreducible_singleton.closure
  have h2 : closure ({z} : Set X) ⊆ W := hW.2 hirr (hWc ▸ h1)
  have h3 : closure ({z} : Set X) = closure {η} := le_antisymm (hWc ▸ h2) h1
  exact (inseparable_iff_closure_eq.mpr h3).eq

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce `x hxZ hxZ'`. Take `⟨η, hη⟩ : ∃ η, IsGenericPoint η Z` from `⟨_, cspD_gen hZ⟩`. Take `⟨η', hη'⟩ : ∃ η', IsGenericPoint η' Z'` from `⟨_, cspD_gen hZ'⟩`. Establish `s1 : η ⤳ x` using `by rw [specializes_iff_mem_closure, hη.def]; exact hxZ`.

Establish `s2 : η' ⤳ x` using `by rw [specializes_iff_mem_closure, hη'.def]; exact hxZ'`. Take `⟨Y, tY, g, hg, ⟨y, rfl⟩, hY⟩` from `hloc x`. Establish `hU : IsOpen (Set.range g)` using `hg.isOpen_range`. Take `⟨a, ha⟩ : η ∈ Set.range g` from `s1.mem_open hU ⟨y, rfl⟩`. Take `⟨b, hb⟩ : η' ∈ Set.range g` from `s2.mem_open hU ⟨y, rfl⟩`.

Establish `hind` using `hg.toIsEmbedding.toIsInducing`. Establish `maxa : ∀ a', a' ⤳ a → a' = a` using `fun a' h => hg.injective (by`. Establish `h' : g a' ⤳ g a` using `h.map hg.continuous`. Rewrite `h'`, the goal using `[ha]`. Conclude with `cspD_max hZ hη _ h')`.

Establish `maxb : ∀ b', b' ⤳ b → b' = b` using `fun b' h => hg.injective (by`. Establish `h' : g b' ⤳ g b` using `h.map hg.continuous`. Rewrite `h'`, the goal using `[hb]`. Conclude with `cspD_max hZ' hη' _ h')`. Establish `ya : a ⤳ y` using `hind.specializes_iff.mp (by rw [ha]; exact s1)`.

Establish `yb : b ⤳ y` using `hind.specializes_iff.mp (by rw [hb]; exact s2)`. Establish `hab` using `hY a b y maxa maxb ya yb`. Apply `hne` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cspD_disj {X : Type} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hloc : ∀ x : X, ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → X), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  rw [Set.disjoint_left]
  intro x hxZ hxZ'
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η Z := ⟨_, cspD_gen hZ⟩
  obtain ⟨η', hη'⟩ : ∃ η', IsGenericPoint η' Z' := ⟨_, cspD_gen hZ'⟩
  have s1 : η ⤳ x := by rw [specializes_iff_mem_closure, hη.def]; exact hxZ
  have s2 : η' ⤳ x := by rw [specializes_iff_mem_closure, hη'.def]; exact hxZ'
  obtain ⟨Y, tY, g, hg, ⟨y, rfl⟩, hY⟩ := hloc x
  have hU : IsOpen (Set.range g) := hg.isOpen_range
  obtain ⟨a, ha⟩ : η ∈ Set.range g := s1.mem_open hU ⟨y, rfl⟩
  obtain ⟨b, hb⟩ : η' ∈ Set.range g := s2.mem_open hU ⟨y, rfl⟩
  have hind := hg.toIsEmbedding.toIsInducing
  have maxa : ∀ a', a' ⤳ a → a' = a := fun a' h => hg.injective (by
    have h' : g a' ⤳ g a := h.map hg.continuous
    rw [ha] at h' ⊢; exact cspD_max hZ hη _ h')
  have maxb : ∀ b', b' ⤳ b → b' = b := fun b' h => hg.injective (by
    have h' : g b' ⤳ g b := h.map hg.continuous
    rw [hb] at h' ⊢; exact cspD_max hZ' hη' _ h')
  have ya : a ⤳ y := hind.specializes_iff.mp (by rw [ha]; exact s1)
  have yb : b ⤳ y := hind.specializes_iff.mp (by rw [hb]; exact s2)
  have hab := hY a b y maxa maxb ya yb
  apply hne
  calc Z = closure {η} := hη.def.symm
    _ = closure {η'} := by rw [← ha, ← hb, hab]
    _ = Z' := hη'.def

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Use `first`. Consider the case `(haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)`. Consider the case `(haveI := Xo.smooth; infer_instance)`. Consider the case `(haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)`.
-/
theorem cspD_smooth (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  first
    | (haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)
    | (haveI := Xo.smooth; infer_instance)
    | (haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)

/- English proof (translation)
Take `⟨_, ⟨V, hV, rfl⟩, hxV, -⟩` from `(Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hV' : IsAffineOpen V` using `hV`. Establish `hsm` using `cspD_smooth Xo c`. Establish `h1` using `HasRingHomProperty.appLE (P := @Smooth) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)`. Set `ψ : c.F →+* Γ(Xo.XF c, V)` to `((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom`.

Establish `hψ : ψ.Smooth` using `RingHom.Smooth.comp (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1`. Set `_ : Algebra c.F Γ(Xo.XF c, V)` to `ψ.toAlgebra`. Establish `: Algebra.Smooth c.F Γ(Xo.XF c, V)` using `hψ`. Take `⟨r, hr, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F) (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)`. Use `⟨PrimeSpectrum (Localization.Away r), inferInstance, hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]`. Conclude with `hr`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Use `show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x`. Rewrite using `[hz]`. Conclude with `hV'.fromSpec_primeIdealOf ⟨x, hxV⟩`. Introduce `a b y ha hb hay hby`. Establish `: IsIntegrallyClosed (MvPolynomial (Fin n) c.F)` using `UniqueFactorizationMonoid.instIsIntegrallyClosed`.

Establish `hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) → a.asIdeal ∈ minimalPrimes (Localization.Away r)`. Introduce `a ha`. Use `⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩` and prove the remaining obligations. Use `ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)` as an intermediate fact. Conclude with `(congrArg PrimeSpectrum.asIdeal this).ge`.

Conclude with `PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal) (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay) ((PrimeSpectrum.le_iff_specializes _ _).2 hby))`.
-/
theorem cspD_local (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have hsm := cspD_smooth Xo c
  have h1 := HasRingHomProperty.appLE (P := @Smooth)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)
  let ψ : c.F →+* Γ(Xo.XF c, V) :=
    ((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra c.F Γ(Xo.XF c, V) := ψ.toAlgebra
  have : Algebra.Smooth c.F Γ(Xo.XF c, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) c.F) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

/- English proof (translation)
The claim follows from `cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))`.
-/
theorem cspD_comp_disj (Xo : Moduli Dw l) (c : Coeff l) (Z Z' : Comp Xo c) (hne : Z ≠ Z') :
    Disjoint (Z : Set (Xo.XF c)) Z' := cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))

end Formalism.L2.Pj.CompSplitPfD
