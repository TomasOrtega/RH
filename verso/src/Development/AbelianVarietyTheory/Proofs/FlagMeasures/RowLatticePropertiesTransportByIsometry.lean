import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfLocalDiscriminant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatTransport

variable {D : D7}

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Introduce `h`.

Conclude with `⟨g x, h, by simp⟩`.
-/
theorem mem_gmap_inv (g : GV D) (Λ : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ↔ g x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g x, h, by simp⟩

variable {T : D.host.E} {F0 G' : FlagG (VS D) D.R.rS T} {g : GV D}

/- English proof (translation)
Establish `h` using `hfr a.castSucc`. Simplify `h` using `[FlagG.fvec, Fin.snoc_castSucc]`.
-/
theorem e_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (a : Fin D.R.rS) : g (F0.e a) = G'.e a := by
  have h := hfr a.castSucc
  simpa [FlagG.fvec, Fin.snoc_castSucc] using h

/- English proof (translation)
Establish `h` using `hfr (Fin.last _)`. Simplify `h` using `[FlagG.fvec, Fin.snoc_last]`.
-/
theorem z_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) : g F0.z = G'.z := by
  have h := hfr (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using h

/- English proof (translation)
Unfold `FlagG.X`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `a`. Conclude with `e_eq hfr a`.
-/
theorem map_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) :
    F0.X.map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = G'.X := by
  unfold FlagG.X
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  exact e_eq hfr a

/- English proof (translation)
Rewrite using `[← map_X hfr]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨v, hv, rfl⟩`. Introduce and unpack `⟨w, hw, hwv⟩`.

Establish `: w = v` using `g.injective hwv`. Conclude with `this ▸ hw`.
-/
theorem mem_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ F0.X ↔ g v ∈ G'.X := by
  rw [← map_X hfr]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

/- English proof (translation)
Establish `hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y` using `hg`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `hy' : g.symm y ∈ F0.X`.

Rewrite using `[mem_X hfr]`. Simplify using `using hy`. Use `h _ hy'` as an intermediate fact. Rewrite `this` using `[← hiso]`. Simplify using `using this`.

Introduce `h x hx`. Rewrite using `[← hiso]`. Conclude with `h _ ((mem_X hfr x).1 hx)`.
-/
theorem mem_orth (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) :
    v ∈ orth (VS D) F0.X ↔ g v ∈ orth (VS D) G'.X := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ F0.X := by
      rw [mem_X hfr]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h x hx
    rw [← hiso]
    exact h _ ((mem_X hfr x).1 hx)

/- English proof (translation)
Establish `hmap : (XS D F0).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = XS D G'`. Unfold `XS`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, ⟨a, x, hx, rfl⟩, rfl⟩`. Use `⟨a, x, hx, ?_⟩` and prove the remaining obligations. Simplify using `[e_eq hfr a]`. Introduce and unpack `⟨a, x, hx, rfl⟩`.

Use `⟨x • F0.e a, ⟨a, x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[e_eq hfr a]`. Rewrite using `[← hmap]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Conclude with `⟨v, hv, rfl⟩`. Introduce and unpack `⟨w, hw, hwv⟩`. Establish `: w = v` using `g.injective hwv`. Conclude with `this ▸ hw`.
-/
theorem mem_XS (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ XS D F0 ↔ g v ∈ XS D G' := by
  have hmap : (XS D F0).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = XS D G' := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      refine ⟨a, x, hx, ?_⟩
      simp [e_eq hfr a]
    · rintro ⟨a, x, hx, rfl⟩
      refine ⟨x • F0.e a, ⟨a, x, hx, rfl⟩, ?_⟩
      simp [e_eq hfr a]
  rw [← hmap]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

/- English proof (translation)
Establish `hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y` using `hg`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `hy' : g.symm y ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ`.

Rewrite using `[mem_gmap_inv]`. Simplify using `using hy`. Use `h _ hy'` as an intermediate fact. Rewrite `this` using `[← hiso]`. Simplify using `using this`.

Introduce `h y hy`. Rewrite using `[← hiso]`. Conclude with `h _ ((mem_gmap_inv g Λ y).1 hy)`.
-/
theorem mem_dual (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ↔ g x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
      rw [mem_gmap_inv]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h y hy
    rw [← hiso]
    exact h _ ((mem_gmap_inv g Λ y).1 hy)

/- English proof (translation)
Use `⟨hL.fg.map _, ?_⟩` and prove the remaining obligations. Establish `e : ((Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ : LV D) : Set (VS D).V) = ((g⁻¹ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V)` using `rfl`. Rewrite using `[e, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `(g⁻¹ : GV D).surjective`.
-/
theorem isLattice_inv (g : GV D) {Λ : LV D} (hL : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ : LV D) : Set (VS D).V) =
      ((g⁻¹ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V) := rfl
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (g⁻¹ : GV D).surjective

/- English proof (translation)
Take `⟨hs, ho⟩` from `hv`. Use `⟨?_, (mem_orth hg hfr v).1 ho⟩` and prove the remaining obligations. Take `⟨y, hy, w, hw, rfl⟩` from `Submodule.mem_sup.1 hs`. Take `⟨hyΛ, hyo⟩` from `hy`. Rewrite using `[map_add]`.

Use `Submodule.add_mem_sup ⟨(mem_gmap_inv g Λ y).1 hyΛ, (mem_orth hg hfr y).1 hyo⟩ ?_` and prove the remaining obligations. Conclude with `(mem_X hfr w).1 hw`.
-/
theorem mem_Lsub (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (Λ : LV D)
    (v : (VS D).V) (hv : v ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0)) : g v ∈ Lsub Λ (lf D G') := by
  obtain ⟨hs, ho⟩ := hv
  refine ⟨?_, (mem_orth hg hfr v).1 ho⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨hyΛ, hyo⟩ := hy
  rw [map_add]
  refine Submodule.add_mem_sup ⟨(mem_gmap_inv g Λ y).1 hyΛ, (mem_orth hg hfr y).1 hyo⟩ ?_
  exact (mem_X hfr w).1 hw

end GlobalTheory.RowLatTransport

namespace GlobalTheory.RowLatTransport

/- English proof (translation)
Introduce `D T F0 G' g hg hfr Λ hL hU hz hX hprim`. Establish `hL'` using `isLattice_inv g hL`. Establish `hU' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)`. Unfold `Formalism.HermitianLatticesTheory.IsUnimodular`. Use extensionality with `x`.

Rewrite using `[mem_dual hg, mem_gmap_inv]`. Establish `hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ` using `hU`. Rewrite using `[hU0]`. Use `⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D.sp.cm (VS D) _ hL' hU', hL', hU', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_gmap_inv, z_eq hfr]`.

Conclude with `hz`. Use extensionality with `v`. Express the relevant statement in the definitionally equal form `v ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ⊓ toO (VS D) F0.X ↔ v ∈ XS D F0`. Rewrite using `[mem_XS hfr, ← hX]`. Express the relevant statement in the definitionally equal form `_ ↔ g v ∈ Λ ⊓ toO (VS D) G'.X`.

Simplify using `only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]`. Rewrite using `[mem_gmap_inv, mem_X hfr]`. Introduce `c hc`. Apply `hprim c` to reduce the goal to its premises. Use `mem_Lsub hg hfr Λ _ hc` as an intermediate fact.

Rewrite `this` using `[map_smul, z_eq hfr]`. Conclude with `this`.
-/
theorem rowLat_transport : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  intro D T F0 G' g hg hfr Λ hL hU hz hX hprim
  have hL' := isLattice_inv g hL
  have hU' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular
    ext x
    rw [mem_dual hg, mem_gmap_inv]
    have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [hU0]
  refine ⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D.sp.cm (VS D) _ hL' hU',
    hL', hU', ?_, ?_, ?_⟩
  · rw [mem_gmap_inv, z_eq hfr]
    exact hz
  · ext v
    change v ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ⊓ toO (VS D) F0.X ↔ v ∈ XS D F0
    rw [mem_XS hfr, ← hX]
    change _ ↔ g v ∈ Λ ⊓ toO (VS D) G'.X
    simp only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]
    rw [mem_gmap_inv, mem_X hfr]
  · intro c hc
    apply hprim c
    have := mem_Lsub hg hfr Λ _ hc
    rw [map_smul, z_eq hfr] at this
    exact this

end GlobalTheory.RowLatTransport
