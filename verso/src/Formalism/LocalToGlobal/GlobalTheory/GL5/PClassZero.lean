import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Triv

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hL : L = ⊥` using `Subsingleton.elim _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hL]`. Conclude with `Submodule.fg_bot`. Conclude with `Subsingleton.elim _ _`.
-/
theorem isLattice_of_subsingleton [Subsingleton V] (L : Submodule (𝓞 K) V) : Submodule.IsLattice K L := by
  have hL : L = ⊥ := Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · rw [hL]; exact Submodule.fg_bot
  · exact Subsingleton.elim _ _

/- English proof (translation)
Establish `hsub : ∀ M N : Submodule (𝓞 K) V, M = N` using `fun M N => Subsingleton.elim _ _`. Establish `hgen : L ∈ Formalism.HermitianLatticesTheory.genus h L` using `⟨isLattice_of_subsingleton L, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩`. Establish `hreps : Formalism.ThetaLiftIndependence.IsClassReps h L {L}`. Use `⟨fun M hM => ?_, fun M _ => ⟨L, ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite `hM` using `[Finset.mem_singleton]`.

Rewrite using `[hM]`. Conclude with `hgen`. Introduce `N hN`. Conclude with `Finset.mem_singleton.mp hN.1`. Establish `hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s` using `⟨_, hreps⟩`.

Establish `hmem : L ∈ hex.choose`. Take `⟨N, ⟨hN, -⟩, -⟩` from `hex.choose_spec.2 L hgen`. Rewrite `hN` using `[hsub N L]`. Then use the resulting hypothesis. Establish `heq : hex.choose = {L}`. Use extensionality with `M`.

Rewrite using `[Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Conclude with `hsub _ _`. Introduce and unpack `rfl`.

Conclude with `hmem`. Establish `haut : Nat.card (Formalism.ThetaLiftIndependence.autL h L) = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩, ⟨⟨1, one_mem _, hsub _ _⟩⟩⟩` and prove the remaining obligations. Unfold `Formalism.HermitianLatticesTheory.mass`.

Rewrite using `[dif_pos hex, heq, Finset.sum_singleton, haut]`. Simplify using the standard rewrite rules.
-/
theorem mass_of_subsingleton [Subsingleton V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = 1 := by
  classical
  have hsub : ∀ M N : Submodule (𝓞 K) V, M = N := fun M N => Subsingleton.elim _ _
  have hgen : L ∈ Formalism.HermitianLatticesTheory.genus h L :=
    ⟨isLattice_of_subsingleton L, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩
  have hreps : Formalism.ThetaLiftIndependence.IsClassReps h L {L} := by
    refine ⟨fun M hM => ?_, fun M _ => ⟨L, ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩, ?_⟩⟩
    · rw [Finset.mem_singleton] at hM; rw [hM]; exact hgen
    · intro N hN; exact Finset.mem_singleton.mp hN.1
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨_, hreps⟩
  have hmem : L ∈ hex.choose := by
    obtain ⟨N, ⟨hN, -⟩, -⟩ := hex.choose_spec.2 L hgen
    rwa [hsub N L] at hN
  have heq : hex.choose = {L} := by
    ext M
    rw [Finset.mem_singleton]
    constructor
    · intro _; exact hsub _ _
    · rintro rfl; exact hmem
  have haut : Nat.card (Formalism.ThetaLiftIndependence.autL h L) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩,
      ⟨⟨1, one_mem _, hsub _ _⟩⟩⟩
  unfold Formalism.HermitianLatticesTheory.mass
  rw [dif_pos hex, heq, Finset.sum_singleton, haut]
  simp

end Triv

/- English proof (translation)
Establish `: IsEmpty (Fin W.rank)` using `by rw [hrk]; infer_instance`. Conclude with `W.frame.repr.toEquiv.subsingleton`.
-/
theorem subsingleton_of_rank_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E)
    (hrk : W.rank = 0) : Subsingleton W.V := by
  have : IsEmpty (Fin W.rank) := by rw [hrk]; infer_instance
  exact W.frame.repr.toEquiv.subsingleton

/- English proof (translation)
Substitute `hM` using the available equality. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Set `a' : HR R σ J` to `a`. Set `b' : HR R σ J` to `b`. Establish `e : (a' : GL (Fin 0) (R ⊗[F] E)) = (b' : GL (Fin 0) (R ⊗[F] E))` using `Units.ext (Matrix.ext fun i _ => Fin.elim0 i)`.

Conclude with `Subtype.ext e`.
-/
theorem subsingleton_HA_zero {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hM : M = 0) : Subsingleton (HA R σ J) := by
  subst hM
  refine ⟨fun a b => ?_⟩
  let a' : HR R σ J := a
  let b' : HR R σ J := b
  have e : (a' : GL (Fin 0) (R ⊗[F] E)) = (b' : GL (Fin 0) (R ⊗[F] E)) :=
    Units.ext (Matrix.ext fun i _ => Fin.elim0 i)
  exact Subtype.ext e

/- English proof (translation)
Introduce `W _ _ hrk`. Use `subsingleton_of_rank_zero W hrk` as an intermediate fact. Rewrite using `[mass_of_subsingleton]`. Unfold `massI`. Rewrite using `[mass_of_subsingleton]`.
-/
theorem genusMassAt_zero (D : D7) : GenusMassAt D 0 := by
  intro W _ _ hrk
  have := subsingleton_of_rank_zero W hrk
  rw [mass_of_subsingleton]
  unfold massI
  rw [mass_of_subsingleton]

/- English proof (translation)
Introduce `W _ _ hrk`. Use `subsingleton_HA_zero (AF D.host.F) D.sp.cm.sig W.gram hrk` as an intermediate fact. Conclude with `⟨1, fun _ => 1, fun x => ⟨0, 1, 1, Subsingleton.elim _ _⟩, fun i j _ _ _ _ _ => Subsingleton.elim i j⟩`.
-/
theorem classFinAt_zero (D : D7) : ClassFinAt D 0 := by
  intro W _ _ hrk
  have := subsingleton_HA_zero (AF D.host.F) D.sp.cm.sig W.gram hrk
  exact ⟨1, fun _ => 1, fun x => ⟨0, 1, 1, Subsingleton.elim _ _⟩, fun i j _ _ _ _ _ => Subsingleton.elim i j⟩

/- English proof (translation)
Introduce `W _ _ hrk m g hcov hdisj`. Use `subsingleton_of_rank_zero W hrk` as an intermediate fact. Use `subsingleton_HA_zero (AF D.host.F) D.sp.cm.sig W.gram hrk` as an intermediate fact. Take `⟨i0, -⟩` from `hcov 1`. Establish `: Unique (Fin m)` using `⟨⟨i0⟩, fun j => hdisj j i0 1 1 1 1 (Subsingleton.elim _ _)⟩`.

Establish `hc : Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i0)) = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun a b => Subtype.ext (Subtype.ext (Subsingleton.elim _ _))⟩, ⟨⟨1, ?_⟩⟩⟩` and prove the remaining obligations. Establish `e : (g i0)⁻¹ * (((1 : GamA D W) : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i0) = 1` using `Subsingleton.elim _ _`. Use `show (g i0)⁻¹ * (((1 : GamA D W) : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i0) ∈ StabFin.SFin D.sp.cm.sig W.gram (L0c D W)`.

Rewrite using `[e]`. Conclude with `(StabFin.SFin D.sp.cm.sig W.gram (L0c D W)).one_mem`. Rewrite using `[mass_of_subsingleton, Fintype.sum_unique, show (default : Fin m) = i0 from Subsingleton.elim _ _, hc]`. Simplify using the standard rewrite rules.
-/
theorem classMassAt_zero (D : D7) : ClassMassAt D 0 := by
  intro W _ _ hrk m g hcov hdisj
  have := subsingleton_of_rank_zero W hrk
  have := subsingleton_HA_zero (AF D.host.F) D.sp.cm.sig W.gram hrk
  obtain ⟨i0, -⟩ := hcov 1
  have : Unique (Fin m) := ⟨⟨i0⟩, fun j => hdisj j i0 1 1 1 1 (Subsingleton.elim _ _)⟩
  have hc : Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i0)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext (Subsingleton.elim _ _))⟩, ⟨⟨1, ?_⟩⟩⟩
    have e : (g i0)⁻¹ * (((1 : GamA D W) : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i0) = 1 :=
      Subsingleton.elim _ _
    show (g i0)⁻¹ * (((1 : GamA D W) : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i0) ∈
      StabFin.SFin D.sp.cm.sig W.gram (L0c D W)
    rw [e]
    exact (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)).one_mem
  rw [mass_of_subsingleton, Fintype.sum_unique, show (default : Fin m) = i0 from Subsingleton.elim _ _, hc]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨genusMassAt_zero D, classFinAt_zero D, classMassAt_zero D⟩`.
-/
theorem classItemsAt_zero (D : D7) : ClassItemsAt D 0 :=
  ⟨genusMassAt_zero D, classFinAt_zero D, classMassAt_zero D⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

/- English proof (translation)
The claim follows from `volume_mass_of_items D hT hV (classItemsAt_zero D) hI1 hI2`.
-/
theorem volume_mass_of_low_ranks (D : D7) (hT : VolTie D) (hV : VolRatioTrue D) (hI1 : ClassItemsAt D 1)
    (hI2 : ClassItemsAt D 2) : VolumeEqMass₂ D :=
  volume_mass_of_items D hT hV (classItemsAt_zero D) hI1 hI2

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
