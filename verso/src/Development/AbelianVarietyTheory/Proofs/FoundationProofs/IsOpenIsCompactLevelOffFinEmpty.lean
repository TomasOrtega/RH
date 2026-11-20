import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
/- English proof (translation)
Simplify using `[mem_levelOpen, mem_levelOffFin]`.
-/
theorem mem_levelOpen_iff_projFin {g : GAd σ J} :
    g ∈ levelOpen σ J L ↔ projFin σ J g ∈ levelOffFin σ J L ∅ := by
  simp [mem_levelOpen, mem_levelOffFin]

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[mem_levelOffFin]`. Use `⟨fun h => ⟨by simp, fun u _ => ?_⟩, fun h => by simpa using h.2 v (by simp)⟩` and prove the remaining obligations. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Simplify using `using h`.

Rewrite using `[projFinLoc_embLocFin_ne σ J e]`. Conclude with `one_mem _`.
-/
theorem mem_stabLoc_iff_embLocFin {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ embLocFin σ J v g ∈ levelOffFin σ J L ∅ := by
  rw [mem_levelOffFin]
  refine ⟨fun h => ⟨by simp, fun u _ => ?_⟩, fun h => by simpa using h.2 v (by simp)⟩
  by_cases e : u = v
  · subst e; simpa using h
  · rw [projFinLoc_embLocFin_ne σ J e]; exact one_mem _

omit [NumberField E] in
/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hg`.

Establish `h : g ∈ (ofFin σ J).range` using `by rw [range_ofFin]; exact (mem_levelOff.1 hg).1`. Take `⟨y, rfl⟩` from `h`. Conclude with `⟨y, hg, rfl⟩`.
-/
theorem image_ofFin_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ofFin σ J '' (levelOffFin σ J L S : Set (GFin σ J)) = (levelOff σ J L S : Set (GAd σ J)) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hg
    have h : g ∈ (ofFin σ J).range := by rw [range_ofFin]; exact (mem_levelOff.1 hg).1
    obtain ⟨y, rfl⟩ := h
    exact ⟨y, hg, rfl⟩

variable [Submodule.IsLattice E L]

/- English proof (translation)
Establish `hfg : L.FG` using `Submodule.IsLattice.fg (A := E)`. Take `⟨K, hK, ho, hc⟩` from `GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ n J L hfg Submodule.IsLattice.span_eq_top`. Establish `e : levelOffFin σ J L ∅ = K`. Use extensionality with `g`. Establish `h` using `mem_levelOpen_iff_latHat σ J hfg (ofFin σ J g)`.

Establish `h2 : Formalism.MainNotions.StandardLattice.finMat σ J (ofFin σ J g) = (HA.mat (Af F) σ J g).1` using `congrArg (fun x => (HA.mat (Af F) σ J x).1) (projFin_ofFin σ J g)`. Rewrite `h` using `[mem_levelOpen_iff_projFin, projFin_ofFin, h2]`. Conclude with `h.trans (hK g).symm`. Rewrite using `[e]`. Conclude with `⟨ho, hc⟩`.
-/
theorem isOpen_isCompact_levelOffFin_empty :
    IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) ∧ IsCompact (levelOffFin σ J L ∅ : Set (GFin σ J)) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E)
  obtain ⟨K, hK, ho, hc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ n J L hfg
    Submodule.IsLattice.span_eq_top
  have e : levelOffFin σ J L ∅ = K := by
    ext g
    have h := mem_levelOpen_iff_latHat σ J hfg (ofFin σ J g)
    have h2 : Formalism.MainNotions.StandardLattice.finMat σ J (ofFin σ J g) = (HA.mat (Af F) σ J g).1 :=
      congrArg (fun x => (HA.mat (Af F) σ J x).1) (projFin_ofFin σ J g)
    rw [mem_levelOpen_iff_projFin, projFin_ofFin, h2] at h
    exact h.trans (hK g).symm
  rw [e]
  exact ⟨ho, hc⟩

/- English proof (translation)
The claim follows from `(isOpen_isCompact_levelOffFin_empty σ J L).1`.
-/
theorem isOpen_levelOffFin_empty : IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
  (isOpen_isCompact_levelOffFin_empty σ J L).1

/- English proof (translation)
Establish `: (levelOpen σ J L : Set (GAd σ J)) = projFin σ J ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J))` using `Set.ext fun _ => mem_levelOpen_iff_projFin σ J L`. Rewrite using `[this]`. Conclude with `(isOpen_levelOffFin_empty σ J L).preimage (continuous_projFin σ J)`.
-/
theorem isOpen_levelOpen : IsOpen (levelOpen σ J L : Set (GAd σ J)) := by
  have : (levelOpen σ J L : Set (GAd σ J)) = projFin σ J ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_levelOpen_iff_projFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_projFin σ J)

/- English proof (translation)
Establish `: (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J))` using `Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L`. Rewrite using `[this]`. Conclude with `(isOpen_levelOffFin_empty σ J L).preimage (continuous_embLocFin σ J v)`.
-/
theorem isOpen_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_embLocFin σ J v)

/- English proof (translation)
Establish `: (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J))` using `Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L`. Rewrite using `[this]`. Conclude with `(Function.LeftInverse.isClosedEmbedding (projFinLoc_embLocFin_self σ J v) (continuous_projFinLoc σ J v) (continuous_embLocFin σ J v)).isCompact_preimage (isOpen_isCompact_levelOffFin_empty σ J L).2`.
-/
theorem isCompact_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (Function.LeftInverse.isClosedEmbedding (projFinLoc_embLocFin_self σ J v) (continuous_projFinLoc σ J v)
    (continuous_embLocFin σ J v)).isCompact_preimage (isOpen_isCompact_levelOffFin_empty σ J L).2

/- English proof (translation)
Establish `: (levelOffFin σ J L S : Set (GFin σ J)) = (levelOffFin σ J L ∅ : Set (GFin σ J)) ∩ ofFin σ J ⁻¹' (awayPts σ J S : Set (GAd σ J))`. Use extensionality with `g`. Express the relevant statement in the definitionally equal form `ofFin σ J g ∈ levelOff σ J L S ↔ ofFin σ J g ∈ levelOff σ J L ∅ ∧ ofFin σ J g ∈ awayPts σ J S`. Simplify using `only [levelOff_eq, finAwayPts, Subgroup.mem_inf, awayPts_empty, Subgroup.mem_top]`. The claim follows by propositional logic.

Rewrite using `[this]`. Conclude with `(isOpen_isCompact_levelOffFin_empty σ J L).2.inter_right ((isClosed_awayPts σ J S).preimage (continuous_ofFin σ J))`.
-/
theorem isCompact_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOffFin σ J L S : Set (GFin σ J)) := by
  have : (levelOffFin σ J L S : Set (GFin σ J)) =
      (levelOffFin σ J L ∅ : Set (GFin σ J)) ∩ ofFin σ J ⁻¹' (awayPts σ J S : Set (GAd σ J)) := by
    ext g
    change ofFin σ J g ∈ levelOff σ J L S ↔ ofFin σ J g ∈ levelOff σ J L ∅ ∧ ofFin σ J g ∈ awayPts σ J S
    simp only [levelOff_eq, finAwayPts, Subgroup.mem_inf, awayPts_empty, Subgroup.mem_top]
    tauto
  rw [this]
  exact (isOpen_isCompact_levelOffFin_empty σ J L).2.inter_right
    ((isClosed_awayPts σ J S).preimage (continuous_ofFin σ J))

/- English proof (translation)
Rewrite using `[← image_ofFin_levelOffFin]`. Conclude with `(isCompact_levelOffFin σ J L S).image (continuous_ofFin σ J)`.
-/
theorem isCompact_levelOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOff σ J L S : Set (GAd σ J)) := by
  rw [← image_ofFin_levelOffFin]
  exact (isCompact_levelOffFin σ J L S).image (continuous_ofFin σ J)

/- English proof (translation)
The claim follows from `isCompact_levelOff σ J L ∅`.
-/
theorem isCompact_levelFin : IsCompact (levelFin σ J L : Set (GAd σ J)) := isCompact_levelOff σ J L ∅

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v => ⟨isOpen_stabLoc σ J L v, isCompact_stabLoc σ J L v⟩, isOpen_levelOpen σ J L, isOpen_isCompact_levelOffFin_empty σ J L, isCompact_levelOff σ J L⟩`.
-/
theorem levels_open_compact :
    (∀ v, IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) ∧ IsCompact (stabLoc σ J L v : Set (GLoc σ J v))) ∧
    IsOpen (levelOpen σ J L : Set (GAd σ J)) ∧
    (IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) ∧ IsCompact (levelOffFin σ J L ∅ : Set (GFin σ J))) ∧
    ∀ S, IsCompact (levelOff σ J L S : Set (GAd σ J)) :=
  ⟨fun v => ⟨isOpen_stabLoc σ J L v, isCompact_stabLoc σ J L v⟩, isOpen_levelOpen σ J L,
    isOpen_isCompact_levelOffFin_empty σ J L, isCompact_levelOff σ J L⟩

end GlobalTheory.AdelicU
