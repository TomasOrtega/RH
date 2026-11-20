import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalIndexFrameLogNormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFiniteIndexStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
open GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `eA : ∀ X Y : Submodule (𝓞 L) W, (X ⊓ Y).toAddSubgroup.relIndex X.toAddSubgroup = Y.toAddSubgroup.relIndex X.toAddSubgroup` using `fun X Y => by`. Establish `: (X ⊓ Y).toAddSubgroup = Y.toAddSubgroup ⊓ X.toAddSubgroup`. Use extensionality with `x`. Simplify using `[and_comm]`. Rewrite using `[this, AddSubgroup.inf_relIndex_right]`.

Establish `hA : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w (A ⊓ B)` using `fun w hw => by`. Rewrite using `[locAt_inf, ← h w hw, inf_idem]`. Establish `hB : ∀ w : FinitePlace L, w ≠ v → locAt w B = locAt w (B ⊓ A)` using `fun w hw => by`. Rewrite using `[locAt_inf, h w hw, inf_idem]`. Establish `n1` using `GlobalTheory.T.local_index_at_single_place L W v A (A ⊓ B) inf_le_left (by rwa [eA]) hA`.

Establish `n2` using `GlobalTheory.T.local_index_at_single_place L W v B (B ⊓ A) inf_le_left (by rwa [eA]) hB`. Rewrite `n1` using `[eA, locAt_inf, eA]`. Rewrite `n2` using `[eA, locAt_inf, eA]`. Rewrite using `[gIdx, gIdx, n1, n2]`.
-/
theorem gIdx_eq_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W)
    (h1 : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (h2 : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (h : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    gIdx A.toAddSubgroup B.toAddSubgroup = gIdx (locAt v A).toAddSubgroup (locAt v B).toAddSubgroup := by
  have eA : ∀ X Y : Submodule (𝓞 L) W, (X ⊓ Y).toAddSubgroup.relIndex X.toAddSubgroup =
      Y.toAddSubgroup.relIndex X.toAddSubgroup := fun X Y => by
    have : (X ⊓ Y).toAddSubgroup = Y.toAddSubgroup ⊓ X.toAddSubgroup := by
      ext x; simp [and_comm]
    rw [this, AddSubgroup.inf_relIndex_right]
  have hA : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w (A ⊓ B) := fun w hw => by
    rw [locAt_inf, ← h w hw, inf_idem]
  have hB : ∀ w : FinitePlace L, w ≠ v → locAt w B = locAt w (B ⊓ A) := fun w hw => by
    rw [locAt_inf, h w hw, inf_idem]
  have n1 := GlobalTheory.T.local_index_at_single_place L W v A (A ⊓ B) inf_le_left (by rwa [eA]) hA
  have n2 := GlobalTheory.T.local_index_at_single_place L W v B (B ⊓ A) inf_le_left (by rwa [eA]) hB
  rw [eA, locAt_inf, eA] at n1
  rw [eA, locAt_inf, eA] at n2
  rw [gIdx, gIdx, n1, n2]

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `T _ hS`. Establish `: glued T = frame 1`. Rewrite using `[glued, ← iInf_locAt_frame_one]`.

Conclude with `iInf_congr fun v => (hS v (by simp)).locAt_frame`. Rewrite using `[this, gIdx_self, Finset.sum_empty]`. Consider the case `insert v S hv ih`. Introduce `T hd hS`. Use `set T' := Function.update T v 1 with hT'`.

Establish `hTv : T' v = 1` using `by simp [hT']`. Establish `hTw : ∀ w, w ≠ v → T' w = T w` using `fun w hw => by simp [hT', hw]`. Establish `hd' : ∀ w, (T' w).det ≠ 0` using `fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[hTv]`. Simplify using the standard rewrite rules. Rewrite using `[hTw w hw]`. Conclude with `hd w`. Establish `hS' : ∀ w, w ∉ S → UnitAt w (T' w)` using `fun w hw => by`.

Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[hTv]`. Conclude with `unitAt_one _`. Rewrite using `[hTw w hwv]; exact hS w (by simp [hwv, hw])`.

Establish `f1 : {w : FinitePlace L | ¬ UnitAt w (T w)}.Finite` using `(Finset.finite_toSet (insert v S)).subset fun w hw => by`. Assume the negation of the conclusion as `h`. Conclude with `hw (hS w h)`. Establish `f2 : {w : FinitePlace L | ¬ UnitAt w (T' w)}.Finite` using `S.finite_toSet.subset fun w hw => by`. Assume the negation of the conclusion as `h`.

Conclude with `hw (hS' w h)`. Take `⟨a1, a2⟩` from `GlobalTheory.T.glued_lattice_finite_index L n T hd f1`. Take `⟨b1, b2⟩` from `GlobalTheory.T.glued_lattice_finite_index L n T' hd' f2`. Establish `c1` using `AddSubgroup.relIndex_ne_zero_trans a1 b2`. Establish `c2` using `AddSubgroup.relIndex_ne_zero_trans b1 a2`.

Establish `loc : ∀ w : FinitePlace L, w ≠ v → locAt w (glued T) = locAt w (glued T')` using `fun w hw => by`. Rewrite using `[GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2, hTw w hw]`. Rewrite using `[gIdx_add c1 c2 b1 b2, gIdx_eq_locAt v _ _ c1 c2 loc, GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2, hTv, GlobalTheory.T.local_index_frame_log_det L n v (T v) (hd v), ih T' hd' hS', Finset.sum_insert hv]`. Use `congrArg _ (Finset.sum_congr rfl fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[hTw w fun e => hv (e ▸ hw)]`.
-/
theorem gIdx_glued (S : Finset (FinitePlace L)) : ∀ T : FinitePlace L → Matrix (Fin n) (Fin n) L,
    (∀ v, (T v).det ≠ 0) → (∀ v, v ∉ S → UnitAt v (T v)) →
    gIdx (glued T).toAddSubgroup (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup =
      ∑ v ∈ S, Real.log (v (T v).det) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro T _ hS
    have : glued T = frame 1 := by
      rw [glued, ← iInf_locAt_frame_one]
      exact iInf_congr fun v => (hS v (by simp)).locAt_frame
    rw [this, gIdx_self, Finset.sum_empty]
  | insert v S hv ih =>
    intro T hd hS
    set T' := Function.update T v 1 with hT'
    have hTv : T' v = 1 := by simp [hT']
    have hTw : ∀ w, w ≠ v → T' w = T w := fun w hw => by simp [hT', hw]
    have hd' : ∀ w, (T' w).det ≠ 0 := fun w => by
      by_cases hw : w = v
      · subst hw; rw [hTv]; simp
      · rw [hTw w hw]; exact hd w
    have hS' : ∀ w, w ∉ S → UnitAt w (T' w) := fun w hw => by
      by_cases hwv : w = v
      · subst hwv; rw [hTv]; exact unitAt_one _
      · rw [hTw w hwv]; exact hS w (by simp [hwv, hw])
    have f1 : {w : FinitePlace L | ¬ UnitAt w (T w)}.Finite :=
      (Finset.finite_toSet (insert v S)).subset fun w hw => by
        by_contra h
        exact hw (hS w h)
    have f2 : {w : FinitePlace L | ¬ UnitAt w (T' w)}.Finite :=
      S.finite_toSet.subset fun w hw => by
        by_contra h
        exact hw (hS' w h)
    obtain ⟨a1, a2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T hd f1
    obtain ⟨b1, b2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T' hd' f2
    have c1 := AddSubgroup.relIndex_ne_zero_trans a1 b2
    have c2 := AddSubgroup.relIndex_ne_zero_trans b1 a2
    have loc : ∀ w : FinitePlace L, w ≠ v → locAt w (glued T) = locAt w (glued T') := fun w hw => by
      rw [GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2, hTw w hw]
    rw [gIdx_add c1 c2 b1 b2, gIdx_eq_locAt v _ _ c1 c2 loc, GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2,
      hTv, GlobalTheory.T.local_index_frame_log_det L n v (T v) (hd v), ih T' hd' hS', Finset.sum_insert hv]
    refine congrArg _ (Finset.sum_congr rfl fun w hw => ?_)
    rw [hTw w fun e => hv (e ▸ hw)]

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

/- English proof (translation)
Introduce `L _ _ V _ _ _ _ n g F T C hg hd hC hfin hF`. Set `Φ : (Fin n → L) →ₗ[𝓞 L] V` to `(Fintype.linearCombination L g).restrictScalars (𝓞 L)`. Establish `hΦ : Function.Injective Φ` using `hg.fintypeLinearCombination_injective`. Establish `hΦa : ∀ c, Φ c = ∑ i, c i • g i` using `fun c => by`. Simplify using `[Φ, Fintype.linearCombination_apply]`.

Establish `hfr : ∀ A : Matrix (Fin n) (Fin n) L, (frame A).map Φ = Submodule.span (𝓞 L) (Set.range fun k => ∑ j, A j k • g j)` using `fun A => by`. Rewrite using `[frame, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Establish `hFg : F = (glued T).map Φ`. Use extensionality with `x`.

Rewrite using `[hF x, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hl⟩`. Establish `hr : x ∈ Set.range (Fintype.linearCombination L g)`. Rewrite `hx` using `[← Fintype.range_linearCombination]`.

Conclude with `hx`. Take `⟨c, rfl⟩` from `hr`. Use `⟨c, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[glued, Submodule.mem_iInf]`. Introduce `v`.

Take `⟨t, ht, h⟩` from `hl v`. Rewrite `h` using `[← hfr, Submodule.mem_map]`. Take `⟨y, hy, e⟩` from `h`. Use `mem_locAt.2 ⟨t, ht, ?_⟩` and prove the remaining obligations. Establish `: t • c = y` using `hΦ (by rw [map_smul, e]; rfl)`.

Rewrite using `[this]` and apply the resulting hypothesis. Introduce and unpack `⟨c, hc, rfl⟩`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← Fintype.range_linearCombination]`. Conclude with `⟨c, rfl⟩`.

Take `⟨t, ht, h⟩` from `mem_locAt.1 ((Submodule.mem_iInf _).1 hc v)`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfr, ← map_smul]`. Conclude with `Submodule.mem_map_of_mem h`. Establish `hidx : logIdx F (fun k => ∑ j, C j k • g j) = gIdx (glued T).toAddSubgroup (frame C).toAddSubgroup`.

Establish `e : logIdx F (fun k => ∑ j, C j k • g j) = gIdx F.toAddSubgroup ((frame C).map Φ).toAddSubgroup`. Rewrite using `[hfr]`. Both sides reduce to the same expression. Rewrite using `[e, hFg, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]`. Conclude with `gIdx_map _ hΦ _ _`.

Take `⟨g1, g2, g3⟩` from `GlobalTheory.T.global_index_frame_log_norm L n C hC`. Establish `hfin' : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite` using `hfin`. Take `⟨a1, a2⟩` from `GlobalTheory.T.glued_lattice_finite_index L n T hd hfin'`. Rewrite using `[hidx, gIdx_add a1 a2 g1 g2, g3, gIdx_glued hfin'.toFinset T hd fun v hv => by`. Assume the negation of the conclusion as `h`.

Conclude with `hv (hfin'.mem_toFinset.2 h)]`. Use `congr 1`. Rewrite using `[finsum_eq_sum_of_support_subset]`. Introduce `v hv`. Rewrite using `[Set.Finite.coe_toFinset]`.

Introduce `h`. Conclude with `hv (show Real.log (v (T v).det) = 0 by rw [h.2, Real.log_one])`.
-/
theorem logIdx_localFrames : ∀ (L : Type) [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (n : ℕ) (g : Fin n → V) (F : Submodule (𝓞 L) V) (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) L), LinearIndependent L g → (∀ v, (T v).det ≠ 0) → C.det ≠ 0 → {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite → (∀ x, x ∈ F ↔ x ∈ Submodule.span L (Set.range g) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • g j)) → logIdx F (fun k => ∑ j, C j k • g j) = (∑ᶠ v : FinitePlace L, Real.log (v (T v).det)) + ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ V _ _ _ _ n g F T C hg hd hC hfin hF
  classical

  let Φ : (Fin n → L) →ₗ[𝓞 L] V := (Fintype.linearCombination L g).restrictScalars (𝓞 L)
  have hΦ : Function.Injective Φ := hg.fintypeLinearCombination_injective
  have hΦa : ∀ c, Φ c = ∑ i, c i • g i := fun c => by
    simp [Φ, Fintype.linearCombination_apply]
  have hfr : ∀ A : Matrix (Fin n) (Fin n) L, (frame A).map Φ =
      Submodule.span (𝓞 L) (Set.range fun k => ∑ j, A j k • g j) := fun A => by
    rw [frame, Submodule.map_span, ← Set.range_comp]
    congr 2
  have hFg : F = (glued T).map Φ := by
    ext x
    rw [hF x, Submodule.mem_map]
    constructor
    · rintro ⟨hx, hl⟩
      have hr : x ∈ Set.range (Fintype.linearCombination L g) := by
        rw [← Fintype.range_linearCombination] at hx
        exact hx
      obtain ⟨c, rfl⟩ := hr
      refine ⟨c, ?_, rfl⟩
      rw [glued, Submodule.mem_iInf]
      intro v
      obtain ⟨t, ht, h⟩ := hl v
      rw [← hfr, Submodule.mem_map] at h
      obtain ⟨y, hy, e⟩ := h
      refine mem_locAt.2 ⟨t, ht, ?_⟩
      have : t • c = y := hΦ (by rw [map_smul, e]; rfl)
      rwa [this]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, fun v => ?_⟩
      · rw [← Fintype.range_linearCombination]
        exact ⟨c, rfl⟩
      · obtain ⟨t, ht, h⟩ := mem_locAt.1 ((Submodule.mem_iInf _).1 hc v)
        refine ⟨t, ht, ?_⟩
        rw [← hfr, ← map_smul]
        exact Submodule.mem_map_of_mem h
  have hidx : logIdx F (fun k => ∑ j, C j k • g j) = gIdx (glued T).toAddSubgroup (frame C).toAddSubgroup := by
    have e : logIdx F (fun k => ∑ j, C j k • g j) = gIdx F.toAddSubgroup ((frame C).map Φ).toAddSubgroup := by
      rw [hfr]; rfl
    rw [e, hFg, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact gIdx_map _ hΦ _ _
  obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.global_index_frame_log_norm L n C hC
  have hfin' : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite := hfin
  obtain ⟨a1, a2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T hd hfin'
  rw [hidx, gIdx_add a1 a2 g1 g2, g3, gIdx_glued hfin'.toFinset T hd fun v hv => by
    by_contra h
    exact hv (hfin'.mem_toFinset.2 h)]
  congr 1
  rw [finsum_eq_sum_of_support_subset]
  intro v hv
  rw [Set.Finite.coe_toFinset]
  intro h
  exact hv (show Real.log (v (T v).det) = 0 by rw [h.2, Real.log_one])

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
