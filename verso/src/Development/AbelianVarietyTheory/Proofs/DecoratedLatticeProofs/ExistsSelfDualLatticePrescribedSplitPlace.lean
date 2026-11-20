import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def place (q : SplitPt D k) : GlobalTheory.LocMod.Place D k where
  e := q.e
  split := q.split
  π := q.pr
  ι := q.sec
  π_ι := q.pr_sec
  ι_π := q.sec_pr
  cont_π := q.cont_pr
  cont_ι := q.cont_sec

/- English proof (translation)
Introduce `i j`. Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem suppAt_one (e : AE D) (S : HSp D) : SuppAt e S 1 := by
  intro i j
  simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Use `⟨suppAt_one _ _, ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.L2.Theta.mt, F.βγ, place]`.
-/
theorem isLoc_one (q : SplitPt D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : (place q).IsLoc F 1 1 := by
  refine ⟨suppAt_one _ _, ?_⟩
  simp [Formalism.L2.Theta.mt, F.βγ, place]

/- English proof (translation)
The claim follows from `(GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (place q)).1 S Y F`.
-/
theorem locGrp (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    (∀ gk : GL Y k, ∃! g, (place q).IsLoc F g gk) ∧ (∀ g, SuppAt (place q).e S g → ∃ gk, (place q).IsLoc F g gk) ∧
      ∀ g gk h hk, (place q).IsLoc F g gk → (place q).IsLoc F h hk → (place q).IsLoc F (g * h) (gk * hk) :=
  (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (place q)).1 S Y F

def frameOf (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : Frame q S Y where
  b := F.β
  b' := F.γ
  bb' := F.βγ
  b'b := F.γβ
  gl :=
    { toFun := fun g => ((locGrp q S Y F).1 g).exists.choose
      map_one' := ((locGrp q S Y F).1 1).unique ((locGrp q S Y F).1 1).exists.choose_spec (isLoc_one q F)
      map_mul' := fun g g' => ((locGrp q S Y F).1 (g * g')).unique ((locGrp q S Y F).1 (g * g')).exists.choose_spec
        ((locGrp q S Y F).2.2 _ _ _ _ ((locGrp q S Y F).1 g).exists.choose_spec
          ((locGrp q S Y F).1 g').exists.choose_spec) }
  gl_supp g := ((locGrp q S Y F).1 g).exists.choose_spec.1
  gl_mat g := ((locGrp q S Y F).1 g).exists.choose_spec.2

def stdLat (k : Type) [Field k] [ValuativeRel k] (Y : Type) : Submodule 𝒪[k] (Y → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

/- English proof (translation)
Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Conclude with `forall_congr' fun i => ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨y i, h⟩, rfl⟩⟩`.
-/
theorem mem_std {Y : Type} (y : Y → k) : y ∈ stdLat k Y ↔ ∀ i, y i ∈ 𝒪[k] := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨y i, h⟩, rfl⟩⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx'` using `(mem_std x).1 hx`. Establish `: x = ∑ i, (⟨x i, hx' i⟩ : 𝒪[k]) • (Pi.single i 1 : Y → k)`. Use function extensionality and compare the values at `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply, Subring.smul_def, smul_eq_mul]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `(mem_std _).2 fun i => ?_` and prove the remaining obligations. Use `show (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k]`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
theorem std_eq_span (Y : Type) [Fintype Y] [DecidableEq Y] :
    stdLat k Y = Submodule.span 𝒪[k] (Set.range fun i : Y => (Pi.single i 1 : Y → k)) := by
  apply le_antisymm
  · intro x hx
    have hx' := (mem_std x).1 hx
    have : x = ∑ i, (⟨x i, hx' i⟩ : 𝒪[k]) • (Pi.single i 1 : Y → k) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine (mem_std _).2 fun i => ?_
    show (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k]
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

/- English proof (translation)
Rewrite using `[std_eq_span]; exact Submodule.fg_span (Set.finite_range _) span_eq_top := by`. Apply `eq_top_iff.mpr` to reduce the goal to its premises. Rewrite using `[← (Pi.basisFun k Y).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `(mem_std _).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply, Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem isLattice_std (Y : Type) [Fintype Y] [DecidableEq Y] : Submodule.IsLattice k (stdLat k Y) where
  fg := by rw [std_eq_span]; exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    apply eq_top_iff.mpr
    rw [← (Pi.basisFun k Y).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine (mem_std _).2 fun j => ?_
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

/- English proof (translation)
Introduce `a ha`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.1 ha`. Use `Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩`.
-/
theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

/- English proof (translation)
Introduce `y hy`. Take `⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩` from `GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)`. Establish `hyv` using `((hSv S).2.2.2 L y hL).1 hy`. Establish `hoff` using `((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2`. Establish `hy₀ : y ∈ latV S L (· ≠ v₀)`.

Rewrite using `[hoff L y hL]`. Use `⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩` and prove the remaining obligations. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Conclude with `hyv.2 u rfl e he`.

Take `⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩` from `GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)`. Establish `hz : e • y = 0`. Use function extensionality and compare the values at `i`. Establish `hyi : y i ∈ idOff D (· = u)` using `(Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩`. Express the relevant statement in the definitionally equal form `e * y i = 0`.

Rewrite using `[← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]`. Rewrite using `[hz]`. Conclude with `zero_mem _`. Rewrite `hy₀` using `[h]`. Establish `h2` using `((hoff L' y hL').1 hy₀).2 v hv ε hεint`.

Establish `hεy : ε • y = y` using `funext fun i => (hεat (y i)).1 (hyv.1 i)`. Rewrite `h2` using `[hεy]`. Then use the resulting hypothesis.
-/
theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

/- English proof (translation)
Introduce `D k _ _ _ _ q S Y _ _ F L₀ hL₀`. Take `⟨M, hM, hMΛ, hoff⟩` from `GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k q S Y (frameOf q S Y F) L₀ (stdLat k Y) hL₀ (isLattice_std Y)`. Use `⟨M, hM, fun v hv => le_antisymm (latV_le_of_off hM.1 hL₀.1 hv hoff) (latV_le_of_off hL₀.1 hM.1 hv hoff.symm), fun y => ?_⟩` and prove the remaining obligations. Conclude with `(mem_std y).symm.trans (hMΛ y)`.
-/
theorem exists_selfDual_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (L₀ : Lat S), IsSelfDualC S L₀ → ∃ L : Lat S, IsSelfDualC S L ∧ (∀ v, v ≠ q.v → latV S L (· = v) = latV S L₀ (· = v)) ∧ ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV S L (· = q.v) := by
  intro D k _ _ _ _ q S Y _ _ F L₀ hL₀
  obtain ⟨M, hM, hMΛ, hoff⟩ :=
    GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k q S Y (frameOf q S Y F) L₀ (stdLat k Y) hL₀ (isLattice_std Y)
  refine ⟨M, hM, fun v hv => le_antisymm (latV_le_of_off hM.1 hL₀.1 hv hoff)
    (latV_le_of_off hL₀.1 hM.1 hv hoff.symm), fun y => ?_⟩
  exact (mem_std y).symm.trans (hMΛ y)

end GlobalTheory.SplitLat
