import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel

namespace GlobalTheory.LatPresc

variable {D : D7}

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
The claim follows from `le_antisymm (latV_le_of_off hL hL' hv h) (latV_le_of_off hL' hL hv h.symm)`.
-/
theorem latV_eq_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) = latV S L' (· = v) :=
  le_antisymm (latV_le_of_off hL hL' hv h) (latV_le_of_off hL' hL hv h.symm)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `Frame.IsLat`. Rewrite using `[h]`.
-/
theorem isLat_congr {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    {L L' : Lat S} (h : latV S L (· = p.v) = latV S L' (· = p.v)) (Λ : Submodule 𝒪[k] (n → k)) :
    β.IsLat L Λ ↔ β.IsLat L' Λ := by
  unfold Frame.IsLat
  rw [h]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩`. Consider the case `cons i l ih`. Take `⟨M, hM, h1, h2⟩` from `ih`. Take `⟨M', hM', h3, h4⟩` from `GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k (p i) S n (β i) M (Λ i) hM (hΛ i)`.

Use `⟨M', hM', fun i' hi' => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : i' = i`. Substitute `e` using the available equality. Conclude with `h3`. Establish `hne : (p i').v ≠ (p i).v` using `fun e' => e (hp e')`.

Conclude with `(isLat_congr (β i') (latV_eq_of_off hM'.1 hM.1 hne h4) (Λ i')).2 (h1 i' ((List.mem_cons.1 hi').resolve_left e))`. Conclude with `(latV_eq_of_off hM'.1 hM.1 (hv i (List.mem_cons_self ..)) h4).trans (h2 v fun i' hi' => hv i' (List.mem_cons_of_mem _ hi'))`.
-/
theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i ∈ l, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k (p i) S n (β i) M (Λ i) hM (hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => ?_⟩
    · by_cases e : i' = i
      · subst e; exact h3
      · have hne : (p i').v ≠ (p i).v := fun e' => e (hp e')
        exact (isLat_congr (β i') (latV_eq_of_off hM'.1 hM.1 hne h4) (Λ i')).2
          (h1 i' ((List.mem_cons.1 hi').resolve_left e))
    · exact (latV_eq_of_off hM'.1 hM.1 (hv i (List.mem_cons_self ..)) h4).trans
        (h2 v fun i' hi' => hv i' (List.mem_cons_of_mem _ hi'))

/- English proof (translation)
Introduce `D k _ _ _ _ ι p I P hP n _ _ S α L hL Λ hΛ`. Take `⟨M, hM, h1, h2⟩` from `exists_modify hP.inj α Λ hΛ hL I`. Conclude with `⟨M, hM, fun i => h1 i (hP.all i), fun x hx => h2 x fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)⟩`.
-/
theorem latAll : ∀ D : D7, LatAll D := by
  intro D k _ _ _ _ ι p I P hP n _ _ S α L hL Λ hΛ
  obtain ⟨M, hM, h1, h2⟩ := exists_modify hP.inj α Λ hΛ hL I
  exact ⟨M, hM, fun i => h1 i (hP.all i), fun x hx => h2 x fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)⟩

end GlobalTheory.LatPresc
