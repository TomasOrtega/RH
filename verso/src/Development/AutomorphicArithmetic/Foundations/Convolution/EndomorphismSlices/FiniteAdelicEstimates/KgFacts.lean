import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.FinLevelHolds

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Simplify using `only [Kg, Subgroup.mem_iInf, Subgroup.mem_inf]`. Use `forall_congr' fun w => forall_congr' fun _ => and_congr_right fun _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : IsSplitAt w`. Simplify using `[h, Subgroup.mem_comap]`. Simplify using `[h]`.
-/
private theorem mem_Kg {S : Set (Pl E)} {L : ∀ w : Pl E, Subgroup (GLw n w)} {g : GL (Fin n) (Af E)} :
    g ∈ Kg S L ↔ ∀ w ∈ S, Slots.loc n w g ∈ L w ∧ (IsSplitAt w → Slots.loc n w (thF E n g) ∈ L w) := by
  simp only [Kg, Subgroup.mem_iInf, Subgroup.mem_inf]
  refine forall_congr' fun w => forall_congr' fun _ => and_congr_right fun _ => ?_
  by_cases h : IsSplitAt w
  · simp [h, Subgroup.mem_comap]
  · simp [h]

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)`.
-/
private theorem continuous_thF' : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

/- English proof (translation)
Simplify using `only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]`.
-/
private theorem mem_Kf {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ w, Slots.loc n w g ∈ KGL w n := by
  simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]

/- English proof (translation)
The claim follows from `mem_Kf.2 fun u => Slots.loc_thF_mem u (mem_Kf.1 hg _)`.
-/
private theorem thF_mem_Kf {g : GL (Fin n) (Af E)} (hg : g ∈ Kf E n) : thF E n g ∈ Kf E n :=
  mem_Kf.2 fun u => Slots.loc_thF_mem u (mem_Kf.1 hg _)

/- English proof (translation)
Establish `e : ((Kf E n ⊓ ⨅ w ∈ Z, ((L w).comap (Slots.loc n w) ⊓ (L w).comap ((Slots.loc n w).comp (thF E n))) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) = (Kf E n : Set _) ∩ ⋂ w ∈ Z, (Slots.loc n w ⁻¹' (L w : Set _) ∩ (Slots.loc n w ∘ thF E n) ⁻¹' (L w : Set _))`. Use extensionality with `g`. Simplify using `[Subgroup.mem_iInf, Subgroup.mem_inf, Subgroup.mem_comap]`. Rewrite using `[e]`. Use `(PositivityTheory.Rg.BcB.G8.Fin.kfOC_holds E n).1.inter (isOpen_biInter_finset fun w _ => ?_)` and prove the remaining obligations.

Conclude with `((hL w).preimage (Slots.continuous_loc n w)).inter ((hL w).preimage ((Slots.continuous_loc n w).comp continuous_thF'))`.
-/
private theorem isOpen_cut (Z : Finset (Pl E)) (L : ∀ w : Pl E, Subgroup (GLw n w))
    (hL : ∀ w, IsOpen (L w : Set (GLw n w))) :
    IsOpen ((Kf E n ⊓ ⨅ w ∈ Z, ((L w).comap (Slots.loc n w) ⊓
      (L w).comap ((Slots.loc n w).comp (thF E n))) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have e : ((Kf E n ⊓ ⨅ w ∈ Z, ((L w).comap (Slots.loc n w) ⊓
      (L w).comap ((Slots.loc n w).comp (thF E n))) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) =
      (Kf E n : Set _) ∩ ⋂ w ∈ Z, (Slots.loc n w ⁻¹' (L w : Set _) ∩ (Slots.loc n w ∘ thF E n) ⁻¹' (L w : Set _)) := by
    ext g
    simp [Subgroup.mem_iInf, Subgroup.mem_inf, Subgroup.mem_comap]
  rw [e]
  refine (PositivityTheory.Rg.BcB.G8.Fin.kfOC_holds E n).1.inter (isOpen_biInter_finset fun w _ => ?_)
  exact ((hL w).preimage (Slots.continuous_loc n w)).inter
    ((hL w).preimage ((Slots.continuous_loc n w).comp continuous_thF'))

/- English proof (translation)
Introduce `E _ _ _ n S Z L hS hZ hL hoff`. Take `⟨-, hcp, -, hsec⟩` from `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `Subgroup.isOpen_mono ?_ (isOpen_cut Z L fun w => (hL w).1)` and prove the remaining obligations. Introduce `g hg`.

Take `⟨hgK, hgZ⟩` from `Subgroup.mem_inf.1 hg`. Use `mem_Kg.2 fun w hw => ?_` and prove the remaining obligations. Distinguish the cases in `hwZ : w ∈ Z`. Establish `h` using `Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hgZ w) hwZ)`. Conclude with `⟨h.1, fun _ => h.2⟩`.

Rewrite using `[hoff w hwZ]`. Conclude with `⟨mem_Kf.1 hgK w, fun _ => mem_Kf.1 (thF_mem_Kf hgK) w⟩`. Introduce `g hg`. Establish `hg'` using `mem_Kg.1 hg`. Use `mem_Kf.2 fun u => ?_` and prove the remaining obligations.

Break down `(hsec S hS u).1 with hu | hu` into its components or cases. Conclude with `(hL u).2 (hg' u hu).1`. Distinguish the cases in `hs : IsSplitAt (cPl u)`. Establish `h1 : Slots.loc n (cPl u) (thF E n g) ∈ KGL (cPl u) n` using `(hL _).2 ((hg' _ hu).2 hs)`. Establish `h2 : Slots.loc n u (thF E n (thF E n g)) ∈ KGL u n` using `Slots.loc_thF_mem u h1`.

Rewrite `h2` using `[GlobalTheory.EulerTw.Comm.thF_thF]`. Then use the resulting hypothesis. Establish `e1 : cPl (cPl u) = cPl u`. Assume the negation of the conclusion as `h`. Conclude with `hs ((hcp (cPl u)).2.2 h)`. Establish `e : cPl u = u` using `e1.symm.trans (hcp u).1`.

Rewrite `hu` using `[e]`. Conclude with `(hL u).2 (hg' u hu).1`. Introduce `w hw k hk`. Use `mem_Kg.2 fun u hu => ⟨?_, fun _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : u = w`.

Substitute `e` using the available equality. Rewrite using `[hoff u hw.1]`. Establish `h : Slots.loc n u (locGL E n u k) = k` using `pLoc_locGL _ _`. Rewrite using `[h]` and apply the resulting hypothesis. Establish `h : Slots.loc n u (locGL E n w k) = 1` using `pLoc_locGL_of_ne e k`.

Rewrite using `[h]`. Conclude with `one_mem _`. Distinguish the cases in `e : cPl u = w`. Establish `hu' : u = cPl w` using `by rw [← e, (hcp u).1]`. Establish `huZ : u ∉ Z` using `hu' ▸ hw.2`.

Rewrite using `[hoff u huZ]`. Use `Slots.loc_thF_mem u ?_` and prove the remaining obligations. Substitute `e` using the available equality. Establish `h : Slots.loc n (cPl u) (locGL E n (cPl u) k) = k` using `pLoc_locGL _ _`. Use `show Slots.loc n (cPl u) (locGL E n (cPl u) k) ∈ KGL (cPl u) n`.

Rewrite using `[h]` and apply the resulting hypothesis. Establish `h : Slots.loc n (Slots.cP u) (locGL E n w k) = Slots.loc n (Slots.cP u) 1`. Rewrite using `[map_one]`. Conclude with `pLoc_locGL_of_ne e k`. Rewrite using `[Slots.loc_thF_congr u h, map_one, map_one]`.

Conclude with `one_mem _`.
-/
theorem kgFacts : KgFacts := by
  intro E _ _ _ n S Z L hS hZ hL hoff
  obtain ⟨-, hcp, -, hsec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  refine ⟨?_, ?_, ?_⟩
  · refine Subgroup.isOpen_mono ?_ (isOpen_cut Z L fun w => (hL w).1)
    intro g hg
    obtain ⟨hgK, hgZ⟩ := Subgroup.mem_inf.1 hg
    refine mem_Kg.2 fun w hw => ?_
    by_cases hwZ : w ∈ Z
    · have h := Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hgZ w) hwZ)
      exact ⟨h.1, fun _ => h.2⟩
    · rw [hoff w hwZ]
      exact ⟨mem_Kf.1 hgK w, fun _ => mem_Kf.1 (thF_mem_Kf hgK) w⟩
  · intro g hg
    have hg' := mem_Kg.1 hg
    refine mem_Kf.2 fun u => ?_
    rcases (hsec S hS u).1 with hu | hu
    · exact (hL u).2 (hg' u hu).1
    · by_cases hs : IsSplitAt (cPl u)
      · have h1 : Slots.loc n (cPl u) (thF E n g) ∈ KGL (cPl u) n := (hL _).2 ((hg' _ hu).2 hs)
        have h2 : Slots.loc n u (thF E n (thF E n g)) ∈ KGL u n := Slots.loc_thF_mem u h1
        rwa [GlobalTheory.EulerTw.Comm.thF_thF] at h2
      · have e1 : cPl (cPl u) = cPl u := by
          by_contra h
          exact hs ((hcp (cPl u)).2.2 h)
        have e : cPl u = u := e1.symm.trans (hcp u).1
        rw [e] at hu
        exact (hL u).2 (hg' u hu).1
  · intro w hw k hk
    refine mem_Kg.2 fun u hu => ⟨?_, fun _ => ?_⟩
    · by_cases e : u = w
      · subst e
        rw [hoff u hw.1]
        have h : Slots.loc n u (locGL E n u k) = k := pLoc_locGL _ _
        rwa [h]
      · have h : Slots.loc n u (locGL E n w k) = 1 := pLoc_locGL_of_ne e k
        rw [h]
        exact one_mem _
    · by_cases e : cPl u = w
      · have hu' : u = cPl w := by rw [← e, (hcp u).1]
        have huZ : u ∉ Z := hu' ▸ hw.2
        rw [hoff u huZ]
        refine Slots.loc_thF_mem u ?_
        subst e
        have h : Slots.loc n (cPl u) (locGL E n (cPl u) k) = k := pLoc_locGL _ _
        show Slots.loc n (cPl u) (locGL E n (cPl u) k) ∈ KGL (cPl u) n
        rwa [h]
      · have h : Slots.loc n (Slots.cP u) (locGL E n w k) = Slots.loc n (Slots.cP u) 1 := by
          rw [map_one]
          exact pLoc_locGL_of_ne e k
        rw [Slots.loc_thF_congr u h, map_one, map_one]
        exact one_mem _

end UpperTheory.Zero.ConvolutionTheory.EB
