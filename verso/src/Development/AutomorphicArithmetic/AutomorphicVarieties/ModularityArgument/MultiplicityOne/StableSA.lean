import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula UpperTheory.V.Z.Mult

/- English proof (translation)
Introduce `hEn hP hG E _ _ _ hunr n hn l₁ l₂`. Take `⟨c₀, hc₀, hl⟩` from `hG E hunr n hn l₁ l₂`. Use `⟨c₀, hc₀, fun π hreg hd hinf S hS Z hZ B τ hB hτ => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hst⟩` from `hl π hreg hd hinf S hS Z hZ B τ hB hτ`. Use `⟨c, hc, fun φ hφ hr => ?_⟩` and prove the remaining obligations.

Take `⟨J, _, D, B₁, hD, hInf, hbd⟩` from `hst φ hφ hr`. Establish `hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w`. Introduce `w hw`. Establish `hcw : cPl w = w`. Assume the negation of the conclusion as `h`.

Conclude with `hw (((hP E).2.1 w).2.2 h)`. Establish `hwZ : w ∉ Z` using `fun h => hw (hZ w h).2`. Conclude with `⟨hwZ, by rwa [hcw]⟩`. Set `good : J → Prop` to `fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w`. Use `⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1, fun j => j.2, ?_⟩` and prove the remaining obligations.

Introduce `T hT hTZ e₁ e₂ ρ hρ hlt`. Establish `hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w`. Introduce `i`. Establish `h` using `i.2`. Simplify using `only [good, not_forall] at h`.

Take `⟨w, h1, h2, h3⟩` from `h`. Conclude with `⟨w, h1, h2, h3⟩`. Use `choose u hu1 hu2 hu3 using hbad`. Establish `hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n` using `fun j w hw => sat_card ((hD j).2 w (hoff w hw))`. Establish `hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n` using `fun w hw => (hB w (hoff w hw)).card`.

Take `⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩` from `hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0) (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)`. Establish `hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0` using `fun j hj => hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩`. Establish `hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0` using `hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩`. Establish `hsm` using `hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by`. Distinguish the cases in `hj : good j`.

Rewrite using `[hvj j hj]`. Conclude with `hlt ⟨j, hj⟩`. Establish `h0 : val T' e₁' e₂' (B₁ j) 0 = 0` using `hzero ⟨j, hj⟩`. Rewrite using `[h0, norm_zero]`. Conclude with `hρ`.

Simplify `hsm` using `only [hgeom, hvB]`.
-/
theorem UpperTheory.V.Z.Mult.stableSA :
    Enlarge → Places → StableBlockGA → StableBlockSA := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn l₁ l₂
  obtain ⟨c₀, hc₀, hl⟩ := hG E hunr n hn l₁ l₂
  refine ⟨c₀, hc₀, fun π hreg hd hinf S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl π hreg hd hinf S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
