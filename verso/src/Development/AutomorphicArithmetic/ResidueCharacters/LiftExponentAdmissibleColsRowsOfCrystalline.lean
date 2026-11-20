import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open Module GlobalTheory.LiftExpSplit

namespace UpperTheory.N

variable {D : D7}

/- English proof (translation)
Introduce `V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'`. Set `T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)` to `{ V := V1, ρ := ρ1, cont := hc1, L := L1 }`. Set `T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)` to `{ V := V2, ρ := ρ2, cont := hc2, L := L2 }`. Take `⟨hcr1, hj1⟩` from `subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₁ hs1`. Take `⟨hcr2, -⟩` from `subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₂ hs2`.

Conclude with `hK N h (D.nbr i w hw).Kw C.LL (hC w hw C) T₁ T₂ F hcr1 hcr2 hF' hj1`.
-/
theorem liftAt_of_liftK (i : D.nd.Loc) (N : ℕ) (hK : LiftK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    {ι : Type} {k : ℕ} (Ms : ι → Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1)
    (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)) (h : ℕ)
    (hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)))
    (hS : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)) τ (Set.Icc (-(h : ℤ)) h)) :
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : ι => ⇑(Ms x)) (eL (D.nd.l i) N h) := by
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'
  let T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V1, ρ := ρ1, cont := hc1, L := L1 }
  let T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V2, ρ := ρ2, cont := hc2, L := L2 }
  obtain ⟨hcr1, hj1⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₁ hs1
  obtain ⟨hcr2, -⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₂ hs2
  exact hK N h (D.nbr i w hw).Kw C.LL (hC w hw C) T₁ T₂ F hcr1 hcr2 hF' hj1

/- English proof (translation)
Establish `hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D` using `D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)`. Establish `hj` using `D.nd.j_range i`. Establish `hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L`. Unfold `AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB`. Expand and normalize the polynomial expressions, which then agree.

Establish `hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ (Set.Icc (-(Formalism.MainNotions.N.h …`. Introduce `w hw C x τ a ha`. Take `⟨g, ρ, -, hx, -⟩` from `hA i (X.r i) (hgood i) w hw C τ`. Establish `hq` using `(hx x a).1.mp ha`. Establish `hb` using `he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq`.

Establish `hb2` using `he.2.1`. Apply `mem_window L a` to reduce the goal to its premises. Establish `hc : (((a : ℚ) : ℝ)) = (a : ℝ)` using `by push_cast; rfl`. Rewrite `hb` using `[hc]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ (Set.Icc (-(Formalism.MainNotions.N.h …`. Introduce `w hw C x τ a ha`. Take `⟨g, ρ, -, hx, -⟩` from `hA i (X.r i) (hgood i) w hw C τ`. Establish `hq` using `(hx x a).2.2.1.mp ha`. Establish `hb` using `he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq`.

Establish `hb2` using `he.2.1`. Apply `mem_window L a` to reduce the goal to its premises. Establish `hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1` using `by push_cast; rfl`. Rewrite `hb` using `[hc]`. Rewrite `hb`, the goal using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith [hb.1, hb.2]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `w hw _ C _`. Conclude with `liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C) (Formalism.MainNotions.N.hN L) (hT w hw C) (fun x => hwinT w hw C x)`. Introduce `w hw _ C _`.

Conclude with `liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x)) (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C) (Formalism.MainNotions.N.hN L) (hD w hw C) (fun x => hwinD w hw C x)`.
-/
theorem lift_exponent_admissible_cols_rows_of_crystalline (L : SizeData₂ D) (i : D.nd.Loc) (N : ℕ) (hK : LiftK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (X : KillingConditions.HubData D) (dc : TruncatedSeriesCountingIdentities.Decl D i) (hgood : ∀ i, GoodR D.nd i (X.r i)) (ep : Bool) (hA : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep)
    (he : AdmissibleParameterJ.JumpAbsoluteBound L) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i)
    (hT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))))
    (hD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x)))) :
    EmbeddingTypes.LiftExponentColumn i (X.r i) dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L)) ∧
      EmbeddingTypes.LiftExponentDualPlaces i (X.r i) dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L)) := by
  have hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)
  have hj := D.nd.j_range i
  have hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L := by
    unfold AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB; ring

  have hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((a : ℚ) : ℝ)) = (a : ℝ) := by push_cast; rfl
    rw [hc] at hb
    linarith
  have hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).2.2.1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1 := by push_cast; rfl
    rw [hc] at hb
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  refine ⟨?_, ?_⟩
  · intro w hw _ C _
    exact liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (hT w hw C) (fun x => hwinT w hw C x)
  · intro w hw _ C _
    exact liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (hD w hw C) (fun x => hwinD w hw C x)

end UpperTheory.N

end
