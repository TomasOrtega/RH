import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftIdeal

def conjO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjO (D : D7) (x : 𝓞 D.host.E) :
    ((conjO D x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[coe_conjO, coe_conjO]`. Simplify using the standard rewrite rules.
-/
theorem conjO_conjO (D : D7) (x : 𝓞 D.host.E) : conjO D (conjO D x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem star_eq (D : D7) (x : D.host.E) : star x = IsCMField.complexConj D.host.E x := rfl

/- English proof (translation)
Unfold `conjI`. Rewrite using `[Ideal.map]`. Use `congr 1`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, hb, h⟩`. Use `⟨b, hb, RingOfIntegers.ext ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Both sides reduce to the same expression. Introduce and unpack `⟨b, hb, rfl⟩`.

Conclude with `⟨b, hb, rfl⟩`.
-/
theorem conjI_eq_map (D : D7) (I : Ideal (𝓞 D.host.E)) :
    conjI I = I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, RingOfIntegers.ext ?_⟩
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

/- English proof (translation)
Rewrite using `[Ideal.map_map]`. Establish `: ((conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).comp (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = RingHom.id _` using `RingHom.ext fun x => conjO_conjO D x`. Rewrite using `[this, Ideal.map_id]`.
-/
theorem map_map_conjO (D : D7) (I : Ideal (𝓞 D.host.E)) :
    (I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = I := by
  rw [Ideal.map_map]
  have : ((conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).comp (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = RingHom.id _ :=
    RingHom.ext fun x => conjO_conjO D x
  rw [this, Ideal.map_id]

end GlobalTheory.LiftIdeal

end

noncomputable section

namespace GlobalTheory.LiftIdeal

open GlobalTheory.LiftLevel

/- English proof (translation)
Use `haveI := PP.isMaximal`. Conclude with `Ideal.map_isMaximal_of_equiv (conjO D)`.
-/
theorem isMaximal_map (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) :
    (PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := by
  haveI := PP.isMaximal
  exact Ideal.map_isMaximal_of_equiv (conjO D)

/- English proof (translation)
Unfold `liftI`. Conclude with `Finset.prod_congr rfl fun PP _ => conjI_eq_map D _`.
-/
theorem liftI_eq (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    liftI Pg Q = ∏ PP ∈ Pg ∪ Q, PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold liftI
  exact Finset.prod_congr rfl fun PP _ => conjI_eq_map D _

/- English proof (translation)
Rewrite using `[conjI_eq_map, liftI_eq]`. Use `map_prod (Ideal.mapHom (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (Pg ∪ Q)` as an intermediate fact. Simplify using `only [Ideal.mapHom_apply] at this`. Rewrite using `[this]`. Conclude with `Finset.prod_congr rfl fun PP _ => map_map_conjO D _`.
-/
theorem conjI_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    conjI (liftI Pg Q) = ∏ PP ∈ Pg ∪ Q, PP.asIdeal := by
  rw [conjI_eq_map, liftI_eq]
  have := map_prod (Ideal.mapHom (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
    (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (Pg ∪ Q)
  simp only [Ideal.mapHom_apply] at this
  rw [this]
  exact Finset.prod_congr rfl fun PP _ => map_map_conjO D _

/- English proof (translation)
Introduce `h`. Use `GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP' fun c hc => ?_` and prove the remaining obligations. Use `⟨conjO D c, h ▸ Ideal.mem_map_of_mem _ hc, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_conjO, star_eq]`.
-/
theorem map_ne {D : D7} {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ S) (hP' : PP' ∈ S) :
    PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ PP'.asIdeal := by
  intro h
  refine GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP' fun c hc => ?_
  refine ⟨conjO D c, h ▸ Ideal.mem_map_of_mem _ hc, ?_⟩
  rw [coe_conjO, star_eq]

/- English proof (translation)
Introduce `D Pg Q e hne h2 he`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨P0, hP0⟩` from `hne`. Introduce `htop`. Establish `hle : liftI Pg Q ≤ P0.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)`.

Rewrite using `[liftI_eq]`. Conclude with `Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hP0))`. Rewrite `hle` using `[htop]`. Conclude with `(isMaximal_map D P0).ne_top (top_le_iff.1 hle)`. Rewrite using `[liftI_eq, ← Ideal.zero_eq_bot]`.

Use `Finset.prod_ne_zero_iff.2 fun PP _ => ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (f := (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (conjO D).injective]`. Conclude with `PP.ne_bot`. Rewrite using `[conjI_liftI, liftI_eq]`. Use `IsCoprime.prod_left fun PP hP => IsCoprime.prod_right fun PP' hP' => ?_` and prove the remaining obligations.

Conclude with `Ideal.isCoprime_iff_sup_eq.2 ((isMaximal_map D PP).coprime_of_ne PP'.isMaximal (map_ne he hP hP'))`. Rewrite using `[liftI_eq]`. Use `IsCoprime.prod_left fun PP hP => Ideal.isCoprime_iff_sup_eq.2 ?_` and prove the remaining obligations. Establish `h2' : (2 : 𝓞 D.host.E) ∉ PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)`. Rewrite using `[Ideal.map_comap_of_equiv, Ideal.mem_comap, map_ofNat]`.

Conclude with `h2 PP (Finset.mem_union.1 hP)`. Conclude with `(isMaximal_map D PP).out.2 _ (left_lt_sup.2 fun hle => h2' (hle (Ideal.mem_span_singleton_self 2)))`.
-/
theorem liftI_props : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) →
    GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  intro D Pg Q e hne h2 he
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P0, hP0⟩ := hne
    intro htop
    have hle : liftI Pg Q ≤ P0.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [liftI_eq]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hP0))
    rw [htop] at hle
    exact (isMaximal_map D P0).ne_top (top_le_iff.1 hle)
  · rw [liftI_eq, ← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
    rw [Ne, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (f := (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (conjO D).injective]
    exact PP.ne_bot
  · rw [conjI_liftI, liftI_eq]
    refine IsCoprime.prod_left fun PP hP => IsCoprime.prod_right fun PP' hP' => ?_
    exact Ideal.isCoprime_iff_sup_eq.2
      ((isMaximal_map D PP).coprime_of_ne PP'.isMaximal (map_ne he hP hP'))
  · rw [liftI_eq]
    refine IsCoprime.prod_left fun PP hP => Ideal.isCoprime_iff_sup_eq.2 ?_
    have h2' : (2 : 𝓞 D.host.E) ∉ PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, map_ofNat]
      exact h2 PP (Finset.mem_union.1 hP)
    exact (isMaximal_map D PP).out.2 _ (left_lt_sup.2 fun hle => h2' (hle (Ideal.mem_span_singleton_self 2)))

end GlobalTheory.LiftIdeal

end
