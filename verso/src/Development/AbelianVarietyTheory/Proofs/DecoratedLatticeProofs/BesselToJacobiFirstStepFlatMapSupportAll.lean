import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForallStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply]`. Establish `e : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V x) = Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V x))`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[e, hx, map_one]`.
-/
theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro x hx
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
  have e : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V x) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V x)) := by
    ext i j
    simp
  rw [e, hx, map_one]

/- English proof (translation)
Apply `congGrp_mono` to reduce the goal to its premises. Conclude with `le_iInf fun w => iInf_le_of_le ⟨w.1, by rw [w.2]; exact hv⟩ le_rfl`.
-/
theorem grpOff_le_at (V : HSp D) {P : Pl D → Prop} {v : Pl D} (hv : P v) : grpOff V P ≤ grpOff V (· = v) := by
  apply congGrp_mono
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, by rw [w.2]; exact hv⟩ le_rfl

/- English proof (translation)
Establish `hI : idOff D P = ⊤` using `by haveI : IsEmpty {w : Pl D // P w} := ⟨fun w => hP ⟨w.1, w.2⟩⟩`. Simplify using `[idOff]`. Rewrite using `[grpOff, hI, eq_top_iff]`. Introduce `x _`. Use `haveI : Subsingleton (AE D ⧸ (⊤ : Ideal (AE D))) := Ideal.Quotient.subsingleton_iff.mpr rfl`.

Conclude with `Subsingleton.elim _ _`.
-/
theorem grpOff_eq_top (V : HSp D) {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : grpOff V P = ⊤ := by
  have hI : idOff D P = ⊤ := by
    haveI : IsEmpty {w : Pl D // P w} := ⟨fun w => hP ⟨w.1, w.2⟩⟩
    simp [idOff]
  rw [grpOff, hI, eq_top_iff]
  intro x _
  haveI : Subsingleton (AE D ⧸ (⊤ : Ideal (AE D))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Subsingleton.elim _ _

/- English proof (translation)
Establish `h` using `((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 V).2.2.1`. Rewrite `h` using `[grpOff_eq_top V hP, inf_top_eq]`. Then use the resulting hypothesis.
-/
theorem grpAt_eq_bot (V : HSp D) {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : grpAt V P = ⊥ := by
  have h := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 V).2.2.1
  rwa [grpOff_eq_top V hP, inf_top_eq] at h

/- English proof (translation)
Rewrite using `[latO, AddSubgroup.closure_eq_bot_iff]`. Introduce and unpack `w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩`. Establish `h0 : α = 0`. Conclude with `RestrictedProduct.ext _ _ fun v => hα v fun h => hP ⟨v, h⟩`. Substitute `h0` using the available equality.

Use extensionality with `i j`. Simplify using `only [pairA, Prod.mk_zero_zero, Matrix.of_apply, Matrix.zero_apply]`. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem latO_eq_bot (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : latO S T LS LT P = ⊥ := by
  rw [latO, AddSubgroup.closure_eq_bot_iff]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    exact RestrictedProduct.ext _ _ fun v => hα v fun h => hP ⟨v, h⟩
  subst h0
  ext i j
  simp only [pairA, Prod.mk_zero_zero, Matrix.of_apply, Matrix.zero_apply]
  exact TensorProduct.zero_tmul _ _

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[heisO, symplOH, symplO, hO]`.
-/
theorem heisO_zero_eq (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

/- English proof (translation)
Introduce `ψ ρ B J s LV LV₀ LW LW₀ P hgood hunr hsdW Φ hΦ`. Use `⟨?_, fun g hg => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `κ κ' hκ hκ'`. Distinguish the cases in `hP : ∃ v, P v`. Take `⟨v, hv⟩` from `hP`.

Conclude with `GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v hv).sdV hsdW P (fun w hw => ⟨(hgood w hw).tame, (hunr w hw).1, (hunr w hw).2⟩) Φ hΦ κ κ' hκ hκ'`. Establish `h1 : κ = 1` using `Subgroup.mem_bot.mp (grpAt_eq_bot B.V hP ▸ hκ.1)`. Establish `h2 : κ' = 1` using `Subgroup.mem_bot.mp (grpAt_eq_bot J.W hP ▸ hκ'.1)`. Substitute `h1 h2` using the available equality. Rewrite using `[Prod.mk_one_one, map_one]`.

Both sides reduce to the same expression. Introduce `h hne`. Use `GlobalTheory.T.placewise_to_adelicDecomposition_forall D J.W LW P hsdW (jacGrp J.d) h ?_` and prove the remaining obligations. Introduce `v hv`. Take `⟨x, hx, y, hy, rfl⟩` from `((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 J.W).1 h`.

Use `⟨x, hx, y, hy, rfl, ?_⟩` and prove the remaining obligations. Establish `hsdV` using `(hgood v hv).sdV`. Establish `htameP : ∀ w, P w → Tame D w` using `fun w hw => (hgood w hw).tame`. Establish `htame1 : ∀ w : Pl D, w = v → Tame D w` using `fun w hw => hw ▸ htameP v hv`. Establish `hΦv : Vac ψ B.V J.W LV LW (· = v) Φ` using `((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW P htameP Φ).1.mp hΦ).2 v hv`.

Establish `hf : Vac ψ B.V J.W LV LW (· = v) (s.om (g, y) Φ)` using `(GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW (· = v) htame1 Φ).2.1 hΦv g (grpOff_le_at B.V hv hg) y hy`. Use `(GlobalTheory.T.oneCoset_besselToFourierJacobi D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s) ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hf).2 x hx ?_` and prove the remaining obligations. Establish `e : s.om (1, x) (s.om (g, y) Φ) = s.om (g, x * y) Φ`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Rewrite using `[e]`.

Conclude with `hne`. Introduce `h hh`. Distinguish the cases in `hP : ∃ v, P v`. Take `⟨v₀, hv₀⟩` from `hP`. Establish `htameP : ∀ w, P w → Tame D w` using `fun w hw => (hgood w hw).tame`.

Establish `hvacP` using `GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v₀ hv₀).sdV hsdW P htameP`. Establish `hf : Vac ψ B.V J.W LV LW P (s.om (g, h) Φ)` using `(hvacP Φ).2.1 hΦ g hg h hh`. Use `((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ (hgood v₀ hv₀).sdV₀ (hgood v₀ hv₀).sdW₀ P htameP _).1.mpr ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ hf.1`. Introduce `v hv`.

Establish `hfv` using `((hvacP _).1.mp hf).2 v hv`. Conclude with `(GlobalTheory.T.oneCoset_besselToFourierJacobi D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s) ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hfv).1`. Use `⟨((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ (s.weil.om_pres _ _ hΦ.1), ?_⟩` and prove the remaining obligations. Rewrite using `[latO_eq_bot _ _ _ _ hP]`. Use `⟨fun u hu => ?_, fun e _ u hu _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[AddSubgroup.mem_bot.mp hu, nsmul_zero, heisO_zero_eq]`. Rewrite using `[AddSubgroup.mem_bot.mp hu, heisO_zero_eq]`.
-/
theorem suppFirst_holds (D : D7) : SuppFirst D := by
  intro ψ ρ B J s LV LV₀ LW LW₀ P hgood hunr hsdW Φ hΦ
  refine ⟨?_, fun g hg => ⟨?_, ?_⟩⟩
  · intro κ κ' hκ hκ'
    by_cases hP : ∃ v, P v
    · obtain ⟨v, hv⟩ := hP
      exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v hv).sdV hsdW P
        (fun w hw => ⟨(hgood w hw).tame, (hunr w hw).1, (hunr w hw).2⟩) Φ hΦ κ κ' hκ hκ'
    · have h1 : κ = 1 := Subgroup.mem_bot.mp (grpAt_eq_bot B.V hP ▸ hκ.1)
      have h2 : κ' = 1 := Subgroup.mem_bot.mp (grpAt_eq_bot J.W hP ▸ hκ'.1)
      subst h1 h2
      rw [Prod.mk_one_one, map_one]
      rfl
  · intro h hne
    refine GlobalTheory.T.placewise_to_adelicDecomposition_forall D J.W LW P hsdW (jacGrp J.d) h ?_
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 J.W).1 h
    refine ⟨x, hx, y, hy, rfl, ?_⟩
    have hsdV := (hgood v hv).sdV
    have htameP : ∀ w, P w → Tame D w := fun w hw => (hgood w hw).tame
    have htame1 : ∀ w : Pl D, w = v → Tame D w := fun w hw => hw ▸ htameP v hv
    have hΦv : Vac ψ B.V J.W LV LW (· = v) Φ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW P htameP Φ).1.mp hΦ).2 v hv
    have hf : Vac ψ B.V J.W LV LW (· = v) (s.om (g, y) Φ) :=
      (GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW (· = v) htame1 Φ).2.1 hΦv g
        (grpOff_le_at B.V hv hg) y hy
    refine (GlobalTheory.T.oneCoset_besselToFourierJacobi D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s)
      ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hf).2 x hx ?_
    have e : s.om (1, x) (s.om (g, y) Φ) = s.om (g, x * y) Φ := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact hne
  · intro h hh
    by_cases hP : ∃ v, P v
    · obtain ⟨v₀, hv₀⟩ := hP
      have htameP : ∀ w, P w → Tame D w := fun w hw => (hgood w hw).tame
      have hvacP := GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v₀ hv₀).sdV hsdW P htameP
      have hf : Vac ψ B.V J.W LV LW P (s.om (g, h) Φ) := (hvacP Φ).2.1 hΦ g hg h hh
      refine ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ (hgood v₀ hv₀).sdV₀ (hgood v₀ hv₀).sdW₀ P
        htameP _).1.mpr ⟨?_, ?_⟩)
      · exact ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ hf.1
      · intro v hv
        have hfv := ((hvacP _).1.mp hf).2 v hv
        exact (GlobalTheory.T.oneCoset_besselToFourierJacobi D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s)
          ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hfv).1
    · refine ⟨((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ (s.weil.om_pres _ _ hΦ.1), ?_⟩
      rw [latO_eq_bot _ _ _ _ hP]
      refine ⟨fun u hu => ?_, fun e _ u hu _ => ?_⟩
      · rw [AddSubgroup.mem_bot.mp hu, nsmul_zero, heisO_zero_eq]
      · rw [AddSubgroup.mem_bot.mp hu, heisO_zero_eq]

end GlobalTheory.FinPl

/- English proof (translation)
The claim follows from `GlobalTheory.FinPl.suppFirst_holds`.
-/
theorem GlobalTheory.FinPl.suppFirst_all : ∀ D : D7, GlobalTheory.FinPl.SuppFirst D := GlobalTheory.FinPl.suppFirst_holds
