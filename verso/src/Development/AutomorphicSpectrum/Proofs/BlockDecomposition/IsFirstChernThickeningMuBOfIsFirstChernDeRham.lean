import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernRationalLift

variable {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)

abbrev famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) : C ⥤ Thick (smFun X q) :=
  G ⋙ (smO γ q 1 s {⊤}).G ⋙ (TO q 1 s {⊤}).ι

/- English proof (translation)
The claim follows from `Category.comp_id _`.
-/
theorem pt_famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) (c : C) :
    pt ((famK γ q s G).obj c) = pt (G.obj c).obj := Category.comp_id _

def liftK {C : Type 1} [Category.{0} C] {G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory} {D : E.LineData X}
    (Λ : B.CLift (q := q) (b := nlBase B' I γ 0) (ht := rfl) (κ := κA K I) (G ⋙ (TS γ q 1 s {⊤}).ι) D) :
    CLiftK (famK γ q s G) D where
  p c := Λ.p c
  hp c := (Λ.hp c).trans (Category.comp_id _).symm
  w φ := Λ.w φ
  hw φ h := Λ.hw φ h

/- English proof (translation)
Introduce `C _ G hG Λ`. Establish `hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥` using `fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1`. Establish `hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c')`. Introduce `c'`. Take `⟨V, ⟨σ, hσ⟩, hU⟩` from `hG c'`.

Use `⟨V, σ, hσ, ?_⟩` and prove the remaining obligations. Unfold `InU`. Rewrite using `[pt_famK]`. Conclude with `hU`. Take `⟨z, hz, hzv, hcls⟩` from `h s C (famK γ q s G) hpd hV (liftK γ q s Λ)`.

Set `m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B')` to `⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩`. Establish `e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z`. Use function extensionality and compare the values at `σ`. Conclude with `(hzv σ).symm`. Establish `hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0`.

Rewrite using `[m'.d_pullC, hz, map_zero]`. Establish `hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0` using `(congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb`. Use `⟨hz', ?_⟩` and prove the remaining obligations. Establish `e1` using `CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb`. Establish `e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) = m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c)`.

Establish `a1` using `(CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1`. Establish `a2` using `(CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o) (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1`. Establish `b` using `(CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1`. Conclude with `(congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)`. Rewrite using `[e2, ← hcls]`.

Use `Eq.trans ?_ e1.symm` and prove the remaining obligations. Establish `key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0), a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha = (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb`. Introduce and unpack `_ _ rfl`. Both sides reduce to the same expression. Conclude with `key _ hz' e`.
-/
theorem isFirstChernThickening_muB_of_isFirstChernDeRham (D : E.LineData X) (c : HdR q 2) (h : IsFirstChernDeRham q D c) :
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := by
  intro C _ G hG Λ
  have hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥ := fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1
  have hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c') := by
    intro c'
    obtain ⟨V, ⟨σ, hσ⟩, hU⟩ := hG c'
    refine ⟨V, σ, hσ, ?_⟩
    unfold InU
    rw [pt_famK]
    exact hU
  obtain ⟨z, hz, hzv, hcls⟩ := h s C (famK γ q s G) hpd hV (liftK γ q s Λ)
  let m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B') :=
    ⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩
  have e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z := by
    funext σ
    exact (hzv σ).symm
  have hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0 := by
    rw [m'.d_pullC, hz, map_zero]
  have hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0 := (congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb
  refine ⟨hz', ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb
  have e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) =
      m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c) := by
    have a1 := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1
    have a2 := (CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o)
      (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1
    have b := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1
    exact (congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)
  rw [e2, ← hcls]
  refine Eq.trans ?_ e1.symm
  have key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0),
      a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha =
        (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb := by
    rintro _ _ rfl
    rfl
  exact key _ hz' e

end GlobalTheory.CompanionTheory.FirstChernRationalLift
