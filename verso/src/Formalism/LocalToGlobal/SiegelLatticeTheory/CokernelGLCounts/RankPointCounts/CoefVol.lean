import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB MeasureTheory
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section VolStep

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxProd : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    EligAt γ w → PairVal.NormRep γ w F' L U →
      PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
        ((PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard : ℝ) *
          ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
            (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

end VolStep

section Good

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

open Formalism.L2.SG.Pf.LocUnramB in

/- English proof (translation)
Take `⟨w₀, hw₀, xy0, hxy0⟩` from `hYo`. Establish `hint` using `orb_int T T' w p hA hg w₀ hw₀`. Take `⟨h1, h2⟩` from `hint xy0.1 xy0.2 (by rw [← hxy0]; exact hYi)`. Establish `hO : kkOrb M p Y = kkOrb M p (modMat δ T T' p w)` using `kkOrb_eq p (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow _)) h1 (isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp _ _)) h2 hxy0`. Use `set H := monoW T T' w p hA hg`.

Establish `hOK` using `hA.1`. Use `hOK.haar.sf` as an intermediate fact. Unfold `wtL`. Rewrite using `[hw₀]`. Simplify using `only`.

Establish `hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep) | Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y} = (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) ×ˢ (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep))`. Use extensionality with `⟨x, y⟩`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]`. Rewrite using `[hO]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨l, ρ, hl, hρ, he⟩`. Establish `hYint : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R`. Rewrite using `[he]`. Conclude with `int_mul _ (int_mul _ hl.2.2 H.int) hρ.2.2`. Take `⟨h1, h2⟩` from `hint x y hYint`.

Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `h1 i.1.1 i.1.2` as an intermediate fact. Simplify using `only [Loc.uLow, if_neg (ne_of_gt i.2), dif_pos i.2] at this`. Conclude with `this`. Use `h2 i.1.1 i.1.2` as an intermediate fact.

Simplify using `only [Loc.uUp, if_neg (ne_of_lt i.2.1), dif_pos i.2] at this`. Conclude with `this`. Introduce and unpack `⟨hx, hy⟩`. Establish `hL` using `isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x)`. Establish `hN` using `isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ y)`.

Use `⟨Loc.uLow x, Loc.uUp w₀ y, ⟨hL.1, hL.2, fun a b => ?_⟩, ⟨hN.1, hN.2, fun a b => ?_⟩, rfl⟩` and prove the remaining obligations. Unfold `Loc.uLow split_ifs`. Conclude with `(M p).R.one_mem`. Conclude with `hx _`. Conclude with `(M p).R.zero_mem`.

Unfold `Loc.uUp split_ifs`. Conclude with `(M p).R.one_mem`. Conclude with `hy _`. Conclude with `(M p).R.zero_mem`. Rewrite using `[hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]`.

Simplify using `[hOK.haar.volR]`.
-/
theorem wtL_good (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p)
    (hg : Good δ M w p) {Y : MatP D p} (hYi : IntP M p Y) (hYo : InOrbP δ T T' p w Y) :
    wtL M δ T T' p w Y = 1 := by
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hYo
  have hint := orb_int T T' w p hA hg w₀ hw₀
  obtain ⟨h1, h2⟩ := hint xy0.1 xy0.2 (by rw [← hxy0]; exact hYi)
  have hO : kkOrb M p Y = kkOrb M p (modMat δ T T' p w) :=
    kkOrb_eq p (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow _)) h1
      (isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp _ _)) h2 hxy0
  set H := monoW T T' w p hA hg
  have hOK := hA.1
  have := hOK.haar.sf
  unfold wtL
  rw [hw₀]
  simp only
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y} =
      (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) ×ˢ
        (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
    rw [hO]
    constructor
    · rintro ⟨l, ρ, hl, hρ, he⟩
      have hYint : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R := by
        rw [he]; exact int_mul _ (int_mul _ hl.2.2 H.int) hρ.2.2
      obtain ⟨h1, h2⟩ := hint x y hYint
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h1 i.1.1 i.1.2
        simp only [Loc.uLow, if_neg (ne_of_gt i.2), dif_pos i.2] at this
        exact this
      · have := h2 i.1.1 i.1.2
        simp only [Loc.uUp, if_neg (ne_of_lt i.2.1), dif_pos i.2] at this
        exact this
    · rintro ⟨hx, hy⟩
      have hL := isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x)
      have hN := isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ y)
      refine ⟨Loc.uLow x, Loc.uUp w₀ y, ⟨hL.1, hL.2, fun a b => ?_⟩, ⟨hN.1, hN.2, fun a b => ?_⟩, rfl⟩
      · unfold Loc.uLow
        split_ifs
        · exact (M p).R.one_mem
        · exact hx _
        · exact (M p).R.zero_mem
      · unfold Loc.uUp
        split_ifs
        · exact (M p).R.one_mem
        · exact hy _
        · exact (M p).R.zero_mem
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  simp [hOK.haar.volR]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Establish `hall` using `LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset`. Rewrite `hall` using `[Filter.eventually_cofinite]`. Use `hall.subset fun p hp => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq]`. Introduce `hg`.

Apply `hp` to reduce the goal to its premises. Take `⟨hyI, hyO⟩` from `hC γ w hγ p`. Use `show (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) = 1`. Rewrite using `[wtL_good _ _ w p (hA p) hg hyI hyO, Complex.ofReal_one]`.
-/
theorem wtL_finite (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) :
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite := by
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine hall.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq]
  intro hg
  apply hp
  obtain ⟨hyI, hyO⟩ := hC γ w hγ p
  show (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) = 1
  rw [wtL_good _ _ w p (hA p) hg hyI hyO, Complex.ofReal_one]

/- English proof (translation)
Introduce `γ w hγ`. Use `⟨wtL_finite hA hC hγ, ?_⟩` and prove the remaining obligations. Establish `hγ0` using `hγ`. Establish `hrel : γ.relevant` using `PCount.eligRel_holds γ w hγ`. Take `⟨⟨hgen, -⟩, hat⟩` from `hγ`.

Take `⟨y, hy⟩` from `hN γ w hat hrel hgen`. Establish `hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2` using `⟨(w, y), hy⟩`. Establish `hn : nrep γ = some hex.choose` using `dif_pos hex`. Establish `hz : zT γ = ZhatL (lf D F0) hex.choose.2.1` using `by unfold zT; rw [hn]`. Establish `hv : PairVal.vRdef D u u' F0 what₂ δ M γ = PairVal.volIdx D u u' F0 what₂ δ M γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1`.

Unfold `PairVal.vRdef`. Rewrite using `[dif_pos ⟨hrel, hgen, hex⟩]`. Establish `hspec` using `hex.choose_spec`. Take `⟨hRep, -, hL, hU, e⟩` from `hspec`. Take `⟨F₁, hR₁, -, hc₁⟩` from `hat`.

Establish `hw : w = hex.choose.1` using `pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩`. Establish `hγ' : EligAt γ hex.choose.1` using `hw ▸ hγ0`. Establish `key` using `hVP hA hT hrows γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 hγ' hex.choose_spec`. Establish `hcast : ((∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℝ) : ℂ) = ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)` using `Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _`. Rewrite using `[← hcast, hv, key, ← hw]`.

Simplify using `only [yT, hz, Complex.ofReal_mul, Complex.ofReal_natCast]`.
-/
theorem volProd_of (hA : ∀ p, Agree δ M p)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hC : LocClsE M δ u u' F0 what₂)
    (hVP : VolIdxProd M δ u u' F0 what₂) : VolProd M δ u u' F0 what₂ := by
  intro γ w hγ
  refine ⟨wtL_finite hA hC hγ, ?_⟩
  have hγ0 := hγ
  have hrel : γ.relevant := PCount.eligRel_holds γ w hγ
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by unfold zT; rw [hn]
  have hv : PairVal.vRdef D u u' F0 what₂ δ M γ =
      PairVal.volIdx D u u' F0 what₂ δ M γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 := by
    unfold PairVal.vRdef; rw [dif_pos ⟨hrel, hgen, hex⟩]
  have hspec := hex.choose_spec
  obtain ⟨hRep, -, hL, hU, e⟩ := hspec
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  have hγ' : EligAt γ hex.choose.1 := hw ▸ hγ0
  have key := hVP hA hT hrows γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 hγ' hex.choose_spec
  have hcast : ((∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℝ) : ℂ) =
      ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) :=
    Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _
  rw [← hcast, hv, key, ← hw]
  simp only [yT, hz, Complex.ofReal_mul, Complex.ofReal_natCast]

end Good

end Formalism.L2.SG.Pf.Coef
