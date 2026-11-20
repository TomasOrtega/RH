import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.ProdF
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.Sl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)}

def cpH (a b : ℕ) : ∀ i : Slot S, Hf E a b →* GLw a i.pl × GLw b i.pl
  | .inl w => GlobalTheory.CompanionTheory.FinLevelTw.atHom a b w.1
  | .inr w => (GlobalTheory.CompanionTheory.FinLevelTw.atHom a b w.1).comp (thP E a b)

def eH (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => (thP E a b).comp ((locGL E a w.1).prodMap (locGL E b w.1))

def φS (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl → ℂ
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

/- English proof (translation)
Apply the tactic sequence `cases i <;> rfl`.
-/
theorem cpH_apply (i : Slot S) (x : Hf E a b) : cpH a b i x = i.cp a b x := by
  cases i <;> rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cpH_inl (w : {w // w ∈ S}) (x : Hf E a b) :
    cpH a b (.inl w : Slot S) x = GlobalTheory.CompanionTheory.SuppFinTw.atH a b w.1 x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cpH_inr (w : {w // w ∈ S ∧ IsSplitAt w}) (x : Hf E a b) :
    cpH a b (.inr w : Slot S) x = GlobalTheory.CompanionTheory.SuppFinTw.atH a b w.1 (thP E a b x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eH_inl (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1) :
    eH a b (.inl w : Slot S) m = ((locGL E a w.1 m.1, locGL E b w.1 m.2) : Hf E a b) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eH_inr (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1) :
    eH a b (.inr w : Slot S) m = thP E a b ((locGL E a w.1 m.1, locGL E b w.1 m.2) : Hf E a b) := rfl

/- English proof (translation)
The claim follows from `Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)`.
-/
theorem atH_loc_self (w : Pl E) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b w ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) = m :=
  Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)

/- English proof (translation)
The claim follows from `Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)`.
-/
theorem atH_loc_ne {w v : Pl E} (h : v ≠ w) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b v ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) = 1 :=
  Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)

/- English proof (translation)
Use `GlobalTheory.CompanionTheory.SuppFinTw.atH_thP_congr (a := a) (b := b) (u := v) rfl (g := ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) (h := 1) (by rw [atH_loc_ne h, map_one])` as an intermediate fact. Rewrite using `[this, map_one, map_one]`.
-/
theorem atH_thP_loc_ne {w v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ w) (m : GLw a w × GLw b w) :
    GlobalTheory.CompanionTheory.SuppFinTw.atH a b v (thP E a b ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) = 1 := by
  have := GlobalTheory.CompanionTheory.SuppFinTw.atH_thP_congr (a := a) (b := b) (u := v) rfl
    (g := ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)) (h := 1) (by rw [atH_loc_ne h, map_one])
  rw [this, map_one, map_one]

/- English proof (translation)
Break down `i with w | w` into its components or cases. Conclude with `atH_loc_self w.1 m`. Conclude with `(congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans (atH_loc_self w.1 m)`.
-/
theorem cpH_eH_self (hS : IsSection S) (i : Slot S) (m : GLw a i.pl × GLw b i.pl) : cpH a b i (eH a b i m) = m := by
  rcases i with w | w
  · exact atH_loc_self w.1 m
  · exact (congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans (atH_loc_self w.1 m)

/- English proof (translation)
Apply the tactic sequence `rcases i with w | w <;> rcases j with v | v`. Conclude with `atH_loc_ne (fun e => h (congrArg Sum.inl (Subtype.ext e))) m`. Conclude with `atH_thP_loc_ne (w := w.1) (v := v.1) (fun e => GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (e ▸ w.2)) m`. Use `atH_thP_loc_ne (w := w.1) (v := v.1) (fun e => ?_) m` and prove the remaining obligations. Establish `e' : v.1 = GlobalTheory.EulerTw.cPl E w.1` using `by rw [← e, GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]`.

Conclude with `GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (e' ▸ v.2)`. Conclude with `(congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b v.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans (atH_loc_ne (fun e => h (congrArg Sum.inr (Subtype.ext e))) m)`.
-/
theorem cpH_eH_ne (hS : IsSection S) (i j : Slot S) (m : GLw a i.pl × GLw b i.pl) (h : j ≠ i) :
    cpH a b j (eH a b i m) = 1 := by
  rcases i with w | w <;> rcases j with v | v
  · exact atH_loc_ne (fun e => h (congrArg Sum.inl (Subtype.ext e))) m
  · exact atH_thP_loc_ne (w := w.1) (v := v.1)
      (fun e => GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (e ▸ w.2)) m
  · refine atH_thP_loc_ne (w := w.1) (v := v.1) (fun e => ?_) m
    have e' : v.1 = GlobalTheory.EulerTw.cPl E w.1 := by rw [← e, GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (e' ▸ v.2)
  · exact (congrArg (GlobalTheory.CompanionTheory.SuppFinTw.atH a b v.1) (GlobalTheory.CompanionTheory.SuppFinTw.thP_thP _)).trans
      (atH_loc_ne (fun e => h (congrArg Sum.inr (Subtype.ext e))) m)

/- English proof (translation)
The claim follows from `Prod.ext (map_mul _ _ _) (map_mul _ _ _)`.
-/
theorem finH_mul (x y : Hf E a b) : finH (x * y) = finH x * finH y :=
  Prod.ext (map_mul _ _ _) (map_mul _ _ _)

/- English proof (translation)
Break down `i with w | w` into its components or cases. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = _`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Use `congr 2`. Express the relevant statement in the definitionally equal form `G (z * ((embT a w.1).prodMap (embT b w.1) m)) = _`. Use `congr 2`. Conclude with `Prod.ext (GlobalTheory.ThetaPull.thetaA_finGL _) (GlobalTheory.ThetaPull.thetaA_finGL _)`.
-/
theorem actS_eq (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) (G : H E a b → ℂ) (z : H E a b) :
    FA.actS φ₁ φ₂ i G z = hint (K2 a b i.pl) (fun m => φS φ₁ φ₂ i m * G (z * finH (eH a b i m))) := by
  rcases i with w | w
  · rfl
  · change hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = _
    congr 1
    funext m
    congr 2
    change G (z * ((embT a w.1).prodMap (embT b w.1) m)) = _
    congr 2
    exact Prod.ext (GlobalTheory.ThetaPull.thetaA_finGL _) (GlobalTheory.ThetaPull.thetaA_finGL _)

/- English proof (translation)
Establish `h0 : ∀ w : Pl E, Continuous fun m : GLw a w × GLw b w => ((locGL E a w m.1, locGL E b w m.2) : Hf E a b)` using `fun w => ((GlobalTheory.EulerTw.continuous_locGL_spl E a w).comp continuous_fst).prodMk ((GlobalTheory.EulerTw.continuous_locGL_spl E b w).comp continuous_snd)`. Break down `i with w | w` into its components or cases. Conclude with `h0 w.1`. Conclude with `GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP.comp (h0 w.1)`.
-/
theorem continuous_eH (i : Slot S) : Continuous (eH (E := E) a b i) := by
  have h0 : ∀ w : Pl E, Continuous fun m : GLw a w × GLw b w => ((locGL E a w m.1, locGL E b w m.2) : Hf E a b) :=
    fun w => ((GlobalTheory.EulerTw.continuous_locGL_spl E a w).comp continuous_fst).prodMk
      ((GlobalTheory.EulerTw.continuous_locGL_spl E b w).comp continuous_snd)
  rcases i with w | w
  · exact h0 w.1
  · exact GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP.comp (h0 w.1)

/- English proof (translation)
Break down `i with w | w` into its components or cases. Conclude with `GlobalTheory.CompanionTheory.FinLevelTw.continuous_atHom w.1`. Conclude with `(GlobalTheory.CompanionTheory.FinLevelTw.continuous_atHom w.1).comp GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP`.
-/
theorem continuous_cpH (i : Slot S) : Continuous (cpH (E := E) a b i) := by
  rcases i with w | w
  · exact GlobalTheory.CompanionTheory.FinLevelTw.continuous_atHom w.1
  · exact (GlobalTheory.CompanionTheory.FinLevelTw.continuous_atHom w.1).comp GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP

/- English proof (translation)
Take `⟨_, _, -, -, -, hc₁⟩` from `h₁`. Take `⟨_, _, -, -, -, hc₂⟩` from `h₂`. Establish `hev : ∀ᶠ w in cofinite, φ₁ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 ∧ φ₂ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 ∧ GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y ∈ K2 a b w ∧ GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y) ∈ K2 a b w` using `hc₁.and (hc₂.and ((GlobalTheory.CompanionTheory.SuppFinTw.ae_mem y).and (GlobalTheory.CompanionTheory.SuppFinTw.ae_mem (thP E a b y))))`. Use `set T := (Filter.eventually_cofinite.1 hev).toFinset with hT`. Establish `hgood : ∀ w, w ∉ T → φ₁ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y) = 1 ∧ φ₂ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y)) = 1` using `fun w hw => by`.

Simplify using `only [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw`. Take `⟨e₁, e₂, m₁, m₂⟩` from `hw`. Rewrite using `[e₁, e₂, Set.indicator_of_mem m₁, Set.indicator_of_mem m₂]`. Conclude with `⟨rfl, rfl⟩`. Unfold `finFn Abs.prodF`.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := T), finprod_eq_prod_of_mulSupport_subset (s := (T.subtype (· ∈ S)).disjSum (T.subtype fun w => w ∈ S ∧ IsSplitAt w)), Finset.prod_disjSum]`. Express the relevant statement in the definitionally equal form `_ = (∏ x ∈ T.subtype (· ∈ S), (fun w => φ₁ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y)) x.1) * ∏ x ∈ T.subtype (fun w => w ∈ S ∧ IsSplitAt w), (fun w => φ₂ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y))) x.1`. Rewrite using `[Finset.prod_subtype_eq_prod_filter (fun w => φ₁ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y)), Finset.prod_subtype_eq_prod_filter (fun w => φ₂ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y))), Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul …`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[finprod_eq_if]`.

Apply the tactic sequence `by_cases hwS : w ∈ S <;> by_cases hws : IsSplitAt w <;> simp [hwS, hws] <;> rfl`. Introduce `j hj`. Break down `j with w | w` into its components or cases. Establish `: w.1 ∈ T` using `by by_contra hw; exact hj (hgood w.1 hw).1`. Simplify using `[Finset.mem_disjSum, Finset.mem_subtype, this]`.

Establish `: w.1 ∈ T` using `by by_contra hw; exact hj (hgood w.1 hw).2`. Simplify using `[Finset.mem_disjSum, Finset.mem_subtype, this]`. Introduce `w hw`. Assume the negation of the conclusion as `hwT`. Apply `hw` to reduce the goal to its premises.

Establish `hg` using `hgood w hwT`. Simplify using `only`. Establish `e1 : φ₁ w (G8.atW w y) = 1` using `hg.1`. Establish `e2 : φ₂ w (G8.atW w (thP E a b y)) = 1` using `hg.2`. Simplify using `[finprod_eq_if, e1, e2]`.
-/
theorem finFn_eq (hS : IsSection S) (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (y : Hf E a b) :
    finFn S φ₁ φ₂ y = Abs.prodF (cpH (S := S) a b) (φS φ₁ φ₂) y := by
  obtain ⟨_, _, -, -, -, hc₁⟩ := h₁
  obtain ⟨_, _, -, -, -, hc₂⟩ := h₂
  have hev : ∀ᶠ w in cofinite, φ₁ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 ∧
      φ₂ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 ∧
      GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y ∈ K2 a b w ∧ GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y) ∈ K2 a b w :=
    hc₁.and (hc₂.and ((GlobalTheory.CompanionTheory.SuppFinTw.ae_mem y).and (GlobalTheory.CompanionTheory.SuppFinTw.ae_mem (thP E a b y))))
  set T := (Filter.eventually_cofinite.1 hev).toFinset with hT
  have hgood : ∀ w, w ∉ T → φ₁ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y) = 1 ∧
      φ₂ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y)) = 1 := fun w hw => by
    simp only [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
    obtain ⟨e₁, e₂, m₁, m₂⟩ := hw
    rw [e₁, e₂, Set.indicator_of_mem m₁, Set.indicator_of_mem m₂]
    exact ⟨rfl, rfl⟩
  unfold finFn Abs.prodF
  rw [finprod_eq_prod_of_mulSupport_subset (s := T), finprod_eq_prod_of_mulSupport_subset
    (s := (T.subtype (· ∈ S)).disjSum (T.subtype fun w => w ∈ S ∧ IsSplitAt w)), Finset.prod_disjSum]
  change _ = (∏ x ∈ T.subtype (· ∈ S), (fun w => φ₁ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y)) x.1) *
    ∏ x ∈ T.subtype (fun w => w ∈ S ∧ IsSplitAt w),
      (fun w => φ₂ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y))) x.1
  rw [Finset.prod_subtype_eq_prod_filter (fun w => φ₁ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w y)),
    Finset.prod_subtype_eq_prod_filter (fun w => φ₂ w (GlobalTheory.CompanionTheory.SuppFinTw.atH a b w (thP E a b y))),
    Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [finprod_eq_if]
    by_cases hwS : w ∈ S <;> by_cases hws : IsSplitAt w <;> simp [hwS, hws] <;> rfl
  · intro j hj
    rcases j with w | w
    · have : w.1 ∈ T := by by_contra hw; exact hj (hgood w.1 hw).1
      simp [Finset.mem_disjSum, Finset.mem_subtype, this]
    · have : w.1 ∈ T := by by_contra hw; exact hj (hgood w.1 hw).2
      simp [Finset.mem_disjSum, Finset.mem_subtype, this]
  · intro w hw
    by_contra hwT
    apply hw
    have hg := hgood w hwT
    dsimp only
    have e1 : φ₁ w (G8.atW w y) = 1 := hg.1
    have e2 : φ₂ w (G8.atW w (thP E a b y)) = 1 := hg.2
    simp [finprod_eq_if, e1, e2]

end PositivityTheory.Rg.BcB.F.FA.Sl

end
