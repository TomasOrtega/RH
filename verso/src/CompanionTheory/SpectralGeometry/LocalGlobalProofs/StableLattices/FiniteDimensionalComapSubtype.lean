import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

noncomputable section

namespace GlobalTheory.CompanionTheory.RgSteps

open CompanionTheory.RgExh
open Formalism.REAL (GlRel IsWeight)
open CompanionTheory.D.LK (LocFin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

/- English proof (translation)
Introduce `u`. Use `choose S hSfd hSst hSmem using fun i => h (u i)`. Use `haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd`. Establish `hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i`. Introduce `a b hab x hx`.

Use `Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_` and prove the remaining obligations. Introduce `y w hy hw`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hy hw`. Establish `hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i)`.

Set `f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i))` to `{ toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `FiniteDimensional.of_injective f (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))`. Use `⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab v hv i _`. Establish `hv' : ∀ j, v j ∈ ⨆ i, S i` using `fun j => hv j (Set.mem_univ j)`.

Express the relevant statement in the definitionally equal form `X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i`. Use `Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hv' b`. Conclude with `Submodule.zero_mem _`.

Introduce `i _`. Conclude with `(le_iSup S i) (hSmem i)`.
-/
theorem locFin_tens (ε : Fin n → Bool) (X : GMod n) (h : LocFin ε X.E) : LocFin ε (tens X).E := by
  intro u
  choose S hSfd hSst hSmem using fun i => h (u i)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd
  have hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i := by
    intro a b hab x hx
    refine Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx
      (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_
    intro y w hy hw
    rw [map_add]
    exact Submodule.add_mem _ hy hw
  have hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) := by
    let f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i)) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f
      (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))
  refine ⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩
  · intro a b hab v hv i _
    have hv' : ∀ j, v j ∈ ⨆ i, S i := fun j => hv j (Set.mem_univ j)
    change X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i
    refine Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_
    split_ifs
    · exact hv' b
    · exact Submodule.zero_mem _
  · intro i _
    exact (le_iSup S i) (hSmem i)

/- English proof (translation)
Use `FiniteDimensional.of_injective (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `hv : ((x : S) : V) = ((y : S) : V)` using `congrArg (fun w : T => (w : V)) hxy`. Conclude with `Subtype.ext (Subtype.ext hv)`.
-/
theorem finiteDimensional_comap_subtype {V : Type} [AddCommGroup V] [Module ℂ V]
    (S T : Submodule ℂ V) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.comap S.subtype) := by
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_
  intro x y hxy
  have hv : ((x : S) : V) = ((y : S) : V) := congrArg (fun w : T => (w : V)) hxy
  exact Subtype.ext (Subtype.ext hv)

/- English proof (translation)
Introduce `x`. Take `⟨F, hF, hst, hx⟩` from `hX x.1`. Use `haveI := hF`. Use `⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩` and prove the remaining obligations. Introduce `a b hab v hv`.

Conclude with `hst a b hab v.1 hv`.
-/
theorem locFin_sub (ε : Fin n → Bool) (X : GMod n) (S : Submodule ℂ X.V)
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (hX : LocFin ε X.E) : LocFin ε (X.sub S h).E := by
  intro x
  obtain ⟨F, hF, hst, hx⟩ := hX x.1
  haveI := hF
  refine ⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩
  intro a b hab v hv
  exact hst a b hab v.1 hv

/- English proof (translation)
Introduce `μ u hu hw a`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, u i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Conclude with `hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)`. Establish `hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i)`.

Introduce `b`. Establish `hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i` using `congrFun (hw b) i`. Distinguish the cases in `hbi : b = i`. Substitute `hbi` using the available equality. Simplify using `only [if_true] at hb ⊢`.

Rewrite using `[Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]`. Conclude with `(add_sub_cancel_right _ _).symm`. Simplify using `only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢`. Conclude with `hb`. Take `⟨m, hm⟩` from `h _ (u i) hi hw' a`.

Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality. Simplify using `only [if_true] at hm`. Conclude with `⟨m + 1, by push_cast; linarith⟩`. Simplify using `only [if_neg hai] at hm`.

Conclude with `⟨m, hm⟩`.
-/
theorem intWt_tens (X : GMod n) (h : IntWt X) : IntWt (tens X) := by
  intro μ u hu hw a
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
  have hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i) := by
    intro b
    have hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i := congrFun (hw b) i
    by_cases hbi : b = i
    · subst hbi
      simp only [if_true] at hb ⊢
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]
      exact (add_sub_cancel_right _ _).symm
    · simp only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢
      exact hb
  obtain ⟨m, hm⟩ := h _ (u i) hi hw' a
  by_cases hai : a = i
  · subst hai
    simp only [if_true] at hm
    exact ⟨m + 1, by push_cast; linarith⟩
  · simp only [if_neg hai] at hm
    exact ⟨m, hm⟩

/- English proof (translation)
Introduce `μ x hx hw a`. Conclude with `hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a`.
-/
theorem intWt_sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S)
    (hX : IntWt X) : IntWt (X.sub S h) := by
  intro μ x hx hw a
  exact hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a

/- English proof (translation)
Conclude with `locFin_sub ε (CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)`.
-/
theorem locFin_step (ε : Fin n → Bool) (X : GMod n) (z : ℂ) (h : LocFin ε X.E) :
    LocFin ε (step X z).E := by
  exact locFin_sub ε (CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)

/- English proof (translation)
Conclude with `intWt_sub (CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)`.
-/
theorem intWt_step (X : GMod n) (z : ℂ) (h : IntWt X) : IntWt (step X z) := by
  exact intWt_sub (CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)

/- English proof (translation)
Introduce `n ε X χ ss`. Proceed by induction on `ss generalizing X χ with`. Consider the case `nil => exact ⟨id, id⟩`. Consider the case `cons s ss ih`. Prove the components needed by the constructor for the conclusion.

Introduce `h first`. Consider the case `exact (ih _ _).1 (locFin_step ε X _ h)`. Consider the case `exact locFin_step ε _ _ ((ih X χ).1 h)`. Consider the case `exact locFin_step ε _ _ ((ih _ _).1 h)`. Introduce `h first`.

Consider the case `exact (ih _ _).2 (intWt_step X _ h)`. Consider the case `exact intWt_step _ _ ((ih X χ).2 h)`. Consider the case `exact intWt_step _ _ ((ih _ _).2 h)`.
-/
theorem pathFin : CompanionTheory.RgExh.Fin.PathFin := by
  intro n ε X χ ss
  induction ss generalizing X χ with
  | nil => exact ⟨id, id⟩
  | cons s ss ih =>
    constructor
    · intro h
      first
        | exact (ih _ _).1 (locFin_step ε X _ h)
        | exact locFin_step ε _ _ ((ih X χ).1 h)
        | exact locFin_step ε _ _ ((ih _ _).1 h)
    · intro h
      first
        | exact (ih _ _).2 (intWt_step X _ h)
        | exact intWt_step _ _ ((ih X χ).2 h)
        | exact intWt_step _ _ ((ih _ _).2 h)

end GlobalTheory.CompanionTheory.RgSteps
