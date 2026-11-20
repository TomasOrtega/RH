import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeNatCastOfAddOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LtNatCastOfAddOneLtSucc
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullVanish

/- English proof (translation)
Take `⟨N, ι, _, h⟩` from `hp`. Establish `: LocallyOfFiniteType (strHom k X)` using `h ▸ inferInstance`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian (strHom k X)`.
-/
theorem isLocallyNoetherian_of_proj {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) : IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k X) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

/- English proof (translation)
Use `letI := algebraΓAlong k (redι Z)`. Rewrite using `[← comp_strHom (g := redι Z) fun _ => rfl]`. Conclude with `ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp`.
-/
theorem isProjOver_red {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) (Z : Closeds X) :
    letI := algebraΓAlong k (redι Z)
    IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
  letI := algebraΓAlong k (redι Z)
  rw [← comp_strHom (g := redι Z) fun _ => rfl]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp

/- English proof (translation)
Use `topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz => ⟨y, subset_closure rfl, fun h => ?_, hyx.trans (specializes_iff_mem_closure.2 hz)⟩` and prove the remaining obligations. Conclude with `hx ((specializes_iff_mem_closure.2 h).mem_open hU hy)`.
-/
theorem dim_closure_add_one_le {T : Type*} [TopologicalSpace T] [QuasiSober T] {x y : T}
    (hyx : y ⤳ x) {U : Set T} (hU : IsOpen U) (hy : y ∈ U) (hx : x ∉ U) :
    topologicalKrullDim (closure ({x} : Set T)) + 1 ≤ topologicalKrullDim (closure ({y} : Set T)) := by
  refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz => ⟨y, subset_closure rfl, fun h => ?_, hyx.trans (specializes_iff_mem_closure.2 hz)⟩
  exact hx ((specializes_iff_mem_closure.2 h).mem_open hU hy)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le`. Consider the case `exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le`. Consider the case `(apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le ..)`.
-/
theorem withBot_le_of_add_one_le {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (n : WithBot ℕ∞) := by
  first
  | exact @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
  | exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
  | (apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le ..)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ`. Consider the case `exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ`. Consider the case `(apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ ..)`.
-/
theorem withBot_lt_of_add_one_lt {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 < ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  first
  | exact @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
  | exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
  | (apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ ..)

def sumOptionEquiv (e r : ℕ) : Fin e ⊕ Option (Fin r) ≃ Option (Fin e ⊕ Fin r) where
  toFun
    | .inl i => some (.inl i)
    | .inr none => none
    | .inr (some b) => some (.inr b)
  invFun
    | none => .inr none
    | some (.inl i) => .inl i
    | some (.inr b) => .inr (some b)
  left_inv := by rintro (i | _ | b) <;> rfl
  right_inv := by rintro (_ | i | b) <;> rfl

def frontEquiv (e r : ℕ) : Fin e ⊕ Fin (r + 1) ≃ Fin (e + r + 1) :=
  ((Equiv.sumCongr (Equiv.refl _) (finSuccEquiv r)).trans (sumOptionEquiv e r)).trans
    ((Equiv.optionCongr finSumFinEquiv).trans (finSuccEquiv (e + r)).symm)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Break down `x with i | a` into its components or cases. Simplify using `[frontEquiv, sumOptionEquiv]`. Use `Fin.cases ?_ (fun b => ?_) a` and prove the remaining obligations. Simplify using `[frontEquiv, sumOptionEquiv]`.

Simplify using `[frontEquiv, sumOptionEquiv]`.
-/
theorem cons_comp_frontEquiv {X : Scheme.{0}} {e r : ℕ} (P : Fin e → LB X) (B : Fin (r + 1) → LB X) :
    (Fin.cons (B 0) (Sum.elim P (fun a => B a.succ) ∘ finSumFinEquiv.symm) : Fin (e + r + 1) → LB X) ∘
      frontEquiv e r = Sum.elim P B := by
  funext x
  rcases x with i | a
  · simp [frontEquiv, sumOptionEquiv]
  · refine Fin.cases ?_ (fun b => ?_) a
    · simp [frontEquiv, sumOptionEquiv]
    · simp [frontEquiv, sumOptionEquiv]

end GlobalTheory.PullVanish

namespace GlobalTheory.PullVanish

/- English proof (translation)
Use `set ι := redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)`. Establish `hr` using `range_redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)`. Establish `h₁ : w ⤳ ι (genericPoint _)` using `specializes_iff_mem_closure.2 (by`. Establish `: ι (genericPoint _) ∈ Set.range ι` using `⟨_, rfl⟩`. Rewrite `this` using `[hr]`.

Conclude with `this)`. Take `⟨y, hy⟩ : w ∈ Set.range ι` from `by rw [hr]; exact subset_closure rfl`. Establish `h₂ : ι (genericPoint _) ⤳ w`. Use `(genericPoint_specializes y).map ι.continuous` as an intermediate fact. Rewrite `this` using `[hy]`. Then use the resulting hypothesis.

Conclude with `(h₁.antisymm h₂).eq.symm`.
-/
theorem redι_genericPoint {X : Scheme.{0}} (w : X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal (⟨closure {w}, isClosed_closure⟩ : Closeds X)).subscheme] :
    redι (⟨closure {w}, isClosed_closure⟩ : Closeds X) (genericPoint _) = w := by
  set ι := redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)
  have hr := range_redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)
  have h₁ : w ⤳ ι (genericPoint _) :=
    specializes_iff_mem_closure.2 (by
      have : ι (genericPoint _) ∈ Set.range ι := ⟨_, rfl⟩
      rw [hr] at this; exact this)
  obtain ⟨y, hy⟩ : w ∈ Set.range ι := by rw [hr]; exact subset_closure rfl
  have h₂ : ι (genericPoint _) ⤳ w := by
    have := (genericPoint_specializes y).map ι.continuous
    rwa [hy] at this
  exact (h₁.antisymm h₂).eq.symm

/- English proof (translation)
Introduce `κ _ e r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `Z W _ _ _ _ g hg`. It suffices to derive a contradiction.

Establish `h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({g (genericPoint Z)} : Set W))` using `by haveI : Nonempty (IrreducibleCloseds (closure ({g (genericPoint Z)} : Set W))) := ⟨⟨closure {⟨g (genericPoint Z), subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩`. Conclude with `Order.krullDim_nonneg`. Rewrite `hg` using `[Nat.cast_zero]`. Conclude with `absurd hg (not_lt.2 h0)`. Consider the case `succ r ih`.

Introduce `Z W _ _ hp hd g hg P hP A hA`. Use `isLocallyNoetherian_of_proj hp` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i, g (genericPoint Z) ∈ (A 0).U i := by`. Establish `: g (genericPoint Z) ∈ (⨆ i, (A 0).U i : W.Opens)`. Rewrite using `[(hA 0).cover]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`. Use `set M : LB Z := (A 0).pull g with hMdef`. Establish `hM : M.IsLB` using `pull_isLB (hA 0) g`. Set `j₀ : M.ι` to `fun _ => i₀`.

Establish `hmem : ∀ x : Z, x ∈ M.U j₀ ↔ g x ∈ (A 0).U i₀` using `fun x => ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩`. Establish `hη : genericPoint Z ∈ M.U j₀` using `(hmem _).2 hi₀`. Establish `hs` using `isRatSec_frameRat hM j₀ hη`. Use `set Q : Fin (e + r) → LB Z := Sum.elim P (fun a : Fin r => (A a.succ).pull g) ∘ finSumFinEquiv.symm with hQdef`. Establish `hQ' : ∀ x, (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).IsLB`.

Introduce and unpack `(i | a)`. Conclude with `hP i`. Conclude with `pull_isLB (hA _) g`. Establish `hQ : ∀ i, (Q i).IsLB` using `fun i => hQ' _`. Establish `key : interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) = interNum κ (structureModule Z) (Fin.cons M Q : Fin (e + r + 1) → LB Z)`.

Rewrite using `[← interNum_comp_equiv κ _ (isLB_cons hM hQ) (frontEquiv e r)]`. Conclude with `congrArg _ (cons_comp_frontEquiv P (fun a => (A a).pull g)).symm`. Rewrite using `[key, GlobalTheory.T.rational_section_cycle_formula_projective κ Z hp (e + r) hd M hM Q hQ _ hs]`. Use `finsum_eq_zero_of_forall_eq_zero fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : (divOfRatSec hM hs).mult w = 0`.

Rewrite using `[hw, zero_mul]`. Establish `hwU : w ∉ M.U j₀` using `fun h => hw (by`. Rewrite using `[((presents_divOfRatSec hM hs).isEqn j₀ w h).mult_eq, frameRat_self hM j₀ hη, Units.val_one]`. Conclude with `(unitAt_one w).ord_eq_zero)`. It suffices to establish `h : interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds Z) Q = 0 by rw [h, mul_zero]`.

Use `set C : Closeds Z := ⟨closure {w}, isClosed_closure⟩ with hC`. Use `haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme := isIntegral_red isIrreducible_singleton.closure`. Use `letI := algebraΓAlong κ (redι C)`. Establish `hιw : redι C (genericPoint _) = w` using `redι_genericPoint w`. Rewrite using `[interNumRed_def, interNumSub_def, interNumOn_eq_interNum_pull (k := κ) (f := redι C) (fun _ => rfl) hQ]`.

Establish `e1 : interNum κ (structureModule _) (fun i => (Q i).pull (redι C)) = interNum κ (structureModule _) (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C))` using `interNum_comp_equiv κ _ (fun x => pull_isLB (hQ' x) (redι C)) finSumFinEquiv.symm`. Establish `e2 : interNum κ (structureModule _) (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) = interNum κ (structureModule _) (Sum.elim (fun i => (P i).pull (redι C)) fun a : Fin r => (A a.succ).pull (redι C ≫ g))`. Use `interNum_congr_cls κ _ (fun x => pull_isLB (hQ' x) (redι C)) ?_ ?_` and prove the remaining obligations. Introduce and unpack `(i | a)`. Conclude with `pull_isLB (hP i) _`.

Conclude with `pull_isLB (hA _) _`. Introduce and unpack `(i | a)`. Both sides reduce to the same expression. Simplify using `only [Sum.elim_inr]`. Rewrite using `[CechPic.cls_pull (pull_isLB (hA _) g), CechPic.cls_pull (hA _) g, CechPic.cls_pull (hA _) (redι C ≫ g), CechPic.pull_comp]`.

Rewrite using `[e1, e2]`. Use `ih _ W (isProjOver_red hp C) ?_ (redι C ≫ g) ?_ _ (fun i => pull_isLB (hP i) _) _ (fun a => hA _)` and prove the remaining obligations. Rewrite using `[topologicalKrullDim_red]`. Establish `h1` using `dim_closure_add_one_le (genericPoint_specializes w) (M.U j₀).isOpen hη hwU`. Establish `h2 : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = topologicalKrullDim Z`.

Rewrite using `[(genericPoint_spec Z).def]`. Conclude with `(Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq`. Conclude with `withBot_le_of_add_one_le (h1.trans (h2.trans_le hd))`. Rewrite using `[Scheme.Hom.comp_apply, hιw]`. Establish `h1` using `dim_closure_add_one_le ((genericPoint_specializes w).map g.continuous) ((A 0).U i₀).isOpen hi₀ (fun h => hwU ((hmem w).2 h))`.

Conclude with `withBot_lt_of_add_one_lt (lt_of_le_of_lt h1 hg)`.
-/
theorem interNum_pull_eq_zero : ∀ (κ : Type) [Field κ] (e r : ℕ) (Z W : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → topologicalKrullDim Z ≤ (e + r : ℕ) → ∀ g : Z ⟶ W, topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) < (r : ℕ) → ∀ (P : Fin e → LB Z), (∀ i, (P i).IsLB) → ∀ (A : Fin r → LB W), (∀ i, (A i).IsLB) → interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) = 0 := by
  intro κ _ e r
  induction r with
  | zero =>
    intro Z W _ _ _ _ g hg
    exfalso
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) := by
      haveI : Nonempty (IrreducibleCloseds (closure ({g (genericPoint Z)} : Set W))) :=
        ⟨⟨closure {⟨g (genericPoint Z), subset_closure rfl⟩}, isIrreducible_singleton.closure,
          isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    rw [Nat.cast_zero] at hg
    exact absurd hg (not_lt.2 h0)
  | succ r ih =>
    intro Z W _ _ hp hd g hg P hP A hA
    have := isLocallyNoetherian_of_proj hp
    obtain ⟨i₀, hi₀⟩ : ∃ i, g (genericPoint Z) ∈ (A 0).U i := by
      have : g (genericPoint Z) ∈ (⨆ i, (A 0).U i : W.Opens) := by
        rw [(hA 0).cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    set M : LB Z := (A 0).pull g with hMdef
    have hM : M.IsLB := pull_isLB (hA 0) g
    let j₀ : M.ι := fun _ => i₀
    have hmem : ∀ x : Z, x ∈ M.U j₀ ↔ g x ∈ (A 0).U i₀ := fun x =>
      ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
    have hη : genericPoint Z ∈ M.U j₀ := (hmem _).2 hi₀
    have hs := isRatSec_frameRat hM j₀ hη
    set Q : Fin (e + r) → LB Z := Sum.elim P (fun a : Fin r => (A a.succ).pull g) ∘ finSumFinEquiv.symm with hQdef
    have hQ' : ∀ x, (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).IsLB := by
      rintro (i | a)
      · exact hP i
      · exact pull_isLB (hA _) g
    have hQ : ∀ i, (Q i).IsLB := fun i => hQ' _
    have key : interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) =
        interNum κ (structureModule Z) (Fin.cons M Q : Fin (e + r + 1) → LB Z) := by
      rw [← interNum_comp_equiv κ _ (isLB_cons hM hQ) (frontEquiv e r)]
      exact congrArg _ (cons_comp_frontEquiv P (fun a => (A a).pull g)).symm
    rw [key, GlobalTheory.T.rational_section_cycle_formula_projective κ Z hp (e + r) hd M hM Q hQ _ hs]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : (divOfRatSec hM hs).mult w = 0
    · rw [hw, zero_mul]
    have hwU : w ∉ M.U j₀ := fun h => hw (by
      rw [((presents_divOfRatSec hM hs).isEqn j₀ w h).mult_eq, frameRat_self hM j₀ hη, Units.val_one]
      exact (unitAt_one w).ord_eq_zero)
    suffices h : interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds Z) Q = 0 by rw [h, mul_zero]
    set C : Closeds Z := ⟨closure {w}, isClosed_closure⟩ with hC
    haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
      isIntegral_red isIrreducible_singleton.closure
    letI := algebraΓAlong κ (redι C)
    have hιw : redι C (genericPoint _) = w := redι_genericPoint w
    rw [interNumRed_def, interNumSub_def,
      interNumOn_eq_interNum_pull (k := κ) (f := redι C) (fun _ => rfl) hQ]
    have e1 : interNum κ (structureModule _) (fun i => (Q i).pull (redι C)) =
        interNum κ (structureModule _)
          (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) :=
      interNum_comp_equiv κ _ (fun x => pull_isLB (hQ' x) (redι C)) finSumFinEquiv.symm
    have e2 : interNum κ (structureModule _)
          (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) =
        interNum κ (structureModule _)
          (Sum.elim (fun i => (P i).pull (redι C)) fun a : Fin r => (A a.succ).pull (redι C ≫ g)) := by
      refine interNum_congr_cls κ _ (fun x => pull_isLB (hQ' x) (redι C)) ?_ ?_
      · rintro (i | a)
        · exact pull_isLB (hP i) _
        · exact pull_isLB (hA _) _
      · rintro (i | a)
        · rfl
        · simp only [Sum.elim_inr]
          rw [CechPic.cls_pull (pull_isLB (hA _) g), CechPic.cls_pull (hA _) g,
            CechPic.cls_pull (hA _) (redι C ≫ g), CechPic.pull_comp]
    rw [e1, e2]
    refine ih _ W (isProjOver_red hp C) ?_ (redι C ≫ g) ?_ _ (fun i => pull_isLB (hP i) _) _
      (fun a => hA _)
    · rw [topologicalKrullDim_red]
      have h1 := dim_closure_add_one_le (genericPoint_specializes w) (M.U j₀).isOpen hη hwU
      have h2 : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = topologicalKrullDim Z := by
        rw [(genericPoint_spec Z).def]
        exact (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq
      exact withBot_le_of_add_one_le (h1.trans (h2.trans_le hd))
    · rw [Scheme.Hom.comp_apply, hιw]
      have h1 := dim_closure_add_one_le ((genericPoint_specializes w).map g.continuous)
        ((A 0).U i₀).isOpen hi₀ (fun h => hwU ((hmem w).2 h))
      exact withBot_lt_of_add_one_lt (lt_of_le_of_lt h1 hg)

end GlobalTheory.PullVanish
