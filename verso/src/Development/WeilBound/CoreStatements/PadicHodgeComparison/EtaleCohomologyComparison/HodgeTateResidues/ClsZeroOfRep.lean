import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

open Pb

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Take `⟨f, hf, rfl, hv⟩` from `hc`. Take `⟨f', hf', rfl, hv'⟩` from `hc'`. Establish `ef : f = fun s => sqMk a b (z s) (hz s)` using `funext fun s => Subtype.ext (hv s)`. Establish `ef' : f' = fun s => sqMk a' b' (z' s) (hz' s)` using `funext fun s => Subtype.ext (hv' s)`. Substitute `ef ef'` using the available equality.

Take `⟨hc, ec⟩` from `CrystallineSemistableComparison.P.cup_cls h.pair e _ _ hf hf'`. Use `⟨fun s => h.aa _ (a.map_mem _ (hz ((CH.front_mono e).functor ⋙ s))) (a'.map_mem _ (hz' ((CH.back_mono e).functor ⋙ s))), _, hc, ec, fun s => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (h.mul_mk _ _ (a.map_mem _ (hz ((CH.front_mono e).functor ⋙ s))) (a'.map_mem _ (hz' ((CH.back_mono e).functor ⋙ s))))`.
-/
theorem rep_cup {a b a' b' a'' b'' : IdF A} (h : MulOk a b a' b' a'' b'') {p q n : ℕ} (e : p + q = n)
    (z : CH.Cn (CH.modF A) p) (z' : CH.Cn (CH.modF A) q) (hz : ∀ s, z s ∈ a.S _) (hz' : ∀ s, z' s ∈ a'.S _)
    {c : CH.H (sq a b) p} {c' : CH.H (sq a' b') q} (hc : Rep a b z c) (hc' : Rep a' b' z' c') :
    (∀ s, (CH.mulP A).cupC e z z' s ∈ a''.S _) ∧ Rep a'' b'' ((CH.mulP A).cupC e z z') (h.pair.cup e c c') := by
  obtain ⟨f, hf, rfl, hv⟩ := hc
  obtain ⟨f', hf', rfl, hv'⟩ := hc'
  have ef : f = fun s => sqMk a b (z s) (hz s) := funext fun s => Subtype.ext (hv s)
  have ef' : f' = fun s => sqMk a' b' (z' s) (hz' s) := funext fun s => Subtype.ext (hv' s)
  subst ef ef'
  obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls h.pair e _ _ hf hf'
  refine ⟨fun s => h.aa _ (a.map_mem _ (hz ((CH.front_mono e).functor ⋙ s))) (a'.map_mem _ (hz' ((CH.back_mono e).functor ⋙ s))), _, hc, ec, fun s => ?_⟩
  exact congrArg Subtype.val (h.mul_mk _ _ (a.map_mem _ (hz ((CH.front_mono e).functor ⋙ s))) (a'.map_mem _ (hz' ((CH.back_mono e).functor ⋙ s))))

/- English proof (translation)
Take `⟨f, hf, e, hv⟩` from `h`. Establish `inj : ∀ (T : C) (x y : A.obj T), Ideal.Quotient.mk (b.S T) x = Ideal.Quotient.mk (b.S T) y → x = y` using `fun T x y hxy => by`. Use `Ideal.Quotient.eq.1 hxy` as an intermediate fact. Rewrite `this` using `[hb, Ideal.mem_bot, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hB` using `((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) n).2.1 f hf).1 e.symm`.

Use `((CrystallineSemistableComparison.P.cls_surj (CH.cx (CH.modF A)) n).2.1 z hz).2 ?_` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero`. Establish `h0 : f = 0` using `hB`. Express the relevant statement in the definitionally equal form `z = 0`.

Use function extensionality and compare the values at `s`. Use `inj _ _ _ ((hv s).symm.trans ?_)` and prove the remaining obligations. Rewrite using `[h0]`. Both sides reduce to the same expression. Consider the case `succ n`.

Take `⟨g, hg⟩` from `hB`. Set `g' : CH.Cn (CH.modF A) n` to `fun s => out a b (g s)`. Set `m₁` to `toSq (IdF.top A) b fun _ => rfl`. Set `m₂ : CH.Mor (sq a b) (sq (IdF.top A) b) (RingHom.id R)` to `sqLe (fun _ => le_top) fun _ => le_rfl`. Establish `e1 : m₁.pullC n g' = m₂.pullC n g`.

Use function extensionality and compare the values at `s`. Use `Subtype.ext ?_` and prove the remaining obligations. Use `mk_out a b (g s)` as an intermediate fact. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (out a b (g s)) = Ideal.Quotient.factorₐ R le_rfl (show sqM a b _ from g s).1`. Use `conv_rhs => rw [← this]`.

Both sides reduce to the same expression. Establish `e2 : m₁.pullC (n + 1) (CH.d _ n g') = m₂.pullC (n + 1) f`. Rewrite using `[← m₁.d_pullC, e1, m₂.d_pullC]`. Conclude with `congrArg _ hg`. Use `⟨g', funext fun s => inj _ _ _ ?_⟩` and prove the remaining obligations.

Establish `e3` using `congrArg Subtype.val (congrFun e2 s)`. Use `e3.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.factorₐ R le_rfl (show sqM a b _ from f s).1 = _`. Rewrite using `[hv s]`. Both sides reduce to the same expression.
-/
theorem cls_zero_of_rep {a b : IdF A} (hb : ∀ T, b.S T = ⊥) {n : ℕ} (z : CH.Cn (CH.modF A) n) (hz : CH.d _ n z = 0)
    (h : Rep a b z 0) : (CH.cx (CH.modF A)).cls z hz = 0 := by
  obtain ⟨f, hf, e, hv⟩ := h
  have inj : ∀ (T : C) (x y : A.obj T), Ideal.Quotient.mk (b.S T) x = Ideal.Quotient.mk (b.S T) y → x = y := fun T x y hxy => by
    have := Ideal.Quotient.eq.1 hxy
    rwa [hb, Ideal.mem_bot, sub_eq_zero] at this
  have hB := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) n).2.1 f hf).1 e.symm
  refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx (CH.modF A)) n).2.1 z hz).2 ?_
  cases n with
  | zero =>
    have h0 : f = 0 := hB
    change z = 0
    funext s
    refine inj _ _ _ ((hv s).symm.trans ?_)
    rw [h0]; rfl
  | succ n =>
    obtain ⟨g, hg⟩ := hB
    let g' : CH.Cn (CH.modF A) n := fun s => out a b (g s)
    let m₁ := toSq (IdF.top A) b fun _ => rfl
    let m₂ : CH.Mor (sq a b) (sq (IdF.top A) b) (RingHom.id R) := sqLe (fun _ => le_top) fun _ => le_rfl
    have e1 : m₁.pullC n g' = m₂.pullC n g := by
      funext s
      refine Subtype.ext ?_
      have := mk_out a b (g s)
      change Ideal.Quotient.mk _ (out a b (g s)) = Ideal.Quotient.factorₐ R le_rfl (show sqM a b _ from g s).1
      conv_rhs => rw [← this]
      rfl
    have e2 : m₁.pullC (n + 1) (CH.d _ n g') = m₂.pullC (n + 1) f := by
      rw [← m₁.d_pullC, e1, m₂.d_pullC]
      exact congrArg _ hg
    refine ⟨g', funext fun s => inj _ _ _ ?_⟩
    have e3 := congrArg Subtype.val (congrFun e2 s)
    refine e3.trans ?_
    change Ideal.Quotient.factorₐ R le_rfl (show sqM a b _ from f s).1 = _
    rw [hv s]; rfl

/- English proof (translation)
Take `⟨f, hf, e, hv⟩` from `hc`. Conclude with `⟨f, hf, e, fun s => (hv s).trans (Ideal.Quotient.eq.2 (h s))⟩`.
-/
theorem rep_congr {a b : IdF A} {n : ℕ} {z z' : ∀ s : ComposableArrows C n, A.obj (s.obj (Fin.last n))}
    (h : ∀ s, z s - z' s ∈ b.S _) {c : CH.H (sq a b) n} (hc : Rep a b z c) : Rep a b z' c := by
  obtain ⟨f, hf, e, hv⟩ := hc
  exact ⟨f, hf, e, fun s => (hv s).trans (Ideal.Quotient.eq.2 (h s))⟩

/- English proof (translation)
Take `⟨f, hf, rfl, hv⟩` from `hc`. Take `⟨f', hf', rfl, hv'⟩` from `hc'`. Establish `: f = f'` using `funext fun s => Subtype.ext ((hv s).trans (hv' s).symm)`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem rep_uniq {a b : IdF A} {n : ℕ} {z : ∀ s : ComposableArrows C n, A.obj (s.obj (Fin.last n))}
    {c c' : CH.H (sq a b) n} (hc : Rep a b z c) (hc' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, hv⟩ := hc
  obtain ⟨f', hf', rfl, hv'⟩ := hc'
  have : f = f' := funext fun s => Subtype.ext ((hv s).trans (hv' s).symm)
  subst this; rfl

end Gen

end CrystallineSemistableComparison.HT
