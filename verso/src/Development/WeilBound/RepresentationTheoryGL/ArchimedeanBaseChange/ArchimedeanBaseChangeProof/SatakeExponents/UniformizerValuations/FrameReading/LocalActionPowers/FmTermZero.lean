import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
  {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E} {e : B.κ ≃ ∀ w : P, κ w}

/- English proof (translation)
Establish `h0 : ∀ h, finFn S (L.ent P (e x) (e z)) L.t h = 0`. Introduce `h`. Assume the negation of the conclusion as `hne`. Apply `(GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero (hL.1 _ _) hL.2 hne w.1 (hP w.2)).1` to reduce the goal to its premises. Simplify using `only [LM.ent, dif_pos w.2]`.

Conclude with `congrFun hw _`. Simplify using `[fm, h0]`.
-/
theorem fm_term_zero (hP : (↑P : Set (Pl E)) ⊆ S) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ) (w : P)
    (hw : L.m w.1 (e x w) (e z w) = 0) (G : H E B.a B.b → ℂ) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = 0 := by
  have h0 : ∀ h, finFn S (L.ent P (e x) (e z)) L.t h = 0 := by
    intro h
    by_contra hne
    apply (GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero (hL.1 _ _) hL.2 hne w.1 (hP w.2)).1
    simp only [LM.ent, dif_pos w.2]
    exact congrFun hw _
  simp [fm, h0]

/- English proof (translation)
Establish `hv : B.vol ≠ 0` using `(hFC E B S hS).1`. Establish `key` using `hFA E B S hS (L.ent P (e x) (e z)) L.t (hL.1 _ _) hL.2 G hG [i₀] (List.nodup_singleton _) (fun i hi => hfix i (by simpa using hi)) y`. Simplify using `only [List.foldr_cons, List.foldr_nil] at key`. Simplify using `only [fm, mul_assoc]`. Rewrite using `[integral_const_mul, key, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]`.
-/
theorem fm_term_act (hS : IsSection S) (hFC : FinConv) (hFA : FinAct) {L : LM κ B.a B.b} (hL : L.Ok P) (x z : B.κ)
    (i₀ : Slot S) (G : H E B.a B.b → ℂ) (hG : HasLev G)
    (hfix : ∀ i, i ≠ i₀ → actS (L.ent P (e x) (e z)) L.t i G = G) (y : H E B.a B.b) :
    ∫ h, fm S P B e L x z h * G (y * finH h) ∂B.ν = actS (L.ent P (e x) (e z)) L.t i₀ G y := by
  have hv : B.vol ≠ 0 := (hFC E B S hS).1
  have key := hFA E B S hS (L.ent P (e x) (e z)) L.t (hL.1 _ _) hL.2 G hG [i₀] (List.nodup_singleton _)
    (fun i hi => hfix i (by simpa using hi)) y
  simp only [List.foldr_cons, List.foldr_nil] at key
  simp only [fm, mul_assoc]
  rw [integral_const_mul, key, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end

/- English proof (translation)
Introduce `hFC hFA E _ _ _ κ _ S P B e hS hP A L w₀ F hL hF hQ p x`. Use function extensionality and compare the values at `y`. Use `set g : κ w₀ → B.κ := fun t => e.symm (Function.update (e x) w₀ t) with hg`. Establish `hginj : Function.Injective g`. Introduce `t t' h`.

Use `congrArg (fun z => e z w₀) h` as an intermediate fact. Simplify `this` using `[hg]`. Establish `hterm : ∀ z : B.κ, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = ∑ t : κ w₀, if z = g t then actP w₀.1 (L.m w₀ (e x w₀) t) (F (p, g t)) y else 0`. Introduce `z`. Distinguish the cases in `hz : ∃ t, z = g t`.

Take `⟨t, rfl⟩` from `hz`. Rewrite using `[Finset.sum_eq_single t (fun t' _ ht' => if_neg fun h => ht' (hginj h).symm) (by simp), if_pos rfl]`. Establish `hez : e (g t) = Function.update (e x) w₀ t` using `by simp [hg]`. Rewrite using `[fm_term_act hS hFC hFA hL x (g t) (Sum.inl ⟨w₀.1, hP w₀.2⟩) (F (p, g t)) (hF _) ?_ y]`. Simplify using `only [actS, LM.ent]`.

Rewrite using `[hez]`. Simplify using the standard rewrite rules. Introduce `i hi`. Use `hQ.2 i hi p x (g t) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hez]`.

Establish `hne : w ≠ w₀`. Introduce and unpack `rfl`. Conclude with `hw (hP w.2) rfl`. Rewrite using `[Function.update_of_ne hne]`. Rewrite using `[Finset.sum_eq_zero fun t _ => if_neg fun h => hz ⟨t, h⟩]`.

Establish `: ∃ w : P, w ≠ w₀ ∧ e x w ≠ e z w`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `hz` to reduce the goal to its premises. Use `⟨e z w₀, e.injective ?_⟩` and prove the remaining obligations.

Simplify using `only [hg, Equiv.apply_symm_apply]`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = w₀`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne hw]`. Conclude with `(hall w hw).symm`. Take `⟨w, hw, hne⟩` from `this`. Use `fm_term_zero hP hL x z w ?_ _ y` and prove the remaining obligations. Use `hQ.1 w.1 w.2 (fun h hh => ?_) _ _ hne` and prove the remaining obligations.

Apply `hw` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Slot.pl hh` as an intermediate fact. Simplify `this.symm` using `[Slot.pl]`. Use `show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _`.

Rewrite using `[Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_comm]`. Simplify using `[Finset.sum_ite_eq', hg]`.
-/
theorem fmAtP_holds : FmAtPOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L w₀ F hL hF hQ p x
  funext y
  set g : κ w₀ → B.κ := fun t => e.symm (Function.update (e x) w₀ t) with hg
  have hginj : Function.Injective g := by
    intro t t' h
    have := congrArg (fun z => e z w₀) h
    simpa [hg] using this
  have hterm : ∀ z : B.κ, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν =
      ∑ t : κ w₀, if z = g t then actP w₀.1 (L.m w₀ (e x w₀) t) (F (p, g t)) y else 0 := by
    intro z
    by_cases hz : ∃ t, z = g t
    · obtain ⟨t, rfl⟩ := hz
      rw [Finset.sum_eq_single t (fun t' _ ht' => if_neg fun h => ht' (hginj h).symm) (by simp), if_pos rfl]
      have hez : e (g t) = Function.update (e x) w₀ t := by simp [hg]
      rw [fm_term_act hS hFC hFA hL x (g t) (Sum.inl ⟨w₀.1, hP w₀.2⟩) (F (p, g t)) (hF _) ?_ y]
      · simp only [actS, LM.ent]
        rw [hez]
        simp
      · intro i hi
        refine hQ.2 i hi p x (g t) fun w hw => ?_
        rw [hez]
        have hne : w ≠ w₀ := by
          rintro rfl
          exact hw (hP w.2) rfl
        rw [Function.update_of_ne hne]
    · rw [Finset.sum_eq_zero fun t _ => if_neg fun h => hz ⟨t, h⟩]
      have : ∃ w : P, w ≠ w₀ ∧ e x w ≠ e z w := by
        by_contra hall
        push Not at hall
        apply hz
        refine ⟨e z w₀, e.injective ?_⟩
        simp only [hg, Equiv.apply_symm_apply]
        funext w
        by_cases hw : w = w₀
        · subst hw; simp
        · rw [Function.update_of_ne hw]; exact (hall w hw).symm
      obtain ⟨w, hw, hne⟩ := this
      refine fm_term_zero hP hL x z w ?_ _ y
      refine hQ.1 w.1 w.2 (fun h hh => ?_) _ _ hne
      apply hw
      apply Subtype.ext
      have := congrArg Slot.pl hh
      simpa [Slot.pl] using this.symm
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_comm]
  simp [Finset.sum_ite_eq', hg]

/- English proof (translation)
Introduce `hFC hFA E _ _ _ κ _ S P B e hS hP A L i₀ F hL hF hoff hQ p x`. Use function extensionality and compare the values at `y`. Use `show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _`. Rewrite using `[Finset.sum_eq_single x]`. Rewrite using `[fm_term_act hS hFC hFA hL x x i₀ (F (p, x)) (hF _) (fun i hi => hQ.2 i hi p x x fun _ _ => rfl) y]`.

Break down `i₀ with ⟨w, hw⟩ | ⟨w, hw⟩` into its components or cases. Establish `hwP : w ∉ P` using `fun h => hoff w h hw rfl`. Simplify using `[actS, LM.ent, dif_neg hwP]`. Both sides reduce to the same expression. Introduce `z _ hz`.

Establish `: ∃ w : P, e x w ≠ e z w`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Conclude with `hz (e.injective (funext hall)).symm`. Take `⟨w, hne⟩` from `this`.

Conclude with `fm_term_zero hP hL x z w (hQ.1 w.1 w.2 (hoff w.1 w.2) _ _ hne) _ y`. Simplify using the standard rewrite rules.
-/
theorem fmOff_holds : FmOffOf := by
  intro hFC hFA E _ _ _ κ _ S P B e hS hP A L i₀ F hL hF hoff hQ p x
  funext y
  show ∑ z, ∫ h, fm S P B e L x z h * F (p, z) (y * finH h) ∂B.ν = _
  rw [Finset.sum_eq_single x]
  · rw [fm_term_act hS hFC hFA hL x x i₀ (F (p, x)) (hF _) (fun i hi => hQ.2 i hi p x x fun _ _ => rfl) y]
    rcases i₀ with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hwP : w ∉ P := fun h => hoff w h hw rfl
      simp [actS, LM.ent, dif_neg hwP]
    · rfl
  · intro z _ hz
    have : ∃ w : P, e x w ≠ e z w := by
      by_contra hall
      push Not at hall
      exact hz (e.injective (funext hall)).symm
    obtain ⟨w, hne⟩ := this
    exact fm_term_zero hP hL x z w (hQ.1 w.1 w.2 (hoff w.1 w.2) _ _ hne) _ y
  · simp

end PositivityTheory.Rg.BcB.F.FA

end
