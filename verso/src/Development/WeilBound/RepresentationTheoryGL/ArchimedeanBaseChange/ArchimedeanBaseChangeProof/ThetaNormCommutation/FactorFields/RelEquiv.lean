import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Count2P

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp⟩ symm := by rintro x y ⟨g, rfl⟩ exact ⟨g⁻¹, by rw [map_inv]; group⟩ trans := by rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩ exact ⟨g * h, by rw [map_mul]; group⟩`.
-/
theorem rel_equiv {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(rel_equiv θ).symm ((rel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h))`. Introduce `h`. Conclude with `(Quot.sound ((rel_equiv θ).symm h))`.
-/
theorem mk_eq_iff {G : Type} [Group G] (θ : G →* G) (x z : G) :
    (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x : TwCl θ) = Quot.mk _ z ↔ ∃ g, x = g⁻¹ * z * θ g := by
  constructor
  · intro h
    exact (rel_equiv θ).symm ((rel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h))
  · intro h
    exact (Quot.sound ((rel_equiv θ).symm h))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨⟨g.1, rfl⟩, ⟨g.2, rfl⟩⟩`. Introduce and unpack `⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩`. Conclude with `⟨(g₁, g₂), Prod.ext h₁ h₂⟩`.
-/
theorem prod_rel {G H : Type} [Group G] [Group H] (θ₁ : G →* G) (θ₂ : H →* H) (x z : G × H) :
    (∃ g : G × H, x = g⁻¹ * z * (θ₁.prodMap θ₂) g) ↔
      (∃ g₁, x.1 = g₁⁻¹ * z.1 * θ₁ g₁) ∧ (∃ g₂, x.2 = g₂⁻¹ * z.2 * θ₂ g₂) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.1, rfl⟩, ⟨g.2, rfl⟩⟩
  · rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩
    exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩

/- English proof (translation)
Take `⟨g, rfl⟩` from `h`. Establish `h1 : nrmL n w (g⁻¹ * z * thL n w g) = g⁻¹ * nrmL n w z * g` using `GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g z`. Establish `h2 : ((g⁻¹ * nrmL n w z * g : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (nrmL n w z : Matrix (Fin n) (Fin n) _) * (g : Matrix (Fin n) (Fin n) _)` using `rfl`. Rewrite using `[h1, h2, Matrix.coe_units_inv]`. Conclude with `Matrix.charpoly_units_conj' g _`.
-/
theorem charpoly_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (x z : GLw n w) (h : ∃ g, x = g⁻¹ * z * thL n w g) :
    (nrmL n w x).val.charpoly = (nrmL n w z).val.charpoly := by
  obtain ⟨g, rfl⟩ := h
  have h1 : nrmL n w (g⁻¹ * z * thL n w g) = g⁻¹ * nrmL n w z * g := GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g z
  have h2 : ((g⁻¹ * nrmL n w z * g : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (nrmL n w z : Matrix (Fin n) (Fin n) _) *
        (g : Matrix (Fin n) (Fin n) _) := rfl
  rw [h1, h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g _

end PositivityTheory.Rg.BcB.G3.Count2P

open PositivityTheory.Rg.BcB.G3.Count2P in
/- English proof (translation)
Introduce `E _ _ _ hU a b S hS P₁ hP₁ P₂ hP₂ y hy hint`. Choose the witnesses or unpack the hypotheses as in `⟨zz, hzz, hzK⟩ : ∃ zz : ∀ w : Pl E, GLw a w × GLw b w, (∀ w, (Quot.mk _ (zz w) : TwCl ((thL a w).prodMap (thL b w))) = y w) ∧ ∀ᶠ w in cofinite, zz w ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by`. Use `⟨fun w => if h : ∃ z ∈ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)), y w = Quot.mk _ z then h.choose else (y w).rep, fun w => ?_, hint.mono fun w hw => ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs with h`. Conclude with `h.choose_spec.2.symm`.

Conclude with `Quot.out_eq _`. Simplify using `only`. Rewrite using `[dif_pos hw]`. Conclude with `hw.choose_spec.1`. Establish `hrel : ∀ w, ∃ g, (y w).rep = g⁻¹ * zz w * ((thL a w).prodMap (thL b w)) g`.

Introduce `w`. Rewrite using `[← mk_eq_iff, hzz w]`. Conclude with `Quot.out_eq _`. Establish `hc1 : ∀ w, (nrmL a w (zz w).1).val.charpoly = atPl w P₁` using `fun w => by`. Rewrite using `[← (hy w).1]`.

Conclude with `(charpoly_eq hU a w _ _ ((prod_rel _ _ _ _).1 (hrel w)).1).symm`. Establish `hc2 : ∀ w, (nrmL b w (zz w).2).val.charpoly = atPl w P₂` using `fun w => by`. Rewrite using `[← (hy w).2]`. Conclude with `(charpoly_eq hU b w _ _ ((prod_rel _ _ _ _).1 (hrel w)).2).symm`. Establish `e1 : Nat.card {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧ ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} * 2 ^ nfac P₁ = 2 ^ (a * Fintype.card (InfinitePlace E))` using `h1 E hU a S hS P₁ hP₁ (fun w => (zz w).1) hc1 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).1)`.

Establish `e2 : Nat.card {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧ ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} * 2 ^ nfac P₂ = 2 ^ (b * Fintype.card (InfinitePlace E))` using `h1 E hU b S hS P₂ hP₂ (fun w => (zz w).2) hc2 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).2)`. Establish `key : ∀ (c : TwCl (thE E a) × TwCl (thE E b)) (w : Pl E), (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w ↔ (∃ g, locEl a w c.1.rep = g⁻¹ * (zz w).1 * thL a w g) ∧ (∃ g, locEl b w c.2.rep = g⁻¹ * (zz w).2 * thL b w g)`. Introduce `c w`. Rewrite using `[← hzz w]`. Conclude with `(mk_eq_iff _ _ _).trans (prod_rel _ _ _ _)`.

Set `eqv : {c : TwCl (thE E a) × TwCl (thE E b) // ((c.1.rep * thE E a c.1.rep).val.charpoly = P₁ ∧ (c.2.rep * thE E b c.2.rep).val.charpoly = P₂) ∧ ∀ w ∈ S, (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w} ≃ {c : TwCl (thE E a) // (c.rep …` to `{ toFun := fun c => (⟨c.1.1, c.2.1.1, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).1⟩, ⟨c.1.2, c.2.1.2, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).2⟩) invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2.1, p.2.2.1⟩, fun w hw => (key (p.1.1, p.2.1) w).2 ⟨p.1.2.2 w hw, p.2.2.2 w hw⟩⟩ left_inv := …`. Rewrite using `[Nat.card_congr eqv, Nat.card_prod, add_mul, pow_add, pow_add, ← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PositivityTheory.Rg.BcB.G3.count2_pf (h1 : Count1) : Count2 := by
  intro E _ _ _ hU a b S hS P₁ hP₁ P₂ hP₂ y hy hint
  obtain ⟨zz, hzz, hzK⟩ : ∃ zz : ∀ w : Pl E, GLw a w × GLw b w,
      (∀ w, (Quot.mk _ (zz w) : TwCl ((thL a w).prodMap (thL b w))) = y w) ∧
        ∀ᶠ w in cofinite, zz w ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
    refine ⟨fun w => if h : ∃ z ∈ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)),
        y w = Quot.mk _ z then h.choose else (y w).rep, fun w => ?_, hint.mono fun w hw => ?_⟩
    · dsimp only
      split_ifs with h
      · exact h.choose_spec.2.symm
      · exact Quot.out_eq _
    · dsimp only
      rw [dif_pos hw]
      exact hw.choose_spec.1
  have hrel : ∀ w, ∃ g, (y w).rep = g⁻¹ * zz w * ((thL a w).prodMap (thL b w)) g := by
    intro w
    rw [← mk_eq_iff, hzz w]
    exact Quot.out_eq _
  have hc1 : ∀ w, (nrmL a w (zz w).1).val.charpoly = atPl w P₁ := fun w => by
    rw [← (hy w).1]
    exact (charpoly_eq hU a w _ _ ((prod_rel _ _ _ _).1 (hrel w)).1).symm
  have hc2 : ∀ w, (nrmL b w (zz w).2).val.charpoly = atPl w P₂ := fun w => by
    rw [← (hy w).2]
    exact (charpoly_eq hU b w _ _ ((prod_rel _ _ _ _).1 (hrel w)).2).symm
  have e1 : Nat.card {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
      ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} * 2 ^ nfac P₁ =
      2 ^ (a * Fintype.card (InfinitePlace E)) :=
    h1 E hU a S hS P₁ hP₁ (fun w => (zz w).1) hc1 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).1)
  have e2 : Nat.card {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
      ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} * 2 ^ nfac P₂ =
      2 ^ (b * Fintype.card (InfinitePlace E)) :=
    h1 E hU b S hS P₂ hP₂ (fun w => (zz w).2) hc2 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).2)
  have key : ∀ (c : TwCl (thE E a) × TwCl (thE E b)) (w : Pl E),
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w ↔
        (∃ g, locEl a w c.1.rep = g⁻¹ * (zz w).1 * thL a w g) ∧
          (∃ g, locEl b w c.2.rep = g⁻¹ * (zz w).2 * thL b w g) := by
    intro c w
    rw [← hzz w]
    exact (mk_eq_iff _ _ _).trans (prod_rel _ _ _ _)
  let eqv : {c : TwCl (thE E a) × TwCl (thE E b) // ((c.1.rep * thE E a c.1.rep).val.charpoly = P₁ ∧
      (c.2.rep * thE E b c.2.rep).val.charpoly = P₂) ∧ ∀ w ∈ S,
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w} ≃
      {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
        ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} ×
      {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
        ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} :=
    { toFun := fun c => (⟨c.1.1, c.2.1.1, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).1⟩,
        ⟨c.1.2, c.2.1.2, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2.1, p.2.2.1⟩,
        fun w hw => (key (p.1.1, p.2.1) w).2 ⟨p.1.2.2 w hw, p.2.2.2 w hw⟩⟩
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr eqv, Nat.card_prod, add_mul, pow_add, pow_add, ← e1, ← e2]
  ring

end
