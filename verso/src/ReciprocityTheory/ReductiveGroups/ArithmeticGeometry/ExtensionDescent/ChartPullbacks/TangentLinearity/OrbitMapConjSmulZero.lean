import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

/- English proof (translation)
Replace the relevant objects with their definitions. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
lemma padd_comm {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] {T : Over S}
    (x y : T ⟶ B) : padd B x y = padd B y x := by
  unfold padd
  first
  | exact mul_comm x y
  | (rw (occs := .pos [1]) [← IsCommMonObj.mul_comm B]; rw [← Category.assoc]; congr 1; ext <;> simp)
  | rw [Category.id_comp]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
lemma ite_neg_one_eq_neg (c : Prop) [Decidable c] : (if c then (-1 : ℤ) else 0) = -(if c then 1 else 0) := by
  split_ifs <;> simp

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)

abbrev xc : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.toPre.P.A :=
  toUnit _ ≫ D.toPre.c χ

abbrev hOv : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
    (Over.map (thick R I e)).obj (thickObj R I e G) :=
  (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map (ιG.act a))

abbrev φA : Fin 4 ⊕ Fin 6 → ((thickObj R I e G).left ⟶ D.toPre.P.A.left) :=
  Sum.elim (D.toPre.Oφ (U.gt e).pG (star a • χ))
    (fun k => (lift (xc e χ (G := G)) (U.gt e).pG).left ≫
      rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)

abbrev εA : Fin 4 ⊕ Fin 6 → ℤ := Sum.elim Oinvε rosatiε

abbrev φB : Fin 4 → ((thickObj R I e G).left ⟶ D.toPre.P.A.left) :=
  fun k => ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ D.toPre.Oφ (U.gt e).pG χ k

abbrev lhs (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε)) :
    LB.Gen (LB.LinComb D.toPre.P.L (φA U ιD e a χ) εA) :=
  LB.mulGen D.toPre.P.L _ _ _ _ ((U.gt e).t (star a • χ))
    (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left)

abbrev rhs : LB.Gen (LB.LinComb D.toPre.P.L (φB U ιG e a χ) Oinvε) :=
  LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (thick R I e)).map (ιG.act a)).left

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma c_star : toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.toPre.c (star a • χ) =
    xc e χ (G := G) ≫ ιD.onB.act (star a) := by
  rw [ιD.c_lin (star a) χ, ← Category.assoc]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
lemma hOv_pG (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a)) :
    hOv ιG e a ≫ (U.gt e).pG = (U.gt e).pG ≫ ιD.onB.act a := by
  simp only [hOv, GtCoord.pG, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, hO a, Functor.map_comp, Category.assoc]
  congr 1
  ext
  simp only [DegPre.prBe, Over.comp_left, Over.homMk_left, Over.map_map_left]
  first
  | exact pullback.lift_fst _ _ _
  | simp

end Fam

section Eqs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)

abbrev OφX {T : Over (Spec (CommRingCat.of R))} (P x : T ⟶ D.toPre.P.A) :
    Fin 4 → (T.left ⟶ D.toPre.P.A.left) :=
  ![(padd D.toPre.P.A P x).left, x.left, P.left, (toUnit T ≫ η[D.toPre.P.A]).left]

omit [Module O D.toPre.X] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma OφX_0 {T : Over (Spec (CommRingCat.of R))} (P x : T ⟶ D.toPre.P.A) :
    OφX (D := D) P x 0 = (padd D.toPre.P.A P x).left := rfl
omit [Module O D.toPre.X] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma OφX_1 {T : Over (Spec (CommRingCat.of R))} (P x : T ⟶ D.toPre.P.A) :
    OφX (D := D) P x 1 = x.left := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma eAk (k : Fin 4) : D.toPre.Oφ (U.gt e).pG (star a • χ) k =
    OφX (D := D) (U.gt e).pG (xc e χ (G := G) ≫ ιD.onB.act (star a)) k := by
  rw [← c_star (G := G) ιD e a χ]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma orbitMap_conj_smul_zero : D.toPre.Oφ (U.gt e).pG (star a • χ) 0 =
    (padd D.toPre.P.A (U.gt e).pG (xc e χ (G := G) ≫ ιD.onB.act (star a))).left := by
  rw [eAk U ιD e a χ 0]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma orbitMap_conj_smul_one : D.toPre.Oφ (U.gt e).pG (star a • χ) 1 = (xc e χ (G := G) ≫ ιD.onB.act (star a)).left := by
  rw [eAk U ιD e a χ 1]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma orbitMap_conj_smul_two : D.toPre.Oφ (U.gt e).pG (star a • χ) 2 = (U.gt e).pG.left := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma selfLieBasisVector : D.toPre.Oφ (U.gt e).pG (star a • χ) 3 =
    (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.toPre.P.A]).left := rfl

variable {U ιD e a χ} in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
lemma eR (f g : D.toPre.P.A ⟶ D.toPre.P.A) (X P : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.toPre.P.A) :
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 0 = (padd D.toPre.P.A (X ≫ f) P).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 1 = (X ≫ f).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 2 = P.left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 3 = (padd D.toPre.P.A X (P ≫ g)).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 4 = X.left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 5 = (P ≫ g).left := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (lift X P).left ≫ (padd D.toPre.P.A (fst D.toPre.P.A D.toPre.P.A ≫ f) (snd D.toPre.P.A D.toPre.P.A)).left = _
    rw [← Over.comp_left]
    congr 1
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    simp
  · change (lift X P).left ≫ (fst D.toPre.P.A D.toPre.P.A ≫ f).left = _
    rw [← Over.comp_left]
    congr 1
    simp
  · change (lift X P).left ≫ (snd D.toPre.P.A D.toPre.P.A).left = _
    rw [← Over.comp_left]
    congr 1
    simp
  · change (lift X P).left ≫ (padd D.toPre.P.A (fst D.toPre.P.A D.toPre.P.A) (snd D.toPre.P.A D.toPre.P.A ≫ g)).left = _
    rw [← Over.comp_left]
    congr 1
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    simp
  · change (lift X P).left ≫ (fst D.toPre.P.A D.toPre.P.A).left = _
    rw [← Over.comp_left]
    congr 1
    simp
  · change (lift X P).left ≫ (snd D.toPre.P.A D.toPre.P.A ≫ g).left = _
    rw [← Over.comp_left]
    congr 1
    simp

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma Ophi_nat_lemma {T T' : Over (Spec (CommRingCat.of R))} (h : T' ⟶ T)
    (p : T ⟶ D.toPre.P.A) (χ : D.toPre.X) (k : Fin 4) :
    h.left ≫ D.toPre.Oφ p χ k = D.toPre.Oφ (h ≫ p) χ k := by
  fin_cases k <;> simp [DegPre.Oφ, padd, ← Over.comp_left]
  all_goals
    congr 1
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma eB (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a)) (k : Fin 4) :
    φB U ιG e a χ k = D.toPre.Oφ ((U.gt e).pG ≫ ιD.onB.act a) χ k := by
  rw [← hOv_pG U ιD ιG e a hO]
  exact Ophi_nat_lemma (hOv ιG e a) (U.gt e).pG χ k

end Eqs

section Sums

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))

include hO in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Supply the required witnesses or components.

Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
lemma hsub : ∀ k : Fin 4, ∃ k', φA U ιD e a χ k' = φB U ιG e a χ k := by
  intro k
  obtain ⟨_, _, _, h3, h4, h5⟩ :=
    eR (e := e) (ιD.onB.act (star a)) (ιD.onB.act a) (xc e χ (G := G)) (U.gt e).pG
  rw [eB U ιD ιG e a χ hO k]
  fin_cases k
  · exact ⟨Sum.inr 3, h3.trans (by rw [padd_comm]; rfl)⟩
  · exact ⟨Sum.inr 4, h4⟩
  · exact ⟨Sum.inr 5, h5⟩
  · exact ⟨Sum.inl 3, (selfLieBasisVector U e a χ).trans rfl⟩

omit [IsDomain R] in
/- English proof (translation)
Supply the required witnesses or components.
-/
lemma v4 {α : Type} (w x y z : α) : ![w, x, y, z] 0 = w ∧ ![w, x, y, z] 1 = x ∧
    ![w, x, y, z] 2 = y ∧ ![w, x, y, z] 3 = z := ⟨rfl, rfl, rfl, rfl⟩

omit [IsDomain R] in
/- English proof (translation)
Supply the required witnesses or components.
-/
lemma v6 {α : Type} (a b c d f g : α) : ![a, b, c, d, f, g] 0 = a ∧ ![a, b, c, d, f, g] 1 = b ∧
    ![a, b, c, d, f, g] 2 = c ∧ ![a, b, c, d, f, g] 3 = d ∧ ![a, b, c, d, f, g] 4 = f ∧
    ![a, b, c, d, f, g] 5 = g := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
private lemma ss_lemma {Y X : Scheme.{0}} (pB x Pa u0 pA xs P : Y ⟶ X) :
    LB.SameSum ![pB, x, Pa, u0] Oinvε (Sum.elim ![pA, xs, P, u0] ![pA, xs, P, pB, x, Pa])
      (Sum.elim Oinvε rosatiε) := by
  intro ψ
  simp only [Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_six]
  show @ite ℤ (pB = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (x = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (Pa = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (u0 = ψ) (Classical.propDecidable _) (-1) 0 =
    (@ite ℤ (pA = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (xs = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (P = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (u0 = ψ) (Classical.propDecidable _) (-1) 0) +
    (@ite ℤ (pA = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (xs = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (P = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (pB = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (x = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (Pa = ψ) (Classical.propDecidable _) (1) 0)
  simp only [ite_neg_one_eq_neg]
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
lemma hA : φA U ιD e a χ = Sum.elim
    ![(padd D.toPre.P.A (U.gt e).pG (xc e χ (G := G) ≫ ιD.onB.act (star a))).left,
      (xc e χ (G := G) ≫ ιD.onB.act (star a)).left, (U.gt e).pG.left,
      (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.toPre.P.A]).left]
    ![(padd D.toPre.P.A (xc e χ (G := G) ≫ ιD.onB.act (star a)) (U.gt e).pG).left,
      (xc e χ (G := G) ≫ ιD.onB.act (star a)).left, (U.gt e).pG.left,
      (padd D.toPre.P.A (xc e χ (G := G)) ((U.gt e).pG ≫ ιD.onB.act a)).left,
      (xc e χ (G := G)).left, ((U.gt e).pG ≫ ιD.onB.act a).left] := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    eR (e := e) (ιD.onB.act (star a)) (ιD.onB.act a) (xc e χ (G := G)) (U.gt e).pG
  funext k
  rcases k with k | k
  · fin_cases k
    · exact orbitMap_conj_smul_zero U ιD e a χ
    · exact orbitMap_conj_smul_one U ιD e a χ
    · exact orbitMap_conj_smul_two U e a χ
    · exact selfLieBasisVector U e a χ
  · fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

include hO in

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma hBv : φB U ιG e a χ =
    ![(padd D.toPre.P.A ((U.gt e).pG ≫ ιD.onB.act a) (xc e χ (G := G))).left,
      (xc e χ (G := G)).left, ((U.gt e).pG ≫ ιD.onB.act a).left,
      (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.toPre.P.A]).left] := by
  funext k
  rw [eB U ιD ιG e a χ hO k]
  fin_cases k <;> rfl

include hO in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma sameSum : LB.SameSum (φB U ιG e a χ) Oinvε (φA U ιD e a χ) εA := by
  rw [hA U ιD e a χ, hBv U ιD ιG e a χ hO,
    padd_comm D.toPre.P.A (xc e χ (G := G) ≫ ιD.onB.act (star a)) (U.gt e).pG,
    padd_comm D.toPre.P.A (xc e χ (G := G)) ((U.gt e).pG ≫ ιD.onB.act a)]
  exact ss_lemma _ _ _ _ _ _ _

end Sums

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
