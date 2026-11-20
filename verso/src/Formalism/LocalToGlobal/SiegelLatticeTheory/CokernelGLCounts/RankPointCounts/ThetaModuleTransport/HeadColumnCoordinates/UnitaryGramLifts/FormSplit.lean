import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section FormSplit

/- English proof (translation)
Unfold `formG`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, Subring.coe_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fs_add_left (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y Y' W : Ix r → O) :
    formG O cj qi Z T T' (Y + Y') W = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y' W := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add]
  ring

/- English proof (translation)
Unfold `formG`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, Subring.coe_add, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fs_add_right (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y (W + W') = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y W' := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add, map_add]
  ring

/- English proof (translation)
Break down `i with a | a` into its components or cases. Rewrite using `[secondProj_apply, e_iota1_inl]`. Rewrite using `[secondProj_apply, e_iota1_inr]`.
-/
theorem splitSecondProj_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g ((iota1 hs l i : M.L.O) : E) = 0 := by
  rcases i with a | a
  · rw [secondProj_apply, e_iota1_inl]
  · rw [secondProj_apply, e_iota1_inr]

/- English proof (translation)
Rewrite using `[firstProj_apply, e_iota2]`.
-/
theorem splitFirstProj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((iota2 hs l i : M.L.O) : E) = 0 := by
  rw [firstProj_apply, e_iota2]

/- English proof (translation)
The claim follows from `secondProj_conj_eq_firstProj x`.
-/
theorem splitSecondProj_conj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := secondProj_conj_eq_firstProj x

/- English proof (translation)
Rewrite using `[eq_iff_ph (g := g)]`. Unfold `formG`. Simplify using `only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitSecondProj_iotaOne, mul_zero, zero_mul, Finset.sum_const_zero]`. Simplify using the standard rewrite rules.
-/
theorem splitForm_iotaOne_iotaOne (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota1 hs l) (iota1 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG
  simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitSecondProj_iotaOne, mul_zero, zero_mul,
    Finset.sum_const_zero]
  simp

/- English proof (translation)
Rewrite using `[eq_iff_ph (g := g)]`. Unfold `formG`. Simplify using `only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitFirstProj_iotaTwo, mul_zero, zero_mul, Finset.sum_const_zero]`. Simplify using the standard rewrite rules.
-/
theorem splitForm_iotaTwo_iotaTwo (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota2 hs l) (iota2 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG
  simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitFirstProj_iotaTwo, mul_zero, zero_mul,
    Finset.sum_const_zero]
  simp

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem fs_map_inv {n : Type} [Fintype n] [DecidableEq n] (f : E →+* E) (A : Matrix n n E) (hA : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Apply the tactic sequence `rcases i with a | a <;> rcases j with b | b <;> by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>`. Apply the tactic sequence `simp [gramG, cor, ha, hb, map_mul, map_add, map_neg, map_sub, M.L.cj_cj, AlgEquiv.commutes] <;> ring`.
-/
theorem fs_gram_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F) (i j : Ix r) :
    (M.L.cj : E →+* E) (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') j i) =
      gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') i j := by
  rcases i with a | a <;> rcases j with b | b <;> by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
    simp [gramG, cor, ha, hb, map_mul, map_add, map_neg, map_sub, M.L.cj_cj, AlgEquiv.commutes] <;> ring

/- English proof (translation)
Take `⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') = G` from `⟨_, rfl⟩`. Rewrite `hU` using `[hGd]`. Establish `hT : G.map (M.L.cj : E →+* E) = G.transpose`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.transpose_apply, ← hGd, fs_gram_herm]`.

Establish `hinv : ∀ i j, (M.L.cj : E →+* E) (G⁻¹ i j) = G⁻¹ j i`. Introduce `i j`. Use `congrFun (congrFun (fs_map_inv (M.L.cj : E →+* E) G hU) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`. Establish `h2 : (G.transpose)⁻¹ = (G⁻¹).transpose` using `by rw [Matrix.transpose_nonsing_inv]`.

Rewrite using `[this, hT, h2, Matrix.transpose_apply]`. Establish `hcc : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x` using `M.L.cj_cj`. Unfold `formG`. Simplify using `only [hGd, map_sum, map_mul, hcc, hinv]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fs_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      (M.L.cj : E →+* E)
        (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') W Y) := by
  obtain ⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') = G :=
    ⟨_, rfl⟩
  rw [hGd] at hU
  have hT : G.map (M.L.cj : E →+* E) = G.transpose := by
    ext i j; rw [Matrix.map_apply, Matrix.transpose_apply, ← hGd, fs_gram_herm]
  have hinv : ∀ i j, (M.L.cj : E →+* E) (G⁻¹ i j) = G⁻¹ j i := by
    intro i j
    have := congrFun (congrFun (fs_map_inv (M.L.cj : E →+* E) G hU) i) j
    rw [Matrix.map_apply] at this
    have h2 : (G.transpose)⁻¹ = (G⁻¹).transpose := by rw [Matrix.transpose_nonsing_inv]
    rw [this, hT, h2, Matrix.transpose_apply]
  have hcc : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x := M.L.cj_cj
  unfold formG
  simp only [hGd, map_sum, map_mul, hcc, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use `conv_lhs => rw [← iota_cmp hs Y, ← iota_cmp hs W]`. Rewrite using `[fs_add_left, fs_add_right, fs_add_right, splitForm_iotaOne_iotaOne, splitForm_iotaTwo_iotaTwo, fs_herm Zh T T' _ hU (iota2 hs (cmp2 hs Y)) (iota1 hs (cmp1 hs W))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fs_split (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs (cmp1 hs Y)) (iota2 hs (cmp2 hs W)) +
        (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
          (algebraMap F E T') (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) := by
  conv_lhs => rw [← iota_cmp hs Y, ← iota_cmp hs W]
  rw [fs_add_left, fs_add_right, fs_add_right, splitForm_iotaOne_iotaOne, splitForm_iotaTwo_iotaTwo,
    fs_herm Zh T T' _ hU (iota2 hs (cmp2 hs Y)) (iota1 hs (cmp1 hs W))]
  ring

/- English proof (translation)
Rewrite using `[thetaOf, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]`. Simplify using `[splitH, splitQ_mk, Prod.ext_iff]`. Conclude with `Iff.rfl`.
-/
theorem fs_rel (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) (Y Y₂ : Ix r → M.L.O) :
    thetaOf hs h₁ h₂ θ₁ θ₂ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ ↔
      θ₁ (QuotientAddGroup.mk (cmp1 hs Y)) = QuotientAddGroup.mk (cmp1 hs Y₂) ∧
        θ₂ (QuotientAddGroup.mk (cmp2 hs Y)) = QuotientAddGroup.mk (cmp2 hs Y₂) := by
  rw [thetaOf, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  simp [splitH, splitQ_mk, Prod.ext_iff]
  exact Iff.rfl

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂`. Establish `hU₁` using `unitGramG_holds F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁`. Establish `hU₂` using `unitGramG_holds F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂`. Prove the components needed by the constructor for the conclusion. Introduce `hF l l₂ w w₂ hl hw`.

Use `hF (iota1 hs l) (iota2 hs w) (iota1 hs l₂) (iota2 hs w₂) ?_ ?_` and prove the remaining obligations. Rewrite using `[fs_rel, firstComponent_iotaOne, firstComponent_iotaOne, secondComponent_iotaOne, secondComponent_iotaOne]`. Conclude with `⟨hl, by simp⟩`. Rewrite using `[fs_rel, firstComponent_iotaTwo, firstComponent_iotaTwo, secondComponent_iotaTwo, secondComponent_iotaTwo]`. Conclude with `⟨by simp, hw⟩`.

Introduce `hB Y W Y₂ W₂ hY hW`. Rewrite `hY`, `hW` using `[fs_rel]`. Rewrite using `[fs_split hs Zh₂ T T' hU₂, fs_split hs Zh₁ T T' hU₁]`. Establish `e1` using `hB (cmp1 hs Y) (cmp1 hs Y₂) (cmp2 hs W) (cmp2 hs W₂) hY.1 hW.2`. Establish `e2` using `hB (cmp1 hs W) (cmp1 hs W₂) (cmp2 hs Y) (cmp2 hs Y₂) hW.1 hY.2`.

Establish `e2' : (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T) (algebraMap F E T') (iota1 hs (cmp1 hs W₂)) (iota2 hs (cmp2 hs Y₂)) - formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F …` using `cj_mem_O M.L e2`. Use `add_mem e1 e2' using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formSplit_holds : FormSplitP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂
  have hU₁ := unitGramG_holds F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁
  have hU₂ := unitGramG_holds F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂
  constructor
  · intro hF l l₂ w w₂ hl hw
    refine hF (iota1 hs l) (iota2 hs w) (iota1 hs l₂) (iota2 hs w₂) ?_ ?_
    · rw [fs_rel, firstComponent_iotaOne, firstComponent_iotaOne, secondComponent_iotaOne, secondComponent_iotaOne]
      exact ⟨hl, by simp⟩
    · rw [fs_rel, firstComponent_iotaTwo, firstComponent_iotaTwo, secondComponent_iotaTwo, secondComponent_iotaTwo]
      exact ⟨by simp, hw⟩
  · intro hB Y W Y₂ W₂ hY hW
    rw [fs_rel] at hY hW
    rw [fs_split hs Zh₂ T T' hU₂, fs_split hs Zh₁ T T' hU₁]
    have e1 := hB (cmp1 hs Y) (cmp1 hs Y₂) (cmp2 hs W) (cmp2 hs W₂) hY.1 hW.2
    have e2 := hB (cmp1 hs W) (cmp1 hs W₂) (cmp2 hs Y) (cmp2 hs Y₂) hW.1 hY.2
    have e2' : (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂
        (algebraMap F E T) (algebraMap F E T') (iota1 hs (cmp1 hs W₂)) (iota2 hs (cmp2 hs Y₂)) -
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) ∈ M.L.O := cj_mem_O M.L e2
    convert add_mem e1 e2' using 1
    rw [map_sub]
    ring

end FormSplit

end Formalism.L2.SG.LocalCountModules.AlgGSplit
