import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalComponentMemIntegralGLCofiniStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTestFactorNeZeroOfGlobalProductNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlAdicCompletionEntriesBoundedOfIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormComplexEmbeddingEntryDefiniteUnitaryRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfValuationBoundedNormLeOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

/- English proof (translation)
The claim follows from `GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite`.
-/
theorem cLoc_eventually_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w n := GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite

/- English proof (translation)
The claim follows from `GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero`.
-/
theorem factor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU E n, (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w n) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero

/- English proof (translation)
Introduce `E _ _ _ hU n w y`. Distinguish the cases in `hs : IsSplitAt w`. Unfold `UL`. Rewrite using `[if_pos hs]`. Conclude with `Subgroup.mem_top _`.

Take `⟨-, -, hloc, -⟩` from `(GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs`. Establish `hu` using `GlobalTheory.DefU.ClassFin.cT_pFin y`. Unfold `UL`. Rewrite using `[if_neg hs]`. Express the relevant statement in the definitionally equal form `cT (cj w) (cLoc w y).val * 1 * (cLoc w y).val = 1`.

Rewrite using `[mul_one]`. Establish `key : cT (cj w) ((GeneralLinearGroup.map (pFin E) (y : GA E n)).val.map (pLoc E w)) = (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [cT, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `(hloc _).symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.map_mul, ← key]`. Both sides reduce to the same expression. Use `_ = 1 := by rw [hu, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem cLoc_mem_UL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UA E n), cLoc w y ∈ UL n w := by
  intro E _ _ _ hU n w y
  by_cases hs : IsSplitAt w
  · unfold UL
    rw [if_pos hs]
    exact Subgroup.mem_top _
  · obtain ⟨-, -, hloc, -⟩ := (GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs
    have hu := GlobalTheory.DefU.ClassFin.cT_pFin y
    unfold UL
    rw [if_neg hs]
    change cT (cj w) (cLoc w y).val * 1 * (cLoc w y).val = 1
    rw [mul_one]
    have key : cT (cj w) ((GeneralLinearGroup.map (pFin E) (y : GA E n)).val.map (pLoc E w)) =
        (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w) := by
      refine Matrix.ext fun i j => ?_
      simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
      exact (hloc _).symm
    calc cT (cj w) (cLoc w y).val * (cLoc w y).val =
        (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val *
          (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w) := by
          rw [Matrix.map_mul, ← key]
          rfl
      _ = 1 := by rw [hu, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
The claim follows from `GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact`.
-/
theorem compact_val_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))), IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j, Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact

/- English proof (translation)
Introduce `E _ _ _ w a`. Take `⟨-, h1, h2⟩` from `conjLoc_spec (GlobalTheory.SplitPts.conjE E) w`. Establish `hv : ∀ (v : Pl E) (b : E), Valued.v (algebraMap E (v.adicCompletion E) b) = v.valuation E b` using `fun v b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v b`. Establish `e` using `h2 (algebraMap E _ a)`. Rewrite `e` using `[h1]`.

Rewrite using `[← hv, ← hv]`. Conclude with `e`.
-/
theorem valuation_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : E), w.valuation E (IsCMField.complexConj E a) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E a := by
  intro E _ _ _ w a
  obtain ⟨-, h1, h2⟩ := conjLoc_spec (GlobalTheory.SplitPts.conjE E) w
  have hv : ∀ (v : Pl E) (b : E), Valued.v (algebraMap E (v.adicCompletion E) b) = v.valuation E b :=
    fun v b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v b
  have e := h2 (algebraMap E _ a)
  rw [h1] at e
  rw [← hv, ← hv]
  exact e

/- English proof (translation)
Introduce `E _ _ _ S hS`. Use `⟨fun w hw => ?_, ?_⟩` and prove the remaining obligations. Take `⟨u, ⟨huS, hu⟩, -⟩` from `hS w`. Distinguish the cases in `hs : IsSplitAt w`. Break down `(GlobalTheory.SplitPts.over_split hs).2.2 u hu with rfl | h` into its components or cases.

Conclude with `absurd huS hw`. Rewrite using `[← h]` and apply the resulting hypothesis. It suffices to derive a contradiction. Conclude with `hs ⟨u, fun h => hw (h ▸ huS), hu⟩`. Introduce `a b hab`.

Establish `ha` using `GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) a`. Establish `hb` using `GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) b`. Rewrite `ha` using `[hab]`. Rewrite `ha`, `hb` using `[GlobalTheory.Mem.Chr.conjPl_iff_mem]`. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations.

Establish `hy : IsIntegral ℤ ((GlobalTheory.SplitPts.conjE E) (x : E))` using `x.isIntegral_coe.map (RingHom.toIntAlgHom (GlobalTheory.SplitPts.conjE E).toRingHom)`. Conclude with `(ha x ⟨_, hy⟩ rfl).trans (hb x ⟨_, hy⟩ rfl).symm`.
-/
theorem section_conjSrc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → (∀ w, w ∉ S → conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S) ∧ Function.Injective (conjSrc (GlobalTheory.SplitPts.conjE E)) := by
  intro E _ _ _ S hS
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
    by_cases hs : IsSplitAt w
    · rcases (GlobalTheory.SplitPts.over_split hs).2.2 u hu with rfl | h
      · exact absurd huS hw
      · rwa [← h]
    · exfalso
      exact hs ⟨u, fun h => hw (h ▸ huS), hu⟩
  · intro a b hab
    have ha := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) a
    have hb := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) b
    rw [hab] at ha
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at ha hb
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have hy : IsIntegral ℤ ((GlobalTheory.SplitPts.conjE E) (x : E)) :=
      x.isIntegral_coe.map (RingHom.toIntAlgHom (GlobalTheory.SplitPts.conjE E).toRingHom)
    exact (ha x ⟨_, hy⟩ rfl).trans (hb x ⟨_, hy⟩ rfl).symm

/- English proof (translation)
The claim follows from `GlobalTheory.T.norm_complexEmbedding_entry_definiteUnitaryRational_le_one`.
-/
theorem unitary_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ (γ.1.val i j)‖ ≤ 1 := GlobalTheory.T.norm_complexEmbedding_entry_definiteUnitaryRational_le_one

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_of_valuation_bounded_norm_le_one`.
-/
theorem finite_of_local_bounds : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := GlobalTheory.T.finite_of_valuation_bounded_norm_le_one

/- English proof (translation)
Introduce `E _ _ _ n w γ`. Establish `h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1` using `γ.2`. Rewrite `h` using `[mul_one]`. Establish `hc : cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (ratF E n γ.1).val * (ratF E n γ.1).val = 1`. Establish `e : (ratF E n γ.1).val = γ.1.val.map (algebraMap E (Af E))` using `rfl`.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.map_mul]`. Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [cT, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `conjFin_algebraMap (E := E) _ _`. Use `_ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero (algebraMap E (Af E))) (map_one (algebraMap E (Af E)))`. Establish `hUA` using `GlobalTheory.DefU.ClassFin.finGL_mem_UA _ hc`. Establish `hfin : (⟨_, hUA⟩ : UA E n) ∈ finU E n` using `(MonoidHom.mem_ker).2 (Units.ext (by`.

Use `pInf_finGL (E := E) (ratF E n γ.1)` as an intermediate fact. Conclude with `congrArg Units.val this))`. Establish `e0 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, hUA⟩` using `dif_pos hUA`. Establish `e1 : (finPt γ).1 = ⟨finGL E n (ratF E n γ.1), hUA⟩`. Unfold `finPt`.

Rewrite using `[e0]`. Conclude with `congrArg Subtype.val (dif_pos hfin)`. Rewrite using `[e1]`. Establish `h2` using `GlobalTheory.CuspRep.pFin_finGL (E := E) (a := n) (ratF E n γ.1)`. Apply `Units.ext` to reduce the goal to its premises.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) h2`.
-/
theorem cLoc_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (γ : UE E n), cLoc w (finPt γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  intro E _ _ _ n w γ
  have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [mul_one] at h
  have hc : cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (ratF E n γ.1).val * (ratF E n γ.1).val = 1 := by
    have e : (ratF E n γ.1).val = γ.1.val.map (algebraMap E (Af E)) := rfl
    rw [e]
    calc cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (γ.1.val.map (algebraMap E (Af E))) * γ.1.val.map (algebraMap E (Af E))
        = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * γ.1.val).map (algebraMap E (Af E)) := by
          rw [Matrix.map_mul]
          congr 1
          refine Matrix.ext fun i j => ?_
          simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
          exact conjFin_algebraMap (E := E) _ _
      _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero (algebraMap E (Af E))) (map_one (algebraMap E (Af E)))
  have hUA := GlobalTheory.DefU.ClassFin.finGL_mem_UA _ hc
  have hfin : (⟨_, hUA⟩ : UA E n) ∈ finU E n := (MonoidHom.mem_ker).2 (Units.ext (by
    have := pInf_finGL (E := E) (ratF E n γ.1)
    exact congrArg Units.val this))
  have e0 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, hUA⟩ := dif_pos hUA
  have e1 : (finPt γ).1 = ⟨finGL E n (ratF E n γ.1), hUA⟩ := by
    unfold finPt
    rw [e0]
    exact congrArg Subtype.val (dif_pos hfin)
  rw [e1]
  have h2 := GlobalTheory.CuspRep.pFin_finGL (E := E) (a := n) (ratF E n γ.1)
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  exact congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) h2

end GlobalTheory.BCT.SuppFin

namespace GlobalTheory.BCT.SuppFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Take `⟨k, rfl⟩` from `hh`. Conclude with `(k.val i j).2`.
-/
theorem val_le_one_of_KGL {w : Pl E} {h : GL (Fin n) (w.adicCompletion E)} (hh : h ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    Valued.v (h.val i j) ≤ 1 := by
  obtain ⟨k, rfl⟩ := hh
  exact (k.val i j).2

/- English proof (translation)
Establish `h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1` using `γ.2`. Rewrite `h` using `[mul_one]`. Rewrite using `[Units.inv_eq_of_mul_eq_one_left h]`. Both sides reduce to the same expression.
-/
theorem conj_entry (γ : UE E n) (i j : Fin n) : IsCMField.complexConj E (γ.1.val i j) = (γ.1⁻¹).val j i := by
  have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [mul_one] at h
  rw [Units.inv_eq_of_mul_eq_one_left h]
  rfl

/- English proof (translation)
Use `set X : Set E := {a | ∃ γ ∈ Γs, ∃ i j, a = γ.1.val i j ∨ a = (γ.1⁻¹).val i j} with hXdef`. Establish `hcc : ∀ a : E, IsCMField.complexConj E (IsCMField.complexConj E a) = a` using `IsCMField.complexConj_apply_apply E`. Establish `hXc : ∀ a ∈ X, IsCMField.complexConj E a ∈ X`. Introduce and unpack `a ⟨γ, hγ, i, j, rfl | rfl⟩`. Apply the tactic sequence `exact ⟨γ, hγ, j, i, Or.inr (conj_entry γ i j)⟩`.

Use `⟨γ, hγ, j, i, Or.inl ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [← conj_entry γ j i, hcc]`. Take `⟨hsec, hinj⟩` from `section_conjSrc E S hS`. Establish `hval : ∀ (w : Pl E) (a : E), w.valuation E a = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E (IsCMField.complexConj E a)`. Introduce `w a`.

Rewrite using `[← valuation_conj, hcc]`. Establish `hall : ∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N`. Introduce `w`. Distinguish the cases in `hw : w ∈ S`. Take `⟨N, hN⟩` from `hb w hw`.

Use `⟨N, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨γ, hγ, i, j, rfl | rfl⟩`. Use `exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]`. Take `⟨N, hN⟩` from `hb _ (hsec w hw)`. Use `⟨N, fun a ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[hval]`. Apply the tactic sequence `obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]`. Use `exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]`. Establish `hcof : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1`. Establish `h2` using `hinj.tendsto_cofinite.eventually hc`.

Use `filter_upwards [hc, h2] with w h1 h2 a ha`. Distinguish the cases in `hw : w ∈ S`. Take `⟨γ, hγ, i, j, rfl | rfl⟩` from `ha exacts [(h1 hw γ hγ i j).1, (h1 hw γ hγ i j).2]`. Rewrite using `[hval]`. Apply the tactic sequence `obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]`.

Use `exacts [(h2 (hsec w hw) γ hγ i j).1, (h2 (hsec w hw) γ hγ i j).2]`. Establish `hinf : ∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1`. Introduce and unpack `a ⟨γ, hγ, i, j, rfl | rfl⟩ τ`. Conclude with `unitary_norm_le_one E n γ τ i j`. Conclude with `unitary_norm_le_one E n γ⁻¹ τ i j`.

Establish `hX` using `finite_of_local_bounds E X hall hcof hinf`. Establish `hM : (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => X).Finite` using `Set.Finite.pi fun _ => Set.Finite.pi fun _ => hX`. Use `(hM.preimage (f := fun γ : UE E n => (γ.1.val : Fin n → Fin n → E)) ?_).subset ?_` and prove the remaining obligations. Introduce `a _ b _ h`. Conclude with `Subtype.ext (Units.ext h)`.

Introduce `γ hγ i _ j _`. Conclude with `⟨γ, hγ, i, j, Or.inl rfl⟩`.
-/
theorem finite_of_bounds (S : Set (Pl E)) (hS : IsSection S) (Γs : Set (UE E n))
    (hb : ∀ w ∈ S, ∃ N : ℤ, ∀ γ ∈ Γs, ∀ i j, w.valuation E (γ.1.val i j) ≤ WithZero.exp N ∧
      w.valuation E ((γ.1⁻¹).val i j) ≤ WithZero.exp N)
    (hc : ∀ᶠ w in cofinite, w ∈ S → ∀ γ ∈ Γs, ∀ i j, w.valuation E (γ.1.val i j) ≤ 1 ∧
      w.valuation E ((γ.1⁻¹).val i j) ≤ 1) : Γs.Finite := by
  classical
  set X : Set E := {a | ∃ γ ∈ Γs, ∃ i j, a = γ.1.val i j ∨ a = (γ.1⁻¹).val i j} with hXdef
  have hcc : ∀ a : E, IsCMField.complexConj E (IsCMField.complexConj E a) = a := IsCMField.complexConj_apply_apply E
  have hXc : ∀ a ∈ X, IsCMField.complexConj E a ∈ X := by
    rintro a ⟨γ, hγ, i, j, rfl | rfl⟩
    · exact ⟨γ, hγ, j, i, Or.inr (conj_entry γ i j)⟩
    · refine ⟨γ, hγ, j, i, Or.inl ?_⟩
      rw [← conj_entry γ j i, hcc]
  obtain ⟨hsec, hinj⟩ := section_conjSrc E S hS
  have hval : ∀ (w : Pl E) (a : E), w.valuation E a =
      (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E (IsCMField.complexConj E a) := by
    intro w a
    rw [← valuation_conj, hcc]
  have hall : ∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨N, hN⟩ := hb w hw
      refine ⟨N, ?_⟩
      rintro a ⟨γ, hγ, i, j, rfl | rfl⟩
      exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]
    · obtain ⟨N, hN⟩ := hb _ (hsec w hw)
      refine ⟨N, fun a ha => ?_⟩
      rw [hval]
      obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]
      exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]
  have hcof : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1 := by
    have h2 := hinj.tendsto_cofinite.eventually hc
    filter_upwards [hc, h2] with w h1 h2 a ha
    by_cases hw : w ∈ S
    · obtain ⟨γ, hγ, i, j, rfl | rfl⟩ := ha
      exacts [(h1 hw γ hγ i j).1, (h1 hw γ hγ i j).2]
    · rw [hval]
      obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]
      exacts [(h2 (hsec w hw) γ hγ i j).1, (h2 (hsec w hw) γ hγ i j).2]
  have hinf : ∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1 := by
    rintro a ⟨γ, hγ, i, j, rfl | rfl⟩ τ
    · exact unitary_norm_le_one E n γ τ i j
    · exact unitary_norm_le_one E n γ⁻¹ τ i j
  have hX := finite_of_local_bounds E X hall hcof hinf
  have hM : (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => X).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hX
  refine (hM.preimage (f := fun γ : UE E n => (γ.1.val : Fin n → Fin n → E)) ?_).subset ?_
  · intro a _ b _ h
    exact Subtype.ext (Units.ext h)
  · intro γ hγ i _ j _
    exact ⟨γ, hγ, i, j, Or.inl rfl⟩

end GlobalTheory.BCT.SuppFin

open GlobalTheory.BCT.SuppFin in

/- English proof (translation)
Introduce `E _ _ _ hU n hn S hS K' hK' f hf x`. Use `set Γs : Set (UE E n) := {γ | globFn S f (x⁻¹ * finPt γ * x) ≠ 0} with hΓs`. Establish `hUL : ∀ (w : Pl E) (z : UA E n), cLoc w z ∈ UL n w` using `fun w z => cLoc_mem_UL E hU n w z`. Establish `hnz : ∀ γ ∈ Γs, ∀ w ∈ S, f w (toSub _ (cLoc w (x⁻¹ * finPt γ * x).1)) ≠ 0` using `fun γ hγ w hw => factor_ne_zero E n S K' f hf (x⁻¹ * finPt γ * x) (cLoc_eventually_KGL E n _) hγ w hw`. Establish `hpt : ∀ (w : Pl E) (γ : UE E n), GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 = cLoc w x.1 * cLoc w (x⁻¹ * finPt γ * x).1 * (cLoc w x.1)⁻¹`.

Introduce `w γ`. Rewrite using `[← cLoc_finPt E n w γ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]`. Use `group`. Establish `hv : ∀ (w : Pl E) (a : E), Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a` using `fun w a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a`. Establish `hent : ∀ (w : Pl E) (γ : UE E n) (i j : Fin n), (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val i j = algebraMap E _ (γ.1.val i j) ∧ ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)⁻¹).val i j = algebraMap E _ ((γ.1⁻¹).val i j)`.

Introduce `w γ i j`. Rewrite using `[← map_inv]`. Conclude with `⟨rfl, rfl⟩`. Use `finite_of_bounds S hS Γs ?_ ?_` and prove the remaining obligations. Introduce `w hw set c := cLoc w x.1 with hcdef set D : Set (GL (Fin n) (w.adicCompletion E)) := (fun h => c * h * c⁻¹) '' ((UL n w).subtype '' tsupport (f w)) with hDdef`.

Establish `hD : IsCompact D` using `(((hf.1 w).1.image continuous_subtype_val).image ((continuous_const.mul continuous_id).mul continuous_const))`. Take `⟨N, hN⟩` from `compact_val_bounded E w n D hD`. Use `⟨N, fun γ hγ i j => ?_⟩` and prove the remaining obligations. Establish `hmem : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ D`. Rewrite using `[hpt]`.

Use `⟨_, ⟨⟨_, hUL w _⟩, subset_tsupport _ ?_, rfl⟩, rfl⟩` and prove the remaining obligations. Establish `h0` using `hnz γ hγ w hw`. Rewrite `h0` using `[toSub, dif_pos (hUL w _)]`. Then use the resulting hypothesis. Take `⟨h1, h2⟩` from `hN _ hmem i j`. Rewrite `h1` using `[(hent w γ i j).1, hv]`.

Rewrite `h2` using `[(hent w γ i j).2, hv]`. Conclude with `⟨h1, h2⟩`. Use `filter_upwards [hf.2, cLoc_eventually_KGL E n x.1] with w hfw hxw hw γ hγ i j`. Establish `h0` using `hnz γ hγ w hw`. Rewrite `h0` using `[hfw, toSub, dif_pos (hUL w _)]`.

Establish `hy : cLoc w (x⁻¹ * finPt γ * x).1 ∈ GlobalTheory.LFun.KGL w n` using `Subgroup.mem_subgroupOf.1 (Set.indicator_apply_ne_zero.1 h0).1`. Establish `hg : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ GlobalTheory.LFun.KGL w n`. Rewrite using `[hpt]`. Conclude with `mul_mem (mul_mem hxw hy) (inv_mem hxw)`. Establish `h1` using `val_le_one_of_KGL hg i j`.

Establish `h2` using `val_le_one_of_KGL (inv_mem hg) i j`. Rewrite `h1` using `[(hent w γ i j).1, hv]`. Rewrite `h2` using `[(hent w γ i j).2, hv]`. Conclude with `⟨h1, h2⟩`.
-/
theorem GlobalTheory.BCT.SuppFin.suppFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU E n, {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite := by
  intro E _ _ _ hU n hn S hS K' hK' f hf x
  classical
  set Γs : Set (UE E n) := {γ | globFn S f (x⁻¹ * finPt γ * x) ≠ 0} with hΓs
  have hUL : ∀ (w : Pl E) (z : UA E n), cLoc w z ∈ UL n w := fun w z => cLoc_mem_UL E hU n w z
  have hnz : ∀ γ ∈ Γs, ∀ w ∈ S, f w (toSub _ (cLoc w (x⁻¹ * finPt γ * x).1)) ≠ 0 :=
    fun γ hγ w hw => factor_ne_zero E n S K' f hf (x⁻¹ * finPt γ * x) (cLoc_eventually_KGL E n _) hγ w hw
  have hpt : ∀ (w : Pl E) (γ : UE E n), GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 =
      cLoc w x.1 * cLoc w (x⁻¹ * finPt γ * x).1 * (cLoc w x.1)⁻¹ := by
    intro w γ
    rw [← cLoc_finPt E n w γ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    group
  have hv : ∀ (w : Pl E) (a : E), Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
    fun w a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
  have hent : ∀ (w : Pl E) (γ : UE E n) (i j : Fin n),
      (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val i j = algebraMap E _ (γ.1.val i j) ∧
      ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)⁻¹).val i j =
        algebraMap E _ ((γ.1⁻¹).val i j) := by
    intro w γ i j
    rw [← map_inv]
    exact ⟨rfl, rfl⟩
  refine finite_of_bounds S hS Γs ?_ ?_
  · intro w hw
    set c := cLoc w x.1 with hcdef
    set D : Set (GL (Fin n) (w.adicCompletion E)) :=
      (fun h => c * h * c⁻¹) '' ((UL n w).subtype '' tsupport (f w)) with hDdef
    have hD : IsCompact D :=
      (((hf.1 w).1.image continuous_subtype_val).image ((continuous_const.mul continuous_id).mul continuous_const))
    obtain ⟨N, hN⟩ := compact_val_bounded E w n D hD
    refine ⟨N, fun γ hγ i j => ?_⟩
    have hmem : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ D := by
      rw [hpt]
      refine ⟨_, ⟨⟨_, hUL w _⟩, subset_tsupport _ ?_, rfl⟩, rfl⟩
      have h0 := hnz γ hγ w hw
      rwa [toSub, dif_pos (hUL w _)] at h0
    obtain ⟨h1, h2⟩ := hN _ hmem i j
    rw [(hent w γ i j).1, hv] at h1
    rw [(hent w γ i j).2, hv] at h2
    exact ⟨h1, h2⟩
  · filter_upwards [hf.2, cLoc_eventually_KGL E n x.1] with w hfw hxw hw γ hγ i j
    have h0 := hnz γ hγ w hw
    rw [hfw, toSub, dif_pos (hUL w _)] at h0
    have hy : cLoc w (x⁻¹ * finPt γ * x).1 ∈ GlobalTheory.LFun.KGL w n :=
      Subgroup.mem_subgroupOf.1 (Set.indicator_apply_ne_zero.1 h0).1
    have hg : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ GlobalTheory.LFun.KGL w n := by
      rw [hpt]
      exact mul_mem (mul_mem hxw hy) (inv_mem hxw)
    have h1 := val_le_one_of_KGL hg i j
    have h2 := val_le_one_of_KGL (inv_mem hg) i j
    rw [(hent w γ i j).1, hv] at h1
    rw [(hent w γ i j).2, hv] at h2
    exact ⟨h1, h2⟩
