import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SplitIso

section Generic

variable {A B : Type} [CommRing A] [CommRing B]

def pairM {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin n) (Fin n) B) :
    Matrix (Fin n) (Fin n) (A × B) :=
  Matrix.of fun i j => (M i j, N i j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[pairM, Matrix.mul_apply, Prod.fst_sum]`. Simplify using `[pairM, Matrix.mul_apply, Prod.snd_sum]`.
-/
theorem pairM_mul {n : ℕ} (M M' : Matrix (Fin n) (Fin n) A) (N N' : Matrix (Fin n) (Fin n) B) :
    pairM M N * pairM M' N' = pairM (M * M') (N * N') := by
  ext i j
  · simp [pairM, Matrix.mul_apply, Prod.fst_sum]
  · simp [pairM, Matrix.mul_apply, Prod.snd_sum]

/- English proof (translation)
Apply the tactic sequence `ext i j <;> by_cases h : i = j <;> simp [pairM, h, Matrix.one_apply]`.
-/
theorem pairM_one {n : ℕ} : pairM (1 : Matrix (Fin n) (Fin n) A) (1 : Matrix (Fin n) (Fin n) B) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [pairM, h, Matrix.one_apply]

def glProd [TopologicalSpace A] [TopologicalSpace B] (n : ℕ) :
    GL (Fin n) (A × B) ≃ₜ* GL (Fin n) A × GL (Fin n) B where
  toFun g := (GeneralLinearGroup.map (RingHom.fst A B) g, GeneralLinearGroup.map (RingHom.snd A B) g)
  invFun p := ⟨pairM p.1.val p.2.val, pairM (p.1⁻¹).val (p.2⁻¹).val,
    by rw [pairM_mul, Units.mul_inv, Units.mul_inv, pairM_one],
    by rw [pairM_mul, Units.inv_mul, Units.inv_mul, pairM_one]⟩
  left_inv g := by
    apply Units.ext
    ext i j <;> rfl
  right_inv p := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_) <;> ext i j <;> rfl
  map_mul' x y := Prod.ext (map_mul _ x y) (map_mul _ x y)
  continuous_toFun :=
    (Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map continuous_fst,
      Units.continuous_coe_inv.matrix_map continuous_fst⟩).prodMk
    (Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map continuous_snd,
      Units.continuous_coe_inv.matrix_map continuous_snd⟩)
  continuous_invFun := by
    refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
    · exact ((Units.continuous_val.matrix_elem i j).comp continuous_fst).prodMk
        ((Units.continuous_val.matrix_elem i j).comp continuous_snd)
    · exact ((Units.continuous_coe_inv.matrix_elem i j).comp continuous_fst).prodMk
        ((Units.continuous_coe_inv.matrix_elem i j).comp continuous_snd)

/- English proof (translation)
Establish `h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T), thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹` using `fun _ _ _ _ => rfl`. Establish `h4 : GeneralLinearGroup.map (RingHom.id S) (GeneralLinearGroup.map (f.comp c) g) = GeneralLinearGroup.map f (GeneralLinearGroup.map c g)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[h3, h3, map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.RegroupFin.map_phiU, GlobalTheory.SplitPts.invT_map, h4]`.
-/
theorem map_thetaGL_comp {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (n : ℕ)
    (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) =
      thetaGL n (RingHom.id S) (GeneralLinearGroup.map (f.comp c) g) := by
  have h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T),
      thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹ := fun _ _ _ _ => rfl
  have h4 : GeneralLinearGroup.map (RingHom.id S) (GeneralLinearGroup.map (f.comp c) g) =
      GeneralLinearGroup.map f (GeneralLinearGroup.map c g) := by
    apply Units.ext
    ext i j
    rfl
  rw [h3, h3, map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.RegroupFin.map_phiU, GlobalTheory.SplitPts.invT_map, h4]

end Generic

section Place

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CjEx GlobalTheory.CompanionTheory.EulerV

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) (conjSrc (conjE E) w)).equalizer ((psi_spec w).1.comp (conjLoc_spec (conjE E) w).1) continuous_id (funext fun k => ?_)) z` and prove the remaining obligations. Simplify using `only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]`. Conclude with `congrArg _ (IsCMField.complexConj_apply_apply E k)`.
-/
theorem psi_conjLoc (w : Pl E) (z : (conjSrc (conjE E) w).adicCompletion E) :
    psi w (conjLoc (conjE E) w z) = z := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) (conjSrc (conjE E) w)).equalizer
    ((psi_spec w).1.comp (conjLoc_spec (conjE E) w).1) continuous_id (funext fun k => ?_)) z
  simp only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

variable {v : PlF E}

/- English proof (translation)
Introduce `h` and use `(over_split hs).1 (congrArg Subtype.val h)`.
-/
theorem conjAbove_ne {w : Above v} (hs : IsSplitAt w.1) : conjAbove w ≠ w := fun h =>
  (over_split hs).1 (congrArg Subtype.val h)

/- English proof (translation)
The claim follows from `((over_split hs).2.2 u.1 (u.2.trans w.2.symm)).imp Subtype.ext Subtype.ext`.
-/
theorem above_cases {w : Above v} (hs : IsSplitAt w.1) (u : Above v) : u = w ∨ u = conjAbove w :=
  ((over_split hs).2.2 u.1 (u.2.trans w.2.symm)).imp Subtype.ext Subtype.ext

def sg (u : Above v) (x : u.1.adicCompletion E) : Av v := Pi.single u x

/- English proof (translation)
Simplify using `[sg]`.
-/
theorem sg_same (u : Above v) (x : u.1.adicCompletion E) : sg u x u = x := by simp [sg]

/- English proof (translation)
Simplify using `[sg, h]`.
-/
theorem sg_ne {t u : Above v} (h : t ≠ u) (x : u.1.adicCompletion E) : sg u x t = 0 := by simp [sg, h]

/- English proof (translation)
The claim follows from `continuous_single (A := fun t : Above v => t.1.adicCompletion E) u`.
-/
theorem continuous_sg (u : Above v) : Continuous (sg u) :=
  continuous_single (A := fun t : Above v => t.1.adicCompletion E) u

def sA (w : Above v) : (conjAbove w).1.adicCompletion E →+* w.1.adicCompletion E := conjLoc (conjE E) w.1

def psiA (w : Above v) : w.1.adicCompletion E →+* (conjAbove w).1.adicCompletion E := psi w.1

/- English proof (translation)
The claim follows from `conjLoc_psi w.1 x`.
-/
theorem sA_psiA (w : Above v) (x : w.1.adicCompletion E) : sA w (psiA w x) = x := conjLoc_psi w.1 x

/- English proof (translation)
The claim follows from `psi_conjLoc w.1 z`.
-/
theorem psiA_sA (w : Above v) (z : (conjAbove w).1.adicCompletion E) : psiA w (sA w z) = z := psi_conjLoc w.1 z

/- English proof (translation)
The claim follows from `(conjLoc_spec (conjE E) w.1).1`.
-/
theorem continuous_sA (w : Above v) : Continuous (sA w) := (conjLoc_spec (conjE E) w.1).1

/- English proof (translation)
The claim follows from `(psi_spec w.1).1`.
-/
theorem continuous_psiA (w : Above v) : Continuous (psiA w) := (psi_spec w.1).1

def ringE (w : Above v) (hs : IsSplitAt w.1) :
    Av v ≃+* w.1.adicCompletion E × w.1.adicCompletion E where
  toFun a := (a w, sA w (a (conjAbove w)))
  invFun p := sg w p.1 + sg (conjAbove w) (psiA w p.2)
  left_inv a := by
    funext u
    rcases above_cases hs u with rfl | rfl
    · show sg u (a u) u + sg (conjAbove u) (psiA u (sA u (a (conjAbove u)))) u = a u
      rw [sg_same, sg_ne (conjAbove_ne hs).symm, add_zero]
    · show sg w (a w) (conjAbove w) + sg (conjAbove w) (psiA w (sA w (a (conjAbove w)))) (conjAbove w) =
        a (conjAbove w)
      rw [sg_ne (conjAbove_ne hs), sg_same, zero_add]
      exact psiA_sA _ _
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show sg w p.1 w + sg (conjAbove w) (psiA w p.2) w = p.1
      rw [sg_same, sg_ne (conjAbove_ne hs).symm, add_zero]
    · show sA w (sg w p.1 (conjAbove w) + sg (conjAbove w) (psiA w p.2) (conjAbove w)) = p.2
      rw [sg_ne (conjAbove_ne hs), sg_same, zero_add]
      exact sA_psiA _ _
  map_mul' x y := Prod.ext rfl (map_mul (sA w) _ _)
  map_add' x y := Prod.ext rfl (map_add (sA w) _ _)

/- English proof (translation)
The claim follows from `(continuous_apply w).prodMk ((continuous_sA w).comp (continuous_apply (conjAbove w)))`.
-/
theorem continuous_ringE (w : Above v) (hs : IsSplitAt w.1) : Continuous (ringE w hs) :=
  (continuous_apply w).prodMk ((continuous_sA w).comp (continuous_apply (conjAbove w)))

/- English proof (translation)
Use `show Continuous fun p : w.1.adicCompletion E × w.1.adicCompletion E => sg w p.1 + sg (conjAbove w) (psiA w p.2)`. Conclude with `((continuous_sg w).comp continuous_fst).add ((continuous_sg (conjAbove w)).comp ((continuous_psiA w).comp continuous_snd))`.
-/
theorem continuous_ringE_symm (w : Above v) (hs : IsSplitAt w.1) : Continuous (ringE w hs).symm := by
  show Continuous fun p : w.1.adicCompletion E × w.1.adicCompletion E =>
    sg w p.1 + sg (conjAbove w) (psiA w p.2)
  exact ((continuous_sg w).comp continuous_fst).add
    ((continuous_sg (conjAbove w)).comp ((continuous_psiA w).comp continuous_snd))

def evb (w : Above v) : Av v →+* w.1.adicCompletion E :=
  (sA w).comp (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

def glSplit (n : ℕ) (w : Above v) (hs : IsSplitAt w.1) : GL (Fin n) (Av v) ≃ₜ* GLw n w.1 × GLw n w.1 :=
  (GlobalTheory.CompanionTheory.LocInert.glEquiv (ringE w hs) (continuous_ringE w hs) (continuous_ringE_symm w hs) n).trans (glProd n)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem glSplit_fst (n : ℕ) (w : Above v) (hs : IsSplitAt w.1) (g : GL (Fin n) (Av v)) :
    (glSplit n w hs g).1 = ev w g := by
  apply Units.ext
  ext i j
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem glSplit_snd (n : ℕ) (w : Above v) (hs : IsSplitAt w.1) (g : GL (Fin n) (Av v)) :
    (glSplit n w hs g).2 = GeneralLinearGroup.map (evb w) g := by
  apply Units.ext
  ext i j
  rfl

def splitE (a b : ℕ) (w : Above v) (hs : IsSplitAt w.1) :
    Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)) where
  toMulEquiv := (MulEquiv.prodCongr (glSplit a w hs).toMulEquiv (glSplit b w hs).toMulEquiv).trans
    (MulEquiv.prodProdProdComm _ _ _ _)
  continuous_toFun := (Homeomorph.prodProdProdComm _ _ _ _).continuous.comp
    ((glSplit a w hs).continuous.prodMap (glSplit b w hs).continuous)
  continuous_invFun := ((glSplit a w hs).symm.continuous.prodMap (glSplit b w hs).symm.continuous).comp
    (Homeomorph.prodProdProdComm _ _ _ _).symm.continuous

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitE_apply (a b : ℕ) (w : Above v) (hs : IsSplitAt w.1) (y : Yv a b v) :
    splitE a b w hs y = (((glSplit a w hs y.1).1, (glSplit b w hs y.2).1),
      ((glSplit a w hs y.1).2, (glSplit b w hs y.2).2)) := rfl

/- English proof (translation)
Use `⟨sLoc E w.1 (x w) + sLoc E (conjAbove w).1 (x (conjAbove w)), ?_⟩` and prove the remaining obligations. Establish `hl : ∀ (u t : Above v) (z : u.1.adicCompletion E), pLoc E t.1 (sLoc E u.1 z) = sg u z t`. Introduce `u t z`. Break down `eq_or_ne t u with rfl | h` into its components or cases. Rewrite using `[sg_same]`.

Express the relevant statement in the definitionally equal form `(Pi.single t.1 z : ∀ r : Pl E, r.adicCompletion E) t.1 = _`. Simplify using the standard rewrite rules. Rewrite using `[sg_ne h]`. Express the relevant statement in the definitionally equal form `(Pi.single u.1 z : ∀ r : Pl E, r.adicCompletion E) t.1 = _`. Conclude with `Pi.single_eq_of_ne (fun e => h (Subtype.ext e)) z`.

Use function extensionality and compare the values at `u`. Use `show pLoc E u.1 (sLoc E w.1 (x w) + sLoc E (conjAbove w).1 (x (conjAbove w))) = x u`. Rewrite using `[map_add, hl, hl]`. Break down `above_cases hs u with rfl | rfl` into its components or cases. Rewrite using `[sg_same, sg_ne (conjAbove_ne hs).symm, add_zero]`.

Rewrite using `[sg_ne (conjAbove_ne hs), sg_same, zero_add]`.
-/
theorem exists_projv {w : Above v} (hs : IsSplitAt w.1) (x : Av v) : ∃ X : Af E, projv v X = x := by
  refine ⟨sLoc E w.1 (x w) + sLoc E (conjAbove w).1 (x (conjAbove w)), ?_⟩
  have hl : ∀ (u t : Above v) (z : u.1.adicCompletion E), pLoc E t.1 (sLoc E u.1 z) = sg u z t := by
    intro u t z
    rcases eq_or_ne t u with rfl | h
    · rw [sg_same]
      change (Pi.single t.1 z : ∀ r : Pl E, r.adicCompletion E) t.1 = _
      simp
    · rw [sg_ne h]
      change (Pi.single u.1 z : ∀ r : Pl E, r.adicCompletion E) t.1 = _
      exact Pi.single_eq_of_ne (fun e => h (Subtype.ext e)) z
  funext u
  show pLoc E u.1 (sLoc E w.1 (x w) + sLoc E (conjAbove w).1 (x (conjAbove w))) = x u
  rw [map_add, hl, hl]
  rcases above_cases hs u with rfl | rfl
  · rw [sg_same, sg_ne (conjAbove_ne hs).symm, add_zero]
  · rw [sg_ne (conjAbove_ne hs), sg_same, zero_add]

/- English proof (translation)
Take `⟨X, rfl⟩` from `exists_projv hs x`. Rewrite using `[← GlobalTheory.CompanionTheory.RegroupFin.cjv_spec hC v X]`. Conclude with `pLoc_conjFin _ _ _`.
-/
theorem cjv_at (hC : CjEx) {w : Above v} (hs : IsSplitAt w.1) (x : Av v) :
    cjv v x w = sA w (x (conjAbove w)) := by
  obtain ⟨X, rfl⟩ := exists_projv hs x
  rw [← GlobalTheory.CompanionTheory.RegroupFin.cjv_spec hC v X]
  exact pLoc_conjFin _ _ _

/- English proof (translation)
Take `⟨X, rfl⟩` from `exists_projv hs x`. Rewrite using `[← GlobalTheory.CompanionTheory.RegroupFin.cjv_spec hC v X]`. Conclude with `(pLoc_conjFin (conjE E) X (conjSrc (conjE E) w.1)).trans (conjLoc_pLoc w.1 X)`.
-/
theorem cjv_at_conj (hC : CjEx) {w : Above v} (hs : IsSplitAt w.1) (x : Av v) :
    cjv v x (conjAbove w) = psiA w (x w) := by
  obtain ⟨X, rfl⟩ := exists_projv hs x
  rw [← GlobalTheory.CompanionTheory.RegroupFin.cjv_spec hC v X]
  exact (pLoc_conjFin (conjE E) X (conjSrc (conjE E) w.1)).trans (conjLoc_pLoc w.1 X)

/- English proof (translation)
The claim follows from `RingHom.ext fun x => cjv_at hC hs x`.
-/
theorem eval_comp_cjv (hC : CjEx) {w : Above v} (hs : IsSplitAt w.1) :
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) w).comp (cjv v) = evb w :=
  RingHom.ext fun x => cjv_at hC hs x

/- English proof (translation)
The claim follows from `RingHom.ext fun x => by show sA w (cjv v x (conjAbove w)) = x w rw [cjv_at_conj hC hs] exact sA_psiA _ _`.
-/
theorem evb_comp_cjv (hC : CjEx) {w : Above v} (hs : IsSplitAt w.1) :
    (evb w).comp (cjv v) = Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) w :=
  RingHom.ext fun x => by
    show sA w (cjv v x (conjAbove w)) = x w
    rw [cjv_at_conj hC hs]
    exact sA_psiA _ _

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (glSplit n w hs (thetaGL n (cjv v) g)).1 = thetaGL n (RingHom.id _) (glSplit n w hs g).2`. Rewrite using `[glSplit_fst, glSplit_snd, ev, map_thetaGL_comp, eval_comp_cjv hC hs]`. Use `show (glSplit n w hs (thetaGL n (cjv v) g)).2 = thetaGL n (RingHom.id _) (glSplit n w hs g).1`. Rewrite using `[glSplit_fst, glSplit_snd, ev, map_thetaGL_comp, evb_comp_cjv hC hs]`.
-/
theorem glSplit_theta (hC : CjEx) (n : ℕ) {w : Above v} (hs : IsSplitAt w.1) (g : GL (Fin n) (Av v)) :
    glSplit n w hs (thetaGL n (cjv v) g) =
      (thetaGL n (RingHom.id _) (glSplit n w hs g).2, thetaGL n (RingHom.id _) (glSplit n w hs g).1) := by
  refine Prod.ext ?_ ?_
  · show (glSplit n w hs (thetaGL n (cjv v) g)).1 = thetaGL n (RingHom.id _) (glSplit n w hs g).2
    rw [glSplit_fst, glSplit_snd, ev, map_thetaGL_comp, eval_comp_cjv hC hs]
  · show (glSplit n w hs (thetaGL n (cjv v) g)).2 = thetaGL n (RingHom.id _) (glSplit n w hs g).1
    rw [glSplit_fst, glSplit_snd, ev, map_thetaGL_comp, evb_comp_cjv hC hs]

/- English proof (translation)
Establish `e1 : ∀ (h : GLw n (conjSrc (conjE E) w)) (i j : Fin n), Valued.v ((GeneralLinearGroup.map (conjLoc (conjE E) w) h).val i j) = Valued.v (h.val i j)` using `fun h i j => (conjLoc_spec (conjE E) w).2.2 _`. Rewrite using `[GlobalTheory.EulerTwKU.mem_KGL_iff_val, GlobalTheory.EulerTwKU.mem_KGL_iff_val, ← map_inv]`. Simplify using `only [e1]`.
-/
theorem map_conjLoc_mem {n : ℕ} (w : Pl E) (g : GLw n (conjSrc (conjE E) w)) :
    GeneralLinearGroup.map (conjLoc (conjE E) w) g ∈ GlobalTheory.LFun.KGL w n ↔
      g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) w) n := by
  have e1 : ∀ (h : GLw n (conjSrc (conjE E) w)) (i j : Fin n),
      Valued.v ((GeneralLinearGroup.map (conjLoc (conjE E) w) h).val i j) = Valued.v (h.val i j) :=
    fun h i j => (conjLoc_spec (conjE E) w).2.2 _
  rw [GlobalTheory.EulerTwKU.mem_KGL_iff_val, GlobalTheory.EulerTwKU.mem_KGL_iff_val, ← map_inv]
  simp only [e1]

/- English proof (translation)
The claim follows from `map_conjLoc_mem w.1 g`.
-/
theorem map_sA_mem {n : ℕ} (w : Above v) (g : GLw n (conjAbove w).1) :
    GeneralLinearGroup.map (sA w) g ∈ GlobalTheory.LFun.KGL w.1 n ↔ g ∈ GlobalTheory.LFun.KGL (conjAbove w).1 n :=
  map_conjLoc_mem w.1 g

/- English proof (translation)
Establish `e : (glSplit n w hs g).2 = GeneralLinearGroup.map (sA w) (ev (conjAbove w) g)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[mem_Kn, e, map_sA_mem, glSplit_fst]`.

Use `⟨fun h => ⟨h w, h (conjAbove w)⟩, fun h u => ?_⟩` and prove the remaining obligations. Break down `above_cases hs u with rfl | rfl` into its components or cases. Conclude with `h.1`. Conclude with `h.2`.
-/
theorem mem_Kn_iff {n : ℕ} {w : Above v} (hs : IsSplitAt w.1) (g : GL (Fin n) (Av v)) :
    g ∈ Kn n v ↔ (glSplit n w hs g).1 ∈ GlobalTheory.LFun.KGL w.1 n ∧ (glSplit n w hs g).2 ∈ GlobalTheory.LFun.KGL w.1 n := by
  have e : (glSplit n w hs g).2 = GeneralLinearGroup.map (sA w) (ev (conjAbove w) g) := by
    apply Units.ext
    ext i j
    rfl
  rw [mem_Kn, e, map_sA_mem, glSplit_fst]
  refine ⟨fun h => ⟨h w, h (conjAbove w)⟩, fun h u => ?_⟩
  rcases above_cases hs u with rfl | rfl
  · exact h.1
  · exact h.2

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Conclude with `(conjLoc_spec (conjE E) w.1).2.1 _`.
-/
theorem glSplit_rat (n : ℕ) {w : Above v} (hs : IsSplitAt w.1) (δ : GL (Fin n) E) :
    glSplit n w hs (GeneralLinearGroup.map (projv v) (ratF E n δ)) =
      (ratW n w.1 δ, ratW n w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) := by
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext i j
    rfl
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact (conjLoc_spec (conjE E) w.1).2.1 _

end Place

/- English proof (translation)
Introduce `hC E _ _ _ a b v w hs`. Use `⟨GlobalTheory.CompanionTheory.SplitIso.splitE a b w hs, fun y => ?_, fun y => ?_, fun y => ?_, fun δ₁ δ₂ => ?_⟩` and prove the remaining obligations. Rewrite using `[splitE_apply, glSplit_fst, glSplit_fst]`. Both sides reduce to the same expression. Establish `h1 : (thv a b v y).1 = thetaGL a (cjv v) y.1` using `rfl`.

Establish `h2 : (thv a b v y).2 = thetaGL b (cjv v) y.2` using `rfl`. Rewrite using `[splitE_apply, splitE_apply, h1, h2, glSplit_theta hC, glSplit_theta hC]`. Both sides reduce to the same expression. Rewrite using `[GlobalTheory.CompanionTheory.EulerV.mem_Kv, mem_Kn_iff hs, mem_Kn_iff hs, splitE_apply]`. Simplify using `only [Subgroup.mem_prod]`.

The claim follows by propositional logic. Establish `h1 : (pv a b v (ratF E a δ₁, ratF E b δ₂)).1 = GeneralLinearGroup.map (projv v) (ratF E a δ₁)` using `rfl`. Establish `h2 : (pv a b v (ratF E a δ₁, ratF E b δ₂)).2 = GeneralLinearGroup.map (projv v) (ratF E b δ₂)` using `rfl`. Rewrite using `[splitE_apply, h1, h2, glSplit_rat, glSplit_rat]`.
-/
theorem split_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)), (∀ y, (e y).1 = evw w y) ∧
    (∀ y, e (thv a b v y) = swTw (sgP a b w.1) (e y)) ∧ (∀ y, y ∈ Kv a b v ↔ e y ∈ (K2 a b w.1).prod (K2 a b w.1)) ∧
    ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), e (pv a b v (ratF E a δ₁, ratF E b δ₂)) =
      ((ratW a w.1 δ₁, ratW b w.1 δ₂),
        (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
         ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂))) := by
  intro hC E _ _ _ a b v w hs
  refine ⟨GlobalTheory.CompanionTheory.SplitIso.splitE a b w hs, fun y => ?_, fun y => ?_, fun y => ?_, fun δ₁ δ₂ => ?_⟩
  · rw [splitE_apply, glSplit_fst, glSplit_fst]
    rfl
  · have h1 : (thv a b v y).1 = thetaGL a (cjv v) y.1 := rfl
    have h2 : (thv a b v y).2 = thetaGL b (cjv v) y.2 := rfl
    rw [splitE_apply, splitE_apply, h1, h2, glSplit_theta hC, glSplit_theta hC]
    rfl
  · rw [GlobalTheory.CompanionTheory.EulerV.mem_Kv, mem_Kn_iff hs, mem_Kn_iff hs, splitE_apply]
    simp only [Subgroup.mem_prod]
    tauto
  · have h1 : (pv a b v (ratF E a δ₁, ratF E b δ₂)).1 = GeneralLinearGroup.map (projv v) (ratF E a δ₁) := rfl
    have h2 : (pv a b v (ratF E a δ₁, ratF E b δ₂)).2 = GeneralLinearGroup.map (projv v) (ratF E b δ₂) := rfl
    rw [splitE_apply, h1, h2, glSplit_rat, glSplit_rat]

end GlobalTheory.CompanionTheory.SplitIso

end
