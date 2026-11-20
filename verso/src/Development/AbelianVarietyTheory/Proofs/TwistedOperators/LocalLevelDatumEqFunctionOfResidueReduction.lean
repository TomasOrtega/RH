import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

variable {D : D7}

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `h1` using `Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx`. Establish `h2 : r x = 0` using `(hr.2.1 x).2 h1`. Rewrite `h` using `[h2]`. Conclude with `not_isUnit_zero h`.
-/
theorem isUnit_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    {x : v.adicCompletionIntegers D.host.F} (h : IsUnit (r x)) : IsUnit x := by
  by_contra hx
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx
  have h2 : r x = 0 := (hr.2.1 x).2 h1
  rw [h2] at h
  exact not_isUnit_zero h

/- English proof (translation)
The claim follows from `(hr.2.2.1 _ _).2 ⟨x.2, rfl⟩`.
-/
theorem redRel_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    (x : v.adicCompletionIntegers D.host.F) : RedRel φ PP (x : Fv D.host.F v) (r x) :=
  (hr.2.2.1 _ _).2 ⟨x.2, rfl⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D v φ PP r hr a b t ht L H c J lam hJ mu χ hmu Y`. Establish `hinl : ∀ (i : Fin a) (j : Fin a), rowsTB ht Y (Sum.inl i) j = Y ⟨i.val, by omega⟩ j` using `fun _ _ => rfl`. Establish `hinr : ∀ (i : Fin t) (j : Fin a), rowsTB ht Y (Sum.inr i) j = Y ⟨a + i.val, by omega⟩ j` using `fun _ _ => rfl`. Unfold `viaRed`. Distinguish the cases in `hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F`.

Use `swap`. Rewrite using `[dif_neg hint]`. Unfold `localNewformFunction`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨⟨k, hk⟩, hbot⟩`.

Apply `hint` to reduce the goal to its premises. Introduce `i j`. Distinguish the cases in `hi : i.val < a`. Establish `h1` using `congrFun (congrFun hk ⟨i.val, hi⟩) j`. Rewrite `h1` using `[Matrix.submatrix_apply, hinl]`.

Simplify using `only [Matrix.map_apply, id] at h1`. Rewrite using `[show i = ⟨i.val, by omega⟩ from rfl, ← h1]`. Conclude with `((k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)) ⟨i.val, hi⟩ j |>.2`. Establish `h1` using `(hbot ⟨i.val - a, by omega⟩ j).1`. Rewrite `h1` using `[hinr]`.

Establish `: (⟨a + (i.val - a), by omega⟩ : Fin b) = i` using `Fin.ext (by simp; omega)`. Rewrite `h1` using `[this]`. Then use the resulting hypothesis. Rewrite using `[dif_pos hint]`. Use `set y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) := Matrix.of fun i j => r ⟨Y i j, hint i j⟩ with hy`. Set `K : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)` to `fun i j => ⟨Y ⟨i.val, by omega⟩ j, hint _ _⟩`.

Establish `hKr : K.map r = topL a y`. Use extensionality with `i j`. Simplify using `only [topL, Matrix.map_apply]`. Rewrite using `[dif_pos ⟨by omega, j.2⟩]`. Both sides reduce to the same expression.

Establish `hKk : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F), ((k : Matrix (Fin a) (Fin a) _).map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) = (rowsTB ht Y).submatrix Sum.inl id) → (k : Matrix (Fin a) (Fin a) _) = K`. Introduce `k hk`. Use function extensionality and compare the values at `i j`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `congrFun (congrFun hk i) j`.

Rewrite `h1` using `[Matrix.submatrix_apply, hinl]`. Conclude with `h1`. Establish `hred : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F), (k : Matrix (Fin a) (Fin a) _) = K → ((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) = topL a y ∧ ∀ i j, RedRel φ PP (((k : Matrix (Fin a) (Fin a) _) i j : v.adicCo …`. Introduce `k hk`. Use `⟨?_, fun i j => redRel_of_isRedMap hr _⟩` and prove the remaining obligations.

Rewrite using `[← hKr, ← hk]`. Both sides reduce to the same expression. Unfold `gLoc localNewformFunction`. Use `split_ifs with hP hG hG`. Establish `hk0` using `hP.1.choose_spec`.

Establish `hg0` using `hG.2.choose_spec`. Generalize the expression as in `hP.1.choose = k₀ at hk0 ⊢`. Take `⟨k, hkJ⟩` from `k₀`. Establish `hK` using `hKk k hk0`. Take `⟨hm, hrr⟩` from `hred k hK`.

Establish `hkg : Matrix.GeneralLinearGroup.map r k = hG.2.choose` using `Units.ext (hm.trans hg0.1.symm)`. Establish `hlam` using `(hJ _ _ hrr).2 hkJ`. Rewrite `hlam` using `[hkg, Formalism.L2.DIV.extendOne_of_mem _ hg0.2.2]`. Establish `hdet : RedRel φ PP ((Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom (Matrix.GeneralLinearGroup.det k) : (Fv D.host.F v)ˣ) : Fv D.host.F v) ((Matrix.GeneralLinearGroup.det hG.2.choose : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP)`. Establish `e2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map r k) : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) = r ((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers D.host.F)ˣ) : v.adicCompletionIntegers D.host.F)`.

Conclude with `(RingHom.map_det r (k : Matrix (Fin a) (Fin a) _)).symm`. Rewrite using `[← hkg, e2]`. Conclude with `redRel_of_isRedMap hr _`. Rewrite using `[hlam, hmu _ _ hdet]`. Use `push_cast`.

Both sides reduce to the same expression. It suffices to derive a contradiction. Apply `hG` to reduce the goal to its premises. Take `⟨⟨⟨k, hkJ⟩, hk⟩, hbot⟩` from `hP`. Establish `hK` using `hKk k hk`.

Take `⟨hm, hrr⟩` from `hred k hK`. Establish `hJk` using `((hJ k _ hrr).1.1 hkJ)`. Use `⟨?_, Matrix.GeneralLinearGroup.map r k, hm, hJk⟩` and prove the remaining obligations. Introduce `i j hi hj`. Establish `h1` using `hbot ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩`.

Rewrite `h1` using `[hinr]`. Establish `: (⟨a + (i.val - a), by omega⟩ : Fin b) = i` using `Fin.ext (by simp; omega)`. Rewrite `h1` using `[this]`. Conclude with `(hr.2.1 ⟨Y i ⟨j.val, hj⟩, hint _ _⟩).2 h1.2`. It suffices to derive a contradiction.

Apply `hP` to reduce the goal to its premises. Take `⟨hlow, g, hg, hgT, hgH⟩` from `hG`. Establish `hdet : IsUnit K.det`. Apply `isUnit_of_isRedMap hr` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hKr, ← hg]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit`. Set `k : GL (Fin a) (v.adicCompletionIntegers D.host.F)` to `((Matrix.isUnit_iff_isUnit_det K).2 hdet).unit`. Establish `hkK : (k : Matrix (Fin a) (Fin a) _) = K` using `rfl`. Take `⟨hm, hrr⟩` from `hred k hkK`. Establish `hkg : Matrix.GeneralLinearGroup.map r k = g` using `Units.ext (hm.trans hg.symm)`.

Establish `hkJ : k ∈ J` using `(hJ k _ hrr).1.2 (hkg ▸ ⟨hgT, hgH⟩)`. Use `⟨⟨⟨k, hkJ⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Both sides reduce to the same expression. Introduce `i j`.

Rewrite using `[hinr]`. Use `⟨hint _ _, (hr.2.1 ⟨Y _ j, hint _ _⟩).1 ?_⟩` and prove the remaining obligations. Conclude with `hlow ⟨a + i.val, by omega⟩ j (by simp) j.2`. Both sides reduce to the same expression.
-/
theorem locDatum_eq_viaRed : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  intro D v φ PP r hr a b t ht L H c J lam hJ mu χ hmu Y
  have hinl : ∀ (i : Fin a) (j : Fin a), rowsTB ht Y (Sum.inl i) j = Y ⟨i.val, by omega⟩ j := fun _ _ => rfl
  have hinr : ∀ (i : Fin t) (j : Fin a), rowsTB ht Y (Sum.inr i) j = Y ⟨a + i.val, by omega⟩ j := fun _ _ => rfl

  unfold viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dif_neg hint]
    unfold localNewformFunction
    rw [dif_neg]
    rintro ⟨⟨k, hk⟩, hbot⟩
    apply hint
    intro i j
    by_cases hi : i.val < a
    · have h1 := congrFun (congrFun hk ⟨i.val, hi⟩) j
      rw [Matrix.submatrix_apply, hinl] at h1
      simp only [Matrix.map_apply, id] at h1
      rw [show i = ⟨i.val, by omega⟩ from rfl, ← h1]
      exact ((k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)) ⟨i.val, hi⟩ j |>.2
    · have h1 := (hbot ⟨i.val - a, by omega⟩ j).1
      rw [hinr] at h1
      have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
      rwa [this] at h1
  rw [dif_pos hint]

  set y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) := Matrix.of fun i j => r ⟨Y i j, hint i j⟩ with hy
  let K : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y ⟨i.val, by omega⟩ j, hint _ _⟩
  have hKr : K.map r = topL a y := by
    ext i j
    simp only [topL, Matrix.map_apply]
    rw [dif_pos ⟨by omega, j.2⟩]
    rfl

  have hKk : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F),
      ((k : Matrix (Fin a) (Fin a) _).map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) =
        (rowsTB ht Y).submatrix Sum.inl id) → (k : Matrix (Fin a) (Fin a) _) = K := by
    intro k hk
    funext i j
    apply Subtype.ext
    have h1 := congrFun (congrFun hk i) j
    rw [Matrix.submatrix_apply, hinl] at h1
    exact h1

  have hred : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F), (k : Matrix (Fin a) (Fin a) _) = K →
      ((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      ∀ i j, RedRel φ PP (((k : Matrix (Fin a) (Fin a) _) i j : v.adicCompletionIntegers D.host.F) : Fv D.host.F v)
        (((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) i j) := by
    intro k hk
    refine ⟨?_, fun i j => redRel_of_isRedMap hr _⟩
    rw [← hKr, ← hk]
    rfl

  unfold gLoc localNewformFunction
  split_ifs with hP hG hG
  ·
    have hk0 := hP.1.choose_spec
    have hg0 := hG.2.choose_spec
    generalize hP.1.choose = k₀ at hk0 ⊢
    obtain ⟨k, hkJ⟩ := k₀
    have hK := hKk k hk0
    obtain ⟨hm, hrr⟩ := hred k hK
    have hkg : Matrix.GeneralLinearGroup.map r k = hG.2.choose := Units.ext (hm.trans hg0.1.symm)
    have hlam := (hJ _ _ hrr).2 hkJ
    rw [hkg, Formalism.L2.DIV.extendOne_of_mem _ hg0.2.2] at hlam
    have hdet : RedRel φ PP ((Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom
        (Matrix.GeneralLinearGroup.det k) : (Fv D.host.F v)ˣ) : Fv D.host.F v)
          ((Matrix.GeneralLinearGroup.det hG.2.choose : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) := by
      have e2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map r k) : (Formalism.L2.DIV.kP PP)ˣ) :
          Formalism.L2.DIV.kP PP) = r ((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers D.host.F)ˣ) :
            v.adicCompletionIntegers D.host.F) := by
        exact (RingHom.map_det r (k : Matrix (Fin a) (Fin a) _)).symm
      rw [← hkg, e2]
      exact redRel_of_isRedMap hr _
    rw [hlam, hmu _ _ hdet]
    push_cast
    rfl
  ·
    exfalso
    apply hG
    obtain ⟨⟨⟨k, hkJ⟩, hk⟩, hbot⟩ := hP
    have hK := hKk k hk
    obtain ⟨hm, hrr⟩ := hred k hK
    have hJk := ((hJ k _ hrr).1.1 hkJ)
    refine ⟨?_, Matrix.GeneralLinearGroup.map r k, hm, hJk⟩
    intro i j hi hj
    have h1 := hbot ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩
    rw [hinr] at h1
    have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
    rw [this] at h1
    exact (hr.2.1 ⟨Y i ⟨j.val, hj⟩, hint _ _⟩).2 h1.2
  ·
    exfalso
    apply hP
    obtain ⟨hlow, g, hg, hgT, hgH⟩ := hG
    have hdet : IsUnit K.det := by
      apply isUnit_of_isRedMap hr
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hKr, ← hg]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    let k : GL (Fin a) (v.adicCompletionIntegers D.host.F) := ((Matrix.isUnit_iff_isUnit_det K).2 hdet).unit
    have hkK : (k : Matrix (Fin a) (Fin a) _) = K := rfl
    obtain ⟨hm, hrr⟩ := hred k hkK
    have hkg : Matrix.GeneralLinearGroup.map r k = g := Units.ext (hm.trans hg.symm)
    have hkJ : k ∈ J := (hJ k _ hrr).1.2 (hkg ▸ ⟨hgT, hgH⟩)
    refine ⟨⟨⟨k, hkJ⟩, ?_⟩, ?_⟩
    · funext i j
      rfl
    · intro i j
      rw [hinr]
      refine ⟨hint _ _, (hr.2.1 ⟨Y _ j, hint _ _⟩).1 ?_⟩
      exact hlow ⟨a + i.val, by omega⟩ j (by simp) j.2
  · rfl

end GlobalTheory.StepVec
