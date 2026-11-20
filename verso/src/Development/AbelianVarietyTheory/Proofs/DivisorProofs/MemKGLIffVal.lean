import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwKU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩`. Use `Matrix.map_injective (Ov E u).subtype_injective ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `x.mul_inv`. Use `Matrix.map_injective (Ov E u).subtype_injective ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `x.inv_mul`.
-/
theorem mem_KGL_iff_val {u : Pl E} (x : GLw n u) :
    x ∈ GlobalTheory.LFun.KGL u n ↔ (∀ i j, Valued.v (x.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((x⁻¹).val i j) ≤ 1 := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

/- English proof (translation)
Unfold `GlobalTheory.EulerTw.Kglob`. Simplify using `only [Subgroup.mem_iInf, Subgroup.mem_comap]`.
-/
theorem mem_Kglob_iff (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    g ∈ GlobalTheory.EulerTw.Kglob E n ↔ ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) g ∈ GlobalTheory.LFun.KGL u n := by
  unfold GlobalTheory.EulerTw.Kglob
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

/- English proof (translation)
Establish `hid : pLoc E u (GlobalTheory.EulerTw.idem E T) = if u ∈ T then 1 else 0` using `rfl`. Use `split_ifs with hu`. Use `Units.ext (Matrix.ext fun i j => ?_) show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = pLoc E u (g.val i j)` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hid, if_pos hu]`. Simplify using the standard rewrite rules.

Use `Units.ext (Matrix.ext fun i j => ?_) show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hid, if_neg hu]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne hij]`.
-/
theorem pLoc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) :
    GeneralLinearGroup.map (pLoc E u) (GlobalTheory.EulerTw.prjG E n T g) =
      if u ∈ T then GeneralLinearGroup.map (pLoc E u) g else 1 := by
  have hid : pLoc E u (GlobalTheory.EulerTw.idem E T) = if u ∈ T then 1 else 0 := rfl
  split_ifs with hu
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = pLoc E u (g.val i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hid, if_pos hu]
    simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hid, if_neg hu]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

/- English proof (translation)
Use `show Valued.v (pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j)) = _`. Rewrite using `[GlobalTheory.ThetaPull.thetaGL_apply, map_mul, Valuation.map_mul, pLoc_conjFin, (conjLoc_spec _ u).2.2]`. Establish `: Valued.v (pLoc E u ((-1) ^ ((i : ℕ) + j))) = 1`. Rewrite using `[map_pow, map_neg, map_one, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow]`. Rewrite using `[this, one_mul]`.

Both sides reduce to the same expression.
-/
theorem val_pLoc_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) (i j : Fin n) :
    Valued.v ((GeneralLinearGroup.map (pLoc E u) (thF E n g)).val i j) =
      Valued.v ((GeneralLinearGroup.map (pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv u)) g⁻¹).val j.rev i.rev) := by
  show Valued.v (pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j)) = _
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, Valuation.map_mul, pLoc_conjFin, (conjLoc_spec _ u).2.2]
  have : Valued.v (pLoc E u ((-1) ^ ((i : ℕ) + j))) = 1 := by
    rw [map_pow, map_neg, map_one, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow]
  rw [this, one_mul]
  rfl

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_Kglob_iff]`. Introduce `u`. Establish `hs` using `(mem_KGL_iff_val _).1 (hg (conjSrc (IsCMField.complexConj E).toRingEquiv u))`. Rewrite using `[mem_KGL_iff_val]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[val_pLoc_thF, map_inv]`. Conclude with `hs.2 _ _`. Rewrite using `[← map_inv, ← map_inv, val_pLoc_thF, inv_inv]`. Conclude with `hs.1 _ _`.
-/
theorem thF_mem_Kglob (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hg : g ∈ GlobalTheory.EulerTw.Kglob E n) :
    thF E n g ∈ GlobalTheory.EulerTw.Kglob E n := by
  rw [mem_Kglob_iff] at hg ⊢
  intro u
  have hs := (mem_KGL_iff_val _).1 (hg (conjSrc (IsCMField.complexConj E).toRingEquiv u))
  rw [mem_KGL_iff_val]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [val_pLoc_thF, map_inv]
    exact hs.2 _ _
  · rw [← map_inv, ← map_inv, val_pLoc_thF, inv_inv]
    exact hs.1 _ _

end GlobalTheory.EulerTwKU
