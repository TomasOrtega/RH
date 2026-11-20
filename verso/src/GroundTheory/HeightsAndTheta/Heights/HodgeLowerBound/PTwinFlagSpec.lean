import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineFurther
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineMore
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineBis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagSpectrum

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl P h u hu`. Use `set z := IndefiniteRowSideFullHecke.LowerBoundFree.zPart P u with hzdef`. Establish `hz : z ∈ mcPts (mCoordIdeal D.y)` using `hu.1`. Use `choose ch f bfr G lam hfr hdom hdet hlam hpl using hu.2`. Use `⟨bfr, fun τ => (hfr τ).2.2.2.1, fun F hF => ?_⟩` and prove the remaining obligations.

Use `choose c0 hc0 using hz.1`. Establish `hy0 : ∀ p : Σ k, ι k, z p ≠ 0 → D.y p ≠ 0`. Introduce `p hp hy`. Apply `hp` to reduce the goal to its premises. Use `eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero D.y (isMultiHomog_X_single p) (by simpa using hy))` as an intermediate fact.

Simplify using `using this`. Establish `hseg : ∀ τ k, D.y ⟨k, ch τ k⟩ ≠ 0` using `fun τ k => Finset.prod_ne_zero_iff.1 (hfr τ).1 k (Finset.mem_univ _)`. Set `α : K ⊕ (Ψ × Fin (D.N - 1)) → Ω` to `Sum.elim (fun k => (D.y ⟨k, c0 k⟩)⁻¹) (fun q => IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y (ch q.1) P.b)`. Establish `hαu : ∀ β, IsUnit (α β)`. Introduce and unpack `(k | q)`.

Conclude with `(inv_ne_zero (hy0 _ (hc0 k))).isUnit`. Conclude with `(Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hseg q.1 k)).isUnit`. Set `x : (Σ k, ι k) → Ω` to `fun p => α (Sum.inl p.1) * D.y p`. Set `V : WedgeVals Pl Ω` to `fun q m cc => α (Sum.inr q) * wedgeVals Pl bfr q m cc`. Establish `hP : aeval (genPtR Pl x V) F = 0` using `(h₃ Pl D.y (wedgeVals Pl bfr) α hαu F).2 hF`.

Set `x' : (Σ k, ι k) → ℂ` to `fun p => z p / z ⟨p.1, c0 p.1⟩`. Set `V' : WedgeVals Pl ℂ` to `fun q m cc => valAt D.y (V q m cc) z`. Establish `hx : ∀ p, IsValueAt D.y (x p) z (x' p)`. Introduce `p`. Use `⟨fun k => if k = p.1 then 1 else 0, X p, X ⟨p.1, c0 p.1⟩, isMultiHomog_X_single p, isMultiHomog_X_single (⟨p.1, c0 p.1⟩ : Σ k, ι k), by simpa using hy0 _ (hc0 p.1), ?_, by simpa using hc0 p.1, by simp [x']⟩` and prove the remaining obligations.

Simplify using `only [aeval_X, x, α, Sum.elim_inl]`. Clear denominators, using `[hy0 _ (hc0 p.1)]` for the nonvanishing conditions. Establish `hVeq : ∀ τ (i : Fin (D.N - 1)) (m : Fin (Pl.M τ i)) (cc : Fin ((i : ℕ) + 1) → Fin D.N), V (τ, i) m cc = P.gen τ (stepTw i) (Fin.cast (h.M_eq τ i) m) (bfr τ ∘ cc) * IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y (ch τ) P.b`. Introduce `τ i m cc`. Simplify using `only [V, α, wedgeVals, Sum.elim_inr]`.

Rewrite using `[h.gen_eq]`. Conclude with `mul_comm _ _`. Establish `hV : ∀ q m cc, IsValueAt D.y (V q m cc) z (V' q m cc)`. Introduce and unpack `⟨τ, i⟩ m cc`. Take `⟨v, ⟨W, hW, -⟩, -⟩` from `hpl τ (stepTw i) (Fin.cast (h.M_eq τ i) m)`.

Take `⟨-, v0, hv0, -⟩` from `hW cc`. Rewrite `hv0` using `[← hVeq]`. Use `show IsValueAt D.y (V (τ, i) m cc) z (valAt D.y (V (τ, i) m cc) z)`. Rewrite using `[valAt_eq hz hv0]`. Conclude with `hv0`.

Establish `hQ` using `h₁ D.y z (genPtR Pl x V) (genPtR Pl x' V') (h₂ Pl z x x' V V' hx hV) F`. Establish `hQ0 : aeval (genPtR Pl x' V') F = 0`. Use extensionality with `μ`. Establish `hμ` using `hQ μ`. Rewrite `hμ` using `[hP, coeff_zero]`.

Rewrite using `[coeff_zero]`. Conclude with `isValueAt_zero hz hμ`. Set `w : GV D.toComponentData → ℂ` to `Sum.elim (Sum.elim (fun k => z ⟨k, c0 k⟩) (fun q => lam q.1 (stepTw q.2) * ∏ k, z ⟨k, ch q.1 k⟩ ^ P.b k)) (fun t => G t.1 t.2.2 t.2.1)`. Establish `key : ∀ j, eval w (genPtR Pl x' V' j) = u (varMap h j)`. Introduce and unpack `⟨k | ⟨τ, i⟩, t⟩`.

Use `show eval w (X (Sum.inl (Sum.inl k)) * C (x' ⟨k, t⟩)) = z ⟨k, t⟩`. Rewrite using `[eval_mul, eval_X, eval_C]`. Simplify using `only [w, x', Sum.elim_inl]`. Clear denominators, using `[hc0 k]` for the nonvanishing conditions. Take `⟨v, ⟨W, hW, hv⟩, hwv⟩` from `hpl τ (stepTw i) (Fin.cast (h.M_eq τ i) t)`.

Use `Eq.trans ?_ hwv.symm` and prove the remaining obligations. Use `show eval w (X (Sum.inl (Sum.inr (τ, i))) * ∑ cc : Fin ((i : ℕ) + 1) → Fin D.N, (∏ a, X (Sum.inr (τ, headIdx (step_le i) a, cc a))) * C (V' (τ, i) t cc)) = _`. Rewrite using `[hv, eval_mul, eval_X, eval_sum]`. Simplify using `only [eval_mul, eval_prod, eval_X, eval_C, w, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[mul_assoc]`.

Use `congr 1`. Rewrite using `[mul_comm, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun cc _ => ?_` and prove the remaining obligations. Take `⟨-, v0, hv0, hWv⟩` from `hW cc`. Establish `hV0 : V' (τ, i) t cc = v0` using `valAt_eq hz (by convert hv0 using 1; exact hVeq τ i t cc)`.

Rewrite using `[hWv, hV0]`. Simplify using `only [IndefiniteRowSideFullHecke.LowerBoundFree.firstCols, headIdx]`. Rewrite using `[show IndefiniteRowSideFullHecke.LowerBoundFree.zPart P u = z from rfl]`. Conclude with `mul_assoc _ _ _`. Establish `hev : eval u (map (Int.castRingHom ℂ) (forget h F)) = eval w (aeval (genPtR Pl x' V') F)`.

Establish `hh : (eval u).comp ((map (Int.castRingHom ℂ)).comp (forget h).toRingHom) = (eval w).comp (aeval (genPtR Pl x' V')).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `j`.

Simplify using `[forget, key]`. Conclude with `RingHom.congr_fun hh F`. Rewrite using `[hev, hQ0, map_zero]`.
-/
theorem proof (h₁ : FlagPolynomialValue.Statement) (h₂ : FlagGenericPointValue.Statement)
    (h₃ : FlagGenericPointScale.Statement) : FlagSpectrum.Statement := by
  classical
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl P h u hu
  set z := IndefiniteRowSideFullHecke.LowerBoundFree.zPart P u with hzdef
  have hz : z ∈ mcPts (mCoordIdeal D.y) := hu.1
  choose ch f bfr G lam hfr hdom hdet hlam hpl using hu.2
  refine ⟨bfr, fun τ => (hfr τ).2.2.2.1, fun F hF => ?_⟩
  choose c0 hc0 using hz.1
  have hy0 : ∀ p : Σ k, ι k, z p ≠ 0 → D.y p ≠ 0 := by
    intro p hp hy
    apply hp
    have := eval_eq_zero_of_mem_mcPts hz
      (mem_mCoordIdeal_of_aeval_eq_zero D.y (isMultiHomog_X_single p) (by simpa using hy))
    simpa using this
  have hseg : ∀ τ k, D.y ⟨k, ch τ k⟩ ≠ 0 := fun τ k =>
    Finset.prod_ne_zero_iff.1 (hfr τ).1 k (Finset.mem_univ _)
  let α : K ⊕ (Ψ × Fin (D.N - 1)) → Ω := Sum.elim (fun k => (D.y ⟨k, c0 k⟩)⁻¹)
    (fun q => IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y (ch q.1) P.b)
  have hαu : ∀ β, IsUnit (α β) := by
    rintro (k | q)
    · exact (inv_ne_zero (hy0 _ (hc0 k))).isUnit
    · exact (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hseg q.1 k)).isUnit
  let x : (Σ k, ι k) → Ω := fun p => α (Sum.inl p.1) * D.y p
  let V : WedgeVals Pl Ω := fun q m cc => α (Sum.inr q) * wedgeVals Pl bfr q m cc
  have hP : aeval (genPtR Pl x V) F = 0 := (h₃ Pl D.y (wedgeVals Pl bfr) α hαu F).2 hF
  let x' : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c0 p.1⟩
  let V' : WedgeVals Pl ℂ := fun q m cc => valAt D.y (V q m cc) z
  have hx : ∀ p, IsValueAt D.y (x p) z (x' p) := by
    intro p
    refine ⟨fun k => if k = p.1 then 1 else 0, X p, X ⟨p.1, c0 p.1⟩, isMultiHomog_X_single p,
      isMultiHomog_X_single (⟨p.1, c0 p.1⟩ : Σ k, ι k), by simpa using hy0 _ (hc0 p.1), ?_,
      by simpa using hc0 p.1, by simp [x']⟩
    simp only [aeval_X, x, α, Sum.elim_inl]
    field_simp [hy0 _ (hc0 p.1)]
  have hVeq : ∀ τ (i : Fin (D.N - 1)) (m : Fin (Pl.M τ i)) (cc : Fin ((i : ℕ) + 1) → Fin D.N),
      V (τ, i) m cc = P.gen τ (stepTw i) (Fin.cast (h.M_eq τ i) m) (bfr τ ∘ cc) *
        IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y (ch τ) P.b := by
    intro τ i m cc
    simp only [V, α, wedgeVals, Sum.elim_inr]
    rw [h.gen_eq]
    exact mul_comm _ _
  have hV : ∀ q m cc, IsValueAt D.y (V q m cc) z (V' q m cc) := by
    rintro ⟨τ, i⟩ m cc
    obtain ⟨v, ⟨W, hW, -⟩, -⟩ := hpl τ (stepTw i) (Fin.cast (h.M_eq τ i) m)
    obtain ⟨-, v0, hv0, -⟩ := hW cc
    rw [← hVeq] at hv0
    show IsValueAt D.y (V (τ, i) m cc) z (valAt D.y (V (τ, i) m cc) z)
    rw [valAt_eq hz hv0]
    exact hv0
  have hQ := h₁ D.y z (genPtR Pl x V) (genPtR Pl x' V') (h₂ Pl z x x' V V' hx hV) F
  have hQ0 : aeval (genPtR Pl x' V') F = 0 := by
    ext μ
    have hμ := hQ μ
    rw [hP, coeff_zero] at hμ
    rw [coeff_zero]
    exact isValueAt_zero hz hμ
  let w : GV D.toComponentData → ℂ :=
    Sum.elim (Sum.elim (fun k => z ⟨k, c0 k⟩)
      (fun q => lam q.1 (stepTw q.2) * ∏ k, z ⟨k, ch q.1 k⟩ ^ P.b k)) (fun t => G t.1 t.2.2 t.2.1)
  have key : ∀ j, eval w (genPtR Pl x' V' j) = u (varMap h j) := by
    rintro ⟨k | ⟨τ, i⟩, t⟩
    · show eval w (X (Sum.inl (Sum.inl k)) * C (x' ⟨k, t⟩)) = z ⟨k, t⟩
      rw [eval_mul, eval_X, eval_C]
      simp only [w, x', Sum.elim_inl]
      field_simp [hc0 k]
    · obtain ⟨v, ⟨W, hW, hv⟩, hwv⟩ := hpl τ (stepTw i) (Fin.cast (h.M_eq τ i) t)
      refine Eq.trans ?_ hwv.symm
      show eval w (X (Sum.inl (Sum.inr (τ, i))) * ∑ cc : Fin ((i : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (τ, headIdx (step_le i) a, cc a))) * C (V' (τ, i) t cc)) = _
      rw [hv, eval_mul, eval_X, eval_sum]
      simp only [eval_mul, eval_prod, eval_X, eval_C, w, Sum.elim_inl, Sum.elim_inr]
      rw [mul_assoc]
      congr 1
      rw [mul_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cc _ => ?_
      obtain ⟨-, v0, hv0, hWv⟩ := hW cc
      have hV0 : V' (τ, i) t cc = v0 := valAt_eq hz (by convert hv0 using 1; exact hVeq τ i t cc)
      rw [hWv, hV0]
      simp only [IndefiniteRowSideFullHecke.LowerBoundFree.firstCols, headIdx]
      rw [show IndefiniteRowSideFullHecke.LowerBoundFree.zPart P u = z from rfl]
      exact mul_assoc _ _ _
  have hev : eval u (map (Int.castRingHom ℂ) (forget h F)) = eval w (aeval (genPtR Pl x' V') F) := by
    have hh : (eval u).comp ((map (Int.castRingHom ℂ)).comp (forget h).toRingHom) =
        (eval w).comp (aeval (genPtR Pl x' V')).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro j
        simp [forget, key]
    exact RingHom.congr_fun hh F
  rw [hev, hQ0, map_zero]

end FlagSpectrum

end GroundTheory.Heights₂.Heights.LowerBoundFree
