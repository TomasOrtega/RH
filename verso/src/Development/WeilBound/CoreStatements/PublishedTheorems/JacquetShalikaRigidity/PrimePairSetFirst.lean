import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLaw

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace primePairSetFirst

variable {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}

/- English proof (translation)
Establish `key` using `GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1))) (isCoLat_ratV E _) (GA E k) (fun p => ψ (-dot (eLast k (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_`. Conclude with `key`. Conclude with `(hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul (hc.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))`. Introduce `g γ hγ y`. Conclude with `(per_coef hψ (eLast k (m + 1)) hc hl g).2 γ hγ y`.
-/
theorem cont_colT (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g) :
    Continuous (colT ψ (m + 1) f) := by
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E k)
    (fun p => ψ (-dot (eLast k (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · exact (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hc.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast k (m + 1)) hc hl g).2 γ hγ y

/- English proof (translation)
Establish `hper` using `per_coef (a := k) hψ (eLast k (m + 1)) hc hl g`. Establish `hT` using `GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1))) (isCoLat_ratV E _) _ hper y`. Establish `hpt : (fun x : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) = fun x => ψ (dot (eLast k (m + 1)) y) * (ψ (-dot (eLast k (m + 1)) (x + y)) * f (blkU (x + y) * g))`. Use function extensionality and compare the values at `x`. Establish `hd : dot (eLast k (m + 1)) (x + y) = dot (eLast k (m + 1)) x + dot (eLast k (m + 1)) y`.

Simplify using `only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Establish `hu : (blkU (x + y) : GA E k) = blkU x * blkU y` using `posU_add _ x y`. Establish `h1 : ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Rewrite using `[hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]`.

Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) = _ * avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * g))`. Rewrite using `[hpt, avg_const_mul]`. Conclude with `congrArg _ hT`.
-/
theorem colT_blkU (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g)
    (y : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k (m + 1)) y) * colT ψ (m + 1) f g := by
  have hper := per_coef (a := k) hψ (eLast k (m + 1)) hc hl g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast k (m + 1)) y) *
        (ψ (-dot (eLast k (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast k (m + 1)) (x + y) = dot (eLast k (m + 1)) x + dot (eLast k (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E k) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y)) *
            (ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

/- English proof (translation)
Simplify using `only [colT, coefF]`. Rewrite using `[← avg_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast k j) y) * f (blkU x * g)`.

Rewrite using `[← mul_assoc, blkU_mul_blkU hj x y, mul_assoc, hlaw, dot_eLast_shift hj x y]`. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colT_law (m : ℕ) (f : GA E k → ℂ) (j : ℕ) (hj : m + 1 < j)
    (hlaw : ∀ (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k), f (blkU y * g) = ψ (dot (eLast k j) y) * f g)
    (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k j) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast k j) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hj x y, mul_assoc, hlaw, dot_eLast_shift hj x y]
  rw [e1]
  ring

/- English proof (translation)
Unfold `colT`. Rewrite using `[GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E k ψ hψ m f hc hl γ hγ (eLast k (m + 1)) g]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Set `s0 : UnipotentBlockColumnIndex k (m + 1) (m + 1)` to `⟨(⟨m, by omega⟩, ⟨m + 1, hmk⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩`.

Rewrite using `[Finset.sum_eq_single s0]`. Establish `h1 : eLast (E` using `E) k (m + 1) s0 = 1 := by simp [eLast, s0]`. Rewrite using `[h1, one_mul]`. Introduce `s _ hs`. Establish `h0 : eLast (E` using `E) k (m + 1) s = 0 := by`.

Simplify using `only [eLast]`. Rewrite using `[if_neg]`. Introduce `e`. Apply `hs` to reduce the goal to its premises. Establish `h2` using `s.2.2`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))`. Rewrite using `[h0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem colT_rat (hψ : StdPsi ψ) (m : ℕ) (hmk : m + 1 < k) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ γ : GL (Fin k) E, IsMir (m + 1) γ → ∀ g, f (ratGL E k γ * g) = f g)
    (γ : GL (Fin k) E) (hγ : IsMir (m + 1) γ) (g : GA E k) :
    colT ψ (m + 1) f (ratGL E k γ * g) = coefF ψ (m + 1) (fun t => γ.val ⟨m, by omega⟩ t.1.1) f g := by
  unfold colT
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E k ψ hψ m f hc hl γ hγ (eLast k (m + 1)) g]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex k (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hmk⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) k (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul]
  · intro s _ hs
    have h0 : eLast (E := E) k (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h` using `t.2.2`. Conclude with `Subtype.ext (Prod.ext rfl (Fin.ext (by show m + 1 = (t.1.2 : ℕ); omega)))`.
-/
theorem blk_eta {m : ℕ} (hmk : m + 1 < k) (t : UnipotentBlockColumnIndex k (m + 1) (m + 1)) :
    (⟨(t.1.1, ⟨m + 1, hmk⟩), t.2.1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k (m + 1) (m + 1)) = t := by
  have h := t.2.2
  exact Subtype.ext (Prod.ext rfl (Fin.ext (by show m + 1 = (t.1.2 : ℕ); omega)))

def rowEquiv (m : ℕ) (hmk : m + 1 < k) : RowT E k (m + 1) ≃ {ξ : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E // ξ ≠ 0} where
  toFun ξ := ⟨fun t => ξ.1 t.1.1, by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ξ.2.1
    have him : (i : ℕ) < m + 1 := by
      by_contra h
      exact hi (ξ.2.2 i (by omega))
    intro h0
    exact hi (congrFun h0 ⟨(i, ⟨m + 1, hmk⟩), him, le_rfl, le_rfl⟩)⟩
  invFun η := ⟨fun i => if h : (i : ℕ) < m + 1 then η.1 ⟨(i, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0, by
    refine ⟨fun h0 => η.2 ?_, fun i hi => dif_neg (by omega)⟩
    funext t
    have h1 := congrFun h0 t.1.1
    simp only [Pi.zero_apply] at h1
    rw [dif_pos t.2.1, blk_eta hmk t] at h1
    exact h1⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    by_cases h : (i : ℕ) < m + 1
    · exact dif_pos h
    · exact (dif_neg h).trans (ξ.2.2 i (by omega)).symm
  right_inv η := by
    apply Subtype.ext
    funext t
    show (if h : (t.1.1 : ℕ) < m + 1 then η.1 ⟨(t.1.1, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0) = η.1 t
    rw [dif_pos t.2.1, blk_eta hmk t]

end primePairSetFirst

/- English proof (translation)
Introduce `hN _ E _ _ _ k ψ hψ m hm1 hmk f hf`. Take `⟨m, rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by omega⟩`. Establish `hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g` using `fun c g => hf.left _ (isMir_blkU c) g`. Simplify using `only [Nat.add_sub_cancel]`. Use `⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨primePairSetFirst.rowEquiv m hmk, fun ξ t => rfl⟩⟩` and prove the remaining obligations.

Conclude with `primePairSetFirst.cont_colT hψ m f hf.cont hl`. Introduce `γ hγ g`. Establish `hγ1 : IsMir (m + 1) γ` using `fun i c h => hγ i c (by omega)`. Rewrite using `[primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left γ hγ1 g]`. Unfold `colT`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[hγ ⟨m, by omega⟩ t.1.1 (Or.inl le_rfl)]`. Establish `ht` using `t.2.1`. Simplify using `only [eLast, Matrix.one_apply]`.

Distinguish the cases in `h : (t.1.1 : ℕ) = m`. Rewrite using `[if_pos (Fin.ext h.symm), if_pos (by omega)]`. Rewrite using `[if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]`. Introduce `j hj y g`. Break down `Nat.lt_or_ge (m + 1) j with h1 | h1` into its components or cases.

Conclude with `primePairSetFirst.colT_law m f j h1 (hf.law j h1) y g`. Take `rfl : j = m + 1` from `by omega`. Conclude with `primePairSetFirst.colT_blkU hψ m f hf.cont hl y g`. Introduce `ξ g`. Take `⟨hB, hrow⟩` from `(hN E k (m + 1) (by omega) (by omega)).1 ξ`.

Establish `hγ : IsMir (m + 1) (gam ξ)` using `fun i c h => hB i c (by omega)`. Rewrite using `[primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left _ hγ g]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `(hrow _ _ rfl).symm`.

Introduce `χ hχ`. Use function extensionality and compare the values at `g`. Simplify using `only [colT, coefF]`. Rewrite using `[← avg_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[hχ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem p1_holds : N0 → P0 → P1 := by
  intro hN _ E _ _ _ k ψ hψ m hm1 hmk f hf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  simp only [Nat.add_sub_cancel]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨primePairSetFirst.rowEquiv m hmk, fun ξ t => rfl⟩⟩
  · exact primePairSetFirst.cont_colT hψ m f hf.cont hl
  · intro γ hγ g
    have hγ1 : IsMir (m + 1) γ := fun i c h => hγ i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left γ hγ1 g]
    unfold colT
    congr 1
    funext t
    rw [hγ ⟨m, by omega⟩ t.1.1 (Or.inl le_rfl)]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro j hj y g
    rcases Nat.lt_or_ge (m + 1) j with h1 | h1
    · exact primePairSetFirst.colT_law m f j h1 (hf.law j h1) y g
    · obtain rfl : j = m + 1 := by omega
      exact primePairSetFirst.colT_blkU hψ m f hf.cont hl y g
  · intro ξ g
    obtain ⟨hB, hrow⟩ := (hN E k (m + 1) (by omega) (by omega)).1 ξ
    have hγ : IsMir (m + 1) (gam ξ) := fun i c h => hB i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left _ hγ g]
    congr 1
    funext t
    exact (hrow _ _ rfl).symm
  · intro χ hχ
    funext g
    simp only [colT, coefF]
    rw [← avg_const_mul]
    congr 1
    funext x
    rw [hχ]
    ring

end PositivityTheory.AdelicQuotientData

end
