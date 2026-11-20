import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.LieFrame

/- English proof (translation)
Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `: e.symm ⟨τ, i⟩ ≠ e.symm ⟨τ, b⟩` using `fun h => hb (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm`. Simplify using `[Pi.single_eq_of_ne this]`.

Simplify using the standard rewrite rules.
-/
theorem sum_single_apply {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (a : Fin (m τ) → ℂ) (i : Fin (m τ)) :
    (∑ i', a i' • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ, i⟩) = a i := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : e.symm ⟨τ, i⟩ ≠ e.symm ⟨τ, b⟩ := fun h =>
      hb (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
    simp [Pi.single_eq_of_ne this]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `j`. Take `⟨⟨τ', i⟩, rfl⟩` from `e.symm.surjective j`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Conclude with `sum_single_apply e τ' (fun i => w (e.symm ⟨τ', i⟩)) i`.

Establish `h0 : w (e.symm ⟨τ', i⟩) = 0`. Assume the negation of the conclusion as `h0`. Conclude with `h (by simpa using hw _ h0)`. Rewrite using `[h0, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Establish `: e.symm ⟨τ', i⟩ ≠ e.symm ⟨τ, b⟩` using `fun h' => h (Sigma.mk.inj (e.symm.injective h')).1`. Simplify using `[Pi.single_eq_of_ne this]`.
-/
theorem eq_sum_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∑ i, w (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ) = w := by
  funext j
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  by_cases h : τ' = τ
  · subst h
    exact sum_single_apply e τ' (fun i => w (e.symm ⟨τ', i⟩)) i
  · have h0 : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h0
      exact h (by simpa using hw _ h0)
    rw [h0, Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : e.symm ⟨τ', i⟩ ≠ e.symm ⟨τ, b⟩ := fun h' => h (Sigma.mk.inj (e.symm.injective h')).1
    simp [Pi.single_eq_of_ne this]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ g e F k P hP`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP`. Establish `hu : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) v` using `fun τ i => (h2 _).exists`. Use `choose u hu using hu`. Use `⟨u, hu, fun τ i => h1 _ _ (hu τ i), fun τ i => ?_, fun τ w hw hew => ?_⟩` and prove the remaining obligations.

Use `(GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ (hu τ i)).2 fun j hj => ?_` and prove the remaining obligations. Distinguish the cases in `hji : j = e.symm ⟨τ, i⟩`. Substitute `hji` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd (Pi.single_eq_of_ne hji _) hj`.

Take `⟨z, hz, huniq⟩` from `h3 w hw`. Establish `hs` using `(GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ hz).1 hew`. Establish `hc` using `GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (u τ) (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ)`. Use `⟨fun i => z (e.symm ⟨τ, i⟩), (hc (fun i => z (e.symm ⟨τ, i⟩)) w).2 ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sum_single e τ z hs]`.

Conclude with `hz`. Establish `h4` using `huniq _ ((hc a w).1 ha)`. Use function extensionality and compare the values at `i`. Conclude with `(sum_single_apply e τ a i).symm.trans (congrFun h4 _)`.
-/
theorem exists_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), (∀ τ i, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (u τ i)) ∧ (∀ τ i, IsTanAt (S := CAt σ) (F.u k P) (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧ ∀ τ (w : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)), IsTanAt (S := CAt σ) (F.u k P) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ, IsCombAt (S := CAt σ) (F.u k P) (u τ) a w := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hu : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) v := fun τ i => (h2 _).exists
  choose u hu using hu
  refine ⟨u, hu, fun τ i => h1 _ _ (hu τ i), fun τ i => ?_, fun τ w hw hew => ?_⟩
  · refine (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ (hu τ i)).2 fun j hj => ?_
    by_cases hji : j = e.symm ⟨τ, i⟩
    · subst hji
      simp
    · exact absurd (Pi.single_eq_of_ne hji _) hj
  · obtain ⟨z, hz, huniq⟩ := h3 w hw
    have hs := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ hz).1 hew
    have hc := GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ)
    refine ⟨fun i => z (e.symm ⟨τ, i⟩), (hc (fun i => z (e.symm ⟨τ, i⟩)) w).2 ?_, fun a ha => ?_⟩
    · rw [eq_sum_single e τ z hs]
      exact hz
    · have h4 := huniq _ ((hc a w).1 ha)
      funext i
      exact (sum_single_apply e τ a i).symm.trans (congrFun h4 _)

end GlobalTheory.LieFrame
