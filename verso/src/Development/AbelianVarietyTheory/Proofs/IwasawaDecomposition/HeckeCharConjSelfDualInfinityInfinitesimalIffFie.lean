import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.FrobDense

namespace GlobalTheory.CuspRep.CsdInf

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
The claim follows from `Units.ext (funext fun w => by change starRingEnd ℂ (Complex.exp (z w)) = Complex.exp (star (z w)) rw [← Complex.exp_conj] rfl)`.
-/
theorem star_expU (z : Cinf L) :
    Units.map (starRingEnd (Cinf L)).toMonoidHom (expU z) = expU (star z) :=
  Units.ext (funext fun w => by
    change starRingEnd ℂ (Complex.exp (z w)) = Complex.exp (star (z w))
    rw [← Complex.exp_conj]
    rfl)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h u`. Take `⟨z, rfl⟩ : ∃ z, expU z = u` from `⟨_, expU_log u⟩`. Rewrite using `[star_expU, ← expU_add]`. Apply `Units.ext` to reduce the goal to its premises.

Establish `h1` using `h z`. Rewrite `h1` using `[map_neg]`. Rewrite using `[chiInf_expU, map_add, ← h1, neg_add_cancel, Complex.exp_zero, Units.val_one]`. Introduce `h z`. Establish `h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1` using `fun t => by`.

Establish `h2` using `h (expU (t • z))`. Rewrite `h2` using `[star_expU, ← expU_add, star_smul, star_trivial, ← smul_add]`. Rewrite using `[← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]`. Establish `h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp`.

Rewrite `h2` using `[funext h1]`. Establish `h3` using `h2.unique (hasDerivAt_const _ _)`. Rewrite `h3` using `[map_add]`. Rewrite using `[map_neg]`. Conclude with `(eq_neg_of_add_eq_zero_left h3).symm`.
-/
theorem lie_iff (χ : HChar L) :
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  constructor
  · intro h u
    obtain ⟨z, rfl⟩ : ∃ z, expU z = u := ⟨_, expU_log u⟩
    rw [star_expU, ← expU_add]
    apply Units.ext
    have h1 := h z
    rw [map_neg] at h1
    rw [chiInf_expU, map_add, ← h1, neg_add_cancel, Complex.exp_zero, Units.val_one]
  · intro h z
    have h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1 := fun t => by
      have h2 := h (expU (t • z))
      rw [star_expU, ← expU_add, star_smul, star_trivial, ← smul_add] at h2
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp
    rw [funext h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    rw [map_add] at h3
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h3).symm

/- English proof (translation)
Rewrite using `[HChar.inf, chiInf, MonoidHom.comp_apply, MonoidHom.comp_apply, NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]`. Both sides reduce to the same expression.
-/
theorem inf_eq (χ : HChar L) (k : Lˣ) :
    χ.inf k = chiInf χ (Units.map (pInf L).toMonoidHom (diagUnits L k)) := by
  rw [HChar.inf, chiInf, MonoidHom.comp_apply, MonoidHom.comp_apply, NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]
  rfl

/- English proof (translation)
The claim follows from `Units.ext (pInf_complexConj (k : L))`.
-/
theorem pInf_conj (k : Lˣ) :
    Units.map (pInf L).toMonoidHom (diagUnits L (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k)) =
      Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map (pInf L).toMonoidHom (diagUnits L k)) :=
  Units.ext (pInf_complexConj (k : L))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h u`. Set `q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L` to `(pInf L).toMonoidHom.comp (incl ∅)`. Establish `hq : Continuous q` using `(continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)`. Establish `h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1` using `fun y => (denseRange_units ∅).induction_on (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul ((Continuous.units_map _ continuous_star).comp (hq.units_map _)) …`.

Establish `e : Units.map q (Units.map (proj ∅) (diagUnits L k)) = Units.map (pInf L).toMonoidHom (diagUnits L k)` using `rfl`. Rewrite using `[e, ← pInf_conj, map_mul, ← inf_eq, ← inf_eq, h k, mul_inv_cancel]`. Establish `h3` using `h2 (Units.map (proj ∅) (infId L u))`. Establish `e : Units.map q (Units.map (proj ∅) (infId L u)) = u` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(infEq L).symm (1 - infEq L 1 + infEq L u) = u`.

Use the proof step `simp)`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis. Introduce `h k`. Establish `h1` using `h (Units.map (pInf L).toMonoidHom (diagUnits L k))`. Rewrite `h1` using `[← pInf_conj, map_mul, ← inf_eq, ← inf_eq]`.

Conclude with `eq_inv_of_mul_eq_one_right h1`.
-/
theorem field_iff (χ : HChar L) :
    (∀ k : Lˣ, χ.inf (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k) = (χ.inf k)⁻¹) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  classical
  constructor
  · intro h u
    let q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L := (pInf L).toMonoidHom.comp (incl ∅)
    have hq : Continuous q := (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)
    have h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1 :=
      fun y => (denseRange_units ∅).induction_on
        (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y
        (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul
          ((Continuous.units_map _ continuous_star).comp (hq.units_map _)))) continuous_const) fun k => by
        have e : Units.map q (Units.map (proj ∅) (diagUnits L k)) = Units.map (pInf L).toMonoidHom (diagUnits L k) := rfl
        rw [e, ← pInf_conj, map_mul, ← inf_eq, ← inf_eq, h k, mul_inv_cancel]
    have h3 := h2 (Units.map (proj ∅) (infId L u))
    have e : Units.map q (Units.map (proj ∅) (infId L u)) = u := Units.ext (by
      change (infEq L).symm (1 - infEq L 1 + infEq L u) = u
      simp)
    rwa [e] at h3
  · intro h k
    have h1 := h (Units.map (pInf L).toMonoidHom (diagUnits L k))
    rw [← pInf_conj, map_mul, ← inf_eq, ← inf_eq] at h1
    exact eq_inv_of_mul_eq_one_right h1

end GlobalTheory.CuspRep.CsdInf

open GlobalTheory.CuspRep.CsdInf in

/- English proof (translation)
The claim follows from `host_isCMField H; (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by intro R H χ have := host_isCMField H have e : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k = Units.map (AlgEquiv.toRingEqu …`.
-/
theorem GlobalTheory.CuspRep.csdInf_iff : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H;
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  intro R H χ
  have := host_isCMField H
  have e : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k =
      Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj H.E)).toMonoidHom k :=
    fun k => Units.ext (host_complexConj H k).symm
  show (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹
  simp only [e]
  exact (lie_iff χ).trans (field_iff χ).symm
