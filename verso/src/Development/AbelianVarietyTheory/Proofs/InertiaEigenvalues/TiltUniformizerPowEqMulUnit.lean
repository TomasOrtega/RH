import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcrisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `(GlobalTheory.RingBasics.mem_OC _).1 x.2`.
-/
theorem norm_OC_le_one (x : Per.OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

/- English proof (translation)
Rewrite using `[PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]`.
-/
theorem mk_untilt_iterate (x : OCb l) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)})
      (PreTilt.untilt ((frobeniusEquiv (OCb l) l).symm^[n] x)) = PreTilt.coeff n x := by
  rw [PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

/- English proof (translation)
The claim follows from `Perfection.teichmuller_zero`.
-/
theorem untilt_zero : PreTilt.untilt (0 : OCb l) = 0 := Perfection.teichmuller_zero

/- English proof (translation)
Use `⟨fun h => Perfection.ext fun n => ?_, fun h => h ▸ untilt_zero⟩` and prove the remaining obligations. Establish `h1` using `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n`. Rewrite `h1` using `[h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Express the relevant statement in the definitionally equal form `PreTilt.coeff n x = PreTilt.coeff n 0`. Rewrite using `[← mk_untilt_iterate, h1, map_zero, map_zero]`.
-/
theorem untilt_eq_zero_iff {x : OCb l} : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => Perfection.ext fun n => ?_, fun h => h ▸ untilt_zero⟩
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  rw [h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at h1
  change PreTilt.coeff n x = PreTilt.coeff n 0
  rw [← mk_untilt_iterate, h1, map_zero, map_zero]

def ofCompatible (y : ℕ → Per.OC l) (hy : ∀ n, y (n + 1) ^ l = y n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (y n), fun n => by rw [← map_pow, hy]⟩ :
    Perfection (ModP (Per.OC l) l) l)

/- English proof (translation)
Use `set φ := (frobeniusEquiv (OCb l) l).symm`. Establish `hnorm : ∀ (x : OCb l) (n : ℕ), ‖((PreTilt.untilt (φ^[n] x) : Per.OC l) : ℂ_[l])‖ ^ l ^ n = ‖((PreTilt.untilt x : Per.OC l) : ℂ_[l])‖`. Introduce `x n`. Rewrite using `[← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]`. Establish `hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l]) ≠ 0`.

Introduce `n h0`. Apply `hb` to reduce the goal to its premises. Establish `h0' : PreTilt.untilt (φ^[n] b) = 0` using `Subtype.ext h0`. Rewrite using `[← untilt_eq_zero_iff, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0', zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Establish `hle : ∀ n, ‖((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l])‖`.

Introduce `n`. Establish `hpn : l ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`. Rewrite using `[← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, hnorm, hnorm]`. Conclude with `h`. Establish `hstep : ∀ (x : OCb l) (n : ℕ), PreTilt.untilt (φ^[n + 1] x) ^ l = PreTilt.untilt (φ^[n] x)`.

Introduce `x n`. Rewrite using `[Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]`. Set `y : ℕ → Per.OC l` to `fun n => ⟨((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l]) / PreTilt.untilt (φ^[n] b), (GlobalTheory.RingBasics.mem_OC _).2 (by`. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩`.

Establish `hy : ∀ n, y (n + 1) ^ l = y n`. Introduce `n`. Use `ext`. Simplify using `only [y, SubmonoidClass.coe_pow, div_pow]`. Rewrite using `[← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, hstep, hstep]`.

Use `⟨ofCompatible y hy, Perfection.ext fun n => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n a = PreTilt.coeff n (b * ofCompatible y hy)`. Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `_ = _ * Ideal.Quotient.mk _ (y n)`. Rewrite using `[← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]`.

Use `congr 1`. Use `ext`. Rewrite using `[MulMemClass.coe_mul]`. Express the relevant statement in the definitionally equal form `_ = _ * (_ / _)`. Rewrite using `[mul_div_cancel₀ _ (hbn n)]`.
-/
theorem dvd_of_norm_untilt_le {a b : OCb l} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt b : Per.OC l) : ℂ_[l])‖) :
    b ∣ a := by
  set φ := (frobeniusEquiv (OCb l) l).symm
  have hnorm : ∀ (x : OCb l) (n : ℕ), ‖((PreTilt.untilt (φ^[n] x) : Per.OC l) : ℂ_[l])‖ ^ l ^ n =
      ‖((PreTilt.untilt x : Per.OC l) : ℂ_[l])‖ := by
    intro x n
    rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
  have hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro n h0
    apply hb
    have h0' : PreTilt.untilt (φ^[n] b) = 0 := Subtype.ext h0
    rw [← untilt_eq_zero_iff, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0',
      zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hle : ∀ n,
      ‖((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l])‖ := by
    intro n
    have hpn : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, hnorm, hnorm]
    exact h
  have hstep : ∀ (x : OCb l) (n : ℕ), PreTilt.untilt (φ^[n + 1] x) ^ l = PreTilt.untilt (φ^[n] x) := by
    intro x n
    rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]
  let y : ℕ → Per.OC l := fun n =>
    ⟨((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l]) / PreTilt.untilt (φ^[n] b), (GlobalTheory.RingBasics.mem_OC _).2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hy : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    ext
    simp only [y, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, hstep, hstep]
  refine ⟨ofCompatible y hy, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n a = PreTilt.coeff n (b * ofCompatible y hy)
  rw [map_mul]
  change _ = _ * Ideal.Quotient.mk _ (y n)
  rw [← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]
  congr 1
  ext
  rw [MulMemClass.coe_mul]
  change _ = _ * (_ / _)
  rw [mul_div_cancel₀ _ (hbn n)]

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨m, hm'⟩ : ∃ m, P.natDegree = m + 1` from `⟨P.natDegree - 1, by omega⟩`. Establish `hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Establish `hl1 : ‖((l : ℕ) : ℂ_[l])‖ < 1` using `GlobalTheory.RingBasics.norm_p_lt`. Establish `hc : ∀ i < P.natDegree, ‖Ψ (P.coeff i)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖`. Introduce `i hi`.

Take `⟨y, hy⟩` from `hdvd i hi`. Rewrite using `[hy, map_mul, map_natCast, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hw : ‖Ψ w‖ = 1`. Establish `h1 : Ψ w * Ψ ↑w⁻¹ = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`.

Establish `ha` using `hΨ w`. Establish `hb` using `hΨ ↑w⁻¹`. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_mul, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (Ψ w), norm_nonneg (Ψ ↑w⁻¹)]`.

Establish `hc0 : ‖Ψ (P.coeff 0)‖ = ‖((l : ℕ) : ℂ_[l])‖`. Rewrite using `[h0, map_mul, map_natCast, norm_mul, hw, mul_one]`. Establish `htop : P.coeff (m + 1) = 1` using `by rw [← hm']; exact hm.coeff_natDegree`. Rewrite `hz` using `[Polynomial.eval₂_eq_sum_range, hm', Finset.sum_range_succ, Finset.sum_range_succ', htop, map_one, one_mul, pow_zero, mul_one]`. Use `set S := ∑ i ∈ Finset.range m, Ψ (P.coeff (i + 1)) * z ^ (i + 1) with hSdef`.

Establish `hS : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * ‖z‖`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i + 1 < P.natDegree` using `by rw [hm']; simpa using Finset.mem_range.1 hi`. Establish `hp : ‖z‖ ^ (i + 1) ≤ ‖z‖` using `pow_le_of_le_one (norm_nonneg _) hz1 (by omega)`.

Conclude with `mul_le_mul (hc _ hi') hp (by positivity) (norm_nonneg _)`. Establish `hzpow : z ^ (m + 1) = -(Ψ (P.coeff 0) + S)` using `by linear_combination hz`. Establish `hSl : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖` using `hS.trans (by nlinarith [norm_nonneg z])`. Establish `hup : ‖z ^ (m + 1)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖`. Rewrite using `[hzpow, norm_neg]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0.le hSl)` and prove the remaining obligations. Establish `hzlt : ‖z‖ < 1`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `: 1 ≤ ‖z‖ ^ (m + 1)` using `one_le_pow₀ hge`.

Rewrite `hup` using `[norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSlt : ‖S‖ < ‖((l : ℕ) : ℂ_[l])‖` using `hS.trans_lt (by nlinarith [norm_nonneg z])`. Establish `hlow : ‖((l : ℕ) : ℂ_[l])‖ ≤ ‖z ^ (m + 1)‖`. Establish `h3 : Ψ (P.coeff 0) = -(z ^ (m + 1) + S)` using `by linear_combination hz`.

Establish `h4` using `IsUltrametricDist.norm_add_le_max (z ^ (m + 1)) S`. Rewrite `h4` using `[← norm_neg (z ^ (m + 1) + S), ← h3, hc0]`. Break down `le_max_iff.1 h4 with h5 | h5` into its components or cases. Conclude with `h5`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hm']`. Conclude with `le_antisymm hup hlow`.
-/
theorem norm_pow_natDegree_eq_of_eisenstein {R : Type*} [CommRing R] (P : Polynomial R) (hm : P.Monic)
    (hpos : 0 < P.natDegree) (hdvd : ∀ i < P.natDegree, ((l : ℕ) : R) ∣ P.coeff i)
    (w : Rˣ) (h0 : P.coeff 0 = ((l : ℕ) : R) * w) (Ψ : R →+* ℂ_[l]) (hΨ : ∀ y, ‖Ψ y‖ ≤ 1)
    (z : ℂ_[l]) (hz1 : ‖z‖ ≤ 1) (hz : P.eval₂ Ψ z = 0) :
    ‖z ^ P.natDegree‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨m, hm'⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hl1 : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hc : ∀ i < P.natDegree, ‖Ψ (P.coeff i)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨y, hy⟩ := hdvd i hi
    rw [hy, map_mul, map_natCast, norm_mul]
    calc _ ≤ ‖((l : ℕ) : ℂ_[l])‖ * 1 := by gcongr; exact hΨ y
      _ = _ := mul_one _
  have hw : ‖Ψ w‖ = 1 := by
    have h1 : Ψ w * Ψ ↑w⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ha := hΨ w
    have hb := hΨ ↑w⁻¹
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    nlinarith [norm_nonneg (Ψ w), norm_nonneg (Ψ ↑w⁻¹)]
  have hc0 : ‖Ψ (P.coeff 0)‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [h0, map_mul, map_natCast, norm_mul, hw, mul_one]
  have htop : P.coeff (m + 1) = 1 := by rw [← hm']; exact hm.coeff_natDegree
  rw [Polynomial.eval₂_eq_sum_range, hm', Finset.sum_range_succ, Finset.sum_range_succ', htop,
    map_one, one_mul, pow_zero, mul_one] at hz
  set S := ∑ i ∈ Finset.range m, Ψ (P.coeff (i + 1)) * z ^ (i + 1) with hSdef
  have hS : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * ‖z‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i + 1 < P.natDegree := by rw [hm']; simpa using Finset.mem_range.1 hi
    have hp : ‖z‖ ^ (i + 1) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1 (by omega)
    exact mul_le_mul (hc _ hi') hp (by positivity) (norm_nonneg _)
  have hzpow : z ^ (m + 1) = -(Ψ (P.coeff 0) + S) := by linear_combination hz
  have hSl : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hS.trans (by nlinarith [norm_nonneg z])
  have hup : ‖z ^ (m + 1)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hzpow, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0.le hSl)
  have hzlt : ‖z‖ < 1 := by
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖z‖ ^ (m + 1) := one_le_pow₀ hge
    rw [norm_pow] at hup
    linarith
  have hSlt : ‖S‖ < ‖((l : ℕ) : ℂ_[l])‖ := hS.trans_lt (by nlinarith [norm_nonneg z])
  have hlow : ‖((l : ℕ) : ℂ_[l])‖ ≤ ‖z ^ (m + 1)‖ := by
    have h3 : Ψ (P.coeff 0) = -(z ^ (m + 1) + S) := by linear_combination hz
    have h4 := IsUltrametricDist.norm_add_le_max (z ^ (m + 1)) S
    rw [← norm_neg (z ^ (m + 1) + S), ← h3, hc0] at h4
    rcases le_max_iff.1 h4 with h5 | h5
    · exact h5
    · linarith
  rw [hm']
  exact le_antisymm hup hlow

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

/- English proof (translation)
Introduce `l _ K bk ϖ hϖ`. Use `set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr`. Establish `h1 : bk.flat.untilt = intToOC K r`. Rewrite using `[← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]`. Conclude with `bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])`.

Set `Ψ0 : (Wq l bk.a)⟦X⟧ →+* ℂ_[l]` to `(PadicComplexInt l).subtype.comp ((intToOC K).comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _)))`. Set `Ψ : Wq l bk.a →+* ℂ_[l]` to `Ψ0.comp (Polynomial.coeToPowerSeries.ringHom.comp Polynomial.C)`. Establish `hΨ : ∀ y, ‖Ψ y‖ ≤ 1` using `fun y => norm_OC_le_one _`. Use `set z : ℂ_[l] := Ψ0 (Polynomial.coeToPowerSeries.ringHom Polynomial.X) with hzdef`. Establish `hzX : z = ((bk.flat.untilt : Per.OC l) : ℂ_[l])`.

Rewrite using `[h1, hzdef, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]`. Both sides reduce to the same expression. Establish `hz1 : ‖z‖ ≤ 1` using `by rw [hzX]; exact norm_OC_le_one _`. Establish `hE : Ψ0 (bk.Ep : (Wq l bk.a)⟦X⟧) = 0`. Establish `: Ideal.Quotient.mk (Ideal.span {(bk.Ep : (Wq l bk.a)⟦X⟧)}) (bk.Ep : (Wq l bk.a)⟦X⟧) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`.

Simplify using `only [Ψ0, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, map_zero]`. Establish `hz : bk.Ep.eval₂ Ψ z = 0`. Rewrite using `[← hE, hzdef, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]`. Both sides reduce to the same expression. Establish `hnorm` using `norm_pow_natDegree_eq_of_eisenstein bk.Ep bk.monic bk.deg_pos bk.dvd_coeff bk.coeff_zero.choose bk.coeff_zero.choose_spec Ψ hΨ z hz1 hz`.

Rewrite `hnorm` using `[hzX, ← SubmonoidClass.coe_pow, ← map_pow]`. Establish `hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Establish `hϖn : ‖((ϖ.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖`. Rewrite using `[hϖ]`. Use `norm_cast`.

Rewrite `hnorm` using `[← hϖn]`. Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hϖn` using `[untilt_zero]`. Simplify using `at hϖn`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨x, hx⟩` from `dvd_of_norm_untilt_le hϖ0 hnorm.le`. Use `⟨x, ?_, hx⟩` and prove the remaining obligations. Establish `hxn : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1`. Establish `h2` using `hnorm`.

Rewrite `h2` using `[hx, map_mul, MulMemClass.coe_mul, norm_mul, hϖn]`. Establish `h3 : ‖((l : ℕ) : ℂ_[l])‖ * ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ * 1`. Rewrite using `[mul_one]`. Conclude with `h2`. Conclude with `mul_left_cancel₀ hl0.ne' h3`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hxn` using `[untilt_zero]`. Simplify using `at hxn`. Use `isUnit_of_dvd_one (dvd_of_norm_untilt_le hx0 ?_)` and prove the remaining obligations.

Rewrite using `[map_one, OneMemClass.coe_one, norm_one, hxn]`.
-/
theorem flat_pow_natDegree_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l),
    ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  intro l _ K bk ϖ hϖ
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have h1 : bk.flat.untilt = intToOC K r := by
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  let Ψ0 : (Wq l bk.a)⟦X⟧ →+* ℂ_[l] := (PadicComplexInt l).subtype.comp
    ((intToOC K).comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _)))
  let Ψ : Wq l bk.a →+* ℂ_[l] := Ψ0.comp (Polynomial.coeToPowerSeries.ringHom.comp Polynomial.C)
  have hΨ : ∀ y, ‖Ψ y‖ ≤ 1 := fun y => norm_OC_le_one _
  set z : ℂ_[l] := Ψ0 (Polynomial.coeToPowerSeries.ringHom Polynomial.X) with hzdef
  have hzX : z = ((bk.flat.untilt : Per.OC l) : ℂ_[l]) := by
    rw [h1, hzdef, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    rfl
  have hz1 : ‖z‖ ≤ 1 := by rw [hzX]; exact norm_OC_le_one _
  have hE : Ψ0 (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 := by
    have : Ideal.Quotient.mk (Ideal.span {(bk.Ep : (Wq l bk.a)⟦X⟧)}) (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [Ψ0, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, map_zero]
  have hz : bk.Ep.eval₂ Ψ z = 0 := by
    rw [← hE, hzdef, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rfl
  have hnorm := norm_pow_natDegree_eq_of_eisenstein bk.Ep bk.monic bk.deg_pos bk.dvd_coeff
    bk.coeff_zero.choose bk.coeff_zero.choose_spec Ψ hΨ z hz1 hz
  rw [hzX, ← SubmonoidClass.coe_pow, ← map_pow] at hnorm
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hϖn : ‖((ϖ.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hϖ]; norm_cast
  rw [← hϖn] at hnorm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hϖn
    simp at hϖn
    linarith
  obtain ⟨x, hx⟩ := dvd_of_norm_untilt_le hϖ0 hnorm.le
  refine ⟨x, ?_, hx⟩
  have hxn : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := by
    have h2 := hnorm
    rw [hx, map_mul, MulMemClass.coe_mul, norm_mul, hϖn] at h2
    have h3 : ‖((l : ℕ) : ℂ_[l])‖ * ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ * 1 := by
      rw [mul_one]; exact h2
    exact mul_left_cancel₀ hl0.ne' h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hxn
    simp at hxn
  refine isUnit_of_dvd_one (dvd_of_norm_untilt_le hx0 ?_)
  rw [map_one, OneMemClass.coe_one, norm_one, hxn]

end GlobalTheory.TiltDiv

end
