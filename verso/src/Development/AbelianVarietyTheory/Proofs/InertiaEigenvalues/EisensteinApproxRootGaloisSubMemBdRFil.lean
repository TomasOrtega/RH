import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RootGal

/- English proof (translation)
Take `⟨k, hk⟩` from `Polynomial.binomExpansion P x (y - x)`. Establish `hxy : x + (y - x) = y` using `by ring`. Rewrite `hk` using `[hxy]`. Establish `hmem : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) ∈ J`. Establish `e : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) = P.eval y - P.eval x`.

Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.sub_mem hy hx`. Take `⟨v, hv⟩` from `(hu k).exists_right_inv`.

Establish `e : y - x = (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) * v`. Rewrite using `[mul_assoc, hv, mul_one]`. Rewrite using `[e]`. Conclude with `J.mul_mem_right _ hmem`.
-/
theorem sub_mem_of_eval_mem {R : Type*} [CommRing R] (J : Ideal R) (P : Polynomial R) (x y : R)
    (hx : P.eval x ∈ J) (hy : P.eval y ∈ J)
    (hu : ∀ k : R, IsUnit ((Polynomial.derivative P).eval x + k * (y - x))) : y - x ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion P x (y - x)
  have hxy : x + (y - x) = y := by ring
  rw [hxy] at hk
  have hmem : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) ∈ J := by
    have e : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) = P.eval y - P.eval x := by
      rw [hk]; ring
    rw [e]; exact J.sub_mem hy hx
  obtain ⟨v, hv⟩ := (hu k).exists_right_inv
  have e : y - x = (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) * v := by
    rw [mul_assoc, hv, mul_one]
  rw [e]; exact J.mul_mem_right _ hmem

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.ev_alg l n a`.
-/
theorem ev_algebraMap (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

/- English proof (translation)
Take `⟨w, rfl⟩` from `hz`. Establish `h2 : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l` using `GlobalTheory.RingIface.alg_mem_kerP l ha`. Rewrite using `[GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_mul, map_pow, aDp, RingHom.comp_apply, ev_algebraMap, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h2 n), zero_mul]`.
-/
theorem mem_filtration_of_dvd (n : ℕ) (a : Per.Ainf l) (ha : Per.θ l a = 0) (z : Per.BdRp l)
    (hz : aDp l a ^ n ∣ z) : z ∈ Per.FilP l n := by
  obtain ⟨w, rfl⟩ := hz
  have h2 : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := GlobalTheory.RingIface.alg_mem_kerP l ha
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_mul, map_pow, aDp, RingHom.comp_apply, ev_algebraMap, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h2 n), zero_mul]

end GlobalTheory.BSP.RootGal

open GlobalTheory.BSP.RootGal in

/- English proof (translation)
Introduce `l _ K bk n M q hq hroot g`. Establish `hP` using `GlobalTheory.MemLoc.thetaD_props l`. Use `set h : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev with hh`. Use `set h' : bk.S →+* Per.BdRp l := (aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev) with hh'`. Use `set f : Wq l bk.a →+* Per.BdRp l := h.comp PowerSeries.C with hf`.

Establish `hf' : h'.comp PowerSeries.C = f`. Use `RingHom.ext fun w => ?_` and prove the remaining obligations. Simplify using `only [hh', hf, hh, RingHom.comp_apply, bk.ev_C, bk.gal_w]`. Establish `hE : Per.θ l (bk.ev bk.E) = 0`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `hE' : Per.θ l (Per.σA (g : GQ l) (bk.ev bk.E)) = 0` using `by rw [GlobalTheory.RingBasics.θ_σA, hE, map_zero]`. Establish `hY : Polynomial.eval₂ f (h q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n`. Use `mem_filtration_of_dvd n (bk.ev bk.E) hE _ ?_` and prove the remaining obligations. Establish `h1` using `map_dvd h hroot`.

Rewrite `h1` using `[Polynomial.hom_eval₂, map_pow]`. Conclude with `h1`. Establish `hY' : Polynomial.eval₂ f (h' q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n`. Use `mem_filtration_of_dvd n (Per.σA (g : GQ l) (bk.ev bk.E)) hE' _ ?_` and prove the remaining obligations. Establish `h1` using `map_dvd h' hroot`.

Rewrite `h1` using `[Polynomial.hom_eval₂, map_pow, hf']`. Conclude with `h1`. Use `set s : Per.BdRp l := f ((l : Wq l bk.a) ^ M) with hs`. Establish `hs' : s = (l : Per.BdRp l) ^ M` using `by rw [hs, map_pow, map_natCast]`. Establish `hsu : IsUnit s` using `hs' ▸ (isUnit_l_BdRp l).pow M`.

Take `⟨r, hr⟩` from `hsu.exists_left_inv`. Establish `hsy : ∀ z : Per.BdRp l, z = s * (r * z)` using `fun z => by rw [← mul_assoc, mul_comm s r, hr, one_mul]`. Establish `hroot' : ∀ z : Per.BdRp l, Polynomial.eval₂ f z (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n → (bk.Ep.map f).eval (r * z) ∈ Per.FilP l n`. Introduce `z hz`. Rewrite `hz` using `[hsy z, hs, Polynomial.scaleRoots_eval₂_mul, ← hs]`.

Establish `h1` using `(Per.FilP l n).mul_mem_left (r ^ bk.Ep.natDegree) hz`. Rewrite `h1` using `[← mul_assoc, ← mul_pow, hr, one_pow, one_mul, ← Polynomial.eval_map]`. Then use the resulting hypothesis. Establish `hθh : ∀ x : bk.S, Per.θD l (h x) = ((Per.θ l (bk.ev x) : OC l) : ℂ_[l])` using `fun x => hP.2.2.2.1 _`. Establish `hθdiff : Per.θD l (h' q - h q) = 0`. Rewrite using `[map_sub, hθh, show h' q = aDp l (Per.σA (g : GQ l) (bk.ev q)) from rfl, hP.2.2.2.1, GlobalTheory.BKLim.BetaUniq.theta_gal_ev bk g q, sub_self]`.

Establish `hθs : Per.θD l s ≠ 0` using `(hsu.map (Per.θD l)).ne_zero`. Establish `hθq : Per.θD l (h q) = Per.θD l s * Per.θD l (h X)`. Take `⟨c, hc⟩` from `hq`. Establish `h1 : q = (l : bk.S) ^ M * X + bk.E * c` using `by rw [← hc]; ring`. Rewrite using `[h1, map_add, map_mul, map_mul, map_add, map_mul, map_mul, hθh bk.E, hE, hs', map_pow, map_pow, map_natCast, map_natCast]`.

Simplify using the standard rewrite rules. Establish `hθy : Per.θD l (r * h q) = Per.θD l (h X)`. Establish `h1 : Per.θD l s * Per.θD l (r * h q) = Per.θD l s * Per.θD l (h X)`. Rewrite using `[← map_mul, ← mul_assoc, mul_comm s r, hr, one_mul, hθq]`. Conclude with `mul_left_cancel₀ hθs h1`.

Establish `hder : Per.θD l ((Polynomial.derivative (bk.Ep.map f)).eval (r * h q)) ≠ 0`. Rewrite using `[Polynomial.derivative_map, Polynomial.eval_map, Polynomial.hom_eval₂, hθy, hf, ← RingHom.comp_assoc, show Per.θD l (h X) = ((Per.θD l).comp h) X from rfl, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe, RingHom.comp_apply, hθh]`. Introduce `h0`. Apply `GlobalTheory.BKLim.ZNotRoot.theta_deriv_ne bk` to reduce the goal to its premises. Conclude with `Subtype.ext h0`.

Establish `key` using `sub_mem_of_eval_mem (Per.FilP l n) (bk.Ep.map f) (r * h q) (r * h' q) (hroot' _ hY) (hroot' _ hY') (fun k => hP.2.2.1 _ (by`. Rewrite using `[map_add, map_mul, ← mul_sub, map_mul, hθdiff, mul_zero, mul_zero, add_zero]`. Conclude with `hder))`. Rewrite using `[map_sub, show aDp l (Per.σA (g : GQ l) (bk.ev q)) = h' q from rfl, show aDp l (bk.ev q) = h q from rfl, hsy (h' q), hsy (h q), ← mul_sub]`. Conclude with `(Per.FilP l n).mul_mem_left s key`.
-/
theorem GlobalTheory.BSP.approxRoot_gal_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  intro l _ K bk n M q hq hroot g
  have hP := GlobalTheory.MemLoc.thetaD_props l
  set h : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev with hh
  set h' : bk.S →+* Per.BdRp l := (aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev) with hh'
  set f : Wq l bk.a →+* Per.BdRp l := h.comp PowerSeries.C with hf
  have hf' : h'.comp PowerSeries.C = f := by
    refine RingHom.ext fun w => ?_
    simp only [hh', hf, hh, RingHom.comp_apply, bk.ev_C, bk.gal_w]
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have hE' : Per.θ l (Per.σA (g : GQ l) (bk.ev bk.E)) = 0 := by rw [GlobalTheory.RingBasics.θ_σA, hE, map_zero]
  have hY : Polynomial.eval₂ f (h q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (bk.ev bk.E) hE _ ?_
    have h1 := map_dvd h hroot
    rw [Polynomial.hom_eval₂, map_pow] at h1
    exact h1
  have hY' : Polynomial.eval₂ f (h' q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (Per.σA (g : GQ l) (bk.ev bk.E)) hE' _ ?_
    have h1 := map_dvd h' hroot
    rw [Polynomial.hom_eval₂, map_pow, hf'] at h1
    exact h1
  set s : Per.BdRp l := f ((l : Wq l bk.a) ^ M) with hs
  have hs' : s = (l : Per.BdRp l) ^ M := by rw [hs, map_pow, map_natCast]
  have hsu : IsUnit s := hs' ▸ (isUnit_l_BdRp l).pow M
  obtain ⟨r, hr⟩ := hsu.exists_left_inv
  have hsy : ∀ z : Per.BdRp l, z = s * (r * z) := fun z => by rw [← mul_assoc, mul_comm s r, hr, one_mul]

  have hroot' : ∀ z : Per.BdRp l, Polynomial.eval₂ f z (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n →
      (bk.Ep.map f).eval (r * z) ∈ Per.FilP l n := by
    intro z hz
    rw [hsy z, hs, Polynomial.scaleRoots_eval₂_mul, ← hs] at hz
    have h1 := (Per.FilP l n).mul_mem_left (r ^ bk.Ep.natDegree) hz
    rwa [← mul_assoc, ← mul_pow, hr, one_pow, one_mul, ← Polynomial.eval_map] at h1

  have hθh : ∀ x : bk.S, Per.θD l (h x) = ((Per.θ l (bk.ev x) : OC l) : ℂ_[l]) := fun x => hP.2.2.2.1 _
  have hθdiff : Per.θD l (h' q - h q) = 0 := by
    rw [map_sub, hθh, show h' q = aDp l (Per.σA (g : GQ l) (bk.ev q)) from rfl, hP.2.2.2.1,
      GlobalTheory.BKLim.BetaUniq.theta_gal_ev bk g q, sub_self]
  have hθs : Per.θD l s ≠ 0 := (hsu.map (Per.θD l)).ne_zero
  have hθq : Per.θD l (h q) = Per.θD l s * Per.θD l (h X) := by
    obtain ⟨c, hc⟩ := hq
    have h1 : q = (l : bk.S) ^ M * X + bk.E * c := by rw [← hc]; ring
    rw [h1, map_add, map_mul, map_mul, map_add, map_mul, map_mul, hθh bk.E, hE, hs', map_pow, map_pow,
      map_natCast, map_natCast]
    simp
  have hθy : Per.θD l (r * h q) = Per.θD l (h X) := by
    have h1 : Per.θD l s * Per.θD l (r * h q) = Per.θD l s * Per.θD l (h X) := by
      rw [← map_mul, ← mul_assoc, mul_comm s r, hr, one_mul, hθq]
    exact mul_left_cancel₀ hθs h1
  have hder : Per.θD l ((Polynomial.derivative (bk.Ep.map f)).eval (r * h q)) ≠ 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.hom_eval₂, hθy, hf, ← RingHom.comp_assoc,
      show Per.θD l (h X) = ((Per.θD l).comp h) X from rfl, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe,
      RingHom.comp_apply, hθh]
    intro h0
    apply GlobalTheory.BKLim.ZNotRoot.theta_deriv_ne bk
    exact Subtype.ext h0
  have key := sub_mem_of_eval_mem (Per.FilP l n) (bk.Ep.map f) (r * h q) (r * h' q) (hroot' _ hY) (hroot' _ hY')
    (fun k => hP.2.2.1 _ (by
      rw [map_add, map_mul, ← mul_sub, map_mul, hθdiff, mul_zero, mul_zero, add_zero]; exact hder))
  rw [map_sub, show aDp l (Per.σA (g : GQ l) (bk.ev q)) = h' q from rfl, show aDp l (bk.ev q) = h q from rfl,
    hsy (h' q), hsy (h q), ← mul_sub]
  exact (Per.FilP l n).mul_mem_left s key
