import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorialMulEqPowAinf
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.AcrisPow
variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `⟨4 * (A + B + 1), fun n hn => ?_⟩` and prove the remaining obligations. Use `set m := 2 * (A + B + 1) with hm`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le (show m ≤ n by omega)`. Establish `hk : m ≤ k` using `by omega`. Establish `h1 : m < 2 ^ m` using `Nat.lt_two_pow_self`.

Establish `h2 : k < 2 ^ k` using `Nat.lt_two_pow_self`. Establish `h3 : (m + 1) * (k + 1) ≤ 2 ^ m * 2 ^ k` using `Nat.mul_le_mul h1 h2`. Rewrite using `[pow_add]`. Establish `h4 : A * (m + k) + B < (m + 1) * (k + 1)` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem eventually_lt_two_pow (A B : ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → A * n + B < 2 ^ n := by
  refine ⟨4 * (A + B + 1), fun n hn => ?_⟩
  set m := 2 * (A + B + 1) with hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show m ≤ n by omega)
  have hk : m ≤ k := by omega
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : (m + 1) * (k + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul h1 h2
  rw [pow_add]
  have h4 : A * (m + k) + B < (m + 1) * (k + 1) := by nlinarith
  omega

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hlu : IsUnit ((l : ℕ) : Per.AinfP l)`. Use `IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hf : IsUnit ((l.factorial : ℕ) : Per.AinfP l)`.

Take `⟨c, hc⟩` from `GlobalTheory.Per.exists_factorial_mul_eq_pow_ainf l l`. Establish `h2` using `congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) hc`. Rewrite `h2` using `[map_mul, map_pow, map_natCast, map_natCast]`. Conclude with `isUnit_of_mul_isUnit_left (h2 ▸ hlu.pow l)`. Take `⟨v, hv⟩` from `hf.exists_right_inv`.

Establish `hx : ((l.factorial : ℕ) : Per.AinfP l) * (v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l) = algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l` using `by rw [← mul_assoc, hv, one_mul]`. Generalize the expression as in `v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l = x at hx`. Establish `hxD : x ∈ Per.Acris0 l` using `GlobalTheory.RingIface.dividedPower_mem_Acris0 l ξ l x hξ hx`. Establish `hfac : ((l.factorial : ℕ) : Per.AinfP l) = ((l : ℕ) : Per.AinfP l) * (((l - 1).factorial : ℕ) : Per.AinfP l)`. Rewrite using `[← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]`.

Use `⟨(((l - 1).factorial : ℕ) : Per.Acris0 l) * ⟨x, hxD⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, SubringClass.coe_natCast]`. Rewrite using `[← hx, hfac, mul_assoc]`.
-/
theorem dvd_pow_acris0 (ξ : Ainf l) (hξ : Per.θ l ξ = 0) :
    ((l : ℕ) : Per.Acris0 l) ∣ algebraMap (Ainf l) (Per.Acris0 l) ξ ^ l := by
  have hp : l.Prime := Fact.out
  have hlu : IsUnit ((l : ℕ) : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)
    rwa [map_natCast] at this
  have hf : IsUnit ((l.factorial : ℕ) : Per.AinfP l) := by
    obtain ⟨c, hc⟩ := GlobalTheory.Per.exists_factorial_mul_eq_pow_ainf l l
    have h2 := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) hc
    rw [map_mul, map_pow, map_natCast, map_natCast] at h2
    exact isUnit_of_mul_isUnit_left (h2 ▸ hlu.pow l)
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hx : ((l.factorial : ℕ) : Per.AinfP l) * (v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l := by rw [← mul_assoc, hv, one_mul]
  generalize v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l = x at hx
  have hxD : x ∈ Per.Acris0 l := GlobalTheory.RingIface.dividedPower_mem_Acris0 l ξ l x hξ hx
  have hfac : ((l.factorial : ℕ) : Per.AinfP l) =
      ((l : ℕ) : Per.AinfP l) * (((l - 1).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  refine ⟨(((l - 1).factorial : ℕ) : Per.Acris0 l) * ⟨x, hxD⟩, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, SubringClass.coe_natCast]
  rw [← hx, hfac, mul_assoc]

/- English proof (translation)
Use `set f := algebraMap (Ainf l) (Per.Acris l)`. Establish `hξ : Per.θ l (bk.ev bk.E) = 0`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `h1 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l`.

Use `map_dvd (algebraMap (Per.Acris0 l) (Per.Acris l)) (dvd_pow_acris0 _ hξ)` as an intermediate fact. Rewrite `this` using `[map_natCast, map_pow, ← GlobalTheory.RingIface.tower l]`. Conclude with `this`. Establish `h2 : (l : Per.Acris l) ∣ f (bk.ev bk.E) - f (bk.ev X) ^ bk.Ep.natDegree`. Use `map_dvd f (AinfDiv.dvd_E bk)` as an intermediate fact.

Rewrite `this` using `[map_natCast, map_sub, map_pow]`. Then use the resulting hypothesis. Establish `h3 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l - (f (bk.ev X) ^ bk.Ep.natDegree) ^ l` using `h2.trans (sub_dvd_pow_sub_pow _ _ l)`. Establish `h4` using `dvd_sub h1 h3`. Rewrite `h4` using `[sub_sub_cancel, ← pow_mul]`. Simplify `h4` using `[RingHom.comp_apply]`.
-/
theorem dvd_X_pow {K : FinExt l} (bk : BK K) :
    (l : Per.Acris l) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (bk.Ep.natDegree * l) := by
  set f := algebraMap (Ainf l) (Per.Acris l)
  have hξ : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h1 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l := by
    have := map_dvd (algebraMap (Per.Acris0 l) (Per.Acris l)) (dvd_pow_acris0 _ hξ)
    rw [map_natCast, map_pow, ← GlobalTheory.RingIface.tower l] at this
    exact this
  have h2 : (l : Per.Acris l) ∣ f (bk.ev bk.E) - f (bk.ev X) ^ bk.Ep.natDegree := by
    have := map_dvd f (AinfDiv.dvd_E bk)
    rwa [map_natCast, map_sub, map_pow] at this
  have h3 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l - (f (bk.ev X) ^ bk.Ep.natDegree) ^ l :=
    h2.trans (sub_dvd_pow_sub_pow _ _ l)
  have h4 := dvd_sub h1 h3
  rw [sub_sub_cancel, ← pow_mul] at h4
  simpa [RingHom.comp_apply] using h4

/- English proof (translation)
Introduce `l _ K bk c M`. Use `set e := bk.Ep.natDegree`. Take `⟨n₀, hn₀⟩` from `eventually_lt_two_pow (e * l * c) (e * l * M)`. Use `⟨n₀, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hlt` using `hn₀ n hn`.

Establish `h2l : 2 ^ n ≤ l ^ n` using `Nat.pow_le_pow_left (Fact.out : l.Prime).two_le n`. Establish `hle : e * l * (c * n + M) ≤ l ^ n - 1`. Establish `: e * l * (c * n + M) = e * l * c * n + e * l * M` using `by ring`. Use linear arithmetic over natural numbers and integers. Establish `hk` using `pow_dvd_pow_of_dvd (dvd_X_pow bk) (c * n + M)`.

Rewrite `hk` using `[← pow_mul]`. Conclude with `hk.trans (pow_dvd_pow _ hle)`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  intro l _ K bk c M
  set e := bk.Ep.natDegree
  obtain ⟨n₀, hn₀⟩ := eventually_lt_two_pow (e * l * c) (e * l * M)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlt := hn₀ n hn
  have h2l : 2 ^ n ≤ l ^ n := Nat.pow_le_pow_left (Fact.out : l.Prime).two_le n
  have hle : e * l * (c * n + M) ≤ l ^ n - 1 := by
    have : e * l * (c * n + M) = e * l * c * n + e * l * M := by ring
    omega
  have hk := pow_dvd_pow_of_dvd (dvd_X_pow bk) (c * n + M)
  rw [← pow_mul] at hk
  exact hk.trans (pow_dvd_pow _ hle)

end GlobalTheory.AcrisPow
