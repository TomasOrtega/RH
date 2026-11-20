import Mathlib
import GroundTheory.PAdicHodge.BCrisEigen
import GroundTheory.PAdicHodge.SenTateCharacters
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Introduce `y hy`. Establish `hc : ‖(y : ℂ_[p])‖ ≤ 1` using `by rwa [PadicComplex.norm_extends]`. Take `⟨k, hk⟩` from `eventually_approx_pow hc 1`. Take `⟨u, hu, hyu⟩` from `hk k le_rfl`. Use `set n := p ^ k with hn`.

Establish `hpn : ‖(p : ℂ_[p])‖ = ‖(p : PadicAlgCl p)‖`. Rewrite using `[← PadicComplex.norm_extends]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hd : ‖y ^ n - u‖ ≤ ‖(p : PadicAlgCl p)‖`.

Rewrite using `[← PadicComplex.norm_extends, ← hpn]`. Establish `e : ((y ^ n - u : PadicAlgCl p) : ℂ_[p]) = (y : ℂ_[p]) ^ n - (u : ℂ_[p])`. Simplify using `only [UniformSpace.Completion.coe_sub, PadicComplex.coe_eq, map_pow]`. Rewrite using `[e]`. Simplify using `using hyu`.

Establish `hσn : ‖σ y ^ n - y ^ n‖ ≤ ‖(p : PadicAlgCl p)‖`. Establish `e : σ y ^ n - y ^ n = σ (y ^ n - u) - (y ^ n - u)`. Rewrite using `[map_sub, map_pow, hσ u hu]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `(norm_sub_le_max_of_ultrametric _ _).trans (max_le ?_ hd)` and prove the remaining obligations. Rewrite using `[norm_gal_apply]`. Conclude with `hd`. Establish `hσy : ‖σ y‖ ≤ 1` using `by rwa [norm_gal_apply]`. Establish `hdiff : ‖σ y - y‖ ≤ 1` using `(norm_sub_le_max_of_ultrametric _ _).trans (max_le hσy hy)`.

Set `a : normInteger (PadicAlgCl p)` to `⟨σ y - y, mem_normInteger.2 hdiff⟩`. Set `b : normInteger (PadicAlgCl p)` to `⟨y, mem_normInteger.2 hy⟩`. Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hp.out a b k`. Establish `hr'` using `congrArg (fun z : normInteger (PadicAlgCl p) => (z : PadicAlgCl p)) hr`. Simplify using `only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, a, b, sub_add_cancel] at hr'`.

Establish `e : (σ y - y) ^ n = (σ y ^ n - y ^ n) - (p : PadicAlgCl p) * (σ y - y) * y * r`. Rewrite using `[hn, hr']`. Expand and normalize the polynomial expressions, which then agree. Establish `hr1 : ‖(r : PadicAlgCl p)‖ ≤ 1` using `mem_normInteger.1 r.2`. Establish `hlt : ‖σ y - y‖ ^ n < 1`.

Rewrite using `[← norm_pow, e]`. Use `(norm_sub_le_max_of_ultrametric (σ y ^ n - y ^ n) ((p : PadicAlgCl p) * (σ y - y) * y * r)).trans_lt (max_lt (hσn.trans_lt norm_natCast_p_algCl_lt_one) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, norm_mul]`. Rewrite using `[mul_assoc, mul_assoc]`. Use `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg (p : PadicAlgCl p)) ?_) (norm_natCast_p_algCl_lt_one (p := p))` and prove the remaining obligations.

Conclude with `mul_le_one₀ hdiff (by positivity) (mul_le_one₀ hy (norm_nonneg _) hr1)`. Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hp.out.ne_zero)).1 hlt`.
-/
theorem mem_inertiaGal_of_forall_unramifiedClosure {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {σ : Gal(PadicAlgCl p/K)} (hσ : ∀ u ∈ unramifiedClosure p, σ u = u) : σ ∈ inertiaGal K := by
  intro y hy
  have hc : ‖(y : ℂ_[p])‖ ≤ 1 := by rwa [PadicComplex.norm_extends]
  obtain ⟨k, hk⟩ := eventually_approx_pow hc 1
  obtain ⟨u, hu, hyu⟩ := hk k le_rfl
  set n := p ^ k with hn
  have hpn : ‖(p : ℂ_[p])‖ = ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.norm_extends]
    congr 1
    simp
  have hd : ‖y ^ n - u‖ ≤ ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.norm_extends, ← hpn]
    have e : ((y ^ n - u : PadicAlgCl p) : ℂ_[p]) = (y : ℂ_[p]) ^ n - (u : ℂ_[p]) := by
      simp only [UniformSpace.Completion.coe_sub, PadicComplex.coe_eq, map_pow]
    rw [e]
    simpa using hyu
  have hσn : ‖σ y ^ n - y ^ n‖ ≤ ‖(p : PadicAlgCl p)‖ := by
    have e : σ y ^ n - y ^ n = σ (y ^ n - u) - (y ^ n - u) := by
      rw [map_sub, map_pow, hσ u hu]
      ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans (max_le ?_ hd)
    rw [norm_gal_apply]
    exact hd
  have hσy : ‖σ y‖ ≤ 1 := by rwa [norm_gal_apply]
  have hdiff : ‖σ y - y‖ ≤ 1 := (norm_sub_le_max_of_ultrametric _ _).trans (max_le hσy hy)
  let a : normInteger (PadicAlgCl p) := ⟨σ y - y, mem_normInteger.2 hdiff⟩
  let b : normInteger (PadicAlgCl p) := ⟨y, mem_normInteger.2 hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out a b k
  have hr' := congrArg (fun z : normInteger (PadicAlgCl p) => (z : PadicAlgCl p)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, a, b,
    sub_add_cancel] at hr'
  have e : (σ y - y) ^ n = (σ y ^ n - y ^ n) - (p : PadicAlgCl p) * (σ y - y) * y * r := by
    rw [hn, hr']
    ring
  have hr1 : ‖(r : PadicAlgCl p)‖ ≤ 1 := mem_normInteger.1 r.2
  have hlt : ‖σ y - y‖ ^ n < 1 := by
    rw [← norm_pow, e]
    refine (norm_sub_le_max_of_ultrametric (σ y ^ n - y ^ n)
      ((p : PadicAlgCl p) * (σ y - y) * y * r)).trans_lt (max_lt (hσn.trans_lt
      norm_natCast_p_algCl_lt_one) ?_)
    rw [norm_mul, norm_mul, norm_mul]
    rw [mul_assoc, mul_assoc]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg (p : PadicAlgCl p)) ?_)
      (norm_natCast_p_algCl_lt_one (p := p))
    exact mul_le_one₀ hdiff (by positivity) (mul_le_one₀ hy (norm_nonneg _) hr1)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hp.out.ne_zero)).1 hlt

namespace ACris

/- English proof (translation)
Introduce `K _ η hη x hx0 hx`. Establish `hfin` using `finite_image_inertiaGal_of_invariant_padic K η⁻¹ (show Continuous fun σ => (η σ)⁻¹ from hη.inv) ⟨x, hx0, fun σ => by`. Rewrite using `[hx σ, ← mul_assoc, ← map_mul, MonoidHom.inv_apply, Units.inv_mul, map_one, one_mul]⟩`. Use `(hfin.image (·⁻¹)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`.

Conclude with `⟨η⁻¹ σ, ⟨σ, mem_inertiaGal_of_forall_unramifiedClosure hσ, rfl⟩, by simp⟩`.
-/
theorem senTateCharacters : SenTateCharacters p := by
  intro K _ η hη x hx0 hx
  have hfin := finite_image_inertiaGal_of_invariant_padic K η⁻¹
    (show Continuous fun σ => (η σ)⁻¹ from hη.inv) ⟨x, hx0, fun σ => by
      rw [hx σ, ← mul_assoc, ← map_mul, MonoidHom.inv_apply, Units.inv_mul, map_one, one_mul]⟩
  refine (hfin.image (·⁻¹)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  exact ⟨η⁻¹ σ, ⟨σ, mem_inertiaGal_of_forall_unramifiedClosure hσ, rfl⟩, by simp⟩

end ACris

end GroundTheory.PAdicHodge
