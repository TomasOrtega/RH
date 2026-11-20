import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.RedInEx

section Abstract

variable {A : Type} [CommRing A] {I : Ideal A} {γ : DividedPowers I} {l s : ℕ}

/- English proof (translation)
Use `le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le γ) fun x hx => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ 1 hx`. Rewrite `h` using `[γ.dpow_one hx]`. Then use the resulting hypothesis.
-/
theorem one_eq (γ : DividedPowers I) : pdP γ 1 = I := by
  refine le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le γ) fun x hx => ?_
  have h := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ 1 hx
  rwa [γ.dpow_one hx] at h

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using h`. Consider the case `succ N ih`. Use `ih ?_` and prove the remaining obligations. Use `hb.tf 1 ((l : A) ^ N * x) (by` as an intermediate fact.

Rewrite using `[one_eq]`. Rewrite using `[pow_succ', mul_assoc] at h)` and apply the resulting hypothesis. Rewrite `this` using `[one_eq]`. Then use the resulting hypothesis.
-/
theorem mem_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x ∈ I) : x ∈ I := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf 1 ((l : A) ^ N * x) (by
      rw [one_eq]
      rwa [pow_succ', mul_assoc] at h)
    rwa [one_eq] at this

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using h`. Consider the case `succ N ih`. Use `ih ?_` and prove the remaining obligations. Use `hb.tf s ((l : A) ^ N * x) (by` as an intermediate fact.

Rewrite using `[hb.nil]`. Rewrite `h` using `[pow_succ', mul_assoc]`. Conclude with `h)`. Rewrite `this` using `[hb.nil]`. Conclude with `this`.
-/
theorem eq_zero_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x = 0) : x = 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf s ((l : A) ^ N * x) (by
      rw [hb.nil]
      rw [pow_succ', mul_assoc] at h
      exact h)
    rw [hb.nil] at this
    exact this

/- English proof (translation)
Take `⟨N, u, hu⟩` from `hb.dv _ k.factorial_ne_zero`. Use `mem_of_pow_mul hb N x ?_` and prove the remaining obligations. Rewrite using `[← hu, mul_comm _ u, mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ h`.
-/
theorem mem_of_fact_mul (hb : TFBase γ l s) (k : ℕ) (x : A) (h : (k.factorial : A) * x ∈ I) : x ∈ I := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  refine mem_of_pow_mul hb N x ?_
  rw [← hu, mul_comm _ u, mul_assoc]
  exact Ideal.mul_mem_left _ _ h

/- English proof (translation)
Take `⟨N, u, hu⟩` from `hb.dv _ k.factorial_ne_zero`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_pow_mul hb N _ ?_` and prove the remaining obligations. Rewrite using `[← hu, mul_comm _ u, mul_assoc, mul_sub, h, sub_self, mul_zero]`.
-/
theorem eq_of_fact_mul (hb : TFBase γ l s) (k : ℕ) {x y : A} (h : (k.factorial : A) * x = (k.factorial : A) * y) :
    x = y := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul hb N _ ?_
  rw [← hu, mul_comm _ u, mul_assoc, mul_sub, h, sub_self, mul_zero]

/- English proof (translation)
Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)`. Establish `haI : a ∈ I` using `mem_of_pow_mul hb n a (by rw [mul_comm, ha]; exact sub_mem hx hy)`. Establish `hc : (l : A) ^ n * a ∈ I` using `Ideal.mul_mem_left _ _ haI`. Establish `e : x = y + (l : A) ^ n * a` using `by rw [mul_comm, ha]; ring`. Rewrite using `[e, γ.dpow_add hy hc, map_sum, Finset.sum_eq_single (k, 0)]`.

Rewrite using `[γ.dpow_zero hc, mul_one]`. Introduce and unpack `⟨i, j⟩ hij hne`. Establish `hj : j ≠ 0`. Introduce and unpack `rfl`. Establish `: i = k` using `by simpa using hij`.

Conclude with `hne (by rw [this])`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (γ.dpow i y * γ.dpow j ((l : A) ^ n * a)) = 0`. Rewrite using `[γ.dpow_mul haI, Ideal.Quotient.eq_zero_iff_mem]`. Take `⟨j, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hj`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (by`.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))`. Introduce `h0`. Conclude with `absurd (by simp) h0`.
-/
theorem dpow_congr (hb : TFBase γ l s) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (h : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) x = Ideal.Quotient.mk _ y) (k : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) (γ.dpow k x) = Ideal.Quotient.mk _ (γ.dpow k y) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have haI : a ∈ I := mem_of_pow_mul hb n a (by rw [mul_comm, ha]; exact sub_mem hx hy)
  have hc : (l : A) ^ n * a ∈ I := Ideal.mul_mem_left _ _ haI
  have e : x = y + (l : A) ^ n * a := by rw [mul_comm, ha]; ring
  rw [e, γ.dpow_add hy hc, map_sum, Finset.sum_eq_single (k, 0)]
  · rw [γ.dpow_zero hc, mul_one]
  · rintro ⟨i, j⟩ hij hne
    have hj : j ≠ 0 := by
      rintro rfl
      have : i = k := by simpa using hij
      exact hne (by rw [this])
    change Ideal.Quotient.mk _ (γ.dpow i y * γ.dpow j ((l : A) ^ n * a)) = 0
    rw [γ.dpow_mul haI, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (by
      rw [pow_succ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · intro h0
    exact absurd (by simp) h0

end Abstract

section Concrete

open PAlg

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A]

def e0 (l : ℕ) [Fact l.Prime] : Acris0 l ≃+* (base l).Acr0 :=
  RingEquiv.ofBijective (base l).cris0 (RL.base_acr (base l) isBase_base).1.1

def lam0 (lam : Acris l →+* A) : (base l).Acr0 →+* A :=
  (lam.comp (algebraMap (Acris0 l) (Acris l))).comp (e0 l).symm.toRingHom

/- English proof (translation)
Establish `h : (e0 l).symm ((base l).cris0 y) = y` using `(e0 l).symm_apply_apply y`. Express the relevant statement in the definitionally equal form `lam (algebraMap (Acris0 l) (Acris l) ((e0 l).symm ((base l).cris0 y))) = _`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem lam0_cris0_eq_lam_of (lam : Acris l →+* A) (y : Acris0 l) :
    lam0 lam ((base l).cris0 y) = lam (AdicCompletion.of _ _ y) := by
  have h : (e0 l).symm ((base l).cris0 y) = y := (e0 l).symm_apply_apply y
  change lam (algebraMap (Acris0 l) (Acris l) ((e0 l).symm ((base l).cris0 y))) = _
  rw [h]
  rfl

/- English proof (translation)
Establish `h : algebraMap (base l).W (base l).Acr0 ((base l).sW w) = (base l).cris0 (algebraMap (Ainf l) (Acris0 l) w)` using `Subtype.ext (awayW_algebraMap (base l).s w).symm`. Rewrite using `[h, lam0_cris0_eq_lam_of, AdicCompletion.algebraMap_apply]`.
-/
theorem lam0_algebraMap_sW_eq_lam_algebraMap (lam : Acris l →+* A) (w : Ainf l) :
    lam0 lam (algebraMap (base l).W (base l).Acr0 ((base l).sW w)) = lam (algebraMap (Ainf l) (Acris l) w) := by
  have h : algebraMap (base l).W (base l).Acr0 ((base l).sW w) = (base l).cris0 (algebraMap (Ainf l) (Acris0 l) w) :=
    Subtype.ext (awayW_algebraMap (base l).s w).symm
  rw [h, lam0_cris0_eq_lam_of, AdicCompletion.algebraMap_apply]

def rho (lam : Acris l →+* A) (n : ℕ) : (base l).Acr n →+* A ⧸ Ideal.span {(l : A) ^ n} :=
  ((base l).cris n).liftOfSurjective ((RL.base_acr (base l) isBase_base).2 n).1
    ⟨(Ideal.Quotient.mk _).comp lam, fun x hx => by
      rw [((RL.base_acr (base l) isBase_base).2 n).2] at hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have hz : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) ((l : A) ^ n) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_mul, map_pow, map_natCast, hz, mul_zero]⟩

/- English proof (translation)
The claim follows from `RingHom.liftOfSurjective_comp_apply _ _ _ c`.
-/
theorem rho_cris (lam : Acris l →+* A) (n : ℕ) (c : Acris l) :
    rho lam n ((base l).cris n c) = Ideal.Quotient.mk _ (lam c) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ c

/- English proof (translation)
Take `⟨y, rfl⟩` from `(e0 l).surjective y`. Express the relevant statement in the definitionally equal form `rho lam n ((base l).mkAcr n ((base l).cris0 y)) = Ideal.Quotient.mk _ (lam0 lam ((base l).cris0 y))`. Rewrite using `[← cris_of, rho_cris, lam0_cris0_eq_lam_of]`.
-/
theorem rho_mk (lam : Acris l →+* A) (n : ℕ) (y : (base l).Acr0) :
    rho lam n ((base l).mkAcr n y) = Ideal.Quotient.mk _ (lam0 lam y) := by
  obtain ⟨y, rfl⟩ := (e0 l).surjective y
  change rho lam n ((base l).mkAcr n ((base l).cris0 y)) = Ideal.Quotient.mk _ (lam0 lam ((base l).cris0 y))
  rw [← cris_of, rho_cris, lam0_cris0_eq_lam_of]

variable {I : Ideal A} {γ : DividedPowers I} {s : ℕ}

/- English proof (translation)
Establish `: (base l).Fil0 1 ≤ I.comap (lam0 lam)`. Rewrite using `[Fil0, Ideal.span_le]`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Use `mem_of_fact_mul hb k _ ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (lam0 lam), ← map_mul, (RL.filtration_multiplicative (base l)).2.2.1 k, map_pow]`.

Use `Ideal.pow_mem_of_mem _ ?_ _ hk` and prove the remaining obligations. Rewrite using `[show (base l).xi = (base l).sW (xi0 l) from rfl, lam0_algebraMap_sW_eq_lam_algebraMap]`. Conclude with `hξ`. Conclude with `this hx`.
-/
theorem lam0_mem_of_mem_fil0_one (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) :
    lam0 lam x ∈ I := by
  have : (base l).Fil0 1 ≤ I.comap (lam0 lam) := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_of_fact_mul hb k _ ?_
    rw [← map_natCast (lam0 lam), ← map_mul, (RL.filtration_multiplicative (base l)).2.2.1 k, map_pow]
    refine Ideal.pow_mem_of_mem _ ?_ _ hk
    rw [show (base l).xi = (base l).sW (xi0 l) from rfl, lam0_algebraMap_sW_eq_lam_algebraMap]
    exact hξ
  exact this hx

/- English proof (translation)
Use `eq_of_fact_mul hb k ?_` and prove the remaining obligations. Rewrite using `[γ.factorial_mul_dpow_eq_pow (lam0_mem_of_mem_fil0_one hb lam hξ hx), ← map_natCast (lam0 lam), ← map_mul, hz, map_pow]`.
-/
theorem lam0_dpow (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x z : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) (k : ℕ)
    (hz : (k.factorial : (base l).Acr0) * z = x ^ k) : lam0 lam z = γ.dpow k (lam0 lam x) := by
  refine eq_of_fact_mul hb k ?_
  rw [γ.factorial_mul_dpow_eq_pow (lam0_mem_of_mem_fil0_one hb lam hξ hx), ← map_natCast (lam0 lam), ← map_mul, hz, map_pow]

/- English proof (translation)
Break down `eq_or_ne k 0 with rfl | hk` into its components or cases. Conclude with `⟨1, by simp⟩`. Take `⟨z, -, hz⟩` from `(RL.pdi (base l)).1 x hx k hk`. Conclude with `⟨z, hz⟩`.
-/
theorem exists_unit_one_add_generator (x : (base l).Acr0) (hx : x ∈ (base l).Fil0 1) (k : ℕ) :
    ∃ z : (base l).Acr0, (k.factorial : (base l).Acr0) * z = x ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨1, by simp⟩
  · obtain ⟨z, -, hz⟩ := (RL.pdi (base l)).1 x hx k hk
    exact ⟨z, hz⟩

end Concrete

/- English proof (translation)
Introduce `l _ K A _ _ I γ s lam hb hξ hO n`. Establish `hfil : ∀ x ∈ (PAlg.base l).Fil n 1, ∃ x₀ ∈ (PAlg.base l).Fil0 1, (PAlg.base l).mkAcr n x₀ = x`. Introduce `x hx`. Rewrite `hx` using `[((PAlg.base l).isPd_pdFil n).1]`. Conclude with `(Ideal.mem_map_iff_of_surjective _ ((PAlg.base l).mkAcr_surjective n)).1 hx`.

Use `⟨{ hl := (Fact.out : l.Prime).ne_zero, ρ := rho lam n, mem := ?_, dp := ?_, hκ := ?_ }, rho_cris lam n⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨x₀, hx₀, rfl⟩` from `hfil x hx`. Conclude with `⟨lam0 lam x₀, lam0_mem_of_mem_fil0_one hb lam hξ hx₀, rho_mk lam n x₀⟩`. Introduce `k x hx y hy e`.

Take `⟨x₀, hx₀, rfl⟩` from `hfil x hx`. Take `⟨z, hz⟩` from `exists_unit_one_add_generator x₀ hx₀ k`. Establish `e1 : (B.DD false (PAlg.base l) n).dpow k ((PAlg.base l).mkAcr n x₀) = (PAlg.base l).mkAcr n z` using `((PAlg.base l).isPd_pdFil n).2 k x₀ z hx₀ hz`. Rewrite using `[e1, rho_mk, lam0_dpow hb lam hξ hx₀ k hz]`. Rewrite `e` using `[rho_mk]`.

Conclude with `dpow_congr hb (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) hy e k`. Introduce `a r h`. Take `⟨w, hw⟩` from `IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (okToOC l K a)`. Establish `h1 : B.κb (okToOC l K) false n a = Ideal.Quotient.mk _ ((PAlg.base l).toAcr n ((PAlg.base l).sW w))`. Express the relevant statement in the definitionally equal form `B.uJ false (PAlg.base l) n ((PAlg.base l).oC (okToOC l K a)) = _`.

Rewrite using `[← hw, PAlg.oC_theta0, B.uJ_th]`. Rewrite `h` using `[h1]`. Establish `h2 : r - (PAlg.base l).toAcr n ((PAlg.base l).sW w) ∈ (PAlg.base l).Fil n 1` using `Ideal.Quotient.eq.1 h.symm`. Take `⟨x₀, hx₀, e⟩` from `hfil _ h2`. Establish `h3 : rho lam n r = Ideal.Quotient.mk _ (lam (algebraMap (Ainf l) (Acris l) w) + lam0 lam x₀)`.

Rewrite using `[map_add, ← rho_mk, e, ← PAlg.cris_algebraMap, ← rho_cris, PAlg.cris_algebraMap, map_sub, add_sub_cancel]`. Use `⟨lam0 lam x₀ - (algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w)), sub_mem (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) (hO a w hw), ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem redIn_ex : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {A : Type} [CommRing A] [Algebra (OK l K) A]
    {I : Ideal A} (γ : DividedPowers I) (s : ℕ) (lam : Acris l →+* A), TFBase γ l s →
    lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I →
    (∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w) ∈ I) →
    ∀ n : ℕ, ∃ d : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) γ l n,
      ∀ c, d.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (lam c) := by
  intro l _ K A _ _ I γ s lam hb hξ hO n
  have hfil : ∀ x ∈ (PAlg.base l).Fil n 1, ∃ x₀ ∈ (PAlg.base l).Fil0 1, (PAlg.base l).mkAcr n x₀ = x := by
    intro x hx
    rw [((PAlg.base l).isPd_pdFil n).1] at hx
    exact (Ideal.mem_map_iff_of_surjective _ ((PAlg.base l).mkAcr_surjective n)).1 hx
  refine ⟨{ hl := (Fact.out : l.Prime).ne_zero, ρ := rho lam n, mem := ?_, dp := ?_, hκ := ?_ }, rho_cris lam n⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    exact ⟨lam0 lam x₀, lam0_mem_of_mem_fil0_one hb lam hξ hx₀, rho_mk lam n x₀⟩
  · intro k x hx y hy e
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    obtain ⟨z, hz⟩ := exists_unit_one_add_generator x₀ hx₀ k
    have e1 : (B.DD false (PAlg.base l) n).dpow k ((PAlg.base l).mkAcr n x₀) = (PAlg.base l).mkAcr n z :=
      ((PAlg.base l).isPd_pdFil n).2 k x₀ z hx₀ hz
    rw [e1, rho_mk, lam0_dpow hb lam hξ hx₀ k hz]
    rw [rho_mk] at e
    exact dpow_congr hb (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) hy e k
  · intro a r h
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (okToOC l K a)
    have h1 : B.κb (okToOC l K) false n a = Ideal.Quotient.mk _ ((PAlg.base l).toAcr n ((PAlg.base l).sW w)) := by
      change B.uJ false (PAlg.base l) n ((PAlg.base l).oC (okToOC l K a)) = _
      rw [← hw, PAlg.oC_theta0, B.uJ_th]
    rw [h1] at h
    have h2 : r - (PAlg.base l).toAcr n ((PAlg.base l).sW w) ∈ (PAlg.base l).Fil n 1 :=
      Ideal.Quotient.eq.1 h.symm
    obtain ⟨x₀, hx₀, e⟩ := hfil _ h2
    have h3 : rho lam n r = Ideal.Quotient.mk _ (lam (algebraMap (Ainf l) (Acris l) w) + lam0 lam x₀) := by
      rw [map_add, ← rho_mk, e, ← PAlg.cris_algebraMap, ← rho_cris, PAlg.cris_algebraMap, map_sub, add_sub_cancel]
    refine ⟨lam0 lam x₀ - (algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w)),
      sub_mem (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) (hO a w hw), ?_⟩
    rw [h3]
    congr 1
    ring

end GlobalTheory.CompanionTheory.RedInEx
