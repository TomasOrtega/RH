import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemPuncturedRingIffPowerSeriesPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)

noncomputable section

namespace GlobalTheory.Conv

def cuspRadius (T : ℝ) : ℝ := Real.exp (-(2 * Real.pi * T))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cuspRadius_pos (T : ℝ) : 0 < cuspRadius T := Real.exp_pos _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cuspRadius_strictAnti : StrictAnti cuspRadius := by
  intro a b h
  exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities.
-/
theorem exists_cuspRadius_eq {ε : ℝ} (hε : 0 < ε) : ∃ T, cuspRadius T = ε := by
  refine ⟨-Real.log ε / (2 * Real.pi), ?_⟩
  have h2 : 2 * Real.pi * (-Real.log ε / (2 * Real.pi)) = -Real.log ε := by
    field_simp
  rw [cuspRadius, h2, neg_neg, Real.exp_log hε]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eTwoPi_ne_zero (w : ℂ) : eTwoPi w ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem norm_eTwoPi (w : ℂ) : ‖eTwoPi w‖ = cuspRadius w.im := by
  show ‖Complex.exp (2 * Real.pi * Complex.I * w)‖ = Real.exp (-(2 * Real.pi * w.im))
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem differentiable_eTwoPi : Differentiable ℂ eTwoPi := by
  show Differentiable ℂ fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * w)
  fun_prop

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_eTwoPi_eq {v : ℂ} (hv : v ≠ 0) : ∃ w, eTwoPi w = v := by
  refine ⟨Complex.log v / (2 * Real.pi * Complex.I), ?_⟩
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  show Complex.exp (2 * Real.pi * Complex.I * (Complex.log v / (2 * Real.pi * Complex.I))) = v
  rw [mul_div_cancel₀ _ hc, Complex.exp_log hv]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Supply the required witnesses or components.
-/
theorem eTwoPi_mem_puncturedDisc {T : ℝ} {w : ℂ} :
    eTwoPi w ∈ puncturedDisc (cuspRadius T) ↔ T < w.im := by
  rw [mem_puncturedDisc, norm_eTwoPi]
  have key : cuspRadius w.im < cuspRadius T ↔ T < w.im := by
    rw [cuspRadius, cuspRadius, Real.exp_lt_exp]
    constructor <;> intro h <;> nlinarith [Real.pi_pos]
  exact ⟨fun h => key.1 h.2, fun h => ⟨eTwoPi_ne_zero w, key.2 h⟩⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem eventually_iff_eTwoPi {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔ ∃ T : ℝ, ∀ w : ℂ, T < w.im → p (eTwoPi w) := by
  rw [eventually_iff_exists_puncturedDisc]
  constructor
  · rintro ⟨ε, hε, h⟩
    obtain ⟨T, rfl⟩ := exists_cuspRadius_eq hε
    exact ⟨T, fun w hw => h _ (eTwoPi_mem_puncturedDisc.2 hw)⟩
  · rintro ⟨T, h⟩
    refine ⟨cuspRadius T, cuspRadius_pos T, fun v hv => ?_⟩
    obtain ⟨w, rfl⟩ := exists_eTwoPi_eq (mem_puncturedDisc.1 hv).1
    exact h w (eTwoPi_mem_puncturedDisc.1 hv)

def halfRing (T : ℝ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {s | ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n}
  mul_mem' hf hg w hw := (hasSum_mul_laurent (eTwoPi_ne_zero w) (hf w hw) (hg w hw)).summable
  add_mem' hf hg w hw := by simpa [add_mul] using (hf w hw).add (hg w hw)
  algebraMap_mem' c w hw :=
    (puncturedRing _).algebraMap_mem c _ (eTwoPi_mem_puncturedDisc.2 hw)

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_halfRing {T : ℝ} {s : ℂ⸨X⸩} :
    s ∈ halfRing T ↔ ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n := Iff.rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem mem_halfRing_iff_puncturedRing {T : ℝ} {s : ℂ⸨X⸩} :
    s ∈ halfRing T ↔ s ∈ puncturedRing (cuspRadius T) := by
  rw [mem_halfRing, mem_puncturedRing]
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := exists_eTwoPi_eq (mem_puncturedDisc.1 hv).1
    exact h w (eTwoPi_mem_puncturedDisc.1 hv)
  · intro h w hw
    exact h _ (eTwoPi_mem_puncturedDisc.2 hw)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem halfRing_eq (T : ℝ) : halfRing T = puncturedRing (cuspRadius T) :=
  Subalgebra.ext fun _ => mem_halfRing_iff_puncturedRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfRing_mono : Monotone halfRing := by
  intro a b h
  rw [halfRing_eq, halfRing_eq]
  exact puncturedRing_anti (StrictAnti.antitone cuspRadius_strictAnti h)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem single_mem_halfRing (T : ℝ) (m : ℤ) (c : ℂ) :
    (HahnSeries.single m c : ℂ⸨X⸩) ∈ halfRing T := by
  rw [halfRing_eq]
  exact single_mem_puncturedRing _ m c

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem coe_mem_halfRing {T : ℝ} {p : ℂ⟦X⟧} :
    (p : ℂ⸨X⸩) ∈ halfRing T ↔ ∀ w : ℂ, T < w.im → ∃ x, SumsAt p w x := by
  rw [mem_halfRing]
  refine forall₂_congr fun w _ => ⟨fun h => ⟨_, hasSum_coe_iff.1 h.hasSum⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact (hasSum_coe_iff.2 hx).summable

def ev (T : ℝ) (w : ℂ) (hw : T < w.im) : halfRing T →ₐ[ℂ] ℂ where
  toFun s := lsum s (eTwoPi w)
  map_one' := by simpa using lsum_single 0 1 (eTwoPi w)
  map_mul' f g := (hasSum_mul_laurent (eTwoPi_ne_zero w) (f.2 w hw) (g.2 w hw)).tsum_eq
  map_zero' := by simp [lsum]
  map_add' f g := by
    simpa [lsum, add_mul] using (f.2 w hw).tsum_add (g.2 w hw)
  commutes' c := lsum_algebraMap c _

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem ev_apply {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    ev T w hw s = lsum s (eTwoPi w) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasSum_ev {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) (ev T w hw s) :=
  (s.2 w hw).hasSum

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ev_eq_of_hasSum {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) {x : ℂ}
    (h : HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) x) : ev T w hw s = x :=
  (hasSum_ev hw s).unique h

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ev_congr {T T' : ℝ} {w : ℂ} (hw : T < w.im) (hw' : T' < w.im) {s : halfRing T}
    {s' : halfRing T'} (h : (s : ℂ⸨X⸩) = s') : ev T w hw s = ev T' w hw' s' := by
  rw [ev_apply, ev_apply, h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ev_single {T : ℝ} {w : ℂ} (hw : T < w.im) (m : ℤ) (c : ℂ) :
    ev T w hw ⟨HahnSeries.single m c, single_mem_halfRing T m c⟩ = c * eTwoPi w ^ m :=
  lsum_single m c _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumsAt_ev {T : ℝ} {w : ℂ} (hw : T < w.im) {p : ℂ⟦X⟧} (hp : (p : ℂ⸨X⸩) ∈ halfRing T) :
    SumsAt p w (ev T w hw ⟨p, hp⟩) := hasSum_coe_iff.1 (hasSum_ev hw ⟨p, hp⟩)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sumsAt_ev_of_eq {T : ℝ} {w : ℂ} (hw : T < w.im) {p : ℂ⟦X⟧} {s : halfRing T}
    (h : (p : ℂ⸨X⸩) = s) : SumsAt p w (ev T w hw s) := by
  have hp : (p : ℂ⸨X⸩) ∈ halfRing T := h ▸ s.2
  rw [ev_congr hw hw (s' := (⟨p, hp⟩ : halfRing T)) h.symm]
  exact sumsAt_ev hw hp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumsAt_iff {p : ℂ⟦X⟧} {w x : ℂ} :
    SumsAt p w x ↔ HasSum (fun n : ℤ => (p : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) x :=
  hasSum_coe_iff.symm

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem analyticOnNhd_lsum_eTwoPi {T : ℝ} {s : ℂ⸨X⸩} (hs : s ∈ halfRing T) :
    AnalyticOnNhd ℂ (fun w => lsum s (eTwoPi w)) {w : ℂ | T < w.im} := by
  rw [mem_halfRing_iff_puncturedRing] at hs
  intro w hw
  have h1 := analyticOnNhd_lsum hs (eTwoPi w) (eTwoPi_mem_puncturedDisc.2 hw)
  exact h1.comp (differentiable_eTwoPi.analyticAt w)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem differentiableOn_lsum_eTwoPi {T : ℝ} {s : ℂ⸨X⸩} (hs : s ∈ halfRing T) :
    DifferentiableOn ℂ (fun w => lsum s (eTwoPi w)) {w : ℂ | T < w.im} :=
  (analyticOnNhd_lsum_eTwoPi hs).differentiableOn

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem differentiableOn_of_eq_ev {T : ℝ} (s : halfRing T) {F : ℂ → ℂ}
    (hF : ∀ w (hw : T < w.im), F w = ev T w hw s) : DifferentiableOn ℂ F {w : ℂ | T < w.im} :=
  (differentiableOn_lsum_eTwoPi s.2).congr fun w hw => hF w hw

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfRing_le_convLaurent (T : ℝ) : halfRing T ≤ convLaurent.toSubalgebra := by
  rw [halfRing_eq]
  exact puncturedRing_le_convLaurent (cuspRadius_pos T)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem mem_convLaurent_iff_halfRing {s : ℂ⸨X⸩} : s ∈ convLaurent ↔ ∃ T, s ∈ halfRing T := by
  rw [mem_convLaurent]
  constructor
  · rintro ⟨ε, hε, h⟩
    obtain ⟨T, rfl⟩ := exists_cuspRadius_eq hε
    exact ⟨T, mem_halfRing_iff_puncturedRing.2 h⟩
  · rintro ⟨T, h⟩
    exact ⟨_, cuspRadius_pos T, mem_halfRing_iff_puncturedRing.1 h⟩

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem iUnion_halfRing : ⋃ T, (halfRing T : Set ℂ⸨X⸩) = convLaurent := by
  ext s
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  exact mem_convLaurent_iff_halfRing.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem eventually_mem_halfRing {s : ℂ⸨X⸩} (hs : s ∈ convLaurent) :
    ∀ᶠ T in atTop, s ∈ halfRing T := by
  obtain ⟨T, hT⟩ := mem_convLaurent_iff_halfRing.1 hs
  exact Filter.eventually_atTop.2 ⟨T, fun T' h => halfRing_mono h hT⟩

def halfIncl (T : ℝ) : halfRing T →ₐ[ℂ] convLaurent :=
  Subalgebra.inclusion (halfRing_le_convLaurent T)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_halfIncl {T : ℝ} (s : halfRing T) : (halfIncl T s : ℂ⸨X⸩) = s := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_lsum_eTwoPi_ne_zero {s : ℂ⸨X⸩} (hs : s ∈ convLaurent) (h0 : s ≠ 0) :
    ∃ T : ℝ, ∀ w : ℂ, T < w.im → lsum s (eTwoPi w) ≠ 0 :=
  eventually_iff_eTwoPi.1 (eventually_lsum_ne_zero hs h0)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_ev_ne_zero {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s ≠ 0 := by
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  obtain ⟨T₁, hT₁⟩ := exists_lsum_eTwoPi_ne_zero (halfRing_le_convLaurent T s.2) hs0
  exact ⟨max T T₁, le_max_left _ _, fun w _ hw' => hT₁ w (lt_of_le_of_lt (le_max_right _ _) hw')⟩

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem eq_zero_of_ev_eq_zero {T : ℝ} {s : halfRing T} (T' : ℝ)
    (h : ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s = 0) : s = 0 := by
  by_contra h0
  obtain ⟨T'', hT'', h1⟩ := exists_ev_ne_zero h0
  let w : ℂ := ⟨0, max T'' T' + 1⟩
  have hwT : T < w.im := by
    show T < max T'' T' + 1
    linarith [le_max_left T'' T']
  have hw1 : T'' < w.im := by
    show T'' < max T'' T' + 1
    linarith [le_max_left T'' T']
  have hw2 : T' < w.im := by
    show T' < max T'' T' + 1
    linarith [le_max_right T'' T']
  exact h1 w hwT hw1 (h w hwT hw2)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_inv_mem_halfRing {T : ℝ} (s : halfRing T) :
    ∃ T' ≥ T, (s : ℂ⸨X⸩)⁻¹ ∈ halfRing T' := by
  have h1 : ((s : ℂ⸨X⸩))⁻¹ ∈ convLaurent := convLaurent.inv_mem (halfRing_le_convLaurent T s.2)
  obtain ⟨T', hT'⟩ := ((eventually_mem_halfRing h1).and (eventually_ge_atTop T)).exists
  exact ⟨T', hT'.2, hT'.1⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_isUnit_halfRing {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) :
    ∃ T', ∃ h : T ≤ T', IsUnit (Subalgebra.inclusion (halfRing_mono h) s) := by
  obtain ⟨T', hT', hinv⟩ := exists_inv_mem_halfRing s
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  refine ⟨T', hT', isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩⟩
  show (s : ℂ⸨X⸩) * (s : ℂ⸨X⸩)⁻¹ = 1
  exact mul_inv_cancel₀ hs0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_forall_mem_halfRing {S : Set ℂ⸨X⸩} (hS : S.Finite)
    (h : ∀ s ∈ S, s ∈ convLaurent) : ∃ T, ∀ s ∈ S, s ∈ halfRing T :=
  ((Filter.eventually_all_finite hS).2 fun s hs => eventually_mem_halfRing (h s hs)).exists

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_le_halfRing {A : Subalgebra ℂ ℂ⸨X⸩} (hA : A.FG)
    (h : A ≤ convLaurent.toSubalgebra) : ∃ T, A ≤ halfRing T := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, hT⟩ := exists_forall_mem_halfRing S.finite_toSet
    (fun s hs => h (Algebra.subset_adjoin hs))
  exact ⟨T, Algebra.adjoin_le fun s hs => hT s hs⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem exists_forall_map_mem_halfRing {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]
    [Algebra.FiniteType S A] (φ : A →+* convLaurent) {T : ℝ}
    (hS : ∀ c : S, (φ (algebraMap S A c) : ℂ⸨X⸩) ∈ halfRing T) :
    ∃ T' ≥ T, ∀ a, (φ a : ℂ⸨X⸩) ∈ halfRing T' := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := S) (A := A)
  obtain ⟨T₁, hT₁⟩ := exists_forall_mem_halfRing
    (S := (fun a => (φ a : ℂ⸨X⸩)) '' (t : Set A)) (t.finite_toSet.image _)
    (by rintro _ ⟨a, -, rfl⟩; exact (φ a).2)
  refine ⟨max T T₁, le_max_left _ _, fun a => ?_⟩
  have key : (⊤ : Subalgebra S A).toSubring ≤
      (halfRing (max T T₁)).toSubring.comap ((convLaurent.val : convLaurent →+* ℂ⸨X⸩).comp φ) := by
    rw [← ht, Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ha)
    · exact halfRing_mono (le_max_left _ _) (hS c)
    · exact halfRing_mono (le_max_right _ _) (hT₁ _ ⟨_, ha, rfl⟩)
  exact key (show a ∈ (⊤ : Subalgebra S A).toSubring from Algebra.mem_top (R := S))

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_factor_halfRing_over {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]
    [Algebra.FiniteType S A] (b : S →+* ℂ) (φ : A →+* convLaurent)
    (hφ : φ.comp (algebraMap S A) = (algebraMap ℂ convLaurent).comp b) (T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ ψ : A →+* halfRing T, (halfIncl T : halfRing T →+* convLaurent).comp ψ = φ ∧
      ψ.comp (algebraMap S A) = (algebraMap ℂ (halfRing T)).comp b := by
  obtain ⟨T, hT, hmem⟩ := exists_forall_map_mem_halfRing φ (T := T₀) fun c => by
    have hc : φ (algebraMap S A c) = algebraMap ℂ convLaurent (b c) := RingHom.congr_fun hφ c
    rw [hc]
    exact (halfRing T₀).algebraMap_mem (b c)
  refine ⟨T, hT, RingHom.codRestrict ((convLaurent.val : convLaurent →+* ℂ⸨X⸩).comp φ)
    (halfRing T) hmem, RingHom.ext fun a => rfl, RingHom.ext fun c => Subtype.ext ?_⟩
  have hc : φ (algebraMap S A c) = algebraMap ℂ convLaurent (b c) := RingHom.congr_fun hφ c
  show (φ (algebraMap S A c) : ℂ⸨X⸩) = algebraMap ℂ ℂ⸨X⸩ (b c)
  rw [hc]
  rfl

def locRing (T : ℝ) (s : halfRing T) : Subalgebra (halfRing T) ℂ⸨X⸩ :=
  Algebra.adjoin (halfRing T) {(s : ℂ⸨X⸩)⁻¹}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coe_mem_locRing {T : ℝ} (s f : halfRing T) : (f : ℂ⸨X⸩) ∈ locRing T s :=
  (locRing T s).algebraMap_mem f

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inv_mem_locRing {T : ℝ} (s : halfRing T) : (s : ℂ⸨X⸩)⁻¹ ∈ locRing T s :=
  Algebra.subset_adjoin (Set.mem_singleton _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_algebraMap_locRing {T : ℝ} (s f : halfRing T) :
    (algebraMap (halfRing T) (locRing T s) f : ℂ⸨X⸩) = f := rfl

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locRing_toSubring {T : ℝ} (s : halfRing T) :
    (locRing T s).toSubring = Subring.closure ((halfRing T : Set ℂ⸨X⸩) ∪ {(s : ℂ⸨X⸩)⁻¹}) := by
  have hr : Set.range (algebraMap (halfRing T) ℂ⸨X⸩) = (halfRing T : Set ℂ⸨X⸩) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [locRing, Algebra.adjoin_eq_ring_closure, hr]

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Proceed by induction.

Treat this case separately. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Treat this case separately. Supply the required witnesses or components.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_locRing {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) {x : ℂ⸨X⸩} :
    x ∈ locRing T s ↔ ∃ (n : ℕ) (f : halfRing T), x * (s : ℂ⸨X⸩) ^ n = f := by
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  constructor
  · intro hx
    unfold locRing at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact ⟨1, 1, by simp [hs0]⟩
    | algebraMap r =>
      exact ⟨0, r, by rw [pow_zero, mul_one]; rfl⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨n, f, hf⟩ := ihx
      obtain ⟨m, g, hg⟩ := ihy
      refine ⟨n + m, f * s ^ m + g * s ^ n, ?_⟩
      push_cast
      rw [← hf, ← hg]
      ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨n, f, hf⟩ := ihx
      obtain ⟨m, g, hg⟩ := ihy
      refine ⟨n + m, f * g, ?_⟩
      push_cast
      rw [← hf, ← hg]
      ring
  · rintro ⟨n, f, hf⟩
    have hx : x = f * ((s : ℂ⸨X⸩)⁻¹) ^ n := by
      rw [← hf, mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]
    rw [hx]
    exact mul_mem (coe_mem_locRing s f) (pow_mem (inv_mem_locRing s) n)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isLocalization_locRing {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) :
    IsLocalization.Away s (locRing T s) := by
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    show IsUnit (algebraMap (halfRing T) (locRing T s) (s ^ n))
    rw [map_pow]
    refine IsUnit.pow n (isUnit_iff_exists_inv.2 ⟨⟨_, inv_mem_locRing s⟩, Subtype.ext ?_⟩)
    exact mul_inv_cancel₀ hs0
  · intro z
    obtain ⟨n, f, hf⟩ := (mem_locRing h0).1 z.2
    refine ⟨⟨f, ⟨s ^ n, n, rfl⟩⟩, Subtype.ext ?_⟩
    show (z : ℂ⸨X⸩) * ((s ^ n : halfRing T) : ℂ⸨X⸩) = f
    rw [SubmonoidClass.coe_pow]
    exact hf
  · intro x y hxy
    refine ⟨1, ?_⟩
    rw [Submonoid.coe_one, one_mul, one_mul]
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext hv

def evLoc (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T) (hs : ev T w hw s ≠ 0) :
    locRing T s →ₐ[ℂ] ℂ :=
  haveI := isLocalization_locRing (s := s) fun h => hs (by rw [h, map_zero])
  IsLocalization.Away.liftAlgHom s (f := ev T w hw) hs.isUnit

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
@[simp] theorem evLoc_algebraMap {T : ℝ} {w : ℂ} (hw : T < w.im) {s : halfRing T}
    (hs : ev T w hw s ≠ 0) (f : halfRing T) :
    evLoc T w hw s hs (algebraMap _ _ f) = ev T w hw f := by
  simp [evLoc]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem evLoc_unique {T : ℝ} {w : ℂ} (hw : T < w.im) {s : halfRing T}
    (hs : ev T w hw s ≠ 0) (φ : locRing T s →+* ℂ)
    (hφ : ∀ f, φ (algebraMap _ _ f) = ev T w hw f) (x : locRing T s) :
    φ x = evLoc T w hw s hs x := by
  have h0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  have := isLocalization_locRing h0
  have key : φ = (evLoc T w hw s hs : locRing T s →+* ℂ) :=
    IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun f => by simp [hφ])
  exact RingHom.congr_fun key x

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem halfRing_spec :
    (∀ (T : ℝ) (s : ℂ⸨X⸩), s ∈ halfRing T ↔
      ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T),
      HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) (ev T w hw s)) ∧
    (∀ (T : ℝ) (s : halfRing T), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {w : ℂ | T < w.im} ∧
      ∀ w (hw : T < w.im), F w = ev T w hw s) ∧
    (∀ (T T' : ℝ) (s : halfRing T),
      (∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s = 0) → s = 0) ∧
    (∀ (T : ℝ) (s : halfRing T), s ≠ 0 →
      ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s ≠ 0) ∧
    Monotone halfRing ∧
    (⋃ T, (halfRing T : Set ℂ⸨X⸩) = convLaurent) ∧
    (∀ A : Subalgebra ℂ ℂ⸨X⸩, A.FG → A ≤ convLaurent.toSubalgebra → ∃ T, A ≤ halfRing T) ∧
    (∀ (T : ℝ) (s : halfRing T), (locRing T s).toSubring =
      Subring.closure ((halfRing T : Set ℂ⸨X⸩) ∪ {(s : ℂ⸨X⸩)⁻¹})) ∧
    (∀ (T : ℝ) (s : halfRing T), s ≠ 0 → IsLocalization.Away s (locRing T s)) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T), ev T w hw s ≠ 0 →
      ∃! φ : locRing T s →ₐ[ℂ] ℂ, ∀ f, φ (algebraMap _ _ f) = ev T w hw f) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (p : ℂ⟦X⟧) (hp : (p : ℂ⸨X⸩) ∈ halfRing T),
      SumsAt p w (ev T w hw ⟨p, hp⟩)) :=
  ⟨fun _ _ => mem_halfRing, fun _ _ hw s => hasSum_ev hw s,
    fun _ s => ⟨fun w => lsum s (eTwoPi w), differentiableOn_lsum_eTwoPi s.2, fun _ _ => rfl⟩,
    fun _ T' _ h => eq_zero_of_ev_eq_zero T' h, fun _ _ h0 => exists_ev_ne_zero h0, halfRing_mono,
    iUnion_halfRing, fun _ hA h => exists_le_halfRing hA h, fun _ s => locRing_toSubring s,
    fun _ _ h0 => isLocalization_locRing h0,
    fun _ _ hw s hs => ⟨evLoc _ _ hw s hs, fun f => evLoc_algebraMap hw hs f,
      fun φ hφ => AlgHom.ext fun x => evLoc_unique hw hs (φ : _ →+* ℂ) hφ x⟩,
    fun _ _ hw _ hp => sumsAt_ev hw hp⟩

end GlobalTheory.Conv
