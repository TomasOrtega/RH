import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Introduce `E _ _ n W hW h1`. Establish `hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)))` using `by open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))`. Establish `hS0 : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)}`. Establish `e : {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} = Set.range (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)))` using `Set.ext fun x => ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩`. Rewrite using `[e]`.

Conclude with `hemb.isOpen_range`. Establish `hGL : ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)}`. Rewrite using `[hemb.isInducing.continuousOn_iff]`. Conclude with `continuousOn_id.congr fun x hx => val_toGLInf hx`. Use `set S : Set (Fin n → Fin n → Cinf E) := {x | IsUnit (Matrix.of x)} with hSdef`.

Establish `hS : IsOpen S` using `hS0`. Establish `hF : ContinuousOn (fun x : Fin n → Fin n → Cinf E => onMatInf W (Matrix.of x)) S`. Use `(hW.comp_continuousOn hGL).congr fun x hx => ?_` and prove the remaining obligations. Conclude with `onMatInf_of_isUnit W hx`. Use `set c : ℂ := starRingEnd ℂ (W 1) with hc`.

Use `set U : Set (Fin n → Fin n → Cinf E) := S ∩ (fun x => (c * onMatInf W (Matrix.of x)).re) ⁻¹' Set.Ioi 0 with hUdef`. Establish `hU : IsOpen U` using `(Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hF)).isOpen_inter_preimage hS isOpen_Ioi`. Use `set x0 : Fin n → Fin n → Cinf E := fun i j => (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j with hx0def`. Establish `hx0 : Matrix.of x0 = 1` using `by ext i j; rfl`. Establish `hval : onMatInf W (Matrix.of x0) = W 1`.

Rewrite using `[hx0]`. Simplify using `using onMatInf_val W 1`. Establish `hpos : 0 < (c * W 1).re`. Rewrite using `[hc, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]`. Conclude with `Complex.normSq_pos.2 h1`.

Establish `hx0U : x0 ∈ U`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show IsUnit (Matrix.of x0)`. Rewrite using `[hx0]`. Conclude with `isUnit_one`.

Use `show 0 < (c * onMatInf W (Matrix.of x0)).re`. Rewrite using `[hval]`. Conclude with `hpos`. Take `⟨ρ, h1ρ, h2ρ, h3ρ, h4ρ, h5ρ⟩` from `exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx0U)`. Establish `hts : tsupport (fun x => (ρ x : ℂ)) ⊆ U` using `(tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) ρ).trans h1ρ`.

Establish `hcs : HasCompactSupport (fun x => (ρ x : ℂ))` using `h2ρ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Use `⟨fun x => (ρ x : ℂ), Complex.ofRealCLM.contDiff.comp h3ρ, hcs, hts.trans Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Use `set f : (Fin n → Fin n → Cinf E) → ℂ := fun a => (ρ a : ℂ) * onMatInf W (Matrix.of a) with hfdef`. Establish `e : smoothMatInf (fun x => (ρ x : ℂ)) W 1 = ∫ a, f a`. Simplify using `[smoothMatInf, f]`.

Establish `hsub : tsupport f ⊆ S` using `tsupport_mul_subset_left.trans (hts.trans Set.inter_subset_left)`. Establish `hfc : Continuous f` using `((Complex.continuous_ofReal.comp h3ρ.continuous).continuousOn.mul hF).continuous_of_tsupport_subset hS hsub`. Establish `hfs : HasCompactSupport f` using `hcs.mul_right`. Establish `hint : Integrable f volume` using `hfc.integrable_of_hasCompactSupport hfs`. Establish `hnn : ∀ a, 0 ≤ (c * f a).re`.

Introduce `a`. Establish `hr : 0 ≤ ρ a` using `(h4ρ ⟨a, rfl⟩).1`. Establish `eq : (c * f a).re = ρ a * (c * onMatInf W (Matrix.of a)).re`. Simplify using `only [f]`. Rewrite using `[mul_left_comm, Complex.re_ofReal_mul]`.

Rewrite using `[eq]`. Distinguish the cases in `ha : ρ a = 0`. Simplify using `[ha]`. Establish `: a ∈ U` using `h1ρ (subset_tsupport _ ha)`. Conclude with `mul_nonneg hr (le_of_lt this.2)`.

Establish `hne : (c * f x0).re ≠ 0`. Simplify using `only [f]`. Rewrite using `[h5ρ, hval]`. Simplify using `using hpos.ne'`. Establish `hcont : Continuous fun a => (c * f a).re` using `Complex.continuous_re.comp (continuous_const.mul hfc)`.

Establish `hsupp : HasCompactSupport fun a => (c * f a).re` using `hfs.comp_left (g := fun z : ℂ => (c * z).re) (by simp)`. Establish `key : 0 < ∫ a, (c * f a).re ∂volume` using `hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnn (x := x0) hne`. Establish `hre : ∫ a, (c * f a).re = (∫ a, c * f a).re` using `integral_re (hint.const_mul c)`. Rewrite using `[e]`. Introduce `h0`.

Rewrite `key` using `[hre, integral_const_mul, h0, mul_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ key`.
-/
theorem exists_smoothMatInf_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 →
    ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧
      tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  intro E _ _ n W hW h1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) := by
    open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))
  have hS0 : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
    have e : {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} =
        Set.range (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) :=
      Set.ext fun x => ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
    rw [e]; exact hemb.isOpen_range
  have hGL : ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
    rw [hemb.isInducing.continuousOn_iff]
    exact continuousOn_id.congr fun x hx => val_toGLInf hx
  set S : Set (Fin n → Fin n → Cinf E) := {x | IsUnit (Matrix.of x)} with hSdef
  have hS : IsOpen S := hS0
  have hF : ContinuousOn (fun x : Fin n → Fin n → Cinf E => onMatInf W (Matrix.of x)) S := by
    refine (hW.comp_continuousOn hGL).congr fun x hx => ?_
    exact onMatInf_of_isUnit W hx
  set c : ℂ := starRingEnd ℂ (W 1) with hc
  set U : Set (Fin n → Fin n → Cinf E) := S ∩ (fun x => (c * onMatInf W (Matrix.of x)).re) ⁻¹' Set.Ioi 0 with hUdef
  have hU : IsOpen U :=
    (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hF)).isOpen_inter_preimage hS isOpen_Ioi
  set x0 : Fin n → Fin n → Cinf E := fun i j => (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j with hx0def
  have hx0 : Matrix.of x0 = 1 := by ext i j; rfl
  have hval : onMatInf W (Matrix.of x0) = W 1 := by
    rw [hx0]; simpa using onMatInf_val W 1
  have hpos : 0 < (c * W 1).re := by
    rw [hc, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h1
  have hx0U : x0 ∈ U := by
    refine ⟨?_, ?_⟩
    · show IsUnit (Matrix.of x0); rw [hx0]; exact isUnit_one
    · show 0 < (c * onMatInf W (Matrix.of x0)).re; rw [hval]; exact hpos
  obtain ⟨ρ, h1ρ, h2ρ, h3ρ, h4ρ, h5ρ⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx0U)
  have hts : tsupport (fun x => (ρ x : ℂ)) ⊆ U :=
    (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) ρ).trans h1ρ
  have hcs : HasCompactSupport (fun x => (ρ x : ℂ)) := h2ρ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨fun x => (ρ x : ℂ), Complex.ofRealCLM.contDiff.comp h3ρ, hcs, hts.trans Set.inter_subset_left, ?_⟩
  set f : (Fin n → Fin n → Cinf E) → ℂ := fun a => (ρ a : ℂ) * onMatInf W (Matrix.of a) with hfdef
  have e : smoothMatInf (fun x => (ρ x : ℂ)) W 1 = ∫ a, f a := by
    simp [smoothMatInf, f]
  have hsub : tsupport f ⊆ S := tsupport_mul_subset_left.trans (hts.trans Set.inter_subset_left)
  have hfc : Continuous f :=
    ((Complex.continuous_ofReal.comp h3ρ.continuous).continuousOn.mul hF).continuous_of_tsupport_subset hS hsub
  have hfs : HasCompactSupport f := hcs.mul_right
  have hint : Integrable f volume := hfc.integrable_of_hasCompactSupport hfs
  have hnn : ∀ a, 0 ≤ (c * f a).re := by
    intro a
    have hr : 0 ≤ ρ a := (h4ρ ⟨a, rfl⟩).1
    have eq : (c * f a).re = ρ a * (c * onMatInf W (Matrix.of a)).re := by
      simp only [f]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [eq]
    by_cases ha : ρ a = 0
    · simp [ha]
    · have : a ∈ U := h1ρ (subset_tsupport _ ha)
      exact mul_nonneg hr (le_of_lt this.2)
  have hne : (c * f x0).re ≠ 0 := by
    simp only [f]
    rw [h5ρ, hval]
    simpa using hpos.ne'
  have hcont : Continuous fun a => (c * f a).re := Complex.continuous_re.comp (continuous_const.mul hfc)
  have hsupp : HasCompactSupport fun a => (c * f a).re :=
    hfs.comp_left (g := fun z : ℂ => (c * z).re) (by simp)
  have key : 0 < ∫ a, (c * f a).re ∂volume :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnn (x := x0) hne
  have hre : ∫ a, (c * f a).re = (∫ a, c * f a).re := integral_re (hint.const_mul c)
  rw [e]
  intro h0
  rw [hre, integral_const_mul, h0, mul_zero, Complex.zero_re] at key
  exact lt_irrefl _ key

end GlobalTheory.JSW.MirCinf
