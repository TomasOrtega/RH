import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormKernelHorizontal

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.BundleIsoGlue

variable {g : ℕ}

def perHom (τ : Matrix (Fin g) (Fin g) ℂ) : Fl g →+ (Fin g → ℂ) where
  toFun := per τ
  map_zero' := by ext i; simp [per, Matrix.vecMul, dotProduct]
  map_add' x y := by
    ext i
    simp [per, Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib]
    ring

/- English proof (translation)
Unfold `per Matrix.vecMul dotProduct`. Use `fun_prop`.
-/
lemma continuous_per (τ : Matrix (Fin g) (Fin g) ℂ) : Continuous (per τ) := by
  unfold per Matrix.vecMul dotProduct
  fun_prop

/- English proof (translation)
The claim follows from `((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ _).2 fun i => ⟨n i, by simp⟩`.
-/
lemma intVec_mem (n : Fin g ⊕ Fin g → ℤ) : (fun i => (n i : ℝ)) ∈ stdLat g :=
  ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ _).2 fun i => ⟨n i, by simp⟩

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {τ : E → Matrix (Fin g) (Fin g) ℂ}
  {j₁ j₂ : Fl g → Pt E g → ℂ}

/- English proof (translation)
Establish `hz : Set.MapsTo (fun P : Pt E g => zeroSec g P.1) (cov U g) (cov U g)` using `fun P hP => ⟨hP.1, trivial⟩`. Establish `hd : Differentiable ℂ (fun P : Pt E g => zeroSec g P.1)`. Unfold `zeroSec`. Use `fun_prop`. Establish `hd2 : DifferentiableOn ℂ (fun P : Pt E g => φ (zeroSec g P.1)) (cov U g)` using `h.1.comp hd.differentiableOn hz`.

Establish `hd3 : DifferentiableOn ℂ (fun P : Pt E g => φ P / φ (zeroSec g P.1)) (cov U g)`. Conclude with `(h.1.mul (hd2.inv fun P hP => h.2.1 _ (hz hP))).congr fun P _ => by`. Simplify using `only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]`. Use `⟨⟨hd3, fun P hP => div_ne_zero (h.2.1 P hP) (h.2.1 _ (hz hP)), fun l hl P hP => ?_⟩, fun b hb => div_self (h.2.1 _ ⟨hb, trivial⟩)⟩` and prove the remaining obligations. Establish `e` using `h.2.2 l hl P hP`.

Express the relevant statement in the definitionally equal form `φ (transl τ l P) / φ (zeroSec g P.1) * j₁ l P = j₂ l P * (φ P / φ (zeroSec g P.1))`. Rewrite using `[div_mul_eq_mul_div, e, mul_div_assoc]`.
-/
lemma normalise {U : Set E} {φ : Pt E g → ℂ} (h : IsBundleIso U τ (stdLat g) j₁ j₂ φ) :
    IsBundleIso U τ (stdLat g) j₁ j₂ (fun P => φ P / φ (zeroSec g P.1)) ∧
      ∀ b ∈ U, (fun P : Pt E g => φ P / φ (zeroSec g P.1)) (zeroSec g b) = 1 := by
  have hz : Set.MapsTo (fun P : Pt E g => zeroSec g P.1) (cov U g) (cov U g) :=
    fun P hP => ⟨hP.1, trivial⟩
  have hd : Differentiable ℂ (fun P : Pt E g => zeroSec g P.1) := by
    unfold zeroSec
    fun_prop
  have hd2 : DifferentiableOn ℂ (fun P : Pt E g => φ (zeroSec g P.1)) (cov U g) :=
    h.1.comp hd.differentiableOn hz
  have hd3 : DifferentiableOn ℂ (fun P : Pt E g => φ P / φ (zeroSec g P.1)) (cov U g) := by
    exact (h.1.mul (hd2.inv fun P hP => h.2.1 _ (hz hP))).congr fun P _ => by
      simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
  refine ⟨⟨hd3,
    fun P hP => div_ne_zero (h.2.1 P hP) (h.2.1 _ (hz hP)), fun l hl P hP => ?_⟩,
    fun b hb => div_self (h.2.1 _ ⟨hb, trivial⟩)⟩
  have e := h.2.2 l hl P hP
  change φ (transl τ l P) / φ (zeroSec g P.1) * j₁ l P = j₂ l P * (φ P / φ (zeroSec g P.1))
  rw [div_mul_eq_mul_div, e, mul_div_assoc]

/- English proof (translation)
Establish `hin : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov U g` using `fun z => ⟨hb, trivial⟩`. Establish `hin' : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov U' g` using `fun z => ⟨hb', trivial⟩`. Establish `hs : Differentiable ℂ (fun z : Fin g → ℂ => ((b, z) : Pt E g))` using `by fun_prop`. Establish `hF : Differentiable ℂ (fun z : Fin g → ℂ => ψ (b, z) / ψ' (b, z))`. Rewrite using `[← differentiableOn_univ]`.

Establish `d1 : DifferentiableOn ℂ (fun z : Fin g → ℂ => ψ (b, z)) Set.univ` using `h.1.comp hs.differentiableOn fun z _ => hin z`. Establish `d2 : DifferentiableOn ℂ (fun z : Fin g → ℂ => ψ' (b, z)) Set.univ` using `h'.1.comp hs.differentiableOn fun z _ => hin' z`. Conclude with `(d1.mul (d2.inv fun z _ => h'.2.1 _ (hin' z))).congr fun z _ => by`. Simplify using `only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]`. Establish `hcov : ∀ w : Fin g → ℂ, ∃ gg ∈ (stdLat g).toAddSubgroup.map (perHom (τ b)), ∃ k ∈ per (τ b) '' Set.Icc (0 : Fl g) 1, w = gg + k`.

Introduce `w`. Take `⟨x, rfl⟩ : ∃ x, per (τ b) x = w` from `⟨_, GlobalTheory.FlatKernel.per_flatOf hdet w⟩`. Establish `hfl : per (τ b) (fun i => (⌊x i⌋ : ℝ)) ∈ (stdLat g).toAddSubgroup.map (perHom (τ b))` using `AddSubgroup.mem_map.2 ⟨fun i => (⌊x i⌋ : ℝ), intVec_mem (fun i => ⌊x i⌋), rfl⟩`. Establish `hfr : per (τ b) (fun i => Int.fract (x i)) ∈ per (τ b) '' Set.Icc (0 : Fl g) 1` using `Set.mem_image_of_mem _ ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩`. Use `⟨_, hfl, _, hfr, ?_⟩` and prove the remaining obligations.

Establish `hx : x = (fun i => (⌊x i⌋ : ℝ)) + fun i => Int.fract (x i)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [hx]`. Conclude with `(perHom (τ b)).map_add _ _`.

Establish `hper : ∀ w : Fin g → ℂ, ∀ gg ∈ (stdLat g).toAddSubgroup.map (perHom (τ b)), ψ (b, w + gg) / ψ' (b, w + gg) = ψ (b, w) / ψ' (b, w)`. Introduce `w gg hgg`. Take `⟨l, hl, rfl⟩` from `hgg`. Establish `e` using `h.2.2 l hl (b, w) (hin w)`. Establish `e'` using `h'.2.2 l hl (b, w) (hin' w)`.

Simplify using `only [transl] at e e'`. Express the relevant statement in the definitionally equal form `ψ (b, w + per (τ b) l) / ψ' (b, w + per (τ b) l) = ψ (b, w) / ψ' (b, w)`. Rewrite using `[div_eq_div_iff (h'.2.1 _ (hin' _)) (h'.2.1 _ (hin' w))]`. Use `mul_right_cancel₀ (hj l hl _ (hin w)) ?_` and prove the remaining obligations. Take the linear combination `ψ' (b, w) * e - ψ (b, w) * e'`.

Take `⟨c, hc⟩` from `GlobalTheory.entire_const_of_addSubgroup_periodic hF ((stdLat g).toAddSubgroup.map (perHom (τ b))) ((isCompact_Icc.image (continuous_per (τ b))).isBounded) hcov hper`. Establish `e0` using `hc 0`. Establish `ez` using `hc z`. Simplify using `only [zeroSec] at h0 h0'`. Rewrite `e0` using `[h0, h0', div_one]`.

Rewrite `ez` using `[← e0]`. Conclude with `(div_eq_one_iff_eq (h'.2.1 _ (hin' z))).1 ez`.
-/
lemma uniq {U U' : Set E} {ψ ψ' : Pt E g → ℂ}
    (h : IsBundleIso U τ (stdLat g) j₁ j₂ ψ) (h' : IsBundleIso U' τ (stdLat g) j₁ j₂ ψ')
    (hj : ∀ l ∈ stdLat g, ∀ P ∈ cov U g, j₁ l P ≠ 0)
    {b : E} (hb : b ∈ U) (hb' : b ∈ U') (hdet : IsUnit ((τ b).map Complex.im).det)
    (h0 : ψ (zeroSec g b) = 1) (h0' : ψ' (zeroSec g b) = 1) (z : Fin g → ℂ) :
    ψ (b, z) = ψ' (b, z) := by
  have hin : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov U g := fun z => ⟨hb, trivial⟩
  have hin' : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov U' g := fun z => ⟨hb', trivial⟩
  have hs : Differentiable ℂ (fun z : Fin g → ℂ => ((b, z) : Pt E g)) := by fun_prop
  have hF : Differentiable ℂ (fun z : Fin g → ℂ => ψ (b, z) / ψ' (b, z)) := by
    rw [← differentiableOn_univ]
    have d1 : DifferentiableOn ℂ (fun z : Fin g → ℂ => ψ (b, z)) Set.univ :=
      h.1.comp hs.differentiableOn fun z _ => hin z
    have d2 : DifferentiableOn ℂ (fun z : Fin g → ℂ => ψ' (b, z)) Set.univ :=
      h'.1.comp hs.differentiableOn fun z _ => hin' z
    exact (d1.mul (d2.inv fun z _ => h'.2.1 _ (hin' z))).congr fun z _ => by
      simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
  have hcov : ∀ w : Fin g → ℂ, ∃ gg ∈ (stdLat g).toAddSubgroup.map (perHom (τ b)),
      ∃ k ∈ per (τ b) '' Set.Icc (0 : Fl g) 1, w = gg + k := by
    intro w
    obtain ⟨x, rfl⟩ : ∃ x, per (τ b) x = w := ⟨_, GlobalTheory.FlatKernel.per_flatOf hdet w⟩
    have hfl : per (τ b) (fun i => (⌊x i⌋ : ℝ)) ∈ (stdLat g).toAddSubgroup.map (perHom (τ b)) :=
      AddSubgroup.mem_map.2 ⟨fun i => (⌊x i⌋ : ℝ), intVec_mem (fun i => ⌊x i⌋), rfl⟩
    have hfr : per (τ b) (fun i => Int.fract (x i)) ∈ per (τ b) '' Set.Icc (0 : Fl g) 1 :=
      Set.mem_image_of_mem _ ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
    refine ⟨_, hfl, _, hfr, ?_⟩
    · have hx : x = (fun i => (⌊x i⌋ : ℝ)) + fun i => Int.fract (x i) := by
        ext i
        simp
      conv_lhs => rw [hx]
      exact (perHom (τ b)).map_add _ _
  have hper : ∀ w : Fin g → ℂ, ∀ gg ∈ (stdLat g).toAddSubgroup.map (perHom (τ b)),
      ψ (b, w + gg) / ψ' (b, w + gg) = ψ (b, w) / ψ' (b, w) := by
    intro w gg hgg
    obtain ⟨l, hl, rfl⟩ := hgg
    have e := h.2.2 l hl (b, w) (hin w)
    have e' := h'.2.2 l hl (b, w) (hin' w)
    simp only [transl] at e e'
    change ψ (b, w + per (τ b) l) / ψ' (b, w + per (τ b) l) = ψ (b, w) / ψ' (b, w)
    rw [div_eq_div_iff (h'.2.1 _ (hin' _)) (h'.2.1 _ (hin' w))]
    refine mul_right_cancel₀ (hj l hl _ (hin w)) ?_
    linear_combination ψ' (b, w) * e - ψ (b, w) * e'
  obtain ⟨c, hc⟩ := GlobalTheory.entire_const_of_addSubgroup_periodic hF
    ((stdLat g).toAddSubgroup.map (perHom (τ b)))
    ((isCompact_Icc.image (continuous_per (τ b))).isBounded) hcov hper
  have e0 := hc 0
  have ez := hc z
  simp only [zeroSec] at h0 h0'
  rw [h0, h0', div_one] at e0
  rw [← e0] at ez
  exact (div_eq_one_iff_eq (h'.2.1 _ (hin' z))).1 ez

end Family

/- English proof (translation)
Introduce `g E _ _ B τ hτ j₁ j₂ hj hloc`. Establish `hdet : ∀ b ∈ B, IsUnit ((τ b).map Complex.im).det` using `fun b hb => isUnit_iff_ne_zero.2 (hτ.2.2 b hb).2.det_pos.ne'`. Establish `hnorm : ∀ b : E, ∃ U : Set E, ∃ ψ : Pt E g → ℂ, b ∈ B → (IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧ IsBundleIso U τ (stdLat g) j₁ j₂ ψ ∧ ∀ b' ∈ U, ψ (zeroSec g b') = 1)`. Introduce `b`. Distinguish the cases in `hb : b ∈ B`.

Take `⟨U, hU, hbU, hUB, φ, hφ⟩` from `hloc b hb`. Conclude with `⟨U, _, fun _ => ⟨hU, hbU, hUB, (normalise hφ).1, (normalise hφ).2⟩⟩`. Conclude with `⟨∅, 0, fun h => absurd h hb⟩`. Use `choose U ψ hψ using hnorm`. Use `⟨fun P => ψ P.1 P, ⟨?_, fun P hP => (hψ P.1 hP.1).2.2.2.1.2.1 P ⟨(hψ P.1 hP.1).2.1, trivial⟩, fun l hl P hP => (hψ P.1 hP.1).2.2.2.1.2.2 l hl P ⟨(hψ P.1 hP.1).2.1, trivial⟩⟩, fun b hb => (hψ b hb).2.2.2.2 b (hψ b hb).2.1⟩` and prove the remaining obligations.

Introduce `P hP`. Take `⟨hUo, hbU, hUB, hiso, h0⟩` from `hψ P.1 hP.1`. Establish `hopen : IsOpen (cov (U P.1) g)` using `hUo.prod isOpen_univ`. Establish `hmem : P ∈ cov (U P.1) g` using `⟨hbU, trivial⟩`. Establish `hev : (fun Q : Pt E g => ψ Q.1 Q) =ᶠ[nhds P] ψ P.1` using `by filter_upwards [hopen.mem_nhds hmem] with Q hQ`.

Take `⟨b', z⟩` from `Q`. Take `⟨_, hbU', hUB', hiso', h0'⟩` from `hψ b' (hUB hQ.1)`. Conclude with `uniq hiso' hiso (fun l hl R hR => hj l hl R ⟨hUB' hR.1, trivial⟩) hbU' hQ.1 (hdet _ (hUB hQ.1)) (h0' _ hbU') (h0 _ hQ.1) z`. Conclude with `(((hiso.1 P hmem).differentiableAt (hopen.mem_nhds hmem)).congr_of_eventuallyEq hev).differentiableWithinAt`.
-/
theorem glue : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j₁ j₂ : Fl g → Pt E g → ℂ),
    (∀ l ∈ stdLat g, ∀ P ∈ cov B g, j₁ l P ≠ 0) →
    (∀ b ∈ B, ∃ U : Set E, IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧ ∃ φ, IsBundleIso U τ (stdLat g) j₁ j₂ φ) →
    ∃ φ, IsBundleIso B τ (stdLat g) j₁ j₂ φ ∧ ∀ b ∈ B, φ (zeroSec g b) = 1 := by
  intro g E _ _ B τ hτ j₁ j₂ hj hloc
  have hdet : ∀ b ∈ B, IsUnit ((τ b).map Complex.im).det := fun b hb =>
    isUnit_iff_ne_zero.2 (hτ.2.2 b hb).2.det_pos.ne'
  have hnorm : ∀ b : E, ∃ U : Set E, ∃ ψ : Pt E g → ℂ, b ∈ B → (IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧
      IsBundleIso U τ (stdLat g) j₁ j₂ ψ ∧ ∀ b' ∈ U, ψ (zeroSec g b') = 1) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨U, hU, hbU, hUB, φ, hφ⟩ := hloc b hb
      exact ⟨U, _, fun _ => ⟨hU, hbU, hUB, (normalise hφ).1, (normalise hφ).2⟩⟩
    · exact ⟨∅, 0, fun h => absurd h hb⟩
  choose U ψ hψ using hnorm
  refine ⟨fun P => ψ P.1 P, ⟨?_, fun P hP => (hψ P.1 hP.1).2.2.2.1.2.1 P ⟨(hψ P.1 hP.1).2.1, trivial⟩,
    fun l hl P hP => (hψ P.1 hP.1).2.2.2.1.2.2 l hl P ⟨(hψ P.1 hP.1).2.1, trivial⟩⟩,
    fun b hb => (hψ b hb).2.2.2.2 b (hψ b hb).2.1⟩
  intro P hP
  obtain ⟨hUo, hbU, hUB, hiso, h0⟩ := hψ P.1 hP.1
  have hopen : IsOpen (cov (U P.1) g) := hUo.prod isOpen_univ
  have hmem : P ∈ cov (U P.1) g := ⟨hbU, trivial⟩
  have hev : (fun Q : Pt E g => ψ Q.1 Q) =ᶠ[nhds P] ψ P.1 := by
    filter_upwards [hopen.mem_nhds hmem] with Q hQ
    obtain ⟨b', z⟩ := Q
    obtain ⟨_, hbU', hUB', hiso', h0'⟩ := hψ b' (hUB hQ.1)
    exact uniq hiso' hiso (fun l hl R hR => hj l hl R ⟨hUB' hR.1, trivial⟩) hbU' hQ.1
      (hdet _ (hUB hQ.1)) (h0' _ hbU') (h0 _ hQ.1) z
  exact (((hiso.1 P hmem).differentiableAt (hopen.mem_nhds hmem)).congr_of_eventuallyEq
    hev).differentiableWithinAt

end GlobalTheory.BundleIsoGlue
