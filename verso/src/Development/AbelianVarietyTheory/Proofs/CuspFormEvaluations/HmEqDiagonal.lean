import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HermDiag

/- English proof (translation)
Unfold `hermForm`. Simplify using `only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hA.apply j i]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hermForm_eq_star_swap {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsHermitian)
    (z w : Fin g → ℂ) : hermForm A z w = star (hermForm A w z) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply j i]
  ring

/- English proof (translation)
Set `L : (Fin g → ℂ) → (Fin g → ℂ) →ₗ[ℝ] ℝ` to `fun w => { toFun := fun z => (hermForm A z w).im - (hermForm B z w).im map_add' := fun z z' => by`. Simplify using `only [hermForm, add_dotProduct, Complex.add_im]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun t z => by`. Simplify using `only [hermForm, smul_dotProduct, Complex.smul_im, RingHom.id_apply, smul_eq_mul]`.

Use `ring }`. Establish `hL : ∀ w z, L w z = (hermForm A z w).im - (hermForm B z w).im` using `fun _ _ => rfl`. Establish `zero_of : ∀ w, (∀ a, L w (P a) = 0) → ∀ z, L w z = 0`. Introduce `w hw z`. Establish `h0 : L w = 0` using `LinearMap.ext_on hP (fun y hy => by`.

Take `⟨a, rfl⟩` from `hy`. Simplify using `using hw a)`. Rewrite using `[h0]`. Both sides reduce to the same expression. Establish `key1 : ∀ a z, L (P a) z = 0` using `fun a => zero_of _ (fun b => by rw [hL, h b a, sub_self])`.

Establish `key2 : ∀ z w, L w z = 0`. Introduce `z w`. Use `zero_of w (fun a => ?_) z` and prove the remaining obligations. Establish `h1` using `key1 a w`. Rewrite `h1`, the goal using `[hL]`.

Rewrite using `[hermForm_eq_star_swap A hA (P a) w, hermForm_eq_star_swap B hB (P a) w]`. Simplify using `only [Complex.star_def, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Use extensionality with `i j`. Apply `Complex.ext` to reduce the goal to its premises.

Establish `h1` using `key2 (Pi.single i Complex.I) (Pi.single j 1)`. Rewrite `h1` using `[hL]`. Simplify using `[hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `key2 (Pi.single i 1) (Pi.single j 1)`.

Rewrite `h1` using `[hL]`. Simplify using `[hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem eq_of_im_hermForm_eq_of_real_span_eq_univ {g : ℕ} {La : Type} [AddCommGroup La] (A B : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (P : La →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (h : ∀ a b, (hermForm A (P a) (P b)).im = (hermForm B (P a) (P b)).im) : A = B := by
  let L : (Fin g → ℂ) → (Fin g → ℂ) →ₗ[ℝ] ℝ := fun w =>
    { toFun := fun z => (hermForm A z w).im - (hermForm B z w).im
      map_add' := fun z z' => by
        simp only [hermForm, add_dotProduct, Complex.add_im]; ring
      map_smul' := fun t z => by
        simp only [hermForm, smul_dotProduct, Complex.smul_im, RingHom.id_apply, smul_eq_mul]; ring }
  have hL : ∀ w z, L w z = (hermForm A z w).im - (hermForm B z w).im := fun _ _ => rfl
  have zero_of : ∀ w, (∀ a, L w (P a) = 0) → ∀ z, L w z = 0 := by
    intro w hw z
    have h0 : L w = 0 := LinearMap.ext_on hP (fun y hy => by
      obtain ⟨a, rfl⟩ := hy
      simpa using hw a)
    rw [h0]; rfl
  have key1 : ∀ a z, L (P a) z = 0 := fun a => zero_of _ (fun b => by rw [hL, h b a, sub_self])
  have key2 : ∀ z w, L w z = 0 := by
    intro z w
    refine zero_of w (fun a => ?_) z
    have h1 := key1 a w
    rw [hL] at h1 ⊢
    rw [hermForm_eq_star_swap A hA (P a) w, hermForm_eq_star_swap B hB (P a) w]
    simp only [Complex.star_def, Complex.conj_im]
    linarith
  ext i j
  apply Complex.ext
  · have h1 := key2 (Pi.single i Complex.I) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith
  · have h1 := key2 (Pi.single i 1) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U k x W Wu hg hU ho`. Take `⟨hr, htype, -⟩` from `hU`. Take `⟨hp0, hΨ⟩` from `htype k`. Establish `hbij : Function.Bijective (relab c σ)`. Rewrite using `[← Finite.injective_iff_bijective]`.

Introduce `τ₁ τ₂ h12`. Use extensionality with `y`. Establish `h1 : σ (Formalism.L2.Pj.embF c τ₁ y) = σ (Formalism.L2.Pj.embF c τ₂ y)` using `congrArg (fun f : E →+* ℂ => f y) h12`. Conclude with `congrArg Subtype.val (σ.injective h1)`. Establish `hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0`.

Introduce `τ`. Establish `h1 : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2`.

Rewrite using `[← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]`. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.mp h2`. Establish `hkey : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0`. Introduce `τ`. Establish `hg' : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0` using `hg`.

Establish `hρ : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0` using `rfl`. Break down `hsq τ with h | h` into its components or cases. Establish `e : Formalism.L2.Pj.embF c τ (H.rt : E) = IntermediateField.inclusion c.le (baseKA l).ρ` using `Subtype.ext (h.trans hρ.symm)`. Establish `h3 : relab c σ τ (H.rt : E) = H.rt0` using `by show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = H.rt0`. Rewrite using `[e, hg']`.

Rewrite using `[h3, h]`. Establish `e : Formalism.L2.Pj.embF c τ (H.rt : E) = -IntermediateField.inclusion c.le (baseKA l).ρ` using `Subtype.ext (by show τ (H.rt : E) = -((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)`. Rewrite using `[h, hρ])`. Establish `h3 : relab c σ τ (H.rt : E) = -H.rt0` using `by show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = -H.rt0`. Rewrite using `[e, map_neg, hg']`.

Rewrite using `[h3, h]`. Establish `hpm : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → Dw.mult τ = Dw.p`. Introduce `τ hτ`. Rewrite `hτ` using `[hΨ, hkey]`. Unfold `Geo.Tor.Datum.mult`.

Rewrite using `[if_pos hτ]`. Establish `hqm : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = Dw.q`. Introduce `τ hτ`. Rewrite `hτ` using `[hΨ, hkey]`. Unfold `Geo.Tor.Datum.mult`.

Rewrite using `[if_neg hτ]`. Take `⟨f, hf⟩` from `GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult hpm hqm`. Use `set idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f with hidx`. Establish `hz : ∀ a j, W.Pm a j = if ((idx j).2 : ℕ) < Dw.q then FD.hermC (idx j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 (idx j).1) (idx j).2) (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E)) else ((FD.mat x.1 (idx j).1)⁻¹.mulVec (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))) (idx j).2`. Introduce `a j`.

Rewrite using `[W.pm_eq a j]`. Unfold `Formalism.L2.Pj.perFr`. Establish `hj : idx j = f (W.e j)` using `rfl`. Rewrite using `[hj]`. Break down `hf (W.e j) with ⟨hin, h1, h2⟩ | ⟨hout, h1, h2, h3⟩` into its components or cases.

Establish `hi : (U.X k).p0 + ((W.e j).2 : ℕ) < r`. Use `(f (W.e j)).2.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_pos hin, dif_pos hi, if_neg (by omega)]`. Establish `e1 : (f (W.e j)).1 = ⟨relab c σ (W.e j).1, hin⟩` using `Subtype.ext h1`.

Establish `e2 : (f (W.e j)).2 = ⟨(U.X k).p0 + ((W.e j).2 : ℕ), hi⟩` using `Fin.ext (by show ((f (W.e j)).2 : ℕ) = (U.X k).p0 + ((W.e j).2 : ℕ) omega)`. Rewrite using `[e1, e2]`. Establish `hcj : conjEmb (relab c σ (W.e j).1) = (f (W.e j)).1.1`. Rewrite using `[h1]`. Conclude with `RingHom.ext fun y => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl`.

Establish `hin' : conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ`. Rewrite using `[hcj]`. Conclude with `(f (W.e j)).1.2`. Establish `hi : (U.X k).p0 - 1 - ((W.e j).2 : ℕ) < r`. Use `(f (W.e j)).2.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg hout, dif_pos hin', dif_pos hi, if_pos (by omega)]`. Establish `e1 : (f (W.e j)).1 = ⟨conjEmb (relab c σ (W.e j).1), hin'⟩` using `Subtype.ext hcj.symm`. Establish `e2 : (f (W.e j)).2 = ⟨(U.X k).p0 - 1 - ((W.e j).2 : ℕ), hi⟩` using `Fin.ext (by show ((f (W.e j)).2 : ℕ) = (U.X k).p0 - 1 - ((W.e j).2 : ℕ) omega)`. Rewrite using `[e1, e2]`.

Establish `hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0)`. Establish `h` using `(U.X k).ξ0_im`. Unfold `FD.cc at h ⊢`. Rewrite using `[map_neg, h]`. Establish `hx : ∀ τ : (U.X k).Ψ, FD.gram τ.1 (U.X k).Gm (FD.mat x.1 τ) = Matrix.diagonal fun a : Fin r => ((FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ)`.

Introduce `τ`. Rewrite using `[← hp0]`. Conclude with `ho τ`. Use `set D0 : Matrix (Fin W.g) (Fin W.g) ℂ := Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) with hD0`. Establish `hD : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im = (hermForm D0 (W.Pm a) (W.Pm b)).im`.

Introduce `a b`. Rewrite using `[Wu.c1 a b, hD0, GlobalTheory.OrthoHerm.im_diag_eq_trace Dw.q (-(U.X k).ξ0) (U.X k).Gm (U.X k).Ψ (U.X k).cmType idx hcc x.1 hx (W.φ k a : Fin r → E) (W.φ k b : Fin r → E) (W.Pm a) (W.Pm b) (hz a) (hz b), ← W.isom k a b]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hD0h : D0.IsHermitian`.

Rewrite using `[hD0]`. Apply `Matrix.isHermitian_diagonal_of_self_adjoint` to reduce the goal to its premises. Use extensionality with `j`. Simplify using the standard rewrite rules. Take `⟨-, -, -, hspan, -⟩` from `W.per`.

Establish `hHm : Wu.Hm = D0` using `eq_of_im_hermForm_eq_of_real_span_eq_univ Wu.Hm D0 Wu.herm hD0h W.Pm hspan hD`. Rewrite using `[hHm, hD0]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Establish `hpos` using `Wu.pos (Pi.single j 1) (by simp)`.

Rewrite `hpos` using `[hHm, hD0]`. Establish `hdiag : (hermForm (Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ)) (Pi.single j 1) (Pi.single j 1)).re = 2 * ((idx j).1.1 (-(U.X k).ξ0)).im`. Simplify using `[hermForm]`. Rewrite `hpos` using `[hdiag, map_neg, Complex.neg_im]`. Establish `hre : ((idx j).1.1 (U.X k).ξ0).re = 0`.

Establish `h1 : starRingEnd ℂ ((idx j).1.1 (U.X k).ξ0) = -((idx j).1.1 (U.X k).ξ0)`. Rewrite using `[← NumberField.IsCMField.complexEmbedding_complexConj (φ := (idx j).1.1) (x := (U.X k).ξ0), ← map_neg]`. Use `congr 1`. Conclude with `(U.X k).ξ0_im`. Establish `h2` using `congrArg Complex.re h1`.

Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnorm : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖(idx j).1.1 (U.X k).ξ0‖`. Establish `hj : idx j = f (W.e j)` using `rfl`. Rewrite using `[hj]`.

Break down `hf (W.e j) with ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩` into its components or cases. Rewrite using `[h1]`. Rewrite using `[h1, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]`. Establish `hfin : ((idx j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖`. Rewrite using `[hnorm, ← (Complex.abs_im_eq_norm).mpr hre, map_neg, Complex.neg_im, abs_of_neg (by linarith)]`.

Rewrite using `[hfin]`.
-/
theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu hg hU ho
  obtain ⟨hr, htype, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := htype k
  have hbij : Function.Bijective (relab c σ) := by
    rw [← Finite.injective_iff_bijective]
    intro τ₁ τ₂ h12
    ext y
    have h1 : σ (Formalism.L2.Pj.embF c τ₁ y) = σ (Formalism.L2.Pj.embF c τ₂ y) :=
      congrArg (fun f : E →+* ℂ => f y) h12
    exact congrArg Subtype.val (σ.injective h1)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
      simpa using this
    have h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  have hkey : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    have hg' : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hg
    have hρ : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases hsq τ with h | h
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hρ.symm)
      have h3 : relab c σ τ (H.rt : E) = H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = H.rt0
        rw [e, hg']
      rw [h3, h]
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = -IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (by
          show τ (H.rt : E) = -((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
          rw [h, hρ])
      have h3 : relab c σ τ (H.rt : E) = -H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = -H.rt0
        rw [e, map_neg, hg']
      rw [h3, h]
  have hpm : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → Dw.mult τ = Dw.p := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_pos hτ]
  have hqm : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = Dw.q := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_neg hτ]
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult hpm hqm
  set idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f with hidx
  have hz : ∀ a j, W.Pm a j = if ((idx j).2 : ℕ) < Dw.q then
      FD.hermC (idx j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 (idx j).1) (idx j).2)
        (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))
      else ((FD.mat x.1 (idx j).1)⁻¹.mulVec (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))) (idx j).2 := by
    intro a j
    rw [W.pm_eq a j]
    unfold Formalism.L2.Pj.perFr
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨hin, h1, h2⟩ | ⟨hout, h1, h2, h3⟩
    · have hi : (U.X k).p0 + ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dif_pos hin, dif_pos hi, if_neg (by omega)]
      have e1 : (f (W.e j)).1 = ⟨relab c σ (W.e j).1, hin⟩ := Subtype.ext h1
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 + ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 + ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
    · have hcj : conjEmb (relab c σ (W.e j).1) = (f (W.e j)).1.1 := by
        rw [h1]
        exact RingHom.ext fun y => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      have hin' : conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ := by
        rw [hcj]
        exact (f (W.e j)).1.2
      have hi : (U.X k).p0 - 1 - ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dif_neg hout, dif_pos hin', dif_pos hi, if_pos (by omega)]
      have e1 : (f (W.e j)).1 = ⟨conjEmb (relab c σ (W.e j).1), hin'⟩ := Subtype.ext hcj.symm
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 - 1 - ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 - 1 - ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have hx : ∀ τ : (U.X k).Ψ, FD.gram τ.1 (U.X k).Gm (FD.mat x.1 τ) =
      Matrix.diagonal fun a : Fin r => ((FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    rw [← hp0]
    exact ho τ
  set D0 : Matrix (Fin W.g) (Fin W.g) ℂ :=
    Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) with hD0
  have hD : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im = (hermForm D0 (W.Pm a) (W.Pm b)).im := by
    intro a b
    rw [Wu.c1 a b, hD0, GlobalTheory.OrthoHerm.im_diag_eq_trace Dw.q (-(U.X k).ξ0) (U.X k).Gm (U.X k).Ψ
      (U.X k).cmType idx hcc x.1 hx (W.φ k a : Fin r → E) (W.φ k b : Fin r → E) (W.Pm a) (W.Pm b)
      (hz a) (hz b), ← W.isom k a b]
    push_cast
    rfl
  have hD0h : D0.IsHermitian := by
    rw [hD0]
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext j
    simp
  obtain ⟨-, -, -, hspan, -⟩ := W.per
  have hHm : Wu.Hm = D0 := eq_of_im_hermForm_eq_of_real_span_eq_univ Wu.Hm D0 Wu.herm hD0h W.Pm hspan hD
  rw [hHm, hD0]
  congr 1
  funext j
  have hpos := Wu.pos (Pi.single j 1) (by simp)
  rw [hHm, hD0] at hpos
  have hdiag : (hermForm (Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ))
      (Pi.single j 1) (Pi.single j 1)).re = 2 * ((idx j).1.1 (-(U.X k).ξ0)).im := by
    simp [hermForm]
  rw [hdiag, map_neg, Complex.neg_im] at hpos
  have hre : ((idx j).1.1 (U.X k).ξ0).re = 0 := by
    have h1 : starRingEnd ℂ ((idx j).1.1 (U.X k).ξ0) = -((idx j).1.1 (U.X k).ξ0) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj (φ := (idx j).1.1) (x := (U.X k).ξ0),
        ← map_neg]
      congr 1
      exact (U.X k).ξ0_im
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hnorm : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖(idx j).1.1 (U.X k).ξ0‖ := by
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1]
    · rw [h1, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  have hfin : ((idx j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    rw [hnorm, ← (Complex.abs_im_eq_norm).mpr hre, map_neg, Complex.neg_im,
      abs_of_neg (by linarith)]
  rw [hfin]

end GlobalTheory.HermDiag
