import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL he j z hj`. Establish `hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i` using `fun z => by`. Establish `h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i`. Rewrite using `[Xo.univ.t.PP.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Conclude with `⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩`. Use `choose ch hc using hch`. Establish `hyx : y'.x = y.x`. Establish `h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x` using `Over.w (A.ex 0)`.

Establish `h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x` using `Over.w (A'.ex 0)`. Rewrite using `[← h1, ← h2, he]`. Establish `ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0` using `fun j z h => A'.fr_ne j z (by rw [he]; exact h)`. Set `q : (Fin g → ℂ) → ℂ` to `fun z => A.fr (ch z) z / A'.fr (ch z) z`. Establish `key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z` using `fun j z h => by`.

Establish `hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z))` using `fun p hp => ⟨h hp, hc z hp⟩`. Establish `h1` using `A.fr_g j (ch z) z hz`. Establish `h2` using `A'.fr_g j (ch z) z (by rw [he]; exact hz)`. Rewrite `h2` using `[he]`. Rewrite using `[h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]`.

Establish `hq : Differentiable ℂ q` using `fun z0 => by`. Establish `hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)}`. Simplify using `using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1`. Establish `h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)}`. Simplify `A'.fr_hol (ch z0)` using `only [he]`.

Establish `hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)}` using `((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz => (key _ z hz).trans (div_eq_mul_inv _ _)`. Conclude with `hd.differentiableAt (hO.mem_nhds (hc z0))`. Set `pvh : (Fin r → E) →+ (Fin g → ℂ)` to `AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add`. Set `P : L →+ (Fin g → ℂ)` to `pvh.comp L.subtype.toAddMonoidHom`. Establish `hP : Submodule.span ℝ (Set.range P) = ⊤`.

Rewrite using `[← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]`. Use `congr 1`. Use extensionality with `w`. Conclude with `⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩`. Establish `hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖` using `fun z a => by`.

Establish `h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z)`. Rewrite using `[GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]`. Conclude with `hc z`. Establish `h1` using `A.fr_per a a.2 (ch z) z (hc z)`. Establish `h2` using `A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)`.

Express the relevant statement in the definitionally equal form `‖q (z + pv X idx x a)‖ = _`. Rewrite using `[key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, A.χ_norm _ a.2, A'.χ_norm _ a.2, mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]`. Establish `hc0` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0`. Establish `h0 : q 0 = 1`. Use `A'.fr_0 (ch 0) (by rw [he]; exact hc 0)` as an intermediate fact.

Rewrite `this` using `[hyx, ← A.fr_0 (ch 0) (hc 0)]`. Express the relevant statement in the definitionally equal form `A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1`. Rewrite using `[this, div_self (A.fr_ne _ _ (hc 0))]`. Rewrite `hc0` using `[h0, key j z hj]`. Conclude with `((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm`.
-/
theorem GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL he j z hj
  have hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := fun z => by
    have h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hc using hch
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0 :=
    fun j z h => A'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => A.fr (ch z) z / A'.fr (ch z) z
  have key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := A.fr_g j (ch z) z hz
    have h2 := A'.fr_g j (ch z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1
    have h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa only [he] using A'.fr_hol (ch z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} :=
      ((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add
  let P : L →+ (Fin g → ℂ) := pvh.comp L.subtype.toAddMonoidHom
  have hP : Submodule.span ℝ (Set.range P) = ⊤ := by
    rw [← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]
    congr 1
    ext w
    exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩
  have hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖ := fun z a => by
    have h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z) := by
      rw [GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]; exact hc z
    have h1 := A.fr_per a a.2 (ch z) z (hc z)
    have h2 := A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)
    change ‖q (z + pv X idx x a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      A.χ_norm _ a.2, A'.χ_norm _ a.2,
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0
  have h0 : q 0 = 1 := by
    have := A'.fr_0 (ch 0) (by rw [he]; exact hc 0)
    rw [hyx, ← A.fr_0 (ch 0) (hc 0)] at this
    change A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1
    rw [this, div_self (A.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact ((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm
