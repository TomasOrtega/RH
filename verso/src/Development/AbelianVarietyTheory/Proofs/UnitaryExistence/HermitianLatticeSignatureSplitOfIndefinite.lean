import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignatureStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignatureStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryConjSplitLatticeOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicOfIndefinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrSelfDual

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat GlobalTheory.HermModel
open scoped nonZeroDivisors

namespace GlobalTheory.SplitGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Use `haveI : IsLocalizedModule (𝓞 E)⁰ φ := { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s surj := fun v => by`. Establish `hv : v ∈ Submodule.span E (Set.range φ)` using `by rw [hspan]; trivial`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv`. Rewrite `ht` using `[← LinearMap.coe_range, Submodule.span_eq]`. Take `⟨m, hm⟩` from `ht`.

Conclude with `⟨(m, t), hm.symm⟩`. Use `exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }`. Set `g` to `IsLocalizedModule.lift (𝓞 E)⁰ φ ψ (fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s)`. Use `⟨LinearMap.toMatrix' (g.extendScalarsOfIsLocalization (𝓞 E)⁰ E), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`.

Conclude with `IsLocalizedModule.lift_apply (𝓞 E)⁰ φ ψ (fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s) x`.
-/
theorem exists_matrix {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (φ ψ : M →ₗ[𝓞 E] (Fin r → E))
    (hf : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤) :
    ∃ A : Matrix (Fin r) (Fin r) E, ∀ x, A *ᵥ φ x = ψ x := by
  haveI : IsLocalizedModule (𝓞 E)⁰ φ :=
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun v => by
        have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
        rw [← LinearMap.coe_range, Submodule.span_eq] at ht
        obtain ⟨m, hm⟩ := ht
        exact ⟨(m, t), hm.symm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  let g := IsLocalizedModule.lift (𝓞 E)⁰ φ ψ
    (fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s)
  refine ⟨LinearMap.toMatrix' (g.extendScalarsOfIsLocalization (𝓞 E)⁰ E), fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact IsLocalizedModule.lift_apply (𝓞 E)⁰ φ ψ
    (fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s) x

/- English proof (translation)
Simplify using `[FD.herm, add_mul, Finset.sum_add_distrib]`.
-/
theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    FD.herm G (x + x') y = FD.herm G x y + FD.herm G x' y := by
  simp [FD.herm, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[FD.herm]`.
-/
theorem herm_zero_left (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E) : FD.herm G 0 x = 0 := by
  simp [FD.herm]

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E S` using `hS ▸ Submodule.mem_top`. Establish `hy : y ∈ Submodule.span E S` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `zero => simp only [mulVec_zero, herm_zero_left]`. Consider the case `add a b _ _ ha hb => simp only [mulVec_add, herm_add_left, ha, hb]`.

Consider the case `smul c a _ ha => simp only [mulVec_smul, herm_smul_left, ha]`. Consider the case `mem x hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `zero => simp only [mulVec_zero, herm_zero_right]`. Consider the case `add a b _ _ ha hb => simp only [mulVec_add, herm_add_right, ha, hb]`.

Consider the case `smul c a _ ha => simp only [mulVec_smul, herm_smul_right, ha]`. Consider the case `mem y hy => exact h x hx y hy`.
-/
theorem herm_ext (G A B C D : Matrix (Fin r) (Fin r) E) {S : Set (Fin r → E)} (hS : Submodule.span E S = ⊤)
    (h : ∀ x ∈ S, ∀ y ∈ S, FD.herm G (A *ᵥ x) (B *ᵥ y) = FD.herm G (C *ᵥ x) (D *ᵥ y)) (x y : Fin r → E) :
    FD.herm G (A *ᵥ x) (B *ᵥ y) = FD.herm G (C *ᵥ x) (D *ᵥ y) := by
  have hx : x ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | zero => simp only [mulVec_zero, herm_zero_left]
  | add a b _ _ ha hb => simp only [mulVec_add, herm_add_left, ha, hb]
  | smul c a _ ha => simp only [mulVec_smul, herm_smul_left, ha]
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | zero => simp only [mulVec_zero, herm_zero_right]
    | add a b _ _ ha hb => simp only [mulVec_add, herm_add_right, ha, hb]
    | smul c a _ ha => simp only [mulVec_smul, herm_smul_right, ha]
    | mem y hy => exact h x hx y hy

/- English proof (translation)
Establish `: ξ * (FD.herm G u v - FD.herm G u' v') = 0` using `eq_zero_of_trace_mul_integer fun a => by`. Establish `h1` using `h a`. Rewrite `h1` using `[show a • u = (a : E) • u from rfl, show a • u' = (a : E) • u' from rfl, herm_smul_left, herm_smul_left]`. Rewrite `h1` using `[← sub_eq_zero, ← map_sub]`. Rewrite using `[← h1]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hξ)`.
-/
theorem herm_eq_of_trace (G : Matrix (Fin r) (Fin r) E) {ξ : E} (hξ : ξ ≠ 0) {u v u' v' : Fin r → E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (ξ * FD.herm G (a • u) v) = Algebra.trace ℚ E (ξ * FD.herm G (a • u') v')) :
    FD.herm G u v = FD.herm G u' v' := by
  have : ξ * (FD.herm G u v - FD.herm G u' v') = 0 := eq_zero_of_trace_mul_integer fun a => by
    have h1 := h a
    rw [show a • u = (a : E) • u from rfl, show a • u' = (a : E) • u' from rfl, herm_smul_left,
      herm_smul_left] at h1
    rw [← sub_eq_zero, ← map_sub] at h1
    rw [← h1]
    congr 1
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hξ)

/- English proof (translation)
Rewrite using `[herm_smul_left, herm_smul_right]`. Establish `hc : FD.cc (N : E) = N` using `by simp [FD.cc]`. Establish `h3 : ξ * ((N : E) * (FD.herm G u v * FD.cc (N : E))) = ((N : ℚ) ^ 2) • (ξ * FD.herm G u v)`. Rewrite using `[hc, Algebra.smul_def]`. Simplify using `only [map_pow, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, map_smul, smul_eq_mul]`.
-/
theorem trace_nsmul (G : Matrix (Fin r) (Fin r) E) (ξ : E) (N : ℕ) (u v : Fin r → E) :
    Algebra.trace ℚ E (ξ * FD.herm G ((N : E) • u) ((N : E) • v)) =
      (N : ℚ) ^ 2 * Algebra.trace ℚ E (ξ * FD.herm G u v) := by
  rw [herm_smul_left, herm_smul_right]
  have hc : FD.cc (N : E) = N := by simp [FD.cc]
  have h3 : ξ * ((N : E) * (FD.herm G u v * FD.cc (N : E))) = ((N : ℚ) ^ 2) • (ξ * FD.herm G u v) := by
    rw [hc, Algebra.smul_def]
    simp only [map_pow, map_natCast]
    ring
  rw [h3, map_smul, smul_eq_mul]

omit [IsCMField E] in

/- English proof (translation)
Establish `hn : ¬ ComplexEmbedding.IsReal τ` using `IsTotallyComplex.complexEmbedding_not_isReal τ`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, (τ x).im ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hn (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (h x)))`.

Set `f : ℝ × ℝ → ℂ` to `fun p => (p.1 : ℂ) + (p.2 : ℂ) * τ x`. Establish `hf : Continuous f` using `by fun_prop`. Establish `hs : Function.Surjective f` using `fun z => ⟨(z.re - z.im / (τ x).im * (τ x).re, z.im / (τ x).im), by`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[f, -Complex.ofReal_div]`.

Simplify using `[f, -Complex.ofReal_div, hx]⟩`. Establish `hd : DenseRange (f ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))` using `hs.denseRange.comp (Rat.denseRange_cast.prodMap Rat.denseRange_cast) hf`. Use `Dense.mono ?_ hd` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `⟨(p.1 : E) + (p.2 : E) * x, by simp [f]⟩`.
-/
theorem denseRange_emb [IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  have hn : ¬ ComplexEmbedding.IsReal τ := IsTotallyComplex.complexEmbedding_not_isReal τ
  obtain ⟨x, hx⟩ : ∃ x, (τ x).im ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (h x)))
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * τ x
  have hf : Continuous f := by fun_prop
  have hs : Function.Surjective f := fun z =>
    ⟨(z.re - z.im / (τ x).im * (τ x).re, z.im / (τ x).im), by
      apply Complex.ext
      · simp [f, -Complex.ofReal_div]
      · simp [f, -Complex.ofReal_div, hx]⟩
  have hd : DenseRange (f ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    hs.denseRange.comp (Rat.denseRange_cast.prodMap Rat.denseRange_cast) hf
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1 : E) + (p.2 : E) * x, by simp [f]⟩

/- English proof (translation)
Establish `hd : DenseRange (Pi.map fun _ : Fin r => (τ : E → ℂ))` using `DenseRange.piMap fun _ => denseRange_emb τ`. Establish `hc : Continuous fun u : Fin r → ℂ => (FD.hermC τ G u u).re`. Unfold `FD.hermC`. Use `fun_prop`. Take `⟨x, hx⟩` from `hd.exists_mem_open (hU.preimage hc) ⟨u, hu⟩`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `: τ (FD.herm G x x) = FD.hermC τ G (τ ∘ x) (τ ∘ x)`. Simplify using `[FD.herm, FD.hermC, FD.cc, IsCMField.complexEmbedding_complexConj]`. Rewrite using `[this]`. Conclude with `hx`.
-/
theorem exists_rat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {U : Set ℝ} (hU : IsOpen U) (u : Fin r → ℂ)
    (hu : (FD.hermC τ G u u).re ∈ U) : ∃ x, (τ (FD.herm G x x)).re ∈ U := by
  have hd : DenseRange (Pi.map fun _ : Fin r => (τ : E → ℂ)) := DenseRange.piMap fun _ => denseRange_emb τ
  have hc : Continuous fun u : Fin r → ℂ => (FD.hermC τ G u u).re := by
    unfold FD.hermC
    fun_prop
  obtain ⟨x, hx⟩ := hd.exists_mem_open (hU.preimage hc) ⟨u, hu⟩
  refine ⟨x, ?_⟩
  have : τ (FD.herm G x x) = FD.hermC τ G (τ ∘ x) (τ ∘ x) := by
    simp [FD.herm, FD.hermC, FD.cc, IsCMField.complexEmbedding_complexConj]
  rw [this]; exact hx

/- English proof (translation)
Take `⟨P, -, hP⟩` from `h`. Prove the components needed by the constructor for the conclusion. Establish `e` using `congrFun (congrFun hP ⟨0, h0.trans h1⟩) ⟨0, h0.trans h1⟩`. Use `exists_rat τ G (U := Set.Ioi 0) isOpen_Ioi (FD.col P ⟨0, h0.trans h1⟩) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `FD.hermC τ G _ _ = _ at e`.

Rewrite using `[Set.mem_Ioi, e]`. Simplify using `[FD.sgn, h0]`. Establish `e` using `congrFun (congrFun hP ⟨p, h1⟩) ⟨p, h1⟩`. Use `exists_rat τ G (U := Set.Iio 0) isOpen_Iio (FD.col P ⟨p, h1⟩) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `FD.hermC τ G _ _ = _ at e`.

Rewrite using `[Set.mem_Iio, e]`. Simplify using `[FD.sgn]`.
-/
theorem both_signs (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {p : ℕ} (h0 : 0 < p) (h1 : p < r)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) :
    (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0 := by
  obtain ⟨P, -, hP⟩ := h
  constructor
  · have e := congrFun (congrFun hP ⟨0, h0.trans h1⟩) ⟨0, h0.trans h1⟩
    refine exists_rat τ G (U := Set.Ioi 0) isOpen_Ioi (FD.col P ⟨0, h0.trans h1⟩) ?_
    change FD.hermC τ G _ _ = _ at e
    rw [Set.mem_Ioi, e]
    simp [FD.sgn, h0]
  · have e := congrFun (congrFun hP ⟨p, h1⟩) ⟨p, h1⟩
    refine exists_rat τ G (U := Set.Iio 0) isOpen_Iio (FD.col P ⟨p, h1⟩) ?_
    change FD.hermC τ G _ _ = _ at e
    rw [Set.mem_Iio, e]
    simp [FD.sgn]

variable {H : Host E}

/- English proof (translation)
Establish `hξ` using `GlobalTheory.OneSpace.cc_rt H`. Establish `hr` using `(rank_integral_selfDual E H D r _ G φ hξ hM).1`. Establish `key : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0`. Introduce `τ hτ`. Establish `s` using `GlobalTheory.T.signature_hermitian_model_of_datum E H D r _ G φ hξ hM τ hτ`.

Break down `lt_or_gt_of_ne (GlobalTheory.OneSpace.im_ne τ hξ (GlobalTheory.OneSpace.rt_ne H)) with h | h` into its components or cases. Conclude with `both_signs τ G (by omega) (by omega) (s.2 h)`. Conclude with `both_signs τ G (by omega) (by omega) (s.1 h)`. Establish `h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2` using `by rw [GlobalTheory.OneSpace.emb_rt_sq, H.sqrt_neg_disc_sq]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases.

Conclude with `key τ h`. Use `key (ComplexEmbedding.conjugate τ) (by` as an intermediate fact. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, GlobalTheory.OneSpace.conj_of_sq H.d_prime.pos (GlobalTheory.OneSpace.emb_rt_sq H τ), h, neg_neg])`. Simplify `this` using `only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]`.
-/
theorem indefinite (D : Datum H) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (G : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (hM : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E ((H.rt : E) * FD.herm G (φ x) (φ y))) (τ : E →+* ℂ) :
    (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0 := by
  have hξ := GlobalTheory.OneSpace.cc_rt H
  have hr := (rank_integral_selfDual E H D r _ G φ hξ hM).1
  have key : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0 := by
    intro τ hτ
    have s := GlobalTheory.T.signature_hermitian_model_of_datum E H D r _ G φ hξ hM τ hτ
    rcases lt_or_gt_of_ne (GlobalTheory.OneSpace.im_ne τ hξ (GlobalTheory.OneSpace.rt_ne H)) with h | h
    · exact both_signs τ G (by omega) (by omega) (s.2 h)
    · exact both_signs τ G (by omega) (by omega) (s.1 h)
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [GlobalTheory.OneSpace.emb_rt_sq, H.sqrt_neg_disc_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact key τ h
  · have := key (ComplexEmbedding.conjugate τ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, GlobalTheory.OneSpace.conj_of_sq H.d_prime.pos (GlobalTheory.OneSpace.emb_rt_sq H τ), h,
        neg_neg])
    simpa only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] using this

/- English proof (translation)
Use `D.fin` as an intermediate fact. Use `D₀.fin` as an intermediate fact. Establish `htop : Lp.comap g ⊔ Lm.comap g = ⊤`. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations. Take `⟨a, ha, hb⟩` from `hs x`.

Conclude with `Submodule.mem_sup.2 ⟨a, ha, x - a, hb, add_sub_cancel _ _⟩`. Establish `le : ∀ L : Submodule (𝓞 E) D₀.La, Module.finrank (𝓞 E) (L.comap g) ≤ Module.finrank (𝓞 E) L` using `fun L => LinearMap.finrank_le_finrank_of_injective (f := g.restrict (p := L.comap g) (q := L) fun _ h => h) fun a b h => Subtype.ext (hg (congrArg Subtype.val h))`. Establish `h1` using `Submodule.rank_add_le_rank_add_rank (Lp.comap g) (Lm.comap g)`. Rewrite `h1` using `[htop, rank_top, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, D.rank]`. Establish `h2 : D.p + D.q ≤ Module.finrank (𝓞 E) (Lp.comap g) + Module.finrank (𝓞 E) (Lm.comap g)`.

Conclude with `h1` after adjusting the coercions. Establish `h3` using `le Lp`. Establish `h4` using `le Lm`. Establish `hN' : (0 : ℝ) < (N : ℝ) ^ 2` using `by positivity`. Establish `e : ∀ a, H.rt0.im * D₀.EF (H.rt • g a) (g a) = (N : ℝ) ^ 2 * (H.rt0.im * D.EF (H.rt • a) a)` using `fun a => by`.

Rewrite using `[← map_smul, hE]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Lp.comap g, Lm.comap g, htop, fun a ha b hb => ?_, by omega, by omega, fun a ha h0 => ?_, fun a ha h0 => ?_⟩` and prove the remaining obligations. Use `ho _ ha _ hb` as an intermediate fact.

Rewrite `this` using `[hE]`. Conclude with `(mul_eq_zero.1 this).resolve_left (by positivity)`. Use `sp _ ha fun h => h0 (hg (h.trans (map_zero g).symm))` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `(mul_pos_iff_of_pos_left hN').1 this`.

Use `sm _ ha fun h => h0 (hg (h.trans (map_zero g).symm))` as an intermediate fact. Rewrite `this` using `[e]`. Assume the negation of the conclusion as `hh`. Conclude with `absurd this (not_lt.2 (mul_nonneg hN'.le (not_lt.1 hh)))`.
-/
theorem split_of_scaled (D D₀ : Datum H) (hp : D₀.p = D.p) (hq : D₀.q = D.q) (Lp Lm : Submodule (𝓞 E) D₀.La)
    (ho : ∀ a ∈ Lp, ∀ b ∈ Lm, D₀.EF a b = 0) (rp : Module.finrank (𝓞 E) Lp = D₀.p)
    (rm : Module.finrank (𝓞 E) Lm = D₀.q) (sp : ∀ a ∈ Lp, a ≠ 0 → 0 < H.rt0.im * D₀.EF (H.rt • a) a)
    (sm : ∀ a ∈ Lm, a ≠ 0 → H.rt0.im * D₀.EF (H.rt • a) a < 0) (N : ℕ) (hN : 0 < N) (g : D.La →ₗ[𝓞 E] D₀.La)
    (hg : Function.Injective g) (hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y)
    (hs : ∀ x, ∃ a, g a ∈ Lp ∧ g (x - a) ∈ Lm) : SplitLat D := by
  have := D.fin
  have := D₀.fin
  have htop : Lp.comap g ⊔ Lm.comap g = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hb⟩ := hs x
    exact Submodule.mem_sup.2 ⟨a, ha, x - a, hb, add_sub_cancel _ _⟩
  have le : ∀ L : Submodule (𝓞 E) D₀.La, Module.finrank (𝓞 E) (L.comap g) ≤ Module.finrank (𝓞 E) L := fun L =>
    LinearMap.finrank_le_finrank_of_injective (f := g.restrict (p := L.comap g) (q := L) fun _ h => h)
      fun a b h => Subtype.ext (hg (congrArg Subtype.val h))
  have h1 := Submodule.rank_add_le_rank_add_rank (Lp.comap g) (Lm.comap g)
  rw [htop, rank_top, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, D.rank] at h1
  have h2 : D.p + D.q ≤ Module.finrank (𝓞 E) (Lp.comap g) + Module.finrank (𝓞 E) (Lm.comap g) := by
    exact_mod_cast h1
  have h3 := le Lp
  have h4 := le Lm
  have hN' : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have e : ∀ a, H.rt0.im * D₀.EF (H.rt • g a) (g a) = (N : ℝ) ^ 2 * (H.rt0.im * D.EF (H.rt • a) a) := fun a => by
    rw [← map_smul, hE]
    push_cast
    ring
  refine ⟨Lp.comap g, Lm.comap g, htop, fun a ha b hb => ?_, by omega, by omega, fun a ha h0 => ?_,
    fun a ha h0 => ?_⟩
  · have := ho _ ha _ hb
    rw [hE] at this
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  · have := sp _ ha fun h => h0 (hg (h.trans (map_zero g).symm))
    rw [e] at this
    exact (mul_pos_iff_of_pos_left hN').1 this
  · have := sm _ ha fun h => h0 (hg (h.trans (map_zero g).symm))
    rw [e] at this
    by_contra hh
    exact absurd this (not_lt.2 (mul_nonneg hN'.le (not_lt.1 hh)))

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨v, hv, e⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Conclude with `hv (eq_zero_of_herm_eq_zero hG fun u => by rw [← h, e, herm_zero_left])`.
-/
theorem isUnit_det {G γ : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    (h : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y) : IsUnit γ.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  exact hv (eq_zero_of_herm_eq_zero hG fun u => by rw [← h, e, herm_zero_left])

/- English proof (translation)
Take `⟨N, hN, hmem⟩` from `GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ hspan`. Use `⟨N, (LinearEquiv.ofInjective φ₀ hinj).symm.toLinearMap ∘ₗ ((N : 𝓞 E) • φ).codRestrict _ hmem, hN, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearEquiv.ofInjective_symm_apply φ₀ (h := hinj) (((N : 𝓞 E) • φ).codRestrict _ hmem x)`. Use `h1.trans ?_` and prove the remaining obligations. Use `show (N : 𝓞 E) • φ x = _`.

Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`.
-/
theorem exists_scaled_map {M M₀ : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [AddCommGroup M₀] [Module (𝓞 E) M₀] (φ : M →ₗ[𝓞 E] (Fin r → E)) (φ₀ : M₀ →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ₀) (hspan : Submodule.span E (Set.range φ₀) = ⊤) :
    ∃ (N : ℕ) (g : M →ₗ[𝓞 E] M₀), 0 < N ∧ ∀ x, φ₀ (g x) = (N : E) • φ x := by
  obtain ⟨N, hN, hmem⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ hspan
  refine ⟨N, (LinearEquiv.ofInjective φ₀ hinj).symm.toLinearMap ∘ₗ ((N : 𝓞 E) • φ).codRestrict _ hmem, hN,
    fun x => ?_⟩
  have h1 := LinearEquiv.ofInjective_symm_apply φ₀ (h := hinj) (((N : 𝓞 E) • φ).codRestrict _ hmem x)
  refine h1.trans ?_
  show (N : 𝓞 E) • φ x = _
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Set `P : D₀.La →ₗ[𝓞 E] D₀.La` to `Lp.subtype ∘ₗ Lp.linearProjOfIsCompl Lm hc`. Establish `hP1 : ∀ y, P y ∈ Lp` using `fun y => (Lp.linearProjOfIsCompl Lm hc y).2`. Establish `hP2 : ∀ y ∈ Lp, P y = y` using `fun y hy => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)`. Establish `hP3 : ∀ y, P y = 0 ↔ y ∈ Lm` using `fun y => by`. Rewrite using `[← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc]`.

Conclude with `Submodule.coe_eq_zero`. Establish `hP4 : ∀ y, y - P y ∈ Lm` using `fun y => by rw [← hP3, map_sub, hP2 _ (hP1 y), sub_self]`. Take `⟨π, hπ⟩` from `exists_matrix φ₀ (φ₀ ∘ₗ P) hinj hspan`. Establish `hπ' : ∀ y, π *ᵥ φ₀ y = φ₀ (P y)` using `hπ`. Establish `o1 : ∀ a ∈ Lp, ∀ b ∈ Lm, FD.herm G (φ₀ a) (φ₀ b) = 0` using `fun a ha b hb => by`.

Rewrite using `[← herm_zero_left G (φ₀ b)]`. Use `herm_eq_of_trace G (GlobalTheory.OneSpace.rt_ne H) fun s => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← hEF, ho _ (Lp.smul_mem s ha) b hb, smul_zero, herm_zero_left]`. Simplify using the standard rewrite rules. Establish `o2 : ∀ a ∈ Lp, ∀ b ∈ Lm, FD.herm G (φ₀ b) (φ₀ a) = 0` using `fun a ha b hb => by`.

Use `GlobalTheory.UTrans.Calc.hf_conj (IsCMField.complexConj E : E →+* E) G (fun a => IsCMField.complexConj_apply_apply E a) hG (φ₀ a) (φ₀ b)` as an intermediate fact. Use `this.symm.trans ?_` and prove the remaining obligations. Rewrite using `[show GlobalTheory.UTrans.hf (IsCMField.complexConj E : E →+* E) G (φ₀ a) (φ₀ b) = 0 from o1 a ha b hb, map_zero]`. Use `⟨π, ?_, fun v w => ?_, fun y => ⟨_, (hπ' y).symm⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y h => ?_⟩` and prove the remaining obligations. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Use `LinearMap.ext_on_range hspan fun y => ?_` and prove the remaining obligations. Rewrite using `[toLin'_apply, toLin'_apply, ← mulVec_mulVec, hπ', hπ', hP2 _ (hP1 y)]`. Use `herm_ext G π 1 1 π hspan (by` as an intermediate fact. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[one_mulVec, one_mulVec, hπ', hπ']`.

Establish `e1 : FD.herm G (φ₀ (P x)) (φ₀ y) = FD.herm G (φ₀ (P x)) (φ₀ (P y))` using `by conv_lhs => rw [← add_sub_cancel (P y) y, map_add, herm_add_right, o1 _ (hP1 x) _ (hP4 y), add_zero]`. Establish `e2 : FD.herm G (φ₀ x) (φ₀ (P y)) = FD.herm G (φ₀ (P x)) (φ₀ (P y))` using `by conv_lhs => rw [← add_sub_cancel (P x) x, map_add, herm_add_left, o2 _ (hP1 y) _ (hP4 x), add_zero]`. Rewrite using `[e1, e2]) v w`. Rewrite `this` using `[one_mulVec, one_mulVec]`. Then use the resulting hypothesis. Rewrite `h` using `[hπ']`.

Rewrite using `[← hinj h]`. Conclude with `hP1 y`. Rewrite using `[hπ', hP2 y h]`. Rewrite `h` using `[hπ', ← map_zero φ₀]`. Conclude with `(hP3 y).1 (hinj h)`.
-/
theorem exists_projector (D₀ : Datum H) (G : Matrix (Fin r) (Fin r) E) (φ₀ : D₀.La →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ₀) (hspan : Submodule.span E (Set.range φ₀) = ⊤)
    (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hEF : ∀ x y, ((D₀.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E ((H.rt : E) * FD.herm G (φ₀ x) (φ₀ y)))
    (Lp Lm : Submodule (𝓞 E) D₀.La) (hc : IsCompl Lp Lm) (ho : ∀ a ∈ Lp, ∀ b ∈ Lm, D₀.EF a b = 0) :
    ∃ π : Matrix (Fin r) (Fin r) E, π * π = π ∧ (∀ v w, FD.herm G (π *ᵥ v) w = FD.herm G v (π *ᵥ w)) ∧
      (∀ y, π *ᵥ φ₀ y ∈ LinearMap.range φ₀) ∧ (∀ y, π *ᵥ φ₀ y = φ₀ y ↔ y ∈ Lp) ∧
      ∀ y, π *ᵥ φ₀ y = 0 → y ∈ Lm := by
  let P : D₀.La →ₗ[𝓞 E] D₀.La := Lp.subtype ∘ₗ Lp.linearProjOfIsCompl Lm hc
  have hP1 : ∀ y, P y ∈ Lp := fun y => (Lp.linearProjOfIsCompl Lm hc y).2
  have hP2 : ∀ y ∈ Lp, P y = y := fun y hy => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)
  have hP3 : ∀ y, P y = 0 ↔ y ∈ Lm := fun y => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc]
    exact Submodule.coe_eq_zero
  have hP4 : ∀ y, y - P y ∈ Lm := fun y => by rw [← hP3, map_sub, hP2 _ (hP1 y), sub_self]
  obtain ⟨π, hπ⟩ := exists_matrix φ₀ (φ₀ ∘ₗ P) hinj hspan
  have hπ' : ∀ y, π *ᵥ φ₀ y = φ₀ (P y) := hπ
  have o1 : ∀ a ∈ Lp, ∀ b ∈ Lm, FD.herm G (φ₀ a) (φ₀ b) = 0 := fun a ha b hb => by
    rw [← herm_zero_left G (φ₀ b)]
    refine herm_eq_of_trace G (GlobalTheory.OneSpace.rt_ne H) fun s => ?_
    rw [← map_smul, ← hEF, ho _ (Lp.smul_mem s ha) b hb, smul_zero, herm_zero_left]
    simp
  have o2 : ∀ a ∈ Lp, ∀ b ∈ Lm, FD.herm G (φ₀ b) (φ₀ a) = 0 := fun a ha b hb => by
    have := GlobalTheory.UTrans.Calc.hf_conj (IsCMField.complexConj E : E →+* E) G
      (fun a => IsCMField.complexConj_apply_apply E a) hG (φ₀ a) (φ₀ b)
    refine this.symm.trans ?_
    rw [show GlobalTheory.UTrans.hf (IsCMField.complexConj E : E →+* E) G (φ₀ a) (φ₀ b) = 0 from o1 a ha b hb, map_zero]
  refine ⟨π, ?_, fun v w => ?_, fun y => ⟨_, (hπ' y).symm⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y h => ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan fun y => ?_
    rw [toLin'_apply, toLin'_apply, ← mulVec_mulVec, hπ', hπ', hP2 _ (hP1 y)]
  · have := herm_ext G π 1 1 π hspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [one_mulVec, one_mulVec, hπ', hπ']
      have e1 : FD.herm G (φ₀ (P x)) (φ₀ y) = FD.herm G (φ₀ (P x)) (φ₀ (P y)) := by
        conv_lhs => rw [← add_sub_cancel (P y) y, map_add, herm_add_right, o1 _ (hP1 x) _ (hP4 y), add_zero]
      have e2 : FD.herm G (φ₀ x) (φ₀ (P y)) = FD.herm G (φ₀ (P x)) (φ₀ (P y)) := by
        conv_lhs => rw [← add_sub_cancel (P x) x, map_add, herm_add_left, o2 _ (hP1 y) _ (hP4 x), add_zero]
      rw [e1, e2]) v w
    rwa [one_mulVec, one_mulVec] at this
  · rw [hπ'] at h
    rw [← hinj h]
    exact hP1 y
  · rw [hπ', hP2 y h]
  · rw [hπ', ← map_zero φ₀] at h
    exact (hP3 y).1 (hinj h)

/- English proof (translation)
Introduce `E _ _ _ H D h1 h3 hp hq`. Take `⟨D₀, ep, eq, Lp, Lm, htop, ho, rp, rm, sp, sm⟩` from `GlobalTheory.T.exists_splitLattice_datum_every_signature E H D.p D.q h1`. Use `D.fin` as an intermediate fact. Use `D₀.fin` as an intermediate fact. Establish `hξ` using `GlobalTheory.OneSpace.cc_rt H`.

Establish `hξ0` using `GlobalTheory.OneSpace.rt_ne H`. Take `⟨G, φ₀, hM₀⟩` from `GlobalTheory.exists_herm_coord_of_datum E H D₀ (H.rt : E) hξ hξ0 (D.p + D.q) (by rw [ep, eq])`. Take `⟨φ, hM⟩` from `GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt E H D₀ D _ (H.rt : E) G φ₀ ep.symm eq.symm hξ hM₀`. Establish `hind` using `indefinite D hp hq G φ hM`. Take `⟨-, hfg, -, hdual⟩` from `rank_integral_selfDual E H D _ _ G φ hξ hM`.

Take `⟨inj₀, span₀, hG, hdet, hEF₀⟩` from `hM₀`. Take `⟨inj, span, -, -, hEF⟩` from `hM`. Establish `hc : IsCompl Lp Lm`. Use `⟨Submodule.disjoint_def.2 fun a ha hb => ?_, codisjoint_iff.2 htop⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Conclude with `lt_asymm (sp a ha h0) (sm a hb h0)`. Take `⟨π, π1, π2, π3, π4, π5⟩` from `exists_projector D₀ G φ₀ inj₀ span₀ hG hEF₀ Lp Lm hc ho`. Establish `hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G`. Use `⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩` and prove the remaining obligations. Establish `h2 : (H.rt : E) = -(H.rt : E)` using `h.symm.trans hξ`.

Take the linear combination `(1 / 2 : E) * h2`. Establish `hz` using `GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind`. Establish `: Nontrivial Lp` using `Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by omega)`. Take `⟨⟨a, ha⟩, ha0⟩` from `exists_ne (0 : Lp)`. Establish `hxx : FD.herm G (φ₀ a) (φ₀ a) ≠ 0`.

Introduce `h`. Establish `h5` using `sp a ha fun h => ha0 (Subtype.ext h)`. Establish `h6` using `hEF₀ (H.rt • a) a`. Rewrite `h6` using `[map_smul φ₀, show H.rt • φ₀ a = (H.rt : E) • φ₀ a from rfl, herm_smul_left, h, mul_zero, mul_zero, map_zero]`. Establish `h7 : D₀.EF (H.rt • a) a = 0` using `by exact_mod_cast h6`.

Rewrite `h5` using `[h7]`. Simplify using `at h5`. Take `⟨b₁, hb₁, m₁⟩` from `GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ span₀`. Take `⟨b₂, hb₂, m₂⟩` from `GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ₀ φ span`. Take `⟨k, f, hk, hf⟩` from `GlobalTheory.T.exists_coprime_scaled_isometry_same_signature E H D D₀ ep eq (2 * b₁ * b₂) (by positivity)`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Rewrite `hk` using `[Nat.coprime_zero_left]`. Rewrite `hk` using `[mul_assoc]`. Use linear arithmetic over natural numbers and integers.

Establish `hkE : (k : E) ≠ 0` using `by exact_mod_cast hk0`. Establish `hkQ : (k : ℚ) ^ 2 ≠ 0` using `by positivity`. Take `⟨A, hA⟩` from `exists_matrix φ (φ₀ ∘ₗ f) inj span`. Establish `hA' : ∀ x, (k : E) • (((k : E)⁻¹ • A) *ᵥ φ x) = φ₀ (f x)` using `fun x => by`. Rewrite using `[smul_mulVec, smul_smul, mul_inv_cancel₀ hkE, one_smul]`.

Conclude with `hA x`. Generalize the expression as in `(k : E)⁻¹ • A = γ₀ at hA'`. Establish `hU₀ : ∀ x y, FD.herm G (γ₀ *ᵥ x) (γ₀ *ᵥ y) = FD.herm G x y` using `fun x y => by`. Use `herm_ext G γ₀ γ₀ 1 1 span (by` as an intermediate fact. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`.

Rewrite using `[one_mulVec, one_mulVec]`. Use `herm_eq_of_trace G hξ0 fun s => ?_` and prove the remaining obligations. Rewrite using `[show s • γ₀ *ᵥ φ x = (s : E) • γ₀ *ᵥ φ x from rfl, ← mulVec_smul, show (s : E) • φ x = s • φ x from rfl, ← map_smul]`. Apply `mul_left_cancel₀ hkQ` to reduce the goal to its premises. Rewrite using `[← trace_nsmul, hA', hA', ← hEF₀, ← hEF, hf]`.

Use `push_cast`. Use the proof step `rfl) x y`. Rewrite `this` using `[one_mulVec, one_mulVec]`. Then use the resulting hypothesis. Establish `hd₀` using `isUnit_det hdet hU₀`. Take `⟨γ, hU, hγ⟩` from `GlobalTheory.T.exists_unitary_conj_split_lattice_of_local (maximalRealSubfield E) E (IsCMField.complexConj E) _ G (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hh hz (LinearMap.range φ) (LinearMap.range φ₀) hfg span π γ₀ (φ₀ a) (2 * b₁ * b₂) k π1 π2 ((π4 a).2 ha) hxx (by rint …`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[mul_right_comm, mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₁]`. Conclude with `nsmul_mem (m₁ x) _)`. Use the proof step `(by`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₂]`. Conclude with `nsmul_mem (m₂ x) _)`. Use `hU₀ hk`. Use the proof step `(by`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[← Nat.cast_smul_eq_nsmul E, hA']`. Conclude with `⟨_, rfl⟩)`. Use the proof step `(by`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `(hdual _).1 fun x => ⟨D₀.EF y (f x), ?_⟩` and prove the remaining obligations.

Rewrite using `[hEF₀, ← hA', ← Nat.cast_smul_eq_nsmul E, herm_smul_left, herm_smul_right, ← hU₀ (γ₀⁻¹ *ᵥ φ₀ y), mulVec_mulVec, mul_nonsing_inv _ hd₀, one_mulVec, show FD.cc (k : E) = k by simp [FD.cc], mul_comm (k : E)])`. Establish `hU' : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y` using `hU`. Establish `hd` using `isUnit_det hdet hU'`. Take `⟨N, g, hN, hg⟩` from `exists_scaled_map ((Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ) φ₀ inj₀ span₀`. Establish `hg' : ∀ x, φ₀ (g x) = (N : E) • γ *ᵥ φ x` using `hg`.

Establish `hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y` using `fun x y => by`. Use `hEF₀ (g x) (g y)` as an intermediate fact. Rewrite `this` using `[hg', hg', trace_nsmul, hU', ← hEF]`. Conclude with `this` after adjusting the coercions. Use `split_of_scaled D D₀ ep eq Lp Lm ho rp rm sp sm N hN g ?_ hE fun x => ?_` and prove the remaining obligations.

Use `(injective_iff_map_eq_zero g).2 fun x hx => D.unimod.1 ?_` and prove the remaining obligations. Use extensionality with `y`. Use `hE x y` as an intermediate fact. Rewrite `this` using `[hx, map_zero, LinearMap.zero_apply]`. Rewrite using `[map_zero, LinearMap.zero_apply]`.

Conclude with `(mul_eq_zero.1 this.symm).resolve_left (by positivity)`. Take `⟨c, hc⟩` from `hγ _ ⟨x, rfl⟩`. Establish `e : γ *ᵥ φ c = π *ᵥ (γ *ᵥ φ x)`. Rewrite using `[hc, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]`. Establish `e2 : π *ᵥ (γ *ᵥ φ c) = γ *ᵥ φ c` using `by rw [e, mulVec_mulVec, π1]`.

Use `⟨c, (π4 _).1 ?_, π5 _ ?_⟩` and prove the remaining obligations. Rewrite using `[hg', mulVec_smul, e2]`. Rewrite using `[hg', mulVec_smul, map_sub, mulVec_sub, mulVec_sub, e2, e, sub_self, smul_zero]`.
-/
theorem splitLat_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → 3 ≤ D.p + D.q → 1 ≤ D.p → 1 ≤ D.q → SplitLat D := by
  intro E _ _ _ H D h1 h3 hp hq
  obtain ⟨D₀, ep, eq, Lp, Lm, htop, ho, rp, rm, sp, sm⟩ := GlobalTheory.T.exists_splitLattice_datum_every_signature E H D.p D.q h1
  have := D.fin
  have := D₀.fin
  have hξ := GlobalTheory.OneSpace.cc_rt H
  have hξ0 := GlobalTheory.OneSpace.rt_ne H
  obtain ⟨G, φ₀, hM₀⟩ := GlobalTheory.exists_herm_coord_of_datum E H D₀ (H.rt : E) hξ hξ0 (D.p + D.q) (by rw [ep, eq])
  obtain ⟨φ, hM⟩ := GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt E H D₀ D _ (H.rt : E) G φ₀ ep.symm eq.symm hξ hM₀
  have hind := indefinite D hp hq G φ hM
  obtain ⟨-, hfg, -, hdual⟩ := rank_integral_selfDual E H D _ _ G φ hξ hM
  obtain ⟨inj₀, span₀, hG, hdet, hEF₀⟩ := hM₀
  obtain ⟨inj, span, -, -, hEF⟩ := hM
  have hc : IsCompl Lp Lm := by
    refine ⟨Submodule.disjoint_def.2 fun a ha hb => ?_, codisjoint_iff.2 htop⟩
    by_contra h0
    exact lt_asymm (sp a ha h0) (sm a hb h0)
  obtain ⟨π, π1, π2, π3, π4, π5⟩ := exists_projector D₀ G φ₀ inj₀ span₀ hG hEF₀ Lp Lm hc ho
  have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
    refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
    have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
    linear_combination (1 / 2 : E) * h2
  have hz := GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind
  have : Nontrivial Lp := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by omega)
  obtain ⟨⟨a, ha⟩, ha0⟩ := exists_ne (0 : Lp)
  have hxx : FD.herm G (φ₀ a) (φ₀ a) ≠ 0 := by
    intro h
    have h5 := sp a ha fun h => ha0 (Subtype.ext h)
    have h6 := hEF₀ (H.rt • a) a
    rw [map_smul φ₀, show H.rt • φ₀ a = (H.rt : E) • φ₀ a from rfl, herm_smul_left, h, mul_zero, mul_zero,
      map_zero] at h6
    have h7 : D₀.EF (H.rt • a) a = 0 := by exact_mod_cast h6
    rw [h7] at h5
    simp at h5
  obtain ⟨b₁, hb₁, m₁⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ span₀
  obtain ⟨b₂, hb₂, m₂⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ₀ φ span
  obtain ⟨k, f, hk, hf⟩ := GlobalTheory.T.exists_coprime_scaled_isometry_same_signature E H D D₀ ep eq (2 * b₁ * b₂) (by positivity)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    rw [mul_assoc] at hk
    omega
  have hkE : (k : E) ≠ 0 := by exact_mod_cast hk0
  have hkQ : (k : ℚ) ^ 2 ≠ 0 := by positivity
  obtain ⟨A, hA⟩ := exists_matrix φ (φ₀ ∘ₗ f) inj span
  have hA' : ∀ x, (k : E) • (((k : E)⁻¹ • A) *ᵥ φ x) = φ₀ (f x) := fun x => by
    rw [smul_mulVec, smul_smul, mul_inv_cancel₀ hkE, one_smul]
    exact hA x
  generalize (k : E)⁻¹ • A = γ₀ at hA'
  have hU₀ : ∀ x y, FD.herm G (γ₀ *ᵥ x) (γ₀ *ᵥ y) = FD.herm G x y := fun x y => by
    have := herm_ext G γ₀ γ₀ 1 1 span (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [one_mulVec, one_mulVec]
      refine herm_eq_of_trace G hξ0 fun s => ?_
      rw [show s • γ₀ *ᵥ φ x = (s : E) • γ₀ *ᵥ φ x from rfl, ← mulVec_smul,
        show (s : E) • φ x = s • φ x from rfl, ← map_smul]
      apply mul_left_cancel₀ hkQ
      rw [← trace_nsmul, hA', hA', ← hEF₀, ← hEF, hf]
      push_cast
      rfl) x y
    rwa [one_mulVec, one_mulVec] at this
  have hd₀ := isUnit_det hdet hU₀
  obtain ⟨γ, hU, hγ⟩ := GlobalTheory.T.exists_unitary_conj_split_lattice_of_local (maximalRealSubfield E) E (IsCMField.complexConj E) _ G
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hh hz (LinearMap.range φ) (LinearMap.range φ₀) hfg span
    π γ₀ (φ₀ a) (2 * b₁ * b₂) k π1 π2 ((π4 a).2 ha) hxx (by rintro _ ⟨y, rfl⟩; exact π3 y) (by positivity)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_right_comm, mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₁]
      exact nsmul_mem (m₁ x) _)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₂]
      exact nsmul_mem (m₂ x) _)
    hU₀ hk
    (by
      rintro _ ⟨x, rfl⟩
      rw [← Nat.cast_smul_eq_nsmul E, hA']
      exact ⟨_, rfl⟩)
    (by
      rintro _ ⟨y, rfl⟩
      refine (hdual _).1 fun x => ⟨D₀.EF y (f x), ?_⟩
      rw [hEF₀, ← hA', ← Nat.cast_smul_eq_nsmul E, herm_smul_left, herm_smul_right, ← hU₀ (γ₀⁻¹ *ᵥ φ₀ y),
        mulVec_mulVec, mul_nonsing_inv _ hd₀, one_mulVec, show FD.cc (k : E) = k by simp [FD.cc], mul_comm (k : E)])
  have hU' : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y := hU
  have hd := isUnit_det hdet hU'
  obtain ⟨N, g, hN, hg⟩ := exists_scaled_map ((Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ) φ₀ inj₀ span₀
  have hg' : ∀ x, φ₀ (g x) = (N : E) • γ *ᵥ φ x := hg
  have hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y := fun x y => by
    have := hEF₀ (g x) (g y)
    rw [hg', hg', trace_nsmul, hU', ← hEF] at this
    exact_mod_cast this
  refine split_of_scaled D D₀ ep eq Lp Lm ho rp rm sp sm N hN g ?_ hE fun x => ?_
  · refine (injective_iff_map_eq_zero g).2 fun x hx => D.unimod.1 ?_
    ext y
    have := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at this
    rw [map_zero, LinearMap.zero_apply]
    exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
  · obtain ⟨c, hc⟩ := hγ _ ⟨x, rfl⟩
    have e : γ *ᵥ φ c = π *ᵥ (γ *ᵥ φ x) := by
      rw [hc, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd,
        Matrix.one_mul]
    have e2 : π *ᵥ (γ *ᵥ φ c) = γ *ᵥ φ c := by rw [e, mulVec_mulVec, π1]
    refine ⟨c, (π4 _).1 ?_, π5 _ ?_⟩
    · rw [hg', mulVec_smul, e2]
    · rw [hg', mulVec_smul, map_sub, mulVec_sub, mulVec_sub, e2, e, sub_self, smul_zero]

end GlobalTheory.SplitGenus
