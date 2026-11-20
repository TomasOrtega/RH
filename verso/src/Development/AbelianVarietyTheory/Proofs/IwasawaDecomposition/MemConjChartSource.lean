import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ConjChart

namespace GlobalTheory.ConjExph

section Charts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ}

/- English proof (translation)
Use extensionality with `a`. Simplify using `[conjCoord, conjV_apply]`.
-/
theorem conjCoord_conjV (d : ℕ) (v : V d) : conjCoord d (conjV d v) = v := by
  ext a; simp [conjCoord, conjV_apply]

/- English proof (translation)
The claim follows from `conjCoord_conjV d v`.
-/
theorem conjV_conjV (d : ℕ) (v : V d) : conjV d (conjV d v) = v := conjCoord_conjV d v

/- English proof (translation)
Express the relevant statement in the definitionally equal form `conjPts p h (c.e.symm (conjCoord d (conjV d v))) = _`. Rewrite using `[conjCoord_conjV]`.
-/
theorem symm_conjChart (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) (v : V d) :
    (conjChart h c).e.symm (conjV d v) = conjPts p h (c.e.symm v) := by
  change conjPts p h (c.e.symm (conjCoord d (conjV d v))) = _
  rw [conjCoord_conjV]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `conjCoord d (c.e ((conjPts p h).symm (conjPts p h z))) = _`. Rewrite using `[Homeomorph.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem conjChart_apply (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) (z : CxPts p σ') :
    (conjChart h c).e (conjPts p h z) = conjV d (c.e z) := by
  change conjCoord d (c.e ((conjPts p h).symm (conjPts p h z))) = _
  rw [Homeomorph.symm_apply_apply]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = conjV d (conjCoord d _)`. Conclude with `(conjCoord_conjV d _).symm`.
-/
theorem apply_symm_conjPts (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) (w : CxPts p σ) :
    c.e ((conjPts p h).symm w) = conjV d ((conjChart h c).e w) := by
  change _ = conjV d (conjCoord d _)
  exact (conjCoord_conjV d _).symm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(conjPts p h).symm (conjPts p h z) ∈ c.e.source ↔ _`. Rewrite using `[Homeomorph.symm_apply_apply]`.
-/
theorem mem_conjChart_source (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) {z : CxPts p σ'} :
    conjPts p h z ∈ (conjChart h c).e.source ↔ z ∈ c.e.source := by
  change (conjPts p h).symm (conjPts p h z) ∈ c.e.source ↔ _
  rw [Homeomorph.symm_apply_apply]

/- English proof (translation)
Establish `hn` using `(GlobalTheory.ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hy hy')`. Establish `e : c'.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] id` using `eventually_of_mem hn fun v hv => by`. Simplify using `only [Function.comp_apply, id]`. Rewrite using `[he _ (c.e.map_target hv.1) hv.2, c.e.right_inv hv.1]`. Use function extensionality and compare the values at `b`.

Simplify using `only [AlgChart.dtrans, e.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply]`.
-/
theorem dtrans_eq_self {d : ℕ} (c c' : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (he : ∀ w ∈ c.e.source, w ∈ c'.e.source → c'.e w = c.e w) (ξ : Fin d → ℂ) :
    c.dtrans c' y ξ = ξ := by
  have hn := (GlobalTheory.ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hy hy')
  have e : c'.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] id := eventually_of_mem hn fun v hv => by
    simp only [Function.comp_apply, id]
    rw [he _ (c.e.map_target hv.1) hv.2, c.e.right_inv hv.1]
  funext b
  simp only [AlgChart.dtrans, e.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply]

/- English proof (translation)
Establish `h1` using `leviV_comp_conjV d (fun v => ψ ((conjChart h c).e.symm v)) (c.e z) ξ`. Simplify using `only [ddcForm, AlgChart.levi]`. Use `congr 1`. Rewrite using `[conjChart_apply]`. Use `Eq.trans (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ)) (Eq.trans (congrArg Complex.re h1) (Complex.conj_re _))` and prove the remaining obligations.

Use `Filter.Eventually.of_forall fun v => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, symm_conjChart]`.
-/
theorem ddcForm_comp_conjPts (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) (z : CxPts p σ') (ψ : CxPts p σ → ℝ) (ξ : Fin d → ℂ) :
    ddcForm (ψ ∘ conjPts p h) c z ξ = ddcForm ψ (conjChart h c) (conjPts p h z) (star ξ) := by
  have h1 := leviV_comp_conjV d (fun v => ψ ((conjChart h c).e.symm v)) (c.e z) ξ
  simp only [ddcForm, AlgChart.levi]
  congr 1
  rw [conjChart_apply]
  refine Eq.trans (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ))
    (Eq.trans (congrArg Complex.re h1) (Complex.conj_re _))
  refine Filter.Eventually.of_forall fun v => ?_
  simp only [Function.comp_apply, symm_conjChart]

end Charts

/- English proof (translation)
Use extensionality with `k l`. Establish `e1 : star (Pi.single k 1 + Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 + Pi.single l 1`. Apply the tactic sequence `ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]`. Establish `e2 : star (Pi.single k 1 - Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 - Pi.single l 1`. Apply the tactic sequence `ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]`.

Establish `e3 : star (Pi.single k 1 + Complex.I • Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 - Complex.I • Pi.single l 1`. Apply the tactic sequence `ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]`. Establish `e4 : star (Pi.single k 1 - Complex.I • Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 + Complex.I • Pi.single l 1`. Apply the tactic sequence `ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]`. Simplify using `only [polMat, Matrix.map_apply, e1, e2, e3, e4, map_div₀, map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem polMat_comp_star {d : ℕ} (q : (Fin d → ℂ) → ℝ) :
    polMat (fun ξ => q (star ξ)) = (polMat q).map (starRingEnd ℂ) := by
  ext k l
  have e1 : star (Pi.single k 1 + Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 + Pi.single l 1 := by
    ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]
  have e2 : star (Pi.single k 1 - Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 - Pi.single l 1 := by
    ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]
  have e3 : star (Pi.single k 1 + Complex.I • Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 - Complex.I • Pi.single l 1 := by
    ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]
  have e4 : star (Pi.single k 1 - Complex.I • Pi.single l 1 : Fin d → ℂ) = Pi.single k 1 + Complex.I • Pi.single l 1 := by
    ext i; simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Pi.single_apply]; split_ifs <;> simp [sub_eq_add_neg]
  simp only [polMat, Matrix.map_apply, e1, e2, e3, e4, map_div₀, map_sub, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  ring

end GlobalTheory.ConjExph

namespace GlobalTheory.ConjExph

/- English proof (translation)
Use extensionality with `i`. Simplify using `[conjV_apply]`.
-/
theorem conjV_I_smul' {d : ℕ} (v : V d) : conjV d (Complex.I • v) = -(Complex.I • conjV d v) := by
  ext i; simp [conjV_apply]

/- English proof (translation)
Set `C` to `(conjV d).toContinuousLinearEquiv`. Set `CC : (V d × V d) ≃L[ℝ] (V d × V d)` to `C.prodCongr C`. Establish `hD : ∀ u : V d × V d, fderiv ℝ (fun x : V d × V d => conjV d (g (conjV d x.1, conjV d x.2))) q u = conjV d (fderiv ℝ g (conjV d q.1, conjV d q.2) (conjV d u.1, conjV d u.2))`. Introduce `u`. Express the relevant statement in the definitionally equal form `fderiv ℝ (C ∘ g ∘ CC) q u = _`.

Rewrite using `[C.comp_fderiv, ContinuousLinearMap.comp_apply, CC.comp_right_fderiv, ContinuousLinearMap.comp_apply]`. Both sides reduce to the same expression. Establish `hI : ((conjV d (Complex.I • w).1, conjV d (Complex.I • w).2) : V d × V d) = -(Complex.I • (conjV d w.1, conjV d w.2))`. Simplify using `[conjV_I_smul']`. Use extensionality with `i`.

Simplify using `only [del_apply, hD, hI, map_neg]`. Simplify using `[conjV_apply, map_ofNat]`. Apply the tactic sequence `try ring`.
-/
theorem del_conj_prod {d : ℕ} (g : V d × V d → V d) (q w : V d × V d) :
    del (fun x : V d × V d => conjV d (g (conjV d x.1, conjV d x.2))) q w =
      conjV d (del g (conjV d q.1, conjV d q.2) (conjV d w.1, conjV d w.2)) := by
  let C := (conjV d).toContinuousLinearEquiv
  let CC : (V d × V d) ≃L[ℝ] (V d × V d) := C.prodCongr C
  have hD : ∀ u : V d × V d, fderiv ℝ (fun x : V d × V d => conjV d (g (conjV d x.1, conjV d x.2))) q u =
      conjV d (fderiv ℝ g (conjV d q.1, conjV d q.2) (conjV d u.1, conjV d u.2)) := by
    intro u
    change fderiv ℝ (C ∘ g ∘ CC) q u = _
    rw [C.comp_fderiv, ContinuousLinearMap.comp_apply, CC.comp_right_fderiv, ContinuousLinearMap.comp_apply]
    rfl
  have hI : ((conjV d (Complex.I • w).1, conjV d (Complex.I • w).2) : V d × V d) =
      -(Complex.I • (conjV d w.1, conjV d w.2)) := by
    simp [conjV_I_smul']
  ext i
  simp only [del_apply, hD, hI, map_neg]
  simp [conjV_apply, map_ofNat]
  try ring

/- English proof (translation)
Set `C` to `(conjV d).toContinuousLinearEquiv`. Establish `hD : ∀ u, fderiv ℝ (fun v => starRingEnd ℂ (h (conjV d v))) z u = starRingEnd ℂ (fderiv ℝ h (conjV d z) (conjV d u))`. Introduce `u`. Express the relevant statement in the definitionally equal form `fderiv ℝ (Complex.conjCLE ∘ h ∘ C) z u = _`. Rewrite using `[Complex.conjCLE.comp_fderiv, ContinuousLinearMap.comp_apply, C.comp_right_fderiv, ContinuousLinearMap.comp_apply]`.

Both sides reduce to the same expression. Simplify using `only [del_apply, hD, conjV_I_smul', map_neg]`. Simplify using `[map_ofNat]`. Apply the tactic sequence `try ring`.
-/
theorem del_conj_scalar {d : ℕ} (h : V d → ℂ) (z ξ : V d) :
    del (fun v => starRingEnd ℂ (h (conjV d v))) z ξ = starRingEnd ℂ (del h (conjV d z) (conjV d ξ)) := by
  let C := (conjV d).toContinuousLinearEquiv
  have hD : ∀ u, fderiv ℝ (fun v => starRingEnd ℂ (h (conjV d v))) z u =
      starRingEnd ℂ (fderiv ℝ h (conjV d z) (conjV d u)) := by
    intro u
    change fderiv ℝ (Complex.conjCLE ∘ h ∘ C) z u = _
    rw [Complex.conjCLE.comp_fderiv, ContinuousLinearMap.comp_apply, C.comp_right_fderiv,
      ContinuousLinearMap.comp_apply]
    rfl
  simp only [del_apply, hD, conjV_I_smul', map_neg]
  simp [map_ofNat]
  try ring

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Matrix.inv_def]`. Establish `h1` using `RingHom.map_adjugate (starRingEnd ℂ) M`. Establish `h2` using `RingHom.map_det (starRingEnd ℂ) M`. Simplify using `only [RingHom.mapMatrix_apply] at h1 h2`. Rewrite using `[← h1, ← h2, Ring.inverse_eq_inv']`.

Use extensionality with `i j`. Simplify using `[map_inv₀]`.
-/
theorem inv_map_conj {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    (M.map (starRingEnd ℂ))⁻¹ = M⁻¹.map (starRingEnd ℂ) := by
  rw [Matrix.inv_def, Matrix.inv_def]
  have h1 := RingHom.map_adjugate (starRingEnd ℂ) M
  have h2 := RingHom.map_det (starRingEnd ℂ) M
  simp only [RingHom.mapMatrix_apply] at h1 h2
  rw [← h1, ← h2, Ring.inverse_eq_inv']
  ext i j
  simp [map_inv₀]

/- English proof (translation)
Establish `hdel : ∀ k l, del (fun v => b' v k l) z ξ = starRingEnd ℂ (del (fun v => b v k l) (conjV d z) (conjV d ξ))`. Introduce `k l`. Rewrite using `[del_congr (f := fun v => b' v k l) (g := fun v => starRingEnd ℂ (b (conjV d v) k l)) (eventually_of_mem (hO.mem_nhds hz) fun v hv => by show b' v k l = _; rw [hb v hv]; rfl)]`. Conclude with `del_conj_scalar (fun v => b v k l) z ξ`. Establish `hv : ∀ (x : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ), (starRingEnd ℂ ∘ x) ᵥ* A.map (starRingEnd ℂ) = starRingEnd ℂ ∘ (x ᵥ* A)` using `fun x A => funext fun j => (RingHom.map_vecMul _ A x j).symm`.

Establish `hx : ξ.ofLp = starRingEnd ℂ ∘ (conjV d ξ).ofLp`. Use function extensionality and compare the values at `i`. Simplify using `[conjV_apply]`. Establish `hD : (Matrix.of fun k l => del (fun v => b' v k l) z ξ) = (Matrix.of fun k l => del (fun v => b v k l) (conjV d z) (conjV d ξ)).map (starRingEnd ℂ)`. Use extensionality with `k l`.

Simplify using `[hdel]`. Rewrite using `[christoffel, christoffel, hD, hb z hz, inv_map_conj, hx, hv, hv]`. Use extensionality with `j`. Simplify using `[conjV_apply]`.
-/
theorem chris_conj {d : ℕ} (b b' : V d → Matrix (Fin d) (Fin d) ℂ) (O : Set (V d)) (hO : IsOpen O)
    (hb : ∀ v ∈ O, b' v = (b (conjV d v)).map (starRingEnd ℂ)) {z : V d} (hz : z ∈ O) (ξ : V d) :
    christoffel b' z ξ = conjV d (christoffel b (conjV d z) (conjV d ξ)) := by
  have hdel : ∀ k l, del (fun v => b' v k l) z ξ =
      starRingEnd ℂ (del (fun v => b v k l) (conjV d z) (conjV d ξ)) := by
    intro k l
    rw [del_congr (f := fun v => b' v k l) (g := fun v => starRingEnd ℂ (b (conjV d v) k l))
      (eventually_of_mem (hO.mem_nhds hz) fun v hv => by show b' v k l = _; rw [hb v hv]; rfl)]
    exact del_conj_scalar (fun v => b v k l) z ξ
  have hv : ∀ (x : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ),
      (starRingEnd ℂ ∘ x) ᵥ* A.map (starRingEnd ℂ) = starRingEnd ℂ ∘ (x ᵥ* A) :=
    fun x A => funext fun j => (RingHom.map_vecMul _ A x j).symm
  have hx : ξ.ofLp = starRingEnd ℂ ∘ (conjV d ξ).ofLp := by
    funext i; simp [conjV_apply]
  have hD : (Matrix.of fun k l => del (fun v => b' v k l) z ξ) =
      (Matrix.of fun k l => del (fun v => b v k l) (conjV d z) (conjV d ξ)).map (starRingEnd ℂ) := by
    ext k l; simp [hdel]
  rw [christoffel, christoffel, hD, hb z hz, inv_map_conj, hx, hv, hv]
  ext j; simp [conjV_apply]

/- English proof (translation)
It suffices to establish `H : ∀ n (q : V d × V d), q.1 ∈ O → jet b' n q = conjV d (jet b n (conjV d q.1, conjV d q.2)) from H n (z, ξ) hz`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro q _`. Simplify using `only [jet_zero, conjV_conjV]`.

Consider the case `succ n ih`. Introduce `q hq`. Establish `hev : jet b' n =ᶠ[𝓝 q] fun x : V d × V d => conjV d (jet b n (conjV d x.1, conjV d x.2))` using `eventually_of_mem ((hO.preimage continuous_fst).mem_nhds hq) fun x hx => ih x hx`. Rewrite using `[jet_succ, del_congr hev, del_conj_prod, jet_succ, chris_conj b b' O hO hb hq]`. Simplify using `only [map_neg, conjV_conjV]`.
-/
theorem jet_conj (d : ℕ) (b b' : V d → Matrix (Fin d) (Fin d) ℂ) (O : Set (V d)) (hO : IsOpen O)
    (hb : ∀ v ∈ O, b' v = (b (conjV d v)).map (starRingEnd ℂ)) (n : ℕ) (z : V d) (hz : z ∈ O) (ξ : V d) :
    jet b' n (z, ξ) = conjV d (jet b n (conjV d z, conjV d ξ)) := by
  suffices H : ∀ n (q : V d × V d), q.1 ∈ O → jet b' n q = conjV d (jet b n (conjV d q.1, conjV d q.2)) from
    H n (z, ξ) hz
  intro n
  induction n with
  | zero => intro q _; simp only [jet_zero, conjV_conjV]
  | succ n ih =>
    intro q hq
    have hev : jet b' n =ᶠ[𝓝 q] fun x : V d × V d => conjV d (jet b n (conjV d x.1, conjV d x.2)) :=
      eventually_of_mem ((hO.preimage continuous_fst).mem_nhds hq) fun x hx => ih x hx
    rw [jet_succ, del_congr hev, del_conj_prod, jet_succ, chris_conj b b' O hO hb hq]
    simp only [map_neg, conjV_conjV]

end GlobalTheory.ConjExph

namespace GlobalTheory.ConjExph

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ}

/- English proof (translation)
Use function extensionality and compare the values at `v`. Express the relevant statement in the definitionally equal form `conjCoord d (c'.e ((conjPts p h).symm (conjPts p h (c.e.symm (conjCoord d v))))) = _`. Rewrite using `[Homeomorph.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem conjChart_trans_eq (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c c' : AlgChart p σ' d) :
    (conjChart h c').e ∘ (conjChart h c).e.symm = conjV d ∘ (c'.e ∘ c.e.symm) ∘ conjV d := by
  funext v
  change conjCoord d (c'.e ((conjPts p h).symm (conjPts p h (c.e.symm (conjCoord d v))))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/- English proof (translation)
Use `set f := c'.e ∘ c.e.symm with hfdef`. Establish `hf : DifferentiableAt ℂ f (c.e z)` using `(c.holo_trans c').differentiableAt ((GlobalTheory.ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hz hz'))`. Use `set C := (conjV d).toContinuousLinearEquiv with hC`. Establish `hg : DifferentiableAt ℂ (conjV d ∘ f ∘ conjV d) (conjV d (c.e z))`. Use `(differentiableAt_piLp 2).2 fun b => ?_` and prove the remaining obligations.

Establish `hF : DifferentiableAt ℂ (fun w => f w b) (conjCoord d (conjV d (c.e z)))`. Rewrite using `[conjCoord_conjV]`. Conclude with `((differentiableAt_piLp 2).1 hf) b`. Conclude with `differentiableAt_conj_comp hF`. Establish `hR : ∀ w, fderiv ℝ (conjV d ∘ f ∘ conjV d) (conjV d (c.e z)) w = conjV d (fderiv ℝ f (c.e z) (conjV d w))`.

Introduce `w`. Express the relevant statement in the definitionally equal form `fderiv ℝ (C ∘ f ∘ C) (C (c.e z)) w = C (fderiv ℝ f (c.e z) (C w))`. Rewrite using `[C.comp_fderiv, ContinuousLinearMap.comp_apply, C.comp_right_fderiv, ContinuousLinearMap.comp_apply, show C (C (c.e z)) = c.e z from conjV_conjV d _]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `b`.

Use `show fderiv ℂ ((conjChart h c').e ∘ (conjChart h c).e.symm) ((conjChart h c).e (conjPts p h z)) (WithLp.toLp 2 (star ξ)) b = starRingEnd ℂ (fderiv ℂ f (c.e z) (WithLp.toLp 2 ξ) b)`. Rewrite using `[conjChart_trans_eq, conjChart_apply]`. Rewrite using `[← ContinuousLinearMap.coe_restrictScalars' (R := ℝ), ← hg.fderiv_restrictScalars ℝ, hR, ← ContinuousLinearMap.coe_restrictScalars' (R := ℝ) (fderiv ℂ f (c.e z)), ← hf.fderiv_restrictScalars ℝ]`. Establish `e : conjV d (WithLp.toLp 2 (star ξ)) = WithLp.toLp 2 ξ`. Use extensionality with `i`.

Simplify using `[conjV_apply]`. Rewrite using `[e, conjV_apply]`.
-/
theorem dtrans_conjChart (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c c' : AlgChart p σ' d) {z : CxPts p σ'}
    (hz : z ∈ c.e.source) (hz' : z ∈ c'.e.source) (ξ : Fin d → ℂ) :
    (conjChart h c).dtrans (conjChart h c') (conjPts p h z) (star ξ) = star (c.dtrans c' z ξ) := by
  set f := c'.e ∘ c.e.symm with hfdef
  have hf : DifferentiableAt ℂ f (c.e z) := (c.holo_trans c').differentiableAt
    ((GlobalTheory.ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hz hz'))
  set C := (conjV d).toContinuousLinearEquiv with hC
  have hg : DifferentiableAt ℂ (conjV d ∘ f ∘ conjV d) (conjV d (c.e z)) := by
    refine (differentiableAt_piLp 2).2 fun b => ?_
    have hF : DifferentiableAt ℂ (fun w => f w b) (conjCoord d (conjV d (c.e z))) := by
      rw [conjCoord_conjV]
      exact ((differentiableAt_piLp 2).1 hf) b
    exact differentiableAt_conj_comp hF
  have hR : ∀ w, fderiv ℝ (conjV d ∘ f ∘ conjV d) (conjV d (c.e z)) w = conjV d (fderiv ℝ f (c.e z) (conjV d w)) := by
    intro w
    change fderiv ℝ (C ∘ f ∘ C) (C (c.e z)) w = C (fderiv ℝ f (c.e z) (C w))
    rw [C.comp_fderiv, ContinuousLinearMap.comp_apply, C.comp_right_fderiv, ContinuousLinearMap.comp_apply,
      show C (C (c.e z)) = c.e z from conjV_conjV d _]
    rfl
  funext b
  show fderiv ℂ ((conjChart h c').e ∘ (conjChart h c).e.symm) ((conjChart h c).e (conjPts p h z))
    (WithLp.toLp 2 (star ξ)) b = starRingEnd ℂ (fderiv ℂ f (c.e z) (WithLp.toLp 2 ξ) b)
  rw [conjChart_trans_eq, conjChart_apply]
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ), ← hg.fderiv_restrictScalars ℝ, hR,
    ← ContinuousLinearMap.coe_restrictScalars' (R := ℝ) (fderiv ℂ f (c.e z)), ← hf.fderiv_restrictScalars ℝ]
  have e : conjV d (WithLp.toLp 2 (star ξ)) = WithLp.toLp 2 ξ := by
    ext i; simp [conjV_apply]
  rw [e, conjV_apply]

end GlobalTheory.ConjExph

namespace GlobalTheory.ConjExph

/- English proof (translation)
Use `show iteratedDeriv n ((conjV d).toContinuousLinearEquiv ∘ g) x = _`. Simplify using `only [iteratedDeriv_eq_iteratedFDeriv, ContinuousLinearEquiv.iteratedFDeriv_comp_left]`. Both sides reduce to the same expression.
-/
theorem iteratedDeriv_conjV {d : ℕ} (g : ℝ → V d) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (conjV d ∘ g) x = conjV d (iteratedDeriv n g x) := by
  show iteratedDeriv n ((conjV d).toContinuousLinearEquiv ∘ g) x = _
  simp only [iteratedDeriv_eq_iteratedFDeriv, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
  rfl

/- English proof (translation)
Introduce `F _ _ Y σ σ' ι a a' E hι ha _ hpot hE`. Break down `isEmpty_or_nonempty (Pts Y σ') with hN | ⟨⟨z0⟩⟩` into its components or cases. Use `⟨fun _ z _ => z, ⟨fun _ _ y => (hN.false y).elim, fun c q _ => (hN.false (c.e.symm q.1)).elim, fun c _ q _ => (hN.false (c.e.symm q.1)).elim, fun _ y => (hN.false y).elim, fun _ y => (hN.false y).elim⟩, fun _ _ _ z => (hN.false z).elim, fun ι' _ _ _ _ z _ => (hN.false (ι' z)).eli …` and prove the remaining obligations. Establish `hσ : σ = (starRingEnd ℂ).comp σ'`. Establish `h1` using `(ι z0).2`.

Rewrite `h1` using `[hι z0, Category.assoc, z0.2, spMap, spMap, spMap, ← Spec.map_comp]`. Conclude with `(congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm`. Take `rfl : ι = conjPts Y.str hσ` from `funext fun z => Subtype.ext (hι z)`. Establish `hK : ∀ (c : AlgChart Y.str σ' Y.dim) (y : Pts Y σ'), y ∈ c.e.source → ∀ ξ, a' c y ξ = a (conjChart hσ c) ((conjPts Y.str hσ) y) (star ξ)`. Introduce `c y hy ξ`.

Take `⟨W, φ, hW, hp⟩` from `ha.1 ((conjPts Y.str hσ) y)`. Rewrite using `[(hpot W φ hp).2.2 c y hy hW ξ, hp.2.2 _ _ ((mem_conjChart_source hσ c).2 hy) hW, ddcForm_comp_conjPts]`. Use `⟨fun c z ξ => (conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) z) (star ξ)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `c1 c2 y hy1 hy2 ξ beta_reduce`. Rewrite using `[hE.trans (conjChart hσ c1) (conjChart hσ c2) ((conjPts Y.str hσ) y) ((mem_conjChart_source hσ c1).2 hy1) ((mem_conjChart_source hσ c2).2 hy2), dtrans_conjChart hσ c1 c2 hy1 hy2]`.

Introduce `c`. Establish `hM : Continuous fun q : V Y.dim × V Y.dim => (conjV Y.dim q.1, conjV Y.dim q.2)` using `((conjV Y.dim).continuous.comp continuous_fst).prodMk ((conjV Y.dim).continuous.comp continuous_snd)`. Use `((conjPts Y.str hσ).symm.continuous.comp_continuousOn ((hE.cont (conjChart hσ c)).comp hM.continuousOn fun q hq => ⟨?_, Set.mem_univ _⟩)).congr fun q _ => ?_` and prove the remaining obligations. Use `show conjCoord Y.dim (conjV Y.dim q.1) ∈ c.e.target`. Rewrite using `[conjCoord_conjV]`.

Conclude with `hq.1`. Simplify using `only [Function.comp_apply, symm_conjChart]`. Both sides reduce to the same expression. Introduce `c1 c2`. Establish `hM : ContDiff ℝ ∞ fun q : V Y.dim × V Y.dim => (conjV Y.dim q.1, conjV Y.dim q.2)` using `((conjV Y.dim).contDiff.comp contDiff_fst).prodMk ((conjV Y.dim).contDiff.comp contDiff_snd)`.

Use `((conjV Y.dim).contDiff.comp_contDiffOn ((hE.smooth (conjChart hσ c1) (conjChart hσ c2)).comp hM.contDiffOn fun q hq => ⟨?_, ?_⟩)).congr fun q _ => ?_` and prove the remaining obligations. Use `show conjCoord Y.dim (conjV Y.dim q.1) ∈ c1.e.target`. Rewrite using `[conjCoord_conjV]`. Conclude with `hq.1`. Use `show E (conjChart hσ c1) ((conjChart hσ c1).e.symm (conjV Y.dim q.1)) (conjV Y.dim q.2).ofLp ∈ (conjChart hσ c2).e.source`.

Rewrite using `[symm_conjChart]`. Conclude with `hq.2`. Simplify using `only [Function.comp_apply, symm_conjChart, apply_symm_conjPts]`. Both sides reduce to the same expression. Introduce `c y hy beta_reduce`.

Rewrite using `[star_zero, hE.zero _ _ ((mem_conjChart_source hσ c).2 hy), Homeomorph.symm_apply_apply]`. Introduce `c y hy ξ n`. Establish `hy'` using `(mem_conjChart_source hσ c).2 hy`. Establish `hb : ∀ v ∈ c.e.target, matIn a' c v = (matIn a (conjChart hσ c) (conjV Y.dim v)).map (starRingEnd ℂ)`. Introduce `v hv`.

Rewrite using `[matIn, matIn, symm_conjChart, ← polMat_comp_star]`. Use `congr 1`. Use function extensionality and compare the values at `ξ'`. Conclude with `hK c _ (c.e.map_target hv) ξ'`. Establish `e1 : (fun t : ℝ => c.e ((conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) y) (star (t • ξ.ofLp))))) = conjV Y.dim ∘ fun t : ℝ => (conjChart hσ c).e (E (conjChart hσ c) ((conjPts Y.str hσ) y) (t • (conjV Y.dim ξ).ofLp))`.

Use function extensionality and compare the values at `t`. Establish `hs : star (t • ξ.ofLp) = t • (conjV Y.dim ξ).ofLp`. Use extensionality with `i`. Simplify using `[conjV_apply]`. Simplify using `only [Function.comp_apply, hs, apply_symm_conjPts]`.

Use `show iteratedDeriv n (fun t : ℝ => c.e ((conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) y) (star (t • ξ.ofLp))))) 0 = _`. Rewrite using `[e1, iteratedDeriv_conjV, hE.jets _ _ hy' (conjV Y.dim ξ) n, conjChart_apply]`. Conclude with `(jet_conj Y.dim _ _ c.e.target c.e.open_target hb n (c.e y) (c.e.map_source hy) ξ).symm`. Introduce `c c' hcc z hz hJz ξ`. Establish `hz'` using `(mem_conjChart_source hσ c').2 hz`.

Use `show (conjPts Y.str hσ) ((conjPts Y.str hσ).symm _) = _`. Rewrite using `[Homeomorph.apply_symm_apply, hE.trans (conjChart hσ c') c ((conjPts Y.str hσ) z) hz' hJz, dtrans_eq_self _ _ hz' hJz ?_]`. Introduce `w hw hwc`. Take `⟨w0, rfl⟩` from `(conjPts Y.str hσ).surjective w`. Use extensionality with `i`.

Rewrite using `[conjChart_apply, conjV_apply, hcc w0 ((mem_conjChart_source hσ c').1 hw) hwc i, Complex.conj_conj]`. Introduce `ι' hι' c c' hcc z hz hz' ξ`. Take `rfl : ι' = (conjPts Y.str hσ).symm` from `funext fun w => Subtype.ext (hι' w)`. Use `show (conjPts Y.str hσ).symm (E c' z ξ) = (conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) ((conjPts Y.str hσ).symm z)) (star (star ξ)))`. Rewrite using `[Homeomorph.apply_symm_apply, star_star, hE.trans c' (conjChart hσ c) z hz hz', dtrans_eq_self _ _ hz hz' ?_]`.

Introduce `w hw hwc`. Use extensionality with `i`. Rewrite using `[hcc w hw hwc i]`. Both sides reduce to the same expression.
-/
theorem exists_conj_exph : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ σ' : F →+* ℂ) (ι : Pts Y σ' → Pts Y σ) (a : ChartForm Y.str σ Y.dim) (a' : ChartForm Y.str σ' Y.dim) (E : ChartMap Y.str σ Y.dim), IsConjMap ι → IsKaehlerForm (Y.an σ) a → IsKaehlerForm (Y.an σ') a' → (∀ W φ, IsPotential (Y.an σ) a W φ → IsPotential (Y.an σ') a' (ι ⁻¹' W) (φ ∘ ι)) → IsExph a E → ∃ E' : ChartMap Y.str σ' Y.dim, IsExph a' E' ∧ ConjComm ι E E' ∧ ∀ ι' : Pts Y σ → Pts Y σ', IsConjMap ι' → ConjComm ι' E' E := by
  intro F _ _ Y σ σ' ι a a' E hι ha _ hpot hE
  rcases isEmpty_or_nonempty (Pts Y σ') with hN | ⟨⟨z0⟩⟩
  · refine ⟨fun _ z _ => z, ⟨fun _ _ y => (hN.false y).elim, fun c q _ => (hN.false (c.e.symm q.1)).elim,
      fun c _ q _ => (hN.false (c.e.symm q.1)).elim, fun _ y => (hN.false y).elim, fun _ y => (hN.false y).elim⟩,
      fun _ _ _ z => (hN.false z).elim, fun ι' _ _ _ _ z _ => (hN.false (ι' z)).elim⟩
  have hσ : σ = (starRingEnd ℂ).comp σ' := by
    have h1 := (ι z0).2
    rw [hι z0, Category.assoc, z0.2, spMap, spMap, spMap, ← Spec.map_comp] at h1
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm
  obtain rfl : ι = conjPts Y.str hσ := funext fun z => Subtype.ext (hι z)
  have hK : ∀ (c : AlgChart Y.str σ' Y.dim) (y : Pts Y σ'), y ∈ c.e.source → ∀ ξ,
      a' c y ξ = a (conjChart hσ c) ((conjPts Y.str hσ) y) (star ξ) := by
    intro c y hy ξ
    obtain ⟨W, φ, hW, hp⟩ := ha.1 ((conjPts Y.str hσ) y)
    rw [(hpot W φ hp).2.2 c y hy hW ξ, hp.2.2 _ _ ((mem_conjChart_source hσ c).2 hy) hW, ddcForm_comp_conjPts]
  refine ⟨fun c z ξ => (conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) z) (star ξ)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro c1 c2 y hy1 hy2 ξ
    beta_reduce
    rw [hE.trans (conjChart hσ c1) (conjChart hσ c2) ((conjPts Y.str hσ) y) ((mem_conjChart_source hσ c1).2 hy1)
      ((mem_conjChart_source hσ c2).2 hy2), dtrans_conjChart hσ c1 c2 hy1 hy2]
  · intro c
    have hM : Continuous fun q : V Y.dim × V Y.dim => (conjV Y.dim q.1, conjV Y.dim q.2) :=
      ((conjV Y.dim).continuous.comp continuous_fst).prodMk ((conjV Y.dim).continuous.comp continuous_snd)
    refine ((conjPts Y.str hσ).symm.continuous.comp_continuousOn ((hE.cont (conjChart hσ c)).comp hM.continuousOn
      fun q hq => ⟨?_, Set.mem_univ _⟩)).congr fun q _ => ?_
    · show conjCoord Y.dim (conjV Y.dim q.1) ∈ c.e.target
      rw [conjCoord_conjV]; exact hq.1
    · simp only [Function.comp_apply, symm_conjChart]
      rfl
  · intro c1 c2
    have hM : ContDiff ℝ ∞ fun q : V Y.dim × V Y.dim => (conjV Y.dim q.1, conjV Y.dim q.2) :=
      ((conjV Y.dim).contDiff.comp contDiff_fst).prodMk ((conjV Y.dim).contDiff.comp contDiff_snd)
    refine ((conjV Y.dim).contDiff.comp_contDiffOn ((hE.smooth (conjChart hσ c1) (conjChart hσ c2)).comp
      hM.contDiffOn fun q hq => ⟨?_, ?_⟩)).congr fun q _ => ?_
    · show conjCoord Y.dim (conjV Y.dim q.1) ∈ c1.e.target
      rw [conjCoord_conjV]; exact hq.1
    · show E (conjChart hσ c1) ((conjChart hσ c1).e.symm (conjV Y.dim q.1)) (conjV Y.dim q.2).ofLp ∈ (conjChart hσ c2).e.source
      rw [symm_conjChart]; exact hq.2
    · simp only [Function.comp_apply, symm_conjChart, apply_symm_conjPts]
      rfl
  · intro c y hy
    beta_reduce
    rw [star_zero, hE.zero _ _ ((mem_conjChart_source hσ c).2 hy), Homeomorph.symm_apply_apply]
  · intro c y hy ξ n
    have hy' := (mem_conjChart_source hσ c).2 hy
    have hb : ∀ v ∈ c.e.target, matIn a' c v = (matIn a (conjChart hσ c) (conjV Y.dim v)).map (starRingEnd ℂ) := by
      intro v hv
      rw [matIn, matIn, symm_conjChart, ← polMat_comp_star]
      congr 1
      funext ξ'
      exact hK c _ (c.e.map_target hv) ξ'
    have e1 : (fun t : ℝ => c.e ((conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) y) (star (t • ξ.ofLp))))) =
        conjV Y.dim ∘ fun t : ℝ => (conjChart hσ c).e (E (conjChart hσ c) ((conjPts Y.str hσ) y) (t • (conjV Y.dim ξ).ofLp)) := by
      funext t
      have hs : star (t • ξ.ofLp) = t • (conjV Y.dim ξ).ofLp := by
        ext i; simp [conjV_apply]
      simp only [Function.comp_apply, hs, apply_symm_conjPts]
    show iteratedDeriv n (fun t : ℝ => c.e ((conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) y) (star (t • ξ.ofLp))))) 0 = _
    rw [e1, iteratedDeriv_conjV, hE.jets _ _ hy' (conjV Y.dim ξ) n, conjChart_apply]
    exact (jet_conj Y.dim _ _ c.e.target c.e.open_target hb n (c.e y) (c.e.map_source hy) ξ).symm
  · intro c c' hcc z hz hJz ξ
    have hz' := (mem_conjChart_source hσ c').2 hz
    show (conjPts Y.str hσ) ((conjPts Y.str hσ).symm _) = _
    rw [Homeomorph.apply_symm_apply, hE.trans (conjChart hσ c') c ((conjPts Y.str hσ) z) hz' hJz, dtrans_eq_self _ _ hz' hJz ?_]
    intro w hw hwc
    obtain ⟨w0, rfl⟩ := (conjPts Y.str hσ).surjective w
    ext i
    rw [conjChart_apply, conjV_apply, hcc w0 ((mem_conjChart_source hσ c').1 hw) hwc i, Complex.conj_conj]
  · intro ι' hι' c c' hcc z hz hz' ξ
    obtain rfl : ι' = (conjPts Y.str hσ).symm := funext fun w => Subtype.ext (hι' w)
    show (conjPts Y.str hσ).symm (E c' z ξ) = (conjPts Y.str hσ).symm (E (conjChart hσ c) ((conjPts Y.str hσ) ((conjPts Y.str hσ).symm z)) (star (star ξ)))
    rw [Homeomorph.apply_symm_apply, star_star, hE.trans c' (conjChart hσ c) z hz hz', dtrans_eq_self _ _ hz hz' ?_]
    intro w hw hwc
    ext i
    rw [hcc w hw hwc i]
    rfl

end GlobalTheory.ConjExph
