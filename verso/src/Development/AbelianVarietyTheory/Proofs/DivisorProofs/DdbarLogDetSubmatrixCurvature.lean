import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

noncomputable section

namespace GlobalTheory.GradedLine

/- English proof (translation)
Establish `hM1 : (H p).submatrix f f = 1` using `by rw [h1]; exact submatrix_one f hf`. Establish `hu : IsUnit ((H p).submatrix f f).det` using `by rw [hM1, det_one]; exact isUnit_one`. Establish `hc : ∀ ζ, conn H p ζ = (mdel H p ζ)ᵀ`. Introduce `ζ`. Rewrite using `[conn, h1, transpose_one, inv_one, Matrix.one_mul]`.

Establish `hb : ∀ a b, mdbar H p η a b = starRingEnd ℂ (mdel H p η b a)`. Introduce `a b`. Rewrite using `[← conjTranspose_mdel hh]`. Both sides reduce to the same expression. Rewrite using `[curv_eq (h2.submatrix f f) hu, hM1]`.

Simplify using `only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, trace, diag, Matrix.sub_apply, Matrix.mul_apply, transpose_apply, Finset.sum_sub_distrib, hc]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mdbar H p η (f c) (f a) * mdel H p ξ (f a) (f c) = _`. Rewrite using `[hb, mul_comm]`.
-/
theorem trace_curv_submatrix_of_eq_one {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {κ : Type} [Fintype κ] [DecidableEq κ]
    (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (f : κ → Fin N) (hf : Function.Injective f)
    (h2 : MContDiffAt 2 H p) (hh : ∀ᶠ v in 𝓝 p, (H v).IsHermitian) (h1 : H p = 1) (ξ η : E) :
    (curv (fun v => (H v).submatrix f f) p ξ η).trace =
      ∑ a, ∑ c, conn H p ξ (f c) (f a) * starRingEnd ℂ (conn H p η (f c) (f a))
        - ∑ a, mddbar H p ξ η (f a) (f a) := by
  have hM1 : (H p).submatrix f f = 1 := by rw [h1]; exact submatrix_one f hf
  have hu : IsUnit ((H p).submatrix f f).det := by rw [hM1, det_one]; exact isUnit_one
  have hc : ∀ ζ, conn H p ζ = (mdel H p ζ)ᵀ := by
    intro ζ; rw [conn, h1, transpose_one, inv_one, Matrix.one_mul]
  have hb : ∀ a b, mdbar H p η a b = starRingEnd ℂ (mdel H p η b a) := by
    intro a b; rw [← conjTranspose_mdel hh]; rfl
  rw [curv_eq (h2.submatrix f f) hu, hM1]
  simp only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, trace, diag, Matrix.sub_apply,
    Matrix.mul_apply, transpose_apply, Finset.sum_sub_distrib, hc]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  change mdbar H p η (f c) (f a) * mdel H p ξ (f a) (f c) = _
  rw [hb, mul_comm]

/- English proof (translation)
Introduce `N E _ _ _ _ H p i h2 hpd h1 ξ η`. Establish `hh : ∀ᶠ v in 𝓝 p, (H v).IsHermitian` using `hpd.mono fun v hv => hv.isHermitian`. Establish `hinj : Function.Injective (emb i)`. Introduce `x y hxy`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y`.

Simplify using `only [emb, Sum.elim_inl] at hxy`. Conclude with `congrArg Sum.inl (Fin.castLE_injective _ hxy)`. Simplify using `only [emb, Sum.elim_inl, Sum.elim_inr] at hxy`. Use `congrArg Fin.val hxy` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [emb, Sum.elim_inl, Sum.elim_inr] at hxy`. Use `congrArg Fin.val hxy` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Conclude with `congrArg Sum.inr (Subsingleton.elim _ _)`. Use `set S : E → Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ := fun v => (H v).submatrix (emb i) (emb i) with hSdef`. Establish `hS1 : S p = 1` using `by simp only [S, h1]; exact submatrix_one _ hinj`. Establish `hS2 : MContDiffAt 2 S p` using `h2.submatrix _ _`. Establish `hSu : IsUnit (S p).det` using `by rw [hS1, det_one]; exact isUnit_one`.

Establish `hsu : IsUnit (subGram (S p)).det`. Establish `h11 : subGram (1 : Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ) = 1`. Use extensionality with `a b`. Simplify using `[subGram, toBlocks₁₁, one_apply]`. Rewrite using `[hS1, h11, det_one]`.

Conclude with `isUnit_one`. Establish `hSh : ∀ᶠ v in 𝓝 p, (S v).IsHermitian` using `hh.mono fun v hv => hv.submatrix _`. Establish `hQh : ∀ᶠ v in 𝓝 p, (quotGram (S v)).IsHermitian` using `hSh.mono fun v hv => isHermitian_quotGram hv`. Establish `hQ2 : MContDiffAt 2 (fun v => quotGram (S v)) p` using `hS2.quotGram hsu`. Establish `hQu` using `isUnit_det_quotGram hSu hsu`.

Establish `e1 : ddbar (fun v => ((-Real.log (quotGram (S v)).det.re : ℝ) : ℂ)) p ξ η = (curv (fun v => quotGram (S v)) p ξ η).trace`. Rewrite using `[trace_curv hQ2 hQh hQu, ← ContinuousLinearMap.neg_apply, ← ContinuousLinearMap.neg_apply, ← leviForm_neg]`. Both sides reduce to the same expression. Establish `e2` using `trace_curv_eq_sub_add_quot hS2 hSu hsu ξ η`. Establish `hsub : (fun v => subGram (S v)) = fun v => (H v).submatrix (emb i ∘ Sum.inl) (emb i ∘ Sum.inl)`.

Use function extensionality and compare the values at `v`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite `e2` using `[hsub]`. Establish `tS` using `trace_curv_submatrix_of_eq_one H p (emb i) hinj h2 hh h1 ξ η`.

Establish `tT` using `trace_curv_submatrix_of_eq_one H p (emb i ∘ Sum.inl) (hinj.comp Sum.inl_injective) h2 hh h1 ξ η`. Establish `hc : ∀ ζ, conn H p ζ = (mdel H p ζ)ᵀ`. Introduce `ζ`. Rewrite using `[conn, h1, transpose_one, inv_one, Matrix.one_mul]`. Establish `hb : ∀ a b, mdbar H p η a b = starRingEnd ℂ (mdel H p η b a)`.

Introduce `a b`. Rewrite using `[← conjTranspose_mdel hh]`. Both sides reduce to the same expression. Establish `hcurv : curv H p ξ η i i = ∑ c, conn H p ξ c i * starRingEnd ℂ (conn H p η c i) - mddbar H p ξ η i i`. Rewrite using `[curv_eq h2 (by rw [h1, det_one]; exact isUnit_one), h1]`.

Simplify using `only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply, transpose_apply, hc]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hb, mul_comm]`. Establish `hI : ∀ g : Fin N → ℂ, ∑ a ∈ Finset.Iio i, g a = ∑ a : Fin i, g (Fin.castLE i.isLt.le a)`.

Introduce `g`. Establish `hIio : Finset.Iio i = Finset.univ.map (Fin.castLEEmb i.isLt.le)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Iio, Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.isLt`. Rewrite using `[hIio, Finset.sum_map]`.

Both sides reduce to the same expression. Establish `hU : ∀ g : Fin N → ℂ, ∑ c, g c = ∑ c ∈ Finset.Iio i, g c + g i + ∑ c ∈ Finset.Ioi i, g c`. Introduce `g`. Establish `hu : (Finset.univ : Finset (Fin N)) = (Finset.Iic i).disjUnion (Finset.Ioi i) (Finset.disjoint_left.2 fun x hx hx' => by`. Simplify using `only [Finset.mem_Iic, Finset.mem_Ioi] at hx hx'; exact absurd hx (not_le.2 hx')) := by`.

Use extensionality with `x`. Simplify using `only [Finset.mem_univ, Finset.disjUnion_eq_union, Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi, true_iff]`. Conclude with `le_or_gt x i`. Rewrite using `[hu, Finset.sum_disjUnion, Finset.Iic_eq_cons_Iio, Finset.sum_cons]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, ← sub_eq_of_eq_add' e2, tS, tT, hcurv, hU (fun c => conn H p ξ c i * starRingEnd ℂ (conn H p η c i)),`. Use the proof step `]`. Simplify using `only [hI, Fintype.sum_sum_type, Fin.sum_univ_one, Function.comp_apply, emb, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ddbar_neg_log_quotGram_emb : ∀ {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (i : Fin N), MContDiffAt 2 H p → (∀ᶠ v in 𝓝 p, (H v).PosDef) → H p = 1 → ∀ ξ η : E, ddbar (fun v => ((-Real.log (quotGram ((H v).submatrix (emb i) (emb i))).det.re : ℝ) : ℂ)) p ξ η = curv H p ξ η i i + ∑ a ∈ Finset.Iio i, conn H p ξ i a * starRingEnd ℂ (conn H p η i a) - ∑ c ∈ Finset.Ioi i, conn H p ξ c i * starRingEnd ℂ (conn H p η c i) := by
  intro N E _ _ _ _ H p i h2 hpd h1 ξ η
  have hh : ∀ᶠ v in 𝓝 p, (H v).IsHermitian := hpd.mono fun v hv => hv.isHermitian
  have hinj : Function.Injective (emb i) := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · simp only [emb, Sum.elim_inl] at hxy
      exact congrArg Sum.inl (Fin.castLE_injective _ hxy)
    · simp only [emb, Sum.elim_inl, Sum.elim_inr] at hxy
      have := congrArg Fin.val hxy; simp at this; omega
    · simp only [emb, Sum.elim_inl, Sum.elim_inr] at hxy
      have := congrArg Fin.val hxy; simp at this; omega
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  set S : E → Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ :=
    fun v => (H v).submatrix (emb i) (emb i) with hSdef
  have hS1 : S p = 1 := by simp only [S, h1]; exact submatrix_one _ hinj
  have hS2 : MContDiffAt 2 S p := h2.submatrix _ _
  have hSu : IsUnit (S p).det := by rw [hS1, det_one]; exact isUnit_one
  have hsu : IsUnit (subGram (S p)).det := by
    have h11 : subGram (1 : Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ) = 1 := by
      ext a b; simp [subGram, toBlocks₁₁, one_apply]
    rw [hS1, h11, det_one]; exact isUnit_one
  have hSh : ∀ᶠ v in 𝓝 p, (S v).IsHermitian := hh.mono fun v hv => hv.submatrix _
  have hQh : ∀ᶠ v in 𝓝 p, (quotGram (S v)).IsHermitian :=
    hSh.mono fun v hv => isHermitian_quotGram hv
  have hQ2 : MContDiffAt 2 (fun v => quotGram (S v)) p := hS2.quotGram hsu
  have hQu := isUnit_det_quotGram hSu hsu
  have e1 : ddbar (fun v => ((-Real.log (quotGram (S v)).det.re : ℝ) : ℂ)) p ξ η =
      (curv (fun v => quotGram (S v)) p ξ η).trace := by
    rw [trace_curv hQ2 hQh hQu, ← ContinuousLinearMap.neg_apply, ← ContinuousLinearMap.neg_apply,
      ← leviForm_neg]; rfl
  have e2 := trace_curv_eq_sub_add_quot hS2 hSu hsu ξ η
  have hsub : (fun v => subGram (S v)) =
      fun v => (H v).submatrix (emb i ∘ Sum.inl) (emb i ∘ Sum.inl) := by
    funext v; ext a b; rfl
  rw [hsub] at e2
  have tS := trace_curv_submatrix_of_eq_one H p (emb i) hinj h2 hh h1 ξ η
  have tT := trace_curv_submatrix_of_eq_one H p (emb i ∘ Sum.inl)
    (hinj.comp Sum.inl_injective) h2 hh h1 ξ η
  have hc : ∀ ζ, conn H p ζ = (mdel H p ζ)ᵀ := by
    intro ζ; rw [conn, h1, transpose_one, inv_one, Matrix.one_mul]
  have hb : ∀ a b, mdbar H p η a b = starRingEnd ℂ (mdel H p η b a) := by
    intro a b; rw [← conjTranspose_mdel hh]; rfl
  have hcurv : curv H p ξ η i i = ∑ c, conn H p ξ c i * starRingEnd ℂ (conn H p η c i)
      - mddbar H p ξ η i i := by
    rw [curv_eq h2 (by rw [h1, det_one]; exact isUnit_one), h1]
    simp only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply,
      Matrix.mul_apply, transpose_apply, hc]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hb, mul_comm]
  have hI : ∀ g : Fin N → ℂ, ∑ a ∈ Finset.Iio i, g a = ∑ a : Fin i, g (Fin.castLE i.isLt.le a) := by
    intro g
    have hIio : Finset.Iio i = Finset.univ.map (Fin.castLEEmb i.isLt.le) := by
      ext x
      simp only [Finset.mem_Iio, Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
      constructor
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩; exact y.isLt
    rw [hIio, Finset.sum_map]
    rfl
  have hU : ∀ g : Fin N → ℂ, ∑ c, g c = ∑ c ∈ Finset.Iio i, g c + g i + ∑ c ∈ Finset.Ioi i, g c := by
    intro g
    have hu : (Finset.univ : Finset (Fin N)) = (Finset.Iic i).disjUnion (Finset.Ioi i)
        (Finset.disjoint_left.2 fun x hx hx' => by
          simp only [Finset.mem_Iic, Finset.mem_Ioi] at hx hx'; exact absurd hx (not_le.2 hx')) := by
      ext x; simp only [Finset.mem_univ, Finset.disjUnion_eq_union, Finset.mem_union,
        Finset.mem_Iic, Finset.mem_Ioi, true_iff]; exact le_or_gt x i
    rw [hu, Finset.sum_disjUnion, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
    ring
  rw [e1, ← sub_eq_of_eq_add' e2, tS, tT, hcurv, hU (fun c => conn H p ξ c i * starRingEnd ℂ (conn H p η c i)),
]
  simp only [hI, Fintype.sum_sum_type, Fin.sum_univ_one, Function.comp_apply, emb, Sum.elim_inl,
    Sum.elim_inr, Finset.sum_add_distrib]
  ring

end GlobalTheory.GradedLine
