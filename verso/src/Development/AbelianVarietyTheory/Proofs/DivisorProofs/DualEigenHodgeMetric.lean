import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualEigFrame

open Matrix

/- English proof (translation)
Simplify using `only [HermFrame.form_eq_sum, Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[blockDiagonal'_apply_eq]`. Introduce `t' _ ht'`.

Simplify using `[blockDiagonal'_apply_ne A i _ (Ne.symm ht')]`. Simplify using the standard rewrite rules.
-/
theorem form_blockDiagonal' {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → Type} [∀ t, Fintype (d t)]
    (A : ∀ t, Matrix (d t) (d t) ℂ) (v w : (Σ t, d t) → ℂ) :
    HermFrame.form (blockDiagonal' A) v w =
      ∑ t, HermFrame.form (A t) (fun i => v ⟨t, i⟩) (fun i => w ⟨t, i⟩) := by
  simp only [HermFrame.form_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single t]
  · simp [blockDiagonal'_apply_eq]
  · intro t' _ ht'
    simp [blockDiagonal'_apply_ne A i _ (Ne.symm ht')]
  · simp

/- English proof (translation)
Establish `hM : Gm * Gm⁻¹ = 1` using `mul_nonsing_inv _ hu`. Establish `h1 : P * (Q * (Pᴴ * Gm⁻¹ * P) - 1) = 0`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Q * (Pᴴ * Gm⁻¹ * P) - 1 = 0`.

Use extensionality with `s s'`. Establish `key : P *ᵥ (fun t => (Q * (Pᴴ * Gm⁻¹ * P) - 1 : Matrix κ κ ℂ) t s') = P *ᵥ 0`. Rewrite using `[mulVec_zero]`. Use function extensionality and compare the values at `b`. Use `congrFun (congrFun h1 b) s'` as an intermediate fact.

Simplify `this` using `[mulVec, dotProduct, mul_apply]`. Conclude with `congrFun (hP key) s`. Establish `h3 : Q * (Pᴴ * Gm⁻¹ * P) = 1` using `sub_eq_zero.1 h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conjTranspose_mul_inv_mul {g : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (P : Matrix (Fin g) κ ℂ)
    (hP : Function.Injective P.mulVec) (Q R : Matrix κ κ ℂ) (hRQ : R * Q = 1) (Gm : Matrix (Fin g) (Fin g) ℂ)
    (hu : IsUnit Gm.det) (hG : Gm = P * Q * Pᴴ) : Pᴴ * Gm⁻¹ * P = R := by
  have hM : Gm * Gm⁻¹ = 1 := mul_nonsing_inv _ hu
  have h1 : P * (Q * (Pᴴ * Gm⁻¹ * P) - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
    calc P * (Q * (Pᴴ * Gm⁻¹ * P)) = (P * Q * Pᴴ) * Gm⁻¹ * P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [← hG, hM, Matrix.one_mul]
  have h2 : Q * (Pᴴ * Gm⁻¹ * P) - 1 = 0 := by
    ext s s'
    have key : P *ᵥ (fun t => (Q * (Pᴴ * Gm⁻¹ * P) - 1 : Matrix κ κ ℂ) t s') = P *ᵥ 0 := by
      rw [mulVec_zero]
      funext b
      have := congrFun (congrFun h1 b) s'
      simpa [mulVec, dotProduct, mul_apply] using this
    exact congrFun (hP key) s
  have h3 : Q * (Pᴴ * Gm⁻¹ * P) = 1 := sub_eq_zero.1 h2
  calc Pᴴ * Gm⁻¹ * P = (R * Q) * (Pᴴ * Gm⁻¹ * P) := by rw [hRQ, Matrix.one_mul]
    _ = R := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[HermFrame.form_eq_sum, HermFrame.dualGram]`. Simplify using `only [transpose_apply, mul_apply, conjTranspose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_dualGram_cols {g : ℕ} {κ : Type} [Fintype κ] (P : Matrix (Fin g) κ ℂ) (Gm : Matrix (Fin g) (Fin g) ℂ)
    (s s' : κ) :
    HermFrame.form (HermFrame.dualGram Gm) (fun b => P b s) (fun b => P b s') = (Pᴴ * Gm⁻¹ * P) s' s := by
  rw [HermFrame.form_eq_sum, HermFrame.dualGram]
  simp only [transpose_apply, mul_apply, conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Complex.star_def]
  ring

end GlobalTheory.DualEigFrame

namespace GlobalTheory.DualEigFrame

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Oz _ β Z G g h hd σ' yc y e ch hy u P hP hbij`. Establish `: QuasiSeparated Z.t.G.hom` using `have := Z.t.semi.separated`. Use `inferInstance`. Take `⟨U, W, hxU, hUle, c0⟩` from `GlobalTheory.Conormal.exists_isChart (GlobalTheory.LieVB.sec_hom (MonObj.one (X := Z.t.G))) (x := y.1 (IsLocalRing.closedPoint ℂ)) (V := ch.U) (CxPts.mem_ptsIn.1 hy)`. Use `choose a ha using fun b => c0.d_surjective (GlobalTheory.LieVB.sec_hom (MonObj.one (X := Z.t.G))) (GlobalTheory.Twist.resM (omega Z.t.G) hUle (ch.e b))`.

Establish `ha' : ∀ b, GlobalTheory.LieVB.dUnit Z.t.G c0.le (a b) = GlobalTheory.Twist.resM (omega Z.t.G) hUle (ch.e b)` using `ha`. Establish `hyU : y ∈ CxPts.ptsIn Z.s (σ'.comp β) U` using `CxPts.mem_ptsIn.2 hxU`. Establish `hxU' : ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ U` using `e ▸ hyU`. Establish `hxC : ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ ch.U` using `e ▸ hy`. Establish `hval : ∀ b τ i, (valR (u.v τ i) W (a b)).snd = P b ⟨τ, i⟩`.

Introduce `b τ i`. Rewrite using `[← (GlobalTheory.LocM.tanEv_dUnit_eq (u.tan τ i) hxU' c0.le (a b)).2, ha', GlobalTheory.LocM.tanEv_resM, hP ⟨τ, i⟩ (u.tan τ i) hxC b]`. Use `set Gm := (h.met (σ'.comp β)).G ch y with hGm`. Set `Q : Matrix (Σ τ, Fin (Dw.mult τ)) (Σ τ, Fin (Dw.mult τ)) ℂ` to `blockDiagonal' fun τ => ((G σ').gram yc u τ)⁻¹`. Set `R : Matrix (Σ τ, Fin (Dw.mult τ)) (Σ τ, Fin (Dw.mult τ)) ℂ` to `blockDiagonal' fun τ => (G σ').gram yc u τ`.

Establish `hG : Gm = P * Q * Pᴴ`. Use extensionality with `b b'`. Establish `e1 : Gm b b' = ∑ τ, HermFrame.form ((G σ').gram yc u τ)⁻¹ (fun i => P b ⟨τ, i⟩) (fun i => P b' ⟨τ, i⟩)`. Rewrite using `[hGm, ← (h.met _).form_frame ch hy, ← (h.met _).form_resM _ _ hUle hyU, ← ha', ← ha', hd σ' yc y e u U W c0.le (a b) (a b') hyU]`. Simplify using `only [hval]`.

Rewrite using `[e1, ← form_blockDiagonal', HermFrame.form_eq_sum]`. Simplify using `only [mul_apply, conjTranspose_apply, Finset.sum_mul, Q]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Complex.star_def]`. Establish `hRQ : R * Q = 1`.

Simplify using `only [R, Q, ← blockDiagonal'_mul]`. Rewrite using `[← blockDiagonal'_one]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 ((G σ').pos yc u τ).isUnit)`.

Establish `hu : IsUnit Gm.det` using `(isUnit_iff_isUnit_det _).1 ((h.met _).posDef ch y hy).isUnit`. Establish `hX` using `conjTranspose_mul_inv_mul P hbij.1 Q R hRQ Gm hu hG`. Use `⟨fun τ i j => ?_, fun s s' hs => ?_⟩` and prove the remaining obligations. Rewrite using `[form_dualGram_cols, hX]`. Simplify using `[R, blockDiagonal'_apply_eq]`.

Rewrite using `[form_dualGram_cols, hX]`. Take `⟨τ, i⟩` from `s`. Take `⟨τ', j⟩` from `s'`. Conclude with `blockDiagonal'_apply_ne _ _ _ (Ne.symm hs)`.
-/
theorem dualGram_tanMat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (G : ∀ σ', EigMet Z σ') {g : ℕ} (h : VMetric Z.s (omega Z.t.G) g), IsDualEig G h →
    ∀ (σ' : c.F →+* ℂ) (yc : CxPts (genStr Z) σ') (y : CxPts Z.s (σ'.comp β)), y.1 = yc.1 ≫ genι Z →
    ∀ (ch : VB.Chart (omega Z.t.G) g), y ∈ CxPts.ptsIn Z.s (σ'.comp β) ch.U →
    ∀ (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (P : Matrix (Fin g) (Σ τ, Fin (Dw.mult τ)) ℂ),
      IsTanMat Z (yc.1 ≫ genι Z) ch (fun s : Σ τ, Fin (Dw.mult τ) => u.v s.1 s.2) P → Function.Bijective P.mulVec →
      (∀ τ i j, HermFrame.form (HermFrame.dualGram ((h.met _).G ch y)) (fun b => P b ⟨τ, i⟩) (fun b => P b ⟨τ, j⟩) =
        (G σ').gram yc u τ j i) ∧
      ∀ s s' : Σ τ, Fin (Dw.mult τ), s.1 ≠ s'.1 →
        HermFrame.form (HermFrame.dualGram ((h.met _).G ch y)) (fun b => P b s) (fun b => P b s') = 0 := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z G g h hd σ' yc y e ch hy u P hP hbij
  classical
  have : QuasiSeparated Z.t.G.hom := have := Z.t.semi.separated; inferInstance
  obtain ⟨U, W, hxU, hUle, c0⟩ := GlobalTheory.Conormal.exists_isChart (GlobalTheory.LieVB.sec_hom (MonObj.one (X := Z.t.G)))
    (x := y.1 (IsLocalRing.closedPoint ℂ)) (V := ch.U) (CxPts.mem_ptsIn.1 hy)
  choose a ha using fun b => c0.d_surjective (GlobalTheory.LieVB.sec_hom (MonObj.one (X := Z.t.G)))
    (GlobalTheory.Twist.resM (omega Z.t.G) hUle (ch.e b))
  have ha' : ∀ b, GlobalTheory.LieVB.dUnit Z.t.G c0.le (a b) = GlobalTheory.Twist.resM (omega Z.t.G) hUle (ch.e b) := ha
  have hyU : y ∈ CxPts.ptsIn Z.s (σ'.comp β) U := CxPts.mem_ptsIn.2 hxU
  have hxU' : ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ U := e ▸ hyU
  have hxC : ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ ch.U := e ▸ hy
  have hval : ∀ b τ i, (valR (u.v τ i) W (a b)).snd = P b ⟨τ, i⟩ := by
    intro b τ i
    rw [← (GlobalTheory.LocM.tanEv_dUnit_eq (u.tan τ i) hxU' c0.le (a b)).2, ha', GlobalTheory.LocM.tanEv_resM,
      hP ⟨τ, i⟩ (u.tan τ i) hxC b]
  set Gm := (h.met (σ'.comp β)).G ch y with hGm
  let Q : Matrix (Σ τ, Fin (Dw.mult τ)) (Σ τ, Fin (Dw.mult τ)) ℂ := blockDiagonal' fun τ => ((G σ').gram yc u τ)⁻¹
  let R : Matrix (Σ τ, Fin (Dw.mult τ)) (Σ τ, Fin (Dw.mult τ)) ℂ := blockDiagonal' fun τ => (G σ').gram yc u τ
  have hG : Gm = P * Q * Pᴴ := by
    ext b b'
    have e1 : Gm b b' = ∑ τ, HermFrame.form ((G σ').gram yc u τ)⁻¹ (fun i => P b ⟨τ, i⟩) (fun i => P b' ⟨τ, i⟩) := by
      rw [hGm, ← (h.met _).form_frame ch hy, ← (h.met _).form_resM _ _ hUle hyU, ← ha', ← ha',
        hd σ' yc y e u U W c0.le (a b) (a b') hyU]
      simp only [hval]
    rw [e1, ← form_blockDiagonal', HermFrame.form_eq_sum]
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, Q]
    rw [Finset.sum_comm]
    simp only [Complex.star_def]
  have hRQ : R * Q = 1 := by
    simp only [R, Q, ← blockDiagonal'_mul]
    rw [← blockDiagonal'_one]
    congr 1
    funext τ
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 ((G σ').pos yc u τ).isUnit)
  have hu : IsUnit Gm.det := (isUnit_iff_isUnit_det _).1 ((h.met _).posDef ch y hy).isUnit
  have hX := conjTranspose_mul_inv_mul P hbij.1 Q R hRQ Gm hu hG
  refine ⟨fun τ i j => ?_, fun s s' hs => ?_⟩
  · rw [form_dualGram_cols, hX]
    simp [R, blockDiagonal'_apply_eq]
  · rw [form_dualGram_cols, hX]
    obtain ⟨τ, i⟩ := s
    obtain ⟨τ', j⟩ := s'
    exact blockDiagonal'_apply_ne _ _ _ (Ne.symm hs)

end GlobalTheory.DualEigFrame

end
