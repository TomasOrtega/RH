import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ}

/- English proof (translation)
Rewrite using `[show ((1 : GA D A), (1 : GA D L)) = 1 from rfl, map_one, mt_one]`.
-/
theorem mt_emb_one (o : OrthDec S₀ A L) : mt S₀ (o.emb (1, 1)) = 1 := by
  rw [show ((1 : GA D A), (1 : GA D L)) = 1 from rfl, map_one, mt_one]

/- English proof (translation)
Rewrite using `[← mt_mul, ← map_mul, Prod.mk_mul_mk, mul_one]`.
-/
theorem mt_emb_mul (o : OrthDec S₀ A L) (h h' : GA D A) :
    mt S₀ (o.emb (h * h', 1)) = mt S₀ (o.emb (h, 1)) ⬝ mt S₀ (o.emb (h', 1)) := by
  rw [← mt_mul, ← map_mul, Prod.mk_mul_mk, mul_one]

def Good (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A)) (g : GA D S) : Prop :=
  (∃ M : GL (Fin ρ) (AE D), mt S g ⬝ d.jX = d.jX ⬝ M.1) ∧
    ∃ h ∈ T, ∃ B : Mx D ρ S₀.rank, mt S g ⬝ d.j0 = d.j0 ⬝ mt S₀ (o.emb (h, 1)) + d.jX ⬝ B

section Good

variable (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A))

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩, 1, T.one_mem, 0, by rw [mt_one, Matrix.one_mul, mt_emb_one, Matrix.mul_one, Matrix.mul_zero, add_zero]⟩`.
-/
theorem good_one : Good d o T 1 :=
  ⟨⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩,
    1, T.one_mem, 0, by rw [mt_one, Matrix.one_mul, mt_emb_one, Matrix.mul_one, Matrix.mul_zero, add_zero]⟩

/- English proof (translation)
Take `⟨⟨M, hM⟩, h, hT, B, hB⟩` from `hg`. Take `⟨⟨M', hM'⟩, h', hT', B', hB'⟩` from `hg'`. Use `⟨⟨M * M', ?_⟩, h * h', T.mul_mem hT hT', B ⬝ mt S₀ (o.emb (h', 1)) + M.1 ⬝ B', ?_⟩` and prove the remaining obligations. Rewrite using `[mt_mul, Matrix.mul_assoc, hM', ← Matrix.mul_assoc, hM, Matrix.mul_assoc, Units.val_mul]`. Rewrite using `[mt_mul, Matrix.mul_assoc, hB', Matrix.mul_add, ← Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hM, mt_emb_mul]`.

Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]`.
-/
theorem good_mul {g g' : GA D S} (hg : Good d o T g) (hg' : Good d o T g') : Good d o T (g * g') := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  obtain ⟨⟨M', hM'⟩, h', hT', B', hB'⟩ := hg'
  refine ⟨⟨M * M', ?_⟩, h * h', T.mul_mem hT hT', B ⬝ mt S₀ (o.emb (h', 1)) + M.1 ⬝ B', ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, hM', ← Matrix.mul_assoc, hM, Matrix.mul_assoc, Units.val_mul]
  · rw [mt_mul, Matrix.mul_assoc, hB', Matrix.mul_add, ← Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hM, mt_emb_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]

/- English proof (translation)
Take `⟨⟨M, hM⟩, h, hT, B, hB⟩` from `hg`. Establish `hI : mt S g⁻¹ ⬝ mt S g = 1` using `mt_inv_mul S g`. Establish `hMM : (M.1 : Mx D ρ ρ) ⬝ (M⁻¹).1 = 1` using `M.mul_inv`. Establish `hX : mt S g⁻¹ ⬝ d.jX = d.jX ⬝ (M⁻¹).1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc (mt S g⁻¹), Matrix.mul_assoc d.jX, hMM, Matrix.mul_one]`. Use `_ = d.jX ⬝ (M⁻¹).1 := by rw [← hM, ← Matrix.mul_assoc, hI, Matrix.one_mul]`. Use `⟨⟨M⁻¹, hX⟩, h⁻¹, T.inv_mem hT, -((M⁻¹).1 ⬝ B ⬝ mt S₀ (o.emb (h⁻¹, 1))), ?_⟩` and prove the remaining obligations. Establish `hH : mt S₀ (o.emb (h, 1)) ⬝ mt S₀ (o.emb (h⁻¹, 1)) = 1`. Rewrite using `[← mt_emb_mul, mul_inv_cancel, mt_emb_one]`.

Establish `h1 : mt S g⁻¹ ⬝ d.j0 ⬝ mt S₀ (o.emb (h, 1)) + d.jX ⬝ (M⁻¹).1 ⬝ B = d.j0`. Establish `h2 : mt S g⁻¹ ⬝ (mt S g ⬝ d.j0) = d.j0` using `by rw [← Matrix.mul_assoc, hI, Matrix.one_mul]`. Rewrite `h2` using `[hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX]`. Conclude with `h2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc _ (mt S₀ _), hH, Matrix.mul_one]`. Use `_ = (d.j0 - d.jX ⬝ (M⁻¹).1 ⬝ B) ⬝ mt S₀ (o.emb (h⁻¹, 1)) := by rw [eq_sub_of_add_eq h1]`. Use `_ = _ := by simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]`.
-/
theorem good_inv {g : GA D S} (hg : Good d o T g) : Good d o T g⁻¹ := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  have hI : mt S g⁻¹ ⬝ mt S g = 1 := mt_inv_mul S g
  have hMM : (M.1 : Mx D ρ ρ) ⬝ (M⁻¹).1 = 1 := M.mul_inv
  have hX : mt S g⁻¹ ⬝ d.jX = d.jX ⬝ (M⁻¹).1 := by
    calc mt S g⁻¹ ⬝ d.jX = mt S g⁻¹ ⬝ (d.jX ⬝ M.1) ⬝ (M⁻¹).1 := by
          rw [Matrix.mul_assoc (mt S g⁻¹), Matrix.mul_assoc d.jX, hMM, Matrix.mul_one]
      _ = d.jX ⬝ (M⁻¹).1 := by rw [← hM, ← Matrix.mul_assoc, hI, Matrix.one_mul]
  refine ⟨⟨M⁻¹, hX⟩, h⁻¹, T.inv_mem hT, -((M⁻¹).1 ⬝ B ⬝ mt S₀ (o.emb (h⁻¹, 1))), ?_⟩
  have hH : mt S₀ (o.emb (h, 1)) ⬝ mt S₀ (o.emb (h⁻¹, 1)) = 1 := by
    rw [← mt_emb_mul, mul_inv_cancel, mt_emb_one]
  have h1 : mt S g⁻¹ ⬝ d.j0 ⬝ mt S₀ (o.emb (h, 1)) + d.jX ⬝ (M⁻¹).1 ⬝ B = d.j0 := by
    have h2 : mt S g⁻¹ ⬝ (mt S g ⬝ d.j0) = d.j0 := by rw [← Matrix.mul_assoc, hI, Matrix.one_mul]
    rw [hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX] at h2
    exact h2
  calc mt S g⁻¹ ⬝ d.j0 = mt S g⁻¹ ⬝ d.j0 ⬝ mt S₀ (o.emb (h, 1)) ⬝ mt S₀ (o.emb (h⁻¹, 1)) := by
        rw [Matrix.mul_assoc _ (mt S₀ _), hH, Matrix.mul_one]
    _ = (d.j0 - d.jX ⬝ (M⁻¹).1 ⬝ B) ⬝ mt S₀ (o.emb (h⁻¹, 1)) := by rw [eq_sub_of_add_eq h1]
    _ = _ := by simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]

def goodSub : Subgroup (GA D S) where
  carrier := {g | Good d o T g}
  one_mem' := good_one d o T
  mul_mem' := good_mul d o T
  inv_mem' := good_inv d o T

end Good

end GlobalTheory.BesProj

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

/- English proof (translation)
Use `congrArg Matrix.conjTranspose d.i₀e` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.
-/
theorem eH_gram_i₀ : d.eᴴ * S.gram * d.i₀ = 0 := by
  have := congrArg Matrix.conjTranspose d.i₀e
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at this

/- English proof (translation)
Use `show Subgroup.closure _ ≤ _`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `g ⟨h1, h2⟩`. Use `choose a ha1 ha2 using h1`. Establish `hz : ∀ k : Fin S₀.rank, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * S.gram).mulVec (fun l => d.i₀ l k) = 0`.

Introduce `k`. Use function extensionality and compare the values at `j`. Conclude with `congrFun (congrFun (eH_gram_i₀ d) j) k`. Use `choose b hb using fun k => h2 _ (hz k)`. Set `U : Mx D ρ ρ` to `Matrix.of fun j i => a i j`.

Set `B : Mx D ρ S₀.rank` to `Matrix.of fun i k => b k i`. Establish `hU : (mt S g - 1) ⬝ d.jX = d.jX ⬝ U`. Use extensionality with `k i`. Conclude with `congrFun (ha2 i) k`. Establish `hB : (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B`.

Use extensionality with `k i`. Conclude with `congrFun (hb i) k`. Establish `hdet : (1 + U).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations.

Simplify using `[U, ha1 i i le_rfl]`. Introduce `i j hji`. Establish `hij : i ≠ j` using `ne_of_gt hji`. Simplify using `[U, ha1 j i hji.le, Matrix.one_apply_ne hij]`. Establish `hdu : IsUnit (1 + U).det` using `by rw [hdet]; exact isUnit_one`.

Set `M : GL (Fin ρ) (AE D)` to `⟨1 + U, (1 + U)⁻¹, Matrix.mul_nonsing_inv _ hdu, Matrix.nonsing_inv_mul _ hdu⟩`. Use `⟨⟨M, ?_⟩, 1, T.one_mem, B, ?_⟩` and prove the remaining obligations. Use `show mt S g ⬝ d.jX = d.jX ⬝ (1 + U)`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, ← hU, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]`. Rewrite using `[mt_emb_one, Matrix.mul_one, ← hB, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]`.
-/
theorem flagN_le_goodSub (T : Subgroup (GA D A)) : flagN d ≤ goodSub d o T := by
  show Subgroup.closure _ ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨h1, h2⟩
  choose a ha1 ha2 using h1
  have hz : ∀ k : Fin S₀.rank, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * S.gram).mulVec
      (fun l => d.i₀ l k) = 0 := by
    intro k; funext j
    exact congrFun (congrFun (eH_gram_i₀ d) j) k
  choose b hb using fun k => h2 _ (hz k)
  let U : Mx D ρ ρ := Matrix.of fun j i => a i j
  let B : Mx D ρ S₀.rank := Matrix.of fun i k => b k i
  have hU : (mt S g - 1) ⬝ d.jX = d.jX ⬝ U := by
    ext k i
    exact congrFun (ha2 i) k
  have hB : (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by
    ext k i
    exact congrFun (hb i) k
  have hdet : (1 + U).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [U, ha1 i i le_rfl]
    · intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      simp [U, ha1 j i hji.le, Matrix.one_apply_ne hij]
  have hdu : IsUnit (1 + U).det := by rw [hdet]; exact isUnit_one
  let M : GL (Fin ρ) (AE D) := ⟨1 + U, (1 + U)⁻¹, Matrix.mul_nonsing_inv _ hdu, Matrix.nonsing_inv_mul _ hdu⟩
  refine ⟨⟨M, ?_⟩, 1, T.one_mem, B, ?_⟩
  · show mt S g ⬝ d.jX = d.jX ⬝ (1 + U)
    rw [Matrix.mul_add, Matrix.mul_one, ← hU, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  · rw [mt_emb_one, Matrix.mul_one, ← hB, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨1, by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩, h, Subgroup.mem_top h, 0, by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_zero, add_zero]⟩`.
-/
theorem embA_mem_goodSub (h : GA D A) : embA d o h ∈ goodSub d o ⊤ :=
  ⟨⟨1, by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩, h, Subgroup.mem_top h, 0,
    by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_zero, add_zero]⟩

/- English proof (translation)
The claim follows from `sup_le (flagN_le_goodSub d o ⊤) (by rintro _ ⟨h, rfl⟩; exact embA_mem_goodSub d o h)`.
-/
theorem besGrp_le_goodSub : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) ≤ goodSub d o ⊤ :=
  sup_le (flagN_le_goodSub d o ⊤) (by rintro _ ⟨h, rfl⟩; exact embA_mem_goodSub d o h)

def matP (g : GA D S) : Mx D A.rank A.rank := o.pA ⬝ (d.p0 ⬝ mt S g ⬝ d.j0) ⬝ o.jA

/- English proof (translation)
Take `⟨-, h, hT, B, hB⟩` from `hg`. Use `⟨h, hT, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.one_mul, Matrix.zero_mul, add_zero]`.
-/
theorem bessel_flag_stabilizer_anisotropic_block_exists {T : Subgroup (GA D A)} {g : GA D S} (hg : g ∈ goodSub d o T) :
    ∃ h ∈ T, d.p0 ⬝ mt S g ⬝ d.j0 = mt S₀ (o.emb (h, 1)) := by
  obtain ⟨-, h, hT, B, hB⟩ := hg
  refine ⟨h, hT, ?_⟩
  rw [Matrix.mul_assoc, hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.one_mul,
    Matrix.zero_mul, add_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]`.
-/
theorem pA_emb_jA (h : GA D A) : o.pA ⬝ mt S₀ (o.emb (h, 1)) ⬝ o.jA = mt A h := by
  rw [Matrix.mul_assoc, o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]

/- English proof (translation)
Take `⟨h, -, hh⟩` from `bessel_flag_stabilizer_anisotropic_block_exists d o (besGrp_le_goodSub d o hg)`. Rewrite using `[matP, hh, pA_emb_jA]`. Conclude with `mt_unitary A h`.
-/
theorem anisotropicBlock_unitary {g : GA D S} (hg : g ∈ (flagN d ⊔ (embA d o).range : Subgroup (GA D S))) :
    adj (matP d o g) * (gA A * matP d o g) = gA A := by
  obtain ⟨h, -, hh⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (besGrp_le_goodSub d o hg)
  rw [matP, hh, pA_emb_jA]
  exact mt_unitary A h

/- English proof (translation)
Take `⟨h', hh', hn⟩` from `bessel_flag_stabilizer_anisotropic_block_exists d o (flagN_le_goodSub d o ⊥ n.2)`. Rewrite `hh'` using `[Subgroup.mem_bot]`. Rewrite `hn` using `[hh', mt_emb_one]`. Establish `: d.p0 ⬝ mt S (n.1 * embA d o h) ⬝ d.j0 = mt S₀ (o.emb (h, 1))`. Rewrite using `[mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hn, Matrix.one_mul]`.

Rewrite using `[matP, this, pA_emb_jA]`.
-/
theorem anisotropicBlock_mul_embA (n : flagN d) (h : GA D A) : matP d o (n.1 * embA d o h) = mt A h := by
  obtain ⟨h', hh', hn⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (flagN_le_goodSub d o ⊥ n.2)
  rw [Subgroup.mem_bot] at hh'
  rw [hh', mt_emb_one] at hn
  have : d.p0 ⬝ mt S (n.1 * embA d o h) ⬝ d.j0 = mt S₀ (o.emb (h, 1)) := by
    rw [mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hn,
      Matrix.one_mul]
  rw [matP, this, pA_emb_jA]

/- English proof (translation)
Introduce `D S S₀ A L ρ d o`. Use `⟨fun g => ofMat A (matP d o g.1) (anisotropicBlock_unitary d o g.2), ?_, fun h n => ?_⟩` and prove the remaining obligations. Use `continuous_of_mt A ?_ show Continuous fun g : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) => matP d o g.1` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul ((continuous_const.matrix_mul ((continuous_mt S).comp continuous_subtype_val)).matrix_mul continuous_const)).matrix_mul continuous_const`. Conclude with `mt_injective A (by rw [mt_ofMat]; exact anisotropicBlock_mul_embA d o n h)`.
-/
theorem exists_continuous_proj : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    ∃ p : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) → GA D A, Continuous p ∧
      ∀ (h : GA D A) (n : flagN d), p ⟨n.1 * embA d o h, mul_mem (Subgroup.mem_sup_left n.2)
        (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ A L ρ d o
  refine ⟨fun g => ofMat A (matP d o g.1) (anisotropicBlock_unitary d o g.2), ?_, fun h n => ?_⟩
  · refine continuous_of_mt A ?_
    show Continuous fun g : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) => matP d o g.1
    exact (continuous_const.matrix_mul ((continuous_const.matrix_mul ((continuous_mt S).comp continuous_subtype_val)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  · exact mt_injective A (by rw [mt_ofMat]; exact anisotropicBlock_mul_embA d o n h)

end GlobalTheory.BesProj
