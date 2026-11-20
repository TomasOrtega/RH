import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

/- English proof (translation)
Simplify using `only [hrow, Formalism.UG.hform, dotProduct, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [hrow, Formalism.UG.hform, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Establish `key : ∀ (a c : Fin n → A) (t : A), (t • Matrix.vecMulVec a c) *ᵥ y = (t * (c ⬝ᵥ y)) • a`. Introduce `a c t`. Use function extensionality and compare the values at `q`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun r _ => by ring`.

Establish `hsum : ∀ (s : Finset (Fin k)) (f : Fin k → Matrix (Fin n) (Fin n) A), (∑ i ∈ s, f i) *ᵥ y = ∑ i ∈ s, f i *ᵥ y`. Introduce `s f`. Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]`.

Unfold `sMat`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, hsum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_mulVec, key, key, hrow_dot, hrow_dot]`.
-/
theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  have key : ∀ (a c : Fin n → A) (t : A), (t • Matrix.vecMulVec a c) *ᵥ y = (t * (c ⬝ᵥ y)) • a := by
    intro a c t
    funext q
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hsum : ∀ (s : Finset (Fin k)) (f : Fin k → Matrix (Fin n) (Fin n) A),
      (∑ i ∈ s, f i) *ᵥ y = ∑ i ∈ s, f i *ᵥ y := by
    intro s f
    classical
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]
  unfold sMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, key, key, hrow_dot, hrow_dot]

end Alg

variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Rewrite using `[sMat_mulVec]`. Use `X.B.I.Lf.add_mem hy (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)` and prove the remaining obligations. Establish `h1 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (bs j) y ∈ IntAf X.B.I.F X.B.I.E` using `(hI X.B.I).1 _ (hb j).2 _ hy`. Establish `h2 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (b j) y ∈ IntAf X.B.I.F X.B.I.E` using `(hI X.B.I).1 _ (hb j).1 _ hy`. Use `X.B.I.Lf.add_mem ?_ ?_` and prove the remaining obligations.

Conclude with `X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).1 h1⟩ (hb i).1`. Conclude with `X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).2 h2⟩ (hb i).2`.
-/
theorem sMat_Lf (hI : IdxDInt) (b bs : Fin D.R.k → VA X.B.I) (hb : ∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf)
    (C D' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ (D' - 1) i j ∈ IntAf X.B.I.F X.B.I.E)
    (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    sMat (sigA X.B.I) (JA X.B.I) b bs C D' *ᵥ y ∈ X.B.I.Lf := by
  rw [sMat_mulVec]
  refine X.B.I.Lf.add_mem hy (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  have h1 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (bs j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).2 _ hy
  have h2 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (b j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).1 _ hy
  refine X.B.I.Lf.add_mem ?_ ?_
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).1 h1⟩ (hb i).1
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).2 h2⟩ (hb i).2

/- English proof (translation)
Rewrite using `[Matrix.sub_apply, Matrix.one_apply]`. Use `split_ifs`. Conclude with `sub_mem hC (one_mem _)`. Simplify using `using hC`.
-/
theorem one_sub_int (i j : Fin D.R.k) (C : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : C i j ∈ IntAf X.B.I.F X.B.I.E) : (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem hC (one_mem _)
  · simpa using hC

/- English proof (translation)
Establish `h1 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1` using `by first`. Consider the case `simp [Formalism.MainNotions.S.AutInst.fmat]`. Consider the case `(simp only [Formalism.MainNotions.S.AutInst.fmat]`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one])`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fmat_inv_fix (x : X.B.I.Gf) (w : VA X.B.I) (h : X.B.I.fmat x *ᵥ w = w) : X.B.I.fmat x⁻¹ *ᵥ w = w := by
  have h1 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    first
    | simp [Formalism.MainNotions.S.AutInst.fmat]
    | (simp only [Formalism.MainNotions.S.AutInst.fmat]
       rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one])
  calc X.B.I.fmat x⁻¹ *ᵥ w = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ w) := by rw [h]
    _ = (X.B.I.fmat x⁻¹ * X.B.I.fmat x) *ᵥ w := by rw [Matrix.mulVec_mulVec]
    _ = w := by rw [h1, Matrix.one_mulVec]

/- English proof (translation)
Break down `hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz` into its components or cases. Rewrite using `[show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) from fmat_inv_fix _ _ (X.xu_fix u a).1]`. Conclude with `Or.inl (Or.inl ⟨a, rfl⟩)`. Rewrite using `[show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) from fmat_inv_fix _ _ (X.xu_fix u a).2]`. Conclude with `Or.inl (Or.inr ⟨a, rfl⟩)`.

Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Conclude with `Or.inr rfl`.
-/
theorem fixV_of (u : D.what₂.Word) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y ∈ fixV X u := by
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).1]
    exact Or.inl (Or.inl ⟨a, rfl⟩)
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).2]
    exact Or.inl (Or.inr ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr rfl

/- English proof (translation)
Introduce `D X Y u _ A`. Take `⟨e, he⟩` from `hAd X.B.I.F X.B.g`. Take `⟨b, bs, hfr, hL, hperp, hcong⟩` from `hFr D X u e he`. Take `⟨C, C', hCC, hint, hres⟩` from `hMat D X Y.TR e he A`. Take `⟨hinv, hherm⟩` from `hSig X.B.I`.

Take `⟨hfix, hcomp, hone, hunit⟩` from `hAlg _ (sigA X.B.I) X.B.I.n D.R.k (JA X.B.I) (epsX X e) b bs hinv hherm hfr`. Establish `hCC' : C * C' = 1` using `mul_eq_one_comm.mp hCC`. Use `set σ := sigA X.B.I with hσ`. Use `set s := sMat σ (JA X.B.I) b bs C (C'.map σ)ᵀ with hs`. Use `set sI := sMat σ (JA X.B.I) b bs C' (C.map σ)ᵀ with hsI`.

Establish `hmapT : ∀ M N : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), M * N = 1 → (N.map σ)ᵀ * (M.map σ)ᵀ = 1`. Introduce `M N hMN`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]`. Establish `h1 : s * sI = 1`. Rewrite using `[hs, hsI, hcomp, hCC', hmapT C C' hCC']`.

Conclude with `hone 1 1 (by simp) (by simp)`. Establish `h2 : sI * s = 1`. Rewrite using `[hs, hsI, hcomp, hCC, hmapT C' C hCC]`. Conclude with `hone 1 1 (by simp) (by simp)`. Set `u0 : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)` to `⟨s, sI, h1, h2⟩`.

Establish `hmem : u0 ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F)` using `hunit C C' hCC`. Set `s' : X.B.I.Gf` to `⟨u0, hmem⟩`. Establish `hfs : X.B.I.fmat s' = s` using `rfl`. Establish `hintS : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C'.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E` using `fun i j => ⟨one_sub_int i j C (hint i j).1, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).2)⟩`. Establish `hintI : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E` using `fun i j => ⟨one_sub_int i j C' (hint i j).2, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).1)⟩`.

Establish `hK : s' ∈ X.B.I.Kset` using `by show ∀ x, x ∈ X.B.I.Lf ↔ s *ᵥ x ∈ X.B.I.Lf`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Conclude with `sMat_Lf hI b bs hL C _ hintS x`. Introduce `hx`.

Use `sMat_Lf hI b bs hL C' _ hintI _ hx` as an intermediate fact. Rewrite `this` using `[← hsI, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `hfixs : ∀ w ∈ fixV X u, s *ᵥ w = w`. Introduce `w hw`. Conclude with `hfix C _ w fun j => hperp j w hw`.

Set `sF : Hfin X u` to `⟨X.xu u * s' * (X.xu u)⁻¹, by`. Introduce `y hy`. Establish `e1 : X.B.I.fmat (X.xu u * s' * (X.xu u)⁻¹) = X.B.I.fmat (X.xu u) * X.B.I.fmat s' * X.B.I.fmat (X.xu u)⁻¹` using `rfl`. Establish `e2 : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1`. Establish `: X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = X.B.I.fmat (X.xu u * (X.xu u)⁻¹)` using `rfl`.

Rewrite using `[this, mul_inv_cancel]`. Both sides reduce to the same expression. Rewrite using `[e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfs, hfixs _ (fixV_of u y hy), Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]⟩`. Establish `hcj : cj X u sF = s'` using `by show (X.xu u)⁻¹ * (X.xu u * s' * (X.xu u)⁻¹) * X.xu u = s' group`. Use `⟨sF, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcj]`. Conclude with `hK`. Rewrite using `[hcj]`. Use function extensionality and compare the values at `v`. Establish `hM : leviM Y.TR s' v = ((A v : GL (Fin D.R.k) (Y.TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (Y.TR.Fq v))`.

Use extensionality with `i j`. Rewrite using `[← hres v i j]`. Conclude with `hLev D X Y.TR e he b bs hfr hL hcong C C' hCC hint v i j`. Unfold `levi`. Use `split_ifs with hdet`.

Use extensionality with `i j show leviM Y.TR s' v i j = _`. Rewrite using `[hM]`. Conclude with `absurd (by rw [hM]; exact (A v).isUnit.map Matrix.detMonoidHom) hdet`.
-/
theorem idxSurj_of (hAlg : IdxDAlg) (hAd : IdxDAd) (hI : IdxDInt) (hSig : IdxDSig) (hFr : IdxDFrame)
    (hMat : IdxDMat) (hLev : IdxDLevi) : IdxSurj := by
  intro D X Y u _ A
  obtain ⟨e, he⟩ := hAd X.B.I.F X.B.g
  obtain ⟨b, bs, hfr, hL, hperp, hcong⟩ := hFr D X u e he
  obtain ⟨C, C', hCC, hint, hres⟩ := hMat D X Y.TR e he A
  obtain ⟨hinv, hherm⟩ := hSig X.B.I
  obtain ⟨hfix, hcomp, hone, hunit⟩ :=
    hAlg _ (sigA X.B.I) X.B.I.n D.R.k (JA X.B.I) (epsX X e) b bs hinv hherm hfr
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  set σ := sigA X.B.I with hσ
  set s := sMat σ (JA X.B.I) b bs C (C'.map σ)ᵀ with hs
  set sI := sMat σ (JA X.B.I) b bs C' (C.map σ)ᵀ with hsI
  have hmapT : ∀ M N : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), M * N = 1 →
      (N.map σ)ᵀ * (M.map σ)ᵀ = 1 := by
    intro M N hMN
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  have h1 : s * sI = 1 := by
    rw [hs, hsI, hcomp, hCC', hmapT C C' hCC']
    exact hone 1 1 (by simp) (by simp)
  have h2 : sI * s = 1 := by
    rw [hs, hsI, hcomp, hCC, hmapT C' C hCC]
    exact hone 1 1 (by simp) (by simp)
  let u0 : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := ⟨s, sI, h1, h2⟩
  have hmem : u0 ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := hunit C C' hCC
  let s' : X.B.I.Gf := ⟨u0, hmem⟩
  have hfs : X.B.I.fmat s' = s := rfl
  have hintS : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C'.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C (hint i j).1, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).2)⟩
  have hintI : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C' (hint i j).2, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).1)⟩
  have hK : s' ∈ X.B.I.Kset := by
    show ∀ x, x ∈ X.B.I.Lf ↔ s *ᵥ x ∈ X.B.I.Lf
    intro x
    constructor
    · exact sMat_Lf hI b bs hL C _ hintS x
    · intro hx
      have := sMat_Lf hI b bs hL C' _ hintI _ hx
      rwa [← hsI, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at this
  have hfixs : ∀ w ∈ fixV X u, s *ᵥ w = w := by
    intro w hw
    exact hfix C _ w fun j => hperp j w hw
  let sF : Hfin X u := ⟨X.xu u * s' * (X.xu u)⁻¹, by
    intro y hy
    have e1 : X.B.I.fmat (X.xu u * s' * (X.xu u)⁻¹) =
        X.B.I.fmat (X.xu u) * X.B.I.fmat s' * X.B.I.fmat (X.xu u)⁻¹ := rfl
    have e2 : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
      have : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = X.B.I.fmat (X.xu u * (X.xu u)⁻¹) := rfl
      rw [this, mul_inv_cancel]; rfl
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfs, hfixs _ (fixV_of u y hy),
      Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]⟩
  have hcj : cj X u sF = s' := by
    show (X.xu u)⁻¹ * (X.xu u * s' * (X.xu u)⁻¹) * X.xu u = s'
    group
  refine ⟨sF, ?_, ?_⟩
  · rw [hcj]; exact hK
  · rw [hcj]
    funext v
    have hM : leviM Y.TR s' v = ((A v : GL (Fin D.R.k) (Y.TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (Y.TR.Fq v)) := by
      ext i j
      rw [← hres v i j]
      exact hLev D X Y.TR e he b bs hfr hL hcong C C' hCC hint v i j
    unfold levi
    split_ifs with hdet
    · ext i j
      show leviM Y.TR s' v i j = _
      rw [hM]
    · exact absurd (by rw [hM]; exact (A v).isUnit.map Matrix.detMonoidHom) hdet

end PI.UnitaryDimensionFormula
