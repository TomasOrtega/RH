import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMMulVecIncV

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus GlobalTheory.UnipMass GlobalTheory.LeviModulus.HCoord
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulus.HCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `A' : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]`. Establish `h2 : (A'ᵀ * M * A'.map star).det ≠ 0`. Rewrite using `[h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_neg]`.

Introduce `h0`. Apply `h2` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_of_hasSig_c {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

/- English proof (translation)
Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Use `det_ne_of_hasSig_c (h w)` as an intermediate fact. Introduce `h0`. Apply `this` to reduce the goal to its premises. Establish `e` using `RingHom.map_det (B.emb w).1 J`.

Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← e, h0, map_zero]`.
-/
theorem det_ne_of_sig_c {n r s : ℕ} (B : Base F E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig_c (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, cA_inclR']`.
-/
theorem incM_map_cA (σ : E →ₐ[F] E) {m k : ℕ} (A : Matrix (Fin m) (Fin k) E) :
    (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_inclR']

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul {m k l : ℕ} (A : Matrix (Fin m) (Fin k) E) (B : Matrix (Fin k) (Fin l) E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

/- English proof (translation)
Establish `hc : (fun i => cA σ ((incM F ι *ᵥ w) i)) = incM F (ι.map σ) *ᵥ fun i => cA σ (w i)`. Use function extensionality and compare the values at `i`. Rewrite using `[← incM_map_cA]`. Conclude with `RingHom.map_mulVec (cA σ).toRingHom (incM F ι) w i`. Rewrite using `[hA, hA, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show (incM F ι)ᵀ = incM F ιᵀ from rfl, ← incM_mul, ← incM_mul, hg]`.
-/
theorem hA_ιι (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (hg : ιᵀ * J * ι.map σ = J₁) (a w : Fin n₁ → AE F E) :
    hA σ J (incM F ι *ᵥ a) (incM F ι *ᵥ w) = hA σ J₁ a w := by
  have hc : (fun i => cA σ ((incM F ι *ᵥ w) i)) = incM F (ι.map σ) *ᵥ fun i => cA σ (w i) := by
    funext i
    rw [← incM_map_cA]
    exact RingHom.map_mulVec (cA σ).toRingHom (incM F ι) w i
  rw [hA, hA, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, show (incM F ι)ᵀ = incM F ιᵀ from rfl, ← incM_mul, ← incM_mul, hg]

/- English proof (translation)
Establish `hb : (fun l => cA σ ((Pi.single j 1 : Fin k → AE F E) l)) = Pi.single j 1`. Use function extensionality and compare the values at `l`. Distinguish the cases in `h : l = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, h]`. Rewrite using `[hA, hb, Matrix.mulVec_single_one]`. Simplify using `[Matrix.vecMul, dotProduct, Matrix.col]`.
-/
theorem hA_single (σ : E →ₐ[F] E) {k : ℕ} (J₁ : Matrix (Fin k) (Fin k) E) (a : Fin k → AE F E) (j : Fin k) :
    hA σ J₁ a (Pi.single j 1) = Matrix.vecMul a (incM F J₁) j := by
  have hb : (fun l => cA σ ((Pi.single j 1 : Fin k → AE F E) l)) = Pi.single j 1 := by
    funext l; by_cases h : l = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hA, hb, Matrix.mulVec_single_one]
  simp [Matrix.vecMul, dotProduct, Matrix.col]

/- English proof (translation)
Rewrite using `[← incM_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_mul_inv {k : ℕ} (J₁ : Matrix (Fin k) (Fin k) E) (hd : J₁.det ≠ 0) :
    incM F J₁ * incM F J₁⁻¹ = 1 := by
  rw [← incM_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LeviModulus.HCoord

namespace GlobalTheory.LeviModulus.HCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n n₁ : ℕ} {X : Spc F E n} {H : Plane E n n₁}

def elt (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (X.J j i) = X.J i j)
    (hxx : hA σ X.J (incV F H.x) (incV F H.x) = 0) (hιx : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0)
    (a : Fin n₁ → AE F E) (c : AE F E) (hc : c + cA σ c = -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) :
    unip σ X H :=
  ⟨⟨⟨hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c,
     hmat σ X.J (incV F H.x) (-(incM F H.ι *ᵥ a)) (-c - hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)),
     by rw [hmat_mul hσ hJ _ _ _ _ _ hxx (hιx a) (by rw [hA_neg_l, hιx a, neg_zero]), add_neg_cancel, hA_neg_l,
          show c + (-c - hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) -
            -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) = 0 by ring, hmat_zero],
     by rw [hmat_mul hσ hJ _ _ _ _ _ hxx (by rw [hA_neg_l, hιx a, neg_zero]) (hιx a), neg_add_cancel, hA_neg_r,
          show -c - hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) + c -
            -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) = 0 by ring, hmat_zero]⟩,
    hmat_unitary hσ hJ _ _ c hxx (hιx a) hc⟩,
   Subgroup.subset_closure ⟨by
      show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ incV F H.x = incV F H.x
      rw [hmat_mulVec, hxx, hA_herm σ X.J hσ hJ, hιx a, map_zero]; simp,
    fun z => ⟨-hA σ X.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ a), by
      show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ (incM F H.ι *ᵥ z) = _
      rw [hmat_mulVec, hιx z]; simp [sub_eq_add_neg]⟩⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_elt (hσ hJ hxx hιx) (a : Fin n₁ → AE F E) (c : AE F E) (hc) :
    mat ((elt (X := X) (H := H) hσ hJ hxx hιx a c hc : unip σ X H) : UA σ X.J) =
      hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Subtype.ext (Units.ext e))`.
-/
theorem unip_ext' {g g' : unip σ X H} (e : mat (g : UA σ X.J) = mat (g' : UA σ X.J)) : g = g' :=
  Subtype.ext (Subtype.ext (Units.ext e))

variable (σ X H) in

def rv (M : Matrix (Fin n) (Fin n) (AE F E)) : Fin n₁ → AE F E :=
  fun j => hA σ X.J (M *ᵥ incV F H.y - incV F H.y) (incM F H.ι *ᵥ Pi.single j 1)

/- English proof (translation)
Use `haveI := (topAE F E).1`. Unfold `hA`. Conclude with `hv.dotProduct (continuous_const.matrix_mulVec (continuous_pi fun i => (continuous_cA σ).comp ((continuous_apply i).comp hw)))`.
-/
theorem continuous_hA (J : Matrix (Fin n) (Fin n) E) {Y : Type} [TopologicalSpace Y] {v w : Y → Fin n → AE F E}
    (hv : Continuous v) (hw : Continuous w) : Continuous fun p => hA σ J (v p) (w p) := by
  haveI := (topAE F E).1
  unfold hA
  exact hv.dotProduct (continuous_const.matrix_mulVec
    (continuous_pi fun i => (continuous_cA σ).comp ((continuous_apply i).comp hw)))

/- English proof (translation)
Use `haveI := (topAE F E).1`. Unfold `hmat`. Use `(continuous_const.add ?_).sub ?_` and prove the remaining obligations. Conclude with `(hu.add (hc.smul continuous_const)).matrix_vecMulVec continuous_const`. Conclude with `continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec (continuous_pi fun i => (continuous_cA σ).comp ((continuous_apply i).comp hu)))`.
-/
theorem continuous_hmat (J : Matrix (Fin n) (Fin n) E) (x : Fin n → AE F E) {Y : Type}
    [TopologicalSpace Y] {u : Y → Fin n → AE F E} {c : Y → AE F E} (hu : Continuous u) (hc : Continuous c) :
    Continuous fun p => hmat σ J x (u p) (c p) := by
  haveI := (topAE F E).1
  unfold hmat
  refine (continuous_const.add ?_).sub ?_
  · exact (hu.add (hc.smul continuous_const)).matrix_vecMulVec continuous_const
  · exact continuous_const.matrix_vecMulVec
      (continuous_const.matrix_mulVec (continuous_pi fun i => (continuous_cA σ).comp ((continuous_apply i).comp hu)))

/- English proof (translation)
Use `haveI := (topAE F E).1`. Use `continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const`.
-/
theorem continuous_rv : Continuous (rv σ X H) := by
  haveI := (topAE F E).1
  refine continuous_pi fun j => ?_
  exact continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const

end GlobalTheory.LeviModulus.HCoord

namespace GlobalTheory.LeviModulus.HCoord

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH`. Use `haveI := (topAE F E).1`. Establish `hσ : ∀ a, σ (σ a) = a` using `cm_conj_conj hB.cm`. Establish `hJ` using `hX.herm`. Establish `hd : X₁.J.det ≠ 0` using `det_ne_of_sig_c B X₁.J hX₁.sig`.

Establish `hdec : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (X.L : Set (Fin n → E))`. Rewrite using `[hX.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, t, u, -, -, -, hz⟩` from `hH.split z hz`. Conclude with `⟨s, t, u, hz⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨s, t, u, rfl⟩` from `hy`. Take `⟨s', t', u', rfl⟩` from `hz`. Conclude with `⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩`. Consider the case `smul a y _ hy`.

Take `⟨s, t, u, rfl⟩` from `hy`. Conclude with `⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩`. Establish `hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0` using `by rw [hA_incV', hH.xx, map_zero]`. Establish `hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1` using `by rw [hA_incV', hH.xy, map_one]`. Establish `hYX : hA σ X.J (incV F H.y) (incV F H.x) = 1` using `by rw [hA_herm σ X.J hσ hJ, hXY, map_one]`.

Establish `hιX : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0` using `hA_ι_incV σ X.J H.ι H.x (fun u => (hH.orth u).1)`. Establish `hιY : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0` using `hA_ι_incV σ X.J H.ι H.y (fun u => (hH.orth u).2)`. Establish `hXι : ∀ z, hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0` using `fun z => by`. Rewrite using `[hA_herm σ X.J hσ hJ, hιX, map_zero]`. Establish `hYι : ∀ z, hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0` using `fun z => by`.

Rewrite using `[hA_herm σ X.J hσ hJ, hιY, map_zero]`. Establish `hιι : ∀ a w, hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ w) = hA σ X₁.J a w` using `hA_ιι σ X.J X₁.J H.ι hH.gram`. Establish `hself : ∀ v, cA σ (hA σ X.J v v) = hA σ X.J v v` using `fun v => (hA_herm σ X.J hσ hJ v v).symm`. Use `set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def`. Establish `hhalf : (2 : AE F E) * half = 1`.

Rewrite using `[hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]`. Establish `hσhalf : cA σ half = half` using `by rw [hhalf_def, cA_inclR', map_inv₀, map_ofNat]`. Establish `hcf : ∀ (a : Fin n₁ → AE F E) (k : imA σ), ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) + cA σ ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) = -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)`. Introduce `a k`. Establish `hk : cA σ (k : AE F E) = -k` using `k.2`.

Rewrite using `[map_sub, map_mul, hk, hσhalf, hself]`. Take the linear combination `(-hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * hhalf`. Set `Ψf : (Fin n₁ → AE F E) × imA σ → unip σ X H` to `fun p => elt hσ hJ hXX hιX p.1 _ (hcf p.1 p.2)`. Establish `hmatΨ : ∀ p, mat ((Ψf p : unip σ X H) : UA σ X.J) = hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ p.1) ((p.2 : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1))` using `fun p => rfl`. Set `A : Matrix (Fin n) (Fin n) (AE F E) → Fin n₁ → AE F E` to `fun M => Matrix.vecMul (rv σ X H M) (incM F X₁.J⁻¹)`.

Set `K : Matrix (Fin n) (Fin n) (AE F E) → AE F E` to `fun M => hA σ X.J (M *ᵥ incV F H.y - incV F H.y) (incV F H.y) + half * hA σ X.J (incM F H.ι *ᵥ A M) (incM F H.ι *ᵥ A M)`. Establish `hdy : ∀ a c, hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ incV F H.y - incV F H.y = incM F H.ι *ᵥ a + c • incV F H.x`. Introduce `a c`. Rewrite using `[hmat_mulVec, hYX, hYι, one_smul, zero_smul, sub_zero, add_sub_cancel_left]`. Establish `hA_h : ∀ a c, A (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = a`.

Introduce `a c`. Establish `e : rv σ X H (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = Matrix.vecMul a (incM F X₁.J)`. Use function extensionality and compare the values at `j`. Simplify using `only [rv]`. Rewrite using `[hdy, hA_add_l, hA_smul_l, hXι, mul_zero, add_zero, hιι, hA_single]`.

Simplify using `only [A]`. Rewrite using `[e, Matrix.vecMul_vecMul, incM_mul_inv _ hd, Matrix.vecMul_one]`. Establish `hK_h : ∀ a c, K (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = c + half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)`. Introduce `a c`. Simplify using `only [K]`.

Rewrite using `[hA_h, hdy, hA_add_l, hA_smul_l, hιY, hXY, mul_one, zero_add]`. Establish `hmemK : ∀ g : unip σ X H, K (mat (g : UA σ X.J)) ∈ imA σ`. Introduce `g`. Take `⟨b, c, hc, hg⟩` from `unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2`. Rewrite using `[hg, hK_h, mem_imA, map_add, map_mul, hσhalf, hself]`.

Take the linear combination `hc + hA σ X.J (incM F H.ι *ᵥ b) (incM F H.ι *ᵥ b) * hhalf`. Set `invf : unip σ X H → (Fin n₁ → AE F E) × imA σ` to `fun g => (A (mat (g : UA σ X.J)), ⟨K (mat (g : UA σ X.J)), hmemK g⟩)`. Establish `hmc : Continuous fun g : unip σ X H => mat (g : UA σ X.J)` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Establish `hAc : Continuous A` using `continuous_rv.matrix_vecMul continuous_const`. Establish `hKc : Continuous K` using `(continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const).add (continuous_const.mul (continuous_hA X.J (continuous_const.matrix_mulVec hAc) (continuous_const.matrix_mulVec hAc)))`.

Establish `hQc : Continuous fun p : (Fin n₁ → AE F E) × imA σ => hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1)` using `continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_fst)`. Set `Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H` to `{ toFun := Ψf invFun := invf left_inv := fun p => by`. Use `Prod.ext (hA_h _ _) (Subtype.ext ?_)` and prove the remaining obligations. Use `show K (mat ((Ψf p : unip σ X H) : UA σ X.J)) = p.2`. Rewrite using `[hmatΨ, hK_h]`.

Expand and normalize the polynomial expressions, which then agree. Use `right_inv := fun g => by`. Apply `unip_ext'` to reduce the goal to its premises. Take `⟨b, c, hc, hg⟩` from `unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2`. Rewrite using `[hmatΨ]`.

Use `show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ A (mat (g : UA σ X.J))) (K (mat (g : UA σ X.J)) - half * hA σ X.J (incM F H.ι *ᵥ A (mat (g : UA σ X.J))) (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))) = mat (g : UA σ X.J)`. Rewrite using `[hg, hK_h, hA_h, add_sub_cancel_right]`. Use `continuous_toFun := by`. Use `Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _` and prove the remaining obligations. Conclude with `continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst) ((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc))`.

Conclude with `continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst).neg (((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc)).neg.sub hQc)`. Use `continuous_invFun := by`. Use `Continuous.prodMk (hAc.comp hmc) (Continuous.subtype_mk (hKc.comp hmc) _) }` and prove the remaining obligations. Establish `hωmem : ∀ a a' : Fin n₁ → AE F E, half * (hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a') - hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) ∈ imA σ`. Introduce `a a'`.

Rewrite using `[mem_imA, map_mul, map_sub, hσhalf, ← hA_herm σ X.J hσ hJ, ← hA_herm σ X.J hσ hJ]`. Expand and normalize the polynomial expressions, which then agree. Set `ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ` to `fun a a' => ⟨_, hωmem a a'⟩`. Use `⟨Ψ, ω, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (continuous_const.mul ((continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_snd)).sub (continuous_hA X.J (continuous_const.matrix_mulVec continuous_snd) (continuous_const.matrix_mulVec continuous_fst)) …`.

Introduce `a b a' b'`. Apply `unip_ext'` to reduce the goal to its premises. Use `show mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) * mat ((Ψf (a', b') : unip σ X H) : UA σ X.J) = mat ((Ψf (a + a', b + b' + ω a a') : unip σ X H) : UA σ X.J)`. Rewrite using `[hmatΨ, hmatΨ, hmatΨ, hmat_mul hσ hJ _ _ _ _ _ hXX (hιX a) (hιX a'), ← Matrix.mulVec_add]`. Use `congr 1`.

Simplify using `only [AddSubgroup.coe_add, ω, Matrix.mulVec_add, hA_add_l, hA_add_r]`. Take the linear combination `(hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) * hhalf`. Introduce `l g₀ m hL a b`. Establish `hpmem : l.1 * cA σ l.1 * (b : AE F E) ∈ imA σ`. Establish `hb : cA σ (b : AE F E) = -b` using `b.2`.

Rewrite using `[mem_imA, map_mul, map_mul, cA_cA σ hσ, hb]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩), ?_, rfl, rfl⟩` and prove the remaining obligations. Use `set M := mat m with hM`. Establish `hMx : M *ᵥ incV F H.x = l.1 • incV F H.x` using `hL.1`.

Establish `hMι : ∀ w, M *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g₀ *ᵥ w)` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, hL.2.2, ← Matrix.mulVec_mulVec]`. Establish `hx' : M *ᵥ ((l⁻¹).1 • incV F H.x) = incV F H.x`. Rewrite using `[Matrix.mulVec_smul, hMx, smul_smul, Units.inv_mul, one_smul]`. Establish `hMvx : ∀ v, hA σ X.J (M *ᵥ v) (incV F H.x) = cA σ (l⁻¹).1 * hA σ X.J v (incV F H.x)` using `fun v => by`.

Establish `e` using `hA_mat m v ((l⁻¹).1 • incV F H.x)`. Rewrite `e` using `[← hM, hx', hA_smul_r]`. Conclude with `e`. Establish `hιp : incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a)) = cA σ l.1 • (M *ᵥ (incM F H.ι *ᵥ a))`. Rewrite using `[Matrix.mulVec_smul, hMι]`.

Establish `hMvu : ∀ v, hA σ X.J (M *ᵥ v) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) = l.1 * hA σ X.J v (incM F H.ι *ᵥ a)` using `fun v => by`. Rewrite using `[hιp, hA_smul_r, cA_cA σ hσ, hM, hA_mat]`. Establish `hQp : hA σ X.J (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) = cA σ l.1 * l.1 * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)`. Rewrite using `[hιp, hA_smul_l, hA_smul_r, cA_cA σ hσ, hM, hA_mat]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinv : cA σ (l⁻¹).1 * cA σ l.1 = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`. Establish `hMMi : M * mat m⁻¹ = 1`. Rewrite using `[hM, show mat m * mat m⁻¹ = mat (m * m⁻¹) from rfl, mul_inv_cancel]`. Both sides reduce to the same expression. Use `set T := mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) with hT`.

Use `set T' := mat ((Ψf (cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩) : unip σ X H) : UA σ X.J) with hT'`. Establish `key : M * T = T' * M`. Use `hmat_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT, hT', hmatΨ, hmatΨ, hmat_mulVec, hmat_mulVec, hMvx, hMvu, hQp]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hMx, hMι, hιp]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(-(hA σ X.J v (incV F H.x) * (incM F H.ι *ᵥ (mat g₀ *ᵥ a)) i + hA σ X.J v (incV F H.x) * incV F H.x i * ((b : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * l.1)) * hinv`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `show M * T * mat m⁻¹ = T'`. Rewrite using `[key, Matrix.mul_assoc, hMMi, Matrix.mul_one]`.
-/
theorem heis_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∃ (Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H) (ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ),
      Continuous (fun p : (Fin n₁ → AE F E) × (Fin n₁ → AE F E) => ω p.1 p.2) ∧
      (∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a')) ∧
      ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi H l g₀ m → ∀ a b,
        ∃ p : (Fin n₁ → AE F E) × imA σ, m * ((Ψ (a, b) : unip σ X H) : UA σ X.J) * m⁻¹ = ((Ψ p : unip σ X H) : UA σ X.J) ∧
          p.1 = cA σ l • (mat g₀ *ᵥ a) ∧ ((p.2 : imA σ) : AE F E) = l * cA σ l * b := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH
  haveI := (topAE F E).1
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hJ := hX.herm
  have hd : X₁.J.det ≠ 0 := det_ne_of_sig_c B X₁.J hX₁.sig
  have hdec : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
      rw [hX.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV', hH.xx, map_zero]
  have hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV', hH.xy, map_one]
  have hYX : hA σ X.J (incV F H.y) (incV F H.x) = 1 := by rw [hA_herm σ X.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 :=
    hA_ι_incV σ X.J H.ι H.x (fun u => (hH.orth u).1)
  have hιY : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 :=
    hA_ι_incV σ X.J H.ι H.y (fun u => (hH.orth u).2)
  have hXι : ∀ z, hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιX, map_zero]
  have hYι : ∀ z, hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιY, map_zero]
  have hιι : ∀ a w, hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ w) = hA σ X₁.J a w :=
    hA_ιι σ X.J X₁.J H.ι hH.gram
  have hself : ∀ v, cA σ (hA σ X.J v v) = hA σ X.J v v := fun v => (hA_herm σ X.J hσ hJ v v).symm
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR', map_inv₀, map_ofNat]
  have hcf : ∀ (a : Fin n₁ → AE F E) (k : imA σ),
      ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) +
        cA σ ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) =
        -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
    intro a k
    have hk : cA σ (k : AE F E) = -k := k.2
    rw [map_sub, map_mul, hk, hσhalf, hself]
    linear_combination (-hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * hhalf

  let Ψf : (Fin n₁ → AE F E) × imA σ → unip σ X H := fun p => elt hσ hJ hXX hιX p.1 _ (hcf p.1 p.2)
  have hmatΨ : ∀ p, mat ((Ψf p : unip σ X H) : UA σ X.J) = hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ p.1)
      ((p.2 : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1)) := fun p => rfl
  let A : Matrix (Fin n) (Fin n) (AE F E) → Fin n₁ → AE F E := fun M => Matrix.vecMul (rv σ X H M) (incM F X₁.J⁻¹)
  let K : Matrix (Fin n) (Fin n) (AE F E) → AE F E := fun M =>
    hA σ X.J (M *ᵥ incV F H.y - incV F H.y) (incV F H.y) + half * hA σ X.J (incM F H.ι *ᵥ A M) (incM F H.ι *ᵥ A M)
  have hdy : ∀ a c, hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ incV F H.y - incV F H.y =
      incM F H.ι *ᵥ a + c • incV F H.x := by
    intro a c; rw [hmat_mulVec, hYX, hYι, one_smul, zero_smul, sub_zero, add_sub_cancel_left]
  have hA_h : ∀ a c, A (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = a := by
    intro a c
    have e : rv σ X H (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = Matrix.vecMul a (incM F X₁.J) := by
      funext j; simp only [rv]; rw [hdy, hA_add_l, hA_smul_l, hXι, mul_zero, add_zero, hιι, hA_single]
    simp only [A]; rw [e, Matrix.vecMul_vecMul, incM_mul_inv _ hd, Matrix.vecMul_one]
  have hK_h : ∀ a c, K (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) =
      c + half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
    intro a c; simp only [K]; rw [hA_h, hdy, hA_add_l, hA_smul_l, hιY, hXY, mul_one, zero_add]
  have hmemK : ∀ g : unip σ X H, K (mat (g : UA σ X.J)) ∈ imA σ := by
    intro g
    obtain ⟨b, c, hc, hg⟩ := unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2
    rw [hg, hK_h, mem_imA, map_add, map_mul, hσhalf, hself]
    linear_combination hc + hA σ X.J (incM F H.ι *ᵥ b) (incM F H.ι *ᵥ b) * hhalf
  let invf : unip σ X H → (Fin n₁ → AE F E) × imA σ := fun g =>
    (A (mat (g : UA σ X.J)), ⟨K (mat (g : UA σ X.J)), hmemK g⟩)
  have hmc : Continuous fun g : unip σ X H => mat (g : UA σ X.J) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hAc : Continuous A := continuous_rv.matrix_vecMul continuous_const
  have hKc : Continuous K :=
    (continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const).add
      (continuous_const.mul (continuous_hA X.J (continuous_const.matrix_mulVec hAc)
        (continuous_const.matrix_mulVec hAc)))
  have hQc : Continuous fun p : (Fin n₁ → AE F E) × imA σ =>
      hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1) :=
    continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_fst)
  let Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H :=
    { toFun := Ψf
      invFun := invf
      left_inv := fun p => by
        refine Prod.ext (hA_h _ _) (Subtype.ext ?_)
        show K (mat ((Ψf p : unip σ X H) : UA σ X.J)) = p.2
        rw [hmatΨ, hK_h]; ring
      right_inv := fun g => by
        apply unip_ext'
        obtain ⟨b, c, hc, hg⟩ := unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2
        rw [hmatΨ]
        show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))
          (K (mat (g : UA σ X.J)) - half * hA σ X.J (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))
            (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))) = mat (g : UA σ X.J)
        rw [hg, hK_h, hA_h, add_sub_cancel_right]
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _
        · exact continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst)
            ((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc))
        · exact continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst).neg
            (((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc)).neg.sub hQc)
      continuous_invFun := by
        refine Continuous.prodMk (hAc.comp hmc) (Continuous.subtype_mk (hKc.comp hmc) _) }

  have hωmem : ∀ a a' : Fin n₁ → AE F E, half * (hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a') -
      hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) ∈ imA σ := by
    intro a a'
    rw [mem_imA, map_mul, map_sub, hσhalf, ← hA_herm σ X.J hσ hJ, ← hA_herm σ X.J hσ hJ]
    ring
  let ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ := fun a a' => ⟨_, hωmem a a'⟩
  refine ⟨Ψ, ω, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_const.mul
      ((continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst)
        (continuous_const.matrix_mulVec continuous_snd)).sub
      (continuous_hA X.J (continuous_const.matrix_mulVec continuous_snd)
        (continuous_const.matrix_mulVec continuous_fst)))) _
  · intro a b a' b'
    apply unip_ext'
    show mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) * mat ((Ψf (a', b') : unip σ X H) : UA σ X.J) =
      mat ((Ψf (a + a', b + b' + ω a a') : unip σ X H) : UA σ X.J)
    rw [hmatΨ, hmatΨ, hmatΨ, hmat_mul hσ hJ _ _ _ _ _ hXX (hιX a) (hιX a'), ← Matrix.mulVec_add]
    congr 1
    simp only [AddSubgroup.coe_add, ω, Matrix.mulVec_add, hA_add_l, hA_add_r]
    linear_combination (hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) * hhalf
  · intro l g₀ m hL a b
    have hpmem : l.1 * cA σ l.1 * (b : AE F E) ∈ imA σ := by
      have hb : cA σ (b : AE F E) = -b := b.2
      rw [mem_imA, map_mul, map_mul, cA_cA σ hσ, hb]; ring
    refine ⟨(cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩), ?_, rfl, rfl⟩
    set M := mat m with hM
    have hMx : M *ᵥ incV F H.x = l.1 • incV F H.x := hL.1
    have hMι : ∀ w, M *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g₀ *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hL.2.2, ← Matrix.mulVec_mulVec]
    have hx' : M *ᵥ ((l⁻¹).1 • incV F H.x) = incV F H.x := by
      rw [Matrix.mulVec_smul, hMx, smul_smul, Units.inv_mul, one_smul]
    have hMvx : ∀ v, hA σ X.J (M *ᵥ v) (incV F H.x) = cA σ (l⁻¹).1 * hA σ X.J v (incV F H.x) := fun v => by
      have e := hA_mat m v ((l⁻¹).1 • incV F H.x)
      rw [← hM, hx', hA_smul_r] at e
      exact e
    have hιp : incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a)) = cA σ l.1 • (M *ᵥ (incM F H.ι *ᵥ a)) := by
      rw [Matrix.mulVec_smul, hMι]
    have hMvu : ∀ v, hA σ X.J (M *ᵥ v) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) =
        l.1 * hA σ X.J v (incM F H.ι *ᵥ a) := fun v => by
      rw [hιp, hA_smul_r, cA_cA σ hσ, hM, hA_mat]
    have hQp : hA σ X.J (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) =
        cA σ l.1 * l.1 * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
      rw [hιp, hA_smul_l, hA_smul_r, cA_cA σ hσ, hM, hA_mat]; ring
    have hinv : cA σ (l⁻¹).1 * cA σ l.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hMMi : M * mat m⁻¹ = 1 := by
      rw [hM, show mat m * mat m⁻¹ = mat (m * m⁻¹) from rfl, mul_inv_cancel]; rfl
    set T := mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) with hT
    set T' := mat ((Ψf (cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩) : unip σ X H) : UA σ X.J) with hT'
    have key : M * T = T' * M := by
      refine hmat_ext fun v => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT, hT', hmatΨ, hmatΨ, hmat_mulVec, hmat_mulVec,
        hMvx, hMvu, hQp]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hMx, hMι, hιp]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(hA σ X.J v (incV F H.x) * (incM F H.ι *ᵥ (mat g₀ *ᵥ a)) i +
        hA σ X.J v (incV F H.x) * incV F H.x i * ((b : AE F E) -
          half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * l.1)) * hinv
    apply Subtype.ext; apply Units.ext
    show M * T * mat m⁻¹ = T'
    rw [key, Matrix.mul_assoc, hMMi, Matrix.mul_one]

end GlobalTheory.LeviModulus.HCoord
