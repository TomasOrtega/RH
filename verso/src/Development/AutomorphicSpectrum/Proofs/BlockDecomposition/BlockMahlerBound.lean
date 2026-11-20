import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
import GroundTheory.AutomorphicForms.ReductionMahler

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open GroundTheory.Automorphic GroundTheory.Global

namespace GlobalTheory.CompanionTheory.MahlerAdelic

section Places

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]`. Both sides reduce to the same expression.
-/
theorem norm_cV (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
  rfl

/- English proof (translation)
Simplify using `[InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v)]`.
-/
theorem mult_eq_two (v : InfinitePlace E) : v.mult = 2 := by
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v)]

/- English proof (translation)
Rewrite using `[finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset) (by simp), finsum_eq_sum_of_support_subset (s := hf.toFinset) _ ?_]`. Conclude with `Real.log_prod (fun i _ => h0 i)`. Introduce `i hi`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_mulSupport]`. Introduce `h1`.

Simplify using `[h1] at hi`.
-/
theorem log_finprod {ι : Type*} {f : ι → ℝ} (hf : (Function.mulSupport f).Finite) (h0 : ∀ i, f i ≠ 0) :
    Real.log (∏ᶠ i, f i) = ∑ᶠ i, Real.log (f i) := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset) (by simp),
    finsum_eq_sum_of_support_subset (s := hf.toFinset) _ ?_]
  · exact Real.log_prod (fun i _ => h0 i)
  · intro i hi
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    simp [h1] at hi

/- English proof (translation)
Establish `hinf : ∀ v : InfinitePlace E, ‖(s : Ad E).1 v‖ ≠ 0` using `fun v => by`. Rewrite using `[← norm_cV]`. Conclude with `norm_ne_zero_iff.2 ((s.isUnit.map (cV v)).ne_zero)`. Establish `hfin : ∀ w : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 w‖ ≠ 0` using `fun w => norm_ne_zero_iff.2 ((s.isUnit.map (cW w)).ne_zero)`. Rewrite using `[IdeleGroup.ideleModule_eq, Real.log_mul (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hinf v)) (by`.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := (IdeleGroup.finite_mulSupport_norm s).toFinset) (by simp)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun w _ => hfin w),`. Use the proof step `Real.log_prod (fun v _ => pow_ne_zero _ (hinf v)), log_finprod (IdeleGroup.finite_mulSupport_norm s) hfin]`. Simplify using `only [logAbs, norm_cV, mult_eq_two]`. Both sides reduce to the same expression.
-/
theorem logAbs_eq (s : (Ad E)ˣ) : logAbs (s : Ad E) = Real.log (IdeleGroup.ideleModule E s) := by
  have hinf : ∀ v : InfinitePlace E, ‖(s : Ad E).1 v‖ ≠ 0 := fun v => by
    rw [← norm_cV]
    exact norm_ne_zero_iff.2 ((s.isUnit.map (cV v)).ne_zero)
  have hfin : ∀ w : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 ((s.isUnit.map (cW w)).ne_zero)
  rw [IdeleGroup.ideleModule_eq, Real.log_mul (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hinf v))
      (by
        rw [finprod_eq_prod_of_mulSupport_subset _ (s := (IdeleGroup.finite_mulSupport_norm s).toFinset) (by simp)]
        exact Finset.prod_ne_zero_iff.2 fun w _ => hfin w),
    Real.log_prod (fun v _ => pow_ne_zero _ (hinf v)), log_finprod (IdeleGroup.finite_mulSupport_norm s) hfin]
  simp only [logAbs, norm_cV, mult_eq_two]
  rfl

end Places

section Theta

variable {A : Type} [CommRing A] {n : ℕ}

abbrev tinv (A : Type) [CommRing A] (n : ℕ) : Monoid.End (GL (Fin n) A) := thetaR (RingHom.id A) n

/- English proof (translation)
Rewrite using `[thetaR_val]`. Both sides reduce to the same expression.
-/
theorem tinv_val (g : GL (Fin n) A) : (tinv A n g).val = ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ := by
  rw [thetaR_val]
  rfl

/- English proof (translation)
The claim follows from `(map_inv (tinv A n) g).symm`.
-/
theorem tinv_inv (g : GL (Fin n) A) : (tinv A n g)⁻¹ = tinv A n g⁻¹ := (map_inv (tinv A n) g).symm

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[tinv_val, tinv_inv, tinv_val, inv_inv, Matrix.transpose_transpose]`.
-/
theorem tinv_tinv (g : GL (Fin n) A) : tinv A n (tinv A n g) = g := by
  refine Units.ext ?_
  rw [tinv_val, tinv_inv, tinv_val, inv_inv, Matrix.transpose_transpose]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: (Units.val ∘ (tinv A n)) = fun g : GL (Fin n) A => ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ` using `funext tinv_val`. Rewrite using `[this]`. Conclude with `Units.continuous_coe_inv.matrix_transpose`. Establish `: (fun g : GL (Fin n) A => (((tinv A n g)⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) = fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A)ᵀ`.

Use function extensionality and compare the values at `g`. Rewrite using `[tinv_inv, tinv_val, inv_inv]`. Express the relevant statement in the definitionally equal form `Continuous (fun g : GL (Fin n) A => (((tinv A n g)⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))`. Rewrite using `[this]`. Conclude with `Units.continuous_val.matrix_transpose`.
-/
theorem continuous_tinv [TopologicalSpace A] [IsTopologicalRing A] : Continuous (tinv A n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ (tinv A n)) = fun g : GL (Fin n) A =>
        ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ := funext tinv_val
    rw [this]
    exact Units.continuous_coe_inv.matrix_transpose
  · have : (fun g : GL (Fin n) A => (((tinv A n g)⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) =
        fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A)ᵀ := by
      funext g
      rw [tinv_inv, tinv_val, inv_inv]
    change Continuous (fun g : GL (Fin n) A => (((tinv A n g)⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    rw [this]
    exact Units.continuous_val.matrix_transpose

end Theta

section Deg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[tinv_val, ← map_inv]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(ratGL E n γ⁻¹).val j i = (ratGL E n (tinv E n γ)).val i j`. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) ((γ⁻¹).val j i) = algebraMap E (Ad E) ((tinv E n γ).val i j)`.

Rewrite using `[tinv_val]`. Both sides reduce to the same expression.
-/
theorem tinv_ratGL (γ : GL (Fin n) E) : tinv (Ad E) n (ratGL E n γ) = ratGL E n (tinv E n γ) := by
  refine Units.ext ?_
  rw [tinv_val, ← map_inv]
  ext i j
  change (ratGL E n γ⁻¹).val j i = (ratGL E n (tinv E n γ)).val i j
  change algebraMap E (Ad E) ((γ⁻¹).val j i) = algebraMap E (Ad E) ((tinv E n γ).val i j)
  rw [tinv_val]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of (GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF GlobalTheory.CompanionTheory.WedgeMinor.mulF) (GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI GlobalTheory.CompanionTheory.DetMonotone.detMono (GlobalTheory.Compani …`.
-/
theorem degBasisG : DegBasisG :=
  GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of
    (GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF GlobalTheory.CompanionTheory.WedgeMinor.mulF)
    (GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI GlobalTheory.CompanionTheory.DetMonotone.detMono
      (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono))
    GlobalTheory.CompanionTheory.WedgeMinor.mulF (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono)
    GlobalTheory.CompanionTheory.LogAbs.logAbsBasic
    (GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul GlobalTheory.CompanionTheory.WedgeMinor.mulF
      (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono) GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin)

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul GlobalTheory.CompanionTheory.WedgeMinor.mulF (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono) GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin`.
-/
theorem finSupp : FinSupp :=
  GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul GlobalTheory.CompanionTheory.WedgeMinor.mulF
               (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono) GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of GlobalTheory.CompanionTheory.WedgeMinor.mulF (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono) GlobalTheory.CompanionTheory.LogAbs.logAbsBasic finSupp`.
-/
theorem degAdelic : DegAdelic :=
  GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of GlobalTheory.CompanionTheory.WedgeMinor.mulF
    (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono) GlobalTheory.CompanionTheory.LogAbs.logAbsBasic finSupp

/- English proof (translation)
Establish `hfr : frame (1 : GA E n) (1 : Matrix (Fin n) (Fin n) E) = 1`. Simplify using `[frame, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h1 : ∀ v : InfinitePlace E, lognInf v (1 : Matrix (Fin n) (Fin n) (Ad E)) = 0` using `fun v => by`. Simplify using `[lognInf, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h2 : ∀ w : HeightOneSpectrum (𝓞 E), lognFin w (1 : Matrix (Fin n) (Fin n) (Ad E)) = 0` using `fun w => by`.

Use `(GlobalTheory.CompanionTheory.WedgeMinor.mulF (w.adicCompletion E) (Fin n) (Fin n) (Fin n) 1).2.2 1` as an intermediate fact. Express the relevant statement in the definitionally equal form `Real.log (nF ((1 : Matrix (Fin n) (Fin n) (Ad E)).map (cW w))) = 0`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), this]`. Simplify using the standard rewrite rules. Simplify using `[degM, hfr, h1, h2]`.
-/
theorem degM_one_one : degM (1 : GA E n) (1 : Matrix (Fin n) (Fin n) E) = 0 := by
  have hfr : frame (1 : GA E n) (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [frame, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ∀ v : InfinitePlace E, lognInf v (1 : Matrix (Fin n) (Fin n) (Ad E)) = 0 := fun v => by
    simp [lognInf, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ∀ w : HeightOneSpectrum (𝓞 E), lognFin w (1 : Matrix (Fin n) (Fin n) (Ad E)) = 0 := fun w => by
    have := (GlobalTheory.CompanionTheory.WedgeMinor.mulF (w.adicCompletion E) (Fin n) (Fin n) (Fin n) 1).2.2 1
    change Real.log (nF ((1 : Matrix (Fin n) (Fin n) (Ad E)).map (cW w))) = 0
    rw [Matrix.map_one _ (map_zero _) (map_one _), this]
    simp
  simp [degM, hfr, h1, h2]

/- English proof (translation)
Establish `hM : ((1 : Matrix (Fin n) (Fin n) E)ᵀ : Fin n → Fin n → E) = ⇑(Pi.basisFun E (Fin n))`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Pi.single_apply, eq_comm]`. Establish `hLI : LinearIndependent E (1 : Matrix (Fin n) (Fin n) E)ᵀ`. Rewrite using `[hM]`.

Conclude with `(Pi.basisFun E (Fin n)).linearIndependent`. Establish `hsp : Submodule.span E (Set.range (1 : Matrix (Fin n) (Fin n) E)ᵀ) = ⊤`. Rewrite using `[hM]`. Conclude with `(Pi.basisFun E (Fin n)).span_eq`. Establish `hb` using `degBasisG E n (Fin n) x 1 hLI`.

Rewrite `hb` using `[degG_eq, hsp]`. Establish `hA` using `degAdelic E n n 1 x x 1 hLI (by simp [Matrix.map_one _ (map_zero _) (map_one _)])`. Rewrite `hA` using `[mul_one, degM_one_one, zero_add]`. Rewrite using `[← hb, hA, ← logAbs_eq (AdelicGLn.det E n x)]`. Both sides reduce to the same expression.
-/
theorem deg_top (x : GA E n) : deg x ⊤ = Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E n x)) := by
  have hM : ((1 : Matrix (Fin n) (Fin n) E)ᵀ : Fin n → Fin n → E) = ⇑(Pi.basisFun E (Fin n)) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hLI : LinearIndependent E (1 : Matrix (Fin n) (Fin n) E)ᵀ := by
    rw [hM]
    exact (Pi.basisFun E (Fin n)).linearIndependent
  have hsp : Submodule.span E (Set.range (1 : Matrix (Fin n) (Fin n) E)ᵀ) = ⊤ := by
    rw [hM]
    exact (Pi.basisFun E (Fin n)).span_eq
  have hb := degBasisG E n (Fin n) x 1 hLI
  rw [degG_eq, hsp] at hb
  have hA := degAdelic E n n 1 x x 1 hLI (by simp [Matrix.map_one _ (map_zero _) (map_one _)])
  rw [mul_one, degM_one_one, zero_add] at hA
  rw [← hb, hA, ← logAbs_eq (AdelicGLn.det E n x)]
  rfl

def colM (m : Fin n → E) : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => m i

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem colM_transpose (m : Fin n → E) : ((colM m)ᵀ : Fin 1 → Fin n → E) = fun _ => m := by
  ext i j
  rfl

/- English proof (translation)
Rewrite using `[mult_eq_two, Reduction.euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `only [nI, Matrix.det_unique, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply]`. Simplify using `only [Complex.re_sum, Complex.star_def, Complex.conj_mul', Reduction.infComp, norm_cV]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `norm_cast`.
-/
theorem nI_col (v : InfinitePlace E) (z : Fin n → Ad E) :
    nI ((Matrix.of fun i (_ : Fin 1) => z i).map (cV v)) =
      Reduction.euclidNorm (Reduction.infComp v z) ^ v.mult := by
  rw [mult_eq_two, Reduction.euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [nI, Matrix.det_unique, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [Complex.re_sum, Complex.star_def, Complex.conj_mul', Reduction.infComp, norm_cV]
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_cast

/- English proof (translation)
Use `haveI : Nonempty (Fin 1 → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩`. Establish `hval : ∀ s : Fin 1 → Fin n, ‖(((Matrix.of fun i (_ : Fin 1) => z i).map (cW w)).submatrix s id).det‖ = ‖Reduction.finComp w z (s 0)‖` using `fun s => by`. Simplify using `only [Matrix.det_unique, Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Both sides reduce to the same expression. Use `le_antisymm (ciSup_le fun s => ?_) ?_` and prove the remaining obligations.

Rewrite using `[hval]`. Conclude with `norm_le_pi_norm _ _`. Use `(pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_` and prove the remaining obligations. Conclude with `Real.iSup_nonneg fun _ => norm_nonneg _`. Rewrite using `[← hval (fun _ => i)]`.

Conclude with `le_ciSup (f := fun s : Fin 1 → Fin n => ‖(((Matrix.of fun i (_ : Fin 1) => z i).map (cW w)).submatrix s id).det‖) (Set.finite_range _).bddAbove (fun _ => i)`.
-/
theorem nF_col (hn : 0 < n) (w : HeightOneSpectrum (𝓞 E)) (z : Fin n → Ad E) :
    nF ((Matrix.of fun i (_ : Fin 1) => z i).map (cW w)) = ‖Reduction.finComp w z‖ := by
  haveI : Nonempty (Fin 1 → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
  have hval : ∀ s : Fin 1 → Fin n,
      ‖(((Matrix.of fun i (_ : Fin 1) => z i).map (cW w)).submatrix s id).det‖ =
        ‖Reduction.finComp w z (s 0)‖ := fun s => by
    simp only [Matrix.det_unique, Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rfl
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · rw [hval]
    exact norm_le_pi_norm _ _
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_
    · exact Real.iSup_nonneg fun _ => norm_nonneg _
    · rw [← hval (fun _ => i)]
      exact le_ciSup (f := fun s : Fin 1 → Fin n =>
        ‖(((Matrix.of fun i (_ : Fin 1) => z i).map (cW w)).submatrix s id).det‖)
        (Set.finite_range _).bddAbove (fun _ => i)

/- English proof (translation)
Establish `hn : 0 < n`. Break down `Nat.eq_zero_or_pos n with rfl | h` into its components or cases. Conclude with `absurd (Subsingleton.elim _ _) hm`. Conclude with `h`. Establish `hLI : LinearIndependent E (colM m)ᵀ`.

Rewrite using `[colM_transpose]`. Conclude with `LinearIndependent.of_subsingleton 0 hm`. Establish `hb` using `degBasisG E n (Fin 1) x (colM m) hLI`. Establish `hsp : Submodule.span E (Set.range (colM m)ᵀ) = Submodule.span E {m}`. Rewrite using `[colM_transpose]`.

Simplify using the standard rewrite rules. Rewrite `hb` using `[degG_eq, hsp]`. Use `set z : Fin n → Ad E := fun i => frame x (colM m) i 0 with hz`. Establish `hfr : frame x (colM m) = Matrix.of fun i (_ : Fin 1) => z i`. Use extensionality with `i j`.

Rewrite using `[Subsingleton.elim j 0]`. Both sides reduce to the same expression. Establish `hzv : Reduction.ratVec m ᵥ* ((tinv (Ad E) n x : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) = z`. Use function extensionality and compare the values at `i`. Rewrite using `[tinv_val]`.

Simplify using `only [hz, frame, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Reduction.ratVec, colM, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Take `⟨L, hL⟩` from `GlobalTheory.CompanionTheory.DegAdelicProof.exists_leftInv (colM m) hLI`. Establish `hleft` using `GlobalTheory.CompanionTheory.DegAdelicProof.frame_leftInv x (colM m) L hL`. Take `⟨hI, hF, -⟩` from `finSupp E (Fin n) (Fin 1) (frame x (colM m)) _ hleft`.

Establish `hfc : Reduction.HasFiniteContent z`. Rewrite using `[← hzv]`. Conclude with `Reduction.hasFiniteContent_height _ hm`. Rewrite `hI`, `hF` using `[hfr]`. Establish `hinf : ∀ v : InfinitePlace E, Reduction.euclidNorm (Reduction.infComp v z) ^ v.mult ≠ 0` using `fun v => by`.

Rewrite using `[← nI_col]`. Conclude with `hI v`. Establish `hfin : ∀ w : HeightOneSpectrum (𝓞 E), ‖Reduction.finComp w z‖ ≠ 0` using `fun w => by`. Rewrite using `[← nF_col hn]`. Conclude with `hF w`.

Establish `hfs` using `hfc.finite_mulSupport`. Establish `hP` using `Finset.prod_ne_zero_iff.2 fun v (_ : v ∈ (Finset.univ : Finset (InfinitePlace E))) => hinf v`. Establish `hQ : ∏ᶠ w : HeightOneSpectrum (𝓞 E), ‖Reduction.finComp w z‖ ≠ 0`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := hfs.toFinset) (by simp)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun w _ => hfin w`.

Use `⟨lt_of_le_of_ne (Reduction.height_nonneg _ _) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Reduction.height, hzv, Reduction.adelicNorm]`. Conclude with `(mul_ne_zero hP hQ).symm`. Rewrite using `[← hb, Reduction.height, hzv, Reduction.adelicNorm, Real.log_mul hP hQ, Real.log_prod (fun v _ => hinf v), log_finprod hfs hfin, degM, hfr]`. Simplify using `only [lognInf, lognFin]`.

Use `congr 2`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← nI_col]`. Both sides reduce to the same expression. Use `finsum_congr fun w => ?_` and prove the remaining obligations.

Rewrite using `[← nF_col hn]`. Both sides reduce to the same expression.
-/
theorem deg_line (x : GA E n) {m : Fin n → E} (hm : m ≠ 0) :
    0 < Reduction.height (tinv (Ad E) n x) m ∧
      deg x (Submodule.span E {m}) = -Real.log (Reduction.height (tinv (Ad E) n x) m) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim _ _) hm
    · exact h
  have hLI : LinearIndependent E (colM m)ᵀ := by
    rw [colM_transpose]
    exact LinearIndependent.of_subsingleton 0 hm
  have hb := degBasisG E n (Fin 1) x (colM m) hLI
  have hsp : Submodule.span E (Set.range (colM m)ᵀ) = Submodule.span E {m} := by
    rw [colM_transpose]
    simp
  rw [degG_eq, hsp] at hb
  set z : Fin n → Ad E := fun i => frame x (colM m) i 0 with hz
  have hfr : frame x (colM m) = Matrix.of fun i (_ : Fin 1) => z i := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  have hzv : Reduction.ratVec m ᵥ* ((tinv (Ad E) n x : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) = z := by
    funext i
    rw [tinv_val]
    simp only [hz, frame, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Reduction.ratVec, colM, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨L, hL⟩ := GlobalTheory.CompanionTheory.DegAdelicProof.exists_leftInv (colM m) hLI
  have hleft := GlobalTheory.CompanionTheory.DegAdelicProof.frame_leftInv x (colM m) L hL
  obtain ⟨hI, hF, -⟩ := finSupp E (Fin n) (Fin 1) (frame x (colM m)) _ hleft
  have hfc : Reduction.HasFiniteContent z := by
    rw [← hzv]
    exact Reduction.hasFiniteContent_height _ hm
  rw [hfr] at hI hF
  have hinf : ∀ v : InfinitePlace E, Reduction.euclidNorm (Reduction.infComp v z) ^ v.mult ≠ 0 := fun v => by
    rw [← nI_col]
    exact hI v
  have hfin : ∀ w : HeightOneSpectrum (𝓞 E), ‖Reduction.finComp w z‖ ≠ 0 := fun w => by
    rw [← nF_col hn]
    exact hF w
  have hfs := hfc.finite_mulSupport
  have hP := Finset.prod_ne_zero_iff.2 fun v (_ : v ∈ (Finset.univ : Finset (InfinitePlace E))) => hinf v
  have hQ : ∏ᶠ w : HeightOneSpectrum (𝓞 E), ‖Reduction.finComp w z‖ ≠ 0 := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfs.toFinset) (by simp)]
    exact Finset.prod_ne_zero_iff.2 fun w _ => hfin w
  refine ⟨lt_of_le_of_ne (Reduction.height_nonneg _ _) ?_, ?_⟩
  · rw [Reduction.height, hzv, Reduction.adelicNorm]
    exact (mul_ne_zero hP hQ).symm
  rw [← hb, Reduction.height, hzv, Reduction.adelicNorm, Real.log_mul hP hQ,
    Real.log_prod (fun v _ => hinf v), log_finprod hfs hfin, degM, hfr]
  simp only [lognInf, lognFin]
  congr 2
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [← nI_col]
    rfl
  · refine finsum_congr fun w => ?_
    rw [← nF_col hn]
    rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]`. Both sides reduce to the same expression.
-/
theorem splitCentre_val (t : ℝ) : ((splitCentre E n t : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) =
    Matrix.scalar (Fin n) (GlobalTheory.CompanionTheory.SplitHomeo.expIdele E t : Ad E) := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  rfl

/- English proof (translation)
The claim follows from `Units.ext (by rw [Units.val_mul, Units.val_mul, splitCentre_val] exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)`.
-/
theorem splitCentre_comm (t : ℝ) (g : GA E n) : splitCentre E n t * g = g * splitCentre E n t :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, splitCentre_val]
    exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

/- English proof (translation)
Establish `hval : ((splitCentre E n t * y : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) = (GlobalTheory.CompanionTheory.SplitHomeo.expIdele E t : Ad E) • (y : Matrix (Fin n) (Fin n) (Ad E))`. Rewrite using `[Units.val_mul, splitCentre_val]`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_mul]`. Establish `h` using `Reduction.adelicNorm_smul (Reduction.hasFiniteContent_height y hm) (GlobalTheory.CompanionTheory.SplitHomeo.expIdele E t)`.

Rewrite `h` using `[GlobalTheory.CompanionTheory.SplitHomeo.ideleModule_expIdele]`. Rewrite using `[Reduction.height, hval, Matrix.vecMul_smul, h]`. Both sides reduce to the same expression.
-/
theorem height_splitCentre_mul (t : ℝ) (y : GA E n) {m : Fin n → E} (hm : m ≠ 0) :
    Reduction.height (splitCentre E n t * y) m =
      Real.exp (Module.finrank ℚ E * t) * Reduction.height y m := by
  have hval : ((splitCentre E n t * y : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) =
      (GlobalTheory.CompanionTheory.SplitHomeo.expIdele E t : Ad E) • (y : Matrix (Fin n) (Fin n) (Ad E)) := by
    rw [Units.val_mul, splitCentre_val]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
  have h := Reduction.adelicNorm_smul (Reduction.hasFiniteContent_height y hm) (GlobalTheory.CompanionTheory.SplitHomeo.expIdele E t)
  rw [GlobalTheory.CompanionTheory.SplitHomeo.ideleModule_expIdele] at h
  rw [Reduction.height, hval, Matrix.vecMul_smul, h]
  rfl

/- English proof (translation)
Establish `hd : AdelicGLn.det E n (tinv (Ad E) n x) = AdelicGLn.det E n x⁻¹` using `Units.ext (by`. Rewrite using `[AdelicGLn.coe_det, AdelicGLn.coe_det, tinv_val, Matrix.det_transpose])`. Establish `hm : (IdeleGroup.ideleModule E (AdelicGLn.det E n (tinv (Ad E) n x)) : ℝ) * IdeleGroup.ideleModule E (AdelicGLn.det E n x) = 1`. Rewrite using `[hd, ← Positive.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]`. Both sides reduce to the same expression.

Establish `h1` using `(IdeleGroup.ideleModule E (AdelicGLn.det E n (tinv (Ad E) n x))).2`. Establish `h2` using `(IdeleGroup.ideleModule E (AdelicGLn.det E n x)).2`. Use `congrArg Real.log hm` as an intermediate fact. Rewrite `this` using `[Real.log_mul h1.ne' h2.ne', Real.log_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_module_tinv (x : GA E n) :
    Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E n (tinv (Ad E) n x))) =
      -Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E n x)) := by
  have hd : AdelicGLn.det E n (tinv (Ad E) n x) = AdelicGLn.det E n x⁻¹ := Units.ext (by
    rw [AdelicGLn.coe_det, AdelicGLn.coe_det, tinv_val, Matrix.det_transpose])
  have hm : (IdeleGroup.ideleModule E (AdelicGLn.det E n (tinv (Ad E) n x)) : ℝ) *
      IdeleGroup.ideleModule E (AdelicGLn.det E n x) = 1 := by
    rw [hd, ← Positive.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    rfl
  have h1 := (IdeleGroup.ideleModule E (AdelicGLn.det E n (tinv (Ad E) n x))).2
  have h2 := (IdeleGroup.ideleModule E (AdelicGLn.det E n x)).2
  have := congrArg Real.log hm
  rw [Real.log_mul h1.ne' h2.ne', Real.log_one] at this
  linarith

end Deg

/- English proof (translation)
Introduce `E _ _ _ n c`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨{1}, isCompact_singleton, fun x _ _ => ⟨1, one_mem _, 1, rfl, Units.ext (Subsingleton.elim _ _)⟩⟩`. Establish `hd0 : (1 : ℝ) ≤ Module.finrank ℚ E` using `by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))`. Establish `hn0 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Take `⟨C₀, hC₀, hcov⟩` from `Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := n) (Real.exp_pos (-(Module.finrank ℚ E * |c|) - c))`. Establish `hS : IsCompact (splitCentre E n '' Set.Icc (-|c|) |c|)` using `isCompact_Icc.image GlobalTheory.CompanionTheory.SplitHomeo.continuous_splitCentre`. Establish `hC₁ : IsCompact ((fun p : GA E n × GA E n => p.1 * p.2) '' ((splitCentre E n '' Set.Icc (-|c|) |c|) ×ˢ C₀))` using `(hS.prod hC₀).image continuous_mul`. Use `⟨tinv (Ad E) n '' _, hC₁.image continuous_tinv, fun x hl ht => ?_⟩` and prove the remaining obligations. Use `set y : GA E n := tinv (Ad E) n x with hy`.

Use `set t : ℝ := GlobalTheory.CompanionTheory.SplitHomeo.splitDeg E n y with htdef`. Establish `hdeg : Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E n y)) = -deg x ⊤`. Rewrite using `[hy, log_module_tinv, deg_top]`. Establish `hnd : (1 : ℝ) ≤ n * Module.finrank ℚ E` using `by nlinarith`. Establish `htd : (n * Module.finrank ℚ E : ℝ) * t = -deg x ⊤`.

Rewrite using `[htdef, GlobalTheory.CompanionTheory.SplitHomeo.splitDeg, hdeg]`. Clear the denominators using the available nonvanishing facts. Establish `hab : |t| ≤ |c|`. Establish `h1 : (n * Module.finrank ℚ E : ℝ) * |t| = |deg x ⊤|`. Rewrite using `[← abs_neg (deg x ⊤), ← htd, abs_mul, abs_of_pos (by linarith : (0:ℝ) < n * Module.finrank ℚ E)]`.

Establish `h2 : |deg x ⊤| ≤ |c|` using `ht.trans (le_abs_self c)`. Use polynomial arithmetic with `[abs_nonneg t]`. Establish `hg` using `GlobalTheory.CompanionTheory.SplitHomeo.splitCentre_neg_mul_mem hn y`. Establish `hh : ∀ m : Fin n → E, m ≠ 0 → Real.exp (-(Module.finrank ℚ E * |c|) - c) ≤ Reduction.height (splitCentre E n (-t) * y) m`. Introduce `m hm`.

Rewrite using `[height_splitCentre_mul _ _ hm]`. Establish `hW : Module.finrank E (Submodule.span E {m}) = 1` using `finrank_span_singleton hm`. Take `⟨hpos, hdl⟩` from `deg_line x hm`. Establish `hl'` using `hl _ hW`. Rewrite `hl'` using `[hdl]`.

Establish `h3 : Real.exp (-c) ≤ Reduction.height y m`. Rewrite using `[← Real.exp_log hpos]`. Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `h4 : Real.exp (-(Module.finrank ℚ E * |c|)) ≤ Real.exp (Module.finrank ℚ E * -t)`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations.

Use `neg_abs_le t` as an intermediate fact. Use `le_abs_self t` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_eq_add_neg, Real.exp_add]`.

Use `_ ≤ _ := mul_le_mul h4 h3 (Real.exp_pos _).le (Real.exp_pos _).le`. Take `⟨_, ⟨γ, rfl⟩, k, hk, hgk⟩` from `hcov _ hg hh`. Establish `hyk : y = AdelicGLn.diagonal E n γ * (splitCentre E n t * k)`. Establish `h1` using `GlobalTheory.CompanionTheory.SplitHomeo.splitCentre_neg_mul_self (-t) y`. Rewrite `h1` using `[neg_neg]`.

Rewrite using `[← mul_assoc, ← splitCentre_comm, mul_assoc]`. Establish `hgk' : AdelicGLn.diagonal E n γ * k = splitCentre E n (-t) * y` using `hgk`. Express the relevant statement in the definitionally equal form `_ = splitCentre E n t * (AdelicGLn.diagonal E n γ * k)`. Rewrite using `[hgk', h1]`. Use `⟨tinv (Ad E) n (AdelicGLn.diagonal E n γ), ⟨tinv E n γ, (tinv_ratGL γ).symm⟩, tinv (Ad E) n (splitCentre E n t * k), ⟨_, ⟨(splitCentre E n t, k), ⟨⟨t, abs_le.1 hab, rfl⟩, hk⟩, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `tinv (Ad E) n (AdelicGLn.diagonal E n γ) * tinv (Ad E) n (splitCentre E n t * k) = x`. Rewrite using `[← map_mul, ← hyk, hy, tinv_tinv]`.
-/
theorem mahlerC : MahlerC := by
  intro E _ _ _ n c
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨{1}, isCompact_singleton, fun x _ _ => ⟨1, one_mem _, 1, rfl, Units.ext (Subsingleton.elim _ _)⟩⟩
  have hd0 : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨C₀, hC₀, hcov⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := n)
    (Real.exp_pos (-(Module.finrank ℚ E * |c|) - c))
  have hS : IsCompact (splitCentre E n '' Set.Icc (-|c|) |c|) :=
    isCompact_Icc.image GlobalTheory.CompanionTheory.SplitHomeo.continuous_splitCentre
  have hC₁ : IsCompact ((fun p : GA E n × GA E n => p.1 * p.2) '' ((splitCentre E n '' Set.Icc (-|c|) |c|) ×ˢ C₀)) :=
    (hS.prod hC₀).image continuous_mul
  refine ⟨tinv (Ad E) n '' _, hC₁.image continuous_tinv, fun x hl ht => ?_⟩
  set y : GA E n := tinv (Ad E) n x with hy
  set t : ℝ := GlobalTheory.CompanionTheory.SplitHomeo.splitDeg E n y with htdef
  have hdeg : Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E n y)) = -deg x ⊤ := by
    rw [hy, log_module_tinv, deg_top]
  have hnd : (1 : ℝ) ≤ n * Module.finrank ℚ E := by nlinarith
  have htd : (n * Module.finrank ℚ E : ℝ) * t = -deg x ⊤ := by
    rw [htdef, GlobalTheory.CompanionTheory.SplitHomeo.splitDeg, hdeg]
    field_simp
  have hab : |t| ≤ |c| := by
    have h1 : (n * Module.finrank ℚ E : ℝ) * |t| = |deg x ⊤| := by
      rw [← abs_neg (deg x ⊤), ← htd, abs_mul, abs_of_pos (by linarith : (0:ℝ) < n * Module.finrank ℚ E)]
    have h2 : |deg x ⊤| ≤ |c| := ht.trans (le_abs_self c)
    nlinarith [abs_nonneg t]
  have hg := GlobalTheory.CompanionTheory.SplitHomeo.splitCentre_neg_mul_mem hn y
  have hh : ∀ m : Fin n → E, m ≠ 0 → Real.exp (-(Module.finrank ℚ E * |c|) - c) ≤
      Reduction.height (splitCentre E n (-t) * y) m := by
    intro m hm
    rw [height_splitCentre_mul _ _ hm]
    have hW : Module.finrank E (Submodule.span E {m}) = 1 := finrank_span_singleton hm
    obtain ⟨hpos, hdl⟩ := deg_line x hm
    have hl' := hl _ hW
    rw [hdl] at hl'
    have h3 : Real.exp (-c) ≤ Reduction.height y m := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 : Real.exp (-(Module.finrank ℚ E * |c|)) ≤ Real.exp (Module.finrank ℚ E * -t) := by
      refine Real.exp_le_exp.2 ?_
      have := neg_abs_le t
      have := le_abs_self t
      nlinarith
    calc Real.exp (-(Module.finrank ℚ E * |c|) - c) = Real.exp (-(Module.finrank ℚ E * |c|)) * Real.exp (-c) := by
          rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ _ := mul_le_mul h4 h3 (Real.exp_pos _).le (Real.exp_pos _).le
  obtain ⟨_, ⟨γ, rfl⟩, k, hk, hgk⟩ := hcov _ hg hh
  have hyk : y = AdelicGLn.diagonal E n γ * (splitCentre E n t * k) := by
    have h1 := GlobalTheory.CompanionTheory.SplitHomeo.splitCentre_neg_mul_self (-t) y
    rw [neg_neg] at h1
    rw [← mul_assoc, ← splitCentre_comm, mul_assoc]
    have hgk' : AdelicGLn.diagonal E n γ * k = splitCentre E n (-t) * y := hgk
    change _ = splitCentre E n t * (AdelicGLn.diagonal E n γ * k)
    rw [hgk', h1]
  refine ⟨tinv (Ad E) n (AdelicGLn.diagonal E n γ), ⟨tinv E n γ, (tinv_ratGL γ).symm⟩,
    tinv (Ad E) n (splitCentre E n t * k), ⟨_, ⟨(splitCentre E n t, k), ⟨⟨t, abs_le.1 hab, rfl⟩, hk⟩, rfl⟩, rfl⟩, ?_⟩
  change tinv (Ad E) n (AdelicGLn.diagonal E n γ) * tinv (Ad E) n (splitCentre E n t * k) = x
  rw [← map_mul, ← hyk, hy, tinv_tinv]

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Cutoff.mahler_of (GlobalTheory.CompanionTheory.DegBound.degBdd_of (GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF GlobalTheory.CompanionTheory.WedgeMinor.mulF) (GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI GlobalTheory.CompanionTheory. …`.
-/
theorem mahler : Mahler :=
  GlobalTheory.CompanionTheory.Cutoff.mahler_of
    (GlobalTheory.CompanionTheory.DegBound.degBdd_of (GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF GlobalTheory.CompanionTheory.WedgeMinor.mulF)
      (GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI GlobalTheory.CompanionTheory.DetMonotone.detMono
        (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono))
      GlobalTheory.CompanionTheory.WedgeMinor.mulF (GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono GlobalTheory.CompanionTheory.DetMonotone.detMono)
      GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin finSupp GlobalTheory.CompanionTheory.LogAbs.logAbsBasic degBasisG)
    (GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG degBasisG) mahlerC

end GlobalTheory.CompanionTheory.MahlerAdelic
