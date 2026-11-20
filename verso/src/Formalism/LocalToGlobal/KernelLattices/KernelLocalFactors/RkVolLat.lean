import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ZeroInjectionMemFourthPower
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Imports
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Reduction
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.EqPOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JArith
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantOfTrianglesData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.OneEntryMem
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PullMulRight
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNormOne
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemStandardThetaLatticeIffAdelicIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.FinrankRow
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuConc
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ReductionOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFacts
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLComm
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLLaw
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLTop
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PolFamInhabited
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.RightMoveTrianglesOfUnit
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Family
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfArith
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndepOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HermitianPairingIntegral
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopIso
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopNorm
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsometryLinkageTrivialLevel
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsometryLinkageAtSplitPrime
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkChi
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker.Cd.KS.Lat

open Formalism.L2.Ker.KS.Lat hiding La_theta al_eq_La alphaQ_isom delta_ne eNat_laF form_flat herm_hSc img_comap isLat_La isLat_comap isLat_laF isom_flat matH_hSc odd_of_cmOK posDef_hSc relIdx_comap relIdx_laF relIdx_laF_eq sc_pos selfDual_comap selfDual_laF thHalf_laF thMoved_laF thZero_laF th_comap th_laF theta_laF

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (hSc)
open Formalism.L2.Th1.F (cmTheta)

section Gen

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [FiniteDimensional ℂ W] {H : Sesq V} {H' : Sesq W} (g : V ≃ₗ[ℂ] W)

/- English proof (translation)
The claim follows from `AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ'`.
-/
theorem img_comap (Λ' : AddSubgroup W) :
    imgLat (g : V →ₗ[ℂ] W) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = Λ' :=
  AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ'

/- English proof (translation)
Unfold `IsSelfDual at h ⊢`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx show g x ∈ Λ'`. Rewrite using `[← h]`.

Introduce `y hy`. Take `⟨m, hm⟩` from `hx (g.symm y) (by show g (g.symm y) ∈ Λ'; rw [g.apply_symm_apply]; exact hy)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`. Establish `h1` using `hI x (g.symm y)`.

Establish `h2 : (g : V →ₗ[ℂ] W) (g.symm y) = y` using `g.apply_symm_apply y`. Rewrite `h1` using `[h2]`. Unfold `altE`. Rewrite using `[← h1]`. Both sides reduce to the same expression.

Introduce `hx y hy`. Establish `hx' : g x ∈ dualLat H' Λ'` using `by rw [h]; exact hx`. Take `⟨m, hm⟩` from `hx' (g y) hy`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`.

Unfold `altE`. Rewrite using `[← hI x y]`. Both sides reduce to the same expression.
-/
theorem selfDual_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} (h : IsSelfDual H' Λ') :
    IsSelfDual H (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  unfold IsSelfDual at h ⊢
  ext x
  constructor
  · intro hx
    show g x ∈ Λ'
    rw [← h]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g.symm y) (by show g (g.symm y) ∈ Λ'; rw [g.apply_symm_apply]; exact hy)
    refine ⟨m, ?_⟩
    rw [← hm]
    have h1 := hI x (g.symm y)
    have h2 : (g : V →ₗ[ℂ] W) (g.symm y) = y := g.apply_symm_apply y
    rw [h2] at h1
    unfold altE
    rw [← h1]
    rfl
  · intro hx y hy
    have hx' : g x ∈ dualLat H' Λ' := by rw [h]; exact hx
    obtain ⟨m, hm⟩ := hx' (g y) hy
    refine ⟨m, ?_⟩
    rw [← hm]
    unfold altE
    rw [← hI x y]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `h.1` as an intermediate fact. Set `f : (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) → Λ'` to `fun x => ⟨g x.1, x.2⟩`. Establish `hf : Continuous f` using `Continuous.subtype_mk (((g : V →ₗ[ℂ] W).continuous_of_finiteDimensional).comp continuous_subtype_val) _`. Establish `hinj : Function.Injective f`.

Introduce `x y hxy`. Conclude with `Subtype.ext (g.injective (congrArg Subtype.val hxy))`. Conclude with `DiscreteTopology.of_continuous_injective hf hinj`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Set `p : W →ₗ[ℝ] V` to `(g.symm : W →ₗ[ℂ] V).restrictScalars ℝ`. Establish `h2 : (Submodule.span ℝ (Λ' : Set W)).map p ≤ Submodule.span ℝ ((Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom : AddSubgroup V) : Set V)`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `show g (g.symm y) ∈ Λ'`. Rewrite using `[g.apply_symm_apply]`. Conclude with `hy`. Use `h2 ⟨g v, by rw [h.2]; trivial, ?_⟩` and prove the remaining obligations. Use `show g.symm (g v) = v`.

Conclude with `g.symm_apply_apply v`.
-/
theorem isLat_comap {Λ' : AddSubgroup W} (h : IsLat Λ') : IsLat (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  constructor
  · have := h.1
    let f : (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) → Λ' := fun x => ⟨g x.1, x.2⟩
    have hf : Continuous f :=
      Continuous.subtype_mk (((g : V →ₗ[ℂ] W).continuous_of_finiteDimensional).comp continuous_subtype_val) _
    have hinj : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
    exact DiscreteTopology.of_continuous_injective hf hinj
  · rw [eq_top_iff]
    intro v _
    let p : W →ₗ[ℝ] V := (g.symm : W →ₗ[ℂ] V).restrictScalars ℝ
    have h2 : (Submodule.span ℝ (Λ' : Set W)).map p ≤
        Submodule.span ℝ ((Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom : AddSubgroup V) : Set V) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      apply Submodule.subset_span
      show g (g.symm y) ∈ Λ'
      rw [g.apply_symm_apply]
      exact hy
    refine h2 ⟨g v, by rw [h.2]; trivial, ?_⟩
    show g.symm (g v) = v
    exact g.symm_apply_apply v

/- English proof (translation)
Apply the tactic sequence `refine (ThIsom_of heisenbergIsometry V W H H' g hI _ α' G).1 ?_`. Rewrite using `[img_comap]`. Conclude with `hG`.
-/
theorem th_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} {α' : W → ℂ} {G : W → ℂ} (hG : G ∈ Th H' α' Λ') :
    (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  refine (ThIsom_of heisenbergIsometry V W H H' g hI _ α' G).1 ?_
  rw [img_comap]
  exact hG

/- English proof (translation)
Unfold `relIdx`. Rewrite using `[AddSubgroup.relIndex_comap]`. Use `congr 1`. Conclude with `AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ₂`.
-/
theorem relIdx_comap (Λ₁ Λ₂ : AddSubgroup W) :
    relIdx (Λ₁.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = relIdx Λ₁ Λ₂ := by
  unfold relIdx
  rw [AddSubgroup.relIndex_comap]
  congr 1
  exact AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ₂

/- English proof (translation)
Unfold `alphaQ Formalism.L2.Th1.H.qOf`. Use `hI v v` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem alphaQ_isom (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) (c : ℝ) (v : V) : alphaQ c H' (g v) = alphaQ c H v := by
  unfold alphaQ Formalism.L2.Th1.H.qOf
  have := hI v v
  rw [← this]
  rfl

end Gen

section Form

variable {D : Car} {X : Fields} (s : Seam D X)

/- English proof (translation)
Rewrite using `[formV_apply]`. Use `show (∑ i, ∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = _`. Establish `h1 : ∀ i : DVar X.Tau a b, (∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = x i * conj (y i) / (A : ℂ)`. Introduce `i`. Rewrite using `[Finset.sum_eq_single i]`.

Unfold `hSc`. Rewrite using `[Matrix.diagonal_apply_eq]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `j _ hj`.

Unfold `hSc`. Rewrite using `[Matrix.diagonal_apply_ne _ (Ne.symm hj)]`. Simplify using the standard rewrite rules. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.

Simplify using `only [h1]`. Rewrite using `[← Finset.sum_div]`. Use `congr 1`. Rewrite using `[Fintype.sum_prod_type, ← Equiv.sum_comp s.iT.symm]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
theorem form_flat (A : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b A⁻¹) x y = formV A D.what₂.Tau a b (s.flatV a b x) (s.flatV a b y) := by
  rw [formV_apply]
  show (∑ i, ∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = _
  have h1 : ∀ i : DVar X.Tau a b, (∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = x i * conj (y i) / (A : ℂ) := by
    intro i
    rw [Finset.sum_eq_single i]
    · unfold hSc
      rw [Matrix.diagonal_apply_eq]
      push_cast
      field_simp
    · intro j _ hj
      unfold hSc
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [h1]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp s.iT.symm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

/- English proof (translation)
Introduce `x y` and use `(form_flat s A a b x y).symm`.
-/
theorem isom_flat (A : ℝ) (a b : ℕ) :
    IsIsom (matH (hSc X.Tau a b A⁻¹)) (formV A D.what₂.Tau a b)
      ((s.flatV a b : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) : (DVar X.Tau a b → ℂ) →ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) :=
  fun x y => (form_flat s A a b x y).symm

/- English proof (translation)
Use `show (∑ i, ∑ j, x i * hSc X.Tau a b sc i j * conj (y j)) = _`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Unfold `hSc`.

Rewrite using `[Matrix.diagonal_apply_eq]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hj`. Unfold `hSc`. Rewrite using `[Matrix.diagonal_apply_ne _ (Ne.symm hj)]`.

Simplify using the standard rewrite rules. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem matH_hSc (sc : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b sc) x y = (sc : ℂ) * ∑ k, x k * conj (y k) := by
  show (∑ i, ∑ j, x i * hSc X.Tau a b sc i j * conj (y j)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · unfold hSc
    rw [Matrix.diagonal_apply_eq]
    ring
  · intro j _ hj
    unfold hSc
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
Introduce `x y`. Rewrite using `[matH_hSc, matH_hSc, map_mul, Complex.conj_ofReal, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj, mul_comm]`.
-/
theorem herm_hSc (sc : ℝ) (a b : ℕ) : IsHerm (matH (hSc X.Tau a b sc)) := by
  intro x y
  rw [matH_hSc, matH_hSc, map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/- English proof (translation)
Introduce `x hx`. Rewrite using `[matH_hSc]`. Establish `h1 : (∑ k, x k * conj (x k)) = ((∑ k, Complex.normSq (x k) : ℝ) : ℂ)`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun k _ => Complex.mul_conj (x k)`.

Rewrite using `[h1, ← Complex.ofReal_mul, Complex.ofReal_re]`. Apply `mul_pos hsc` to reduce the goal to its premises. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, x k ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hx (funext hcon)`. Conclude with `Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ k, Complex.normSq_pos.2 hk⟩`.
-/
theorem posDef_hSc {sc : ℝ} (hsc : 0 < sc) (a b : ℕ) : IsPosDef (matH (hSc X.Tau a b sc)) := by
  intro x hx
  rw [matH_hSc]
  have h1 : (∑ k, x k * conj (x k)) = ((∑ k, Complex.normSq (x k) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => Complex.mul_conj (x k)
  rw [h1, ← Complex.ofReal_mul, Complex.ofReal_re]
  apply mul_pos hsc
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ k, Complex.normSq_pos.2 hk⟩

end Form

section Lat

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

include B in

/- English proof (translation)
Rewrite using `[show TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]`. Conclude with `inv_pos.2 (Formalism.L2.Th1.F.areaPos_thm B.L)`.
-/
theorem sc_pos : 0 < (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹ := by
  rw [show TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  exact inv_pos.2 (Formalism.L2.Th1.F.areaPos_thm B.L)

/- English proof (translation)
The claim follows from `Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ`.
-/
theorem delta_ne (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ

variable {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}

/- English proof (translation)
Establish `hL` using `B.latAll hcc hδ (delta_ne hcc hδ)`. Establish `h0 : IsLat (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b))` using `Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J.lat0IsLat (B.stdOK hcc hδ) a b`. Establish `hc` using `hL.2 a b _ _ _ _ (Formalism.L2.Ker.Cd.Base.first_coordinate_admissible hA) hA`. Conclude with `KR.isLat_of_comm h0 hc.2 hc.1`.
-/
theorem isLat_La (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    IsLat (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') := by
  have hL := B.latAll hcc hδ (delta_ne hcc hδ)
  have h0 : IsLat (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) :=
    Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J.lat0IsLat (B.stdOK hcc hδ) a b
  have hc := hL.2 a b _ _ _ _ (Formalism.L2.Ker.Cd.Base.first_coordinate_admissible hA) hA
  exact KR.isLat_of_comm h0 hc.2 hc.1

/- English proof (translation)
The claim follows from `isLat_comap (s.flatV a b) (isLat_La B hcc hδ hA)`.
-/
theorem isLat_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    IsLat (s.laF B.tor L L') :=
  isLat_comap (s.flatV a b) (isLat_La B hcc hδ hA)

/- English proof (translation)
The claim follows from `selfDual_comap (s.flatV a b) (isom_flat s _ a b) ((B.latAll hcc hδ (delta_ne hcc hδ)).1 a b L L' hA).1`.
-/
theorem selfDual_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    IsSelfDual (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)) (s.laF B.tor L L') :=
  selfDual_comap (s.flatV a b) (isom_flat s _ a b) ((B.latAll hcc hδ (delta_ne hcc hδ)).1 a b L L' hA).1

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, A, hA, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨cmTheta 1 D.host.d * w, Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.lam_theta hw, A, hA, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg x _ h => rw [smul_neg]`.

Conclude with `neg_mem h`.
-/
theorem La_theta {x : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b} (hx : x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') : cmTheta 1 D.host.d • x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨cmTheta 1 D.host.d * w, Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.lam_theta hw, A, hA, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Take `⟨k, rfl⟩` from `hb`. Establish `h1 : cmTheta (2 * k + 1) D.host.d = (k : ℂ) + cmTheta 1 D.host.d`. Unfold `cmTheta`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `show s.flatV a b (cmTheta (2 * k + 1) D.host.d • x) ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L'`. Rewrite using `[map_smul, h1, add_smul]`. Use `add_mem ?_ (La_theta B hx)` and prove the remaining obligations. Establish `h2 : ((k : ℂ) • s.flatV a b x) = k • s.flatV a b x`. Rewrite using `[← Int.cast_smul_eq_zsmul ℂ]`.

Rewrite using `[h2]`. Conclude with `AddSubgroup.zsmul_mem _ hx k`.
-/
theorem theta_laF {b₀ : ℤ} (hb : Odd b₀) {x : DVar X.Tau a b → ℂ} (hx : x ∈ s.laF B.tor L L') :
    cmTheta b₀ D.host.d • x ∈ s.laF B.tor L L' := by
  obtain ⟨k, rfl⟩ := hb
  have h1 : cmTheta (2 * k + 1) D.host.d = (k : ℂ) + cmTheta 1 D.host.d := by
    unfold cmTheta
    push_cast
    ring
  show s.flatV a b (cmTheta (2 * k + 1) D.host.d • x) ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L'
  rw [map_smul, h1, add_smul]
  refine add_mem ?_ (La_theta B hx)
  have h2 : ((k : ℂ) • s.flatV a b x) = k • s.flatV a b x := by
    rw [← Int.cast_smul_eq_zsmul ℂ]
  rw [h2]
  exact AddSubgroup.zsmul_mem _ hx k

/- English proof (translation)
Take `⟨h1, -, h3, -⟩` from `h`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[Int.not_odd_iff_even]`. Take `⟨k, rfl⟩` from `hcon`. Establish `h4 : (d : ℤ) % 8 = 7` using `by exact_mod_cast h3`.

Establish `h5 : 4 * ((a₀ : ℤ) * c₀) = 4 * (k * k) + d` using `by rw [← mul_assoc, h1]; ring`. Generalize the expression as in `(a₀ : ℤ) * c₀ = u at h5`. Generalize the expression as in `k * k = v at h5`. Use linear arithmetic over natural numbers and integers.
-/
theorem odd_of_cmOK {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (h : CmOK a₀ b₀ c₀ d) : Odd b₀ := by
  obtain ⟨h1, -, h3, -⟩ := h
  by_contra hcon
  rw [Int.not_odd_iff_even] at hcon
  obtain ⟨k, rfl⟩ := hcon
  have h4 : (d : ℤ) % 8 = 7 := by exact_mod_cast h3
  have h5 : 4 * ((a₀ : ℤ) * c₀) = 4 * (k * k) + d := by rw [← mul_assoc, h1]; ring
  generalize (a₀ : ℤ) * c₀ = u at h5
  generalize k * k = v at h5
  omega

/- English proof (translation)
Introduce `x hx`. Take `⟨m, hm⟩` from `Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b L L' hA x hx`. Conclude with `al_eq D B.tor x m hm`.
-/
theorem al_eq_La (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    ∀ x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L', Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor x =
      alphaQ (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) x := by
  intro x hx
  obtain ⟨m, hm⟩ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b L L' hA x hx
  exact al_eq D B.tor x m hm

/- English proof (translation)
Establish `h1` using `Th_congr _ _ _ _ (al_eq_La B hcc hδ hA) hG`. Establish `h2` using `th_comap (s.flatV a b) (isom_flat s _ a b) h1`. Use `Th_congr _ _ _ _ (fun x _ => ?_) h2` and prove the remaining obligations. Conclude with `alphaQ_isom (s.flatV a b) (isom_flat s _ a b) _ x`.
-/
theorem th_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') {G : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b → ℂ}
    (hG : G ∈ Th (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor) (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L')) :
    (fun z => G (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') := by
  have h1 := Th_congr _ _ _ _ (al_eq_La B hcc hδ hA) hG
  have h2 := th_comap (s.flatV a b) (isom_flat s _ a b) h1
  refine Th_congr _ _ _ _ (fun x _ => ?_) h2
  exact alphaQ_isom (s.flatV a b) (isom_flat s _ a b) _ x

/- English proof (translation)
The claim follows from `th_laF s B hcc hδ (Formalism.L2.Ker.Cd.Inhab.Adm_std D a b ha hb) (B.thZeroMem (B.stdOK hcc hδ) a b)`.
-/
theorem thZero_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (ha : Even a) (hb : Even b) :
    (fun z => B.thZero a b (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)))
      (s.laF B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) :=
  th_laF s B hcc hδ (Formalism.L2.Ker.Cd.Inhab.Adm_std D a b ha hb) (B.thZeroMem (B.stdOK hcc hδ) a b)

/- English proof (translation)
The claim follows from `th_laF s B hcc hδ (Formalism.L2.Ker.Cd.Base.isAdmissible_flagPair_of_unitriangular_left_automorphism hA) (B.thHalf_mem (B.stdOK hcc hδ) (B.latAll hcc hδ (delta_ne hcc hδ)) hA)`.
-/
theorem thHalf_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    (fun z => B.thHalf a b L (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)))
      (s.laF B.tor L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) :=
  th_laF s B hcc hδ (Formalism.L2.Ker.Cd.Base.isAdmissible_flagPair_of_unitriangular_left_automorphism hA) (B.thHalf_mem (B.stdOK hcc hδ) (B.latAll hcc hδ (delta_ne hcc hδ)) hA)

/- English proof (translation)
The claim follows from `th_laF s B hcc hδ hA (B.thMoved_mem (B.latAll hcc hδ (delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)`.
-/
theorem thMoved_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    (fun z => B.thMoved a b L L' (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') :=
  th_laF s B hcc hδ hA (B.thMoved_mem (B.latAll hcc hδ (delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)

/- English proof (translation)
The claim follows from `Submodule.smul_mem _ (Formalism.L2.Ker.Cd.Base.chiFac χ a b L L') (thMoved_laF s B hcc hδ hA)`.
-/
theorem eNat_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    (fun z => B.eNat χ a b L L' (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') :=
  Submodule.smul_mem _ (Formalism.L2.Ker.Cd.Base.chiFac χ a b L L') (thMoved_laF s B hcc hδ hA)

/- English proof (translation)
Unfold `Formalism.L2.Ker.Cd.Seam.laF`. Rewrite using `[relIdx_comap]`. Conclude with `((B.latAll hcc hδ (delta_ne hcc hδ)).2 a b _ _ _ _ hA hA₁).1`.
-/
theorem relIdx_laF (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') (hA₁ : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L₁ L₁') :
    relIdx (s.laF B.tor L L') (s.laF B.tor L₁ L₁') ≠ 0 := by
  unfold Formalism.L2.Ker.Cd.Seam.laF
  rw [relIdx_comap]
  exact ((B.latAll hcc hδ (delta_ne hcc hδ)).2 a b _ _ _ _ hA hA₁).1

/- English proof (translation)
Unfold `Formalism.L2.Ker.Cd.Seam.laF`. Rewrite using `[relIdx_comap]`.
-/
theorem relIdx_laF_eq {L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} :
    relIdx (s.laF B.tor L L') (s.laF B.tor L₁ L₁') = relIdx (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L₁ L₁') := by
  unfold Formalism.L2.Ker.Cd.Seam.laF
  rw [relIdx_comap]

end Lat

end Formalism.L2.Ker.Cd.KS.Lat
