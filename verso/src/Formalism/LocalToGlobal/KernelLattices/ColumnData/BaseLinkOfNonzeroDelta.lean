import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsometryLinkageAtSplitPrime
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

/- English proof (translation)
Introduce `cc hcc`. Take `⟨L, hL0⟩` from `Formalism.L2.Ker.Cd.periodExists D cc 1 hcc one_ne_zero`. Establish `hL : ∀ w : ℂ, w ∈ lamOf D cc 1 ↔ w ∈ L.lattice` using `fun w => by rw [← hL0]; rfl`. Establish `h4` using `Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 2 (by norm_num)`. Establish `h6` using `Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 3 (by norm_num)`.

Use `Formalism.L2.Th1.F.discNeZero L` as an intermediate fact. Unfold `Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3`. Rewrite using `[h4, h6]`. Simplify `this` using `[PeriodPair.g₂, PeriodPair.g₃]`.
-/
theorem discrNe (D : Car) : DiscrNe D := by
  intro cc hcc
  obtain ⟨L, hL0⟩ := Formalism.L2.Ker.Cd.periodExists D cc 1 hcc one_ne_zero
  have hL : ∀ w : ℂ, w ∈ lamOf D cc 1 ↔ w ∈ L.lattice := fun w => by rw [← hL0]; rfl
  have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 2 (by norm_num)
  have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

def LinkDeltaNe : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0

def LinkBaseRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Nonempty (Base D cc δ)

def LinkQInt : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.QIntAll

def LinkEqBase : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → ∀ N N' L L', admitted D N N' L L' →
      (B.eNat χ N N' L L' = fun z => χ (detId D (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ)) *
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) (La D (tor0 D cc δ) L L')
          (B.eNat χ N N' L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) z) ∧
      (B.eNat χ N N' L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') = fun z => χ (detId D (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) *
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N'))
          (La D (tor0 D cc δ) L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N'))
          (B.eNat χ N N' (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) z) ∧
      B.eNat χ N N' (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N') = B.thZero N N'

def LinkPart : Prop :=
  ∀ D : Car, AdmittedStatements D → ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    (∃ χ, IsChi D χ) ∧ ∀ χ, IsChi D χ → ∃ e : FamE D,
      NonzeroThetaVectorFamily D (tor0 D cc δ) e ∧ ThetaNormIndependent D (tor0 D cc δ) e ∧ th22U D (tor0 D cc δ) e

def LinkThetaFamily : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

def LinkThetaFamily' : Prop :=
  LinkPer → ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    KroneckerLimit → Uniformization → CMTransitive D → DedekindFactor D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

def PerAll (D : Car) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)

def RestAll (D : Car) (C : ℝ) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ

/- English proof (translation)
Introduce `D cc hcc δ hδ e`. Apply `discrNe D cc hcc.1` to reduce the goal to its premises. Rewrite using `[← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]`. Evaluate the numerical expressions.
-/
theorem delta_nonzero_link : LinkDeltaNe := by
  intro D cc hcc δ hδ e
  apply discrNe D cc hcc.1
  rw [← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]
  norm_num

/- English proof (translation)
Introduce `D cc hcc δ hδ` and use `base_linkage_exists D cc hcc δ (delta_nonzero_link D cc hcc δ hδ)`.
-/
theorem base_link_of_nonzero_delta : LinkBaseRec :=
  fun D cc hcc δ hδ => base_linkage_exists D cc hcc δ (delta_nonzero_link D cc hcc δ hδ)

/- English proof (translation)
Introduce `D cc hcc δ hδ B N N' L L' hA x hx`. Take `⟨a, b, hab, e⟩` from `hermitian_form_integral_values D cc hcc δ hδ (delta_nonzero_link D cc hcc δ hδ) N N' L L' hA x hx x hx`. Establish `hs` using `IO.sqrt_d_pos D`. Establish `hreal : (Hf D (tor0 D cc δ) x x).im = 0`. Establish `h1` using `IO.Hf_herm (tor0 D cc δ) x x`.

Establish `h2` using `congrArg Complex.im h1`. Rewrite `h2` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : b = 0`. Rewrite `hreal` using `[e]`.

Simplify using `at hreal`. Conclude with `hreal`. Substitute `hb` using the available equality. Take `⟨j, hj⟩` from `hab`. Use `⟨j, ?_⟩` and prove the remaining obligations.

Use `show Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = (j : ℝ)`. Rewrite using `[e]`. Establish `ha : (a : ℝ) = 2 * j`. Establish `: a = 2 * j` using `by linarith`. Conclude with `this` after adjusting the coercions.

Simplify using `only [Int.cast_zero, zero_mul, add_zero, Complex.ofReal_re]`. Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts.
-/
theorem rational_integrality_link : LinkQInt := by
  intro D cc hcc δ hδ B N N' L L' hA x hx
  obtain ⟨a, b, hab, e⟩ := hermitian_form_integral_values D cc hcc δ hδ (delta_nonzero_link D cc hcc δ hδ) N N' L L' hA x hx x hx
  have hs := IO.sqrt_d_pos D
  have hreal : (Hf D (tor0 D cc δ) x x).im = 0 := by
    have h1 := IO.Hf_herm (tor0 D cc δ) x x
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    linarith
  have hb : b = 0 := by
    rw [e] at hreal
    simp at hreal
    exact hreal
  subst hb
  obtain ⟨j, hj⟩ := hab
  refine ⟨j, ?_⟩
  show Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = (j : ℝ)
  rw [e]
  have ha : (a : ℝ) = 2 * j := by
    have : a = 2 * j := by linarith
    exact_mod_cast this
  simp only [Int.cast_zero, zero_mul, add_zero, Complex.ofReal_re]
  rw [ha]
  field_simp

/- English proof (translation)
Introduce `D cc hcc δ hδ B χ hχ N N' L L' hA`. Establish `hS` using `SO.stdOK B hcc hδ`. Establish `hL` using `B.latAll hcc hδ (delta_nonzero_link D cc hcc δ hδ)`. Conclude with `⟨B.eq_change_right hS hL χ hχ hA, B.eq_change_left hS hL χ hχ hA, B.eNat_zero hS hL χ hχ hA.1 hA.2.1⟩`.
-/
theorem equation_base_link : LinkEqBase := by
  intro D cc hcc δ hδ B χ hχ N N' L L' hA
  have hS := SO.stdOK B hcc hδ
  have hL := B.latAll hcc hδ (delta_nonzero_link D cc hcc δ hδ)
  exact ⟨B.eq_change_right hS hL χ hχ hA, B.eq_change_left hS hL χ hχ hA, B.eNat_zero hS hL χ hχ hA.1 hA.2.1⟩

/- English proof (translation)
Introduce `D hA cc hcc δ hδ`. Take `⟨B⟩` from `base_link_of_nonzero_delta D cc hcc δ hδ`. Use `⟨character_linkage_holds D hA, fun χ hχ => ⟨B.eNat χ, vector_bound_link D cc hcc δ hδ B χ hχ, ?_⟩⟩` and prove the remaining obligations. Conclude with `theta_bound_link D cc hcc δ hδ B χ hχ`.
-/
theorem partition_link : LinkPart := by
  intro D hA cc hcc δ hδ
  obtain ⟨B⟩ := base_link_of_nonzero_delta D cc hcc δ hδ
  refine ⟨character_linkage_holds D hA, fun χ hχ => ⟨B.eNat χ, vector_bound_link D cc hcc δ hδ B χ hχ, ?_⟩⟩
  exact theta_bound_link D cc hcc δ hδ B χ hχ

/- English proof (translation)
Introduce `D C hA hper h` and use `eigen_linkage_all_primes D C hA hper (discrNe D) h`.
-/
theorem provision_link_holds : LinkThetaFamily :=
  fun D C hA hper h => eigen_linkage_all_primes D C hA hper (discrNe D) h

/- English proof (translation)
Introduce `hP D C hA h1 h2 h3 h4 h` and use `provision_link_holds D C hA (hP D h1 h2 h3 h4) h`.
-/
theorem provision_link_of_periods : LinkThetaFamily' :=
  fun hP D C hA h1 h2 h3 h4 h => provision_link_holds D C hA (hP D h1 h2 h3 h4) h

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
