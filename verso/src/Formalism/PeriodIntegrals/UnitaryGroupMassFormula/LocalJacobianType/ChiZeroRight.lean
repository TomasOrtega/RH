import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousPsiVOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

def chi (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) : ℂ :=
  psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sdE_eq (ι : Type) [Fintype ι] :
    sdE (E := E) ψ v ι = if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι)
      then h.choose else 0 := rfl

/- English proof (translation)
Simplify using `only [chi, Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib, psiV_add']`.
-/
theorem chi_add_left (ι : Type) [Fintype ι] (x t y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y := by
  simp only [chi, Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib, psiV_add']

/- English proof (translation)
Simplify using `only [chi, mul_comm]`.
-/
theorem chi_symm (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι x y = chi (E := E) v ψ ι y x := by
  simp only [chi, mul_comm]

/- English proof (translation)
Simplify using `[chi, psiV_zero]`.
-/
theorem chi_zero_right (ι : Type) [Fintype ι] (x : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι x 0 = 1 := by
  simp [chi, psiV_zero]

/- English proof (translation)
Simplify using `only [chi, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]`.
-/
theorem chi_smul (ι : Type) [Fintype ι] (c : Fv F v) (x y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι (c • x) y = chi (E := E) v ψ ι x (c • y) := by
  simp only [chi, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]

def D1 : Set (Fv F v ⊗[F] E) :=
  {y | ∀ x ∈ OEv (E := E) v, psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1}

def Dbox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => D1 (E := E) v ψ

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy i _ x hx`. Establish `h` using `hy (Pi.single i x) (fun j _ => by`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `using hx`. Simplify `oev_zero v)` using `[Pi.single_apply, hj]`. Establish `hs : ∑ j, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((Pi.single i x : ι → Fv F v ⊗[F] E) j * y j) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y i)`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_apply, hj]`. Simplify using the standard rewrite rules. Simplify using `only [chi] at h`.

Rewrite `h` using `[hs]`. Then use the resulting hypothesis. Introduce `hy x hx`. Simplify using `only [chi]`. Rewrite using `[psiV_sum]`. Conclude with `Finset.prod_eq_one fun i _ => hy i trivial (x i) (hx i trivial)`.
-/
theorem ann_obox (ι : Type) [Fintype ι] :
    ann (chi (E := E) v ψ ι) (Obox (E := E) v ι) = Dbox (E := E) v ψ ι := by
  classical
  ext y
  constructor
  · intro hy i _ x hx
    have h := hy (Pi.single i x) (fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using hx
      · simpa [Pi.single_apply, hj] using oev_zero v)
    have hs : ∑ j, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((Pi.single i x : ι → Fv F v ⊗[F] E) j * y j) =
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y i) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    simp only [chi] at h
    rwa [hs] at h
  · intro hy x hx
    simp only [chi]
    rw [psiV_sum]
    exact Finset.prod_eq_one fun i _ => hy i trivial (x i) (hx i trivial)

def ObS (ι : Type) : AddSubgroup (ι → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ fun _ => Osub (E := E) v

/- English proof (translation)
Simplify using `[ObS, AddSubgroup.coe_pi, Obox, Osub]`.
-/
theorem coe_ObS (ι : Type) : (ObS (E := E) v ι : Set (ι → Fv F v ⊗[F] E)) = Obox (E := E) v ι := by
  simp [ObS, AddSubgroup.coe_pi, Obox, Osub]

/- English proof (translation)
The claim follows from `isCompact_univ_pi fun _ => isCompact_oev v`.
-/
theorem isCompact_obox (ι : Type) [Fintype ι] : IsCompact (Obox (E := E) v ι) :=
  isCompact_univ_pi fun _ => isCompact_oev v

/- English proof (translation)
The claim follows from `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v`.
-/
theorem isOpen_obox (ι : Type) [Fintype ι] : IsOpen (Obox (E := E) v ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v

/- English proof (translation)
Introduce `_ _` and use `oev_zero v`.
-/
theorem zero_mem_obox (ι : Type) : (0 : ι → Fv F v ⊗[F] E) ∈ Obox (E := E) v ι :=
  fun _ _ => oev_zero v

variable [SecondCountableTopology (Fv F v ⊗[F] E)]

/- English proof (translation)
Use `hμ.1` as an intermediate fact. Use `set L := ObS (E := E) v ι`. Establish `hLo : IsOpen (L : Set (ι → Fv F v ⊗[F] E))` using `by rw [coe_ObS]; exact isOpen_obox v ι`. Establish `hLc : IsCompact (L : Set (ι → Fv F v ⊗[F] E))` using `by rw [coe_ObS]; exact isCompact_obox v ι`. Establish `hcl : IsClopen (L : Set (ι → Fv F v ⊗[F] E))` using `⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩`.

Use `set Φ : (ι → Fv F v ⊗[F] E) → ℂ := (L : Set (ι → Fv F v ⊗[F] E)).indicator (fun _ => (1 : ℂ))`. Establish `hΦc : Continuous Φ` using `by classical`. Rewrite using `[show Φ = (L : Set _).piecewise (fun _ => (1 : ℂ)) (fun _ => 0) from (Set.piecewise_eq_indicator).symm]`. Conclude with `continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const`. Establish `hΦs : HasCompactSupport Φ` using `HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _`.

Establish `hχ : ∀ x t y, chi (E` using `E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y := chi_add_left v ψ ι`. Establish `hT : ∀ y, ∫ x, Φ x * chi (E` using `E) v ψ ι x y ∂μ = (Dbox (E := E) v ψ ι).indicator (fun _ => ((μ.real (Obox (E := E) v ι) : ℝ) : ℂ)) y := by`. Introduce `y`. Establish `h` using `transform_indicator μ (chi (E := E) v ψ ι) hχ L hLo y`. Rewrite `h` using `[coe_ObS, ann_obox]`.

Conclude with `h`. Establish `hI : Integrable (fun y => ∫ x, Φ x * chi (E` using `E) v ψ ι x y ∂μ) μ := by`. Simplify using `only [hT]`. Rewrite using `[integrable_indicator_iff hA]`. Conclude with `integrableOn_const hfin.ne`.

Establish `h` using `hμ.2 Φ hΦc hΦs hI 0`. Simplify using `only [hT] at h`. Simplify using `only [chi_zero_right, mul_one, neg_zero] at h`. Rewrite `h` using `[integral_indicator_const _ hA]`. Establish `h0 : Φ 0 = 1` using `by simp [Φ, L.zero_mem]`.

Rewrite `h` using `[h0]`. Establish `h2 : ((μ.real (Dbox (E` using `E) v ψ ι) * μ.real (Obox (E := E) v ι) : ℝ) : ℂ) = 1 := by`. Rewrite using `[← h]`. Simplify using `[Complex.real_smul]`. Establish `h3 : μ.real (Dbox (E` using `E) v ψ ι) * μ.real (Obox (E := E) v ι) = 1 := by exact_mod_cast h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sd_test (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    (hμ : SelfDual μ (chi (E := E) v ψ ι)) (hA : MeasurableSet (Dbox (E := E) v ψ ι))
    (hfin : μ (Dbox (E := E) v ψ ι) < ⊤) :
    μ.real (Obox (E := E) v ι) * μ.real (Dbox (E := E) v ψ ι) = 1 := by
  have := hμ.1
  set L := ObS (E := E) v ι
  have hLo : IsOpen (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isOpen_obox v ι
  have hLc : IsCompact (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isCompact_obox v ι
  have hcl : IsClopen (L : Set (ι → Fv F v ⊗[F] E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : (ι → Fv F v ⊗[F] E) → ℂ := (L : Set (ι → Fv F v ⊗[F] E)).indicator (fun _ => (1 : ℂ))
  have hΦc : Continuous Φ := by
    classical
    rw [show Φ = (L : Set _).piecewise (fun _ => (1 : ℂ)) (fun _ => 0) from
      (Set.piecewise_eq_indicator).symm]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ := HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hχ : ∀ x t y, chi (E := E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y :=
    chi_add_left v ψ ι
  have hT : ∀ y, ∫ x, Φ x * chi (E := E) v ψ ι x y ∂μ =
      (Dbox (E := E) v ψ ι).indicator (fun _ => ((μ.real (Obox (E := E) v ι) : ℝ) : ℂ)) y := by
    intro y
    have h := transform_indicator μ (chi (E := E) v ψ ι) hχ L hLo y
    rw [coe_ObS, ann_obox] at h
    exact h
  have hI : Integrable (fun y => ∫ x, Φ x * chi (E := E) v ψ ι x y ∂μ) μ := by
    simp only [hT]
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hfin.ne
  have h := hμ.2 Φ hΦc hΦs hI 0
  simp only [hT] at h
  simp only [chi_zero_right, mul_one, neg_zero] at h
  rw [integral_indicator_const _ hA] at h
  have h0 : Φ 0 = 1 := by simp [Φ, L.zero_mem]
  rw [h0] at h
  have h2 : ((μ.real (Dbox (E := E) v ψ ι) * μ.real (Obox (E := E) v ι) : ℝ) : ℂ) = 1 := by
    rw [← h]; simp [Complex.real_smul]
  have h3 : μ.real (Dbox (E := E) v ψ ι) * μ.real (Obox (E := E) v ι) = 1 := by exact_mod_cast h2
  linarith

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
