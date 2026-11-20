import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehomA
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AwayToSectionFromZero

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

variable (R : Type) [CommRing R] (N : ℕ)

abbrev grading : ℕ → Submodule R (MvPolynomial (Fin (N + 1)) R) :=
  homogeneousSubmodule (Fin (N + 1)) R

/- English proof (translation)
The claim follows from `isHomogeneous_X R i`.
-/
theorem X_mem (i : Fin (N + 1)) : (X i : MvPolynomial (Fin (N + 1)) R) ∈ grading R N 1 :=
  isHomogeneous_X R i

/- English proof (translation)
The claim follows from `isHomogeneous_X_pow i n`.
-/
theorem X_pow_mem (i : Fin (N + 1)) (n : ℕ) :
    (X i ^ n : MvPolynomial (Fin (N + 1)) R) ∈ grading R N n :=
  isHomogeneous_X_pow i n

abbrev chart (i : Fin (N + 1)) : (PSpace R N).Opens :=
  Proj.basicOpen (grading R N) (X i)

/- English proof (translation)
The claim follows from `Proj.isAffineOpen_basicOpen _ _ (X_mem R N i) one_pos`.
-/
theorem isAffineOpen_chart (i : Fin (N + 1)) : IsAffineOpen (chart R N i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem R N i) one_pos

/- English proof (translation)
Rewrite using `[← Set.image_univ, mem_ideal_span_X_image]`. Introduce `m hm`. Use `by_contra! H`. Take `rfl : m = 0` from `Finsupp.ext fun i => H i (Set.mem_univ i)`. Use `hf (mem_support_iff.1 hm)` as an intermediate fact.

Simplify using `only [map_zero] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_span_X_of_isHomogeneous {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) : f ∈ Ideal.span (Set.range (X : Fin (N + 1) → MvPolynomial _ R)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! H
  obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
  have := hf (mem_support_iff.1 hm)
  simp only [map_zero] at this
  omega

/- English proof (translation)
The claim follows from `(HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_isHomogeneous R N hn hf`.
-/
theorem irrelevant_le_span_X : (HomogeneousIdeal.irrelevant (grading R N)).toIdeal ≤
    Ideal.span (Set.range (X : Fin (N + 1) → MvPolynomial _ R)) :=
  (HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_isHomogeneous R N hn hf

/- English proof (translation)
The claim follows from `Proj.iSup_basicOpen_eq_top _ _ (irrelevant_le_span_X R N)`.
-/
theorem iSup_chart : ⨆ i, chart R N i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (irrelevant_le_span_X R N)

/- English proof (translation)
The claim follows from `Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))`.
-/
theorem exists_mem_chart (x : PSpace R N) : ∃ i, x ∈ chart R N i :=
  Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))

variable {R N}

/- English proof (translation)
Introduce `x hx h` and use `hU hx (x.isPrime.mem_of_pow_mem n h)`.
-/
theorem le_basicOpen_X_pow {U : (PSpace R N).Opens} {i : Fin (N + 1)} (hU : U ≤ chart R N i) (n : ℕ) :
    U ≤ Proj.basicOpen (grading R N) (X i ^ n) :=
  fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)

def formOn (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hU : U ≤ chart R N i) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) : Γ(PSpace R N, U) :=
  frac (grading R N) U f (X i ^ n) hf (X_pow_mem R N i n) (le_basicOpen_X_pow hU n)

def ratioOn (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hU : U ≤ chart R N i) (j : Fin (N + 1)) :
    Γ(PSpace R N, U) :=
  frac (grading R N) U (X j) (X i) (X_mem R N j) (X_mem R N i) hU

variable (R N) in

abbrev ratio (i j : Fin (N + 1)) : Γ(PSpace R N, chart R N i) := ratioOn (chart R N i) i le_rfl j

def ratioUnit (U : (PSpace R N).Opens) (i j : Fin (N + 1)) (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) :
    Γ(PSpace R N, U)ˣ :=
  fracUnit (grading R N) U (X j) (X i) (X_mem R N j) (X_mem R N i) hj hi

section

variable {U V : (PSpace R N).Opens} {i j k : Fin (N + 1)} {hi : U ≤ chart R N i} {hj : U ≤ chart R N j}
  {hk : U ≤ chart R N k} {n m : ℕ} {f g : MvPolynomial (Fin (N + 1)) R}

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem val_ratioUnit : (ratioUnit U i j hi hj : Γ(PSpace R N, U)) = ratioOn U i hi j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inv_ratioUnit : (ratioUnit U i j hi hj)⁻¹ = ratioUnit U j i hj hi := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resG_ratioOn (h : V ≤ U) : resG _ h (ratioOn U i hi j) = ratioOn V i (h.trans hi) j := rfl

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem res_ratioUnit (h : V ≤ U) :
    res h (ratioUnit U i j hi hj) = ratioUnit V i j (h.trans hi) (h.trans hj) := Units.ext rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resG_formOn (h : V ≤ U) (hf : f.IsHomogeneous n) :
    resG _ h (formOn U i hi n f hf) = formOn V i (h.trans hi) n f hf := rfl

/- English proof (translation)
The claim follows from `frac_self`.
-/
@[simp] theorem ratioOn_self : ratioOn U i hi i = 1 := frac_self

/- English proof (translation)
The claim follows from `frac_mul_eq (by ring)`.
-/
theorem ratioOn_mul_ratioOn : ratioOn U i hi j * ratioOn U j hj k = ratioOn U i hi k :=
  frac_mul_eq (by ring)

/- English proof (translation)
The claim follows from `Units.ext (ratioOn_self (hi := hi))`.
-/
theorem ratioUnit_self {hi' : U ≤ chart R N i} : ratioUnit U i i hi hi' = 1 :=
  Units.ext (ratioOn_self (hi := hi))

/- English proof (translation)
The claim follows from `Units.ext (ratioOn_mul_ratioOn (hi := hi) (hj := hj))`.
-/
theorem ratioUnit_mul_ratioUnit :
    ratioUnit U i j hi hj * ratioUnit U j k hj hk = ratioUnit U i k hi hk :=
  Units.ext (ratioOn_mul_ratioOn (hi := hi) (hj := hj))

/- English proof (translation)
The claim follows from `basicOpen_frac`.
-/
theorem basicOpen_ratioOn : (PSpace R N).basicOpen (ratioOn U i hi j) = U ⊓ chart R N j :=
  basicOpen_frac

/- English proof (translation)
The claim follows from `basicOpen_frac`.
-/
theorem basicOpen_formOn (hf : f.IsHomogeneous n) :
    (PSpace R N).basicOpen (formOn U i hi n f hf) = U ⊓ Proj.basicOpen (grading R N) f :=
  basicOpen_frac

/- English proof (translation)
The claim follows from `frac_eq (by ring)`.
-/
theorem formOn_X : formOn U i hi 1 (X j) (isHomogeneous_X R j) = ratioOn U i hi j :=
  frac_eq (by ring)

/- English proof (translation)
The claim follows from `frac_add`.
-/
theorem formOn_add (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) :
    formOn U i hi n (f + g) (hf.add hg) = formOn U i hi n f hf + formOn U i hi n g hg :=
  frac_add

/- English proof (translation)
The claim follows from `frac_zero`.
-/
theorem formOn_zero : formOn U i hi n 0 (isHomogeneous_zero _ R n) = 0 := frac_zero

/- English proof (translation)
The claim follows from `(frac_mul_eq (by ring)).symm`.
-/
theorem formOn_mul (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous m) :
    formOn U i hi (n + m) (f * g) (hf.mul hg) = formOn U i hi n f hf * formOn U i hi m g hg :=
  (frac_mul_eq (by ring)).symm

/- English proof (translation)
Rewrite using `[ratioOn, frac_pow]`. Conclude with `(frac_mul_eq (by ring)).symm`.
-/
theorem formOn_eq_ratioOn_pow_mul (hj : U ≤ chart R N j) (hf : f.IsHomogeneous n) :
    formOn U i hi n f hf = ratioOn U i hi j ^ n * formOn U j hj n f hf := by
  rw [ratioOn, frac_pow]
  exact (frac_mul_eq (by ring)).symm

end

variable (R N)

def O1 : LB (PSpace R N) where
  ι := Fin (N + 1)
  U := chart R N
  g i j := ratioUnit (chart R N i ⊓ chart R N j) i j inf_le_left inf_le_right

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem twistingSheafOne_chart_eq_preimage_standardChart (i : Fin (N + 1)) : (O1 R N).U i = Proj.basicOpen (grading R N) (X i) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem O1_g_eq_ratioUnit_chart_inf (i j : Fin (N + 1)) :
    (O1 R N).g i j = ratioUnit (chart R N i ⊓ chart R N j) i j inf_le_left inf_le_right := rfl

/- English proof (translation)
The claim follows from `iSup_chart R N g_self _ := Units.ext (ratioOn_self (hi := le_rfl)) cocycle _ _ _ := Units.ext (ratioOn_mul_ratioOn (hi := inf_le_left.trans inf_le_left) (hj := inf_le_left.trans inf_le_right))`.
-/
theorem O1_isLB : (O1 R N).IsLB where
  cover := iSup_chart R N
  g_self _ := Units.ext (ratioOn_self (hi := le_rfl))
  cocycle _ _ _ := Units.ext (ratioOn_mul_ratioOn (hi := inf_le_left.trans inf_le_left)
    (hj := inf_le_left.trans inf_le_right))

def coord (k : Fin (N + 1)) : (O1 R N).Sec where
  f i := ratio R N i k
  compat _ _ := (ratioOn_mul_ratioOn (hi := inf_le_left) (hj := inf_le_right)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coord_f (k i : Fin (N + 1)) : (coord R N k).f i = ratio R N i k := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `⨆ i, (PSpace R N).basicOpen (ratio R N i k) = chart R N k`. Simplify using `only [ratio, basicOpen_ratioOn]`. Rewrite using `[← iSup_inf_eq, iSup_chart, top_inf_eq]`.
-/
theorem nonzeroLocus_coord (k : Fin (N + 1)) : nonzeroLocus (coord R N k) = (O1 R N).U k := by
  change ⨆ i, (PSpace R N).basicOpen (ratio R N i k) = chart R N k
  simp only [ratio, basicOpen_ratioOn]
  rw [← iSup_inf_eq, iSup_chart, top_inf_eq]

/- English proof (translation)
Simplify using `only [nonzeroLocus_coord]`. Conclude with `iSup_chart R N`.
-/
theorem iSup_nonzeroLocus_coord : ⨆ k, nonzeroLocus (coord R N k) = ⊤ := by
  simp only [nonzeroLocus_coord]
  exact iSup_chart R N

/- English proof (translation)
Simplify using `only [LB.LinComb, Fintype.prod_unique]`. Both sides reduce to the same expression.
-/
theorem linComb_punit_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℤ) (i j : PUnit → L.ι) :
    (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).g i j =
      res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => φ) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ => φ) j PUnit.unit)) :
          LB.wchart L (fun _ => φ) i ⊓ LB.wchart L (fun _ => φ) j ≤
            φ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)))
        (pullU φ _ (L.g (i PUnit.unit) (j PUnit.unit))) ^ n := by
  simp only [LB.LinComb, Fintype.prod_unique]
  rfl

abbrev On (n : ℤ) : LB (PSpace R N) :=
  LB.LinComb (O1 R N) (K := PUnit) (fun _ => 𝟙 (PSpace R N)) (fun _ => n)

/- English proof (translation)
The claim follows from `LB.isLB_linComb (O1_isLB R N) _ _`.
-/
theorem On_isLB (n : ℤ) : (On R N n).IsLB := LB.isLB_linComb (O1_isLB R N) _ _

/- English proof (translation)
The claim follows from `le_antisymm (LB.wchart_le (O1 R N) (fun _ => 𝟙 (PSpace R N)) j PUnit.unit) fun _ hx => Set.mem_iInter.2 fun _ => hx`.
-/
theorem On_U (n : ℤ) (j : PUnit → Fin (N + 1)) : (On R N n).U j = chart R N (j PUnit.unit) :=
  le_antisymm (LB.wchart_le (O1 R N) (fun _ => 𝟙 (PSpace R N)) j PUnit.unit)
    fun _ hx => Set.mem_iInter.2 fun _ => hx

/- English proof (translation)
The claim follows from `(linComb_punit_g (O1 R N) (𝟙 _) n i j).trans (congrArg (· ^ n) (Units.ext rfl))`.
-/
theorem On_g (n : ℤ) (i j : PUnit → Fin (N + 1)) :
    (On R N n).g i j = ratioUnit ((On R N n).U i ⊓ (On R N n).U j) (i PUnit.unit) (j PUnit.unit)
      (inf_le_left.trans (On_U R N n i).le) (inf_le_right.trans (On_U R N n j).le) ^ n :=
  (linComb_punit_g (O1 R N) (𝟙 _) n i j).trans (congrArg (· ^ n) (Units.ext rfl))

variable {R N}

def formSec (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    (lbPow (O1 R N) n).Sec where
  f j := formOn _ (j PUnit.unit) (On_U R N n j).le n f hf
  compat i j := by
    have e := On_g R N n i j
    rw [zpow_natCast] at e
    have e' := (congrArg Units.val e).trans (Units.val_pow_eq_pow_val _ _)
    exact (formOn_eq_ratioOn_pow_mul (hi := inf_le_left.trans (On_U R N n i).le)
      (inf_le_right.trans (On_U R N n j).le) hf).trans (congrArg (· * _) e'.symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem formSec_f (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n)
    (j : PUnit → Fin (N + 1)) :
    (formSec n f hf).f j = formOn _ (j PUnit.unit) (On_U R N n j).le n f hf := rfl

/- English proof (translation)
Establish `e : ∀ j, (PSpace R N).basicOpen ((formSec n f hf).f j) = (On R N n).U j ⊓ Proj.basicOpen (grading R N) f` using `fun j => basicOpen_formOn (hi := (On_U R N n j).le) hf`. Use `(iSup_congr e).trans ((iSup_inf_eq _ _).symm.trans ?_)` and prove the remaining obligations. Conclude with `(congrArg (· ⊓ _) (On_isLB R N n).cover).trans (top_inf_eq _)`.
-/
theorem nonzeroLocus_formSec (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    nonzeroLocus (formSec n f hf) = Proj.basicOpen (grading R N) f := by
  have e : ∀ j, (PSpace R N).basicOpen ((formSec n f hf).f j) =
      (On R N n).U j ⊓ Proj.basicOpen (grading R N) f := fun j =>
    basicOpen_formOn (hi := (On_U R N n j).le) hf
  refine (iSup_congr e).trans ((iSup_inf_eq _ _).symm.trans ?_)
  exact (congrArg (· ⊓ _) (On_isLB R N n).cover).trans (top_inf_eq _)

variable (R N)

@[instance_reducible]
scoped instance algebraSections (U : (PSpace R N).Opens) : Algebra R Γ(PSpace R N, U) :=
  (baseRingHom (PSpace.str R N) U).hom.toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_sections_eq (U : (PSpace R N).Opens) :
    algebraMap R Γ(PSpace R N, U) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (PSpace.str R N).appLE ⊤ U le_top).hom := rfl

variable {R N} in

/- English proof (translation)
The claim follows from `baseRingHom_res (PSpace.str R N) h r`.
-/
theorem resG_algebraMap {U V : (PSpace R N).Opens} (h : V ≤ U) (r : R) :
    resG _ h (algebraMap R Γ(PSpace R N, U) r) = algebraMap R Γ(PSpace R N, V) r :=
  baseRingHom_res (PSpace.str R N) h r

def constAway (i : Fin (N + 1)) : R →+* HomogeneousLocalization.Away (grading R N) (X i) :=
  (HomogeneousLocalization.fromZeroRingHom (grading R N) _).comp (algebraMap R (grading R N 0))

/- English proof (translation)
Establish `h` using `baseRingHom_comp_SpecMap (Proj.toSpecZero (grading R N)) (CommRingCat.ofHom (algebraMap R (grading R N 0))) (chart R N i)`. Establish `h'` using `ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading R N) (X_mem R N i) one_pos`. Rewrite `h` using `[baseRingHom.eq_1 (Proj.toSpecZero _), h']`. Conclude with `congrArg (fun φ => φ.hom r) h`.
-/
theorem algebraMap_chart (i : Fin (N + 1)) (r : R) :
    algebraMap R Γ(PSpace R N, chart R N i) r =
      (Proj.awayToSection (grading R N) (X i)).hom (constAway R N i r) := by
  have h := baseRingHom_comp_SpecMap (Proj.toSpecZero (grading R N))
    (CommRingCat.ofHom (algebraMap R (grading R N 0))) (chart R N i)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading R N) (X_mem R N i) one_pos
  rw [baseRingHom.eq_1 (Proj.toSpecZero _), h'] at h
  exact congrArg (fun φ => φ.hom r) h

variable {R N} in

/- English proof (translation)
Rewrite using `[← resG_algebraMap hi, algebraMap_chart]`. Both sides reduce to the same expression.
-/
theorem formOn_C {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} (r : R) :
    formOn U i hi 0 (C r) (isHomogeneous_C _ r) = algebraMap R Γ(PSpace R N, U) r := by
  rw [← resG_algebraMap hi, algebraMap_chart]
  rfl

def dehom (i : Fin (N + 1)) : MvPolynomial (Fin (N + 1)) R →ₐ[R] MvPolynomial {j // j ≠ i} R :=
  aeval fun j => if h : j = i then 1 else X ⟨j, h⟩

/- English proof (translation)
Simplify using `[dehom]`.
-/
@[simp] theorem dehom_X_self (i : Fin (N + 1)) : dehom R N i (X i) = 1 := by simp [dehom]

/- English proof (translation)
Simplify using `[dehom, j.2]`.
-/
@[simp] theorem dehom_X_of_ne (i : Fin (N + 1)) (j : {j // j ≠ i}) : dehom R N i (X j.1) = X j := by
  simp [dehom, j.2]

def ratioAway (i j : Fin (N + 1)) : HomogeneousLocalization.Away (grading R N) (X i) :=
  HomogeneousLocalization.Away.mk (grading R N) (X_mem R N i) 1 (X j) (X_mem R N j)

def polyToAway (i : Fin (N + 1)) :
    MvPolynomial {j // j ≠ i} R →+* HomogeneousLocalization.Away (grading R N) (X i) :=
  eval₂Hom (constAway R N i) fun j => ratioAway R N i j.1

def awayToPoly (i : Fin (N + 1)) :
    HomogeneousLocalization.Away (grading R N) (X i) →+* MvPolynomial {j // j ≠ i} R :=
  (IsLocalization.Away.lift (S := Localization.Away (X i : MvPolynomial (Fin (N + 1)) R)) (X i)
    (g := (dehom R N i).toRingHom) (by simp)).comp (algebraMap _ _)

/- English proof (translation)
Simplify using `only [awayToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift]`. Rewrite using `[IsLocalization.lift_mk'_spec]`. Simplify using the standard rewrite rules.
-/
theorem awayToPoly_mk (i : Fin (N + 1)) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f ∈ grading R N (n • 1)) :
    awayToPoly R N i (HomogeneousLocalization.Away.mk (grading R N) (X_mem R N i) n f hf) =
      dehom R N i f := by
  simp only [awayToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  simp

/- English proof (translation)
Set `L` to `Localization.Away (X i : MvPolynomial (Fin (N + 1)) R)`. Set `t : L` to `Localization.mk 1 ⟨X i, 1, pow_one _⟩`. Set `a` to `algebraMap (MvPolynomial (Fin (N + 1)) R) L`. Establish `h1 : ((algebraMap _ L).comp (polyToAway R N i)).comp (dehom R N i).toRingHom = eval₂Hom (a.comp C) (fun j => a (X j) * t)`. Use `ringHom_ext (fun r => ?_) (fun j => ?_)` and prove the remaining obligations.

Simplify using `[polyToAway, constAway]`. Both sides reduce to the same expression. Establish `e : a (X j) * t = Localization.mk (X j) (⟨X i ^ 1, 1, rfl⟩ : Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R))`. Rewrite using `[← Localization.mk_one_eq_algebraMap, Localization.mk_mul]`. Use `congr 1`.

Apply the tactic sequence `all_goals simp`. Rewrite using `[eval₂Hom_X', e]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehom_X_self, map_one]`.

Rewrite using `[eq_comm, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]`. Conclude with `⟨1, by simp⟩`. Use `dehom_X_of_ne R N i ⟨j, h⟩` as an intermediate fact. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this, polyToAway, eval₂Hom_X']`. Both sides reduce to the same expression.

Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Establish `h2` using `congrArg (fun φ => φ f) h1`. Establish `hf' : f.IsHomogeneous n` using `by simpa using hf`. Simplify using `only [coe_eval₂Hom, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hf'] at h2`. Establish `h3 : eval₂ (a.comp C) (fun j => a (X j)) f = a f`.

Use `eval₂_comp_left a C X f` as an intermediate fact. Rewrite `this` using `[eval₂_eta]`. Conclude with `this.symm`. Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[h3, HomogeneousLocalization.Away.val_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul]`.

Use `congr 1`. Simplify using the standard rewrite rules. Use `ext1`. Simplify using the standard rewrite rules.
-/
theorem polyToAway_dehom (i : Fin (N + 1)) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f ∈ grading R N (n • 1)) :
    polyToAway R N i (dehom R N i f) =
      HomogeneousLocalization.Away.mk (grading R N) (X_mem R N i) n f hf := by
  let L := Localization.Away (X i : MvPolynomial (Fin (N + 1)) R)
  let t : L := Localization.mk 1 ⟨X i, 1, pow_one _⟩
  let a := algebraMap (MvPolynomial (Fin (N + 1)) R) L
  have h1 : ((algebraMap _ L).comp (polyToAway R N i)).comp (dehom R N i).toRingHom =
      eval₂Hom (a.comp C) (fun j => a (X j) * t) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [polyToAway, constAway]
      rfl
    · have e : a (X j) * t = Localization.mk (X j) (⟨X i ^ 1, 1, rfl⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R)) := by
        rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
        congr 1
        all_goals simp
      rw [eval₂Hom_X', e]
      by_cases h : j = i
      · subst h
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehom_X_self, map_one]
        rw [eq_comm, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp⟩
      · have := dehom_X_of_ne R N i ⟨j, h⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this, polyToAway,
          eval₂Hom_X']
        rfl
  apply HomogeneousLocalization.val_injective
  have h2 := congrArg (fun φ => φ f) h1
  have hf' : f.IsHomogeneous n := by simpa using hf
  simp only [coe_eval₂Hom, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hf'] at h2
  have h3 : eval₂ (a.comp C) (fun j => a (X j)) f = a f := by
    have := eval₂_comp_left a C X f
    rw [eval₂_eta] at this
    exact this.symm
  refine h2.trans ?_
  rw [h3, HomogeneousLocalization.Away.val_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow,
    Localization.mk_mul]
  congr 1
  · simp
  · ext1; simp

def polyEquivAway (i : Fin (N + 1)) :
    MvPolynomial {j // j ≠ i} R ≃+* HomogeneousLocalization.Away (grading R N) (X i) where
  __ := polyToAway R N i
  invFun := awayToPoly R N i
  left_inv p := by
    have : (awayToPoly R N i).comp (polyToAway R N i) = RingHom.id _ := by
      refine ringHom_ext (fun r => ?_) (fun j => ?_)
      · have := awayToPoly_mk R N i 0 (C r) (isHomogeneous_C _ r)
        simp only [RingHom.comp_apply, polyToAway, eval₂Hom_C, RingHom.id_apply]
        exact this.trans (by simp)
      · simp only [RingHom.comp_apply, polyToAway, eval₂Hom_X', RingHom.id_apply, ratioAway]
        exact (awayToPoly_mk R N i 1 _ _).trans (dehom_X_of_ne R N i j)
    exact congrArg (fun φ => φ p) this
  right_inv x := by
    obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) x
    rw [awayToPoly_mk]
    exact polyToAway_dehom R N i n f hf

def chartAlgEquiv (i : Fin (N + 1)) :
    MvPolynomial {j // j ≠ i} R ≃ₐ[R] Γ(PSpace R N, chart R N i) where
  __ := (polyEquivAway R N i).trans
    (Proj.basicOpenIsoAway (grading R N) (X i) (X_mem R N i) one_pos).commRingCatIsoToRingEquiv
  commutes' r := by
    rw [algebraMap_chart]
    exact congrArg (Proj.awayToSection (grading R N) (X i)).hom (eval₂Hom_C _ _ r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chartAlgEquiv_apply (i : Fin (N + 1)) (p : MvPolynomial {j // j ≠ i} R) :
    chartAlgEquiv R N i p = (Proj.awayToSection (grading R N) (X i)).hom (polyToAway R N i p) := rfl

/- English proof (translation)
Rewrite using `[chartAlgEquiv_apply, polyToAway, eval₂Hom_X', ratioAway, awayToSection_mk]`. Conclude with `frac_eq (by ring)`.
-/
@[simp] theorem chartAlgEquiv_X (i : Fin (N + 1)) (j : {j // j ≠ i}) :
    chartAlgEquiv R N i (X j) = ratio R N i j.1 := by
  rw [chartAlgEquiv_apply, polyToAway, eval₂Hom_X', ratioAway, awayToSection_mk]
  exact frac_eq (by ring)

/- English proof (translation)
Rewrite using `[chartAlgEquiv_apply, polyToAway_dehom R N i n f (by simpa using hf), awayToSection_mk]`. Conclude with `frac_eq rfl`.
-/
theorem chartAlgEquiv_dehom (i : Fin (N + 1)) {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) :
    chartAlgEquiv R N i (dehom R N i f) = formOn (chart R N i) i le_rfl n f hf := by
  rw [chartAlgEquiv_apply, polyToAway_dehom R N i n f (by simpa using hf), awayToSection_mk]
  exact frac_eq rfl

variable {R N} in

/- English proof (translation)
Establish `h : ((resG _ hi).comp (RingHomClass.toRingHom (chartAlgEquiv R N i))).comp (RingHomClass.toRingHom (dehom R N i)) = RingHomClass.toRingHom (aeval (ratioOn U i hi) : MvPolynomial (Fin (N + 1)) R →ₐ[R] _)`. Use `ringHom_ext (fun r => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, algHom_C]`. Rewrite using `[AlgEquiv.commutes]`. Conclude with `resG_algebraMap hi r`.

Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, aeval_X]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Rewrite using `[dehom_X_self, map_one, map_one, ratioOn_self]`. Rewrite using `[dehom_X_of_ne R N i ⟨j, h⟩, chartAlgEquiv_X]`.

Both sides reduce to the same expression. Use `congrArg (fun φ => φ f) h` as an intermediate fact. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, chartAlgEquiv_dehom R N i hf] at this`. Conclude with `this`.
-/
theorem formOn_eq_aeval {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    formOn U i hi n f hf = aeval (ratioOn U i hi) f := by
  have h : ((resG _ hi).comp (RingHomClass.toRingHom (chartAlgEquiv R N i))).comp
      (RingHomClass.toRingHom (dehom R N i)) =
      RingHomClass.toRingHom (aeval (ratioOn U i hi) : MvPolynomial (Fin (N + 1)) R →ₐ[R] _) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, algHom_C]
      rw [AlgEquiv.commutes]
      exact resG_algebraMap hi r
    · simp only [RingHom.comp_apply, RingHom.coe_coe, aeval_X]
      by_cases h : j = i
      · subst h
        rw [dehom_X_self, map_one, map_one, ratioOn_self]
      · rw [dehom_X_of_ne R N i ⟨j, h⟩, chartAlgEquiv_X]
        rfl
  have := congrArg (fun φ => φ f) h
  simp only [RingHom.comp_apply, RingHom.coe_coe, chartAlgEquiv_dehom R N i hf] at this
  exact this

/- English proof (translation)
Use `⟨fun h => ?_, fun h => by subst h; rfl⟩` and prove the remaining obligations. Rewrite `h` using `[← chartAlgEquiv_dehom, ← chartAlgEquiv_dehom]`. Establish `h1` using `congrArg (fun p => (polyToAway R N i p).val) ((chartAlgEquiv R N i).injective h)`. Simplify `hf), polyToAway_dehom R N i n g (by simpa using hg), HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h1` using `only [polyToAway_dehom R N i n f (by simpa`. Take `⟨⟨_, m, rfl⟩, h1⟩` from `h1`.

Conclude with `((isRegular_X (n := i)).pow n).left (((isRegular_X (n := i)).pow m).left h1)`.
-/
theorem formOn_chart_inj (i : Fin (N + 1)) {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) :
    formOn (chart R N i) i le_rfl n f hf = formOn (chart R N i) i le_rfl n g hg ↔ f = g := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  rw [← chartAlgEquiv_dehom, ← chartAlgEquiv_dehom] at h
  have h1 := congrArg (fun p => (polyToAway R N i p).val) ((chartAlgEquiv R N i).injective h)
  simp only [polyToAway_dehom R N i n f (by simpa using hf), polyToAway_dehom R N i n g (by simpa using hg),
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h1
  obtain ⟨⟨_, m, rfl⟩, h1⟩ := h1
  exact ((isRegular_X (n := i)).pow n).left (((isRegular_X (n := i)).pow m).left h1)

variable {R N} in

/- English proof (translation)
Use `⟨fun h => (formOn_chart_inj R N 0 hf hg).1 ?_, fun h => by subst h; rfl⟩` and prove the remaining obligations. Conclude with `congrArg (fun s : (lbPow (O1 R N) n).Sec => resG _ (On_U R N n fun _ => 0).ge (s.f fun _ => (0 : Fin (N + 1)))) h`.
-/
theorem formSec_inj {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) : formSec n f hf = formSec n g hg ↔ f = g := by
  refine ⟨fun h => (formOn_chart_inj R N 0 hf hg).1 ?_, fun h => by subst h; rfl⟩
  exact congrArg (fun s : (lbPow (O1 R N) n).Sec => resG _ (On_U R N n fun _ => 0).ge (s.f fun _ => (0 : Fin (N + 1)))) h

/- English proof (translation)
Introduce `s`. Take `⟨p, rfl⟩` from `(chartAlgEquiv R N i).surjective s`. Use `⟨rename Subtype.val p, ?_⟩` and prove the remaining obligations. Establish `: (aeval (R` using `R) (ratio R N i)).comp (rename Subtype.val) = (chartAlgEquiv R N i).toAlgHom := algHom_ext fun j => by simp`. Conclude with `congrArg (fun φ => φ p) this`.
-/
theorem aeval_ratio_surjective (i : Fin (N + 1)) :
    Function.Surjective (aeval (R := R) (ratio R N i)) := by
  intro s
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N i).surjective s
  refine ⟨rename Subtype.val p, ?_⟩
  have : (aeval (R := R) (ratio R N i)).comp (rename Subtype.val) = (chartAlgEquiv R N i).toAlgHom :=
    algHom_ext fun j => by simp
  exact congrArg (fun φ => φ p) this

def chartι (i : Fin (N + 1)) : Sp (MvPolynomial {j // j ≠ i} R) ⟶ PSpace R N :=
  spMap (awayToPoly R N i) ≫ Proj.awayι (grading R N) (X i) (X_mem R N i) one_pos

instance isIso_spMap_awayToPoly (i : Fin (N + 1)) : IsIso (spMap (awayToPoly R N i)) :=
  inferInstanceAs (IsIso (Spec.map (polyEquivAway R N i).toCommRingCatIso.inv))

instance isOpenImmersion_chartι (i : Fin (N + 1)) : IsOpenImmersion (chartι R N i) := by
  unfold chartι
  infer_instance

/- English proof (translation)
The claim follows from `(Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)`.
-/
theorem opensRange_chartι (i : Fin (N + 1)) : (chartι R N i).opensRange = chart R N i :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)

/- English proof (translation)
Rewrite using `[chartι, PSpace.str, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use `ext1`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Conclude with `(awayToPoly_mk R N i 0 (C r) (isHomogeneous_C _ r)).trans (by simp)`.
-/
theorem chartι_str (i : Fin (N + 1)) :
    chartι R N i ≫ PSpace.str R N = spMap (C : R →+* MvPolynomial {j // j ≠ i} R) := by
  rw [chartι, PSpace.str, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  refine RingHom.ext fun r => ?_
  exact (awayToPoly_mk R N i 0 (C r) (isHomogeneous_C _ r)).trans (by simp)

def chartCover : (PSpace R N).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (N + 1)) (fun i => Sp (MvPolynomial {j // j ≠ i} R)) (chartι R N)
    fun x => by
      obtain ⟨i, hi⟩ := exists_mem_chart R N x
      rw [← opensRange_chartι] at hi
      exact ⟨i, hi⟩

section BaseChange

variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')

def gradedMap : grading R N →+*ᵍ grading R' N where
  __ := MvPolynomial.map φ
  map_mem hf := IsHomogeneous.map hf φ

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem gradedMap_apply (f : MvPolynomial (Fin (N + 1)) R) :
    gradedMap N φ f = MvPolynomial.map φ f := rfl

/- English proof (translation)
Use `(irrelevant_le_span_X R' N).trans (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← map_X φ i]`. Conclude with `Ideal.mem_map_of_mem (gradedMap N φ).toRingHom (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem R N i))`.
-/
theorem irrelevant_le_map : HomogeneousIdeal.irrelevant (grading R' N) ≤
    (HomogeneousIdeal.irrelevant (grading R N)).map (gradedMap N φ) := by
  refine (irrelevant_le_span_X R' N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  rw [← map_X φ i]
  exact Ideal.mem_map_of_mem (gradedMap N φ).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem R N i))

def baseChange : PSpace R' N ⟶ PSpace R N :=
  Proj.map (gradedMap N φ) (irrelevant_le_map N φ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem baseChange_preimage_basicOpen (f : MvPolynomial (Fin (N + 1)) R) :
    baseChange N φ ⁻¹ᵁ Proj.basicOpen (grading R N) f =
      Proj.basicOpen (grading R' N) (MvPolynomial.map φ f) := rfl

/- English proof (translation)
Rewrite using `[chart, baseChange_preimage_basicOpen, map_X]`.
-/
theorem baseChange_preimage_chart (i : Fin (N + 1)) :
    baseChange N φ ⁻¹ᵁ chart R N i = chart R' N i := by
  rw [chart, baseChange_preimage_basicOpen, map_X]

variable {N} in

/- English proof (translation)
Introduce `_ hx` and use `(baseChange_preimage_chart N φ i).le (hi hx)`.
-/
theorem baseChange_preimage_le {U : (PSpace R N).Opens} {i : Fin (N + 1)} (hi : U ≤ chart R N i) :
    baseChange N φ ⁻¹ᵁ U ≤ chart R' N i :=
  fun _ hx => (baseChange_preimage_chart N φ i).le (hi hx)

variable {N} in

/- English proof (translation)
The claim follows from `(map_app_frac (gradedMap N φ) (irrelevant_le_map N φ) U _ _ _ _ hi).trans (frac_eq (by simp))`.
-/
theorem baseChange_app_ratioOn {U : (PSpace R N).Opens} {i : Fin (N + 1)} (hi : U ≤ chart R N i)
    (j : Fin (N + 1)) :
    ((baseChange N φ).app U).hom (ratioOn U i hi j) =
      ratioOn (baseChange N φ ⁻¹ᵁ U) i (baseChange_preimage_le φ hi) j :=
  (map_app_frac (gradedMap N φ) (irrelevant_le_map N φ) U _ _ _ _ hi).trans (frac_eq (by simp))

variable {N} in

/- English proof (translation)
The claim follows from `(map_app_frac (gradedMap N φ) (irrelevant_le_map N φ) U _ _ _ _ (le_basicOpen_X_pow hi n)).trans (frac_eq (by simp))`.
-/
theorem baseChange_app_formOn {U : (PSpace R N).Opens} {i : Fin (N + 1)} (hi : U ≤ chart R N i)
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    ((baseChange N φ).app U).hom (formOn U i hi n f hf) =
      formOn (baseChange N φ ⁻¹ᵁ U) i (baseChange_preimage_le φ hi) n (MvPolynomial.map φ f) (hf.map φ) :=
  (map_app_frac (gradedMap N φ) (irrelevant_le_map N φ) U _ _ _ _ (le_basicOpen_X_pow hi n)).trans
    (frac_eq (by simp))

variable {N} in

/- English proof (translation)
The claim follows from `Units.ext (baseChange_app_ratioOn φ hi j)`.
-/
theorem pullU_baseChange_ratioUnit {U : (PSpace R N).Opens} {i j : Fin (N + 1)} (hi : U ≤ chart R N i)
    (hj : U ≤ chart R N j) :
    pullU (baseChange N φ) U (ratioUnit U i j hi hj) =
      ratioUnit (baseChange N φ ⁻¹ᵁ U) i j (baseChange_preimage_le φ hi) (baseChange_preimage_le φ hj) :=
  Units.ext (baseChange_app_ratioOn φ hi j)

/- English proof (translation)
Establish `key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (hs : s = X i) (hd : s ∈ grading R' N 1), ∃ ψ : HomogeneousLocalization.Away (grading R' N) s →+* MvPolynomial {j // j ≠ i} R', chartι R' N i = spMap ψ ≫ Proj.awayι (grading R' N) s hd one_pos ∧ ∀ n f hf, ψ (HomogeneousLocalization.Away …`. Introduce and unpack `_ rfl hd`. Conclude with `⟨awayToPoly R' N i, rfl, awayToPoly_mk R' N i⟩`. Take `⟨ψ, h1, h2⟩` from `key (gradedMap N φ (X i)) (map_X φ i) ((gradedMap N φ).2 (X_mem R N i))`. Rewrite using `[h1, Category.assoc, baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N i), chartι, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]`.

Use `congr 2`. Use `ext1`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨n, f, hf, rfl⟩` from `HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) x`. Express the relevant statement in the definitionally equal form `ψ (HomogeneousLocalization.Away.map (gradedMap N φ) (X i) _) = MvPolynomial.map φ (awayToPoly R N i _)`.

Rewrite using `[HomogeneousLocalization.Away.map_mk, h2, awayToPoly_mk]`. Establish `: (RingHomClass.toRingHom (dehom R' N i)).comp (MvPolynomial.map φ) = (MvPolynomial.map φ).comp (RingHomClass.toRingHom (dehom R N i))`. Use `ringHom_ext (fun r => by simp) (fun j => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : j = i <;> simp [dehom, h]`. Conclude with `congrArg (fun φ => φ f) this`.
-/
theorem chartι_baseChange (i : Fin (N + 1)) :
    chartι R' N i ≫ baseChange N φ =
      spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _) ≫ chartι R N i := by
  have key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (hs : s = X i) (hd : s ∈ grading R' N 1),
      ∃ ψ : HomogeneousLocalization.Away (grading R' N) s →+* MvPolynomial {j // j ≠ i} R',
        chartι R' N i = spMap ψ ≫ Proj.awayι (grading R' N) s hd one_pos ∧
        ∀ n f hf, ψ (HomogeneousLocalization.Away.mk (grading R' N) hd n f hf) = dehom R' N i f := by
    rintro _ rfl hd
    exact ⟨awayToPoly R' N i, rfl, awayToPoly_mk R' N i⟩
  obtain ⟨ψ, h1, h2⟩ := key (gradedMap N φ (X i)) (map_X φ i) ((gradedMap N φ).2 (X_mem R N i))
  rw [h1, Category.assoc, baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N i), chartι,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext1
  refine RingHom.ext fun x => ?_
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) x
  change ψ (HomogeneousLocalization.Away.map (gradedMap N φ) (X i) _) =
    MvPolynomial.map φ (awayToPoly R N i _)
  rw [HomogeneousLocalization.Away.map_mk, h2, awayToPoly_mk]
  have : (RingHomClass.toRingHom (dehom R' N i)).comp (MvPolynomial.map φ) =
      (MvPolynomial.map φ).comp (RingHomClass.toRingHom (dehom R N i)) := by
    refine ringHom_ext (fun r => by simp) (fun j => ?_)
    by_cases h : j = i <;> simp [dehom, h]
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Use `Scheme.isPullback_of_openCover _ _ _ _ (chartCover R N) fun (i : Fin (N + 1)) => ?_` and prove the remaining obligations. Establish `h1 : IsPullback (chartι R' N i) (spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _)) (baseChange N φ) (chartι R N i)` using `(IsOpenImmersion.isPullback _ _ _ _ (chartι_baseChange N φ i) (by rw [opensRange_chartι, opensRange_chartι, baseChange_preimage_chart])).flip`. Establish `h2 : IsPullback (spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _)) (chartι R' N i ≫ PSpace.str R' N) (chartι R N i ≫ PSpace.str R N) (spMap φ)`. Rewrite using `[chartι_str, chartι_str]`. Use `letI := φ.toAlgebra`.

Use `letI := MvPolynomial.algebraMvPolynomial (σ := {j // j ≠ i}) (R := R) (S := R')`. Conclude with `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R (MvPolynomial {j // j ≠ i} R) R' (MvPolynomial {j // j ≠ i} R'))`. Conclude with `h2.of_iso h1.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (h1.isoPullback_hom_snd).symm) ((Category.comp_id _).trans (h1.isoPullback_hom_fst_assoc _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans (Catego …`.
-/
theorem isPullback_baseChange :
    IsPullback (baseChange N φ) (PSpace.str R' N) (PSpace.str R N) (spMap φ) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (chartCover R N) fun (i : Fin (N + 1)) => ?_
  have h1 : IsPullback (chartι R' N i) (spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _))
      (baseChange N φ) (chartι R N i) :=
    (IsOpenImmersion.isPullback _ _ _ _ (chartι_baseChange N φ i)
      (by rw [opensRange_chartι, opensRange_chartι, baseChange_preimage_chart])).flip
  have h2 : IsPullback (spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _))
      (chartι R' N i ≫ PSpace.str R' N) (chartι R N i ≫ PSpace.str R N) (spMap φ) := by
    rw [chartι_str, chartι_str]
    letI := φ.toAlgebra
    letI := MvPolynomial.algebraMvPolynomial (σ := {j // j ≠ i}) (R := R) (S := R')
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout R (MvPolynomial {j // j ≠ i} R) R' (MvPolynomial {j // j ≠ i} R'))
  exact h2.of_iso h1.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (h1.isoPullback_hom_snd).symm)
    ((Category.comp_id _).trans (h1.isoPullback_hom_fst_assoc _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/- English proof (translation)
The claim follows from `(isPullback_baseChange N φ).w`.
-/
theorem baseChange_str : baseChange N φ ≫ PSpace.str R N = PSpace.str R' N ≫ spMap φ :=
  (isPullback_baseChange N φ).w

/- English proof (translation)
The claim follows from `le_antisymm ((LB.wchart_le (O1 R N) (fun _ => baseChange N φ) j PUnit.unit).trans (baseChange_preimage_chart N φ _).le) fun _ hx => Set.mem_iInter.2 fun _ => (baseChange_preimage_chart N φ _).ge hx`.
-/
theorem pull_O1_chart (j : PUnit → Fin (N + 1)) :
    ((O1 R N).pull (baseChange N φ)).U j = chart R' N (j PUnit.unit) :=
  le_antisymm ((LB.wchart_le (O1 R N) (fun _ => baseChange N φ) j PUnit.unit).trans
      (baseChange_preimage_chart N φ _).le)
    fun _ hx => Set.mem_iInter.2 fun _ => (baseChange_preimage_chart N φ _).ge hx

/- English proof (translation)
The claim follows from `(linComb_punit_g (O1 R N) (baseChange N φ) 1 i j).trans ((zpow_one _).trans (congrArg (res _) (pullU_baseChange_ratioUnit φ inf_le_left inf_le_right)))`.
-/
theorem pullback_O1_transition_eq_blockUnit (i j : PUnit → Fin (N + 1)) :
    ((O1 R N).pull (baseChange N φ)).g i j =
      ratioUnit (((O1 R N).pull (baseChange N φ)).U i ⊓ ((O1 R N).pull (baseChange N φ)).U j)
        (i PUnit.unit) (j PUnit.unit) (inf_le_left.trans (pull_O1_chart N φ i).le)
        (inf_le_right.trans (pull_O1_chart N φ j).le) :=
  (linComb_punit_g (O1 R N) (baseChange N φ) 1 i j).trans ((zpow_one _).trans
    (congrArg (res _) (pullU_baseChange_ratioUnit φ inf_le_left inf_le_right)))

def baseChangeIso : LB.Iso ((O1 R N).pull (baseChange N φ)) (O1 R' N) where
  s p := ratioUnit _ p.1 (p.2 PUnit.unit) inf_le_left (inf_le_right.trans (pull_O1_chart N φ p.2).le)

/- English proof (translation)
Introduce and unpack `⟨i, j⟩ ⟨i', j'⟩`. Simplify using `only [LB.div, O1_g_eq_ratioUnit_chart_inf, baseChangeIso]`. Use `erw [pullback_O1_transition_eq_blockUnit, res_ratioUnit, res_ratioUnit, res_ratioUnit, res_ratioUnit]`. Use `erw [inv_ratioUnit, mul_right_comm, ratioUnit_mul_ratioUnit, ratioUnit_mul_ratioUnit]`.
-/
theorem baseChangeIso_isGen : (baseChangeIso N φ).IsGen := by
  rintro ⟨i, j⟩ ⟨i', j'⟩
  simp only [LB.div, O1_g_eq_ratioUnit_chart_inf, baseChangeIso]
  erw [pullback_O1_transition_eq_blockUnit, res_ratioUnit, res_ratioUnit, res_ratioUnit, res_ratioUnit]
  erw [inv_ratioUnit, mul_right_comm, ratioUnit_mul_ratioUnit, ratioUnit_mul_ratioUnit]

/- English proof (translation)
Assemble the required witnesses or components as `⟨baseChangeIso N φ, baseChangeIso_isGen N φ⟩`.
-/
theorem lbIso_pull_O1 : LBIso ((O1 R N).pull (baseChange N φ)) (O1 R' N) :=
  ⟨baseChangeIso N φ, baseChangeIso_isGen N φ⟩

/- English proof (translation)
Establish `e` using `baseChange_app_ratioOn φ (le_refl (chart R N (j PUnit.unit))) k`. Conclude with `(ratioOn_mul_ratioOn (hi := inf_le_left) (hj := inf_le_right.trans (pull_O1_chart N φ j).le)).symm.trans (congrArg (_ * resG _ _ ·) e.symm)`.
-/
theorem baseChangeIso_coord (k i : Fin (N + 1)) (j : PUnit → Fin (N + 1)) :
    resG _ (inf_le_left : (O1 R' N).U i ⊓ ((O1 R N).pull (baseChange N φ)).U j ≤ _) ((coord R' N k).f i) =
      ((baseChangeIso N φ).s (i, j)).val *
        resG _ (inf_le_right.trans (LB.wchart_le (O1 R N) (fun _ => baseChange N φ) j PUnit.unit))
          (((baseChange N φ).app ((O1 R N).U (j PUnit.unit))).hom ((coord R N k).f (j PUnit.unit))) := by
  have e := baseChange_app_ratioOn φ (le_refl (chart R N (j PUnit.unit))) k
  exact (ratioOn_mul_ratioOn (hi := inf_le_left)
    (hj := inf_le_right.trans (pull_O1_chart N φ j).le)).symm.trans (congrArg (_ * resG _ _ ·) e.symm)

/- English proof (translation)
Use `(chartCover R N).hom_ext _ _ fun (i : Fin (N + 1)) => ?_` and prove the remaining obligations. Use `(chartι_baseChange N (RingHom.id R) i).trans ?_` and prove the remaining obligations. Establish `: (MvPolynomial.map (RingHom.id R) : MvPolynomial {j // j ≠ i} R →+* _) = RingHom.id _` using `RingHom.ext map_id`. Rewrite using `[this]`. Conclude with `(congrArg (· ≫ _) (Spec.map_id _)).trans ((Category.id_comp _).trans (Category.comp_id _).symm)`.
-/
theorem baseChange_id : baseChange N (RingHom.id R) = 𝟙 (PSpace R N) := by
  refine (chartCover R N).hom_ext _ _ fun (i : Fin (N + 1)) => ?_
  refine (chartι_baseChange N (RingHom.id R) i).trans ?_
  have : (MvPolynomial.map (RingHom.id R) : MvPolynomial {j // j ≠ i} R →+* _) = RingHom.id _ :=
    RingHom.ext map_id
  rw [this]
  exact (congrArg (· ≫ _) (Spec.map_id _)).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

/- English proof (translation)
Use `(chartCover R'' N).hom_ext _ _ fun (i : Fin (N + 1)) => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `chartι R'' N i ≫ _ = chartι R'' N i ≫ _`. Rewrite using `[chartι_baseChange, ← Category.assoc, chartι_baseChange, Category.assoc, chartι_baseChange, ← Spec.map_comp_assoc]`. Establish `: (MvPolynomial.map (ψ.comp φ) : MvPolynomial {j // j ≠ i} R →+* _) = (MvPolynomial.map ψ).comp (MvPolynomial.map φ)` using `RingHom.ext fun p => (map_map φ ψ p).symm`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem baseChange_comp {R'' : Type} [CommRing R''] (ψ : R' →+* R'') :
    baseChange N (ψ.comp φ) = baseChange N ψ ≫ baseChange N φ := by
  refine (chartCover R'' N).hom_ext _ _ fun (i : Fin (N + 1)) => ?_
  change chartι R'' N i ≫ _ = chartι R'' N i ≫ _
  rw [chartι_baseChange, ← Category.assoc, chartι_baseChange, Category.assoc, chartι_baseChange,
    ← Spec.map_comp_assoc]
  have : (MvPolynomial.map (ψ.comp φ) : MvPolynomial {j // j ≠ i} R →+* _) =
      (MvPolynomial.map ψ).comp (MvPolynomial.map φ) := RingHom.ext fun p => (map_map φ ψ p).symm
  rw [this]
  rfl

end BaseChange

/- English proof (translation)
Assemble the required witnesses or components as `⟨(chartAlgEquiv_X R 1 0 ⟨1, by decide⟩).symm, ratioOn_self (hi := le_rfl), rfl⟩`.
-/
example : (coord R 1 1).f (0 : Fin 2) = chartAlgEquiv R 1 0 (X ⟨1, by decide⟩) ∧
    (coord R 1 1).f (1 : Fin 2) = 1 ∧
    ((O1 R 1).g (0 : Fin 2) (1 : Fin 2)).val = resG _ inf_le_left ((coord R 1 1).f (0 : Fin 2)) :=
  ⟨(chartAlgEquiv_X R 1 0 ⟨1, by decide⟩).symm, ratioOn_self (hi := le_rfl), rfl⟩

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[nonzeroLocus_coord]`. Establish `h1 : (PSpace R 1).basicOpen (ratio R 1 0 1) = chart R 1 0` using `basicOpen_ratioOn.trans ((congrArg (_ ⊓ ·) h).trans (inf_top_eq _))`. Establish `h2 : IsUnit (ratio R 1 0 1)` using `(PSpace R 1).toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ((PSpace R 1).mem_basicOpen _ x hx).1 (h1.ge hx)`. Rewrite `h2` using `[← chartAlgEquiv_X R 1 0 ⟨1, by decide⟩]`.

Establish `h3` using `(h2.map (chartAlgEquiv R 1 0).symm).map constantCoeff`. Rewrite `h3` using `[AlgEquiv.symm_apply_apply, constantCoeff_X]`. Conclude with `not_isUnit_zero h3`.
-/
example [Nontrivial R] : nonzeroLocus (coord R 1 1) ≠ ⊤ := by
  intro h
  rw [nonzeroLocus_coord] at h
  have h1 : (PSpace R 1).basicOpen (ratio R 1 0 1) = chart R 1 0 :=
    basicOpen_ratioOn.trans ((congrArg (_ ⊓ ·) h).trans (inf_top_eq _))
  have h2 : IsUnit (ratio R 1 0 1) := (PSpace R 1).toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx =>
    ((PSpace R 1).mem_basicOpen _ x hx).1 (h1.ge hx)
  rw [← chartAlgEquiv_X R 1 0 ⟨1, by decide⟩] at h2
  have h3 := (h2.map (chartAlgEquiv R 1 0).symm).map constantCoeff
  rw [AlgEquiv.symm_apply_apply, constantCoeff_X] at h3
  exact not_isUnit_zero h3

/- English proof (translation)
Rewrite using `[formOn_eq_aeval]`. Simplify using the standard rewrite rules.
-/
example (h : (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) R).IsHomogeneous 2) :
    formOn (chart R 2 0) 0 le_rfl 2 (X 0 * X 1 - X 2 ^ 2) h = ratio R 2 0 1 - ratio R 2 0 2 ^ 2 := by
  rw [formOn_eq_aeval]
  simp

end GlobalTheory.ProjSpace
