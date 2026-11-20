import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriods
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisRingHomBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisDiscRingHomExtOfAinfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RegularPeriodsFiltration

/- English proof (translation)
Establish `hcn : ∀ (n : ℕ) y, c ^ n * y = 0 → y = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Simplify using `using hy`.

Consider the case `succ n ih => intro y hy; exact ih y (hc _ (by rw [← mul_assoc, ← pow_succ']; exact hy))`. Establish `hdet : A.det * B.det = c ^ d`. Rewrite using `[← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `hreg : ∀ y, A.det * y = 0 → y = 0` using `fun y hy => hcn d y (by rw [← hdet, mul_comm A.det, mul_assoc, hy, mul_zero])`. Establish `h1 : A.det • B = c • A.adjugate`.

Rewrite using `[← Matrix.one_mul B, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]`. Establish `h2 : A.det • (B * A) = A.det • (c • (1 : Matrix (Fin d) (Fin d) R))`. Rewrite using `[← Matrix.smul_mul, h1, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_comm]`. Use extensionality with `i j`. Use `congrFun (congrFun h2 i) j` as an intermediate fact.

Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this ⊢`. Conclude with `sub_eq_zero.1 (hreg _ (by rw [mul_sub, this, sub_self]))`.
-/
theorem mul_comm_of_regular {R : Type} [CommRing R] {d : ℕ} {A B : Matrix (Fin d) (Fin d) R} {c : R}
    (hc : ∀ y, c * y = 0 → y = 0) (h : A * B = c • (1 : Matrix (Fin d) (Fin d) R)) :
    B * A = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hcn : ∀ (n : ℕ) y, c ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; exact ih y (hc _ (by rw [← mul_assoc, ← pow_succ']; exact hy))
  have hdet : A.det * B.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hreg : ∀ y, A.det * y = 0 → y = 0 := fun y hy =>
    hcn d y (by rw [← hdet, mul_comm A.det, mul_assoc, hy, mul_zero])
  have h1 : A.det • B = c • A.adjugate := by
    rw [← Matrix.one_mul B, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, h, Matrix.mul_smul,
      Matrix.mul_one]
  have h2 : A.det • (B * A) = A.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    rw [← Matrix.smul_mul, h1, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_comm]
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this ⊢
  exact sub_eq_zero.1 (hreg _ (by rw [mul_sub, this, sub_self]))

end GlobalTheory.BSP.RegularPeriodsFiltration

namespace GlobalTheory.BSP.RegularPeriodsFiltration

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `he` using `GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C`. Take `⟨hfil, hreg, -, -⟩` from `GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he`. Take `⟨-, hker, hunit, -, -⟩` from `GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l`. Take `⟨-, ht1, ht2, -⟩` from `GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C`. Take `⟨-, hjσ, -⟩` from `GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris`.

Use `set ξ := aDp l (xi C.ε) with hξ`. Take `⟨u, hu⟩` from `(hfil 1 _).1 ht1`. Rewrite `hu` using `[pow_one]`. Establish `huu : IsUnit u` using `hunit u fun h0 => ht2 (by`. Take `⟨v, hv⟩` from `(hfil 1 u).1 ((hker u).1 h0)`.

Conclude with `(hfil 2 _).2 ⟨v, by rw [hu, hv]; ring⟩)`. Take `⟨ui, hui⟩` from `huu.exists_right_inv`. Take `⟨c, c', hc, hcc'⟩` from `GlobalTheory.MemLoc.FilLaws.σDp_xi C.ε he g`. Establish `hregn : ∀ (n : ℕ) (y : Per.BdRp l), ξ ^ n * y = 0 → y = 0`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ n ih => intro y hy; exact ih y (hreg _ (by rw [← mul_assoc, ← pow_succ']; exact hy))`. Establish `hσt : Per.σDp g (C.j C.t) = ξ * (c * Per.σDp g u)` using `by rw [hu, map_mul, hc, mul_assoc]`.

Establish `hJZZ : Z.map C.j * Z'.map C.j = C.j C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l))`. Use `congrArg (Matrix.map · C.j) hZZ` as an intermediate fact. Simplify using `only [Matrix.map_mul, GlobalTheory.BSP.SeedAsm.map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_pow] at this`. Conclude with `this`. Establish `htreg : ∀ y, C.j C.t ^ (2 * N) * y = 0 → y = 0` using `fun y hy => by`.

Establish `h3 : ξ ^ (2 * N) * (u ^ (2 * N) * y) = 0` using `by rw [← mul_assoc, ← mul_pow, ← hu]; exact hy`. Establish `h4` using `hregn _ _ h3`. Establish `h5 : (ui ^ (2 * N) * u ^ (2 * N)) * y = 0` using `by rw [mul_assoc, h4, mul_zero]`. Rewrite `h5` using `[← mul_pow, mul_comm ui, hui, one_pow, one_mul]`. Then use the resulting hypothesis. Establish `hJZ'Z` using `mul_comm_of_regular htreg hJZZ`.

Establish `hσZ : (Z.map (sigA g)).map C.j = (Z.map C.j).map (Per.σDp g)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Conclude with `hjσ g _`. Establish `hσX : (XA.map (sigA g)).map C.j = (XA.map C.j).map (Per.σDp g)`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Conclude with `hjσ g _`. Establish `eY : ∀ i j, C.j ((X'A * κm * XA.map (sigA g)) i j) = (X'A.map C.j * κm.map C.j * (XA.map C.j).map (Per.σDp g)) i j` using `fun i j => by`. Rewrite using `[← Matrix.map_apply (f := C.j), Matrix.map_mul, Matrix.map_mul, hσX]`.

Establish `hgJ` using `congrArg (Matrix.map · C.j) hg`. Simplify using `only [Matrix.map_mul, GlobalTheory.BSP.SeedAsm.map_smul_hom, map_mul, map_pow, map_natCast, hσZ, hjσ] at hgJ`. Use `set ZJ := Z.map C.j`. Use `set Z'J := Z'.map C.j`. Use `set XJ := XA.map C.j`.

Use `set X'J := X'A.map C.j`. Use `set RJ := R.map C.j`. Use `set κJ := κm.map C.j`. Establish `key : (C.j C.t ^ N * (l : Per.BdRp l) ^ k₀) • (X'J * Z'J * RJ * (ZJ * XJ).map (Per.σDp g)) = (Per.σDp g (C.j C.t) ^ N * C.j C.t ^ (2 * N)) • (X'J * κJ * XJ.map (Per.σDp g))`. Establish `e1 : X'J * Z'J * ((C.j C.t ^ N * (l : Per.BdRp l) ^ k₀) • (RJ * ZJ.map (Per.σDp g))) * XJ.map (Per.σDp g) = X'J * Z'J * (Per.σDp g (C.j C.t) ^ N • (ZJ * κJ)) * XJ.map (Per.σDp g)` using `by rw [hgJ]`.

Rewrite using `[Matrix.map_mul]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at e1 ⊢`. Rewrite using `[e1, ← Matrix.mul_assoc Z'J ZJ, hJZ'Z, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]`. Establish `hA : ∀ a b, ξ ^ (2 * N) ∣ ((X'A * Z').map C.j) a b` using `fun a b => (hfil _ _).1 (hf2 a b)`. Establish `hB : ∀ a b, ξ ^ (2 * N) ∣ ((ZJ * XJ).map (Per.σDp g)) a b` using `fun a b => by`.

Establish `e : ((ZJ * XJ).map (Per.σDp g)) a b = Per.σDp g (C.j ((Z * XA) a b))` using `by show Per.σDp g ((Z.map C.j * XA.map C.j) a b) = _`. Rewrite using `[← Matrix.map_mul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(hfil _ _).1 (GlobalTheory.MemLoc.FilLaws.σDp_mem_FilP g _ _ (hf1 a b))`.

Use `choose A0 hA0 using hA`. Use `choose B0 hB0 using hB`. Establish `eA : X'J * Z'J = ξ ^ (2 * N) • Matrix.of A0` using `by show X'A.map C.j * Z'.map C.j = _`. Rewrite using `[← Matrix.map_mul]`. Use extensionality with `a b`.

Conclude with `hA0 a b`. Establish `eB : (ZJ * XJ).map (Per.σDp g) = ξ ^ (2 * N) • Matrix.of B0`. Use extensionality with `a b`. Conclude with `hB0 a b`. Rewrite `key` using `[eA, eB]`.

Introduce `i j`. Establish `key2` using `congrFun (congrFun key i) j`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul] at key2`. Rewrite `key2` using `[hσt, hu]`. Rewrite using `[eY, hfil]`.

Use `set Y := (X'J * κJ * XJ.map (Per.σDp g)) i j`. Use `set P := (Matrix.of A0 * RJ * Matrix.of B0) i j`. Establish `hσu : Per.σDp g u * Per.σDp g ui = 1` using `by rw [← map_mul, hui, map_one]`. Use `set v := (c * Per.σDp g u) ^ N * u ^ (2 * N)`. Use `set v' := (c' * Per.σDp g ui) ^ N * ui ^ (2 * N)`.

Establish `hvv : v * v' = 1`. Rewrite using `[show v * v' = (c * c') ^ N * (Per.σDp g u * Per.σDp g ui) ^ N * (u * ui) ^ (2 * N) by ring, hcc', hσu, hui]`. Simplify using the standard rewrite rules. Use `⟨u ^ N * (l : Per.BdRp l) ^ k₀ * P * v', ?_⟩` and prove the remaining obligations. Establish `h0 : ξ ^ (3 * N) * (v * (Y - ξ ^ (2 * N) * (u ^ N * (l : Per.BdRp l) ^ k₀ * P * v'))) = 0`.

Take the linear combination `(-1 : Per.BdRp l) * key2 - (ξ ^ (5 * N) * u ^ N * (l : Per.BdRp l) ^ k₀ * P) * hvv`. Establish `h1` using `hregn _ _ h0`. Establish `h2 : Y - ξ ^ (2 * N) * (u ^ N * (l : Per.BdRp l) ^ k₀ * P * v') = 0`. Take the linear combination `v' * h1 - (Y - ξ ^ (2 * N) * (u ^ N * (l : Per.BdRp l) ^ k₀ * P * v')) * hvv`. Take the linear combination `h2`.
-/
theorem fil_nopole (C : Core l) {d N k₀ : ℕ} (g : GQ l) (R Z Z' XA X'A κm : Matrix (Fin d) (Fin d) (Per.Acris l))
    (hZZ : Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)))
    (hg : (C.t ^ N * (l : Per.Acris l) ^ k₀) • (R * Z.map (sigA g)) = sigA g C.t ^ N • (Z * κm))
    (hf1 : ∀ i j, C.j ((Z * XA) i j) ∈ Per.FilP l (2 * N))
    (hf2 : ∀ i j, C.j ((X'A * Z') i j) ∈ Per.FilP l (2 * N)) :
    ∀ i j, C.j ((X'A * κm * XA.map (sigA g)) i j) ∈ Per.FilP l (2 * N) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨hfil, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  set ξ := aDp l (xi C.ε) with hξ
  obtain ⟨u, hu⟩ := (hfil 1 _).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := hunit u fun h0 => ht2 (by
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 _).2 ⟨v, by rw [hu, hv]; ring⟩)
  obtain ⟨ui, hui⟩ := huu.exists_right_inv
  obtain ⟨c, c', hc, hcc'⟩ := GlobalTheory.MemLoc.FilLaws.σDp_xi C.ε he g
  have hregn : ∀ (n : ℕ) (y : Per.BdRp l), ξ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; exact ih y (hreg _ (by rw [← mul_assoc, ← pow_succ']; exact hy))
  have hσt : Per.σDp g (C.j C.t) = ξ * (c * Per.σDp g u) := by rw [hu, map_mul, hc, mul_assoc]

  have hJZZ : Z.map C.j * Z'.map C.j = C.j C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    have := congrArg (Matrix.map · C.j) hZZ
    simp only [Matrix.map_mul, GlobalTheory.BSP.SeedAsm.map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_pow] at this
    exact this
  have htreg : ∀ y, C.j C.t ^ (2 * N) * y = 0 → y = 0 := fun y hy => by
    have h3 : ξ ^ (2 * N) * (u ^ (2 * N) * y) = 0 := by rw [← mul_assoc, ← mul_pow, ← hu]; exact hy
    have h4 := hregn _ _ h3
    have h5 : (ui ^ (2 * N) * u ^ (2 * N)) * y = 0 := by rw [mul_assoc, h4, mul_zero]
    rwa [← mul_pow, mul_comm ui, hui, one_pow, one_mul] at h5
  have hJZ'Z := mul_comm_of_regular htreg hJZZ
  have hσZ : (Z.map (sigA g)).map C.j = (Z.map C.j).map (Per.σDp g) := by
    ext i j; simp only [Matrix.map_apply]; exact hjσ g _
  have hσX : (XA.map (sigA g)).map C.j = (XA.map C.j).map (Per.σDp g) := by
    ext i j; simp only [Matrix.map_apply]; exact hjσ g _
  have eY : ∀ i j, C.j ((X'A * κm * XA.map (sigA g)) i j) =
      (X'A.map C.j * κm.map C.j * (XA.map C.j).map (Per.σDp g)) i j := fun i j => by
    rw [← Matrix.map_apply (f := C.j), Matrix.map_mul, Matrix.map_mul, hσX]
  have hgJ := congrArg (Matrix.map · C.j) hg
  simp only [Matrix.map_mul, GlobalTheory.BSP.SeedAsm.map_smul_hom, map_mul, map_pow, map_natCast, hσZ, hjσ] at hgJ

  set ZJ := Z.map C.j
  set Z'J := Z'.map C.j
  set XJ := XA.map C.j
  set X'J := X'A.map C.j
  set RJ := R.map C.j
  set κJ := κm.map C.j
  have key : (C.j C.t ^ N * (l : Per.BdRp l) ^ k₀) • (X'J * Z'J * RJ * (ZJ * XJ).map (Per.σDp g)) =
      (Per.σDp g (C.j C.t) ^ N * C.j C.t ^ (2 * N)) • (X'J * κJ * XJ.map (Per.σDp g)) := by
    have e1 : X'J * Z'J * ((C.j C.t ^ N * (l : Per.BdRp l) ^ k₀) • (RJ * ZJ.map (Per.σDp g))) * XJ.map (Per.σDp g) =
        X'J * Z'J * (Per.σDp g (C.j C.t) ^ N • (ZJ * κJ)) * XJ.map (Per.σDp g) := by rw [hgJ]
    rw [Matrix.map_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at e1 ⊢
    rw [e1, ← Matrix.mul_assoc Z'J ZJ, hJZ'Z, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  have hA : ∀ a b, ξ ^ (2 * N) ∣ ((X'A * Z').map C.j) a b := fun a b => (hfil _ _).1 (hf2 a b)
  have hB : ∀ a b, ξ ^ (2 * N) ∣ ((ZJ * XJ).map (Per.σDp g)) a b := fun a b => by
    have e : ((ZJ * XJ).map (Per.σDp g)) a b = Per.σDp g (C.j ((Z * XA) a b)) := by
      show Per.σDp g ((Z.map C.j * XA.map C.j) a b) = _
      rw [← Matrix.map_mul]; rfl
    rw [e]
    exact (hfil _ _).1 (GlobalTheory.MemLoc.FilLaws.σDp_mem_FilP g _ _ (hf1 a b))
  choose A0 hA0 using hA
  choose B0 hB0 using hB
  have eA : X'J * Z'J = ξ ^ (2 * N) • Matrix.of A0 := by
    show X'A.map C.j * Z'.map C.j = _
    rw [← Matrix.map_mul]; ext a b; exact hA0 a b
  have eB : (ZJ * XJ).map (Per.σDp g) = ξ ^ (2 * N) • Matrix.of B0 := by
    ext a b; exact hB0 a b
  rw [eA, eB] at key
  intro i j
  have key2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul] at key2
  rw [hσt, hu] at key2
  rw [eY, hfil]
  set Y := (X'J * κJ * XJ.map (Per.σDp g)) i j
  set P := (Matrix.of A0 * RJ * Matrix.of B0) i j
  have hσu : Per.σDp g u * Per.σDp g ui = 1 := by rw [← map_mul, hui, map_one]
  set v := (c * Per.σDp g u) ^ N * u ^ (2 * N)
  set v' := (c' * Per.σDp g ui) ^ N * ui ^ (2 * N)
  have hvv : v * v' = 1 := by
    rw [show v * v' = (c * c') ^ N * (Per.σDp g u * Per.σDp g ui) ^ N * (u * ui) ^ (2 * N) by ring, hcc', hσu, hui]
    simp
  refine ⟨u ^ N * (l : Per.BdRp l) ^ k₀ * P * v', ?_⟩
  have h0 : ξ ^ (3 * N) * (v * (Y - ξ ^ (2 * N) * (u ^ N * (l : Per.BdRp l) ^ k₀ * P * v'))) = 0 := by
    linear_combination (-1 : Per.BdRp l) * key2 - (ξ ^ (5 * N) * u ^ N * (l : Per.BdRp l) ^ k₀ * P) * hvv
  have h1 := hregn _ _ h0
  have h2 : Y - ξ ^ (2 * N) * (u ^ N * (l : Per.BdRp l) ^ k₀ * P * v') = 0 := by
    linear_combination v' * h1 - (Y - ξ ^ (2 * N) * (u ^ N * (l : Per.BdRp l) ^ k₀ * P * v')) * hvv
  linear_combination h2

end GlobalTheory.BSP.RegularPeriodsFiltration

open GlobalTheory.BSP.SeedAsm GlobalTheory.BSP.RegularPeriodsFiltration in

/- English proof (translation)
Introduce `l _ K bk C τ hτ d ρ N c₁ c₂ c₃ k₀ F F' X X' Z Z' κ hZ`. Take `⟨hF, hX, hZZ, hφ, hg, hfix, hf1, hf2, hlog⟩` from `hZ`. Use `haveI := isDomain bk`. Take `⟨γ, hγ, hn⟩` from `GlobalTheory.T.exists_acris_ring_hom_bounded l K bk`. Take `⟨ν, hν⟩` from `acrisToDisc_image_t_eq_unit_mul_period C hτ γ hγ hn`.

Use `set a := bk.iA (bk.ev bk.E * τ) with ha_def`. Establish `ha : a ≠ 0` using `fun h => evE_mul_ne_zero hτ (iA_injective bk (h.trans (map_zero _).symm))`. Use `set e := bk.iS bk.E with he_def`. Establish `hae : a = e * bk.iA τ` using `by rw [ha_def, map_mul]; rfl`. Establish `he : e ≠ 0` using `fun h => ha (by rw [hae, h, zero_mul])`.

Establish `hγS : ∀ s : bk.S, γ (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) s) = bk.iS s` using `fun s => hγ _`. Establish `hmapS : ∀ M : Matrix (Fin d) (Fin d) bk.S, (M.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map γ = M.map bk.iS` using `fun M => by`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Conclude with `hγS _`.

Use `choose w hw using fun i j => GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ (hf1 i j)`. Use `choose w' hw' using fun i j => GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ (hf2 i j)`. Use `set G := Z.map γ`. Use `set G' := Z'.map γ`. Use `set Xs := X.map bk.iS`.

Use `set X's := X'.map bk.iS`. Establish `hW1 : G * Xs = e ^ (2 * N) • Matrix.of w`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]`. Establish `hW1' : X's * G' = e ^ (2 * N) • Matrix.of w'`.

Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw' i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]`. Establish `hXX : Xs * X's = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`. Use `congrArg (Matrix.map · bk.iS) hX` as an intermediate fact. Simplify using `only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow, map_natCast] at this`.

Conclude with `this`. Establish `hGG : G * G' = (γ C.t) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`. Use `congrArg (Matrix.map · γ) hZZ` as an intermediate fact. Simplify using `only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_pow] at this`. Conclude with `this`.

Take `⟨Lu, hLu⟩` from `isUnit_l_disc l (bk.ev PowerSeries.X) bk.ρ₀`. Use `set μ : bk.DA bk.ρ₀ := (ν : bk.DA bk.ρ₀)`. Use `set μi : bk.DA bk.ρ₀ := ((ν⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)`. Use `set Li : bk.DA bk.ρ₀ := ((Lu⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)`. Establish `hμ : μi * μ = 1` using `Units.inv_mul ν`.

Establish `hL : Li * (l : bk.DA bk.ρ₀) = 1` using `by rw [← hLu]; exact Units.inv_mul Lu`. Establish `c1 : Matrix.of w * X's = ((l : bk.DA bk.ρ₀) ^ c₂) • G`. Apply `smul_cancel (pow_ne_zero (2 * N) he)` to reduce the goal to its premises. Rewrite using `[← Matrix.smul_mul, ← hW1, Matrix.mul_assoc, hXX, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]`. Establish `c2 : Matrix.of w * Matrix.of w' = ((l : bk.DA bk.ρ₀) ^ c₂ * μ ^ (2 * N) * bk.iA τ ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`.

Apply `smul_cancel (pow_ne_zero (2 * N) he)` to reduce the goal to its premises. Apply `smul_cancel (pow_ne_zero (2 * N) he)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hGG, smul_smul]`. Use `_ = _ := by`.

Rewrite using `[smul_smul, smul_smul, hν, hae]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hV : (μi ^ N • Matrix.of w) * X's = (μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) • G`. Rewrite using `[Matrix.smul_mul, c1, smul_smul]`.

Establish `hLk : (Li * (l : bk.DA bk.ρ₀)) ^ k₀ = 1` using `by rw [hL, one_pow]`. Use `⟨WSeed.mk N c₁ c₂ c₃ F F' hF X X' hX (μi ^ N • Matrix.of w) ((Li ^ c₂ * μi ^ N) • Matrix.of w') ?_ ?_ (fun g => Li ^ k₀ • (κ g).map γ) ?_ ?_ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, c2, smul_smul, smul_smul]`. Use `congr 1`. Establish `h1 : (μi * μ) ^ N = 1` using `by rw [hμ, one_pow]`.

Establish `h2 : (Li * (l : bk.DA bk.ρ₀)) ^ c₂ = 1` using `by rw [hL, one_pow]`. Take the linear combination `(bk.iA τ ^ (2 * N)) * ((μi * μ) ^ N * (μi * μ) ^ N * h2 + (μi * μ) ^ N * h1 + h1)`. Introduce `Φ hΦ`. Establish `hP : (Z.map γ).map Φ = (Z.map (phiA l)).map γ`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Conclude with `comm_phi γ hγ hn Φ hΦ _`. Establish `hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map γ = F.map (bk.iS.comp PowerSeries.C)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, RingHom.comp_apply]`.

Conclude with `hγ _`. Establish `htφ : γ (phiA l C.t) = Φ μ * (bk.iS (frobS l bk.a bk.E) * a)`. Rewrite using `[← comm_phi γ hγ hn Φ hΦ, hν, map_mul]`. Use `congr 1`. Rewrite using `[ha_def, hΦ.ext, map_mul WittVector.frobenius, ← bk.ev_frob, hτ.1, map_mul bk.iA]`.

Both sides reduce to the same expression. Establish `hyp` using `congrArg (Matrix.map · γ) hφ`. Simplify using `only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, map_natCast, hFm, hν, htφ] at hyp`. Rewrite using `[hV, map_smul_hom, hP]`. Use extensionality with `i j`.

Establish `hij` using `congrFun (congrFun hyp i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, map_mul, map_pow, map_natCast] at hij ⊢`. Apply `mul_left_cancel₀ (pow_ne_zero N ha)` to reduce the goal to its premises. Establish `h1 : (μi * μ) ^ N = 1` using `by rw [hμ, one_pow]`. Establish `h3 : (Φ μi * Φ μ) ^ N = 1` using `by rw [← map_mul, hμ, map_one, one_pow]`.

Rewrite `hij` using `[show Z.map γ = G from rfl]`. Take the linear combination `(μi ^ N * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) * hij - (a ^ N * (l : bk.DA bk.ρ₀) ^ c₁ * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * (Z.map (phiA l)).map γ i j) * h1 + (a ^ N * bk.iS (frobS l bk.a bk.E) ^ N * μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * (G * F.map (bk.iS.comp PowerSeries.C)) i j) * h …`. Introduce `g Gm hG`. Establish `hP : (Z.map γ).map Gm = (Z.map (sigA (g : GQ l))).map γ`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Conclude with `comm_sig γ hγ hn _ Gm hG _`. Establish `hR : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map γ = (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l)))`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, RingHom.comp_apply]`.

Conclude with `hγ _`. Establish `hb : Gm a = bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ))` using `by rw [ha_def]; exact hG.ext _`. Establish `htσ : γ (sigA (g : GQ l) C.t) = Gm μ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ))`. Rewrite using `[← comm_sig γ hγ hn _ Gm hG, hν, map_mul, hb]`. Establish `hyp` using `congrArg (Matrix.map · γ) (hg g)`.

Simplify using `only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, map_natCast, hR, hν, htσ] at hyp`. Rewrite using `[hV, map_smul_hom, hP]`. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hyp i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul, map_mul, map_pow, map_natCast] at hij ⊢`.

Rewrite `hij` using `[show Z.map γ = G from rfl]`. Establish `h1 : (μi * μ) ^ N = 1` using `by rw [hμ, one_pow]`. Establish `h3 : (Gm μi * Gm μ) ^ N = 1` using `by rw [← map_mul, hμ, map_one, one_pow]`. Rewrite `hij` using `[ha_def, map_mul]`. Take the linear combination `(μi ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * Li ^ k₀) * hij - ((bk.iA (bk.ev bk.E) * bk.iA τ) ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (Z.map (sigA (g : GQ l))).map γ) i j) * h1 - ((bk.iA (bk.ev bk.E) * bk.iA τ) ^ N * Gm μ …`.

Introduce `g hg'`. Rewrite using `[hfix g hg', map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), smul_smul, map_pow, map_natCast, ← mul_pow, hL, one_pow, one_smul]`. Introduce `g Gm hG i j`. Establish `hfn` using `fil_nopole C (g : GQ l) ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))) Z Z' (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) (X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) (κ g) hZZ (hg g) hf1 hf2 i j`. Establish `hd` using `GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ hfn`.

Establish `hσX : ((X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))).map γ = (X.map bk.iS).map Gm`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[← comm_sig γ hγ hn _ Gm hG, hγS]`. Establish `eq : (X'.map bk.iS * (Li ^ k₀ • (κ g).map γ) * (X.map bk.iS).map Gm) i j = Li ^ k₀ * γ ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * κ g * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))) i j)`.

Rewrite using `[← Matrix.map_apply (f := γ), Matrix.map_mul, Matrix.map_mul, hσX, hmapS, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[eq]`. Conclude with `Dvd.dvd.mul_left hd _`. Introduce `m`. Take `⟨k, Λ, hΛ, hΛg⟩` from `hlog m`.

Use `⟨k, Λ, hΛ, fun g Gm hG i j => ?_⟩` and prove the remaining obligations. Establish `hd` using `GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn m _ (hΛg g i j)`. Establish `hσΛ : ((Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))).map γ = (Λ.map bk.iS).map Gm`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`.

Rewrite using `[← comm_sig γ hγ hn _ Gm hG, hγS]`. Establish `e1 : γ ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))) i j) = ((κ g).map γ * (Λ.map bk.iS).map Gm) i j`. Rewrite using `[← Matrix.map_apply (f := γ), Matrix.map_mul, hσΛ]`. Establish `eq : (Li ^ k₀ • (κ g).map γ * (Λ.map bk.iS).map Gm - Λ.map bk.iS) i j = Li ^ k₀ * γ ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j)`. Simplify using `only [Matrix.sub_apply, map_sub, e1, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, Matrix.smul_mul, Matrix.map_apply, hγS]`.

Take the linear combination `(bk.iS (Λ i j)) * hLk`. Rewrite using `[eq]`. Conclude with `Dvd.dvd.mul_left hd _`.
-/
theorem GlobalTheory.BKLim.wseed_of_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), (F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m) → Nonempty (WSeed bk d ρ τ) := by
  intro l _ K bk C τ hτ d ρ N c₁ c₂ c₃ k₀ F F' X X' Z Z' κ hZ
  obtain ⟨hF, hX, hZZ, hφ, hg, hfix, hf1, hf2, hlog⟩ := hZ
  haveI := isDomain bk
  obtain ⟨γ, hγ, hn⟩ := GlobalTheory.T.exists_acris_ring_hom_bounded l K bk
  obtain ⟨ν, hν⟩ := acrisToDisc_image_t_eq_unit_mul_period C hτ γ hγ hn
  set a := bk.iA (bk.ev bk.E * τ) with ha_def
  have ha : a ≠ 0 := fun h => evE_mul_ne_zero hτ (iA_injective bk (h.trans (map_zero _).symm))
  set e := bk.iS bk.E with he_def
  have hae : a = e * bk.iA τ := by rw [ha_def, map_mul]; rfl
  have he : e ≠ 0 := fun h => ha (by rw [hae, h, zero_mul])
  have hγS : ∀ s : bk.S, γ (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) s) = bk.iS s := fun s => hγ _
  have hmapS : ∀ M : Matrix (Fin d) (Fin d) bk.S,
      (M.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map γ = M.map bk.iS := fun M => by
    ext i j; simp only [Matrix.map_apply]; exact hγS _
  choose w hw using fun i j => GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ (hf1 i j)
  choose w' hw' using fun i j => GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ (hf2 i j)
  set G := Z.map γ
  set G' := Z'.map γ
  set Xs := X.map bk.iS
  set X's := X'.map bk.iS
  have hW1 : G * Xs = e ^ (2 * N) • Matrix.of w := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]
  have hW1' : X's * G' = e ^ (2 * N) • Matrix.of w' := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hw' i j, ← Matrix.map_apply (f := γ), Matrix.map_mul, hmapS]
  have hXX : Xs * X's = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (Matrix.map · bk.iS) hX
    simp only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow, map_natCast] at this
    exact this
  have hGG : G * G' = (γ C.t) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (Matrix.map · γ) hZZ
    simp only [Matrix.map_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), map_pow] at this
    exact this
  obtain ⟨Lu, hLu⟩ := isUnit_l_disc l (bk.ev PowerSeries.X) bk.ρ₀
  set μ : bk.DA bk.ρ₀ := (ν : bk.DA bk.ρ₀)
  set μi : bk.DA bk.ρ₀ := ((ν⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)
  set Li : bk.DA bk.ρ₀ := ((Lu⁻¹ : (bk.DA bk.ρ₀)ˣ) : bk.DA bk.ρ₀)
  have hμ : μi * μ = 1 := Units.inv_mul ν
  have hL : Li * (l : bk.DA bk.ρ₀) = 1 := by rw [← hLu]; exact Units.inv_mul Lu
  have c1 : Matrix.of w * X's = ((l : bk.DA bk.ρ₀) ^ c₂) • G := by
    apply smul_cancel (pow_ne_zero (2 * N) he)
    rw [← Matrix.smul_mul, ← hW1, Matrix.mul_assoc, hXX, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
  have c2 : Matrix.of w * Matrix.of w' =
      ((l : bk.DA bk.ρ₀) ^ c₂ * μ ^ (2 * N) * bk.iA τ ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    apply smul_cancel (pow_ne_zero (2 * N) he)
    apply smul_cancel (pow_ne_zero (2 * N) he)
    calc e ^ (2 * N) • e ^ (2 * N) • (Matrix.of w * Matrix.of w')
        = (e ^ (2 * N) • Matrix.of w) * (e ^ (2 * N) • Matrix.of w') := by rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = G * (Xs * X's) * G' := by rw [← hW1, ← hW1', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ((l : bk.DA bk.ρ₀) ^ c₂ * e ^ (2 * N) * γ C.t ^ (2 * N)) • 1 := by
        rw [hXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hGG, smul_smul]
      _ = _ := by
        rw [smul_smul, smul_smul, hν, hae]
        congr 1
        ring
  have hV : (μi ^ N • Matrix.of w) * X's = (μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) • G := by
    rw [Matrix.smul_mul, c1, smul_smul]
  have hLk : (Li * (l : bk.DA bk.ρ₀)) ^ k₀ = 1 := by rw [hL, one_pow]
  refine ⟨WSeed.mk N c₁ c₂ c₃ F F' hF X X' hX (μi ^ N • Matrix.of w) ((Li ^ c₂ * μi ^ N) • Matrix.of w') ?_ ?_
    (fun g => Li ^ k₀ • (κ g).map γ) ?_ ?_ ?_ ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, c2, smul_smul, smul_smul]
    congr 1
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h2 : (Li * (l : bk.DA bk.ρ₀)) ^ c₂ = 1 := by rw [hL, one_pow]
    linear_combination (bk.iA τ ^ (2 * N)) * ((μi * μ) ^ N * (μi * μ) ^ N * h2 + (μi * μ) ^ N * h1 + h1)
  · intro Φ hΦ
    have hP : (Z.map γ).map Φ = (Z.map (phiA l)).map γ := by
      ext i j; simp only [Matrix.map_apply]; exact comm_phi γ hγ hn Φ hΦ _
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map γ =
        F.map (bk.iS.comp PowerSeries.C) := by
      ext i j; simp only [Matrix.map_apply, RingHom.comp_apply]; exact hγ _
    have htφ : γ (phiA l C.t) = Φ μ * (bk.iS (frobS l bk.a bk.E) * a) := by
      rw [← comm_phi γ hγ hn Φ hΦ, hν, map_mul]
      congr 1
      rw [ha_def, hΦ.ext, map_mul WittVector.frobenius, ← bk.ev_frob, hτ.1, map_mul bk.iA]
      rfl
    have hyp := congrArg (Matrix.map · γ) hφ
    simp only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, map_natCast, hFm, hν, htφ] at hyp
    rw [hV, map_smul_hom, hP]
    ext i j
    have hij := congrFun (congrFun hyp i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, map_mul, map_pow, map_natCast] at hij ⊢
    apply mul_left_cancel₀ (pow_ne_zero N ha)
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h3 : (Φ μi * Φ μ) ^ N = 1 := by rw [← map_mul, hμ, map_one, one_pow]
    rw [show Z.map γ = G from rfl] at hij
    linear_combination (μi ^ N * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂) * hij -
      (a ^ N * (l : bk.DA bk.ρ₀) ^ c₁ * Φ μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * (Z.map (phiA l)).map γ i j) * h1 +
      (a ^ N * bk.iS (frobS l bk.a bk.E) ^ N * μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        (G * F.map (bk.iS.comp PowerSeries.C)) i j) * h3
  · intro g Gm hG
    have hP : (Z.map γ).map Gm = (Z.map (sigA (g : GQ l))).map γ := by
      ext i j; simp only [Matrix.map_apply]; exact comm_sig γ hγ hn _ Gm hG _
    have hR : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map γ =
        (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) := by
      ext i j; simp only [Matrix.map_apply, RingHom.comp_apply]; exact hγ _
    have hb : Gm a = bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by rw [ha_def]; exact hG.ext _
    have htσ : γ (sigA (g : GQ l) C.t) = Gm μ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by
      rw [← comm_sig γ hγ hn _ Gm hG, hν, map_mul, hb]
    have hyp := congrArg (Matrix.map · γ) (hg g)
    simp only [Matrix.map_mul, map_smul_hom, map_mul, map_pow, map_natCast, hR, hν, htσ] at hyp
    rw [hV, map_smul_hom, hP]
    ext i j
    have hij := congrFun (congrFun hyp i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul, map_mul, map_pow, map_natCast] at hij ⊢
    rw [show Z.map γ = G from rfl] at hij
    have h1 : (μi * μ) ^ N = 1 := by rw [hμ, one_pow]
    have h3 : (Gm μi * Gm μ) ^ N = 1 := by rw [← map_mul, hμ, map_one, one_pow]
    rw [ha_def, map_mul] at hij
    linear_combination (μi ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ * Li ^ k₀) * hij -
      ((bk.iA (bk.ev bk.E) * bk.iA τ) ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (Z.map (sigA (g : GQ l))).map γ) i j) * h1 -
      ((bk.iA (bk.ev bk.E) * bk.iA τ) ^ N * Gm μi ^ N * (l : bk.DA bk.ρ₀) ^ c₂ *
        ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (Z.map (sigA (g : GQ l))).map γ) i j) * (μi * μ) ^ N * hLk +
      ((bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) * bk.iA (Per.σA (g : GQ l) τ)) ^ N * μi ^ N *
        (l : bk.DA bk.ρ₀) ^ c₂ * Li ^ k₀ * (G * (κ g).map γ) i j) * h3
  · intro g hg'
    rw [hfix g hg', map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _), smul_smul, map_pow, map_natCast, ← mul_pow,
      hL, one_pow, one_smul]
  · intro g Gm hG i j
    have hfn := fil_nopole C (g : GQ l) ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))))
      Z Z' (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) (X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev))
      (κ g) hZZ (hg g) hf1 hf2 i j
    have hd := GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn (2 * N) _ hfn
    have hσX : ((X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))).map γ = (X.map bk.iS).map Gm := by
      ext a b; simp only [Matrix.map_apply]; rw [← comm_sig γ hγ hn _ Gm hG, hγS]
    have eq : (X'.map bk.iS * (Li ^ k₀ • (κ g).map γ) * (X.map bk.iS).map Gm) i j = Li ^ k₀ *
        γ ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * κ g *
          (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))) i j) := by
      rw [← Matrix.map_apply (f := γ), Matrix.map_mul, Matrix.map_mul, hσX, hmapS, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_apply, smul_eq_mul]
    rw [eq]
    exact Dvd.dvd.mul_left hd _
  · intro m
    obtain ⟨k, Λ, hΛ, hΛg⟩ := hlog m
    refine ⟨k, Λ, hΛ, fun g Gm hG i j => ?_⟩
    have hd := GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc l K bk C γ hγ hn m _ (hΛg g i j)
    have hσΛ : ((Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))).map γ = (Λ.map bk.iS).map Gm := by
      ext a b; simp only [Matrix.map_apply]; rw [← comm_sig γ hγ hn _ Gm hG, hγS]
    have e1 : γ ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l))) i j) =
        ((κ g).map γ * (Λ.map bk.iS).map Gm) i j := by
      rw [← Matrix.map_apply (f := γ), Matrix.map_mul, hσΛ]
    have eq : (Li ^ k₀ • (κ g).map γ * (Λ.map bk.iS).map Gm - Λ.map bk.iS) i j = Li ^ k₀ *
        γ ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) -
          (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) := by
      simp only [Matrix.sub_apply, map_sub, e1, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast,
        Matrix.smul_mul, Matrix.map_apply, hγS]
      linear_combination (bk.iS (Λ i j)) * hLk
    rw [eq]
    exact Dvd.dvd.mul_left hd _
