import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylRowActMemOfIsUnitDet

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.WeylLocal

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ w.asIdeal.primeCompl),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

/- English proof (translation)
The claim follows from `IsLocalization.AtPrime.isLocalRing (locRing w) w.asIdeal`.
-/
theorem isLocalRing_locRing (w : HeightOneSpectrum (𝓞 K)) : IsLocalRing (locRing w) :=
  IsLocalization.AtPrime.isLocalRing (locRing w) w.asIdeal

/- English proof (translation)
Introduce `h`. Establish `h0 : s = 0` using `(FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])`. Conclude with `hs (by rw [h0]; exact w.asIdeal.zero_mem)`.
-/
theorem ne_zero_of_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∈ w.asIdeal.primeCompl) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have h0 : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact hs (by rw [h0]; exact w.asIdeal.zero_mem)

/- English proof (translation)
Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨r, t, ht, hat⟩` from `(mem_locRing w a).mp ha`. Use `⟨t * s, mul_mem ht hs, ?_⟩` and prove the remaining obligations. Establish `ht0` using `ne_zero_of_mem w ht`. Establish `he : (t * s) • (a • y) = r • (s • y)`.

Rewrite using `[hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r, ← algebraMap_smul K s, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[he]`.

Conclude with `M.smul_mem r hsy`.
-/
theorem smul_mem_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : a ∈ locRing w) {y : Z}
    (hy : y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) : a • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
  obtain ⟨s, hs, hsy⟩ := hy
  obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp ha
  refine ⟨t * s, mul_mem ht hs, ?_⟩
  have ht0 := ne_zero_of_mem w ht
  have he : (t * s) • (a • y) = r • (s • y) := by
    rw [hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
      ← algebraMap_smul K s, smul_smul, smul_smul]
    congr 1
    rw [map_mul]
    field_simp
  rw [he]
  exact M.smul_mem r hsy

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hy⟩`.
-/
theorem le_locP {Z : Type} [AddCommGroup Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {y : Z} (hy : y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
  ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hy⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Establish `h : (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun a => (B : Matrix (Fin n) (Fin n) K) a j) i = (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) i j` using `rfl`. Rewrite using `[h, Units.inv_mul, Matrix.one_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz => rw [Matrix.mulVec_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]`. Conclude with `mul_mem ⟨a, rfl⟩ hy`.
-/
theorem coord_of_mem_colLat {n : ℕ} (B : GL (Fin n) K) {x : Fin n → K} (hx : x ∈ colLat B) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have h : (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        fun a => (B : Matrix (Fin n) (Fin n) K) a j) i =
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) i j := rfl
    rw [h, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ hy

/- English proof (translation)
Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨a, ha⟩` from `coord_of_mem_colLat B hsx i`. Rewrite `ha` using `[Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]`. Use `(mem_locRing w _).mpr ⟨a, s, hs, ?_⟩` and prove the remaining obligations. Establish `hs0` using `ne_zero_of_mem w hs`.

Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts.
-/
theorem coord_of_mem_locP {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) {x : Fin n → K}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ locRing w := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨a, ha⟩ := coord_of_mem_colLat B hsx i
  rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at ha
  refine (mem_locRing w _).mpr ⟨a, s, hs, ?_⟩
  have hs0 := ne_zero_of_mem w hs
  rw [ha]
  field_simp

/- English proof (translation)
Establish `hx : (fun a => (B' : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)`. Rewrite using `[h]`. Conclude with `le_locP w _ (Submodule.subset_span ⟨j, rfl⟩)`. Conclude with `coord_of_mem_locP w B hx i`.
-/
theorem entries_mem {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B')) (i j : Fin n) :
    ((B⁻¹ * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ locRing w := by
  have hx : (fun a => (B' : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) := by
    rw [h]
    exact le_locP w _ (Submodule.subset_span ⟨j, rfl⟩)
  exact coord_of_mem_locP w B hx i

/- English proof (translation)
Establish `h1` using `entries_mem w 1 g h`. Establish `h2` using `entries_mem w g 1 h.symm`. Rewrite `h1` using `[inv_one, one_mul]`. Rewrite `h2` using `[mul_one]`. Set `g₀ : Matrix (Fin n) (Fin n) (locRing w)` to `Matrix.of fun i j => ⟨_, h1 i j⟩`.

Set `g₁ : Matrix (Fin n) (Fin n) (locRing w)` to `Matrix.of fun i j => ⟨_, h2 i j⟩`. Establish `e0 : g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K)` using `rfl`. Establish `e1 : g₁.map (algebraMap (locRing w) K) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)` using `rfl`. Use `⟨g₀, ?_, e0⟩` and prove the remaining obligations. Establish `hm : g₀ * g₁ = 1`.

Apply `Matrix.map_injective (f := algebraMap (locRing w) K) Subtype.val_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, e0, e1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Matrix.isUnit_det_of_right_inverse hm`.
-/
theorem exists_lift {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ g₀ : Matrix (Fin n) (Fin n) (locRing w), IsUnit g₀.det ∧
      g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := by
  have h1 := entries_mem w 1 g h
  have h2 := entries_mem w g 1 h.symm
  rw [inv_one, one_mul] at h1
  rw [mul_one] at h2
  let g₀ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let g₁ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have e0 : g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := rfl
  have e1 : g₁.map (algebraMap (locRing w) K) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine ⟨g₀, ?_, e0⟩
  have hm : g₀ * g₁ = 1 := by
    apply Matrix.map_injective (f := algebraMap (locRing w) K) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e0, e1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_right_inverse hm

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Use `Submodule.subset_span ⟨v, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `smul a y _ hy`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S n n le_rfl ν := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Use `le_locP w _ ⟨_, Submodule.subset_span ⟨v, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[toK_apply, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `smul a y _ hy`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `smul_mem_locP w _ a.2 hy`.
-/
theorem map_weyl_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) (locRing w)} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl (locRing w) n n le_rfl ν) :
    map (algebraMap (locRing w) K) f ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K _)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine le_locP w _ ⟨_, Submodule.subset_span ⟨v, rfl⟩, ?_⟩
    simp only
    rw [toK_apply, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact smul_mem_locP w _ a.2 hy

/- English proof (translation)
Take `⟨g₀, hu, e0⟩` from `exists_lift w g h`. Take `⟨f₀, hf₀, rfl⟩` from `hf`. Use `haveI := isLocalRing_locRing w`. Establish `h1` using `map_mem_weyl (algebraMap (𝓞 K) (locRing w)) lam.natW hf₀`. Establish `h2` using `GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det (locRing w) n lam.natW (natW_antitone lam) g₀ᵀ (by rwa [Matrix.det_transpose]) _ h1`.

Establish `h3` using `map_weyl_mem_locP w lam.natW h2`. Rewrite `h3` using `[Formalism.GradedWeylDivisibility.ldtwist_map_rowAct, map_map, ← IsScalarTower.algebraMap_eq, Matrix.transpose_map, e0]`. Use `smul_mem_locP w _ ?_ h3` and prove the remaining obligations. Establish `hd : Matrix.GeneralLinearGroup.det g = Units.map (algebraMap (locRing w) K).toMonoidHom hu.unit`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, ← e0, Units.coe_map, IsUnit.unit_spec]`. Conclude with `((algebraMap (locRing w) K).map_det g₀).symm`. Rewrite using `[detPow, hd, ← map_zpow, Units.coe_map]`. Conclude with `Subtype.property _`.
-/
theorem sqAct_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) K)
    (h : IsBasisAt w (colLat 1) g) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ (delSq (𝓞 K) n lam).map (toK K _)) :
    sqAct K n lam g f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  obtain ⟨g₀, hu, e0⟩ := exists_lift w g h
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  haveI := isLocalRing_locRing w
  have h1 := map_mem_weyl (algebraMap (𝓞 K) (locRing w)) lam.natW hf₀
  have h2 := GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det (locRing w) n lam.natW (natW_antitone lam) g₀ᵀ (by rwa [Matrix.det_transpose]) _ h1
  have h3 := map_weyl_mem_locP w lam.natW h2
  rw [Formalism.GradedWeylDivisibility.ldtwist_map_rowAct, map_map, ← IsScalarTower.algebraMap_eq, Matrix.transpose_map, e0] at h3
  refine smul_mem_locP w _ ?_ h3
  have hd : Matrix.GeneralLinearGroup.det g = Units.map (algebraMap (locRing w) K).toMonoidHom hu.unit := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← e0, Units.coe_map, IsUnit.unit_spec]
    exact ((algebraMap (locRing w) K).map_det g₀).symm
  rw [detPow, hd, ← map_zpow, Units.coe_map]
  exact Subtype.property _

/- English proof (translation)
Use `choose s hs hsf using hf`. Use `⟨∏ τ, s τ, prod_mem fun τ _ => hs τ, Submodule.subset_span ⟨fun τ => s τ • f τ, hsf, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[ten, ← Finset.prod_smul]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `((Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap.map_smul_of_tower (s τ) (f τ)).symm`.
-/
theorem ten_mem_locP (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ}
    (M : ι → Submodule (𝓞 K) (MvPolynomial (Fin n × Fin n) K)) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (M τ)) :
    ten f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K M) := by
  choose s hs hsf using hf
  refine ⟨∏ τ, s τ, prod_mem fun τ _ => hs τ, Submodule.subset_span ⟨fun τ => s τ • f τ, hsf, ?_⟩⟩
  rw [ten, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact ((Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap.map_smul_of_tower (s τ) (f τ)).symm

/- English proof (translation)
Introduce `K _ _ ι _ n lam w g hg F hF`. Establish `key : ∀ P ∈ delStd K lam, actP lam g P ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam)`. Introduce `P hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨f, hf, rfl⟩` from `hy`. Establish `h` using `actTen K ι n lam g f`. Rewrite `h` using `[ten]`. Rewrite using `[h]`. Conclude with `ten_mem_locP w _ _ fun τ => sqAct_mem_locP w (lam τ) (g τ) (hg τ) (hf τ)`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy`.

Rewrite using `[LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ _ hy`. Take `⟨s, hs, hsF⟩` from `hF`. Take `⟨t, ht, h⟩` from `key _ hsF`. Rewrite `h` using `[LinearMap.map_smul_of_tower]`.

Conclude with `⟨t * s, mul_mem ht hs, (mul_smul t s (actP lam g F)).symm ▸ h⟩`.
-/
theorem polyAction_mem_locP_delStd : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ ι _ n lam w g hg F hF
  have key : ∀ P ∈ delStd K lam, actP lam g P ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      have h := actTen K ι n lam g f
      rw [ten] at h
      rw [h]
      exact ten_mem_locP w _ _ fun τ => sqAct_mem_locP w (lam τ) (g τ) (hg τ) (hf τ)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hsF⟩ := hF
  obtain ⟨t, ht, h⟩ := key _ hsF
  rw [LinearMap.map_smul_of_tower] at h
  exact ⟨t * s, mul_mem ht hs, (mul_smul t s (actP lam g F)).symm ▸ h⟩

end GlobalTheory.TestLat.WeylLocal
