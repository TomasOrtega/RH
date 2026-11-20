import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show star (a • c i) = a • star (c i)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, star_mul', hU.star_fix, mul_comm]`.
-/
theorem star_smul_vec [hU : Unram F E] {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', hU.star_fix, mul_comm]

def trForm [Unram F E] (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp only [star_add, add_dotProduct, map_add])
    (fun a c b => by simp only [star_smul_vec, smul_dotProduct, map_smul])
    (fun c b b' => by simp only [dotProduct_add, map_add])
    (fun a c b => by simp only [dotProduct_smul, map_smul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trForm_apply [Unram F E] {r : ℕ} (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

/- English proof (translation)
Set `σ : E ≃ₐ[F] E` to `AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)`. Conclude with `Algebra.trace_eq_of_algEquiv σ z`.
-/
theorem trace_star [hU : Unram F E] (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)
  exact Algebra.trace_eq_of_algEquiv σ z

/- English proof (translation)
Use `⟨fun c b => ?_⟩` and prove the remaining obligations. Rewrite using `[trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]`.
-/
theorem trForm_symm [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun c b => ?_⟩
  rw [trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]

/- English proof (translation)
Use `haveI : CharZero F := hU.charZero`. Assume the negation of the conclusion as `hc`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, c i ≠ 0 := by`. Assume the negation of the conclusion as `h'`. Use `push_neg at h'`.

Conclude with `hc (funext h')`. Establish `h1` using `h (Pi.single i (star (c i))⁻¹)`. Rewrite `h1` using `[trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi), ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq]`. Evaluate the numerical expressions using `at h1`.
-/
theorem trForm_sepLeft [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  haveI : CharZero F := hU.charZero
  by_contra hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hc (funext h')
  have h1 := h (Pi.single i (star (c i))⁻¹)
  rw [trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi),
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq] at h1
  norm_num at h1

/- English proof (translation)
Use `⟨fun c h => trForm_sepLeft (F := F) r c h, fun b h => trForm_sepLeft (F := F) r b fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[(trForm_symm r).eq]`. Conclude with `h c`.
-/
theorem trForm_nondeg [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate := by
  refine ⟨fun c h => trForm_sepLeft (F := F) r c h, fun b h => trForm_sepLeft (F := F) r b fun c => ?_⟩
  rw [(trForm_symm r).eq]; exact h c

/- English proof (translation)
Take `⟨b⟩` from `(GlobalTheory.JR.Et.quadratic_structure F E A).1`. Use `haveI : Module.Free A.K A.L := Module.Free.of_basis b`. Use `haveI : Module.Finite A.K A.L := Module.Finite.of_basis b`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`. Use `haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L`.

Use `haveI : Module.Finite E A.L := Module.Finite.of_restrictScalars_finite F E A.L`. Unfold `Et.kerL Et.psiK`. Rewrite using `[hx, Algebra.trace_trace (R := F) (S := E) (T := A.L), ← Algebra.trace_trace (R := F) (S := A.K) (T := A.L)]`. Use `congr 2`. Rewrite using `[show algebraMap A.K A.L x * star y' * y = x • (star y' * y) by rw [Algebra.smul_def, mul_assoc], map_smul, smul_eq_mul]`.
-/
theorem kerL_eq [hU : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)}
    (hx : A.IsIsom x j) (y' y : A.L) :
    A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  obtain ⟨b⟩ := (GlobalTheory.JR.Et.quadratic_structure F E A).1
  haveI : Module.Free A.K A.L := Module.Free.of_basis b
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : Module.Finite E A.L := Module.Finite.of_restrictScalars_finite F E A.L
  unfold Et.kerL Et.psiK
  rw [hx, Algebra.trace_trace (R := F) (S := E) (T := A.L), ← Algebra.trace_trace (R := F) (S := A.K) (T := A.L)]
  congr 2
  rw [show algebraMap A.K A.L x * star y' * y = x • (star y' * y) by rw [Algebra.smul_def, mul_assoc], map_smul,
    smul_eq_mul]

end GlobalTheory.JR.MeasTransport

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddChar.map_zero_eq_one]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum (ψ : AddChar F ℂ) {ι : Type} (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/- English proof (translation)
Use `letI := M.mE`. Use `haveI := M.bE`. Use `haveI := M.haarE`. Use `haveI : IsUltrametricDist E := hU.ultraE`. Use `haveI : LocallyCompactSpace F := hU.lcF`.

Use `haveI : LocallyCompactSpace E := hU.lcE`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`. Use `haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional`.

Use `haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi`. Set `O : AddSubgroup (Fin r → E)` to `{ carrier := {v | ∀ i, ‖v i‖ ≤ 1} zero_mem' := by intro i; simp add_mem' := fun {a b} ha hb i => (IsUltrametricDist.norm_add_le_max (a i) (b i)).trans (max_le (ha i) (hb i)) neg_mem' := fun {a} ha i => by simpa using ha i }`. Establish `hmem : ∀ v, v ∈ O ↔ ∀ i, ‖v i‖ ≤ 1` using `fun v => Iff.rfl`. Establish `hOset : (O : Set (Fin r → E)) = Set.univ.pi fun _ => Metric.closedBall (0 : E) 1`. Use extensionality with `v`.

Simplify using `[O, Set.mem_pi]`. Establish `hOo : IsOpen (O : Set (Fin r → E))`. Rewrite using `[hOset]`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero`. Establish `hOk : IsCompact (O : Set (Fin r → E))`.

Rewrite using `[hOset]`. Conclude with `isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Establish `hc` using `((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2`. Establish `hdual : {y | ∀ x ∈ O, ψ (trForm (F` using `F) r x y) = 1} = (O : Set (Fin r → E)) := by`. Use extensionality with `y`.

Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use `(hc (y i)).1 fun e he => ?_` and prove the remaining obligations. Establish `h1` using `h (Pi.single i (star e)) (by`.

Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[hU.norm_star, he]`. Simplify using `[hk])`.

Rewrite `h1` using `[trForm_apply]`. Simplify `h1` using `[dotProduct, Pi.single_apply, apply_ite star]`. Introduce `h x hx`. Rewrite using `[trForm_apply, dotProduct, map_sum, addChar_sum]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.star_apply]`. Conclude with `(hc (y i)).2 (h i) (star (x i)) (by rw [hU.norm_star]; exact hx i)`. Establish `hvol : (Measure.pi fun _ : Fin r => M.μE) O = 1`. Rewrite using `[hOset, Measure.pi_pi]`. Simplify using `[M.volE]`.

Use `haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Establish `key` using `(GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r) (Measure.pi fun _ : Fin r => M.μE) inferInstance).1 O hOo hOk |>.1`. Rewrite using `[key, hdual, hvol, one_mul]`.
-/
theorem pi_selfDual [hU : Unram F E] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) (M : Meas r F E) :
    letI := M.mE
    SelfDual (Measure.pi fun _ : Fin r => M.μE) (fun a b => ψ (trForm (F := F) r a b)) := by
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  let O : AddSubgroup (Fin r → E) :=
    { carrier := {v | ∀ i, ‖v i‖ ≤ 1}
      zero_mem' := by intro i; simp
      add_mem' := fun {a b} ha hb i => (IsUltrametricDist.norm_add_le_max (a i) (b i)).trans (max_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hmem : ∀ v, v ∈ O ↔ ∀ i, ‖v i‖ ≤ 1 := fun v => Iff.rfl
  have hOset : (O : Set (Fin r → E)) = Set.univ.pi fun _ => Metric.closedBall (0 : E) 1 := by
    ext v; simp [O, Set.mem_pi]
  have hOo : IsOpen (O : Set (Fin r → E)) := by
    rw [hOset]; exact isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hOk : IsCompact (O : Set (Fin r → E)) := by
    rw [hOset]; exact isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hc := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hdual : {y | ∀ x ∈ O, ψ (trForm (F := F) r x y) = 1} = (O : Set (Fin r → E)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hmem]
    constructor
    · intro h i
      refine (hc (y i)).1 fun e he => ?_
      have h1 := h (Pi.single i (star e)) (by
        intro k
        by_cases hk : k = i
        · subst hk; simp [hU.norm_star, he]
        · simp [hk])
      rw [trForm_apply] at h1
      simpa [dotProduct, Pi.single_apply, apply_ite star] using h1
    · intro h x hx
      rw [trForm_apply, dotProduct, map_sum, addChar_sum]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [Pi.star_apply]
      exact (hc (y i)).2 (h i) (star (x i)) (by rw [hU.norm_star]; exact hx i)
  have hvol : (Measure.pi fun _ : Fin r => M.μE) O = 1 := by
    rw [hOset, Measure.pi_pi]; simp [M.volE]
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r) (Measure.pi fun _ : Fin r => M.μE) inferInstance).1 O
    hOo hOk |>.1
  rw [key, hdual, hvol, one_mul]

/- English proof (translation)
Use `haveI : IsUltrametricDist E := hU.ultraE`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : LocallyCompactSpace E := hU.lcE`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`.

Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`. Use `haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional`. Use `haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi`. Use `haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L`. Use `haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L`.

Use `haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L`. Set `jF : A.L ≃ₗ[F] (Fin r → E)` to `j.restrictScalars F`. Establish `hc : Continuous jF` using `IsModuleTopology.continuous_of_linearMap jF.toLinearMap`. Establish `hcs : Continuous jF.symm` using `IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap`. Set `jC : A.L ≃L[F] (Fin r → E)` to `{ jF with continuous_toFun := hc, continuous_invFun := hcs }`.

Establish `hcoe : (⇑jC : A.L → Fin r → E) = ⇑j` using `rfl`. Establish `hme : MeasurableEmbedding (⇑j)` using `by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding`. Use `haveI := hμ.1`. Establish `hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L), fourB (Measure.map j μ) (fun a b => ψ (trForm (F` using `F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by`. Introduce `g y`.

Unfold `fourB`. Rewrite using `[hme.integral_map]`. Simplify using `only [Function.comp, kerL_eq A ψ hx, trForm_apply]`. Use `⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `j.surjective v`.

Establish `hfj : IsTest (f ∘ j)`. Use `⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩` and prove the remaining obligations. Rewrite using `[← hcoe]`. Conclude with `hf.2.comp_homeomorph jC.toHomeomorph`. Rewrite using `[hfour]`.

Establish `h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F` using `F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=`. Use function extensionality and compare the values at `fun y => hfour f y`. Rewrite using `[h2, hμ.2 _ hfj y]`. Simplify using `[map_neg]`.
-/
theorem map_selfDual [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  let jC : A.L ≃L[F] (Fin r → E) := { jF with continuous_toFun := hc, continuous_invFun := hcs }
  have hcoe : (⇑jC : A.L → Fin r → E) = ⇑j := rfl
  have hme : MeasurableEmbedding (⇑j) := by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding
  haveI := hμ.1
  have hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L),
      fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by
    intro g y
    unfold fourB
    rw [hme.integral_map]
    simp only [Function.comp, kerL_eq A ψ hx, trForm_apply]
  refine ⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩
  obtain ⟨y, rfl⟩ := j.surjective v
  have hfj : IsTest (f ∘ j) := by
    refine ⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩
    rw [← hcoe]; exact hf.2.comp_homeomorph jC.toHomeomorph
  rw [hfour]
  have h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=
    funext fun y => hfour f y
  rw [h2, hμ.2 _ hfj y]
  simp [map_neg]

/- English proof (translation)
Introduce `F E _ _ _ _ hU A ψ hψ r M x j hx`. Use `⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩` and prove the remaining obligations. Use `letI := M.mE`. Use `haveI := M.bE`. Use `haveI : IsUltrametricDist E := hU.ultraE`.

Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : LocallyCompactSpace E := hU.lcE`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`.

Use `haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional`. Use `haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi`. Take `⟨⟨μ0, _, huniq⟩, _⟩` from `GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r)`. Conclude with `(huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm`.
-/
theorem map_isIsom_eq_pi : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  intro F E _ _ _ _ hU A ψ hψ r M x j hx
  refine ⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩
  letI := M.mE
  haveI := M.bE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  obtain ⟨⟨μ0, _, huniq⟩, _⟩ := GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r)
    (trForm_symm r) (trForm_nondeg r)
  exact (huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm

end GlobalTheory.JR.MeasTransport
