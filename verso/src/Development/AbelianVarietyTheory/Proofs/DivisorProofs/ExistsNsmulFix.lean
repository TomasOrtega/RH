import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

variable (σ) in

def conjHalf (e : AEF F E) (nS nT : ℕ) : AddSubgroup (WOF F E nS nT) where
  carrier := {u | ∀ i j, cAF σ e * u i j = u i j}
  add_mem' := fun {a b} ha hb i j => by
    simp only [Set.mem_setOf_eq] at ha hb
    rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by simp
  neg_mem' := fun {a} ha i j => by
    simp only [Set.mem_setOf_eq] at ha
    rw [Matrix.neg_apply, mul_neg, ha i j]

variable (σ JS JT xi0 ψ) in

def heisL (w : WOF F E nS nT) : (WOF F E nS nT → ℂ) →ₗ[ℂ] (WOF F E nS nT → ℂ) where
  toFun := heisOF σ JS JT xi0 ψ w
  map_add' := GlobalTheory.WeilPartsF.heisOF_add w
  map_smul' := fun c f => GlobalTheory.WeilPartsF.heisOF_smul c w f

variable (σ JS JT xi0 ψ) in

def commF (u y : WOF F E nS nT) : ℂ :=
  ψ (symplOHF σ JS JT xi0 u y - symplOHF σ JS JT xi0 y u)

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisOF, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[GlobalTheory.HeisThetaF.symplOHF_add_left w u y, GlobalTheory.HeisThetaF.symplOHF_add_right w u y, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, add_assoc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisOF_heisOF (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      ψ (symplOHF σ JS JT xi0 u y) • heisOF σ JS JT xi0 ψ (u + y) f := by
  funext w
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.HeisThetaF.symplOHF_add_left w u y, GlobalTheory.HeisThetaF.symplOHF_add_right w u y,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, add_assoc]
  ring

/- English proof (translation)
Rewrite using `[heisOF_heisOF, heisOF_heisOF, smul_smul, add_comm y u, commF, ← AddChar.map_add_eq_mul, sub_add_cancel]`.
-/
theorem heisOF_comm (u y : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ u (heisOF σ JS JT xi0 ψ y f) =
      commF σ JS JT xi0 ψ u y • heisOF σ JS JT xi0 ψ y (heisOF σ JS JT xi0 ψ u f) := by
  rw [heisOF_heisOF, heisOF_heisOF, smul_smul, add_comm y u, commF, ← AddChar.map_add_eq_mul, sub_add_cancel]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisOF, add_zero, GlobalTheory.HeisThetaF.symplOHF_zero_right, AddChar.map_zero_eq_one, one_mul]`.
-/
theorem heisOF_zero (f : WOF F E nS nT → ℂ) : heisOF σ JS JT xi0 ψ 0 f = f := by
  funext w
  simp only [heisOF, add_zero, GlobalTheory.HeisThetaF.symplOHF_zero_right, AddChar.map_zero_eq_one, one_mul]

/- English proof (translation)
Take `⟨-, -, v, ε, -, h⟩` from `he`. Establish `h2` using `congrArg (cAF σ) h`. Rewrite `h2` using `[map_add, GlobalTheory.HeisThetaF.cAF_algebraMap]`. Take the linear combination `h2 - h`.
-/
theorem cAF_cAF {e : AEF F E} (he : IsSplitIdemF σ e) : cAF σ (cAF σ e) = e := by
  obtain ⟨-, -, v, ε, -, h⟩ := he
  have h2 := congrArg (cAF σ) h
  rw [map_add, GlobalTheory.HeisThetaF.cAF_algebraMap] at h2
  linear_combination h2 - h

/- English proof (translation)
Establish `hcc` using `cAF_cAF he`. Establish `h2 : e * cAF σ e = 0` using `he.2.1`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Establish `e1 : cAF σ (y c b) = e * cAF σ (y c b)` using `by conv_lhs => rw [← hy c b]`. Rewrite using `[map_mul, hcc]`.

Rewrite using `[e1, ← hx d a]`. Take the linear combination `(incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * x d a) * h2`.
-/
theorem hOF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : hOF σ JS JT x y = 0 := by
  have hcc := cAF_cAF he
  have h2 : e * cAF σ e = 0 := he.2.1
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, hcc]
  rw [e1, ← hx d a]
  linear_combination (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * x d a) * h2

/- English proof (translation)
Simplify using `only [symplOHF, symplOF, hOF_half he hx hy, mul_zero, map_zero]`.
-/
theorem symplOHF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : symplOHF σ JS JT xi0 x y = 0 := by
  simp only [symplOHF, symplOF, hOF_half he hx hy, mul_zero, map_zero]

/- English proof (translation)
Take `⟨he1, he2, v, ε, hpl, hsum⟩` from `he`. Take `⟨α, rfl, hα1, hα0⟩` from `id hpl`. Take `⟨U, hU, hUf⟩` from `hg.level`. Use `haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩`. Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`.

Use `haveI : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)`. Use `set ε' := algebraMap (AF F) (AEF F E) (pairA F 0 α) with hε'`. Establish `hcc : cAF σ e * cAF σ e = cAF σ e` using `by rw [← map_mul, he1]`. Establish `hce : cAF σ e * ε' = cAF σ e`. Rewrite using `[← hsum]`.

Take the linear combination `he2 + hcc`. Establish `hu' : ∀ i j, ε' * u i j = u i j` using `fun i j => by`. Use `hu i j` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Set `φ : Af F → WOF F E nS nT` to `fun t i j => algebraMap (AF F) (AEF F E) (pairA F 0 t) * u i j`.

Establish `hφ : Continuous φ`. Establish `h1 : Continuous fun t : Af F => algebraMap (AF F) (AEF F E) (pairA F 0 t)`. Establish `: Continuous fun t : Af F => pairA F 0 t` using `continuous_const.prodMk continuous_id`. Establish `h2 : Continuous fun c : AF F => algebraMap (AF F) (AEF F E) c`. Simplify using `only [Algebra.algebraMap_eq_smul_one]`.

Conclude with `continuous_smul.comp (continuous_id.prodMk continuous_const)`. Conclude with `h2.comp this`. Conclude with `continuous_pi fun i => continuous_pi fun j => h1.mul continuous_const`. Establish `h0 : φ 0 = 0`. Use function extensionality and compare the values at `i j`.

Use `show algebraMap (AF F) (AEF F E) (pairA F 0 0) * u i j = 0`. Rewrite using `[show pairA F 0 0 = (0 : AF F) from rfl, map_zero, zero_mul]`. Establish `hV : φ ⁻¹' (U : Set (WOF F E nS nT)) ∈ nhds (0 : Af F)` using `(hU.preimage hφ).mem_nhds (by rw [Set.mem_preimage, h0]; exact U.zero_mem)`. Take `⟨N, hN, hNα⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV`. Establish `hint : ∀ w, α w ∈ w.adicCompletionIntegers F` using `fun w => by`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[show α w = 1 from hα1]`. Conclude with `one_mem _`. Rewrite using `[show α w = 0 from hα0 w hw]`.

Conclude with `zero_mem _`. Establish `hmem` using `hNα α hint`. Establish `heq : φ (N • α) = N • u`. Use function extensionality and compare the values at `i j`. Use `show algebraMap (AF F) (AEF F E) (pairA F 0 (N • α)) * u i j = (N • u) i j`.

Rewrite using `[show pairA F 0 (N • α) = N • pairA F 0 α by show ((0 : Ainf F), N • α) = N • ((0 : Ainf F), α)`. Rewrite using `[Prod.smul_mk, smul_zero], map_nsmul, smul_mul_assoc, hu' i j, Matrix.smul_apply]`. Rewrite `hmem` using `[Set.mem_preimage, heq]`. Use `⟨N, hN, hUf _ hmem ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `show infPartF F E ((N • u) i j) = 0`. Rewrite using `[Matrix.smul_apply, map_nsmul, ← hu' i j, map_mul, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl, zero_mul, smul_zero]`.
-/
theorem exists_nsmul_fix {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT)
    {g : WOF F E nS nT → ℂ} (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT xi0 ψ (k • u) g = g := by
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := he
  obtain ⟨α, rfl, hα1, hα0⟩ := id hpl
  obtain ⟨U, hU, hUf⟩ := hg.level
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)
  set ε' := algebraMap (AF F) (AEF F E) (pairA F 0 α) with hε'
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hce : cAF σ e * ε' = cAF σ e := by
    rw [← hsum]
    linear_combination he2 + hcc
  have hu' : ∀ i j, ε' * u i j = u i j := fun i j => by
    have := hu i j
    calc ε' * u i j = ε' * (cAF σ e * u i j) := by rw [this]
      _ = (cAF σ e * ε') * u i j := by ring
      _ = u i j := by rw [hce, this]
  let φ : Af F → WOF F E nS nT := fun t i j => algebraMap (AF F) (AEF F E) (pairA F 0 t) * u i j
  have hφ : Continuous φ := by
    have h1 : Continuous fun t : Af F => algebraMap (AF F) (AEF F E) (pairA F 0 t) := by
      have : Continuous fun t : Af F => pairA F 0 t := continuous_const.prodMk continuous_id
      have h2 : Continuous fun c : AF F => algebraMap (AF F) (AEF F E) c := by
        simp only [Algebra.algebraMap_eq_smul_one]
        exact continuous_smul.comp (continuous_id.prodMk continuous_const)
      exact h2.comp this
    exact continuous_pi fun i => continuous_pi fun j => h1.mul continuous_const
  have h0 : φ 0 = 0 := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 0) * u i j = 0
    rw [show pairA F 0 0 = (0 : AF F) from rfl, map_zero, zero_mul]
  have hV : φ ⁻¹' (U : Set (WOF F E nS nT)) ∈ nhds (0 : Af F) :=
    (hU.preimage hφ).mem_nhds (by rw [Set.mem_preimage, h0]; exact U.zero_mem)
  obtain ⟨N, hN, hNα⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  have hint : ∀ w, α w ∈ w.adicCompletionIntegers F := fun w => by
    by_cases hw : w = v
    · subst hw
      rw [show α w = 1 from hα1]
      exact one_mem _
    · rw [show α w = 0 from hα0 w hw]
      exact zero_mem _
  have hmem := hNα α hint
  have heq : φ (N • α) = N • u := by
    funext i j
    show algebraMap (AF F) (AEF F E) (pairA F 0 (N • α)) * u i j = (N • u) i j
    rw [show pairA F 0 (N • α) = N • pairA F 0 α by
      show ((0 : Ainf F), N • α) = N • ((0 : Ainf F), α)
      rw [Prod.smul_mk, smul_zero], map_nsmul, smul_mul_assoc, hu' i j, Matrix.smul_apply]
  rw [Set.mem_preimage, heq] at hmem
  refine ⟨N, hN, hUf _ hmem ?_⟩
  ext i j
  show infPartF F E ((N • u) i j) = 0
  rw [Matrix.smul_apply, map_nsmul, ← hu' i j, map_mul, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl, zero_mul, smul_zero]

end GlobalTheory.SplitInvFormF

end
