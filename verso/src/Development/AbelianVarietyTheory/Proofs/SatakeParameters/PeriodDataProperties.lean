import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open TensorProduct

namespace GlobalTheory.SubSumJumps

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Use `⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp`.

Consider the case `add y z hy hz => simp only [map_add, hy, hz]`.
-/
theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/- English proof (translation)
Establish `h1 : ∀ (g : G) (y : V ⊗[Qp] BdR), actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y) = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVdR, hf]`.

Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Establish `h2 : ∀ (c : K) (y : V ⊗[Qp] BdR), mulVdR (K` using `K) (BdR := BdR) (V := V') (LL := LL) c (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y) = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y) := by`. Introduce `c y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v b => simp [mulVdR]`. Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Simplify using `only [DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢`. Use `⟨fun g => ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[h1, hx.1 g]`.

Rewrite using `[h2, hx.2 c, map_smul]`.
-/
theorem map_mem_DdRE (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdRE PD ρ τ) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ DdRE PD ρ' τ := by
  have h1 : ∀ (g : G) (y : V ⊗[Qp] BdR),
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, hf]
    | add y z hy hz => simp only [map_add, hy, hz]
  have h2 : ∀ (c : K) (y : V ⊗[Qp] BdR),
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c
        (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)
          (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVdR]
    | add y z hy hz => simp only [map_add, hy, hz]
  simp only [DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  refine ⟨fun g => ?_, fun c => ?_⟩
  · rw [h1, hx.1 g]
  · rw [h2, hx.2 c, map_smul]

/- English proof (translation)
Introduce and unpack `x ⟨y, rfl⟩`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩`. Consider the case `add y z hy hz => rw [map_add]`.

Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem FilV_anti (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

end

/- English proof (translation)
Introduce `G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ ι k Ms τ J hsub hJ a ha`. Assume the negation of the conclusion as `haJ`. Apply `ha` to reduce the goal to its premises. Take `⟨m, xs, j, hj, hje⟩` from `hsub`. Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)`.

Establish `hrv : ∀ v, r (j v) = v` using `fun v => LinearMap.congr_fun hr v`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `inf_le_inf_left _ (FilV_anti PD a)`. Introduce `x hx`. Use `⟨hx.1, ?_⟩` and prove the remaining obligations.

Set `p : Fin m → (V →ₗ[LL] (Fin k → LL))` to `fun b => (LinearMap.proj b).comp j`. Set `s : Fin m → ((Fin k → LL) →ₗ[LL] V)` to `fun b => r.comp (LinearMap.single LL (fun _ : Fin m => Fin k → LL) b)`. Establish `hdec : ∀ y : V ⊗[Qp] BdR, y = ∑ b, AlgebraTensorModule.map (s b) (LinearMap.id : BdR →ₗ[Qp] BdR) (AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) y)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v c`. Simplify using `only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]`. Use `congr 1`. Simplify using `only [s, p, LinearMap.comp_apply, ← map_sum]`.

Use `conv_lhs => rw [← hrv v]`. Use `congr 1`. Conclude with `(Finset.univ_sum_single (j v)).symm`. Consider the case `add y z hy hz`. Simplify using `only [map_add, Finset.sum_add_distrib]`.

Rewrite using `[← hy, ← hz]`. Rewrite using `[hdec x]`. Use `Submodule.sum_mem _ fun b _ => map_mem_FilV PD (s b) (a + 1) _ ?_` and prove the remaining obligations. Establish `heq : FildR PD (matRep (Ms (xs b))) τ (a + 1) = FildR PD (matRep (Ms (xs b))) τ a`. Assume the negation of the conclusion as `h`.

Conclude with `haJ (hJ (xs b) a h)`. Establish `hm : AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FildR PD (matRep (Ms (xs b))) τ a`. Use `⟨map_mem_DdRE PD ρ _ (p b) (fun g v => ?_) τ x hx.1, map_mem_FilV PD (p b) a x hx.2⟩` and prove the remaining obligations. Simplify using `[p, hje, matRep, Matrix.toLinAlgEquiv'_apply]`. Rewrite `hm` using `[← heq]`.

Conclude with `hm.2`.
-/
theorem jumpsInV_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (τ : K →ₐ[Qp] LL) (J : Set ℤ), IsSubOfSums ρ (fun x g => Ms x g) → (∀ x, JumpsInV PD (matRep (Ms x)) τ J) → JumpsInV PD ρ τ J := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ ι k Ms τ J
    hsub hJ a ha
  by_contra haJ
  apply ha
  obtain ⟨m, xs, j, hj, hje⟩ := hsub
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
  have hrv : ∀ v, r (j v) = v := fun v => LinearMap.congr_fun hr v
  apply le_antisymm
  · exact inf_le_inf_left _ (FilV_anti PD a)
  intro x hx
  refine ⟨hx.1, ?_⟩
  let p : Fin m → (V →ₗ[LL] (Fin k → LL)) := fun b => (LinearMap.proj b).comp j
  let s : Fin m → ((Fin k → LL) →ₗ[LL] V) := fun b =>
    r.comp (LinearMap.single LL (fun _ : Fin m => Fin k → LL) b)
  have hdec : ∀ y : V ⊗[Qp] BdR, y = ∑ b, AlgebraTensorModule.map (s b)
      (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]
      congr 1
      simp only [s, p, LinearMap.comp_apply, ← map_sum]
      conv_lhs => rw [← hrv v]
      congr 1
      exact (Finset.univ_sum_single (j v)).symm
    | add y z hy hz =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [← hy, ← hz]
  rw [hdec x]
  refine Submodule.sum_mem _ fun b _ => map_mem_FilV PD (s b) (a + 1) _ ?_
  have heq : FildR PD (matRep (Ms (xs b))) τ (a + 1) = FildR PD (matRep (Ms (xs b))) τ a := by
    by_contra h
    exact haJ (hJ (xs b) a h)
  have hm : AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FildR PD (matRep (Ms (xs b))) τ a := by
    refine ⟨map_mem_DdRE PD ρ _ (p b) (fun g v => ?_) τ x hx.1, map_mem_FilV PD (p b) a x hx.2⟩
    simp [p, hje, matRep, Matrix.toLinAlgEquiv'_apply]
  rw [← heq] at hm
  exact hm.2

end GlobalTheory.SubSumJumps
