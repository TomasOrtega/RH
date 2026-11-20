import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

open TensorProduct Module

noncomputable section

namespace GlobalTheory.CrysSub

section Alg

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

/- English proof (translation)
Simplify using `[Dcris, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB, hf]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem rTensor_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PD ρ g x) =
      actVB PD σ g (AlgebraTensorModule.rTensor Qp B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

def Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) : Dcris PD ρ →ₗ[LL] Dcris PD σ :=
  (AlgebraTensorModule.rTensor Qp B f).restrict (fun x hx => by
    rw [mem_Dcris] at hx ⊢
    intro g
    rw [← rTensor_act PD ρ σ f hf, hx])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (x : Dcris PD ρ) :
    (Dmap PD ρ σ f hf x : W ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B f x := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem rTensor_eq (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Introduce `x hx`. Establish `h0 : (q.restrictScalars Qp).rTensor B (x : W ⊗[Qp] B) = 0`. Rewrite using `[← rTensor_eq, ← coe_Dmap PD σ τ q hq, LinearMap.mem_ker.mp hx]`. Both sides reduce to the same expression. Establish `hex : Function.Exact ((f.restrictScalars Qp).rTensor B) ((q.restrictScalars Qp).rTensor B)` using `rTensor_exact B (f := f.restrictScalars Qp) (g := q.restrictScalars Qp) he hs`.

Establish `hinj : Function.Injective ((f.restrictScalars Qp).rTensor B)` using `Module.Flat.rTensor_preserves_injective_linearMap _ hi`. Take `⟨y, hy⟩` from `(hex _).mp h0`. Rewrite `hy` using `[← rTensor_eq]`. Use `⟨⟨y, ?_⟩, Subtype.ext hy⟩` and prove the remaining obligations. Rewrite using `[mem_Dcris]`.

Introduce `g`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← rTensor_eq, ← rTensor_eq, rTensor_act PD ρ σ f hf, hy]`. Conclude with `(mem_Dcris PD σ _).mp x.2 g`.
-/
theorem exact_Dmap (ρ : Representation LL G V) (σ : Representation LL G W)
    (τ : Representation LL G U) (f : V →ₗ[LL] W) (q : W →ₗ[LL] U)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hq : ∀ g v, q (σ g v) = τ g (q v))
    (hi : Function.Injective f) (he : Function.Exact f q) (hs : Function.Surjective q) :
    LinearMap.ker (Dmap PD σ τ q hq) ≤ LinearMap.range (Dmap PD ρ σ f hf) := by
  intro x hx
  have h0 : (q.restrictScalars Qp).rTensor B (x : W ⊗[Qp] B) = 0 := by
    rw [← rTensor_eq, ← coe_Dmap PD σ τ q hq, LinearMap.mem_ker.mp hx]
    rfl
  have hex : Function.Exact ((f.restrictScalars Qp).rTensor B) ((q.restrictScalars Qp).rTensor B) :=
    rTensor_exact B (f := f.restrictScalars Qp) (g := q.restrictScalars Qp) he hs
  have hinj : Function.Injective ((f.restrictScalars Qp).rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨y, hy⟩ := (hex _).mp h0
  rw [← rTensor_eq] at hy
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  rw [mem_Dcris]
  intro g
  apply hinj
  rw [← rTensor_eq, ← rTensor_eq, rTensor_act PD ρ σ f hf, hy]
  exact (mem_Dcris PD σ _).mp x.2 g

/- English proof (translation)
Establish `hk : Module.Finite LL (LinearMap.ker q)` using `Submodule.finiteDimensional_of_le h`. Establish `hq : Module.Finite LL (A₂ ⧸ LinearMap.ker q)` using `Module.Finite.equiv (q.quotKerEquivRange).symm`. Establish `h2 : Module.Finite LL A₂` using `Module.Finite.of_submodule_quotient (LinearMap.ker q)`. Use `⟨h2, ?_⟩` and prove the remaining obligations. Establish `h3` using `q.finrank_range_add_finrank_ker`.

Establish `h4` using `Submodule.finrank_mono h`. Establish `h5` using `f.finrank_range_le`. Establish `h6` using `(LinearMap.range q).finrank_le`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_of_ker_le {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [Module LL A₁]
    [AddCommGroup A₂] [Module LL A₂] [AddCommGroup A₃] [Module LL A₃]
    [Module.Finite LL A₁] [Module.Finite LL A₃] (f : A₁ →ₗ[LL] A₂) (q : A₂ →ₗ[LL] A₃)
    (h : LinearMap.ker q ≤ LinearMap.range f) :
    Module.Finite LL A₂ ∧ finrank LL A₂ ≤ finrank LL A₁ + finrank LL A₃ := by
  have hk : Module.Finite LL (LinearMap.ker q) := Submodule.finiteDimensional_of_le h
  have hq : Module.Finite LL (A₂ ⧸ LinearMap.ker q) :=
    Module.Finite.equiv (q.quotKerEquivRange).symm
  have h2 : Module.Finite LL A₂ := Module.Finite.of_submodule_quotient (LinearMap.ker q)
  refine ⟨h2, ?_⟩
  have h3 := q.finrank_range_add_finrank_ker
  have h4 := Submodule.finrank_mono h
  have h5 := f.finrank_range_le
  have h6 := (LinearMap.range q).finrank_le
  omega

def piRep {m : ℕ} (ρ : Fin m → Representation LL G V) : Representation LL G (Fin m → V) where
  toFun g := LinearMap.pi fun a => (ρ a g).comp (LinearMap.proj a)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem piRep_apply {m : ℕ} (ρ : Fin m → Representation LL G V) (g : G) (v : Fin m → V)
    (a : Fin m) : piRep ρ g v a = ρ a g (v a) := rfl

/- English proof (translation)
Establish `hp : ∀ a g v, (LinearMap.proj a : (Fin m → V) →ₗ[LL] V) (piRep ρ g v) = ρ a g ((LinearMap.proj a : (Fin m → V) →ₗ[LL] V) v)` using `fun a g v => rfl`. Establish `hs : ∀ a g v, (LinearMap.single LL (fun _ : Fin m => V) a) (ρ a g v) = piRep ρ g (LinearMap.single LL (fun _ : Fin m => V) a v)`. Introduce `a g v`. Use function extensionality and compare the values at `b`. Rewrite using `[piRep_apply]`.

Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Set `F : Dcris PD (piRep ρ) →ₗ[LL] (∀ a, Dcris PD (ρ a))` to `LinearMap.pi fun a => Dmap PD _ _ _ (hp a)`.

Establish `key : ∀ (a b : Fin m) (x : V ⊗[Qp] B), AlgebraTensorModule.rTensor Qp B (LinearMap.proj b : (Fin m → V) →ₗ[LL] V) (AlgebraTensorModule.rTensor Qp B (LinearMap.single LL (fun _ : Fin m => V) a) x) = if a = b then x else 0`. Introduce `a b x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v c`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Pi.single_eq_of_ne (Ne.symm h)]`. Consider the case `add x y hx hy`.

Simplify using `only [map_add, hx, hy]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hF : Function.Surjective F`. Introduce `y`. Use `⟨∑ a, Dmap PD _ _ _ (hs a) (y a), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [F, LinearMap.pi_apply, coe_Dmap, Submodule.coe_sum, map_sum, key]`. Simplify using the standard rewrite rules. Establish `h1 : Module.Finite LL (∀ a, Dcris PD (ρ a))` using `Module.Finite.of_surjective F hF`.

Establish `h2 : ∀ a, Module.Finite LL (Dcris PD (ρ a))` using `fun a => Module.Finite.of_surjective (LinearMap.proj a : (∀ a, Dcris PD (ρ a)) →ₗ[LL] _) (LinearMap.proj_surjective a)`. Rewrite using `[← Module.finrank_pi_fintype]`. Conclude with `LinearMap.finrank_le_finrank_of_surjective hF`.
-/
theorem sum_le_finrank_piRep {m : ℕ} (ρ : Fin m → Representation LL G V)
    [Module.Finite LL (Dcris PD (piRep ρ))] :
    ∑ a, finrank LL (Dcris PD (ρ a)) ≤ finrank LL (Dcris PD (piRep ρ)) := by
  have hp : ∀ a g v, (LinearMap.proj a : (Fin m → V) →ₗ[LL] V) (piRep ρ g v) =
      ρ a g ((LinearMap.proj a : (Fin m → V) →ₗ[LL] V) v) := fun a g v => rfl
  have hs : ∀ a g v, (LinearMap.single LL (fun _ : Fin m => V) a) (ρ a g v) =
      piRep ρ g (LinearMap.single LL (fun _ : Fin m => V) a v) := by
    intro a g v
    funext b
    rw [piRep_apply]
    by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  let F : Dcris PD (piRep ρ) →ₗ[LL] (∀ a, Dcris PD (ρ a)) :=
    LinearMap.pi fun a => Dmap PD _ _ _ (hp a)
  have key : ∀ (a b : Fin m) (x : V ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.proj b : (Fin m → V) →ₗ[LL] V)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.single LL (fun _ : Fin m => V) a) x) =
        if a = b then x else 0 := by
    intro a b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      by_cases h : a = b
      · subst h; simp
      · simp [h, Pi.single_eq_of_ne (Ne.symm h)]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      split_ifs <;> simp
  have hF : Function.Surjective F := by
    intro y
    refine ⟨∑ a, Dmap PD _ _ _ (hs a) (y a), ?_⟩
    funext b
    apply Subtype.ext
    simp only [F, LinearMap.pi_apply, coe_Dmap, Submodule.coe_sum, map_sum, key]
    simp
  have h1 : Module.Finite LL (∀ a, Dcris PD (ρ a)) := Module.Finite.of_surjective F hF
  have h2 : ∀ a, Module.Finite LL (Dcris PD (ρ a)) := fun a =>
    Module.Finite.of_surjective (LinearMap.proj a : (∀ a, Dcris PD (ρ a)) →ₗ[LL] _)
      (LinearMap.proj_surjective a)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective hF

end Alg

/- English proof (translation)
Introduce `G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ O _ _ hF hO A ι k Ms hc hsub hcr`. Take `⟨m, xs, j, hj, hjg⟩` from `hsub`. Establish `htr : IsTopologicalRing LL` using `hO.2.2.2.1`. Set `σ : Representation LL G (Fin m → Fin k → LL)` to `piRep fun a => matRep (Ms (xs a))`. Establish `hσ : ∀ g v a, σ g v a = (Ms (xs a) g).mulVec (v a)`.

Introduce `g v a`. Simplify using `[σ, piRep_apply, matRep, Matrix.toLinAlgEquiv'_apply]`. Establish `hjσ : ∀ g v, j (A.ρ g v) = σ g (j v)`. Introduce `g v`. Rewrite using `[hjg]`.

Use function extensionality and compare the values at `a`. Rewrite using `[hσ]`. Establish `hst : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (σ g)`. Introduce and unpack `g _ ⟨v, rfl⟩`. Conclude with `⟨A.ρ g v, hjσ g v⟩`.

Establish `hσc : ∀ v, Continuous fun g => σ g v`. Introduce `v`. Use `continuous_pi fun a => ?_` and prove the remaining obligations. Simplify using `only [hσ]`. Conclude with `(hc (xs a)).matrix_mulVec continuous_const`.

Set `τ` to `σ.quotient (LinearMap.range j) hst`. Establish `hτ : ∀ g v, (LinearMap.range j).mkQ (σ g v) = τ g ((LinearMap.range j).mkQ v)` using `fun g v => rfl`. Establish `: ContinuousSMul LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j)` using `IsModuleTopology.toContinuousSMul _ _`. Set `Q : GRep G Qp LL O` to `{ V := (Fin m → Fin k → LL) ⧸ LinearMap.range j ρ := τ cont := by`. Introduce `x`.

Take `⟨v, rfl⟩` from `(LinearMap.range j).mkQ_surjective x`. Simplify using `only [← hτ]`. Conclude with `continuous_quot_mk.comp (hσc v) }`. Take `⟨⟨fA, lA⟩, -⟩` from `hF LL O hO A`. Take `⟨⟨fQ, lQ⟩, -⟩` from `hF LL O hO Q`.

Establish `fQ' : Module.Finite LL (Dcris PD τ)` using `fQ`. Establish `lQ' : finrank LL (Dcris PD τ) ≤ finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j)` using `lQ`. Take `⟨fS, lS⟩` from `finrank_le_of_ker_le _ _ (exact_Dmap PD A.ρ σ τ j (LinearMap.range j).mkQ hjσ hτ hj (LinearMap.exact_map_mkQ_range j) (LinearMap.range j).mkQ_surjective)`. Establish `h1` using `sum_le_finrank_piRep PD (fun a => matRep (Ms (xs a)))`. Establish `h2 : ∀ a, finrank LL (Dcris PD (matRep (Ms (xs a)))) = finrank Qp K₀ * k`.

Introduce `a`. Use `hcr (xs a)` as an intermediate fact. Rewrite `this` using `[IsCrys]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Simplify using `only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1`. Establish `h3` using `(LinearMap.range j).finrank_quotient_add_finrank`. Rewrite `h3` using `[LinearMap.finrank_range_of_inj hj]`. Establish `h4 : finrank LL (Fin m → Fin k → LL) = m * k`. Simplify using `[Module.finrank_pi_fintype]`.

Establish `h5 : m * (finrank Qp K₀ * k) = finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) + finrank Qp K₀ * finrank LL A.V`. Rewrite using `[← mul_add, h3, h4]`. Expand and normalize the polynomial expressions, which then agree. Establish `h6 : finrank LL (Dcris PD (piRep fun a => matRep (Ms (xs a)))) = finrank LL (Dcris PD σ)` using `rfl`. Rewrite using `[IsCrys]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isCrys_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], Formalism.MainNotions.LocalSituation.fontCore PD → GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)), (∀ x, Continuous (Ms x)) → IsSubOfSums A.ρ (fun x g => Ms x g) → (∀ x, IsCrys PD (matRep (Ms x))) → IsCrys PD A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ O _ _ hF hO A ι k Ms
    hc hsub hcr
  obtain ⟨m, xs, j, hj, hjg⟩ := hsub
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let σ : Representation LL G (Fin m → Fin k → LL) := piRep fun a => matRep (Ms (xs a))
  have hσ : ∀ g v a, σ g v a = (Ms (xs a) g).mulVec (v a) := by
    intro g v a
    simp [σ, piRep_apply, matRep, Matrix.toLinAlgEquiv'_apply]
  have hjσ : ∀ g v, j (A.ρ g v) = σ g (j v) := by
    intro g v
    rw [hjg]
    funext a
    rw [hσ]
  have hst : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (σ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, hjσ g v⟩
  have hσc : ∀ v, Continuous fun g => σ g v := by
    intro v
    refine continuous_pi fun a => ?_
    simp only [hσ]
    exact (hc (xs a)).matrix_mulVec continuous_const
  let τ := σ.quotient (LinearMap.range j) hst
  have hτ : ∀ g v, (LinearMap.range j).mkQ (σ g v) = τ g ((LinearMap.range j).mkQ v) :=
    fun g v => rfl
  have : ContinuousSMul LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) :=
    IsModuleTopology.toContinuousSMul _ _
  let Q : GRep G Qp LL O :=
    { V := (Fin m → Fin k → LL) ⧸ LinearMap.range j
      ρ := τ
      cont := by
        intro x
        obtain ⟨v, rfl⟩ := (LinearMap.range j).mkQ_surjective x
        simp only [← hτ]
        exact continuous_quot_mk.comp (hσc v) }
  obtain ⟨⟨fA, lA⟩, -⟩ := hF LL O hO A
  obtain ⟨⟨fQ, lQ⟩, -⟩ := hF LL O hO Q
  have fQ' : Module.Finite LL (Dcris PD τ) := fQ
  have lQ' : finrank LL (Dcris PD τ) ≤
    finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) := lQ
  obtain ⟨fS, lS⟩ := finrank_le_of_ker_le _ _
    (exact_Dmap PD A.ρ σ τ j (LinearMap.range j).mkQ hjσ hτ hj
      (LinearMap.exact_map_mkQ_range j) (LinearMap.range j).mkQ_surjective)
  have h1 := sum_le_finrank_piRep PD (fun a => matRep (Ms (xs a)))
  have h2 : ∀ a, finrank LL (Dcris PD (matRep (Ms (xs a)))) = finrank Qp K₀ * k := by
    intro a
    have := hcr (xs a)
    rw [IsCrys] at this
    rw [this]
    simp
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h3 := (LinearMap.range j).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hj] at h3
  have h4 : finrank LL (Fin m → Fin k → LL) = m * k := by
    simp [Module.finrank_pi_fintype]
  have h5 : m * (finrank Qp K₀ * k) =
      finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) +
        finrank Qp K₀ * finrank LL A.V := by
    rw [← mul_add, h3, h4]; ring
  have h6 : finrank LL (Dcris PD (piRep fun a => matRep (Ms (xs a)))) = finrank LL (Dcris PD σ) := rfl
  rw [IsCrys]
  omega

end GlobalTheory.CrysSub
