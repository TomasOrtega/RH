import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRingsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.SeqDim

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

include PD in
/- English proof (translation)
Use `nontrivial_of_ne PD.t 0 ?_` and prove the remaining obligations. Introduce `h`. Apply `PD.not_mem_filtration_two` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Conclude with `(PD.Fil 2).zero_mem`.
-/
theorem nontrivial_B : Nontrivial B := by
  refine nontrivial_of_ne PD.t 0 ?_
  intro h
  apply PD.not_mem_filtration_two
  rw [h, map_zero]
  exact (PD.Fil 2).zero_mem

def incl : V →ₗ[LL] V ⊗[Qp] B where
  toFun v := v ⊗ₜ[Qp] (1 : B)
  map_add' a b := add_tmul a b 1
  map_smul' c v := (smul_tmul' c v (1 : B)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_apply (v : V) : incl (Qp := Qp) (B := B) (LL := LL) v = v ⊗ₜ[Qp] (1 : B) := rfl

include PD in
/- English proof (translation)
Use `haveI := nontrivial_B PD`. Establish `h1 : Function.Injective (Algebra.linearMap Qp B)` using `(algebraMap Qp B).injective`. Establish `h2` using `Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h1`. Introduce `a b hab`. Establish `: (TensorProduct.rid Qp V).symm a = (TensorProduct.rid Qp V).symm b`.

Apply `h2` to reduce the goal to its premises. Simplify `hab` using `[TensorProduct.rid_symm_apply]`. Conclude with `(TensorProduct.rid Qp V).symm.injective this`.
-/
theorem incl_injective : Function.Injective (fun v : V => v ⊗ₜ[Qp] (1 : B)) := by
  haveI := nontrivial_B PD
  have h1 : Function.Injective (Algebra.linearMap Qp B) := (algebraMap Qp B).injective
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h1
  intro a b hab
  have : (TensorProduct.rid Qp V).symm a = (TensorProduct.rid Qp V).symm b := by
    apply h2
    simpa [TensorProduct.rid_symm_apply] using hab
  exact (TensorProduct.rid Qp V).symm.injective this

/- English proof (translation)
Simplify using `[actVB]`.
-/
theorem actVB_incl (g : G) (v : V) :
    actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = (ρ g v) ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

/- English proof (translation)
Simplify using `[φVB]`.
-/
theorem φVB_incl (v : V) : φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
  simp [φVB]

/- English proof (translation)
Use `⟨v ⊗ₜ[Qp] (⟨1, PD.one_mem⟩ : (PD.Fil 0).restrictScalars Qp), ?_⟩` and prove the remaining obligations. Simplify using `[ιV]`.
-/
theorem ιV_incl_mem (v : V) : ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) ∈ FilV PD (LL := LL) (V := V) 0 := by
  refine ⟨v ⊗ₜ[Qp] (⟨1, PD.one_mem⟩ : (PD.Fil 0).restrictScalars Qp), ?_⟩
  simp [ιV]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def E : Submodule LL (V ⊗[Qp] B) where
  carrier := {x | ∃ c ∈ finiteCocycles PD ρ, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨0, (finiteCocycles PD ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩
    refine ⟨c + d, (finiteCocycles PD ρ).add_mem hc hd, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro a x ⟨c, hc, hx⟩
    refine ⟨a • c, (finiteCocycles PD ρ).smul_mem a hc, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

include PD in
/- English proof (translation)
The claim follows from `funext fun g => incl_injective PD (show c g ⊗ₜ[Qp] (1 : B) = c' g ⊗ₜ[Qp] (1 : B) by rw [hc, hc'])`.
-/
theorem cob_unique {x : V ⊗[Qp] B} {c c' : G → V}
    (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
    (hc' : ∀ g, c' g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) : c = c' :=
  funext fun g => incl_injective PD (show c g ⊗ₜ[Qp] (1 : B) = c' g ⊗ₜ[Qp] (1 : B) by rw [hc, hc'])

def cE : E PD ρ →ₗ[LL] finiteCocycles PD ρ where
  toFun x := ⟨x.2.choose, x.2.choose_spec.1⟩
  map_add' x y := by
    apply Subtype.ext
    refine cob_unique PD ρ (x := ((x + y : E PD ρ) : V ⊗[Qp] B)) (x + y).2.choose_spec.2 ?_
    intro g
    simp only [Submodule.coe_add, Pi.add_apply, add_tmul, x.2.choose_spec.2, y.2.choose_spec.2, map_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    refine cob_unique PD ρ (x := ((a • x : E PD ρ) : V ⊗[Qp] B)) (a • x).2.choose_spec.2 ?_
    intro g
    have hx := x.2.choose_spec.2 g
    change (a • x.2.choose g) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (a • (x : V ⊗[Qp] B)) - a • (x : V ⊗[Qp] B)
    rw [← TensorProduct.smul_tmul', hx, map_smul, smul_sub]

/- English proof (translation)
The claim follows from `x.2.choose_spec.2 g`.
-/
theorem cE_spec (x : E PD ρ) (g : G) :
    ((cE PD ρ x : finiteCocycles PD ρ) : G → V) g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x :=
  x.2.choose_spec.2 g

/- English proof (translation)
The claim follows from `cob_unique PD ρ (cE_spec PD ρ x) hc`.
-/
theorem cE_eq (x : E PD ρ) (c : G → V) (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    ((cE PD ρ x : finiteCocycles PD ρ) : G → V) = c :=
  cob_unique PD ρ (cE_spec PD ρ x) hc

/- English proof (translation)
Simplify using `[Dcris, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_Dcris (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Introduce `x hx`. Use `⟨0, (finiteCocycles PD ρ).zero_mem, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[(mem_Dcris PD ρ x).1 hx g]`. Simplify using the standard rewrite rules.
-/
theorem Dcris_le_E : Dcris PD ρ ≤ E PD ρ := by
  intro x hx
  refine ⟨0, (finiteCocycles PD ρ).zero_mem, fun g => ?_⟩
  rw [(mem_Dcris PD ρ x).1 hx g]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cob_apply (v : V) (g : G) : cob ρ v g = ρ g v - v := rfl

/- English proof (translation)
Use `⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩` and prove the remaining obligations. Establish `: (cob ρ v : G → V) = fun g => ρ g v + (-v)`. Use function extensionality and compare the values at `g`. Rewrite using `[cob_apply, sub_eq_add_neg]`. Rewrite using `[this]`.

Conclude with `(hρ v).add continuous_const`. Simplify using `only [cob_apply, map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[actVB_incl, cob_apply, sub_tmul]`.
-/
theorem coboundary_mem_blochKatoCocycles (hρ : ∀ x, Continuous fun g => ρ g x) (v : V) : cob ρ v ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : (cob ρ v : G → V) = fun g => ρ g v + (-v) := by
      funext g; rw [cob_apply, sub_eq_add_neg]
    rw [this]
    exact (hρ v).add continuous_const
  · simp only [cob_apply, map_mul, Module.End.mul_apply, map_sub]
    abel
  · rw [actVB_incl, cob_apply, sub_tmul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨cob ρ v, coboundary_mem_blochKatoCocycles PD ρ hρ v, fun g => by rw [actVB_incl, cob_apply, sub_tmul]⟩`.
-/
theorem incl_mem_E (hρ : ∀ x, Continuous fun g => ρ g x) (v : V) :
    v ⊗ₜ[Qp] (1 : B) ∈ E PD ρ :=
  ⟨cob ρ v, coboundary_mem_blochKatoCocycles PD ρ hρ v, fun g => by rw [actVB_incl, cob_apply, sub_tmul]⟩

def Θ : E PD ρ →ₗ[LL] FiniteCohomology PD ρ :=
  (Submodule.mkQ ((B1 ρ).comap (finiteCocycles PD ρ).subtype)).comp (cE PD ρ)

/- English proof (translation)
Introduce `q`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨hc, x, hx⟩` from `c.2`. Use `⟨⟨x, c, c.2, hx⟩, ?_⟩` and prove the remaining obligations. Establish `: cE PD ρ ⟨x, c, c.2, hx⟩ = c` using `Subtype.ext (cE_eq PD ρ _ _ hx)`.

Simplify using `only [Θ, LinearMap.comp_apply, this, Submodule.mkQ_apply]`.
-/
theorem Θ_surjective : Function.Surjective (Θ PD ρ) := by
  intro q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨hc, x, hx⟩ := c.2
  refine ⟨⟨x, c, c.2, hx⟩, ?_⟩
  have : cE PD ρ ⟨x, c, c.2, hx⟩ = c := Subtype.ext (cE_eq PD ρ _ _ hx)
  simp only [Θ, LinearMap.comp_apply, this, Submodule.mkQ_apply]

/- English proof (translation)
Rewrite using `[LinearMap.mem_ker, Θ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`. Rewrite using `[Submodule.mem_sup]`. Use `⟨(x : V ⊗[Qp] B) - v ⊗ₜ[Qp] (1 : B), ?_, v ⊗ₜ[Qp] (1 : B), ⟨v, rfl⟩, sub_add_cancel _ _⟩` and prove the remaining obligations.

Rewrite using `[mem_Dcris]`. Introduce `g`. Establish `h1` using `cE_spec PD ρ x g`. Rewrite `h1` using `[← hv, cob_apply, sub_tmul]`. Rewrite using `[map_sub, actVB_incl]`.

Rewrite using `[← sub_eq_zero]`. Establish `: actVB PD ρ g (x : V ⊗[Qp] B) - ρ g v ⊗ₜ[Qp] (1 : B) - ((x : V ⊗[Qp] B) - v ⊗ₜ[Qp] (1 : B)) = (actVB PD ρ g (x : V ⊗[Qp] B) - x) - (ρ g v ⊗ₜ[Qp] (1 : B) - v ⊗ₜ[Qp] (1 : B))` using `by abel`. Rewrite using `[this, ← h1, sub_self]`. Introduce `hx`. Take `⟨d, hd, w, ⟨v, rfl⟩, hdw⟩` from `Submodule.mem_sup.1 hx`.

Use `⟨v, ?_⟩` and prove the remaining obligations. Use `symm`. Apply `cE_eq` to reduce the goal to its premises. Introduce `g`. Rewrite using `[cob_apply, sub_tmul, ← hdw, map_add, (mem_Dcris PD ρ d).1 hd g, incl_apply, actVB_incl]`.

Normalize the expressions using the abelian group laws.
-/
theorem mem_ker_Θ (hρ : ∀ x, Continuous fun g => ρ g x) (x : E PD ρ) :
    x ∈ LinearMap.ker (Θ PD ρ) ↔ (x : V ⊗[Qp] B) ∈ Dcris PD ρ ⊔ LinearMap.range (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) := by
  rw [LinearMap.mem_ker, Θ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨v, hv⟩
    rw [Submodule.mem_sup]
    refine ⟨(x : V ⊗[Qp] B) - v ⊗ₜ[Qp] (1 : B), ?_, v ⊗ₜ[Qp] (1 : B), ⟨v, rfl⟩, sub_add_cancel _ _⟩
    rw [mem_Dcris]
    intro g
    have h1 := cE_spec PD ρ x g
    rw [← hv, cob_apply, sub_tmul] at h1
    rw [map_sub, actVB_incl]
    rw [← sub_eq_zero]
    have : actVB PD ρ g (x : V ⊗[Qp] B) - ρ g v ⊗ₜ[Qp] (1 : B) - ((x : V ⊗[Qp] B) - v ⊗ₜ[Qp] (1 : B)) =
        (actVB PD ρ g (x : V ⊗[Qp] B) - x) - (ρ g v ⊗ₜ[Qp] (1 : B) - v ⊗ₜ[Qp] (1 : B)) := by abel
    rw [this, ← h1, sub_self]
  · intro hx
    obtain ⟨d, hd, w, ⟨v, rfl⟩, hdw⟩ := Submodule.mem_sup.1 hx
    refine ⟨v, ?_⟩
    symm
    apply cE_eq
    intro g
    rw [cob_apply, sub_tmul, ← hdw, map_add, (mem_Dcris PD ρ d).1 hd g, incl_apply, actVB_incl]
    abel

section abelian₂

variable (hinj : ∀ (c : G → V) (x : V ⊗[Qp] B), (∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) →
      x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ ∧
        ∃ d ∈ DdR PD ρ, ιV PD (LL := LL) (V := V) x - d ∈ FilV PD (LL := LL) (V := V) 0)

abbrev F0 : Submodule LL (DdR PD ρ) := (FilV PD (LL := LL) (V := V) 0).comap (DdR PD ρ).subtype

def Λ₁ : E PD ρ →ₗ[LL] Dcris PD ρ :=
  LinearMap.codRestrict (Dcris PD ρ)
    ((LinearMap.id - φVB PD (LL := LL) (V := V)).comp (E PD ρ).subtype)
    (fun x => (hinj _ _ (cE_spec PD ρ x)).1)

def dE (x : E PD ρ) : DdR PD ρ :=
  ⟨(hinj _ _ (cE_spec PD ρ x)).2.choose, (hinj _ _ (cE_spec PD ρ x)).2.choose_spec.1⟩

/- English proof (translation)
The claim follows from `(hinj _ _ (cE_spec PD ρ x)).2.choose_spec.2`.
-/
theorem dE_spec (x : E PD ρ) :
    ιV PD (LL := LL) (V := V) (x : V ⊗[Qp] B) - (dE PD ρ hinj x : V ⊗[Qp] BdR) ∈ FilV PD (LL := LL) (V := V) 0 :=
  (hinj _ _ (cE_spec PD ρ x)).2.choose_spec.2

def Λ₂ : E PD ρ →ₗ[LL] (DdR PD ρ ⧸ F0 PD ρ) where
  toFun x := Submodule.Quotient.mk (dE PD ρ hinj x)
  map_add' x y := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.mem_comap]
    have h := (FilV PD (LL := LL) (V := V) 0).sub_mem
      ((FilV PD (LL := LL) (V := V) 0).add_mem (dE_spec PD ρ hinj x) (dE_spec PD ρ hinj y))
      (dE_spec PD ρ hinj (x + y))
    convert h using 1
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.subtype_apply, map_add]
    abel
  map_smul' a x := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
    have h := (FilV PD (LL := LL) (V := V) 0).sub_mem
      ((FilV PD (LL := LL) (V := V) 0).smul_mem a (dE_spec PD ρ hinj x))
      (dE_spec PD ρ hinj (a • x))
    convert h using 1
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.subtype_apply, map_smul, smul_sub]
    abel

def Λ : E PD ρ →ₗ[LL] (Dcris PD ρ × (DdR PD ρ ⧸ F0 PD ρ)) := LinearMap.prod (Λ₁ PD ρ hinj) (Λ₂ PD ρ hinj)

/- English proof (translation)
Rewrite using `[LinearMap.mem_ker, Λ, LinearMap.prod_apply, Prod.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : (x : V ⊗[Qp] B) - φVB PD (LL` using `LL) (V := V) x = 0 := congrArg Subtype.val h1`. Establish `h2'` using `(Submodule.Quotient.mk_eq_zero _).1 h2`.

Rewrite `h2'` using `[Submodule.mem_comap]`. Take `⟨v, hv⟩` from `hker x (sub_eq_zero.1 h1').symm (by`. Use `(FilV PD (LL := LL) (V := V) 0).add_mem (dE_spec PD ρ hinj x) h2'` as an intermediate fact. Simplify using `using this)`. Conclude with `⟨v, hv.symm⟩`.

Introduce and unpack `⟨v, hv⟩`. Rewrite `hv` using `[incl_apply]`. Prove the components needed by the constructor for the conclusion. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(x : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) x = 0`.

Rewrite using `[← hv, φVB_incl, sub_self]`. Apply `(Submodule.Quotient.mk_eq_zero _).2` to reduce the goal to its premises. Rewrite using `[Submodule.mem_comap, Submodule.subtype_apply]`. Establish `h` using `(FilV PD (LL := LL) (V := V) 0).sub_mem (ιV_incl_mem PD (LL := LL) v) (dE_spec PD ρ hinj x)`. Rewrite `h` using `[← hv]`.

Simplify using `using h`.
-/
theorem mem_ker_Λ (hρ : ∀ x, Continuous fun g => ρ g x)
    (hker : ∀ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x →
      ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B))
    (x : E PD ρ) :
    x ∈ LinearMap.ker (Λ PD ρ hinj) ↔ (x : V ⊗[Qp] B) ∈ LinearMap.range (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) := by
  rw [LinearMap.mem_ker, Λ, LinearMap.prod_apply, Prod.mk_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (x : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) x = 0 := congrArg Subtype.val h1
    have h2' := (Submodule.Quotient.mk_eq_zero _).1 h2
    rw [Submodule.mem_comap] at h2'
    obtain ⟨v, hv⟩ := hker x (sub_eq_zero.1 h1').symm (by
      have := (FilV PD (LL := LL) (V := V) 0).add_mem (dE_spec PD ρ hinj x) h2'
      simpa using this)
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, hv⟩
    rw [incl_apply] at hv
    constructor
    · apply Subtype.ext
      change (x : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) x = 0
      rw [← hv, φVB_incl, sub_self]
    · apply (Submodule.Quotient.mk_eq_zero _).2
      rw [Submodule.mem_comap, Submodule.subtype_apply]
      have h := (FilV PD (LL := LL) (V := V) 0).sub_mem (ιV_incl_mem PD (LL := LL) v) (dE_spec PD ρ hinj x)
      rw [← hv] at h
      simpa using h

/- English proof (translation)
Introduce and unpack `⟨d₁, q⟩`. Take `⟨d₂, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨x, y, c, hy, h1, h2, hc, hcx⟩` from `hdel d₁ d₁.2 d₂ d₂.2`. Use `⟨⟨x, c, hc, hcx⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Λ, LinearMap.prod_apply]`.

Use `Prod.ext (Subtype.ext h1) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply]`. Establish `h` using `(FilV PD (LL := LL) (V := V) 0).sub_mem hy (dE_spec PD ρ hinj ⟨x, c, hc, hcx⟩)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Submodule.coe_sub, ← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem Λ_surjective
    (hdel : ∀ d₁ ∈ Dcris PD ρ, ∀ d₂ ∈ DdR PD ρ, ∃ (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (c : G → V),
      y ∈ FilV PD (LL := LL) (V := V) 0 ∧ x - φVB PD (LL := LL) (V := V) x = d₁ ∧
      ιV PD (LL := LL) (V := V) x - y = d₂ ∧ c ∈ finiteCocycles PD ρ ∧ ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    Function.Surjective (Λ PD ρ hinj) := by
  rintro ⟨d₁, q⟩
  obtain ⟨d₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨x, y, c, hy, h1, h2, hc, hcx⟩ := hdel d₁ d₁.2 d₂ d₂.2
  refine ⟨⟨x, c, hc, hcx⟩, ?_⟩
  rw [Λ, LinearMap.prod_apply]
  refine Prod.ext (Subtype.ext h1) ?_
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply]
  have h := (FilV PD (LL := LL) (V := V) 0).sub_mem hy (dE_spec PD ρ hinj ⟨x, c, hc, hcx⟩)
  convert h using 1
  simp only [Submodule.coe_sub, ← h2]
  abel

end abelian₂

/- English proof (translation)
Simplify using `[H0V, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_H0V (v : V) : v ∈ H0V ρ ↔ ∀ g, ρ g v = v := by
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, v, rfl⟩`. Use `⟨v, (mem_H0V ρ v).2 fun g => ?_, rfl⟩` and prove the remaining obligations. Apply `incl_injective PD` to reduce the goal to its premises.

Use `(mem_Dcris PD ρ _).1 hy g` as an intermediate fact. Rewrite `this` using `[incl_apply, actVB_incl]`. Conclude with `this`. Introduce and unpack `⟨v, hv, rfl⟩`. Use `⟨(mem_Dcris PD ρ _).2 fun g => ?_, v, rfl⟩` and prove the remaining obligations.

Rewrite using `[incl_apply, actVB_incl, (mem_H0V ρ v).1 hv g]`.
-/
theorem Dcris_inf_range :
    Dcris PD ρ ⊓ LinearMap.range (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) =
      (H0V ρ).map (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) := by
  ext y
  constructor
  · rintro ⟨hy, v, rfl⟩
    refine ⟨v, (mem_H0V ρ v).2 fun g => ?_, rfl⟩
    apply incl_injective PD
    have := (mem_Dcris PD ρ _).1 hy g
    rw [incl_apply, actVB_incl] at this
    exact this
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(mem_Dcris PD ρ _).2 fun g => ?_, v, rfl⟩
    rw [incl_apply, actVB_incl, (mem_H0V ρ v).1 hv g]

/- English proof (translation)
Establish `hinc : Function.Injective (incl (Qp` using `Qp) (B := B) (LL := LL) (V := V)) := incl_injective PD`. Use `set R := LinearMap.range (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) with hR`. Establish `hRE : R ≤ E PD ρ`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `incl_mem_E PD ρ hρ v`.

Establish `hRfr : finrank LL R = finrank LL V` using `LinearMap.finrank_range_of_inj hinc`. Use `haveI : Module.Finite LL R := Module.Finite.range _`. Establish `hkerΛ : LinearMap.ker (Λ PD ρ hinj) = R.comap (E PD ρ).subtype`. Use extensionality with `x`. Rewrite using `[mem_ker_Λ PD ρ hinj hρ hker x]`.

Both sides reduce to the same expression. Establish `ekΛ : LinearMap.ker (Λ PD ρ hinj) ≃ₗ[LL] R` using `(LinearEquiv.ofEq _ _ hkerΛ).trans (Submodule.comapSubtypeEquivOfLe hRE)`. Use `haveI : Module.Finite LL (LinearMap.ker (Λ PD ρ hinj)) := Module.Finite.equiv ekΛ.symm`. Use `haveI : Module.Finite LL (E PD ρ) := by`. Rewrite using `[Module.finite_def]`.

Use `Submodule.fg_of_fg_map_of_fg_inf_ker (Λ PD ρ hinj) ?_ ?_` and prove the remaining obligations. Conclude with `IsNoetherian.noetherian _`. Rewrite using `[top_inf_eq]`. Conclude with `Module.Finite.iff_fg.mp inferInstance`. Use `set S := Dcris PD ρ ⊔ R with hS`.

Establish `hSE : S ≤ E PD ρ` using `sup_le (Dcris_le_E PD ρ) hRE`. Establish `hkerΘ : LinearMap.ker (Θ PD ρ) = S.comap (E PD ρ).subtype`. Use extensionality with `x`. Rewrite using `[mem_ker_Θ PD ρ hρ x]`. Both sides reduce to the same expression.

Establish `frkerΘ : finrank LL (LinearMap.ker (Θ PD ρ)) = finrank LL S` using `((LinearEquiv.ofEq _ _ hkerΘ).trans (Submodule.comapSubtypeEquivOfLe hSE)).finrank_eq`. Use `haveI : Module.Finite LL (FiniteCohomology PD ρ) := Module.Finite.of_surjective _ (Θ_surjective PD ρ)`. Establish `ha` using `LinearMap.finrank_range_add_finrank_ker (Θ PD ρ)`. Rewrite `ha` using `[LinearMap.range_eq_top.2 (Θ_surjective PD ρ), finrank_top, frkerΘ]`. Establish `hb` using `Submodule.finrank_sup_add_finrank_inf_eq (Dcris PD ρ) R`.

Rewrite `hb` using `[← hS, Dcris_inf_range PD ρ, ← (Submodule.equivMapOfInjective _ hinc _).finrank_eq, hRfr]`. Establish `hc` using `LinearMap.finrank_range_add_finrank_ker (Λ PD ρ hinj)`. Rewrite `hc` using `[LinearMap.range_eq_top.2 (Λ_surjective PD ρ hinj hdel), finrank_top, Module.finrank_prod, ekΛ.finrank_eq, hRfr]`. Establish `hd` using `Submodule.finrank_quotient_add_finrank (F0 PD ρ)`. Establish `he : finrank LL (F0 PD ρ) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL` using `LL) (V := V) 0) := by`.

Rewrite using `[← Submodule.map_comap_subtype]`. Conclude with `(Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[← he, ← hd]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers.
-/
theorem H1f_dim_formula [FiniteDimensional LL V]
    (hρ : ∀ x, Continuous fun g => ρ g x)
    (hker : ∀ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x →
      ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B))
    (hdel : ∀ d₁ ∈ Dcris PD ρ, ∀ d₂ ∈ DdR PD ρ, ∃ (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (c : G → V),
      y ∈ FilV PD (LL := LL) (V := V) 0 ∧ x - φVB PD (LL := LL) (V := V) x = d₁ ∧
      ιV PD (LL := LL) (V := V) x - y = d₂ ∧ c ∈ finiteCocycles PD ρ ∧ ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
    (hinj : ∀ (c : G → V) (x : V ⊗[Qp] B), (∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) →
      x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ ∧
        ∃ d ∈ DdR PD ρ, ιV PD (LL := LL) (V := V) x - d ∈ FilV PD (LL := LL) (V := V) 0)
    (hC : Module.Finite LL (Dcris PD ρ)) (hD : Module.Finite LL (DdR PD ρ)) :
    Module.Finite LL (FiniteCohomology PD ρ) ∧
      (finrank LL (FiniteCohomology PD ρ) : ℤ) = finrank LL ↥(H0V ρ) +
        ((finrank LL ↥(DdR PD ρ) : ℤ) - finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) := by
  classical
  have hinc : Function.Injective (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) := incl_injective PD
  set R := LinearMap.range (incl (Qp := Qp) (B := B) (LL := LL) (V := V)) with hR
  have hRE : R ≤ E PD ρ := by
    rintro _ ⟨v, rfl⟩
    exact incl_mem_E PD ρ hρ v
  have hRfr : finrank LL R = finrank LL V := LinearMap.finrank_range_of_inj hinc
  haveI : Module.Finite LL R := Module.Finite.range _
  have hkerΛ : LinearMap.ker (Λ PD ρ hinj) = R.comap (E PD ρ).subtype := by
    ext x
    rw [mem_ker_Λ PD ρ hinj hρ hker x]
    rfl
  have ekΛ : LinearMap.ker (Λ PD ρ hinj) ≃ₗ[LL] R :=
    (LinearEquiv.ofEq _ _ hkerΛ).trans (Submodule.comapSubtypeEquivOfLe hRE)
  haveI : Module.Finite LL (LinearMap.ker (Λ PD ρ hinj)) := Module.Finite.equiv ekΛ.symm
  haveI : Module.Finite LL (E PD ρ) := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Λ PD ρ hinj) ?_ ?_
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact Module.Finite.iff_fg.mp inferInstance
  set S := Dcris PD ρ ⊔ R with hS
  have hSE : S ≤ E PD ρ := sup_le (Dcris_le_E PD ρ) hRE
  have hkerΘ : LinearMap.ker (Θ PD ρ) = S.comap (E PD ρ).subtype := by
    ext x
    rw [mem_ker_Θ PD ρ hρ x]
    rfl
  have frkerΘ : finrank LL (LinearMap.ker (Θ PD ρ)) = finrank LL S :=
    ((LinearEquiv.ofEq _ _ hkerΘ).trans (Submodule.comapSubtypeEquivOfLe hSE)).finrank_eq
  haveI : Module.Finite LL (FiniteCohomology PD ρ) := Module.Finite.of_surjective _ (Θ_surjective PD ρ)
  have ha := LinearMap.finrank_range_add_finrank_ker (Θ PD ρ)
  rw [LinearMap.range_eq_top.2 (Θ_surjective PD ρ), finrank_top, frkerΘ] at ha
  have hb := Submodule.finrank_sup_add_finrank_inf_eq (Dcris PD ρ) R
  rw [← hS, Dcris_inf_range PD ρ, ← (Submodule.equivMapOfInjective _ hinc _).finrank_eq, hRfr] at hb
  have hc := LinearMap.finrank_range_add_finrank_ker (Λ PD ρ hinj)
  rw [LinearMap.range_eq_top.2 (Λ_surjective PD ρ hinj hdel), finrank_top, Module.finrank_prod,
    ekΛ.finrank_eq, hRfr] at hc
  have hd := Submodule.finrank_quotient_add_finrank (F0 PD ρ)
  have he : finrank LL (F0 PD ρ) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq
  refine ⟨inferInstance, ?_⟩
  rw [← he, ← hd]
  push_cast
  omega

end Gen

/- English proof (translation)
Introduce `l _ P AI hT K LL _ _ _ O _ _ hO A hdr`. Establish `hfs` using `GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K LL A.V`. Establish `hfont` using `GlobalTheory.T.fontaine_bounds_crystalline_deRham_concrete_rings l P AI hT K LL O hO A`. Conclude with `H1f_dim_formula (P.PD K) A.ρ A.cont hfs.2 (fun d₁ h₁ d₂ h₂ => GlobalTheory.FundDel.connecting_cocycle l P AI hT K LL O hO A d₁ h₁ d₂ h₂) (GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K LL O hO A hdr) hfont.1.1 hfont.2.1.1`.
-/
theorem h1f_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ →
      Module.Finite LL (FiniteCohomology (P.PD K) A.ρ) ∧
        (finrank LL (FiniteCohomology (P.PD K) A.ρ) : ℤ) = finrank LL ↥(H0V A.ρ) +
          ((finrank LL ↥(DdR (P.PD K) A.ρ) : ℤ) -
            finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0)) := by
  intro l _ P AI hT K LL _ _ _ O _ _ hO A hdr
  have hfs := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K LL A.V
  have hfont := GlobalTheory.T.fontaine_bounds_crystalline_deRham_concrete_rings l P AI hT K LL O hO A
  exact H1f_dim_formula (P.PD K) A.ρ A.cont hfs.2
    (fun d₁ h₁ d₂ h₂ => GlobalTheory.FundDel.connecting_cocycle l P AI hT K LL O hO A d₁ h₁ d₂ h₂)
    (GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K LL O hO A hdr) hfont.1.1 hfont.2.1.1

end GlobalTheory.SeqDim
