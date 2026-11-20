import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

noncomputable section

namespace GlobalTheory.NegVan

/- English proof (translation)
Use `haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral`.
-/
private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

open TensorProduct in

/- English proof (translation)
Take `⟨⟨hcc, hcoc⟩, x, hx⟩` from `hc`. Take `⟨S, rfl⟩` from `TensorProduct.exists_finset x`. Take `⟨T⟩` from `Loc.tiedP l`. Use `haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)`. Use `haveI := fd_adjoin_range l (fun p : S => p.1.1)`.

Set `E : IntermediateField ℚ_[l] (PadicAlgCl l)` to `E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)`. Establish `hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E` using `fun g => (le_sup_left : E₀ ≤ E) (hκ g)`. Establish `hS : ∀ p ∈ S, p.1 ∈ E` using `fun p hp => (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)`. Take `⟨π, hπ⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l)) (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)`. Establish `hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y` using `fun y => LinearMap.congr_fun hπ y`.

Set `κ' : H →* Eˣ` to `MonoidHom.toHomUnits { toFun := fun g => ⟨κ g, hκE g⟩ map_one' := Subtype.ext (by simp) map_mul' := fun g h => Subtype.ext (by simp) }`. Establish `hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g` using `fun g => rfl`. Establish `hπ2 : ∀ g y, π (κ g * y) = κ' g * π y` using `fun g y => map_smul π (κ' g : E) y`. Set `f : PadicAlgCl l →ₗ[ℚ_[l]] E` to `π.restrictScalars ℚ_[l]`. Set `i : E →ₗ[ℚ_[l]] PadicAlgCl l` to `E.val.toLinearMap`.

Establish `key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) = Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) = Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Use `set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd`. Establish `hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x`. Rewrite using `[hxd, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]`. Use `congr 1`. Conclude with `congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)`. Establish `hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) = Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x` using `fun g => by`.

Rewrite using `[← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]`. Establish `hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g` using `fun g => by`. Establish `h1` using `congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)`. Rewrite `h1` using `[map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul]`. Conclude with `Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l) (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1`.

Use `⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩` and prove the remaining obligations. Conclude with `continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)`. Use `hcoc g h` as an intermediate fact. Simplify using `only [Loc.chRep] at this ⊢`. Simplify using `[this, f, hπ2]`.
-/
private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add, ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

/- English proof (translation)
Take `⟨s, hs⟩` from `(Module.Finite.fg_top (R := ℤ_[l]) (M := c.O))`. Use `⟨_, fd_adjoin_range l (fun q : s => ((q : c.O) : PadicAlgCl l)), fun x hx => ?_⟩` and prove the remaining obligations. Set `K` to `IntermediateField.adjoin ℚ_[l] (Set.range fun q : s => ((q : c.O) : PadicAlgCl l))`. Set `M : Submodule ℤ_[l] (PadicAlgCl l)` to `(K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule`. Establish `hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (s : Set c.O)` using `hs ▸ Submodule.mem_top`.

Establish `hle : Submodule.span ℤ_[l] (s : Set c.O) ≤ M.comap c.O.val.toLinearMap`. Rewrite using `[Submodule.span_le]`. Introduce `q hq`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨q, hq⟩, rfl⟩`. Conclude with `hle hmem`.
-/
private theorem coef_finext {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x ∈ c.O, x ∈ K := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := ℤ_[l]) (M := c.O))
  refine ⟨_, fd_adjoin_range l (fun q : s => ((q : c.O) : PadicAlgCl l)), fun x hx => ?_⟩
  let K := IntermediateField.adjoin ℚ_[l] (Set.range fun q : s => ((q : c.O) : PadicAlgCl l))
  let M : Submodule ℤ_[l] (PadicAlgCl l) := (K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule
  have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  have hle : Submodule.span ℤ_[l] (s : Set c.O) ≤ M.comap c.O.val.toLinearMap := by
    rw [Submodule.span_le]
    intro q hq
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q, hq⟩, rfl⟩
  exact hle hmem

end GlobalTheory.NegVan

open GlobalTheory.NegVan in

/- English proof (translation)
Introduce `hP l _ κ hκc c hκO w hw hwt f hf`. Take `⟨K₀, hK₀, hK⟩` from `coef_finext c`. Take `⟨E, _, κ', c', hκ, hc', hf'⟩` from `desc (MonoidHom.id (GQ l)) κ K₀ (fun g => hK _ (hκO g)) f hf`. Use `haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional`. Establish `hw' : Loc.HasWeight (MonoidHom.id (GQ l)) κ' w`.

Take `⟨U, hU, hUw⟩` from `hwt`. Use `⟨U, hU, fun g hg hI => ?_⟩` and prove the remaining obligations. Establish `h` using `hUw g hg hI`. Establish `hcy : Units.map ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l) (Loc.cycA l l E g) = Loc.cycA l l (PadicAlgCl l) g`. Use `Units.ext ?_` and prove the remaining obligations.

Simplify using `only [Units.coe_map, MonoidHom.coe_coe, Loc.cycA, MonoidHom.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]`. Both sides reduce to the same expression. Apply `Units.map_injective (f := ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l)) (algebraMap E (PadicAlgCl l)).injective` to reduce the goal to its premises. Rewrite using `[map_zpow, MonoidHom.id_apply, hcy, ← MonoidHom.id_apply (GQ l) g, ← h]`.

Conclude with `Units.ext (hκ g)`. Establish `hz` using `(Loc.z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ' (continuous_induced_rng.2 (hκc.congr fun g => (hκ g).symm)) w hw').1 hw`. Rewrite `hf'` using `[hz.1, mem_coboundaries1]`. Take `⟨m, hm⟩` from `hf'`. Use `⟨(m : PadicAlgCl l), fun σ => ?_⟩` and prove the remaining obligations.

Establish `h4 : c' σ = κ' σ * m - m` using `hm σ`. Rewrite using `[← hc' σ, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]`.
-/
theorem GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight :
    Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) →
      ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w →
      ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  intro hP l _ κ hκc c hκO w hw hwt f hf
  obtain ⟨K₀, hK₀, hK⟩ := coef_finext c
  obtain ⟨E, _, κ', c', hκ, hc', hf'⟩ := desc (MonoidHom.id (GQ l)) κ K₀ (fun g => hK _ (hκO g)) f hf
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw' : Loc.HasWeight (MonoidHom.id (GQ l)) κ' w := by
    obtain ⟨U, hU, hUw⟩ := hwt
    refine ⟨U, hU, fun g hg hI => ?_⟩
    have h := hUw g hg hI
    have hcy : Units.map ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l)
        (Loc.cycA l l E g) = Loc.cycA l l (PadicAlgCl l) g := by
      refine Units.ext ?_
      simp only [Units.coe_map, MonoidHom.coe_coe, Loc.cycA, MonoidHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    apply Units.map_injective (f := ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l))
      (algebraMap E (PadicAlgCl l)).injective
    rw [map_zpow, MonoidHom.id_apply, hcy, ← MonoidHom.id_apply (GQ l) g, ← h]
    exact Units.ext (hκ g)
  have hz := (Loc.z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ'
    (continuous_induced_rng.2 (hκc.congr fun g => (hκ g).symm)) w hw').1 hw
  rw [hz.1, mem_coboundaries1] at hf'
  obtain ⟨m, hm⟩ := hf'
  refine ⟨(m : PadicAlgCl l), fun σ => ?_⟩
  have h4 : c' σ = κ' σ * m - m := hm σ
  rw [← hc' σ, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
