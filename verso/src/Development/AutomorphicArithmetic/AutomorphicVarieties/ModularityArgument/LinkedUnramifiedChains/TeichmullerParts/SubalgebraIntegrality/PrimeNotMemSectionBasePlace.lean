import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasWeightAtOfTensorDualIntertwiner
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveInfinitePlaceOfEmbAtSplitPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAll
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Mult (Cp)
open UpperTheory.V.Z.J.D
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Alg

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/- English proof (translation)
The claim follows from `LinearMap.rank_le_of_injective (f.codRestrict Z h) fun _ _ e => hf (congrArg Subtype.val e)`.
-/
private theorem rank_le_of (f : W' →ₗ[ℂ] W) (hf : Function.Injective f) (Z : Submodule ℂ W) (h : ∀ z, f z ∈ Z) :
    Module.rank ℂ W' ≤ Module.rank ℂ Z :=
  LinearMap.rank_le_of_injective (f.codRestrict Z h) fun _ _ e => hf (congrArg Subtype.val e)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem box_tmul (ρ : Representation ℂ G W) (τ : Representation ℂ H W') (g : G × H) (x : W) (y : W') :
    box ρ τ g (x ⊗ₜ y) = ρ g.1 x ⊗ₜ τ g.2 y := rfl

/- English proof (translation)
Rewrite using `[← rank_tensorProduct']`. Establish `hi : Function.Injective (TensorProduct.map (fixd ρ K).subtype (fixd τ K').subtype)` using `TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective`. Use `rank_le_of _ hi _ fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `tmul a b`. Introduce `u hu`. Rewrite using `[TensorProduct.map_tmul, box_tmul]`.

Conclude with `congrArg₂ _ (a.2 _ hu.1) (b.2 _ hu.2)`.
-/
private theorem box_fix (ρ : Representation ℂ G W) (τ : Representation ℂ H W') (K : Subgroup G) (K' : Subgroup H) :
    Module.rank ℂ (fixd ρ K) * Module.rank ℂ (fixd τ K') ≤ Module.rank ℂ (fixd (box ρ τ) (K.prod K')) := by
  rw [← rank_tensorProduct']
  have hi : Function.Injective (TensorProduct.map (fixd ρ K).subtype (fixd τ K').subtype) :=
    TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective
  refine rank_le_of _ hi _ fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    intro u hu
    rw [TensorProduct.map_tmul, box_tmul]
    exact congrArg₂ _ (a.2 _ hu.1) (b.2 _ hu.2)

/- English proof (translation)
Use `haveI : ∀ i, Module.Finite ℂ (fixd (τ i) (K i)) := fun i => Module.finite_of_finrank_pos (h i)`. Establish `e : ((∏ i, Module.finrank ℂ (fixd (τ i) (K i)) : ℕ) : Cardinal) = Module.rank ℂ (⨂[ℂ] i, fixd (τ i) (K i))`. Rewrite using `[rank_eq_card_basis (Basis.piTensorProduct fun i => Module.finBasis ℂ (fixd (τ i) (K i)))]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Use `choose r hr using fun i => (fixd (τ i) (K i)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)`. Establish `hi : Function.Injective (PiTensorProduct.map fun i => (fixd (τ i) (K i)).subtype)`. Use `Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.comp_apply, ← PiTensorProduct.map_comp]`. Simplify using `only [hr, PiTensorProduct.map_id, LinearMap.id_apply]`.

Use `rank_le_of _ hi _ fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using PiTensorProduct.induction_on with`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul_tprod a f`.

Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ fun u hu => ?_` and prove the remaining obligations. Rewrite using `[PiTensorProduct.map_tprod]`. Use `(PiTensorProduct.map_tprod (fun i => τ i (u i)) _).trans ?_` and prove the remaining obligations. Conclude with `congrArg _ (funext fun i => (f i).2 _ (hu i trivial))`.
-/
private theorem pi_fix {I : Type} [Fintype I] {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (K : ∀ i, Subgroup (Gi i))
    (h : ∀ i, 0 < Module.finrank ℂ (fixd (τ i) (K i))) :
    ((∏ i, Module.finrank ℂ (fixd (τ i) (K i)) : ℕ) : Cardinal) ≤ Module.rank ℂ (fixd (piRep τ) (Subgroup.pi Set.univ K)) := by
  classical
  haveI : ∀ i, Module.Finite ℂ (fixd (τ i) (K i)) := fun i => Module.finite_of_finrank_pos (h i)
  have e : ((∏ i, Module.finrank ℂ (fixd (τ i) (K i)) : ℕ) : Cardinal) = Module.rank ℂ (⨂[ℂ] i, fixd (τ i) (K i)) := by
    rw [rank_eq_card_basis (Basis.piTensorProduct fun i => Module.finBasis ℂ (fixd (τ i) (K i)))]
    simp
  rw [e]
  choose r hr using fun i => (fixd (τ i) (K i)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have hi : Function.Injective (PiTensorProduct.map fun i => (fixd (τ i) (K i)).subtype) := by
    refine Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => ?_
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id, LinearMap.id_apply]
  refine rank_le_of _ hi _ fun z => ?_
  induction z using PiTensorProduct.induction_on with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | smul_tprod a f =>
    rw [map_smul]
    refine Submodule.smul_mem _ _ fun u hu => ?_
    rw [PiTensorProduct.map_tprod]
    refine (PiTensorProduct.map_tprod (fun i => τ i (u i)) _).trans ?_
    exact congrArg _ (funext fun i => (f i).2 _ (hu i trivial))

/- English proof (translation)
Take `⟨X, _, _, κ, f, hf⟩` from `hS G Unit Z W' (ρ.comp (MonoidHom.fst G Unit)) τ hτ hI`. Establish `key : ∀ g m (x : X), (f (τ g m ⊗ₜ x) : W) = π g (f (m ⊗ₜ x))` using `fun g m x => by`. Establish `h` using `hf (g, 1) (m ⊗ₜ x)`. Rewrite `h` using `[box_tmul, map_one]`. Conclude with `(congrArg Subtype.val h).trans (hρ g _)`.

Establish `h3 : Module.rank ℂ (fixd τ K) * Module.rank ℂ X ≤ Module.rank ℂ ↥(Z ⊓ fixd π K)`. Rewrite using `[← rank_tensorProduct']`. Establish `hi : Function.Injective (Z.subtype ∘ₗ f.toLinearMap ∘ₗ LinearMap.rTensor X (fixd τ K).subtype)` using `Subtype.val_injective.comp (f.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective))`. Use `rank_le_of _ hi _ fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `tmul a b`. Use `⟨(f _).2, fun u hu => ?_⟩` and prove the remaining obligations.

Conclude with `(key u a b).symm.trans (congrArg (fun m => (f (m ⊗ₜ b) : W)) (a.2 u hu))`. Establish `h4 : Module.rank ℂ X ≤ 1`. Establish `h5 : (P : Cardinal) * Module.rank ℂ X ≤ P` using `(mul_le_mul_left h1 _).trans (h3.trans h2)`. Assume the negation of the conclusion as `hc`. Establish `h6 : (2 : Cardinal) ≤ Module.rank ℂ X`.

Rewrite using `[← one_add_one_eq_two]`. Conclude with `Cardinal.add_one_le_of_lt (not_le.1 hc)`. Establish `h7 : (P : Cardinal) * 2 ≤ P` using `(mul_le_mul_right h6 _).trans h5`. Normalize the coercions in `at h7`. Use linear arithmetic over natural numbers and integers.

Establish `h8 : Nontrivial X`. Assume the negation of the conclusion as `hc`. Use `haveI := not_nontrivial_iff_subsingleton.1 hc`. Use `haveI : Subsingleton Z := f.symm.injective.subsingleton`. Conclude with `hZ (Submodule.eq_bot_of_subsingleton)`.

Establish `h9 : Module.rank ℂ ℂ = Module.rank ℂ X`. Rewrite using `[Module.rank_self]`. Conclude with `le_antisymm (Cardinal.one_le_iff_pos.2 rank_pos) h4`. Take `⟨e⟩` from `nonempty_linearEquiv_of_rank_eq h9`. Set `E : W' ≃ₗ[ℂ] Z` to `(TensorProduct.rid ℂ W').symm ≪≫ₗ LinearEquiv.lTensor W' e ≪≫ₗ f`.

Use `⟨Z.subtype ∘ₗ E.toLinearMap, Subtype.val_injective.comp E.injective, ?_, fun g m => key g m (e 1)⟩` and prove the remaining obligations. Rewrite using `[LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]`.
-/
private theorem one_copy (hS : Step) (π : Representation ℂ G W) (τ : Representation ℂ G W') (Z : Submodule ℂ W)
    (ρ : Representation ℂ G Z) (hτ : AbsIrr τ) (hρ : Intw ρ π Z.subtype) (hI : Isot ρ τ) (hZ : Z ≠ ⊥) (K : Subgroup G)
    (P : ℕ) (hP : 0 < P) (h1 : (P : Cardinal) ≤ Module.rank ℂ (fixd τ K)) (h2 : Module.rank ℂ ↥(Z ⊓ fixd π K) ≤ P) :
    ∃ f : W' →ₗ[ℂ] W, Function.Injective f ∧ LinearMap.range f = Z ∧ Intw τ π f := by
  obtain ⟨X, _, _, κ, f, hf⟩ := hS G Unit Z W' (ρ.comp (MonoidHom.fst G Unit)) τ hτ hI
  have key : ∀ g m (x : X), (f (τ g m ⊗ₜ x) : W) = π g (f (m ⊗ₜ x)) := fun g m x => by
    have h := hf (g, 1) (m ⊗ₜ x)
    rw [box_tmul, map_one] at h
    exact (congrArg Subtype.val h).trans (hρ g _)
  have h3 : Module.rank ℂ (fixd τ K) * Module.rank ℂ X ≤ Module.rank ℂ ↥(Z ⊓ fixd π K) := by
    rw [← rank_tensorProduct']
    have hi : Function.Injective (Z.subtype ∘ₗ f.toLinearMap ∘ₗ LinearMap.rTensor X (fixd τ K).subtype) :=
      Subtype.val_injective.comp (f.injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective))
    refine rank_le_of _ hi _ fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a b =>
      refine ⟨(f _).2, fun u hu => ?_⟩
      exact (key u a b).symm.trans (congrArg (fun m => (f (m ⊗ₜ b) : W)) (a.2 u hu))
  have h4 : Module.rank ℂ X ≤ 1 := by
    have h5 : (P : Cardinal) * Module.rank ℂ X ≤ P := (mul_le_mul_left h1 _).trans (h3.trans h2)
    by_contra hc
    have h6 : (2 : Cardinal) ≤ Module.rank ℂ X := by
      rw [← one_add_one_eq_two]
      exact Cardinal.add_one_le_of_lt (not_le.1 hc)
    have h7 : (P : Cardinal) * 2 ≤ P := (mul_le_mul_right h6 _).trans h5
    norm_cast at h7
    omega
  have h8 : Nontrivial X := by
    by_contra hc
    haveI := not_nontrivial_iff_subsingleton.1 hc
    haveI : Subsingleton Z := f.symm.injective.subsingleton
    exact hZ (Submodule.eq_bot_of_subsingleton)
  have h9 : Module.rank ℂ ℂ = Module.rank ℂ X := by
    rw [Module.rank_self]
    exact le_antisymm (Cardinal.one_le_iff_pos.2 rank_pos) h4
  obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq h9
  let E : W' ≃ₗ[ℂ] Z := (TensorProduct.rid ℂ W').symm ≪≫ₗ LinearEquiv.lTensor W' e ≪≫ₗ f
  refine ⟨Z.subtype ∘ₗ E.toLinearMap, Subtype.val_injective.comp E.injective, ?_, fun g m => key g m (e 1)⟩
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

end Alg

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

open GlobalTheory.BCT (UL KL IsCompU)
open GlobalTheory.PRep (fixed)

/- English proof (translation)
Take `⟨⟨τ₀, h₀, hfd⟩, hu⟩` from `GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w`. Take `⟨T⟩` from `hu τ₀ τ h₀ hτ`. Use `haveI := hfd K hK`. Conclude with `GlobalTheory.BCT.SphLine.finiteDimensional_fixed_of_equiv T K`.
-/
private theorem loc_adm (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) (w : Plc E)
    (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) (K : Subgroup (UL n w)) (hK : IsOpen (K : Set (UL n w))) :
    FiniteDimensional ℂ (fixed τ.ρ K) := by
  obtain ⟨⟨τ₀, h₀, hfd⟩, hu⟩ := GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w
  obtain ⟨T⟩ := hu τ₀ τ h₀ hτ
  haveI := hfd K hK
  exact GlobalTheory.BCT.SphLine.finiteDimensional_fixed_of_equiv T K

/- English proof (translation)
Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hU n σ hσ w τ hτ h)`. Take `⟨θ, h1, h2, h3⟩` from `GlobalTheory.BCT.SphLine.exists_gelfand_anti E hU n w`. Take `⟨hKo, hKc⟩` from `GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w`. Rewrite using `[GlobalTheory.fixed_eq_span_of_gelfandPair (UL n w) (KL n w) hKo hKc θ h1 h2 h3 τ.V τ.ρ τ.irred ⟨τ.smooth, fun K hK _ => loc_adm hU hn hσ w τ hτ K hK⟩ x hx hx0, finrank_span_singleton hx0]`.
-/
private theorem loc_one (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) (w : Plc E)
    (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) (h : IsUnramU σ w) : Module.finrank ℂ (fixed τ.ρ (KL n w)) = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hU n σ hσ w τ hτ h)
  obtain ⟨θ, h1, h2, h3⟩ := GlobalTheory.BCT.SphLine.exists_gelfand_anti E hU n w
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  rw [GlobalTheory.fixed_eq_span_of_gelfandPair (UL n w) (KL n w) hKo hKc θ h1 h2 h3 τ.V τ.ρ τ.irred
    ⟨τ.smooth, fun K hK _ => loc_adm hU hn hσ w τ hτ K hK⟩ x hx hx0, finrank_span_singleton hx0]

/- English proof (translation)
Take `⟨h0, -⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred`. Take `⟨x, hx⟩` from `exists_ne (0 : τ.V)`. Set `St : Subgroup (UL n w)` to `{ carrier := {k | τ.ρ k x = x} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`.

Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `ho : IsOpen ((St ⊓ KL n w : Subgroup (UL n w)) : Set (UL n w))` using `(τ.smooth x).inter (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1`.

Use `⟨_, ho, inf_le_right, ?_⟩` and prove the remaining obligations. Use `haveI := loc_adm hU hn hσ w τ hτ _ ho`. Use `Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, ?_⟩, fun h => hx (congrArg Subtype.val h)⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.GelfandLine.mem_fixed_iff]`. Conclude with `fun k hk => hk.1`.
-/
private theorem loc_deep (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) (w : Plc E)
    (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) :
    ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧ 0 < Module.finrank ℂ (fixed τ.ρ K) := by
  obtain ⟨h0, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
  obtain ⟨x, hx⟩ := exists_ne (0 : τ.V)
  let St : Subgroup (UL n w) :=
    { carrier := {k | τ.ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have ho : IsOpen ((St ⊓ KL n w : Subgroup (UL n w)) : Set (UL n w)) :=
    (τ.smooth x).inter (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1
  refine ⟨_, ho, inf_le_right, ?_⟩
  haveI := loc_adm hU hn hσ w τ hτ _ ho
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, ?_⟩, fun h => hx (congrArg Subtype.val h)⟩
  rw [GlobalTheory.GelfandLine.mem_fixed_iff]
  exact fun k hk => hk.1

/- English proof (translation)
Establish `hm : ∀ g : GLw n w, g ∈ UL n w` using `fun g => by`. Rewrite using `[UL, if_pos hw]`. Discharge the goal by the elementary cases of `trivial`. Set `τ₁ : SmIrr (UL n w)` to `{ V := τ'.V ρ := τ'.ρ.comp (UL n w).subtype smooth := fun v => (τ'.smooth v).preimage continuous_subtype_val irred := by`. Take `⟨h0, h⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 τ'.irred`.

Conclude with `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, hm g⟩ x hx⟩ }`. Establish `h₁ : IsCompU σ w τ₁`. Take `⟨-, F, hF0, hFσ, hF⟩` from `h'`. Conclude with `⟨((cLoc w).comp (locU n w).subtype).codRestrict _ fun x => hm _, fun _ => rfl, τ₁.irred, F, hF0, hFσ, fun x v => hF x v⟩`. Take `⟨T⟩` from `(GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).2 τ₁ τ h₁ hτ`.

Establish `hT : ∀ (k : UL n w) (x : τ'.V), T.toLinearEquiv (τ'.ρ k x) = τ.ρ k (T.toLinearEquiv x)` using `fun k x => LinearMap.congr_fun (T.isIntertwining' k) x`. Use `(T.toLinearEquiv.ofSubmodules _ _ ?_).finrank_eq` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[GlobalTheory.GelfandLine.mem_fixed_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩ k hk`. Conclude with `(hT k x).symm.trans (congrArg T.toLinearEquiv (hx k ⟨k, hk, rfl⟩))`. Introduce `hy`. Take `⟨x, rfl⟩` from `T.toLinearEquiv.surjective y`. Use `⟨x, ?_, rfl⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `T.toLinearEquiv.injective ((hT k x).trans (hy k hk))`.
-/
private theorem loc_move (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) {w : Plc E}
    (hw : IsSplitAt w) (τ : SmIrr (UL n w)) (hτ : IsCompU σ w τ) (τ' : SmIrr (GLw n w)) (h' : Cp σ w τ')
    (K : Subgroup (UL n w)) :
    Module.finrank ℂ (fixd τ'.ρ (K.map (UL n w).subtype)) = Module.finrank ℂ (fixed τ.ρ K) := by
  have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by
    rw [UL, if_pos hw]
    trivial
  let τ₁ : SmIrr (UL n w) :=
    { V := τ'.V
      ρ := τ'.ρ.comp (UL n w).subtype
      smooth := fun v => (τ'.smooth v).preimage continuous_subtype_val
      irred := by
        obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ'.irred
        exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, hm g⟩ x hx⟩ }
  have h₁ : IsCompU σ w τ₁ := by
    obtain ⟨-, F, hF0, hFσ, hF⟩ := h'
    exact ⟨((cLoc w).comp (locU n w).subtype).codRestrict _ fun x => hm _, fun _ => rfl, τ₁.irred, F, hF0, hFσ,
      fun x v => hF x v⟩
  obtain ⟨T⟩ := (GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).2 τ₁ τ h₁ hτ
  have hT : ∀ (k : UL n w) (x : τ'.V), T.toLinearEquiv (τ'.ρ k x) = τ.ρ k (T.toLinearEquiv x) := fun k x =>
    LinearMap.congr_fun (T.isIntertwining' k) x
  refine (T.toLinearEquiv.ofSubmodules _ _ ?_).finrank_eq
  ext y
  rw [GlobalTheory.GelfandLine.mem_fixed_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ k hk
    exact (hT k x).symm.trans (congrArg T.toLinearEquiv (hx k ⟨k, hk, rfl⟩))
  · intro hy
    obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
    refine ⟨x, ?_, rfl⟩
    rintro _ ⟨k, hk, rfl⟩
    exact T.toLinearEquiv.injective ((hT k x).trans (hy k hk))

/- English proof (translation)
Use `choose τ hτ _ using fun w => (GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).1`. Establish `hex : ∀ w : Plc E, ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧ 0 < Module.finrank ℂ (fixed (τ w).ρ K) ∧ (w.under (𝓞 (Lp E)) ∉ T → K = KL n w)` using `fun w => by`. Distinguish the cases in `h : w.under (𝓞 (Lp E)) ∈ T`. Take `⟨K, h1, h2, h3⟩` from `loc_deep hU hn hσ w (τ w) (hτ w)`. Conclude with `⟨K, h1, h2, h3, fun h' => absurd h h'⟩`.

Use `⟨KL n w, (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1, le_rfl, ?_, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[loc_one hU hn hσ w (τ w) (hτ w) (hun w h)]`. Conclude with `one_pos`. Use `choose K h1 h2 h3 h4 using hex`. Establish `hinj : Function.Injective sw` using `Function.LeftInverse.injective hsw`.

Establish `hS : GlobalTheory.BCT.IsSection (Set.range sw)` using `fun w => ⟨sw (w.under (𝓞 (Lp E))), ⟨⟨_, rfl⟩, hsw _⟩, by`. Introduce and unpack `_ ⟨⟨v, rfl⟩, hv⟩`. Rewrite using `[← hv, hsw]⟩`. Establish `hfin : {w : Plc E | w.under (𝓞 (Lp E)) ∈ T}.Finite`. Use `(T.finite_toSet.biUnion (t := fun v => {w : Plc E | w.under (𝓞 (Lp E)) = v}) fun v _ => ?_).subset fun w hw => Set.mem_biUnion hw rfl` and prove the remaining obligations.

Use `haveI := v.isMaximal`. Use `Set.Finite.of_finite_image (f := fun w : Plc E => w.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_) fun _ _ _ _ h => HeightOneSpectrum.ext h` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl, rfl⟩`. Conclude with `⟨w.isPrime, ⟨rfl⟩⟩`. Establish `hK : GlobalTheory.BCT.IsLevelFam (fun w : Plc E => MonoidHom.id (UL n w)) (KL n) K` using `⟨fun w => ⟨h1 w, h2 w, fun _ h => h⟩, hfin.subset fun w hw => by_contra fun h => hw (h4 w h)⟩`.

Use `⟨fun w => (K w).map (UL n w).subtype, fun v => Module.finrank ℂ (fixed (τ (sw v)).ρ (K (sw v))), GlobalTheory.BCT.globLev (Set.range sw) K, fun x hx v => ?_, fun w => ?_, fun v hv τ' h' => loc_move hU hn hσ (hsp v hv) _ (hτ _) τ' h' _, fun v => h3 _, ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx (sw v)) ⟨v, rfl⟩`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Rewrite using `[GlobalTheory.SmGL.SphCompletion.KO_completion w n]`. Conclude with `h2 w hk`.

Rewrite using `[GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn σ hσ _ hS lam hlam K hK τ hτ, finprod_mem_range hinj, Nat.cast_prod]`. Use `congr 1`. Use `finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h => hv ?_` and prove the remaining obligations. Establish `h' : (sw v).under (𝓞 (Lp E)) ∉ T` using `by rwa [hsw]`. Use `beta_reduce`.

Rewrite using `[h4 _ h', loc_one hU hn hσ _ (τ _) (hτ _) (hun _ h'), Nat.cast_one]`.
-/
private theorem glob_dim (hU : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ)
    (sw : Plc (Lp E) → Plc E) (hsw : ∀ v, (sw v).under (𝓞 (Lp E)) = v) (T : Finset (Plc (Lp E)))
    (hsp : ∀ v ∈ T, IsSplitAt (sw v)) (hun : ∀ w : Plc E, w.under (𝓞 (Lp E)) ∉ T → IsUnramU σ w)
    (lam : InfinitePlace E → DomWeight n) (hlam : ∀ v, HasWeightAt σ v.embedding (lam v)) :
    ∃ (K : ∀ w : Plc E, Subgroup (GLw n w)) (a : Plc (Lp E) → ℕ) (U : Subgroup (finU E n)),
      (∀ x ∈ U, ∀ v, cLoc (sw v) x.1 ∈ K (sw v)) ∧ (∀ w, K w ≤ KO (w.adicCompletion E) (Fin n)) ∧
      (∀ v ∈ T, ∀ τ, Cp σ (sw v) τ → Module.finrank ℂ (fixd τ.ρ (K (sw v))) = a v) ∧ (∀ v, 0 < a v) ∧
      (Module.finrank ℂ ↥(σ ⊓ fixed (GlobalTheory.BCT.RF E n) U) : ℂ) = GlobalTheory.BCT.dimW lam * (∏ v ∈ T, a v : ℕ) := by
  choose τ hτ _ using fun w => (GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).1
  have hex : ∀ w : Plc E, ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧
      0 < Module.finrank ℂ (fixed (τ w).ρ K) ∧ (w.under (𝓞 (Lp E)) ∉ T → K = KL n w) := fun w => by
    by_cases h : w.under (𝓞 (Lp E)) ∈ T
    · obtain ⟨K, h1, h2, h3⟩ := loc_deep hU hn hσ w (τ w) (hτ w)
      exact ⟨K, h1, h2, h3, fun h' => absurd h h'⟩
    · refine ⟨KL n w, (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1, le_rfl, ?_, fun _ => rfl⟩
      rw [loc_one hU hn hσ w (τ w) (hτ w) (hun w h)]
      exact one_pos
  choose K h1 h2 h3 h4 using hex
  have hinj : Function.Injective sw := Function.LeftInverse.injective hsw
  have hS : GlobalTheory.BCT.IsSection (Set.range sw) := fun w => ⟨sw (w.under (𝓞 (Lp E))), ⟨⟨_, rfl⟩, hsw _⟩, by
    rintro _ ⟨⟨v, rfl⟩, hv⟩
    rw [← hv, hsw]⟩
  have hfin : {w : Plc E | w.under (𝓞 (Lp E)) ∈ T}.Finite := by
    refine (T.finite_toSet.biUnion (t := fun v => {w : Plc E | w.under (𝓞 (Lp E)) = v}) fun v _ => ?_).subset
      fun w hw => Set.mem_biUnion hw rfl
    haveI := v.isMaximal
    refine Set.Finite.of_finite_image (f := fun w : Plc E => w.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_) fun _ _ _ _ h => HeightOneSpectrum.ext h
    rintro _ ⟨w, rfl, rfl⟩
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have hK : GlobalTheory.BCT.IsLevelFam (fun w : Plc E => MonoidHom.id (UL n w)) (KL n) K :=
    ⟨fun w => ⟨h1 w, h2 w, fun _ h => h⟩, hfin.subset fun w hw => by_contra fun h => hw (h4 w h)⟩
  refine ⟨fun w => (K w).map (UL n w).subtype, fun v => Module.finrank ℂ (fixed (τ (sw v)).ρ (K (sw v))),
    GlobalTheory.BCT.globLev (Set.range sw) K, fun x hx v => ?_, fun w => ?_,
    fun v hv τ' h' => loc_move hU hn hσ (hsp v hv) _ (hτ _) τ' h' _, fun v => h3 _, ?_⟩
  · exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx (sw v)) ⟨v, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact h2 w hk
  · rw [GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn σ hσ _ hS lam hlam K hK τ hτ, finprod_mem_range hinj, Nat.cast_prod]
    congr 1
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h => hv ?_
    have h' : (sw v).under (𝓞 (Lp E)) ∉ T := by rwa [hsw]
    beta_reduce
    rw [h4 _ h', loc_one hU hn hσ _ (τ _) (hτ _) (hun _ h'), Nat.cast_one]

end Loc

section Glob

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

/- English proof (translation)
Unfold `CaseU.cmp`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal`. Rewrite using `[map_natCast]`.
-/
private theorem l_under {u : Plc L} :
    ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
  rw [map_natCast]

/- English proof (translation)
Establish `h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1` using `h`. Establish `e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1)` using `Units.ext rfl`. Rewrite using `[e, h1, map_one]`.
-/
private theorem cLoc_inf {x : UA L n} (h : x ∈ infU L n) (u : Plc L) : cLoc u x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := h
  have e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl
  rw [e, h1, map_one]

variable (s : HidaSetting l L Ω)

/- English proof (translation)
Use extensionality with `x`. Conclude with `(s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)`.
-/
private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

/- English proof (translation)
Introduce `h`. Establish `hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p` using `s.norm_v0_eq_one`. Establish `hl0 : ((l : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0`. Simplify using `using (Ideal.Quotient.eq_zero_iff_mem.2 h)`. Establish `hp0 : ((s.p : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0`.

Use `card_nsmul_eq_zero' (G := 𝓞 (Lp L) ⧸ s.v0.asIdeal) (x := 1)` as an intermediate fact. Rewrite `this` using `[hcard]`. Simplify using `using this`. Take `⟨a, b, e⟩` from `((Nat.coprime_primes (Fact.out : l.Prime) s.p_prime).2 (Ne.symm s.p_ne)).isCoprime`. Establish `e'` using `congrArg (Int.cast : ℤ → 𝓞 (Lp L) ⧸ s.v0.asIdeal) e`.

Move the coercions through the operations in `at e'`. Rewrite `e'` using `[hl0, hp0, mul_zero, mul_zero, add_zero]`. Use `haveI := subsingleton_of_zero_eq_one e'`. Rewrite `hcard` using `[Nat.card_of_subsingleton (0 : 𝓞 (Lp L) ⧸ s.v0.asIdeal)]`. Conclude with `s.p_prime.one_lt.ne hcard`.
-/
private theorem SectionSplitPlaces : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p := s.norm_v0_eq_one
  have hl0 : ((l : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hp0 : ((s.p : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := card_nsmul_eq_zero' (G := 𝓞 (Lp L) ⧸ s.v0.asIdeal) (x := 1)
    rw [hcard] at this
    simpa using this
  obtain ⟨a, b, e⟩ := ((Nat.coprime_primes (Fact.out : l.Prime) s.p_prime).2 (Ne.symm s.p_ne)).isCoprime
  have e' := congrArg (Int.cast : ℤ → 𝓞 (Lp L) ⧸ s.v0.asIdeal) e
  push_cast at e'
  rw [hl0, hp0, mul_zero, mul_zero, add_zero] at e'
  haveI := subsingleton_of_zero_eq_one e'
  rw [Nat.card_of_subsingleton (0 : 𝓞 (Lp L) ⧸ s.v0.asIdeal)] at hcard
  exact s.p_prime.one_lt.ne hcard

/- English proof (translation)
Use `cmp_of (fun e => ?_) x` and prove the remaining obligations. Establish `e'` using `l_under.1 e`. Rewrite `e'` using `[under_w]`. Break down `h with h | rfl` into its components or cases. Conclude with `s.St_l _ h e'`.

Conclude with `SectionSplitPlaces s e'`.
-/
private theorem cmp_S {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) (x : UA L n) :
    cmp n (s.w v) ((away l L n).rangeRestrict x) = cLoc (s.w v) x := by
  refine cmp_of (fun e => ?_) x
  have e' := l_under.1 e
  rw [under_w] at e'
  rcases h with h | rfl
  · exact s.St_l _ h e'
  · exact SectionSplitPlaces s e'

/- English proof (translation)
The claim follows from `cmp_of (fun e => h (Or.inl (l_under.1 e))) x`.
-/
private theorem cmp_off {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := cmp_of (fun e => h (Or.inl (l_under.1 e))) x

/- English proof (translation)
The claim follows from `Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h2 w hw⟩`.
-/
private theorem mem_KS {a : Ga l L n} (h1 : toGS n s a = 1)
    (h2 : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w a ∈ KO (w.adicCompletion L) (Fin n)) : a ∈ KS n s :=
  Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h2 w hw⟩

/- English proof (translation)
Unfold `secS`. Rewrite using `[dif_pos hb]`. Use `⟨(MulEquiv.ofBijective _ hb).apply_symm_apply g, fun w hw => ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((MulEquiv.ofBijective _ hb).symm g).2 w) ⟨fun h => hw (Or.inr (Or.inl h)), fun h => hw (Or.inr (Or.inr h))⟩`.
-/
private theorem sec_spec (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w (secS n s g) = 1 := by
  unfold secS
  rw [dif_pos hb]
  refine ⟨(MulEquiv.ofBijective _ hb).apply_symm_apply g, fun w hw => ?_⟩
  exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((MulEquiv.ofBijective _ hb).symm g).2 w)
    ⟨fun h => hw (Or.inr (Or.inl h)), fun h => hw (Or.inr (Or.inr h))⟩

/- English proof (translation)
Use `mem_KS s ?_ fun w hw => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, (sec_spec s hb _).1, inv_mul_cancel]`. Rewrite using `[map_mul, map_inv, (sec_spec s hb _).2 w hw, inv_one, one_mul, cmp_off s hw]`. Conclude with `UpperTheory.mem_maximalCompact_of_under_eq L n x _ w (under_w s _).symm (hx _)`.
-/
private theorem sec_rest (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (x : UA L n)
    (hx : ∀ v, cLoc (s.w v) x ∈ KO ((s.w v).adicCompletion L) (Fin n)) :
    (secS n s (toGS n s ((away l L n).rangeRestrict x)))⁻¹ * (away l L n).rangeRestrict x ∈ KS n s := by
  refine mem_KS s ?_ fun w hw => ?_
  · rw [map_mul, map_inv, (sec_spec s hb _).1, inv_mul_cancel]
  · rw [map_mul, map_inv, (sec_spec s hb _).2 w hw, inv_one, one_mul, cmp_off s hw]
    exact UpperTheory.mem_maximalCompact_of_under_eq L n x _ w (under_w s _).symm (hx _)

/- English proof (translation)
Use `⟨(Finset.univ : Finset (Vl l L)).map (Function.Embedding.subtype _) ∪ insert s.v0 s.St, fun v => ?_, fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_union, Finset.mem_map, Finset.mem_insert, Finset.mem_univ, true_and]`. Conclude with `or_congr ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨v, h⟩, rfl⟩⟩ or_comm`. Rewrite using `[Finset.prod_union, Finset.prod_map, Finset.prod_insert s.v0_St, Finset.prod_coe_sort s.St a, mul_comm (a s.v0)]`. Both sides reduce to the same expression.

Use `Finset.disjoint_left.2 fun v hv hv' => ?_` and prove the remaining obligations. Take `⟨u, -, rfl⟩` from `Finset.mem_map.1 hv`. Break down `Finset.mem_insert.1 hv' with h | h` into its components or cases. Conclude with `SectionSplitPlaces s (h ▸ u.2)`. Conclude with `s.St_l _ h u.2`.
-/
private theorem prod_S [Fintype (Vl l L)] : ∃ T : Finset (Plc (Lp L)), (∀ v, v ∈ T ↔ v ∈ s.S) ∧
    ∀ a : Plc (Lp L) → ℕ, ∏ v ∈ T, a v = (∏ v : Vl l L, a v.1) * ((∏ u : s.St, a u) * a s.v0) := by
  classical
  refine ⟨(Finset.univ : Finset (Vl l L)).map (Function.Embedding.subtype _) ∪ insert s.v0 s.St, fun v => ?_, fun a => ?_⟩
  · simp only [Finset.mem_union, Finset.mem_map, Finset.mem_insert, Finset.mem_univ, true_and]
    exact or_congr ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨v, h⟩, rfl⟩⟩ or_comm
  · rw [Finset.prod_union, Finset.prod_map, Finset.prod_insert s.v0_St, Finset.prod_coe_sort s.St a, mul_comm (a s.v0)]
    · rfl
    · refine Finset.disjoint_left.2 fun v hv hv' => ?_
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hv
      rcases Finset.mem_insert.1 hv' with h | h
      · exact SectionSplitPlaces s (h ▸ u.2)
      · exact s.St_l _ h u.2

variable {s} (V : s.Lev)

/- English proof (translation)
Establish `e1` using `h1 _ (sec_rest s hb x fun v => hK _ (hx v))`. Establish `e2` using `h2 (fun v : V.frame.Vl => cLoc (s.w v.1) x, toGS n s ((away l L n).rangeRestrict x)) ⟨fun v _ => hx v.1, fun u _ => Set.mem_of_eq_of_mem (cmp_S s (Or.inl u.2) x) (hx u.1), Set.mem_of_eq_of_mem (cmp_S s (Or.inr rfl) x) (hx _)⟩`. Use function extensionality and compare the values at `y`. Use `Eq.trans ?_ (congrFun e2 y)` and prove the remaining obligations. Use `Eq.trans (congrArg F ?_) (congrFun e1 (y * (secS n s (toGS n s ((away l L n).rangeRestrict x)), fun v : V.frame.Vl => cLoc (s.w v.1) x)))` and prove the remaining obligations.

Use `Prod.ext ?_ (mul_one _).symm` and prove the remaining obligations. Conclude with `congrArg (y.1 * ·) (mul_inv_cancel_left _ _).symm |>.trans (mul_assoc _ _ _).symm`.
-/
private theorem fix_J {d : ℕ} (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype))
    (K : ∀ w : Plc L, Subgroup (GLw n w)) (hK : ∀ w, K w ≤ KO (w.adicCompletion L) (Fin n))
    (F : Ga l L n × GL' n V → Fin d → ℂ)
    (h1 : F ∈ fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s))
    (h2 : F ∈ fixd (actS n V d) ((Subgroup.pi Set.univ fun v : V.frame.Vl => K (s.w v.1)).prod
      ((Subgroup.pi Set.univ fun u : s.St => K (s.w u)).prod (K (s.w s.v0)))))
    (x : UA L n) (hx : ∀ v, cLoc (s.w v) x ∈ K (s.w v)) :
    rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ) ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x) F = F := by
  have e1 := h1 _ (sec_rest s hb x fun v => hK _ (hx v))
  have e2 := h2 (fun v : V.frame.Vl => cLoc (s.w v.1) x, toGS n s ((away l L n).rangeRestrict x))
    ⟨fun v _ => hx v.1, fun u _ => Set.mem_of_eq_of_mem (cmp_S s (Or.inl u.2) x) (hx u.1),
      Set.mem_of_eq_of_mem (cmp_S s (Or.inr rfl) x) (hx _)⟩
  funext y
  refine Eq.trans ?_ (congrFun e2 y)
  refine Eq.trans (congrArg F ?_)
    (congrFun e1 (y * (secS n s (toGS n s ((away l L n).rangeRestrict x)), fun v : V.frame.Vl => cLoc (s.w v.1) x)))
  refine Prod.ext ?_ (mul_one _).symm
  exact congrArg (y.1 * ·) (mul_inv_cancel_left _ _).symm |>.trans (mul_assoc _ _ _).symm

variable {V} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero`. Introduce `ℓ`. Establish `: toForm ι e (0 : Ga l L n × GL' n V → Fin d → ℂ) ℓ = 0`.

Use function extensionality and compare the values at `g`. Simplify using `only [toForm, Pi.zero_apply, map_zero]`. Rewrite using `[this]`. Conclude with `σ.zero_mem`. Consider the case `add x y _ _ hx hy`.

Introduce `ℓ`. Establish `: toForm ι e (x + y) ℓ = toForm ι e x ℓ + toForm ι e y ℓ`. Use function extensionality and compare the values at `g`. Simplify using `only [toForm, Pi.add_apply, map_add]`. Rewrite using `[this]`.

Conclude with `σ.add_mem (hx ℓ) (hy ℓ)`. Consider the case `smul a x _ hx`. Introduce `ℓ`. Establish `: toForm ι e (a • x) ℓ = a • toForm ι e x ℓ`. Use function extensionality and compare the values at `g`.

Simplify using `only [toForm, Pi.smul_apply, map_smul]`. Rewrite using `[this]`. Conclude with `σ.smul_mem a (hx ℓ)`.
-/
private theorem span_form (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GL' n V → Fin d → ℂ)
    (h : F ∈ Submodule.span ℂ {F : Ga l L n × GL' n V → Fin d → ℂ | ∀ ℓ, toForm ι e F ℓ ∈ σ}) : ∀ ℓ, toForm ι e F ℓ ∈ σ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    intro ℓ
    have : toForm ι e (0 : Ga l L n × GL' n V → Fin d → ℂ) ℓ = 0 := by
      funext g
      simp only [toForm, Pi.zero_apply, map_zero]
    rw [this]; exact σ.zero_mem
  | add x y _ _ hx hy =>
    intro ℓ
    have : toForm ι e (x + y) ℓ = toForm ι e x ℓ + toForm ι e y ℓ := by
      funext g
      simp only [toForm, Pi.add_apply, map_add]
    rw [this]; exact σ.add_mem (hx ℓ) (hy ℓ)
  | smul a x _ hx =>
    intro ℓ
    have : toForm ι e (a • x) ℓ = a • toForm ι e x ℓ := by
      funext g
      simp only [toForm, Pi.smul_apply, map_smul]
    rw [this]; exact σ.smul_mem a (hx ℓ)

/- English proof (translation)
Establish `h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1` using `fun τ => by`. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1`. Rewrite using `[MonoidHom.mem_ker.1 hk, map_one]`. Express the relevant statement in the definitionally equal form `PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1`. Simplify using `only [h1, map_one]`.

Conclude with `map_one _`.
-/
private theorem infRep_fin {k : UA L n} (hk : k ∈ finU L n) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

/- English proof (translation)
Use `haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV`. Use `haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _`. Set `Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ)` to `{ toFun := fun ℓ => toForm ι e F ℓ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `UpperTheory.hasWeightAt_of_tensor_dual_intertwiner L n hn _ (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res) (UpperTheory.injective_infinitePlace_of_emb_at_split_places l L Ω s V ι) (fun y => lam y.res) σ Φ (fun h0 => hF fun ℓ => LinearMap.congr_fun h0 ℓ) …` and prove the remaining obligations. Establish `h1 : (((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x) : Ga l L n × GL' n V) = 1` using `Prod.ext (Subtype.ext (funext fun u => cLoc_inf hx u.1)) (funext fun v => cLoc_inf hx _)`.

Establish `h2` using `h3 F ℓ x`. Simplify using `only [h1, mul_one] at h2`. Conclude with `h2`.
-/
private theorem form_wt (hn : 1 ≤ n)
    (h3 : ∀ (F : Ga l L n × GL' n V → Fin d → ℂ) ℓ (x : UA L n), RU L n x (toForm ι e F ℓ) =
      toForm ι e (fun g => F (g * ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GL' n V → Fin d → ℂ) (hF : ¬ ∀ ℓ, toForm ι e F ℓ = 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ) (y : Emb l (fun v : V.frame.Vl => s.w v.1)) :
    HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV
  haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  let Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    { toFun := fun ℓ => toForm ι e F ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine UpperTheory.hasWeightAt_of_tensor_dual_intertwiner L n hn _ (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.injective_infinitePlace_of_emb_at_split_places l L Ω s V ι) (fun y => lam y.res) σ Φ (fun h0 => hF fun ℓ => LinearMap.congr_fun h0 ℓ) hσ
    (fun ℓ x hx => ?_) y
  have h1 : (((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x) : Ga l L n × GL' n V) = 1 :=
    Prod.ext (Subtype.ext (funext fun u => cLoc_inf hx u.1)) (funext fun v => cLoc_inf hx _)
  have h2 := h3 F ℓ x
  simp only [h1, mul_one] at h2
  exact h2

/- English proof (translation)
Take `⟨ℓ, hℓ⟩` from `not_forall.1 hF`. Use `⟨_, hσ ℓ, hℓ, fun x hx hk => ?_⟩` and prove the remaining obligations. Establish `hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1` using `fun v hv => GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ (under_w s v).symm ▸ hv)`. Establish `hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)`. Rewrite using `[GlobalTheory.SmGL.SphCompletion.KO_completion w n]`.

Conclude with `hk`. Establish `hm : (away l L n).rangeRestrict x ∈ KS n s`. Use `mem_KS s (Prod.ext (funext fun u => (cmp_S s (Or.inl u.2) x).trans (hS _ (Or.inr (Or.inl u.2)))) ((cmp_S s (Or.inr rfl) x).trans (hS _ (Or.inr (Or.inr rfl))))) fun u hu => ?_` and prove the remaining obligations. Rewrite using `[cmp_off s hu]`. Distinguish the cases in `h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))`.

Conclude with `UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK`. Rewrite using `[show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]`. Conclude with `one_mem _`. Establish `hl : (fun v : V.frame.Vl => cLoc (s.w v.1) x) = 1` using `funext fun v => hS v.1 (Or.inl v.2)`. Rewrite using `[h3, hl, infRep_fin ι ((finU L n).inv_mem (Subgroup.mem_inf.1 hx).1)]`.

Conclude with `congrArg (fun G => toForm ι e G ℓ) (h1 _ hm)`.
-/
private theorem form_unr
    (h3 : ∀ (F : Ga l L n × GL' n V → Fin d → ℂ) ℓ (x : UA L n), RU L n x (toForm ι e F ℓ) =
      toForm ι e (fun g => F (g * ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GL' n V → Fin d → ℂ) (hF : ¬ ∀ ℓ, toForm ι e F ℓ = 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ)
    (h1 : F ∈ fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s))
    (w : Plc L) (hw : w.under (𝓞 (Lp L)) ∉ s.S) : IsUnramU σ w := by
  obtain ⟨ℓ, hℓ⟩ := not_forall.1 hF
  refine ⟨_, hσ ℓ, hℓ, fun x hx hk => ?_⟩
  have hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1 := fun v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ (under_w s v).symm ▸ hv)
  have hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact hk
  have hm : (away l L n).rangeRestrict x ∈ KS n s := by
    refine mem_KS s (Prod.ext (funext fun u => (cmp_S s (Or.inl u.2) x).trans (hS _ (Or.inr (Or.inl u.2))))
      ((cmp_S s (Or.inr rfl) x).trans (hS _ (Or.inr (Or.inr rfl))))) fun u hu => ?_
    rw [cmp_off s hu]
    by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · exact UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK
    · rw [show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]
      exact one_mem _
  have hl : (fun v : V.frame.Vl => cLoc (s.w v.1) x) = 1 := funext fun v => hS v.1 (Or.inl v.2)
  rw [h3, hl, infRep_fin ι ((finU L n).inv_mem (Subgroup.mem_inf.1 hx).1)]
  exact congrArg (fun G => toForm ι e G ℓ) (h1 _ hm)

end Glob

section Model

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {σ : Submodule ℂ (UA L n → ℂ)} (C : Comps V σ)

/- English proof (translation)
Use `letI : Fintype V.frame.Vl := V.frame.finV`. Conclude with `hB _ _ _ _ _ _ (hP _ _ _ _ fun v => hG L n _ _) (hB _ _ _ _ _ _ (hP _ _ _ _ fun u => hG L n _ _) (hG L n _ _))`.
-/
private theorem model_irr (hB : BoxIrr) (hP : PiIrr) (hG : SchurGL) : AbsIrr (box C.repL C.repS) := by
  classical
  letI : Fintype V.frame.Vl := V.frame.finV
  exact hB _ _ _ _ _ _ (hP _ _ _ _ fun v => hG L n _ _) (hB _ _ _ _ _ _ (hP _ _ _ _ fun u => hG L n _ _) (hG L n _ _))

/- English proof (translation)
Establish `el` using `fun v : V.frame.Vl => k3 v.1 (Or.inl v.2) _ (C.hl v)`. Establish `eu` using `fun u : s.St => k3 u.1 (Or.inr (Or.inl u.2)) _ (C.hu u)`. Establish `eo` using `k3 s.v0 (Or.inr (Or.inr rfl)) _ C.ho`. Establish `rl` using `pi_fix (fun v => (C.l v).ρ) (fun v => K (s.w v.1)) fun v => (k4 _).trans_eq (el v).symm`. Establish `ru` using `pi_fix (fun u => (C.u u).ρ) (fun u => K (s.w u.1)) fun u => (k4 _).trans_eq (eu u).symm`.

Establish `ro : (a s.v0 : Cardinal) ≤ Module.rank ℂ (fixd C.o.ρ (K (s.w s.v0)))` using `by haveI := Module.finite_of_finrank_pos ((k4 _).trans_eq eo.symm)`. Conclude with `((congrArg Nat.cast eo).symm.trans (Module.finrank_eq_rank _ _)).le`. Rewrite `rl` using `[Finset.prod_congr rfl fun v _ => el v]`. Rewrite `ru` using `[Finset.prod_congr rfl fun u _ => eu u]`. Rewrite using `[Nat.cast_mul, Nat.cast_mul]`.

Conclude with `(mul_le_mul' rl ((mul_le_mul' ru ro).trans (box_fix _ _ _ _))).trans (box_fix _ _ _ _)`.
-/
private theorem model_rank [Fintype V.frame.Vl] (K : ∀ w : Plc L, Subgroup (GLw n w)) (a : Plc (Lp L) → ℕ) (k4 : ∀ v, 0 < a v)
    (k3 : ∀ v ∈ s.S, ∀ τ, Cp σ (s.w v) τ → Module.finrank ℂ (fixd τ.ρ (K (s.w v))) = a v) :
    (((∏ v : V.frame.Vl, a v.1) * ((∏ u : s.St, a u) * a s.v0) : ℕ) : Cardinal) ≤
      Module.rank ℂ (fixd (box C.repL C.repS) ((Subgroup.pi Set.univ fun v : V.frame.Vl => K (s.w v.1)).prod
        ((Subgroup.pi Set.univ fun u : s.St => K (s.w u)).prod (K (s.w s.v0))))) := by
  have el := fun v : V.frame.Vl => k3 v.1 (Or.inl v.2) _ (C.hl v)
  have eu := fun u : s.St => k3 u.1 (Or.inr (Or.inl u.2)) _ (C.hu u)
  have eo := k3 s.v0 (Or.inr (Or.inr rfl)) _ C.ho
  have rl := pi_fix (fun v => (C.l v).ρ) (fun v => K (s.w v.1)) fun v => (k4 _).trans_eq (el v).symm
  have ru := pi_fix (fun u => (C.u u).ρ) (fun u => K (s.w u.1)) fun u => (k4 _).trans_eq (eu u).symm
  have ro : (a s.v0 : Cardinal) ≤ Module.rank ℂ (fixd C.o.ρ (K (s.w s.v0))) := by
    haveI := Module.finite_of_finrank_pos ((k4 _).trans_eq eo.symm)
    exact ((congrArg Nat.cast eo).symm.trans (Module.finrank_eq_rank _ _)).le
  rw [Finset.prod_congr rfl fun v _ => el v] at rl
  rw [Finset.prod_congr rfl fun u _ => eu u] at ru
  rw [Nat.cast_mul, Nat.cast_mul]
  exact (mul_le_mul' rl ((mul_le_mul' ru ro).trans (box_fix _ _ _ _))).trans (box_fix _ _ _ _)

/- English proof (translation)
Use `fun G hG => ⟨hG.1.1, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `fix_J V hb K hK G hG.1.2 hG.2 x.1 (hU x hx)`.
-/
private theorem level_le (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) {d : ℕ}
    (K : ∀ w : Plc L, Subgroup (GLw n w)) (hK : ∀ w, K w ≤ KO (w.adicCompletion L) (Fin n)) (U : Subgroup (finU L n))
    (hU : ∀ x ∈ U, ∀ v, cLoc (s.w v) x.1 ∈ K (s.w v)) (B : Submodule ℂ (Ga l L n × GL' n V → Fin d → ℂ)) :
    (B ⊓ fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s)) ⊓
      fixd (actS n V d) ((Subgroup.pi Set.univ fun v : V.frame.Vl => K (s.w v.1)).prod
        ((Subgroup.pi Set.univ fun u : s.St => K (s.w u)).prod (K (s.w s.v0)))) ≤
    B ⊓ fixd (rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)) (U.map ((MonoidHom.prod (away l L n).rangeRestrict
      (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))).comp (finU L n).subtype)) := by
  refine fun G hG => ⟨hG.1.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact fix_J V hb K hK G hG.1.2 hG.2 x.1 (hU x hx)

end Model

/- English proof (translation)
Establish `f` using `formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl`. Take `⟨F, hF, hF0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Establish `hF1` using `mt (f.1 F hF.1.1) hF0`. Establish `hF2` using `span_form ι e σ F hF.1.2`. Use `⟨form_wt ι e hn f.2.2.1 σ F hF1 hF2, form_unr ι e f.2.2.1 σ F hF1 hF2 hF.2, fun h => hF0 (funext fun _ => funext fun i => ?_)⟩` and prove the remaining obligations.

Conclude with `(h ▸ i : Fin 0).elim0`.
-/
private theorem vs_data {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (σ : Submodule ℂ (UA L n → ℂ))
    (hne : VS V ι e ξ Q τ₀ σ ≠ ⊥) :
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU σ w) ∧ d ≠ 0 := by
  have f := formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hF1 := mt (f.1 F hF.1.1) hF0
  have hF2 := span_form ι e σ F hF.1.2
  refine ⟨form_wt ι e hn f.2.2.1 σ F hF1 hF2, form_unr ι e f.2.2.1 σ F hF1 hF2 hF.2, fun h => hF0 (funext fun _ => funext fun i => ?_)⟩
  exact (h ▸ i : Fin 0).elim0

/- English proof (translation)
Establish `h5 : f = P * d`. Rewrite `h3` using `[← h2, mul_comm]`. Conclude with `h3` after adjusting the coercions. Establish `h6 : y * d = (P : Cardinal) * d`. Rewrite using `[← h1, h4 (h5 ▸ Nat.mul_pos hP (Nat.pos_of_ne_zero hd)), h5, Nat.cast_mul]`.

Conclude with `((Cardinal.mul_natCast_inj hd).1 h6).le`.
-/
private theorem cancel_rank {r y : Cardinal} {f d P : ℕ} {D : ℂ} (hP : 0 < P) (hd : d ≠ 0) (h1 : r = y * d) (h2 : (d : ℂ) = D)
    (h3 : (f : ℂ) = D * (P : ℕ)) (h4 : 0 < f → r = f) : y ≤ P := by
  have h5 : f = P * d := by
    rw [← h2, mul_comm] at h3
    exact_mod_cast h3
  have h6 : y * d = (P : Cardinal) * d := by
    rw [← h1, h4 (h5 ▸ Nat.mul_pos hP (Nat.pos_of_ne_zero hd)), h5, Nat.cast_mul]
  exact ((Cardinal.mul_natCast_inj hd).1 h6).le

/- English proof (translation)
Introduce `hI hS hB hP hG hD hW hSec l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ hne C`. Use `letI : Fintype V.frame.Vl := V.frame.finV`. Use `(hI l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ C).elim fun ρ hρ => ?_` and prove the remaining obligations. Take `⟨lam', hl⟩` from `hW l L Ω s n hn V hV ι lam`. Establish `hv` using `vs_data hn Q ι τ₀ e ξ hξ σ hne`.

Establish `hwt` using `(hl σ hσ).1 hv.1`. Take `⟨T, hT, hprod⟩` from `@prod_S l _ L Ω _ _ _ _ _ _ s V.frame.finV`. Use `(glob_dim (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) hn hσ s.w (under_w s) T (fun v hv => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v ((hT v).1 hv)) _ (under_w s v)) (fun w hw => hv.2.1 w fun h => …` and prove the remaining obligations. Establish `d1` using `hD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ lam' hl σ hσ hwt U _ rfl`. Establish `hPp : 0 < ∏ v ∈ T, a v` using `Finset.prod_pos fun v _ => k.2.2.2.1 v`.

Establish `hY` using `cancel_rank hPp hv.2.2 d1.1 d1.2 k.2.2.2.2 fun h => haveI := Module.finite_of_finrank_pos h (Module.finrank_eq_rank _ _).symm`. Establish `h1` using `model_rank C K a k.2.2.2.1 fun v h => k.2.2.1 v ((hT v).2 h)`. Conclude with `one_copy hS (actS n V d) (box C.repL C.repS) _ ρ (model_irr C hB hP hG) hρ.1 hρ.2 hne _ _ hPp ((congrArg Nat.cast (hprod a)).trans_le h1) ((Submodule.rank_mono (level_le (hSec l L Ω s n hn V hV).1 K k.2.1 U k.1 _)).trans hY)`.
-/
theorem UpperTheory.V.Z.J.D.flath :
    IsotS → Step → BoxIrr → PiIrr → SchurGL → InfDim → WtEx → SecS → Flath := by
  intro hI hS hB hP hG hD hW hSec l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ hne C
  letI : Fintype V.frame.Vl := V.frame.finV
  refine (hI l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ σ hσ C).elim fun ρ hρ => ?_
  obtain ⟨lam', hl⟩ := hW l L Ω s n hn V hV ι lam
  have hv := vs_data hn Q ι τ₀ e ξ hξ σ hne
  have hwt := (hl σ hσ).1 hv.1
  obtain ⟨T, hT, hprod⟩ := @prod_S l _ L Ω _ _ _ _ _ _ s V.frame.finV
  refine (glob_dim (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) hn hσ s.w (under_w s) T
    (fun v hv => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v ((hT v).1 hv)) _ (under_w s v))
    (fun w hw => hv.2.1 w fun h => hw ((hT _).2 h)) lam' hwt).elim fun K hK => hK.elim fun a ha => ha.elim fun U k => ?_
  have d1 := hD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ lam' hl σ hσ hwt U _ rfl
  have hPp : 0 < ∏ v ∈ T, a v := Finset.prod_pos fun v _ => k.2.2.2.1 v
  have hY := cancel_rank hPp hv.2.2 d1.1 d1.2 k.2.2.2.2 fun h =>
    haveI := Module.finite_of_finrank_pos h
    (Module.finrank_eq_rank _ _).symm
  have h1 := model_rank C K a k.2.2.2.1 fun v h => k.2.2.1 v ((hT v).2 h)
  exact one_copy hS (actS n V d) (box C.repL C.repS) _ ρ (model_irr C hB hP hG) hρ.1 hρ.2 hne _ _ hPp
    ((congrArg Nat.cast (hprod a)).trans_le h1)
    ((Submodule.rank_mono (level_le (hSec l L Ω s n hn V hV).1 K k.2.1 U k.1 _)).trans hY)
