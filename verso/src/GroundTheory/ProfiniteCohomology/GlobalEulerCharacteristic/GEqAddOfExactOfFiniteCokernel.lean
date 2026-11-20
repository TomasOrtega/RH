import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.UnitsDefs
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ModNEquivOfSurjectiveApplyModNRep
import GroundTheory.GlobalFields.HerbrandQuotients.SUnits
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u v

open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct

section Finiteness

variable {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (n : ℕ) [NeZero n]

/- English proof (translation)
Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `y`. Use `⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Express the relevant statement in the definitionally equal form `(n : ℤ) • (Submodule.Quotient.mk a : ModN A n) = 0`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨a, rfl⟩`.
-/
theorem finite_modN_of_moduleFinite : Finite (ModN A n) := by
  apply Module.finite_of_fg_torsion
  intro y
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (n : ℤ) • (Submodule.Quotient.mk a : ModN A n) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨a, rfl⟩

/- English proof (translation)
Establish `: Module.Finite ℤ (TorsN A n)` using `Module.Finite.of_injective (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).subtype Subtype.val_injective`. Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `x`. Use `⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(n : ℤ) • (x : A) = 0`. Rewrite using `[natCast_zsmul]`. Conclude with `(mem_ker_lsmul_iff n (x : A)).1 x.2`.
-/
theorem finite_torsN_of_moduleFinite : Finite (TorsN A n) := by
  have : Module.Finite ℤ (TorsN A n) :=
    Module.Finite.of_injective (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).subtype
      Subtype.val_injective
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  apply Subtype.ext
  change (n : ℤ) • (x : A) = 0
  rw [natCast_zsmul]
  exact (mem_ker_lsmul_iff n (x : A)).1 x.2

end Finiteness

namespace AdditiveFunction

variable {l : ℕ} [NeZero l] {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

/- English proof (translation)
Establish `hR : ∀ (γ : Γ) (c : C), c ∈ p.range → γ • c ∈ p.range`. Introduce and unpack `γ _ ⟨b, rfl⟩`. Conclude with `⟨γ • b, hpγ γ b⟩`. Set `_` to `subgroupDistribMulAction p.range hR`. Establish `: Module.Finite ℤ p.range` using `Module.Finite.of_injective p.range.subtype.toIntLinearMap Subtype.val_injective`.

Use `finite_modN_of_moduleFinite (A := A) l` as an intermediate fact. Use `finite_torsN_of_moduleFinite (A := A) l` as an intermediate fact. Use `finite_modN_of_moduleFinite (A := p.range) l` as an intermediate fact. Use `finite_torsN_of_moduleFinite (A := p.range) l` as an intermediate fact. Establish `: Finite (C ⧸ p.range.subtype.range)`.

Rewrite using `[AddSubgroup.range_subtype]`. Use `infer_instance`. Rewrite using `[d.g_add f p.rangeRestrict hfγ (fun γ b ↦ Subtype.ext (hpγ γ b)) hf (fun y ↦ by`. Rewrite using `[← hfp y]`. Conclude with `⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩)`.

Use the proof step `p.rangeRestrict_surjective,`. Use the proof step `d.g_eq_of_finite_cokernel p.range.subtype (fun _ _ ↦ rfl) p.range.subtype_injective]`.
-/
theorem g_eq_add_of_exact_of_finite_cokernel {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    [Module.Finite ℤ A] [Module.Finite ℤ C] (f : A →+ B) (p : B →+ C)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b)
    (hf : Function.Injective f) (hfp : Function.Exact f p) [Finite (C ⧸ p.range)] :
    d.g B = d.g A + d.g C := by
  have hR : ∀ (γ : Γ) (c : C), c ∈ p.range → γ • c ∈ p.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hpγ γ b⟩
  let _ := subgroupDistribMulAction p.range hR
  have : Module.Finite ℤ p.range :=
    Module.Finite.of_injective p.range.subtype.toIntLinearMap Subtype.val_injective
  have := finite_modN_of_moduleFinite (A := A) l
  have := finite_torsN_of_moduleFinite (A := A) l
  have := finite_modN_of_moduleFinite (A := p.range) l
  have := finite_torsN_of_moduleFinite (A := p.range) l
  have : Finite (C ⧸ p.range.subtype.range) := by
    rw [AddSubgroup.range_subtype]
    infer_instance
  rw [d.g_add f p.rangeRestrict hfγ (fun γ b ↦ Subtype.ext (hpγ γ b)) hf
      (fun y ↦ by
        rw [← hfp y]
        exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩)
      p.rangeRestrict_surjective,
    d.g_eq_of_finite_cokernel p.range.subtype (fun _ _ ↦ rfl) p.range.subtype_injective]

/- English proof (translation)
Establish `hK : ∀ (γ : Γ) (b : B), b ∈ p.ker → γ • b ∈ p.ker` using `fun γ b hb ↦ by`. Rewrite `hb`, the goal using `[AddMonoidHom.mem_ker]`. Rewrite using `[hpγ, hb, smul_zero]`. Set `_` to `subgroupDistribMulAction p.ker hK`. Use `finite_modN_of_moduleFinite (A := C) l` as an intermediate fact.

Use `finite_torsN_of_moduleFinite (A := C) l` as an intermediate fact. Rewrite using `[d.g_add p.ker.subtype p (fun _ _ ↦ rfl) hpγ p.ker.subtype_injective (fun y ↦ by simp) hp, d.g_eq_zero_of_finite p.ker, zero_add]`.
-/
theorem g_eq_of_surjective_of_finite_ker {B C : Type u} [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ B] [DistribMulAction Γ C] [Module.Finite ℤ C] (p : B →+ C)
    (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b) (hp : Function.Surjective p) [Finite p.ker] :
    d.g B = d.g C := by
  have hK : ∀ (γ : Γ) (b : B), b ∈ p.ker → γ • b ∈ p.ker := fun γ b hb ↦ by
    rw [AddMonoidHom.mem_ker] at hb ⊢
    rw [hpγ, hb, smul_zero]
  let _ := subgroupDistribMulAction p.ker hK
  have := finite_modN_of_moduleFinite (A := C) l
  have := finite_torsN_of_moduleFinite (A := C) l
  rw [d.g_add p.ker.subtype p (fun _ _ ↦ rfl) hpγ p.ker.subtype_injective
      (fun y ↦ by simp) hp, d.g_eq_zero_of_finite p.ker, zero_add]

/- English proof (translation)
Set `` to `repAction (funPermRep ℤ Γ X)`. Establish `ht : ∀ a : X → ℤ, l • a = 0 → a = 0` using `fun a ha ↦ by`. Use function extensionality and compare the values at `x`. Establish `h` using `congrFun ha x`. Simplify using `only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h`.

Conclude with `(mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)`. Set `φ : (X → ℤ) →+ (X → ZMod l)` to `{ toFun := fun a x ↦ (a x : ZMod l) map_zero' := by`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use the proof step `map_add' := fun a b ↦ by`.

Use function extensionality and compare the values at `x`. Simplify using `}`. Establish `hs : Function.Surjective φ` using `fun b ↦ ⟨fun x ↦ (ZMod.intCast_surjective (b x)).choose,`. Use function extensionality and compare the values at `fun x ↦ (ZMod.intCast_surjective (b x)).choose_spec⟩`. Establish `hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) l)`.

Introduce `a`. Rewrite using `[mem_range_lsmul_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hd : ∀ x, (l : ℤ) ∣ a x` using `fun x ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd (a x) l).1 (congrFun h x)`.

Use `choose c hc using hd`. Use `⟨c, funext fun x ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Rewrite using `[hc x]`. Introduce and unpack `⟨y, rfl⟩`.

Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `(((l • y) x : ℤ) : ZMod l) = 0`. Simplify using the standard rewrite rules. Establish `hφ : ∀ (γ : Γ) (a : X → ℤ), φ (γ • a) = funPermRep (ZMod l) Γ X γ (φ a)` using `fun _ _ ↦ rfl`. Use `finite_modN_of_moduleFinite (A := X → ℤ) l` as an intermediate fact.

Rewrite using `[d.g_eq_of_torsion_trivial _ ht]`. Conclude with `d.toFun_congr _ _ (modNEquivOfSurjective φ hs hker) (modNEquivOfSurjective_apply_modNRep _ φ hs hker hφ)`.
-/
theorem g_funPermRep (X : Type u) [MulAction Γ X] [Finite X] :
    letI := repAction (funPermRep ℤ Γ X)
    d.g (X → ℤ) = d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) := by
  let := repAction (funPermRep ℤ Γ X)
  have ht : ∀ a : X → ℤ, l • a = 0 → a = 0 := fun a ha ↦ by
    funext x
    have h := congrFun ha x
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne l)
  let φ : (X → ℤ) →+ (X → ZMod l) :=
    { toFun := fun a x ↦ (a x : ZMod l)
      map_zero' := by
        funext x
        simp
      map_add' := fun a b ↦ by
        funext x
        simp }
  have hs : Function.Surjective φ := fun b ↦
    ⟨fun x ↦ (ZMod.intCast_surjective (b x)).choose,
      funext fun x ↦ (ZMod.intCast_surjective (b x)).choose_spec⟩
  have hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) l) := by
    intro a
    rw [mem_range_lsmul_iff]
    constructor
    · intro h
      have hd : ∀ x, (l : ℤ) ∣ a x := fun x ↦
        (ZMod.intCast_zmod_eq_zero_iff_dvd (a x) l).1 (congrFun h x)
      choose c hc using hd
      refine ⟨c, funext fun x ↦ ?_⟩
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hc x]
    · rintro ⟨y, rfl⟩
      funext x
      change (((l • y) x : ℤ) : ZMod l) = 0
      simp
  have hφ : ∀ (γ : Γ) (a : X → ℤ), φ (γ • a) = funPermRep (ZMod l) Γ X γ (φ a) :=
    fun _ _ ↦ rfl
  have := finite_modN_of_moduleFinite (A := X → ℤ) l
  rw [d.g_eq_of_torsion_trivial _ ht]
  exact d.toFun_congr _ _ (modNEquivOfSurjective φ hs hker)
    (modNEquivOfSurjective_apply_modNRep _ φ hs hker hφ)

end AdditiveFunction

section LogLattice

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Set `bM` to `Module.Free.chooseBasis ℤ (logLattice L)`. Set `b` to `bM.prod (Basis.singleton Unit ℤ)`. Set `B` to `Algebra.TensorProduct.basis ℝ b`. Set `E` to `(logLatticeProdMap (L := L)).liftBaseChange ℝ`. Set `v` to `Sum.elim (fun i ↦ (bM i : InfinitePlace L → ℝ)) (fun _ : Unit ↦ (1 : InfinitePlace L → ℝ))`.

Establish `hEB : ∀ j, E (B j) = v j`. Introduce `j`. Rewrite using `[Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]`. Break down `j with i | u` into its components or cases. Simplify using `[b, v, Basis.prod_apply, logLatticeProdMap_apply]`.

Simplify using `[b, v, Basis.prod_apply, logLatticeProdMap_apply]`. Establish `hli : LinearIndependent ℝ v` using `linearIndependent_logLattice_one bM`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (logLattice L) ⊕ Unit) = finrank ℝ (InfinitePlace L → ℝ)`. Rewrite using `[Fintype.card_sum, Fintype.card_unit, Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_chooseBasisIndex, finrank_logLattice, rank]`. Establish `: 0 < Fintype.card (InfinitePlace L)` using `Fintype.card_pos`.

Use linear arithmetic over natural numbers and integers. Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank hcard`. Establish `hsurj : Function.Surjective E`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `⟨B j, hEB j⟩`. Establish `hdim : finrank ℝ (ℝ ⊗[ℤ] (logLattice L × ℤ)) = finrank ℝ (InfinitePlace L → ℝ)`. Rewrite using `[Module.finrank_eq_card_basis B, hcard]`. Establish `hinj : Function.Injective E` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj`. Establish `hbij : Function.Bijective E` using `⟨hinj, hsurj⟩`.

Set `P` to `TensorProduct.piScalarRight ℤ ℝ ℝ (InfinitePlace L)`. Set `e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ)` to `(LinearEquiv.ofBijective E hbij).trans P.symm`. Establish `hE : ∀ (g : L ≃ₐ[K] L) y, E ((((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (E y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul, logLatticeProdMap_comm]`. Consider the case `add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]`. Use `⟨e, fun g y ↦ ?_⟩` and prove the remaining obligations.

Apply `P.injective` to reduce the goal to its premises. Simplify using `only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hE]`.
-/
theorem exists_logLatticeProd_real_equiv :
    ∃ e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ),
      ∀ (g : L ≃ₐ[K] L) y, e ((((logLatticeRep K L).prod
          (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
        (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g).baseChange ℝ (e y) := by
  classical
  let bM := Module.Free.chooseBasis ℤ (logLattice L)
  let b := bM.prod (Basis.singleton Unit ℤ)
  let B := Algebra.TensorProduct.basis ℝ b
  let E := (logLatticeProdMap (L := L)).liftBaseChange ℝ
  let v := Sum.elim (fun i ↦ (bM i : InfinitePlace L → ℝ))
    (fun _ : Unit ↦ (1 : InfinitePlace L → ℝ))
  have hEB : ∀ j, E (B j) = v j := by
    intro j
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
    rcases j with i | u
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
  have hli : LinearIndependent ℝ v := linearIndependent_logLattice_one bM
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (logLattice L) ⊕ Unit) =
      finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Fintype.card_sum, Fintype.card_unit, Module.finrank_fintype_fun_eq_card,
      ← Module.finrank_eq_card_chooseBasisIndex, finrank_logLattice, rank]
    have : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hsurj : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨B j, hEB j⟩
  have hdim : finrank ℝ (ℝ ⊗[ℤ] (logLattice L × ℤ)) = finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Module.finrank_eq_card_basis B, hcard]
  have hinj : Function.Injective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  have hbij : Function.Bijective E := ⟨hinj, hsurj⟩
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ (InfinitePlace L)
  let e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ) :=
    (LinearEquiv.ofBijective E hbij).trans P.symm
  have hE : ∀ (g : L ≃ₐ[K] L) y, E ((((logLatticeRep K L).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (E y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        map_smul, logLatticeProdMap_comm]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  refine ⟨e, fun g y ↦ ?_⟩
  apply P.injective
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply,
    LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hE]

/- English proof (translation)
Take `⟨e, he⟩` from `exists_logLatticeProd_real_equiv (K := K) (L := L)`. Conclude with `exists_injective_intertwiner_of_real_equiv _ _ e he`.
-/
theorem exists_logLatticeProd_intertwiner :
    ∃ φ : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ (g : L ≃ₐ[K] L) x, φ (((logLatticeRep K L).prod
          (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
        funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g (φ x) := by
  obtain ⟨e, he⟩ := exists_logLatticeProd_real_equiv (K := K) (L := L)
  exact exists_injective_intertwiner_of_real_equiv _ _ e he

end LogLattice

namespace AdditiveFunction

section Units

variable {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (L ≃ₐ[K] L))

/- English proof (translation)
Set `_` to `repAction (logLatticeRep K L)`. Set `_` to `trivialIntAction.{u} (L ≃ₐ[K] L)`. Set `_` to `repAction (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L))`. Take `⟨φ, hφi, ⟨n, hn, hφn⟩, hφγ⟩` from `exists_logLatticeProd_intertwiner (K := K) (L := L)`. Set `ψ : logLattice L × ULift.{u} ℤ →+ (InfinitePlace L → ℤ)` to `φ.toAddMonoidHom.comp ((AddMonoidHom.id _).prodMap AddEquiv.ulift.toAddMonoidHom)`.

Establish `hψ : ∀ x, ψ x = φ (x.1, x.2.down)` using `fun _ ↦ rfl`. Establish `hψi : Function.Injective ψ`. Introduce `x y h`. Rewrite `h` using `[hψ, hψ]`. Establish `h'` using `hφi h`.

Conclude with `_root_.Prod.ext (Prod.mk.inj h').1 (ULift.ext _ _ (Prod.mk.inj h').2)`. Establish `hψγ : ∀ (γ : L ≃ₐ[K] L) x, ψ (γ • x) = γ • ψ x`. Introduce `γ x`. Express the relevant statement in the definitionally equal form `φ (logLatticeRep K L γ x.1, x.2.down) = funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) γ (φ (x.1, x.2.down))`. Rewrite using `[← hφγ]`.

Both sides reduce to the same expression. Establish `: Finite ((InfinitePlace L → ℤ) ⧸ ψ.range)` using `finite_quotient_of_smul_mem _ hn fun y ↦ by`. Take `⟨x, hx⟩` from `hφn y`. Conclude with `⟨(x.1, ULift.up x.2), hx⟩`. Use `finite_modN_of_moduleFinite (A := InfinitePlace L → ℤ) l` as an intermediate fact.

Use `finite_torsN_of_moduleFinite (A := InfinitePlace L → ℤ) l` as an intermediate fact. Use `finite_modN_of_moduleFinite (A := logLattice L) l` as an intermediate fact. Use `finite_torsN_of_moduleFinite (A := logLattice L) l` as an intermediate fact. Use `finite_modN_uliftInt.{u} l` as an intermediate fact. Use `finite_torsN_uliftInt.{u} l` as an intermediate fact.

Rewrite using `[← d.g_funPermRep (InfinitePlace L), d.g_eq_of_finite_cokernel' ψ hψγ hψi, d.g_add (AddMonoidHom.inl (logLattice L) (ULift.{u} ℤ)) (AddMonoidHom.snd (logLattice L) (ULift.{u} ℤ)) (fun γ a ↦ _root_.Prod.ext rfl (smul_zero γ).symm) (fun _ _ ↦ rfl) (fun a b h ↦ congrArg Prod.fst h) …`. Introduce and unpack `⟨a, t⟩`. Prove the components needed by the constructor for the conclusion. Introduce `ht`. Express the relevant statement in the definitionally equal form `t = 0 at ht`.

Conclude with `⟨a, by rw [ht]; rfl⟩`. Introduce and unpack `⟨a', h⟩`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem g_logLattice_add_one :
    letI := repAction (logLatticeRep K L)
    d.g (logLattice L) + d.one =
      d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) := by
  let _ := repAction (logLatticeRep K L)
  let _ := trivialIntAction.{u} (L ≃ₐ[K] L)
  let _ := repAction (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L))
  obtain ⟨φ, hφi, ⟨n, hn, hφn⟩, hφγ⟩ := exists_logLatticeProd_intertwiner (K := K) (L := L)
  let ψ : logLattice L × ULift.{u} ℤ →+ (InfinitePlace L → ℤ) :=
    φ.toAddMonoidHom.comp ((AddMonoidHom.id _).prodMap AddEquiv.ulift.toAddMonoidHom)
  have hψ : ∀ x, ψ x = φ (x.1, x.2.down) := fun _ ↦ rfl
  have hψi : Function.Injective ψ := by
    intro x y h
    rw [hψ, hψ] at h
    have h' := hφi h
    exact _root_.Prod.ext (Prod.mk.inj h').1 (ULift.ext _ _ (Prod.mk.inj h').2)
  have hψγ : ∀ (γ : L ≃ₐ[K] L) x, ψ (γ • x) = γ • ψ x := by
    intro γ x
    change φ (logLatticeRep K L γ x.1, x.2.down) =
      funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) γ (φ (x.1, x.2.down))
    rw [← hφγ]
    rfl
  have : Finite ((InfinitePlace L → ℤ) ⧸ ψ.range) :=
    finite_quotient_of_smul_mem _ hn fun y ↦ by
      obtain ⟨x, hx⟩ := hφn y
      exact ⟨(x.1, ULift.up x.2), hx⟩
  have := finite_modN_of_moduleFinite (A := InfinitePlace L → ℤ) l
  have := finite_torsN_of_moduleFinite (A := InfinitePlace L → ℤ) l
  have := finite_modN_of_moduleFinite (A := logLattice L) l
  have := finite_torsN_of_moduleFinite (A := logLattice L) l
  have := finite_modN_uliftInt.{u} l
  have := finite_torsN_uliftInt.{u} l
  rw [← d.g_funPermRep (InfinitePlace L), d.g_eq_of_finite_cokernel' ψ hψγ hψi,
    d.g_add (AddMonoidHom.inl (logLattice L) (ULift.{u} ℤ))
      (AddMonoidHom.snd (logLattice L) (ULift.{u} ℤ))
      (fun γ a ↦ _root_.Prod.ext rfl (smul_zero γ).symm) (fun _ _ ↦ rfl)
      (fun a b h ↦ congrArg Prod.fst h) ?_ (fun t ↦ ⟨(0, t), rfl⟩),
    d.g_of_trivial_int (ULift.{u} ℤ) (fun _ _ ↦ rfl) AddEquiv.ulift]
  rintro ⟨a, t⟩
  constructor
  · intro ht
    change t = 0 at ht
    exact ⟨a, by rw [ht]; rfl⟩
  · rintro ⟨a', h⟩
    rw [← h]
    rfl

/- English proof (translation)
Set `_` to `repAction (unitsRep K L)`. Set `_` to `repAction (logLatticeRep K L)`. Set `p : Additive (𝓞 L)ˣ →+ logLattice L` to `(fullLog L).toIntLinearMap.rangeRestrict.toAddMonoidHom`. Establish `hp : Function.Surjective p` using `(fullLog L).toIntLinearMap.surjective_rangeRestrict`. Establish `: Finite p.ker`.

Use `Finite.of_injective (β := torsion L) (fun x ↦ ⟨(x : Additive (𝓞 L)ˣ).toMul, (fullLog_eq_zero_iff L x).1 ?_⟩) ?_` and prove the remaining obligations. Conclude with `congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)`. Introduce `x y h`. Simplify using `only [Subtype.mk.injEq] at h`. Conclude with `Subtype.ext (Additive.toMul.injective h)`.

Rewrite using `[d.g_eq_of_surjective_of_finite_ker p (fun γ x ↦ Subtype.ext (fullLog_unitsRep γ x)) hp, ← d.g_logLattice_add_one, add_sub_cancel_right]`.
-/
theorem g_units :
    letI := repAction (unitsRep K L)
    d.g (Additive (𝓞 L)ˣ) =
      d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) -
        d.one := by
  let _ := repAction (unitsRep K L)
  let _ := repAction (logLatticeRep K L)
  let p : Additive (𝓞 L)ˣ →+ logLattice L :=
    (fullLog L).toIntLinearMap.rangeRestrict.toAddMonoidHom
  have hp : Function.Surjective p := (fullLog L).toIntLinearMap.surjective_rangeRestrict
  have : Finite p.ker := by
    refine Finite.of_injective (β := torsion L)
      (fun x ↦ ⟨(x : Additive (𝓞 L)ˣ).toMul, (fullLog_eq_zero_iff L x).1 ?_⟩) ?_
    · exact congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
    · intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Additive.toMul.injective h)
  rw [d.g_eq_of_surjective_of_finite_ker p (fun γ x ↦ Subtype.ext (fullLog_unitsRep γ x)) hp,
    ← d.g_logLattice_add_one, add_sub_cancel_right]

/- English proof (translation)
Set `_` to `sUnitAction S hS`. Set `_` to `stableMulAction S hS`. Set `_` to `repAction (unitsRep K L)`. Set `_` to `repAction (funPermRep ℤ (L ≃ₐ[K] L) S)`. Establish `: Module.Finite ℤ (Additive (𝓞 L)ˣ)` using `Module.Finite.of_injective (SUnit.ofUnits (K := L) S).toAdditive.toIntLinearMap (fun a b h ↦ SUnit.ofUnits_injective S (congrArg Additive.toMul h))`.

Establish `: Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K` using `L) S).toAddMonoidHom.range) := finite_quotient_range_valuationVector S`. Rewrite using `[d.g_eq_add_of_exact_of_finite_cokernel (SUnit.ofUnits (K := L) S).toAdditive (SUnit.valuationVector (K := L) S).toAddMonoidHom (fun γ a ↦ ofUnits_unitsRep S hS γ a) (fun γ b ↦ valuationVector_sUnitRep S hS γ b) (fun a b h ↦ SUnit.ofUnits_injective S (congrArg Additive.toMul h)) …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g_sUnits (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
    (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI := sUnitAction S hS
    letI := stableMulAction S hS
    d.g (Additive (S.unit L)) =
      d.toFun (S → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) S) +
        d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) -
          d.one := by
  let _ := sUnitAction S hS
  let _ := stableMulAction S hS
  let _ := repAction (unitsRep K L)
  let _ := repAction (funPermRep ℤ (L ≃ₐ[K] L) S)
  have : Module.Finite ℤ (Additive (𝓞 L)ˣ) :=
    Module.Finite.of_injective (SUnit.ofUnits (K := L) S).toAdditive.toIntLinearMap
      (fun a b h ↦ SUnit.ofUnits_injective S (congrArg Additive.toMul h))
  have : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) :=
    finite_quotient_range_valuationVector S
  rw [d.g_eq_add_of_exact_of_finite_cokernel (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom (fun γ a ↦ ofUnits_unitsRep S hS γ a)
      (fun γ b ↦ valuationVector_sUnitRep S hS γ b)
      (fun a b h ↦ SUnit.ofUnits_injective S (congrArg Additive.toMul h))
      (exact_ofUnits_valuationVector S),
    d.g_units, d.g_funPermRep S]
  ring

end Units

end AdditiveFunction

end GroundTheory.ProfCoh
