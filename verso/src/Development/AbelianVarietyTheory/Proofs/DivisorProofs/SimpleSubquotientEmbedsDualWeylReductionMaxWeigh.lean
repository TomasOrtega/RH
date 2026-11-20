import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeylStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightFormOnSimpleSubquotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotientStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `O _ _ _ _ N ι _ _ lam ϖ hϖ hlam hBC hC Gm _ _ hS hSQ w hw hJ hmax`. Take `⟨z₀, hz₀, hfix⟩` from `hJ`. Take `⟨φ, hφ0, hφc, hφp⟩` from `GlobalTheory.T.exists_weightForm_on_simple_subquotient O N ι lam ϖ hϖ Gm hSQ w z₀ hz₀ hfix`. Take `⟨Pz, hPc, hPg, hPp, hPn, hPz0⟩` from `GlobalTheory.T.exists_matrixCoefficientPoly_simpleSubquotient O N ι lam ϖ hϖ hlam hC Gm hSQ w hmax φ z₀ hφ0 hfix hφc hφp`. Establish `hmuA : ∀ τ, Antitone (res N (GlobalTheory.HighWt.extW N w τ))` using `fun τ => by`.

Rewrite using `[GlobalTheory.HighWt.res_extW]`. Conclude with `hw τ`. Establish `hle : (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) ≤ LinearMap.ker (redT O N (GlobalTheory.HighWt.extW N w) ϖ)`. Use `Submodule.smul_le.2 fun r hr n _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_smul]`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite using `[Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), mul_zero, map_zero, zero_mul]`. Use `set L := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))).liftQ (redT O N (GlobalTheory.HighWt.extW N w) ϖ) hle with hL`. Establish `hLmk : ∀ y, L (Submodule.Quotient.mk y) = redT O N (GlobalTheory.HighWt.extW N w) ϖ y` using `fun y => rfl`. Establish `hLinj : Function.Injective L`.

Rewrite using `[← LinearMap.ker_eq_bot, hL, Submodule.ker_liftQ_eq_bot]`. Introduce `y hy`. Conclude with `GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC y hy`. Establish `hsurj : ∀ z, ∃ q, L q = Pz z`. Introduce `z`.

Establish `h1 : Pz z ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (GlobalTheory.HighWt.extW N w τ))`. Establish `e : (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) = w` using `funext fun τ => GlobalTheory.HighWt.res_extW N w τ`. Rewrite using `[e]`. Use `haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Use `letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _`.

Conclude with `GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl (O ⧸ Ideal.span {ϖ}) N ι w (Pz z) (hPn z)`. Take `⟨y, hy⟩` from `GlobalTheory.T.exists_lift_dualWeylTensorReduction O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC _ h1`. Conclude with `⟨Submodule.Quotient.mk y, hy⟩`. Use `choose q hq using hsurj`. Establish `hsm : ∀ (a : alg O N lam) (z : Gm), Pz z = 0 → Pz (a • z) = 0`.

Introduce and unpack `⟨a, ha⟩`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Introduce `z hz`. Break down `hx with ⟨g, rfl⟩ | ⟨τ, v, hp⟩` into its components or cases.

Establish `e : (⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩ : alg O N lam) = grpA O N lam g` using `rfl`. Rewrite using `[e, hPg, hz, map_zero]`. Rewrite using `[hPp τ v _ hp, hz, map_zero]`. Consider the case `algebraMap c`. Introduce `z hz`.

Establish `e : (⟨algebraMap O _ c, Subalgebra.algebraMap_mem _ c⟩ : alg O N lam) = algebraMap O (alg O N lam) c` using `rfl`. Rewrite using `[e, hPc, hz, mul_zero]`. Consider the case `add x y hx hy ihx ihy`. Introduce `z hz`. Establish `e : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`.

Rewrite using `[e, add_smul, map_add, ihx z hz, ihy z hz, add_zero]`. Consider the case `mul x y hx hy ihx ihy`. Introduce `z hz`. Establish `e : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ * ⟨y, hy⟩` using `rfl`. Rewrite using `[e, mul_smul]`.

Conclude with `ihx _ (ihy z hz)`. Set `K : Submodule (alg O N lam) Gm` to `{ carrier := {z | Pz z = 0} add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb, add_zero] zero_mem' := by simp smul_mem' := fun a z hz => hsm a z hz }`. Establish `hK : K = ⊥` using `by haveI : IsSimpleOrder (Submodule (alg O N lam) Gm) := (isSimpleModule_iff _ _).1 hS`. Break down `IsSimpleOrder.eq_bot_or_eq_top K with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Establish `: z₀ ∈ K` using `h ▸ Submodule.mem_top`. Conclude with `hPz0 this`. Set `ψ : Gm →+ NablaT O N (GlobalTheory.HighWt.extW N w) ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w)))` to `{ toFun := q map_zero' := hLinj (by rw [hq, map_zero, map_zero]) map_add' := fun a b => hLinj (by rw [hq, map_add, map_add, hq, hq]) }`. Use `⟨ψ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Establish `h1 : Pz (a - b) = 0`. Rewrite using `[map_sub, ← hq a, ← hq b]`. Conclude with `sub_eq_zero.2 (congrArg L hab)`. Establish `h2 : a - b ∈ K` using `h1`.

Rewrite `h2` using `[hK, Submodule.mem_bot]`. Conclude with `sub_eq_zero.1 h2`. Introduce `c z`. Apply `hLinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `L (q _) = L (c • q z)`.

Rewrite using `[hq, hPc, LinearMap.map_smul, hq, Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]`. Introduce `g z y hzy`. Apply `hLinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `L (q _) = _`. Establish `hzy' : q z = Submodule.Quotient.mk y` using `hzy`.

Rewrite using `[hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action, hPg, ← hq z, hzy', hLmk]`. Introduce `τ v a a' ha ha' z y hzy`. Apply `hLinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `L (q _) = _`. Establish `hzy' : q z = Submodule.Quotient.mk y` using `hzy`.

Rewrite using `[hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_weightProjector O N ι _ ϖ τ v a' ha', hPp τ v a ha, ← hq z, hzy', hLmk]`.
-/
theorem embeds_of_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam hBC hC Gm _ _ hS hSQ w hw hJ hmax
  obtain ⟨z₀, hz₀, hfix⟩ := hJ
  obtain ⟨φ, hφ0, hφc, hφp⟩ := GlobalTheory.T.exists_weightForm_on_simple_subquotient O N ι lam ϖ hϖ Gm hSQ w z₀ hz₀ hfix
  obtain ⟨Pz, hPc, hPg, hPp, hPn, hPz0⟩ :=
    GlobalTheory.T.exists_matrixCoefficientPoly_simpleSubquotient O N ι lam ϖ hϖ hlam hC Gm hSQ w hmax φ z₀ hφ0 hfix hφc hφp
  have hmuA : ∀ τ, Antitone (res N (GlobalTheory.HighWt.extW N w τ)) := fun τ => by
    rw [GlobalTheory.HighWt.res_extW]; exact hw τ
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) ≤
      LinearMap.ker (redT O N (GlobalTheory.HighWt.extW N w) ϖ) := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), mul_zero, map_zero, zero_mul]
  set L := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))).liftQ
    (redT O N (GlobalTheory.HighWt.extW N w) ϖ) hle with hL
  have hLmk : ∀ y, L (Submodule.Quotient.mk y) = redT O N (GlobalTheory.HighWt.extW N w) ϖ y := fun y => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, hL, Submodule.ker_liftQ_eq_bot]
    intro y hy
    exact GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC y hy
  have hsurj : ∀ z, ∃ q, L q = Pz z := by
    intro z
    have h1 : Pz z ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) := by
      have e : (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) = w := funext fun τ => GlobalTheory.HighWt.res_extW N w τ
      rw [e]
      haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
      letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
      exact GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl (O ⧸ Ideal.span {ϖ}) N ι w (Pz z) (hPn z)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lift_dualWeylTensorReduction O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC _ h1
    exact ⟨Submodule.Quotient.mk y, hy⟩
  choose q hq using hsurj
  have hsm : ∀ (a : alg O N lam) (z : Gm), Pz z = 0 → Pz (a • z) = 0 := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨g, rfl⟩ | ⟨τ, v, hp⟩
      · have e : (⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩ : alg O N lam) = grpA O N lam g := rfl
        rw [e, hPg, hz, map_zero]
      · rw [hPp τ v _ hp, hz, map_zero]
    | algebraMap c =>
      intro z hz
      have e : (⟨algebraMap O _ c, Subalgebra.algebraMap_mem _ c⟩ : alg O N lam) = algebraMap O (alg O N lam) c := rfl
      rw [e, hPc, hz, mul_zero]
    | add x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, add_smul, map_add, ihx z hz, ihy z hz, add_zero]
    | mul x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, mul_smul]
      exact ihx _ (ihy z hz)
  let K : Submodule (alg O N lam) Gm :=
    { carrier := {z | Pz z = 0}
      add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun a z hz => hsm a z hz }
  have hK : K = ⊥ := by
    haveI : IsSimpleOrder (Submodule (alg O N lam) Gm) := (isSimpleModule_iff _ _).1 hS
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      have : z₀ ∈ K := h ▸ Submodule.mem_top
      exact hPz0 this
  let ψ : Gm →+ NablaT O N (GlobalTheory.HighWt.extW N w) ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) :=
    { toFun := q
      map_zero' := hLinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hLinj (by rw [hq, map_add, map_add, hq, hq]) }
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : Pz (a - b) = 0 := by
      rw [map_sub, ← hq a, ← hq b]
      exact sub_eq_zero.2 (congrArg L hab)
    have h2 : a - b ∈ K := h1
    rw [hK, Submodule.mem_bot] at h2
    exact sub_eq_zero.1 h2
  · intro c z
    apply hLinj
    change L (q _) = L (c • q z)
    rw [hq, hPc, LinearMap.map_smul, hq, Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  · intro g z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action, hPg, ← hq z, hzy', hLmk]
  · intro τ v a a' ha ha' z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_weightProjector O N ι _ ϖ τ v a' ha', hPp τ v a ha, ← hq z, hzy', hLmk]

end GlobalTheory.HighWtEmb

end
