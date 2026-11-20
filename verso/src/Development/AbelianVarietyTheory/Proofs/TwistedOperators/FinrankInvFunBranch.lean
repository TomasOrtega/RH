import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorShuffleEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorMapSurjectiveAndKerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorRepresentationIntertwinerCompatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsOfIsoDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunDualTprodEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoOuterDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrrepCompConjIsoDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOnePlaceIsoDirectSumPartitionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterIrrIsoWeylRepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeightsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadColumnWeightsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StrictInterlaceGanGrossPrasadBigSmallStatement

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

noncomputable section

namespace GlobalTheory.OneFunctional

/- English proof (translation)
Use `choose π hs he hk using h`. Take `⟨e, hE⟩` from `GlobalTheory.T.exists_piTensor_tmul_piTensor_linearEquiv_piTensor_tmul ι F V`. Take `⟨h1, h2⟩` from `GlobalTheory.T.piTensorProduct_map_surjective_and_dual_vanishes ι _ _ π hs`. Use `⟨PiTensorProduct.map π ∘ₗ e.toLinearMap, h1.comp e.surjective, fun h g f v => ?_, fun l hl x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `f using PiTensorProduct.induction_on with`.

Consider the case `add a b ha hb => simp only [map_add, TensorProduct.add_tmul, ha, hb]`. Consider the case `smul_tprod c f`. Proceed by induction on `v using PiTensorProduct.induction_on with`. Consider the case `add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]`. Consider the case `smul_tprod d v`.

Simplify using `[outer_apply, outer₂_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul, hE, he]`. Take `⟨x, rfl⟩` from `e.symm.surjective x`. Use `h2 (l ∘ₗ e.symm.toLinearMap) (fun τ y hy => ?_) x (by simpa using hx)` and prove the remaining obligations. Set `m` to `(l ∘ₗ e.symm.toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ)`. Establish `key : ∀ (k : H) (f : F τ) (v : V τ) (y : ∀ σ, F σ ⊗[ℂ] V σ), m (Function.update y τ (φ τ (k, 1) f ⊗ₜ σ τ k v)) = m (Function.update y τ (f ⊗ₜ v))`.

Introduce `k f v y`. Set `u : ι → H` to `Function.update 1 τ k`. Set `T : ∀ σ, F σ ⊗[ℂ] V σ →ₗ[ℂ] F σ ⊗[ℂ] V σ` to `fun ρ => TensorProduct.map (φ ρ (u ρ, 1)) (σ ρ (u ρ))`. Establish `hT : (l ∘ₗ e.symm.toLinearMap) ∘ₗ PiTensorProduct.map T = l ∘ₗ e.symm.toLinearMap`. Rewrite using `[← LinearMap.cancel_right (g := e.toLinearMap) e.surjective]`.

Use `TensorProduct.ext ?_` and prove the remaining obligations. Use extensionality with `f' v'`. Establish `h3` using `hl u (PiTensorProduct.tprod ℂ f') (PiTensorProduct.tprod ℂ v')`. Rewrite `h3` using `[outer_apply, outer₂_apply, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hE, PiTensorProduct.map_tprod, T, TensorProduct.map_tmul]`.

Rewrite using `[← hE, ← hE, e.symm_apply_apply, e.symm_apply_apply]`. Conclude with `h3`. Establish `h4` using `LinearMap.congr_fun hT (PiTensorProduct.tprod ℂ (Function.update y τ (f ⊗ₜ v)))`. Rewrite `h4` using `[LinearMap.comp_apply, PiTensorProduct.map_tprod]`. Use `Eq.trans (congrArg m (funext fun ρ => ?_)) h4` and prove the remaining obligations.

Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Simplify using `[T, u]`. Establish `: φ ρ (1, 1) = 1` using `map_one _`. Simplify using `[T, u, Function.update_of_ne hρ, this, Module.End.one_eq_id]`.

Use `hk τ (m.toLinearMap y τ) (fun k f v => key k f v y) (y τ) hy` as an intermediate fact. Simplify `this` using `[m]`.
-/
theorem Contracts.outer {ι H G : Type} [Fintype ι] [DecidableEq ι] [Monoid H] [Monoid G] {F V W : ι → Type}
    [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] {φ : ∀ τ, Representation ℂ (H × G) (F τ)}
    {σ : ∀ τ, Representation ℂ H (V τ)} {σ' : ∀ τ, Representation ℂ G (W τ)} (h : ∀ τ, Contracts (φ τ) (σ τ) (σ' τ)) :
    Contracts (outer₂ φ) (outer σ) (outer σ') := by
  choose π hs he hk using h
  obtain ⟨e, hE⟩ := GlobalTheory.T.exists_piTensor_tmul_piTensor_linearEquiv_piTensor_tmul ι F V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.piTensorProduct_map_surjective_and_dual_vanishes ι _ _ π hs
  refine ⟨PiTensorProduct.map π ∘ₗ e.toLinearMap, h1.comp e.surjective, fun h g f v => ?_, fun l hl x hx => ?_⟩
  · induction f using PiTensorProduct.induction_on with
    | add a b ha hb => simp only [map_add, TensorProduct.add_tmul, ha, hb]
    | smul_tprod c f =>
      induction v using PiTensorProduct.induction_on with
      | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
      | smul_tprod d v =>
        simp [outer_apply, outer₂_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul, hE, he]
  · obtain ⟨x, rfl⟩ := e.symm.surjective x
    refine h2 (l ∘ₗ e.symm.toLinearMap) (fun τ y hy => ?_) x (by simpa using hx)
    let m := (l ∘ₗ e.symm.toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ)
    have key : ∀ (k : H) (f : F τ) (v : V τ) (y : ∀ σ, F σ ⊗[ℂ] V σ),
        m (Function.update y τ (φ τ (k, 1) f ⊗ₜ σ τ k v)) = m (Function.update y τ (f ⊗ₜ v)) := by
      intro k f v y
      let u : ι → H := Function.update 1 τ k
      let T : ∀ σ, F σ ⊗[ℂ] V σ →ₗ[ℂ] F σ ⊗[ℂ] V σ := fun ρ => TensorProduct.map (φ ρ (u ρ, 1)) (σ ρ (u ρ))
      have hT : (l ∘ₗ e.symm.toLinearMap) ∘ₗ PiTensorProduct.map T = l ∘ₗ e.symm.toLinearMap := by
        rw [← LinearMap.cancel_right (g := e.toLinearMap) e.surjective]
        refine TensorProduct.ext ?_
        ext f' v'
        have h3 := hl u (PiTensorProduct.tprod ℂ f') (PiTensorProduct.tprod ℂ v')
        rw [outer_apply, outer₂_apply, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod] at h3
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, hE, PiTensorProduct.map_tprod, T, TensorProduct.map_tmul]
        rw [← hE, ← hE, e.symm_apply_apply, e.symm_apply_apply]
        exact h3
      have h4 := LinearMap.congr_fun hT (PiTensorProduct.tprod ℂ (Function.update y τ (f ⊗ₜ v)))
      rw [LinearMap.comp_apply, PiTensorProduct.map_tprod] at h4
      refine Eq.trans (congrArg m (funext fun ρ => ?_)) h4
      by_cases hρ : ρ = τ
      · subst hρ; simp [T, u]
      · have : φ ρ (1, 1) = 1 := map_one _
        simp [T, u, Function.update_of_ne hρ, this, Module.End.one_eq_id]
    have := hk τ (m.toLinearMap y τ) (fun k f v => key k f v y) (y τ) hy
    simpa [m] using this

/- English proof (translation)
Establish `hc : ∀ τ, Contracts ((ρ τ).comp (MonoidHom.fst H PUnit) : Representation ℂ (H × PUnit) (F τ)) (σ τ) (1 : Representation ℂ PUnit ℂ)`. Introduce `τ`. Take `⟨ε, h0, hε⟩` from `finrank_eq_one_iff'.1 (h τ)`. Establish `h0' : ε.1 ≠ 0` using `fun e => h0 (Subtype.ext e)`. Use `⟨ε.1, LinearMap.range_eq_top.1 (Module.Dual.range_eq_top_of_ne_zero h0'), fun k g f v => ?_, fun l hl x hx => ?_⟩` and prove the remaining obligations.

Conclude with `ε.2 k (f ⊗ₜ v)`. Establish `hl' : l ∈ invFun ((ρ τ).tprod (σ τ))`. Introduce `k z`. Proceed by induction on `z with`. Consider the case `zero => simp`.

Consider the case `tmul a b => exact hl k a b`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Take `⟨c, hc⟩` from `hε ⟨l, hl'⟩`. Establish `: c • ε.1 = l` using `congrArg Subtype.val hc`. Rewrite using `[← this, LinearMap.smul_apply, hx, smul_zero]`.

Take `⟨π, hs, he, hk⟩` from `Contracts.outer hc`. Set `ε : Module.Dual ℂ _` to `(PiTensorProduct.constantBaseRingEquiv ι ℂ).toLinearMap ∘ₗ π`. Establish `hs' : Function.Surjective ε` using `(PiTensorProduct.constantBaseRingEquiv ι ℂ).surjective.comp hs`. Establish `hε : ε ∈ invFun ((outer ρ).tprod (outer σ))`. Introduce `k z`.

Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Use `he k 1 a b` as an intermediate fact. Rewrite `this` using `[map_one]`.

Conclude with `congrArg (PiTensorProduct.constantBaseRingEquiv ι ℂ) this`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Take `⟨z, hz⟩` from `hs' 1`. Use `finrank_eq_one_iff'.2 ⟨⟨ε, hε⟩, fun e => ?_, fun l => ⟨l.1 z, Subtype.ext (LinearMap.ext fun x => ?_)⟩⟩` and prove the remaining obligations. Establish `: ε = 0` using `congrArg Subtype.val e`.

Rewrite `hz` using `[this]`. Simplify using `at hz`. Use `hk l.1 (fun k f v => l.2 k (f ⊗ₜ v)) (x - ε x • z) ((PiTensorProduct.constantBaseRingEquiv ι ℂ).map_eq_zero_iff.1 (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `ε _ = 0`. Rewrite using `[map_sub, map_smul, hz]`.

Use the proof step `simp))`. Rewrite `this` using `[map_sub, map_smul, sub_eq_zero]`. Rewrite using `[this]`. Simplify using `[mul_comm]`.
-/
theorem finrank_invFun_outer {ι H : Type} [Fintype ι] [DecidableEq ι] [Monoid H] {F V : ι → Type}
    [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (ρ : ∀ τ, Representation ℂ H (F τ)) (σ : ∀ τ, Representation ℂ H (V τ))
    (h : ∀ τ, Module.finrank ℂ (invFun ((ρ τ).tprod (σ τ))) = 1) :
    Module.finrank ℂ (invFun ((outer ρ).tprod (outer σ))) = 1 := by
  have hc : ∀ τ, Contracts ((ρ τ).comp (MonoidHom.fst H PUnit) : Representation ℂ (H × PUnit) (F τ)) (σ τ)
      (1 : Representation ℂ PUnit ℂ) := by
    intro τ
    obtain ⟨ε, h0, hε⟩ := finrank_eq_one_iff'.1 (h τ)
    have h0' : ε.1 ≠ 0 := fun e => h0 (Subtype.ext e)
    refine ⟨ε.1, LinearMap.range_eq_top.1 (Module.Dual.range_eq_top_of_ne_zero h0'), fun k g f v => ?_, fun l hl x hx => ?_⟩
    · exact ε.2 k (f ⊗ₜ v)
    · have hl' : l ∈ invFun ((ρ τ).tprod (σ τ)) := by
        intro k z
        induction z with
        | zero => simp
        | tmul a b => exact hl k a b
        | add a b ha hb => simp only [map_add, ha, hb]
      obtain ⟨c, hc⟩ := hε ⟨l, hl'⟩
      have : c • ε.1 = l := congrArg Subtype.val hc
      rw [← this, LinearMap.smul_apply, hx, smul_zero]
  obtain ⟨π, hs, he, hk⟩ := Contracts.outer hc
  let ε : Module.Dual ℂ _ := (PiTensorProduct.constantBaseRingEquiv ι ℂ).toLinearMap ∘ₗ π
  have hs' : Function.Surjective ε := (PiTensorProduct.constantBaseRingEquiv ι ℂ).surjective.comp hs
  have hε : ε ∈ invFun ((outer ρ).tprod (outer σ)) := by
    intro k z
    induction z with
    | zero => simp
    | tmul a b =>
      have := he k 1 a b
      rw [map_one] at this
      exact congrArg (PiTensorProduct.constantBaseRingEquiv ι ℂ) this
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨z, hz⟩ := hs' 1
  refine finrank_eq_one_iff'.2 ⟨⟨ε, hε⟩, fun e => ?_, fun l => ⟨l.1 z, Subtype.ext (LinearMap.ext fun x => ?_)⟩⟩
  · have : ε = 0 := congrArg Subtype.val e
    rw [this] at hz
    simp at hz
  · have := hk l.1 (fun k f v => l.2 k (f ⊗ₜ v)) (x - ε x • z)
      ((PiTensorProduct.constantBaseRingEquiv ι ℂ).map_eq_zero_iff.1 (by
        change ε _ = 0
        rw [map_sub, map_smul, hz]; simp))
    rw [map_sub, map_smul, sub_eq_zero] at this
    rw [this]
    simp [mul_comm]

def addW {n : ℕ} (lam : DomWeight n) (c : ℤ) : DomWeight n :=
  ⟨fun i => lam.w i + c, fun _ _ h => add_le_add_left (lam.anti h) c⟩

/- English proof (translation)
Consider the cases of `lam`. Consider the cases of `mu`. Reduce the equality to equality of the corresponding arguments. Conclude with `funext h`.
-/
theorem domWeight_ext {n : ℕ} {lam mu : DomWeight n} (h : ∀ i, lam.w i = mu.w i) : lam = mu := by
  cases lam; cases mu
  congr
  exact funext h

/- English proof (translation)
Use `Iso.trans ?_ (GlobalTheory.T.iso_unitaryIrrep_conj_dual n _)` and prove the remaining obligations. Use `Iso.trans ?_ ((GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift n (-α) mu (addW mu (-α)) fun _ => rfl).comp (conjU n))` and prove the remaining obligations. Use `⟨LinearEquiv.refl _ _, fun g x => ?_⟩` and prove the remaining obligations. Establish `: detU n (conjU n g) = (detU n g)⁻¹`. Rewrite using `[← map_inv]`.

Use `ext`. Conclude with `Matrix.det_transpose (star g.1)`. Express the relevant statement in the definitionally equal form `(((detU n ^ α) g : ℂˣ) : ℂ) • irr n mu (conjU n g) x = (((detU n ^ (-α)) (conjU n g) : ℂˣ) : ℂ) • irr n mu (conjU n g) x`. Simplify using `[this]`.
-/
theorem iso_twist_conj (n : ℕ) (α : ℤ) (mu : DomWeight n) :
    Iso (twist (detU n ^ α) ((irr n mu).comp (conjU n))) (irr n (addW mu (-α))).dual := by
  refine Iso.trans ?_ (GlobalTheory.T.iso_unitaryIrrep_conj_dual n _)
  refine Iso.trans ?_ ((GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift n (-α) mu (addW mu (-α)) fun _ => rfl).comp (conjU n))
  refine ⟨LinearEquiv.refl _ _, fun g x => ?_⟩
  have : detU n (conjU n g) = (detU n g)⁻¹ := by
    rw [← map_inv]
    ext
    exact Matrix.det_transpose (star g.1)
  change (((detU n ^ α) g : ℂˣ) : ℂ) • irr n mu (conjU n g) x = (((detU n ^ (-α)) (conjU n g) : ℂˣ) : ℂ) • irr n mu (conjU n g) x
  simp [this]

/- English proof (translation)
Establish `hm : min a b = a` using `min_eq_left hab.le`. Establish `hpos : ∀ i, 0 ≤ lam.w i + α` using `fun i => by`. Establish `h1` using `h ⟨i.1, i.2.trans hab⟩`. Establish `h2` using `h ⟨a, hab⟩`. Establish `h3` using `lam'.anti (show (⟨i.1, i.2.trans hab⟩ : Fin b) ≤ ⟨a, hab⟩ from i.2.le)`.

Simplify using `only [i.2, dite_true, lt_irrefl, dite_false] at h1 h2`. Establish `: lam.w ⟨i.1, i.2⟩ = lam.w i` using `rfl`. Use linear arithmetic over natural numbers and integers. Set `i₀ : GlobalTheory.GLDuality.Part (min a b)` to `⟨fun i => (lam.w (Fin.cast hm i) + α).toNat, fun i j hij => by`. Use `lam.anti (show Fin.cast hm i ≤ Fin.cast hm j from hij)` as an intermediate fact.

Simplify using `only`. Use the proof step `omega⟩`. Establish `ha : addW (GlobalTheory.GLDuality.pad a i₀) (-α) = lam` using `domWeight_ext fun i => by`. Use `hpos i` as an intermediate fact. Establish `e : Fin.cast hm ⟨i.1, by omega⟩ = i` using `rfl`.

Simplify using `only [addW, GlobalTheory.GLDuality.pad_w_of_lt i₀ i (by omega), i₀, e]`. Use linear arithmetic over natural numbers and integers. Use `(GlobalTheory.T.contracts_of_iso_directSum' _ _ _ _ _ _ _ _ _ _ (irr a lam) i₀ (GlobalTheory.T.fockOnePlace_iso_directSum_partitions a b α β) (fun i hi => ?_) ?_).congr (Iso.refl _) (Iso.refl _) (GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift b β _ _ fun i => ?_)` and prove the remaining obligations. Use `((iso_twist_conj a α _).tprod (Iso.refl _)).invFun_eq_bot ?_` and prove the remaining obligations. Take `⟨e⟩` from `GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap _ _ _ (irr a (addW (GlobalTheory.GLDuality.pad a i) (-α))) (irr a lam)`.

Establish `hne : lam ≠ addW (GlobalTheory.GLDuality.pad a i) (-α)` using `fun e' => hi (GlobalTheory.GLDuality.pad_injective (min_le_left a b) (domWeight_ext fun j => by`. Use `congrArg (fun w : DomWeight a => w.w j) (ha.trans e')` as an intermediate fact. Simplify using `only [addW] at this`. Use the proof step `omega))`. Establish `: Subsingleton ((irr a lam).IntertwiningMap (irr a (addW (GlobalTheory.GLDuality.pad a i) (-α))))` using `⟨fun x y => (intertwining_unitary_eq_zero a _ _ hne x).trans (intertwining_unitary_eq_zero a _ _ hne y).symm⟩`.

Rewrite using `[← Submodule.subsingleton_iff_eq_bot]`. Conclude with `e.toEquiv.subsingleton`. Rewrite using `[((iso_twist_conj a α _).tprod (Iso.refl _)).finrank_invFun, ha]`. Take `⟨e⟩` from `GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap _ _ _ (irr a lam) (irr a lam)`. Use `isIrreducible_smallRep_unitary a lam` as an intermediate fact.

Rewrite using `[e.finrank_eq]`. Conclude with `Representation.IsIrreducible.finrank_intertwiningMap_self _`. Rewrite using `[h i] split_ifs with hi`. Use `hpos ⟨i.1, hi⟩` as an intermediate fact. Establish `e : Fin.cast hm ⟨i.1, by omega⟩ = ⟨i.1, hi⟩` using `rfl`.

Simplify using `only [GlobalTheory.GLDuality.pad_w_of_lt i₀ i (by omega), i₀, e]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[GlobalTheory.GLDuality.pad_w_of_le i₀ i (by omega), zero_add]`.
-/
theorem contracts_fockOne {a b : ℕ} (hab : a < b) (α β : ℤ) (lam : DomWeight a) (lam' : DomWeight b)
    (h : StepW α β lam lam') : Contracts (fockOne a b α β) (irr a lam) (irr b lam') := by
  have hm : min a b = a := min_eq_left hab.le
  have hpos : ∀ i, 0 ≤ lam.w i + α := fun i => by
    have h1 := h ⟨i.1, i.2.trans hab⟩
    have h2 := h ⟨a, hab⟩
    have h3 := lam'.anti (show (⟨i.1, i.2.trans hab⟩ : Fin b) ≤ ⟨a, hab⟩ from i.2.le)
    simp only [i.2, dite_true, lt_irrefl, dite_false] at h1 h2
    have : lam.w ⟨i.1, i.2⟩ = lam.w i := rfl
    omega
  let i₀ : GlobalTheory.GLDuality.Part (min a b) := ⟨fun i => (lam.w (Fin.cast hm i) + α).toNat, fun i j hij => by
    have := lam.anti (show Fin.cast hm i ≤ Fin.cast hm j from hij)
    simp only
    omega⟩
  have ha : addW (GlobalTheory.GLDuality.pad a i₀) (-α) = lam := domWeight_ext fun i => by
    have := hpos i
    have e : Fin.cast hm ⟨i.1, by omega⟩ = i := rfl
    simp only [addW, GlobalTheory.GLDuality.pad_w_of_lt i₀ i (by omega), i₀, e]
    omega
  refine (GlobalTheory.T.contracts_of_iso_directSum' _ _ _ _ _ _ _ _ _ _ (irr a lam) i₀ (GlobalTheory.T.fockOnePlace_iso_directSum_partitions a b α β) (fun i hi => ?_) ?_).congr (Iso.refl _) (Iso.refl _)
    (GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift b β _ _ fun i => ?_)
  · refine ((iso_twist_conj a α _).tprod (Iso.refl _)).invFun_eq_bot ?_
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap _ _ _ (irr a (addW (GlobalTheory.GLDuality.pad a i) (-α))) (irr a lam)
    have hne : lam ≠ addW (GlobalTheory.GLDuality.pad a i) (-α) := fun e' => hi (GlobalTheory.GLDuality.pad_injective (min_le_left a b)
      (domWeight_ext fun j => by
        have := congrArg (fun w : DomWeight a => w.w j) (ha.trans e')
        simp only [addW] at this
        omega))
    have : Subsingleton ((irr a lam).IntertwiningMap (irr a (addW (GlobalTheory.GLDuality.pad a i) (-α)))) :=
      ⟨fun x y => (intertwining_unitary_eq_zero a _ _ hne x).trans (intertwining_unitary_eq_zero a _ _ hne y).symm⟩
    rw [← Submodule.subsingleton_iff_eq_bot]
    exact e.toEquiv.subsingleton
  · rw [((iso_twist_conj a α _).tprod (Iso.refl _)).finrank_invFun, ha]
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap _ _ _ (irr a lam) (irr a lam)
    have := isIrreducible_smallRep_unitary a lam
    rw [e.finrank_eq]
    exact Representation.IsIrreducible.finrank_intertwiningMap_self _
  · rw [h i]
    split_ifs with hi
    · have := hpos ⟨i.1, hi⟩
      have e : Fin.cast hm ⟨i.1, by omega⟩ = ⟨i.1, hi⟩ := rfl
      simp only [GlobalTheory.GLDuality.pad_w_of_lt i₀ i (by omega), i₀, e]
      omega
    · rw [GlobalTheory.GLDuality.pad_w_of_le i₀ i (by omega), zero_add]

/- English proof (translation)
Establish `e : lam.dual.dual = lam` using `domWeight_ext fun i => by simp [DomWeight.dual]`. Use `(GlobalTheory.T.iso_unitaryIrrep_conj_dual n lam.dual).symm.trans (GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual n hn lam.dual)` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem iso_dual_dual {n : ℕ} (hn : 0 < n) (lam : DomWeight n) : Iso (irr n lam.dual).dual (irr n lam) := by
  have e : lam.dual.dual = lam := domWeight_ext fun i => by simp [DomWeight.dual]
  have := (GlobalTheory.T.iso_unitaryIrrep_conj_dual n lam.dual).symm.trans (GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual n hn lam.dual)
  rwa [e] at this

/- English proof (translation)
Establish `e : (irr N lam).comp (embed1 h) = resRep (unitaryIncl n) h lam` using `MonoidHom.ext fun g => congrArg (sqRep ℂ N lam) (Units.ext rfl)`. Rewrite using `[e, ((Iso.tprod_comm _ _).trans ((iso_dual_dual hn kap).symm.tprod (Iso.refl _))).finrank_invFun]`. Take `⟨e⟩` from `GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap _ _ _ (irr n kap.dual) (resRep (unitaryIncl n) h lam)`. Rewrite using `[e.finrank_eq]`. Conclude with `(comult_unitary n N h lam kap.dual).1 hI`.
-/
theorem finrank_invFun_branch {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (kap : DomWeight n)
    (hI : Formalism.MainNotions.PrimeDegreeVariant.Interlace h lam kap.dual) :
    Module.finrank ℂ (invFun (Representation.tprod ((irr N lam).comp (embed1 h)) (irr n kap))) = 1 := by
  have e : (irr N lam).comp (embed1 h) = resRep (unitaryIncl n) h lam :=
    MonoidHom.ext fun g => congrArg (sqRep ℂ N lam) (Units.ext rfl)
  rw [e, ((Iso.tprod_comm _ _).trans ((iso_dual_dual hn kap).symm.tprod (Iso.refl _))).finrank_invFun]
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap _ _ _ (irr n kap.dual) (resRep (unitaryIncl n) h lam)
  rw [e.finrank_eq]
  exact (comult_unitary n N h lam kap.dual).1 hI

/- English proof (translation)
Introduce `i`. Take `⟨hl, hI⟩` from `GlobalTheory.T.strictInterlace_ganGrossPrasad_big_small S Q hQ`. Establish `hi : i.1 < Q.smallPar.length` using `by rw [length_small]; exact i.2`. Establish `hi' : i.1 + 1 < Q.bigPar.length` using `by omega`. Take `⟨a1, a2⟩` from `hI i hi hi'`.

Establish `b1` using `hw_small Q i hi`. Establish `b2` using `hw_big Q hQ i (by omega)`. Establish `b3` using `hw_big Q hQ (i + 1) hi'`. Establish `hl' : (Q.bigPar.length : ℚ) = Q.smallPar.length + 1` using `by exact_mod_cast hl`. Rewrite `b2`, `b3` using `[hl']`.

Move the coercions through the operations in `at b3`. Rewrite using `[h1, h1, h2]`. Prove the components needed by the constructor for the conclusion. Establish `: (hw Q.smallPar i : ℚ) < hw Q.bigPar i + 1` using `by linarith`. Establish `: hw Q.smallPar i < hw Q.bigPar i + 1` using `by exact_mod_cast this`.

Conclude with `Int.lt_add_one_iff.1 this`. Establish `: (hw Q.bigPar (i + 1) : ℚ) < hw Q.smallPar i + 1` using `by linarith`. Establish `: hw Q.bigPar (i + 1) < hw Q.smallPar i + 1` using `by exact_mod_cast this`. Conclude with `Int.lt_add_one_iff.1 this`.
-/
theorem interlace_weights (S : Sizes) (Q : Entries S) (hQ : Q.Good) (lam : DomWeight (S.nR S.m)) (mu : DomWeight (S.nC S.m))
    (h1 : ∀ i, lam.w i = hw Q.bigPar i) (h2 : ∀ i, mu.w i = hw Q.smallPar i) :
    Formalism.MainNotions.PrimeDegreeVariant.Interlace S.nC_succ lam mu := by
  intro i
  obtain ⟨hl, hI⟩ := GlobalTheory.T.strictInterlace_ganGrossPrasad_big_small S Q hQ
  have hi : i.1 < Q.smallPar.length := by rw [length_small]; exact i.2
  have hi' : i.1 + 1 < Q.bigPar.length := by omega
  obtain ⟨a1, a2⟩ := hI i hi hi'
  have b1 := hw_small Q i hi
  have b2 := hw_big Q hQ i (by omega)
  have b3 := hw_big Q hQ (i + 1) hi'
  have hl' : (Q.bigPar.length : ℚ) = Q.smallPar.length + 1 := by exact_mod_cast hl
  rw [hl'] at b2 b3
  push_cast at b3
  rw [h1, h1, h2]
  constructor
  · have : (hw Q.smallPar i : ℚ) < hw Q.bigPar i + 1 := by linarith
    have : hw Q.smallPar i < hw Q.bigPar i + 1 := by exact_mod_cast this
    exact Int.lt_add_one_iff.1 this
  · have : (hw Q.bigPar (i + 1) : ℚ) < hw Q.smallPar i + 1 := by linarith
    have : hw Q.bigPar (i + 1) < hw Q.smallPar i + 1 := by exact_mod_cast this
    exact Int.lt_add_one_iff.1 this

/- English proof (translation)
Assemble the required witnesses or components as `⟨LinearEquiv.refl _ _, fun g x => by simp⟩`.
-/
theorem iso_dual_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G) :
    Iso (Representation.dual (ρ.comp f : Representation ℂ H V)) (ρ.dual.comp f : Representation ℂ H _) :=
  ⟨LinearEquiv.refl _ _, fun g x => by simp⟩

/- English proof (translation)
Use `S.k_pos` as an intermediate fact. Unfold `Sizes.nR`. Use linear arithmetic over natural numbers and integers.
-/
theorem nR_pos (S : Sizes) (j : ℕ) : 0 < S.nR j := by
  have := S.k_pos
  unfold Sizes.nR
  omega

/- English proof (translation)
Use `S.k_pos` as an intermediate fact. Use `S.m_pos` as an intermediate fact. Unfold `Sizes.nC`. Use linear arithmetic over natural numbers and integers.
-/
theorem nC_pos (S : Sizes) (j : ℕ) : 0 < S.nC j := by
  have := S.k_pos
  have := S.m_pos
  unfold Sizes.nC
  omega

/- English proof (translation)
Unfold `Sizes.nR`. Rewrite using `[add_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nR_lt (S : Sizes) (j : ℕ) : S.nR j < S.nR (j + 1) := by
  unfold Sizes.nR
  rw [add_mul]
  omega

/- English proof (translation)
Use `S.s_odd.pos` as an intermediate fact. Unfold `Sizes.nC`. Rewrite using `[add_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nC_lt (S : Sizes) (j : ℕ) : S.nC j < S.nC (j + 1) := by
  have := S.s_odd.pos
  unfold Sizes.nC
  rw [add_mul]
  omega

/- English proof (translation)
Introduce `ι _ _ S P hP`. Use `choose lam hl0 hl1 hl using fun τ => GlobalTheory.T.exists_ganGrossPrasad_row_weights S (P τ) (hP τ)`. Use `choose kap hk0 hk1 hk using fun τ => GlobalTheory.T.exists_ganGrossPrasad_column_weights S (P τ) (hP τ)`. Take `⟨p, ps, pe, pk⟩` from `GlobalTheory.T.contracts_tensorProduct_chain S.m (fun j => UG ι (S.nR j)) (fun j => Pol ι (S.nR j.castSucc) (S.nR j.succ)) _ (fun j => fock _ _ (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ))) (fun j => outer fun τ => irr _ (lam τ j) …`. Take `⟨q, qs, qe, qk⟩` from `GlobalTheory.T.contracts_tensorProduct_chain S.m (fun j => UG ι (S.nC j)) (fun j => Pol ι (S.nC j.castSucc) (S.nC j.succ)) _ (fun i => fock _ _ (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ))) (fun j => outer fun …`.

Establish `i1` using `(GlobalTheory.T.outer_irr_iso_weylRep_of_pos ι _ (nR_pos S _) (psiWt P) (fun τ => lam τ 0) hl0).symm`. Establish `i2` using `((GlobalTheory.T.outer_irr_iso_weylRep_of_pos ι _ (nC_pos S _) (baseWt P) (fun τ => (kap τ 0).dual) hk0).symm.dual.trans (GlobalTheory.T.iso_dual_outer_outer_dual ι _ _ _)).trans (Iso.outer fun τ => iso_dual_dual (nC_pos S _) (kap τ 0))`. Set `c` to `(outer fun τ => irr _ (lam τ 0)).comp ((Pi.evalMonoidHom _ 0).comp (rowComp (ι := ι) S))`. Set `d` to `(outer fun τ => irr _ (kap τ 0)).comp ((Pi.evalMonoidHom (fun i : Fin (S.m + 1) => UG ι (S.nC i)) 0).comp (MonoidHom.snd (∀ j : Fin S.m, UG ι (S.nR j)) _))`. Establish `j1 : Iso (psiRep P) c` using `i1.comp _`.

Establish `j2 : Iso (baseRep P).dual d` using `(iso_dual_comp _ _).trans (i2.comp _)`. Set `r : Gc ι S →* UG ι (S.nC S.m)` to `(Pi.evalMonoidHom (fun i : Fin (S.m + 1) => UG ι (S.nC i)) (Fin.last _)).comp (MonoidHom.snd _ _)`. Set `x` to `outer fun τ => (irr (S.nR S.m) (lam τ (Fin.last _))).comp (embed1 S.nC_succ)`. Set `y` to `outer fun τ => irr (S.nC S.m) (kap τ (Fin.last _))`. Establish `hlast : ∀ g : Gc ι S, rowComp S g (Fin.last _) = embed S.nC_succ (g.2 (Fin.last _))` using `fun g => Fin.snoc_last (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _`.

Establish `h1 : Module.finrank ℂ (invFun (omRep P)) = Module.finrank ℂ (invFun ((piTprod (rowFock P)).tprod ((piTprod (colFock P)).tprod (Representation.tprod c d))))` using `((Iso.refl _).tprod ((Iso.refl _).tprod (j1.tprod j2))).finrank_invFun`. Establish `h2` using `GlobalTheory.T.tensor_representation_intertwiner_compat (Gc ι S) _ _ _ _ _ _ (piTprod (rowFock P)) (piTprod (colFock P)) c d (x.comp r) (y.comp r) p q ps qs (fun g u w => (pe (rowComp S g) u w).trans (by rw [hlast]; rfl)) (fun g u w => qe g.2 u w) (fun l hl => pk l fun g hg u w = …`. Establish `e : rowComp S ((fun j => g j.castSucc, 1) : Gc ι S) = g`. Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations.

Rewrite using `[hlast, hg]`. Conclude with `map_one _`. Conclude with `Fin.snoc_castSucc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _ _`. Use `hl (fun j => g j.castSucc, 1) ((piTprod (colFock P)).map_one) (d.map_one) u w` as an intermediate fact. Rewrite using `[← e]`.

Conclude with `this)`. Use the proof step `(fun l hl => qk l fun g hg u w => by`. Establish `e : rowComp S ((1, g) : Gc ι S) = rowComp S 1`. Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations.

Rewrite using `[hlast, hlast]`. Conclude with `congrArg _ hg`. Conclude with `(Fin.snoc_castSucc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _ _).trans (Fin.snoc_castSucc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _ _).symm`. Use `hl (1, g) (Eq.trans ?_ (piTprod (rowFock P)).map_one) (Eq.trans ?_ c.map_one) u w` and prove the remaining obligations. Rewrite using `[piTprod_apply, piTprod_apply]`.

Use `congrArg _ (funext fun j => ?_)` and prove the remaining obligations. Simplify using `only [rowFock, MonoidHom.comp_apply, e]`. Simplify using `only [c, MonoidHom.comp_apply, e])`. Establish `h3 : invFun (Representation.tprod (x.comp r) (y.comp r)) = invFun (Representation.tprod x y)`. Use extensionality with `l`.

Use `⟨fun h g z => ?_, fun h g z => h (r g) z⟩` and prove the remaining obligations. Use `h (1, Function.update 1 (Fin.last _) g) z` as an intermediate fact. Establish `e : r (1, Function.update 1 (Fin.last _) g) = g` using `Function.update_self _ _ _`. Rewrite using `[← e]`. Conclude with `this`.

Rewrite using `[h1, h2, h3]`. Conclude with `finrank_invFun_outer _ _ fun τ => finrank_invFun_branch S.nC_succ (nC_pos S _) _ _ (interlace_weights S (P τ) (hP τ) _ _ (hl1 τ) (hk1 τ))`.
-/
theorem oneLine : OneLine := by
  intro ι _ _ S P hP
  choose lam hl0 hl1 hl using fun τ => GlobalTheory.T.exists_ganGrossPrasad_row_weights S (P τ) (hP τ)
  choose kap hk0 hk1 hk using fun τ => GlobalTheory.T.exists_ganGrossPrasad_column_weights S (P τ) (hP τ)
  obtain ⟨p, ps, pe, pk⟩ := GlobalTheory.T.contracts_tensorProduct_chain S.m (fun j => UG ι (S.nR j)) (fun j => Pol ι (S.nR j.castSucc) (S.nR j.succ)) _
    (fun j => fock _ _ (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ)))
    (fun j => outer fun τ => irr _ (lam τ j)) fun j =>
      (Contracts.outer fun τ => contracts_fockOne (nR_lt S j) _ _ _ _ (hl τ j)).congr (GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock ι _ _ _ _) (Iso.refl _) (Iso.refl _)
  obtain ⟨q, qs, qe, qk⟩ := GlobalTheory.T.contracts_tensorProduct_chain S.m (fun j => UG ι (S.nC j)) (fun j => Pol ι (S.nC j.castSucc) (S.nC j.succ)) _
    (fun i => fock _ _ (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ))
      (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)))
    (fun j => outer fun τ => irr _ (kap τ j)) fun j =>
      (Contracts.outer fun τ => contracts_fockOne (nC_lt S j) _ _ _ _ (hk τ j)).congr (GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock ι _ _ _ _) (Iso.refl _) (Iso.refl _)
  have i1 := (GlobalTheory.T.outer_irr_iso_weylRep_of_pos ι _ (nR_pos S _) (psiWt P) (fun τ => lam τ 0) hl0).symm
  have i2 := ((GlobalTheory.T.outer_irr_iso_weylRep_of_pos ι _ (nC_pos S _) (baseWt P) (fun τ => (kap τ 0).dual) hk0).symm.dual.trans
    (GlobalTheory.T.iso_dual_outer_outer_dual ι _ _ _)).trans (Iso.outer fun τ => iso_dual_dual (nC_pos S _) (kap τ 0))
  let c := (outer fun τ => irr _ (lam τ 0)).comp ((Pi.evalMonoidHom _ 0).comp (rowComp (ι := ι) S))
  let d := (outer fun τ => irr _ (kap τ 0)).comp
    ((Pi.evalMonoidHom (fun i : Fin (S.m + 1) => UG ι (S.nC i)) 0).comp (MonoidHom.snd (∀ j : Fin S.m, UG ι (S.nR j)) _))
  have j1 : Iso (psiRep P) c := i1.comp _
  have j2 : Iso (baseRep P).dual d := (iso_dual_comp _ _).trans (i2.comp _)
  let r : Gc ι S →* UG ι (S.nC S.m) :=
    (Pi.evalMonoidHom (fun i : Fin (S.m + 1) => UG ι (S.nC i)) (Fin.last _)).comp (MonoidHom.snd _ _)
  let x := outer fun τ => (irr (S.nR S.m) (lam τ (Fin.last _))).comp (embed1 S.nC_succ)
  let y := outer fun τ => irr (S.nC S.m) (kap τ (Fin.last _))
  have hlast : ∀ g : Gc ι S, rowComp S g (Fin.last _) = embed S.nC_succ (g.2 (Fin.last _)) := fun g =>
    Fin.snoc_last (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _
  have h1 : Module.finrank ℂ (invFun (omRep P)) =
      Module.finrank ℂ (invFun ((piTprod (rowFock P)).tprod ((piTprod (colFock P)).tprod (Representation.tprod c d)))) :=
    ((Iso.refl _).tprod ((Iso.refl _).tprod (j1.tprod j2))).finrank_invFun
  have h2 := GlobalTheory.T.tensor_representation_intertwiner_compat (Gc ι S) _ _ _ _ _ _ (piTprod (rowFock P)) (piTprod (colFock P)) c d (x.comp r) (y.comp r) p q ps qs
    (fun g u w => (pe (rowComp S g) u w).trans (by rw [hlast]; rfl)) (fun g u w => qe g.2 u w)
    (fun l hl => pk l fun g hg u w => by
      have e : rowComp S ((fun j => g j.castSucc, 1) : Gc ι S) = g := by
        funext j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [hlast, hg]; exact map_one _
        · exact Fin.snoc_castSucc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _ _
      have := hl (fun j => g j.castSucc, 1) ((piTprod (colFock P)).map_one) (d.map_one) u w
      rw [← e]
      exact this)
    (fun l hl => qk l fun g hg u w => by
      have e : rowComp S ((1, g) : Gc ι S) = rowComp S 1 := by
        funext j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [hlast, hlast]; exact congrArg _ hg
        · exact (Fin.snoc_castSucc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _ _).trans
            (Fin.snoc_castSucc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) _ _ _).symm
      refine hl (1, g) (Eq.trans ?_ (piTprod (rowFock P)).map_one) (Eq.trans ?_ c.map_one) u w
      · rw [piTprod_apply, piTprod_apply]
        refine congrArg _ (funext fun j => ?_)
        simp only [rowFock, MonoidHom.comp_apply, e]
      · simp only [c, MonoidHom.comp_apply, e])
  have h3 : invFun (Representation.tprod (x.comp r) (y.comp r)) = invFun (Representation.tprod x y) := by
    ext l
    refine ⟨fun h g z => ?_, fun h g z => h (r g) z⟩
    have := h (1, Function.update 1 (Fin.last _) g) z
    have e : r (1, Function.update 1 (Fin.last _) g) = g := Function.update_self _ _ _
    rw [← e]
    exact this
  rw [h1, h2, h3]
  exact finrank_invFun_outer _ _ fun τ => finrank_invFun_branch S.nC_succ (nC_pos S _) _ _
    (interlace_weights S (P τ) (hP τ) _ _ (hl1 τ) (hk1 τ))

end GlobalTheory.OneFunctional
