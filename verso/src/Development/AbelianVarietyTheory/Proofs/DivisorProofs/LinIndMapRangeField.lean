import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.SatakeDualWeyl.DualWeylRepApply
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.LatBC

section Comp

variable {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) (N : ℕ)

def dwMap (ν : Fin N → ℕ) : dualWeyl O N N ν →ₛₗ[φ] dualWeyl K N N ν where
  toFun x := ⟨MvPolynomial.map φ (x : MvPolynomial (Fin N × Fin N) O), dualWeylMap O K φ N N ν _ x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp [smul_eq_C_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem dwMap_coe (ν : Fin N → ℕ) (x : dualWeyl O N N ν) :
    ((dwMap φ N ν x : dualWeyl K N N ν) : MvPolynomial (Fin N × Fin N) K) =
      MvPolynomial.map φ (x : MvPolynomial (Fin N × Fin N) O) := rfl

end Comp

section Tensor

variable {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ)

def bc : NablaT O N lam →ₛₗ[φ] NablaT K N lam :=
  letI : Module O (NablaT K N lam) := Module.compHom _ φ
  let f : MultilinearMap O (fun τ => dualWeyl O N N (res N (lam τ))) (NablaT K N lam) :=
    { toFun := fun m => PiTensorProduct.tprod K fun τ => dwMap φ N _ (m τ)
      map_update_add' := fun m i x y => by
        have hu : ∀ z, (fun τ => dwMap φ N (res N (lam τ)) (Function.update m i z τ)) =
            Function.update (fun τ => dwMap φ N (res N (lam τ)) (m τ)) i (dwMap φ N _ z) :=
          fun z => funext fun τ => Function.apply_update (fun τ => dwMap φ N (res N (lam τ))) m i z τ
        simp only [hu, map_add, MultilinearMap.map_update_add]
      map_update_smul' := fun m i c x => by
        have hu : ∀ z, (fun τ => dwMap φ N (res N (lam τ)) (Function.update m i z τ)) =
            Function.update (fun τ => dwMap φ N (res N (lam τ)) (m τ)) i (dwMap φ N _ z) :=
          fun z => funext fun τ => Function.apply_update (fun τ => dwMap φ N (res N (lam τ))) m i z τ
        simp only [hu, LinearMap.map_smulₛₗ, MultilinearMap.map_update_smul]
        rfl }
  { toFun := PiTensorProduct.lift f
    map_add' := fun x y => map_add _ x y
    map_smul' := fun c x => (PiTensorProduct.lift f).map_smul c x }

/- English proof (translation)
Use `letI : Module O (NablaT K N lam) := Module.compHom _ φ`. Conclude with `PiTensorProduct.lift.tprod m`.
-/
theorem bc_tprod (m : ∀ τ, dualWeyl O N N (res N (lam τ))) :
    bc φ N lam (PiTensorProduct.tprod O m) = PiTensorProduct.tprod K fun τ => dwMap φ N _ (m τ) := by
  letI : Module O (NablaT K N lam) := Module.compHom _ φ
  exact PiTensorProduct.lift.tprod m

end Tensor

end GlobalTheory.LatBC

namespace GlobalTheory.LatBC

section Bases

/- English proof (translation)
Rewrite `hv`, the goal using `[linearIndependent_iff']`. Introduce `s c hsum i hi`. Set `B` to `Module.Free.chooseBasis F K`. Apply `B.ext_elem` to reduce the goal to its premises. Introduce `j`.

Establish `key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0`. Use extensionality with `m`. Establish `h1` using `congrArg (fun z => z m) hsum`. Simplify using `only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h1 ⊢`. Establish `h2` using `congrArg (fun x => B.repr x j) h1`.

Simplify using `only [map_sum, map_zero, Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]`. Use `hv s (fun i => B.repr (c i) j) key i hi` as an intermediate fact.

Simplify using `using this`.
-/
theorem linInd_mapRange_field {F K P ι : Type} [Field F] [Field K] [Algebra F K] {v : ι → P →₀ F}
    (hv : LinearIndependent F v) :
    LinearIndependent K (fun i => Finsupp.mapRange (algebraMap F K) (map_zero _) (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (fun z => z m) hsum
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply] at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    simp only [map_sum, map_zero, Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

/- English proof (translation)
Use `letI : Algebra (FractionRing O) K := (IsFractionRing.lift hφ).toAlgebra`. Set `Lq : (P →₀ O) →ₗ[O] (P →₀ FractionRing O)` to `Finsupp.mapRange.linearMap (Algebra.linearMap O (FractionRing O))`. Establish `h1 : LinearIndependent O fun a => Lq (y a)` using `hy.map' Lq (LinearMap.ker_eq_bot.2 fun a b hab => Finsupp.ext fun p => IsFractionRing.injective O (FractionRing O) (by simpa [Lq] using congrArg (fun z => z p) hab))`. Establish `h2 : LinearIndependent (FractionRing O) fun a => Lq (y a)` using `(LinearIndependent.iff_fractionRing O (FractionRing O)).mp h1`. Establish `h3` using `linInd_mapRange_field (K := K) h2`.

Use `h3 using 2 with a` and compare the differences between its conclusion and the goal. Use extensionality with `p`. Simplify using `[Lq, RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]`.
-/
theorem linInd_mapRange {O K P : Type} [CommRing O] [IsDomain O] [Field K] (φ : O →+* K)
    (hφ : Function.Injective φ) {n : ℕ} {y : Fin n → P →₀ O} (hy : LinearIndependent O y) :
    LinearIndependent K (fun a => Finsupp.mapRange φ φ.map_zero (y a)) := by
  classical
  letI : Algebra (FractionRing O) K := (IsFractionRing.lift hφ).toAlgebra
  let Lq : (P →₀ O) →ₗ[O] (P →₀ FractionRing O) := Finsupp.mapRange.linearMap (Algebra.linearMap O (FractionRing O))
  have h1 : LinearIndependent O fun a => Lq (y a) :=
    hy.map' Lq (LinearMap.ker_eq_bot.2 fun a b hab => Finsupp.ext fun p =>
      IsFractionRing.injective O (FractionRing O) (by simpa [Lq] using congrArg (fun z => z p) hab))
  have h2 : LinearIndependent (FractionRing O) fun a => Lq (y a) :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp h1
  have h3 := linInd_mapRange_field (K := K) h2
  convert h3 using 2 with a
  ext p
  simp [Lq, RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]

/- English proof (translation)
Set `g : M →ₛₗ[φ] (P →₀ K)` to `{ toFun := fun x => Finsupp.mapRange φ φ.map_zero (BO.repr x) map_add' := fun x y => by`. Rewrite using `[map_add]`. Conclude with `Finsupp.mapRange_add (fun a b => map_add φ a b) _ _`. Use the proof step `map_smul' := fun c x => by`. Use extensionality with `p`.

Simplify using `}`. Establish `: (BK.repr.toLinearMap.comp f : M →ₛₗ[φ] (P →₀ K)) = g`. Use `BO.ext fun p => ?_` and prove the remaining obligations. Simplify using `[g, h]`. Conclude with `congrArg (fun F : M →ₛₗ[φ] (P →₀ K) => F x) this`.
-/
theorem repr_of_basis {O K M M' P : Type} [CommRing O] [Field K] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module K M'] (φ : O →+* K) (f : M →ₛₗ[φ] M') (BO : Module.Basis P O M)
    (BK : Module.Basis P K M') (h : ∀ p, f (BO p) = BK p) (x : M) :
    BK.repr (f x) = Finsupp.mapRange φ φ.map_zero (BO.repr x) := by
  classical
  let g : M →ₛₗ[φ] (P →₀ K) :=
    { toFun := fun x => Finsupp.mapRange φ φ.map_zero (BO.repr x)
      map_add' := fun x y => by
        rw [map_add]; exact Finsupp.mapRange_add (fun a b => map_add φ a b) _ _
      map_smul' := fun c x => by
        ext p; simp }
  have : (BK.repr.toLinearMap.comp f : M →ₛₗ[φ] (P →₀ K)) = g := by
    refine BO.ext fun p => ?_
    simp [g, h]
  exact congrArg (fun F : M →ₛₗ[φ] (P →₀ K) => F x) this

/- English proof (translation)
Use `⟨fun x y hxy => ?_, fun n x hx => ?_, ?_⟩` and prove the remaining obligations. Apply `BO.repr.injective` to reduce the goal to its premises. Use extensionality with `p`. Use `congrArg (fun z => BK.repr z p) hxy` as an intermediate fact. Simplify using `only [repr_of_basis φ f BO BK h, Finsupp.mapRange_apply] at this`.

Conclude with `hφ this`. Establish `h1 : LinearIndependent O fun a => BO.repr (x a)` using `hx.map' BO.repr.toLinearMap (LinearMap.ker_eq_bot.2 BO.repr.injective)`. Establish `h2` using `linInd_mapRange φ hφ h1`. Establish `h3` using `h2.map' BK.repr.symm.toLinearMap (LinearMap.ker_eq_bot.2 BK.repr.symm.injective)`. Establish `e : (fun a => f (x a)) = BK.repr.symm.toLinearMap ∘ fun a => Finsupp.mapRange φ φ.map_zero (BO.repr (x a))`.

Use function extensionality and compare the values at `a`. Simplify using `[← repr_of_basis φ f BO BK h]`. Rewrite using `[e]`. Conclude with `h3`. Rewrite using `[eq_top_iff, ← BK.span_eq]`.

Conclude with `Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨BO p, h p⟩)`.
-/
theorem of_basis {O K M M' P : Type} [CommRing O] [IsDomain O] [Field K] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module K M'] (φ : O →+* K) (hφ : Function.Injective φ) (f : M →ₛₗ[φ] M')
    (BO : Module.Basis P O M) (BK : Module.Basis P K M') (h : ∀ p, f (BO p) = BK p) :
    Function.Injective f ∧
      (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent K fun a => f (x a)) ∧
      Submodule.span K (Set.range f) = ⊤ := by
  refine ⟨fun x y hxy => ?_, fun n x hx => ?_, ?_⟩
  · apply BO.repr.injective
    ext p
    have := congrArg (fun z => BK.repr z p) hxy
    simp only [repr_of_basis φ f BO BK h, Finsupp.mapRange_apply] at this
    exact hφ this
  · have h1 : LinearIndependent O fun a => BO.repr (x a) :=
      hx.map' BO.repr.toLinearMap (LinearMap.ker_eq_bot.2 BO.repr.injective)
    have h2 := linInd_mapRange φ hφ h1
    have h3 := h2.map' BK.repr.symm.toLinearMap (LinearMap.ker_eq_bot.2 BK.repr.symm.injective)
    have e : (fun a => f (x a)) = BK.repr.symm.toLinearMap ∘ fun a => Finsupp.mapRange φ φ.map_zero (BO.repr (x a)) := by
      funext a
      simp [← repr_of_basis φ f BO BK h]
    rw [e]
    exact h3
  · rw [eq_top_iff, ← BK.span_eq]
    exact Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨BO p, h p⟩)

variable {O K : Type} [CommRing O] [IsDomain O] [Field K] (φ : O →+* K) (N : ℕ)

/- English proof (translation)
Use `letI : Algebra O K := φ.toAlgebra`. Take `⟨b, hb, -⟩` from `sSBasis O N N ν`. Establish `hK` using `Formalism.GradedWeylDivisibility.ldlat_linInd_base (K := K) hφ hb.1`. Establish `hsK` using `Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl (K := K) hb`. Set `BO` to `(Module.Basis.span hb.1).map (LinearEquiv.ofEq _ _ hb.2.1)`.

Set `BK` to `(Module.Basis.span hK).map (LinearEquiv.ofEq _ _ hsK)`. Use `⟨ssIdx N N ν, (sSIdxFinite N N ν).to_subtype, BO, BK, fun p => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[BO, BK, Module.Basis.span_apply]`. Both sides reduce to the same expression.
-/
theorem exists_bases (hφ : Function.Injective φ) (ν : Fin N → ℕ) :
    ∃ (P : Type) (_ : Finite P) (BO : Module.Basis P O (dualWeyl O N N ν))
      (BK : Module.Basis P K (dualWeyl K N N ν)), ∀ p, dwMap φ N ν (BO p) = BK p := by
  letI : Algebra O K := φ.toAlgebra
  obtain ⟨b, hb, -⟩ := sSBasis O N N ν
  have hK := Formalism.GradedWeylDivisibility.ldlat_linInd_base (K := K) hφ hb.1
  have hsK := Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl (K := K) hb
  let BO := (Module.Basis.span hb.1).map (LinearEquiv.ofEq _ _ hb.2.1)
  let BK := (Module.Basis.span hK).map (LinearEquiv.ofEq _ _ hsK)
  refine ⟨ssIdx N N ν, (sSIdxFinite N N ν).to_subtype, BO, BK, fun p => ?_⟩
  apply Subtype.ext
  simp [BO, BK, Module.Basis.span_apply]
  rfl

end Bases

end GlobalTheory.LatBC

namespace GlobalTheory.LatBC

section Main

/- English proof (translation)
Use `choose P hP BO BK h using fun τ => exists_bases φ N hφ (res N (lam τ))`. Use `of_basis φ hφ (bc φ N lam) (Basis.piTensorProduct BO) (Basis.piTensorProduct BK) fun p => ?_` and prove the remaining obligations. Rewrite using `[Basis.piTensorProduct_apply, Basis.piTensorProduct_apply, bc_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `τ`.

Conclude with `h τ (p τ)`.
-/
theorem bc_props {O K : Type} [CommRing O] [IsDomain O] [Field K] (φ : O →+* K) (N : ℕ) {ι : Type} [Fintype ι]
    (lam : ι → ℕ → ℕ) (hφ : Function.Injective φ) :
    Function.Injective (bc φ N lam) ∧
      (∀ (n : ℕ) (x : Fin n → NablaT O N lam), LinearIndependent O x →
        LinearIndependent K fun a => bc φ N lam (x a)) ∧
      Submodule.span K (Set.range (bc φ N lam)) = ⊤ := by
  choose P hP BO BK h using fun τ => exists_bases φ N hφ (res N (lam τ))
  refine of_basis φ hφ (bc φ N lam) (Basis.piTensorProduct BO) (Basis.piTensorProduct BK) fun p => ?_
  rw [Basis.piTensorProduct_apply, Basis.piTensorProduct_apply, bc_tprod]
  congr 1
  funext τ
  exact h τ (p τ)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, x, hx, rfl⟩` from `hy`.

Use `choose x0 hx0 hmap using hx`. Use `⟨c • PiTensorProduct.tprod F.O (fun τ => (⟨x0 τ, hx0 τ⟩ : dualWeyl F.O N N (res N (lam τ)))), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, bc_tprod]`. Use `congr 2`. Use function extensionality and compare the values at `τ`.

Conclude with `Subtype.ext (hmap τ)`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨x, rfl⟩` from `ha`. Take `⟨z, rfl⟩` from `hb`.

Conclude with `⟨x + z, map_add _ _ _⟩`. Consider the case `neg a _ ha`. Take `⟨x, rfl⟩` from `ha`. Conclude with `⟨-x, map_neg _ _⟩`. Introduce and unpack `⟨x, rfl⟩`.

Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r m`. Rewrite using `[LinearMap.map_smulₛₗ, bc_tprod]`. Conclude with `AddSubgroup.subset_closure ⟨r, fun τ => dwMap F.emb N _ (m τ), fun τ => ⟨m τ, (m τ).2, rfl⟩, rfl⟩`. Consider the case `add a b ha hb`.

Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.
-/
theorem latN_iff {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : GlobalTheory.ExpFrame.Frame l ι N)
    (lam : ι → ℕ → ℕ) (y : NablaT (PadicAlgCl l) N lam) :
    y ∈ F.latN lam ↔ ∃ x, bc F.emb N lam x = y := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, x, hx, rfl⟩ := hy
      choose x0 hx0 hmap using hx
      refine ⟨c • PiTensorProduct.tprod F.O (fun τ => (⟨x0 τ, hx0 τ⟩ : dualWeyl F.O N N (res N (lam τ)))), ?_⟩
      rw [LinearMap.map_smulₛₗ, bc_tprod]
      congr 2
      funext τ
      exact Subtype.ext (hmap τ)
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨z, rfl⟩ := hb
      exact ⟨x + z, map_add _ _ _⟩
    | neg a _ ha =>
      obtain ⟨x, rfl⟩ := ha
      exact ⟨-x, map_neg _ _⟩
  · rintro ⟨x, rfl⟩
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      rw [LinearMap.map_smulₛₗ, bc_tprod]
      exact AddSubgroup.subset_closure ⟨r, fun τ => dwMap F.emb N _ (m τ), fun τ => ⟨m τ, (m τ).2, rfl⟩, rfl⟩
    | add a b ha hb =>
      rw [map_add]
      exact add_mem ha hb

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, x, hx, rfl⟩` from `hy`.

Use `choose x0 hx0 hmap using hx`. Establish `hd : ∀ τ, x0 τ ∈ dualWeyl F.O N N (res N (lam τ))` using `fun τ => weylLeDual F.O N N le_rfl _ (hlam τ) (hx0 τ)`. Set `w : ∀ τ, deltaIn F.O N lam τ` to `fun τ => ⟨⟨x0 τ, hd τ⟩, hx0 τ⟩`. Use `⟨c • PiTensorProduct.tprod F.O (fun τ => (w τ : dualWeyl F.O N N (res N (lam τ)))), ⟨c • PiTensorProduct.tprod F.O w, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, PiTensorProduct.map_tprod]`.

Both sides reduce to the same expression. Rewrite using `[LinearMap.map_smulₛₗ, bc_tprod]`. Use `congr 2`. Use function extensionality and compare the values at `τ`. Conclude with `Subtype.ext (hmap τ)`.

Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨x, hx, rfl⟩` from `ha`. Take `⟨z, hz, rfl⟩` from `hb`. Conclude with `⟨x + z, add_mem hx hz, map_add _ _ _⟩`.

Consider the case `neg a _ ha`. Take `⟨x, hx, rfl⟩` from `ha`. Conclude with `⟨-x, neg_mem hx, map_neg _ _⟩`. Introduce and unpack `⟨x, ⟨z, rfl⟩, rfl⟩`. Proceed by induction on `z using PiTensorProduct.induction_on with`.

Consider the case `smul_tprod r m`. Rewrite using `[LinearMap.map_smul, PiTensorProduct.map_tprod, LinearMap.map_smulₛₗ, bc_tprod]`. Conclude with `AddSubgroup.subset_closure ⟨r, fun τ => dwMap F.emb N _ (m τ), fun τ => ⟨((m τ : dualWeyl F.O N N (res N (lam τ))) : MvPolynomial (Fin N × Fin N) F.O), (m τ).2, rfl⟩, rfl⟩`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`.

Conclude with `add_mem ha hb`.
-/
theorem latD_iff {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : GlobalTheory.ExpFrame.Frame l ι N)
    (lam : ι → ℕ → ℕ) (hlam : ∀ τ, Antitone (res N (lam τ))) (y : NablaT (PadicAlgCl l) N lam) :
    y ∈ F.latD lam ↔ ∃ x ∈ tensSub (deltaIn F.O N lam), bc F.emb N lam x = y := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, x, hx, rfl⟩ := hy
      choose x0 hx0 hmap using hx
      have hd : ∀ τ, x0 τ ∈ dualWeyl F.O N N (res N (lam τ)) :=
        fun τ => weylLeDual F.O N N le_rfl _ (hlam τ) (hx0 τ)
      let w : ∀ τ, deltaIn F.O N lam τ := fun τ => ⟨⟨x0 τ, hd τ⟩, hx0 τ⟩
      refine ⟨c • PiTensorProduct.tprod F.O (fun τ => (w τ : dualWeyl F.O N N (res N (lam τ)))), ⟨c • PiTensorProduct.tprod F.O w, ?_⟩, ?_⟩
      · rw [LinearMap.map_smul, PiTensorProduct.map_tprod]
        rfl
      · rw [LinearMap.map_smulₛₗ, bc_tprod]
        congr 2
        funext τ
        exact Subtype.ext (hmap τ)
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨z, hz, rfl⟩ := hb
      exact ⟨x + z, add_mem hx hz, map_add _ _ _⟩
    | neg a _ ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨-x, neg_mem hx, map_neg _ _⟩
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      rw [LinearMap.map_smul, PiTensorProduct.map_tprod, LinearMap.map_smulₛₗ, bc_tprod]
      exact AddSubgroup.subset_closure ⟨r, fun τ => dwMap F.emb N _ (m τ),
        fun τ => ⟨((m τ : dualWeyl F.O N N (res N (lam τ))) : MvPolynomial (Fin N × Fin N) F.O), (m τ).2, rfl⟩, rfl⟩
    | add a b ha hb =>
      rw [map_add, map_add]
      exact add_mem ha hb

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, map_mul, map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `[rowAct, map_sum, Matrix.map_apply]`.
-/
theorem rowAct_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R M f) = rowAct S (M.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum, Matrix.map_apply]

/- English proof (translation)
Simplify using `only [Formalism.UG.dwAct, rowAct_map]`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem dwAct_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n : ℕ) (g : GL (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (Formalism.UG.dwAct R r n g f) =
      Formalism.UG.dwAct S r n (Matrix.GeneralLinearGroup.map φ g) (MvPolynomial.map φ f) := by
  simp only [Formalism.UG.dwAct, rowAct_map]
  rw [← map_inv]
  rfl

/- English proof (translation)
Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r m`. Rewrite using `[LinearMap.map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.map_smul]`. Use `congr 1`. Establish `h1` using `(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (lam τ)) g m).1`.

Establish `h2` using `(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product K ι (fun _ => N) (fun _ => N) (fun τ => res N (lam τ)) (fun τ => Matrix.GeneralLinearGroup.map φ (g τ)) (fun τ => dwMap φ N _ (m τ))).1`. Simplify using `only [GlobalTheory.ExpFrame.grp]`. Rewrite using `[h1, bc_tprod, bc_tprod, h2]`. Use `congr 1`. Use function extensionality and compare the values at `τ`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Formalism.UG.dualWeylRep_apply, dwMap_coe, dwAct_map]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem bc_grp {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) (N : ℕ) {ι : Type} [DecidableEq ι]
    (lam : ι → ℕ → ℕ) (g : ι → GL (Fin N) O) (x : NablaT O N lam) :
    bc φ N lam (GlobalTheory.ExpFrame.grp O N lam g x) =
      GlobalTheory.ExpFrame.grp K N lam (fun τ => Matrix.GeneralLinearGroup.map φ (g τ)) (bc φ N lam x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.map_smul]
    congr 1
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (lam τ)) g m).1
    have h2 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product K ι (fun _ => N) (fun _ => N) (fun τ => res N (lam τ))
      (fun τ => Matrix.GeneralLinearGroup.map φ (g τ)) (fun τ => dwMap φ N _ (m τ))).1
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1, bc_tprod, bc_tprod, h2]
    congr 1
    funext τ
    apply Subtype.ext
    simp only [Formalism.UG.dualWeylRep_apply, dwMap_coe, dwAct_map]
  | add a b ha hb => simp only [map_add, ha, hb]

end Main

end GlobalTheory.LatBC

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal in

/- English proof (translation)
Introduce `l _ ι _ _ N F lam hinj hlam`. Take `⟨h1, h5, h6⟩` from `GlobalTheory.LatBC.bc_props F.emb N lam hinj`. Conclude with `⟨GlobalTheory.LatBC.bc F.emb N lam, h1, GlobalTheory.LatBC.latN_iff F lam, GlobalTheory.LatBC.latD_iff F lam hlam, GlobalTheory.LatBC.bc_grp F.emb N lam, h5, h6⟩`.
-/
theorem GlobalTheory.LatBC.baseChange_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), Function.Injective F.emb → (∀ τ, Antitone (res N (lam τ))) → ∃ b : NablaT F.O N lam →ₛₗ[F.emb] NablaT (PadicAlgCl l) N lam, Function.Injective b ∧ (∀ y, y ∈ F.latN lam ↔ ∃ x, b x = y) ∧ (∀ y, y ∈ F.latD lam ↔ ∃ x ∈ tensSub (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn F.O N lam), b x = y) ∧ (∀ g x, b (grp F.O N lam g x) = grp (PadicAlgCl l) N lam (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x)) ∧ (∀ (n : ℕ) (x : Fin n → NablaT F.O N lam), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) ∧ Submodule.span (PadicAlgCl l) (Set.range b) = ⊤ := by
  intro l _ ι _ _ N F lam hinj hlam
  obtain ⟨h1, h5, h6⟩ := GlobalTheory.LatBC.bc_props F.emb N lam hinj
  exact ⟨GlobalTheory.LatBC.bc F.emb N lam, h1, GlobalTheory.LatBC.latN_iff F lam, GlobalTheory.LatBC.latD_iff F lam hlam,
    GlobalTheory.LatBC.bc_grp F.emb N lam, h5, h6⟩
