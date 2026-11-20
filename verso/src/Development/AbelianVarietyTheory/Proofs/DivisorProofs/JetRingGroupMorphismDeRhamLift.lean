import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open TensorProduct

namespace GlobalTheory.LatJet.JetFil

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
  {J : JetRing R I n} {X : Obj F 𝔠 (Sp R)}
  {m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))}

/- English proof (translation)
Use `LinearMap.ext fun c ↦ ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hm.2 c`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]`.
-/
theorem crys_ext (hm : m.IsBC) {d₁ d₂ : Crys J.κ (spMap J.π) X.A} (h : ∀ c, d₁ (m.pull c) = d₂ (m.pull c)) :
    d₁ = d₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

/- English proof (translation)
The claim follows from `(hm.corr_iff.2 rfl : m.Corr h (hm.bcMap h)) c`.
-/
theorem bcMap_apply (hm : m.IsBC) (h : HdR X.A) (c : primDR X.A) :
    hm.bcMap h (m.pull c) = algebraMap R J.B (h c) :=
  (hm.corr_iff.2 rfl : m.Corr h (hm.bcMap h)) c

/- English proof (translation)
The claim follows from `(GrpMor.pull_pull m (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A) (homMor (dp0 R) (𝟙 _) (𝟙 X.A)) (fun r ↦ J.π_algebraMap r) (by simp) c).trans (Subtype.ext (IsMor.pullCohomologyOne_id _ c.1))`.
-/
theorem red_pull (c : primDR X.A) : (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).pull (m.pull c) = c :=
  (GrpMor.pull_pull m (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (fun r ↦ J.π_algebraMap r) (by simp) c).trans (Subtype.ext (IsMor.pullCohomologyOne_id _ c.1))

/- English proof (translation)
Rewrite using `[J.π_eq, JetRing.t, J.b.repr_self, Finsupp.single_apply, if_neg]`. Introduce `h`. Use `congrFun (congrArg Subtype.val h) i` as an intermediate fact. Simplify using `at this`.
-/
theorem jet_filtration_proj_section_eq_zero (i : I) : J.π (J.t i) = 0 := by
  rw [J.π_eq, JetRing.t, J.b.repr_self, Finsupp.single_apply, if_neg]
  intro h
  have := congrFun (congrArg Subtype.val h) i
  simp at this

/- English proof (translation)
The claim follows from `Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (ν.1 j)) (Finset.mem_univ i)).trans ν.2)⟩ : Fin (n + 2))) fun a b h ↦ Subtype.ext (funext fun i ↦ by simpa using congrFun h i)`.
-/
theorem finite_idx : Finite (Idx I n) :=
  Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (ν.1 j)) (Finset.mem_univ i)).trans ν.2)⟩ : Fin (n + 2)))
    fun a b h ↦ Subtype.ext (funext fun i ↦ by simpa using congrFun h i)

noncomputable def fintypeIdx : Fintype (Idx I n) := @Fintype.ofFinite _ finite_idx

attribute [local instance] fintypeIdx

def co (hm : m.IsBC) (ν : Idx I n) (d : Crys J.κ (spMap J.π) X.A) : HdR X.A where
  toFun c := J.b.repr (d (m.pull c)) ν
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' r c := by
    rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      RingHom.id_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem co_apply (hm : m.IsBC) (ν : Idx I n) (d : Crys J.κ (spMap J.π) X.A) (c : primDR X.A) :
    co hm ν d c = J.b.repr (d (m.pull c)) ν := rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun c ↦ by simp only [co_apply, LinearMap.add_apply, map_add, Finsupp.add_apply]`.
-/
theorem co_add (hm : m.IsBC) (ν : Idx I n) (d₁ d₂ : Crys J.κ (spMap J.π) X.A) :
    co hm ν (d₁ + d₂) = co hm ν d₁ + co hm ν d₂ :=
  LinearMap.ext fun c ↦ by simp only [co_apply, LinearMap.add_apply, map_add, Finsupp.add_apply]

/- English proof (translation)
The claim follows from `LinearMap.ext fun c ↦ by simp only [co_apply, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]`.
-/
theorem co_zero (hm : m.IsBC) (ν : Idx I n) : co hm ν (0 : Crys J.κ (spMap J.π) X.A) = 0 :=
  LinearMap.ext fun c ↦ by simp only [co_apply, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]

/- English proof (translation)
The claim follows from `LinearMap.ext fun c ↦ by rw [co_apply, LinearMap.smul_apply, bcMap_apply, smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, LinearMap.smul_apply, smul_eq_mul, mul_comm]`.
-/
theorem co_smul_bc (hm : m.IsBC) (ν : Idx I n) (β : J.B) (h : HdR X.A) :
    co hm ν (β • hm.bcMap h) = J.b.repr β ν • h :=
  LinearMap.ext fun c ↦ by
    rw [co_apply, LinearMap.smul_apply, bcMap_apply, smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def,
      map_smul, Finsupp.smul_apply, smul_eq_mul, LinearMap.smul_apply, smul_eq_mul, mul_comm]

/- English proof (translation)
Use `crys_ext hm fun c ↦ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `conv_lhs => rw [← J.b.sum_repr (d (m.pull c))]`. Use `Finset.sum_congr rfl fun ν _ ↦ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, bcMap_apply, co_apply, smul_eq_mul, Algebra.smul_def, mul_comm]`.
-/
theorem eq_sum_co (hm : m.IsBC) (d : Crys J.κ (spMap J.π) X.A) :
    d = ∑ ν, J.b ν • hm.bcMap (co hm ν d) := by
  refine crys_ext hm fun c ↦ ?_
  rw [LinearMap.sum_apply]
  conv_lhs => rw [← J.b.sum_repr (d (m.pull c))]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [LinearMap.smul_apply, bcMap_apply, co_apply, smul_eq_mul, Algebra.smul_def, mul_comm]

def bcE (hm : m.IsBC) : J.B ⊗[R] HdR X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A := liftSemi hm.bcMap

/- English proof (translation)
Set `G : Crys J.κ (spMap J.π) X.A → J.B ⊗[R] HdR X.A` to `fun d ↦ ∑ ν, J.b ν ⊗ₜ co hm ν d`. Establish `hG : ∀ z, G (bcE hm z) = z` using `fun z ↦ by`. Proceed by induction on `z with`. Consider the case `zero => simp only [G, map_zero, co_zero, tmul_zero, Finset.sum_const_zero]`. Consider the case `add x y hx hy`.

Simplify using `only [G, map_add, co_add, tmul_add, Finset.sum_add_distrib] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `tmul β h`. Simplify using `only [G, bcE, liftSemi_tmul, co_smul_bc, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]`. Rewrite using `[J.b.sum_repr]`.

Use `⟨Function.LeftInverse.injective hG, fun d ↦ ⟨∑ ν, J.b ν ⊗ₜ co hm ν d, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [map_sum, bcE, liftSemi_tmul]`. Conclude with `(eq_sum_co hm d).symm`.
-/
theorem bcE_bijective (hm : m.IsBC) : Function.Bijective (bcE hm) := by
  let G : Crys J.κ (spMap J.π) X.A → J.B ⊗[R] HdR X.A := fun d ↦ ∑ ν, J.b ν ⊗ₜ co hm ν d
  have hG : ∀ z, G (bcE hm z) = z := fun z ↦ by
    induction z with
    | zero => simp only [G, map_zero, co_zero, tmul_zero, Finset.sum_const_zero]
    | add x y hx hy =>
      simp only [G, map_add, co_add, tmul_add, Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy]
    | tmul β h =>
      simp only [G, bcE, liftSemi_tmul, co_smul_bc, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
      rw [J.b.sum_repr]
  refine ⟨Function.LeftInverse.injective hG, fun d ↦ ⟨∑ ν, J.b ν ⊗ₜ co hm ν d, ?_⟩⟩
  simp only [map_sum, bcE, liftSemi_tmul]
  exact (eq_sum_co hm d).symm

section Tensor

variable {A M : Type*} [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

/- English proof (translation)
Set `P` to `(q.projection p h.symm).baseChange A`. Establish `hp : ∀ z ∈ Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (p : Set M)), P z = 0` using `fun z hz ↦ by`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`.

Rewrite using `[LinearMap.baseChange_tmul, Submodule.projection_apply_of_mem_right h.symm hy, tmul_zero]`. Consider the case `zero => exact map_zero _`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [map_smul, hx, smul_zero]`. Establish `hq : ∀ z ∈ Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (q : Set M)), P z = z` using `fun z hz ↦ by`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Rewrite using `[LinearMap.baseChange_tmul, Submodule.projection_apply_of_mem_left h.symm hy]`. Consider the case `zero => exact map_zero _`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `smul a x _ hx => rw [map_smul, hx]`. Use `⟨Submodule.disjoint_def.2 fun z h₁ h₂ ↦ (hq z h₂).symm.trans (hp z h₁), codisjoint_iff.2 ?_⟩` and prove the remaining obligations. Use `(Submodule.eq_top_iff'.2 fun z ↦ ?_)` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => exact zero_mem _`. Consider the case `tmul β x`. Take `⟨y, hy, k, hk, rfl⟩` from `Submodule.mem_sup.1 (h.sup_eq_top ▸ Submodule.mem_top : x ∈ p ⊔ q)`. Establish `e : ∀ w : M, β ⊗ₜ[R] w = β • ((1 : A) ⊗ₜ[R] w)` using `fun w ↦ by rw [smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[tmul_add, e, e]`.

Conclude with `add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩))) (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)))`. Consider the case `add x y hx hy => exact add_mem hx hy`.
-/
theorem isCompl_span_tmul {p q : Submodule R M} (h : IsCompl p q) :
    IsCompl (Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (p : Set M)))
      (Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (q : Set M))) := by
  let P := (q.projection p h.symm).baseChange A
  have hp : ∀ z ∈ Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (p : Set M)), P z = 0 := fun z hz ↦ by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [LinearMap.baseChange_tmul, Submodule.projection_apply_of_mem_right h.symm hy, tmul_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have hq : ∀ z ∈ Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (q : Set M)), P z = z := fun z hz ↦ by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [LinearMap.baseChange_tmul, Submodule.projection_apply_of_mem_left h.symm hy]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  refine ⟨Submodule.disjoint_def.2 fun z h₁ h₂ ↦ (hq z h₂).symm.trans (hp z h₁), codisjoint_iff.2 ?_⟩
  refine (Submodule.eq_top_iff'.2 fun z ↦ ?_)
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul β x =>
    obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.1 (h.sup_eq_top ▸ Submodule.mem_top : x ∈ p ⊔ q)
    have e : ∀ w : M, β ⊗ₜ[R] w = β • ((1 : A) ⊗ₜ[R] w) := fun w ↦ by rw [smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [tmul_add, e, e]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)))
  | add x y hx hy => exact add_mem hx hy

end Tensor

variable {N : I → Module.End R (HdR X.A)}

def nilK (N : I → Module.End R (HdR X.A)) : Module.End J.B (J.B ⊗[R] HdR X.A) :=
  ∑ i, J.t i • (N i).baseChange J.B

/- English proof (translation)
Establish `h : ∀ i j, (N i).baseChange J.B * (N j).baseChange J.B = 0` using `fun i j ↦ by`. Rewrite using `[Module.End.mul_eq_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hN, LinearMap.baseChange_zero]`. Simplify using `only [nilK, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, h, smul_zero, Finset.sum_const_zero]`.
-/
theorem nilK_sq (hN : ∀ i j, N i * N j = 0) : nilK (J := J) N * nilK N = 0 := by
  have h : ∀ i j, (N i).baseChange J.B * (N j).baseChange J.B = 0 := fun i j ↦ by
    rw [Module.End.mul_eq_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hN,
      LinearMap.baseChange_zero]
  simp only [nilK, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, h, smul_zero, Finset.sum_const_zero]

def jetAut (hN : ∀ i j, N i * N j = 0) : (J.B ⊗[R] HdR X.A) ≃ₗ[J.B] (J.B ⊗[R] HdR X.A) :=
  LinearEquiv.ofLinear (1 + nilK N) (1 - nilK N)
    (by
      rw [← Module.End.mul_eq_comp, ← Module.End.one_eq_id]
      have : (1 + nilK (J := J) N) * (1 - nilK N) = 1 - nilK N * nilK N := by noncomm_ring
      rw [this, nilK_sq hN, sub_zero])
    (by
      rw [← Module.End.mul_eq_comp, ← Module.End.one_eq_id]
      have : (1 - nilK (J := J) N) * (1 + nilK N) = 1 - nilK N * nilK N := by noncomm_ring
      rw [this, nilK_sq hN, sub_zero])

def jetEquiv (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) :
    (J.B ⊗[R] HdR X.A) ≃ₗ[J.B] Crys J.κ (spMap J.π) X.A :=
  (jetAut hN).trans (LinearEquiv.ofBijective (bcE hm) (bcE_bijective hm))

/- English proof (translation)
Simplify using `only [jetEquiv, jetAut, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply, LinearEquiv.ofBijective_apply, LinearMap.add_apply, Module.End.one_apply, nilK, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul, map_add, map_sum, map_smul, bcE, liftSemi_tmul, one_s …`.
-/
theorem jetEquiv_tmul (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) (x : HdR X.A) :
    jetEquiv hm hN (1 ⊗ₜ x) = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := by
  simp only [jetEquiv, jetAut, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply, LinearEquiv.ofBijective_apply,
    LinearMap.add_apply, Module.End.one_apply, nilK, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, map_add, map_sum, map_smul, bcE, liftSemi_tmul, one_smul]

/- English proof (translation)
Rewrite using `[jetEquiv_tmul, LinearMap.add_apply, LinearMap.sum_apply, bcMap_apply]`. Simplify using `only [LinearMap.smul_apply, bcMap_apply, smul_eq_mul]`.
-/
theorem jetEquiv_tmul_apply (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) (x : HdR X.A) (c : primDR X.A) :
    jetEquiv hm hN (1 ⊗ₜ x) (m.pull c) = algebraMap R J.B (x c) + ∑ i, J.t i * algebraMap R J.B (N i x c) := by
  rw [jetEquiv_tmul, LinearMap.add_apply, LinearMap.sum_apply, bcMap_apply]
  simp only [LinearMap.smul_apply, bcMap_apply, smul_eq_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h ↦ crys_ext hm fun c ↦ (h c).trans (jetEquiv_tmul_apply hm hN x c).symm, fun h c ↦ h ▸ jetEquiv_tmul_apply hm hN x c⟩`.
-/
theorem isJetElt_iff (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) (x : HdR X.A) (d : Crys J.κ (spMap J.π) X.A) :
    IsJetElt J X N m x d ↔ d = jetEquiv hm hN (1 ⊗ₜ x) :=
  ⟨fun h ↦ crys_ext hm fun c ↦ (h c).trans (jetEquiv_tmul_apply hm hN x c).symm,
    fun h c ↦ h ▸ jetEquiv_tmul_apply hm hN x c⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H c`. Use `H (m.pull c)` as an intermediate fact. Rewrite `this` using `[red_pull]`. Then use the resulting hypothesis. Introduce `H c'`.

Take `⟨z, rfl⟩` from `hm.2 c'`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add x z hx hz => simp only [map_add, hx, hz]`. Consider the case `tmul β c`.

Rewrite using `[liftSemi_tmul, LinearMap.map_smulₛₗ, red_pull, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, H c]`.
-/
theorem corr_iff (hm : m.IsBC) (d : Crys J.κ (spMap J.π) X.A) (y : HdR X.A) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y ↔ ∀ c, y c = J.π (d (m.pull c)) := by
  constructor
  · intro H c
    have := H (m.pull c)
    rwa [red_pull] at this
  · intro H c'
    obtain ⟨z, rfl⟩ := hm.2 c'
    induction z with
    | zero => simp
    | add x z hx hz => simp only [map_add, hx, hz]
    | tmul β c =>
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ, red_pull, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, H c]

/- English proof (translation)
Proceed by induction on `hd using Submodule.span_induction with`. Consider the case `mem d hd`. Take `⟨x, hx, hj⟩` from `hd`. Use `⟨x, hx, fun c ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hj c, map_add, map_sum]`.

Simplify using `[jet_filtration_proj_section_eq_zero, JetRing.π_algebraMap]`. Consider the case `zero => exact ⟨0, zero_mem _, fun c ↦ by simp⟩`. Consider the case `add d₁ d₂ _ _ h₁ h₂`. Take `⟨y₁, hy₁, e₁⟩` from `h₁`. Take `⟨y₂, hy₂, e₂⟩` from `h₂`.

Conclude with `⟨y₁ + y₂, add_mem hy₁ hy₂, fun c ↦ by simp [e₁, e₂]⟩`. Consider the case `smul β d _ h`. Take `⟨y₁, hy₁, e₁⟩` from `h`. Conclude with `⟨J.π β • y₁, Submodule.smul_mem _ _ hy₁, fun c ↦ by simp [e₁]⟩`.
-/
theorem exists_red_mem (hm : m.IsBC) {d : Crys J.κ (spMap J.π) X.A}
    (hd : d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) :
    ∃ y ∈ Fil X.A, ∀ c, y c = J.π (d (m.pull c)) := by
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, hj⟩ := hd
    refine ⟨x, hx, fun c ↦ ?_⟩
    rw [hj c, map_add, map_sum]
    simp [jet_filtration_proj_section_eq_zero, JetRing.π_algebraMap]
  | zero => exact ⟨0, zero_mem _, fun c ↦ by simp⟩
  | add d₁ d₂ _ _ h₁ h₂ =>
    obtain ⟨y₁, hy₁, e₁⟩ := h₁
    obtain ⟨y₂, hy₂, e₂⟩ := h₂
    exact ⟨y₁ + y₂, add_mem hy₁ hy₂, fun c ↦ by simp [e₁, e₂]⟩
  | smul β d _ h =>
    obtain ⟨y₁, hy₁, e₁⟩ := h
    exact ⟨J.π β • y₁, Submodule.smul_mem _ _ hy₁, fun c ↦ by simp [e₁]⟩

/- English proof (translation)
The claim follows from `((GlobalTheory.Published.GrothendieckMessing.canonical_of_abelianDeRham (κ := dividedPowersBot R) (π := RingHom.id R) HR (isDPNilpotent_bot R) Function.surjective_id ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)) _ X.A X.A _ ((GlobalTheory.CrysConn.isGrpPullback_ …`.
-/
theorem fil_compl (HR : GlobalTheory.Published.AbelianDeRham) (X : Obj F 𝔠 (Sp R)) : ∃ C, IsCompl (Fil X.A) C :=
  ((GlobalTheory.Published.GrothendieckMessing.canonical_of_abelianDeRham (κ := dividedPowersBot R) (π := RingHom.id R) HR
    (isDPNilpotent_bot R) Function.surjective_id ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)) _
    X.A X.A _ ((GlobalTheory.CrysConn.isGrpPullback_refl X.A).congr (Cris.spMap_id R).symm rfl) X.ab X.dim).2.1

end GlobalTheory.LatJet.JetFil

namespace GlobalTheory.LatJet

open GlobalTheory.LatJet.JetFil

/- English proof (translation)
Introduce `HG HR HD F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m`. Establish `hm` using `isBC_jetRing HG HR HD F 𝔠 R I n J X m`. Establish `hN' : ∀ i j, N i * N j = 0` using `hN.2.1`. Take `⟨C, hC⟩` from `fil_compl HR X`. Establish `hS : {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} = jetEquiv hm hN' '' ((fun x ↦ (1 : J.B) ⊗ₜ[R] x) '' (Fil X.A : Set (HdR X.A)))`.

Use extensionality with `d`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, isJetElt_iff hm hN', SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨_, ⟨x, hx, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`. Use `⟨?_, fun y ↦ ⟨fun hy ↦ ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hS]`. Establish `h` using `(Submodule.orderIsoMapComap (jetEquiv hm hN')).isCompl (isCompl_span_tmul (A := J.B) hC)`.

Simplify using `only [Submodule.orderIsoMapComap_apply, Submodule.map_span] at h`. Conclude with `⟨_, h⟩`. Use `⟨jetEquiv hm hN' (1 ⊗ₜ y), Submodule.subset_span ⟨y, hy, (isJetElt_iff hm hN' y _).2 rfl⟩, (corr_iff hm _ _).2 fun c ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[jetEquiv_tmul_apply, map_add, map_sum]`. Simplify using `[jet_filtration_proj_section_eq_zero, JetRing.π_algebraMap]`.

Introduce and unpack `⟨d, hd, hc⟩`. Take `⟨y', hy', e⟩` from `exists_red_mem hm hd`. Establish `: y = y'` using `LinearMap.ext fun c ↦ ((corr_iff hm d y).1 hc c).trans (e c).symm`. Conclude with `this ▸ hy'`.
-/
theorem jetFil_summand_reduces : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      (∃ N' : Submodule J.B (Crys J.κ (spMap J.π) X.A), IsCompl (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) N') ∧
      ∀ y : HdR X.A, y ∈ Fil X.A ↔ ∃ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y := by
  intro HG HR HD F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m
  have hm := isBC_jetRing HG HR HD F 𝔠 R I n J X m
  have hN' : ∀ i j, N i * N j = 0 := hN.2.1
  obtain ⟨C, hC⟩ := fil_compl HR X
  have hS : {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} =
      jetEquiv hm hN' '' ((fun x ↦ (1 : J.B) ⊗ₜ[R] x) '' (Fil X.A : Set (HdR X.A))) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image, isJetElt_iff hm hN', SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  refine ⟨?_, fun y ↦ ⟨fun hy ↦ ?_, ?_⟩⟩
  · rw [hS]
    have h := (Submodule.orderIsoMapComap (jetEquiv hm hN')).isCompl (isCompl_span_tmul (A := J.B) hC)
    simp only [Submodule.orderIsoMapComap_apply, Submodule.map_span] at h
    exact ⟨_, h⟩
  · refine ⟨jetEquiv hm hN' (1 ⊗ₜ y), Submodule.subset_span ⟨y, hy, (isJetElt_iff hm hN' y _).2 rfl⟩,
      (corr_iff hm _ _).2 fun c ↦ ?_⟩
    rw [jetEquiv_tmul_apply, map_add, map_sum]
    simp [jet_filtration_proj_section_eq_zero, JetRing.π_algebraMap]
  · rintro ⟨d, hd, hc⟩
    obtain ⟨y', hy', e⟩ := exists_red_mem hm hd
    have : y = y' := LinearMap.ext fun c ↦ ((corr_iff hm d y).1 hc c).trans (e c).symm
    exact this ▸ hy'

end GlobalTheory.LatJet
