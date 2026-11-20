import Mathlib
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.SmoothRepSchur
import GroundTheory.AutomorphicForms.HeckeAlgebra
import GroundTheory.AutomorphicForms.LocallyProfinite

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace SchurOrthogonality

open MeasureTheory Topology Set Function ComplexConjugate

section Descent

variable {G : Type*} [Group G] {Z : Subgroup G} {β : Type*} {F : G → β}

/- English proof (translation)
Take `⟨z, hz⟩` from `QuotientGroup.mk_out_eq_mul Z g`. Rewrite using `[hz]`. Conclude with `hF g z z.2`.
-/
theorem apply_out_mk (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (g : G) :
    F (QuotientGroup.mk g : G ⧸ Z).out = F g := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul Z g
  rw [hz]
  exact hF g z z.2

variable [Z.Normal]

/- English proof (translation)
Use `conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]`. Conclude with `apply_out_mk hF _`.
-/
theorem apply_out_mul (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (q : G ⧸ Z) (h : G) :
    F (q * (h : G ⧸ Z)).out = F (q.out * h) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]
  exact apply_out_mk hF _

/- English proof (translation)
Use `conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]`. Conclude with `apply_out_mk hF _`.
-/
theorem apply_out_mul_left (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (q : G ⧸ Z) (h : G) :
    F ((h : G ⧸ Z) * q).out = F (h * q.out) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]
  exact apply_out_mk hF _

/- English proof (translation)
Use `conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_inv]`. Conclude with `apply_out_mk hF _`.
-/
theorem apply_out_inv (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (q : G ⧸ Z) :
    F (q⁻¹).out = F (q.out⁻¹) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_inv]
  exact apply_out_mk hF _

variable [TopologicalSpace G] [TopologicalSpace β]

/- English proof (translation)
Rewrite using `[(QuotientGroup.isQuotientMap_mk Z).continuous_iff]`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `apply_out_mk hF g`.
-/
theorem continuous_apply_out (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (hc : Continuous F) :
    Continuous fun q : G ⧸ Z => F q.out := by
  rw [(QuotientGroup.isQuotientMap_mk Z).continuous_iff]
  convert hc using 1
  funext g
  exact apply_out_mk hF g

variable [IsTopologicalGroup G] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Use `integral_mul_right_eq_self (μ := ν) (fun q => F q.out) (h : G ⧸ Z)` as an intermediate fact. Simplify using `only [apply_out_mul hF] at this`. Conclude with `this`.
-/
theorem integral_out_mul [ν.IsMulRightInvariant] {F : G → E}
    (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (h : G) :
    ∫ q, F (q.out * h) ∂ν = ∫ q, F q.out ∂ν := by
  have := integral_mul_right_eq_self (μ := ν) (fun q => F q.out) (h : G ⧸ Z)
  simp only [apply_out_mul hF] at this
  exact this

/- English proof (translation)
Use `integral_mul_left_eq_self (μ := ν) (fun q => F q.out) (h : G ⧸ Z)` as an intermediate fact. Simplify using `only [apply_out_mul_left hF] at this`. Conclude with `this`.
-/
theorem integral_mul_out [ν.IsMulLeftInvariant] {F : G → E}
    (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (h : G) :
    ∫ q, F (h * q.out) ∂ν = ∫ q, F q.out ∂ν := by
  have := integral_mul_left_eq_self (μ := ν) (fun q => F q.out) (h : G ⧸ Z)
  simp only [apply_out_mul_left hF] at this
  exact this

end Descent

/- English proof (translation)
Take `⟨K, hK⟩` from `exists_compactOpenSubgroup (G := G)`. Use `set K' : Subgroup (G ⧸ Z) := K.toSubgroup.map (QuotientGroup.mk' Z)`. Establish `hK'set : (K' : Set (G ⧸ Z)) = QuotientGroup.mk '' (K : Set G)`. Simplify using `[K']`. Establish `hK'o : IsOpen (K' : Set (G ⧸ Z))`.

Rewrite using `[hK'set]`. Conclude with `QuotientGroup.isOpenMap_coe _ K.isOpen`. Establish `hK'c : IsCompact (K' : Set (G ⧸ Z))`. Rewrite using `[hK'set]`. Conclude with `hK.image QuotientGroup.continuous_mk`.

Establish `hK0 : ν K' ≠ 0` using `hK'o.measure_ne_zero ν ⟨1, K'.one_mem⟩`. Establish `hKT : ν K' ≠ ⊤` using `hK'c.measure_lt_top.ne`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul ν.inv ν`. Establish `hc : Measure.haarScalarFactor ν.inv ν = 1`. Establish `h` using `congrArg (fun μ : Measure (G ⧸ Z) => μ K') e`.

Simplify using `only [Measure.inv_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h`. Establish `hKinv : (K' : Set (G ⧸ Z))⁻¹ = K'`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `h` using `[hKinv]`.

Use `(ENNReal.mul_eq_right hK0 hKT).1 h.symm` as an intermediate fact. Conclude with `this` after adjusting the coercions. Conclude with `⟨by rw [e, hc, one_smul]⟩`.
-/
theorem isInvInvariant_of_isMulRightInvariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [SecondCountableTopology G] (Z : Subgroup G) [Z.Normal] [MeasurableSpace (G ⧸ Z)]
    [BorelSpace (G ⧸ Z)] (ν : Measure (G ⧸ Z)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] :
    ν.IsInvInvariant := by
  obtain ⟨K, hK⟩ := exists_compactOpenSubgroup (G := G)
  set K' : Subgroup (G ⧸ Z) := K.toSubgroup.map (QuotientGroup.mk' Z)
  have hK'set : (K' : Set (G ⧸ Z)) = QuotientGroup.mk '' (K : Set G) := by
    simp [K']
  have hK'o : IsOpen (K' : Set (G ⧸ Z)) := by
    rw [hK'set]
    exact QuotientGroup.isOpenMap_coe _ K.isOpen
  have hK'c : IsCompact (K' : Set (G ⧸ Z)) := by
    rw [hK'set]
    exact hK.image QuotientGroup.continuous_mk
  have hK0 : ν K' ≠ 0 := hK'o.measure_ne_zero ν ⟨1, K'.one_mem⟩
  have hKT : ν K' ≠ ⊤ := hK'c.measure_lt_top.ne
  have e := Measure.isMulLeftInvariant_eq_smul ν.inv ν
  have hc : Measure.haarScalarFactor ν.inv ν = 1 := by
    have h := congrArg (fun μ : Measure (G ⧸ Z) => μ K') e
    simp only [Measure.inv_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have hKinv : (K' : Set (G ⧸ Z))⁻¹ = K' := by
      ext x
      simp
    rw [hKinv] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  exact ⟨by rw [e, hc, one_smul]⟩

section Coefficients

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Z : Subgroup G) [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  (ν : Measure (G ⧸ Z))
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def IsSquareIntegrable (π : Representation ℂ G V) : Prop :=
  (∀ z ∈ Z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v) ∧
    ∀ (v : V) (φ : smoothVectors (Representation.dual π)),
      MemLp (fun q : G ⧸ Z => ‖(φ : Module.Dual ℂ V) (π q.out v)‖) 2 ν

def SameCentralCharacter (π : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∀ z ∈ Z, ∃ c : ℂ, (∀ v, π z v = c • v) ∧ ∀ w, σ z w = c • w

variable {Z ν}

def coeffProd (π : Representation ℂ G V) (σ : Representation ℂ G W) (v : V)
    (φ : Module.Dual ℂ V) (w : W) (ψ : Module.Dual ℂ W) (g : G) : ℂ :=
  φ (π g v) * ψ (σ g⁻¹ w)

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem rep_apply_inv_apply (σ : Representation ℂ G W) (h : G) (x : W) : σ h (σ h⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
theorem rep_inv_apply_apply (σ : Representation ℂ G W) (h : G) (x : W) : σ h⁻¹ (σ h x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Introduce `g z hz`. Take `⟨c, hv, hw⟩` from `hc z hz`. Establish `key : ∀ x : W, c * ψ (σ z⁻¹ x) = ψ x`. Introduce `x`. Rewrite using `[← smul_eq_mul, ← map_smul, ← hw, rep_apply_inv_apply]`.

Simplify using `only [coeffProd, mul_inv_rev, map_mul, Module.End.mul_apply, hv, map_smul, smul_eq_mul]`. Rewrite using `[← key (σ g⁻¹ w)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeffProd_mul_mem {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (hc : SameCentralCharacter Z π σ) (v : V) (φ : Module.Dual ℂ V) (w : W)
    (ψ : Module.Dual ℂ W) : ∀ g, ∀ z ∈ Z, coeffProd π σ v φ w ψ (g * z) = coeffProd π σ v φ w ψ g := by
  intro g z hz
  obtain ⟨c, hv, hw⟩ := hc z hz
  have key : ∀ x : W, c * ψ (σ z⁻¹ x) = ψ x := by
    intro x
    rw [← smul_eq_mul, ← map_smul, ← hw, rep_apply_inv_apply]
  simp only [coeffProd, mul_inv_rev, map_mul, Module.End.mul_apply, hv, map_smul, smul_eq_mul]
  rw [← key (σ g⁻¹ w)]
  ring

/- English proof (translation)
Introduce `g z hz`. Take `⟨c, hc1, hc⟩` from `h1 z hz`. Rewrite using `[map_mul, Module.End.mul_apply, hc, map_smul, map_smul, smul_eq_mul, norm_mul, hc1, one_mul]`.
-/
theorem norm_coeff_mul_mem {π : Representation ℂ G V}
    (h1 : ∀ z ∈ Z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v) (v : V) (φ : Module.Dual ℂ V) :
    ∀ g, ∀ z ∈ Z, ‖φ (π (g * z) v)‖ = ‖φ (π g v)‖ := by
  intro g z hz
  obtain ⟨c, hc1, hc⟩ := h1 z hz
  rw [map_mul, Module.End.mul_apply, hc, map_smul, map_smul, smul_eq_mul, norm_mul, hc1, one_mul]

/- English proof (translation)
Introduce `z hz` and use `by obtain ⟨c, -, hc⟩ := hπ.1 z hz exact ⟨c, hc, hc⟩`.
-/
theorem sameCentralCharacter_self {π : Representation ℂ G V} (hπ : IsSquareIntegrable Z ν π) :
    SameCentralCharacter Z π π := fun z hz => by
  obtain ⟨c, -, hc⟩ := hπ.1 z hz
  exact ⟨c, hc, hc⟩

/- English proof (translation)
The claim follows from `(continuous_dual_orbit (hπs v) φ).mul ((continuous_dual_orbit (hσs w) ψ).comp continuous_inv)`.
-/
theorem continuous_coeffProd {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (hπs : IsSmooth π) (hσs : IsSmooth σ) (v : V) (φ : Module.Dual ℂ V) (w : W)
    (ψ : Module.Dual ℂ W) : Continuous (coeffProd π σ v φ w ψ) :=
  (continuous_dual_orbit (hπs v) φ).mul ((continuous_dual_orbit (hσs w) ψ).comp continuous_inv)

/- English proof (translation)
Establish `ha` using `hπ.2 v φ`. Establish `hb : MemLp (fun q : G ⧸ Z => ‖(ψ : Module.Dual ℂ W) (σ q.out w)‖) 2 ν` using `hσ.2 w ψ`. Establish `hb' : MemLp ((fun q : G ⧸ Z => ‖(ψ : Module.Dual ℂ W) (σ q.out w)‖) ∘ Inv.inv) 2 ν` using `hb.comp_measurePreserving (Measure.measurePreserving_inv ν)`. Establish `hprod` using `ha.integrable_mul hb'`. Use `hprod.mono' ?_ (ae_of_all _ fun q => ?_)` and prove the remaining obligations.

Conclude with `(continuous_apply_out (coeffProd_mul_mem hc v φ w ψ) (continuous_coeffProd hπs hσs v φ w ψ)).aestronglyMeasurable`. Simplify using `only [coeffProd, norm_mul, Pi.mul_apply, Function.comp_apply]`. Rewrite using `[apply_out_inv (F := fun g => ‖(ψ : Module.Dual ℂ W) (σ g w)‖) (norm_coeff_mul_mem hσ.1 w ψ)]`.
-/
theorem integrable_coeffProd [ν.IsInvInvariant] {π : Representation ℂ G V}
    {σ : Representation ℂ G W} (hπ : IsSquareIntegrable Z ν π) (hσ : IsSquareIntegrable Z ν σ)
    (hc : SameCentralCharacter Z π σ) (hπs : IsSmooth π) (hσs : IsSmooth σ) (v : V)
    (φ : smoothVectors (Representation.dual π)) (w : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    Integrable (fun q : G ⧸ Z => coeffProd π σ v φ w ψ q.out) ν := by
  have ha := hπ.2 v φ
  have hb : MemLp (fun q : G ⧸ Z => ‖(ψ : Module.Dual ℂ W) (σ q.out w)‖) 2 ν := hσ.2 w ψ
  have hb' : MemLp ((fun q : G ⧸ Z => ‖(ψ : Module.Dual ℂ W) (σ q.out w)‖) ∘ Inv.inv) 2 ν :=
    hb.comp_measurePreserving (Measure.measurePreserving_inv ν)
  have hprod := ha.integrable_mul hb'
  refine hprod.mono' ?_ (ae_of_all _ fun q => ?_)
  · exact (continuous_apply_out (coeffProd_mul_mem hc v φ w ψ)
      (continuous_coeffProd hπs hσs v φ w ψ)).aestronglyMeasurable
  · simp only [coeffProd, norm_mul, Pi.mul_apply, Function.comp_apply]
    rw [apply_out_inv (F := fun g => ‖(ψ : Module.Dual ℂ W) (σ g w)‖)
      (norm_coeff_mul_mem hσ.1 w ψ)]

end Coefficients

section Pairing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Z : Subgroup G) [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  (ν : Measure (G ⧸ Z))
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def pairing (π : Representation ℂ G V) (σ : Representation ℂ G W) (v : V) (φ : Module.Dual ℂ V)
    (w : W) (ψ : Module.Dual ℂ W) : ℂ :=
  ∫ q : G ⧸ Z, coeffProd π σ v φ w ψ q.out ∂ν

variable {Z ν} {π : Representation ℂ G V} {σ : Representation ℂ G W}
  [ν.IsInvInvariant] (hπ : IsSquareIntegrable Z ν π) (hσ : IsSquareIntegrable Z ν σ)
  (hc : SameCentralCharacter Z π σ) (hπs : IsSmooth π) (hσs : IsSmooth σ)

include hπ hσ hc hπs hσs in
/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v₁ φ w ψ) (integrable_coeffProd hπ hσ hc hπs hσs v₂ φ w ψ)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, map_add, add_mul]`.
-/
theorem pairing_add_left (v₁ v₂ : V) (φ : smoothVectors (Representation.dual π)) (w : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    pairing Z ν π σ (v₁ + v₂) φ w ψ = pairing Z ν π σ v₁ φ w ψ + pairing Z ν π σ v₂ φ w ψ := by
  unfold pairing
  rw [← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v₁ φ w ψ)
    (integrable_coeffProd hπ hσ hc hπs hσs v₂ φ w ψ)]
  congr 1
  funext q
  simp only [coeffProd, map_add, add_mul]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_smul_left (c : ℂ) (v : V) (φ : Module.Dual ℂ V) (w : W) (ψ : Module.Dual ℂ W) :
    pairing Z ν π σ (c • v) φ w ψ = c * pairing Z ν π σ v φ w ψ := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [coeffProd, map_smul, smul_eq_mul]
  ring

include hπ hσ hc hπs hσs in
/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v φ w ψ₁) (integrable_coeffProd hπ hσ hc hπs hσs v φ w ψ₂)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, Submodule.coe_add, LinearMap.add_apply, mul_add]`.
-/
theorem pairing_add_right (v : V) (φ : smoothVectors (Representation.dual π)) (w : W)
    (ψ₁ ψ₂ : smoothVectors (Representation.dual σ)) :
    pairing Z ν π σ v φ w ((ψ₁ + ψ₂ : smoothVectors (Representation.dual σ)) : Module.Dual ℂ W) =
      pairing Z ν π σ v φ w ψ₁ + pairing Z ν π σ v φ w ψ₂ := by
  unfold pairing
  rw [← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v φ w ψ₁)
    (integrable_coeffProd hπ hσ hc hπs hσs v φ w ψ₂)]
  congr 1
  funext q
  simp only [coeffProd, Submodule.coe_add, LinearMap.add_apply, mul_add]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_smul_right (c : ℂ) (v : V) (φ : Module.Dual ℂ V) (w : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    pairing Z ν π σ v φ w ((c • ψ : smoothVectors (Representation.dual σ)) : Module.Dual ℂ W) =
      c * pairing Z ν π σ v φ w ψ := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [coeffProd, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

include hπ hσ hc hπs hσs in
/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v φ w₁ ψ) (integrable_coeffProd hπ hσ hc hπs hσs v φ w₂ ψ)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, map_add, mul_add]`.
-/
theorem pairing_add_w (v : V) (φ : smoothVectors (Representation.dual π)) (w₁ w₂ : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    pairing Z ν π σ v φ (w₁ + w₂) ψ = pairing Z ν π σ v φ w₁ ψ + pairing Z ν π σ v φ w₂ ψ := by
  unfold pairing
  rw [← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v φ w₁ ψ)
    (integrable_coeffProd hπ hσ hc hπs hσs v φ w₂ ψ)]
  congr 1
  funext q
  simp only [coeffProd, map_add, mul_add]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_smul_w (c : ℂ) (v : V) (φ : Module.Dual ℂ V) (w : W) (ψ : Module.Dual ℂ W) :
    pairing Z ν π σ v φ (c • w) ψ = c * pairing Z ν π σ v φ w ψ := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [coeffProd, map_smul, smul_eq_mul]
  ring

include hπ hσ hc hπs hσs in
/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v φ₁ w ψ) (integrable_coeffProd hπ hσ hc hπs hσs v φ₂ w ψ)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, Submodule.coe_add, LinearMap.add_apply, add_mul]`.
-/
theorem pairing_add_φ (v : V) (φ₁ φ₂ : smoothVectors (Representation.dual π)) (w : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    pairing Z ν π σ v ((φ₁ + φ₂ : smoothVectors (Representation.dual π)) : Module.Dual ℂ V) w ψ =
      pairing Z ν π σ v φ₁ w ψ + pairing Z ν π σ v φ₂ w ψ := by
  unfold pairing
  rw [← integral_add (integrable_coeffProd hπ hσ hc hπs hσs v φ₁ w ψ)
    (integrable_coeffProd hπ hσ hc hπs hσs v φ₂ w ψ)]
  congr 1
  funext q
  simp only [coeffProd, Submodule.coe_add, LinearMap.add_apply, add_mul]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_smul_φ (c : ℂ) (v : V) (φ : smoothVectors (Representation.dual π)) (w : W)
    (ψ : Module.Dual ℂ W) :
    pairing Z ν π σ v ((c • φ : smoothVectors (Representation.dual π)) : Module.Dual ℂ V) w ψ =
      c * pairing Z ν π σ v φ w ψ := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [coeffProd, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit [ν.IsInvInvariant] in
include hc in

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_out_mul (coeffProd_mul_mem hc v φ w _) h]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul, Module.End.mul_apply, rep_apply_inv_apply]`.
-/
theorem pairing_apply_left [ν.IsMulRightInvariant] (h : G) (v : V) (φ : Module.Dual ℂ V) (w : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    pairing Z ν π σ (π h v) φ w ψ =
      pairing Z ν π σ v φ w ((contragredient σ h⁻¹ ψ : smoothVectors (Representation.dual σ)) :
        Module.Dual ℂ W) := by
  unfold pairing
  rw [← integral_out_mul (coeffProd_mul_mem hc v φ w _) h]
  congr 1
  funext q
  simp only [coeffProd, contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul,
    Module.End.mul_apply, rep_apply_inv_apply]

omit [ν.IsInvInvariant] in
include hc in

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_mul_out (coeffProd_mul_mem hc v _ w ψ) h⁻¹]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [coeffProd, contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul, Module.End.mul_apply, rep_apply_inv_apply]`.
-/
theorem pairing_apply_w [ν.IsMulLeftInvariant] (h : G) (v : V)
    (φ : smoothVectors (Representation.dual π)) (w : W) (ψ : Module.Dual ℂ W) :
    pairing Z ν π σ v φ (σ h w) ψ =
      pairing Z ν π σ v ((contragredient π h⁻¹ φ : smoothVectors (Representation.dual π)) :
        Module.Dual ℂ V) w ψ := by
  unfold pairing
  rw [← integral_mul_out (coeffProd_mul_mem hc v _ w ψ) h⁻¹]
  congr 1
  funext q
  simp only [coeffProd, contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul,
    Module.End.mul_apply, rep_apply_inv_apply]

end Pairing

section Intertwining

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

/- English proof (translation)
Establish `hsm : ∀ v, T v ∈ smoothVectors (Representation.dual (contragredient σ))`. Introduce `v`. Use `Subgroup.isOpen_mono (H₁ := stabilizerOf π v) (fun h hh => ?_) (hπs v)` and prove the remaining obligations. Rewrite `hh`, the goal using `[mem_stabilizerOf]`. Use extensionality with `ψ`.

Rewrite using `[dual_apply_apply, ← hT, hh]`. Set `S : V →ₗ[ℂ] smoothVectors (Representation.dual (contragredient σ))` to `T.codRestrict _ hsm`. Establish `hS : ∀ v ψ, ((S v : smoothVectors (Representation.dual (contragredient σ))) : Module.Dual ℂ (smoothVectors (Representation.dual σ))) ψ = T v ψ` using `fun _ _ => rfl`. Set `D` to `toDoubleContragredient hσ.1`. Establish `hDb : Function.Bijective D.toLinearMap` using `toDoubleContragredient_bijective hσ`.

Set `e` to `LinearEquiv.ofBijective D.toLinearMap hDb`. Set `E₀ : V →ₗ[ℂ] W` to `e.symm.toLinearMap ∘ₗ S`. Establish `hE : ∀ v, D (E₀ v) = S v` using `fun v => e.apply_symm_apply (S v)`. Establish `hSint : ∀ h v, S (π h v) = contragredient (contragredient σ) h (S v)`. Introduce `h v`.

Use `Subtype.ext (LinearMap.ext fun ψ => ?_)` and prove the remaining obligations. Rewrite using `[hS, contragredient_apply_apply, hS, hT]`. Use `⟨⟨E₀, fun h => LinearMap.ext fun v => ?_⟩, fun v ψ => ?_⟩` and prove the remaining obligations. Apply `hDb.1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `D (E₀ (π h v)) = D (σ h (E₀ v))`.

Rewrite using `[hE, D.isIntertwining, hE, hSint]`. Express the relevant statement in the definitionally equal form `T v ψ = (ψ : Module.Dual ℂ W) (E₀ v)`. Rewrite using `[← toDoubleContragredient_apply_apply σ hσ.1 (E₀ v) ψ]`. Express the relevant statement in the definitionally equal form `T v ψ = ((D (E₀ v) : smoothVectors (Representation.dual (contragredient σ))) : Module.Dual ℂ (smoothVectors (Representation.dual σ))) ψ`. Rewrite using `[hE, hS]`.
-/
theorem exists_intertwiningMap (hπs : IsSmooth π) (hσ : IsAdmissible σ)
    (T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual σ)))
    (hT : ∀ h v ψ, T (π h v) ψ = T v (contragredient σ h⁻¹ ψ)) :
    ∃ E : Representation.IntertwiningMap π σ, ∀ v ψ, T v ψ = (ψ : Module.Dual ℂ W) (E v) := by
  have hsm : ∀ v, T v ∈ smoothVectors (Representation.dual (contragredient σ)) := by
    intro v
    refine Subgroup.isOpen_mono (H₁ := stabilizerOf π v) (fun h hh => ?_) (hπs v)
    rw [mem_stabilizerOf] at hh ⊢
    ext ψ
    rw [dual_apply_apply, ← hT, hh]
  let S : V →ₗ[ℂ] smoothVectors (Representation.dual (contragredient σ)) := T.codRestrict _ hsm
  have hS : ∀ v ψ, ((S v : smoothVectors (Representation.dual (contragredient σ))) :
      Module.Dual ℂ (smoothVectors (Representation.dual σ))) ψ = T v ψ := fun _ _ => rfl
  let D := toDoubleContragredient hσ.1
  have hDb : Function.Bijective D.toLinearMap := toDoubleContragredient_bijective hσ
  let e := LinearEquiv.ofBijective D.toLinearMap hDb
  let E₀ : V →ₗ[ℂ] W := e.symm.toLinearMap ∘ₗ S
  have hE : ∀ v, D (E₀ v) = S v := fun v => e.apply_symm_apply (S v)
  have hSint : ∀ h v, S (π h v) = contragredient (contragredient σ) h (S v) := by
    intro h v
    refine Subtype.ext (LinearMap.ext fun ψ => ?_)
    rw [hS, contragredient_apply_apply, hS, hT]
  refine ⟨⟨E₀, fun h => LinearMap.ext fun v => ?_⟩, fun v ψ => ?_⟩
  · apply hDb.1
    change D (E₀ (π h v)) = D (σ h (E₀ v))
    rw [hE, D.isIntertwining, hE, hSint]
  · change T v ψ = (ψ : Module.Dual ℂ W) (E₀ v)
    rw [← toDoubleContragredient_apply_apply σ hσ.1 (E₀ v) ψ]
    change T v ψ = ((D (E₀ v) : smoothVectors (Representation.dual (contragredient σ))) :
      Module.Dual ℂ (smoothVectors (Representation.dual σ))) ψ
    rw [hE, hS]

/- English proof (translation)
Take `⟨E, hE⟩` from `exists_intertwiningMap hπ.1 hπ T hT`. Take `⟨c, hc⟩` from `(algebraMap_intertwiningMap_bijective_of_isSmooth hπ.1).2 E`. Use `⟨c, fun v ψ => ?_⟩` and prove the remaining obligations. Rewrite using `[hE, ← hc, Algebra.algebraMap_eq_smul_one]`. Express the relevant statement in the definitionally equal form `(ψ : Module.Dual ℂ V) (c • v) = _`.

Rewrite using `[map_smul, smul_eq_mul]`.
-/
theorem exists_smul_of_intertwining [SecondCountableTopology G] (hπ : IsAdmissible π)
    [π.IsIrreducible] (T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual π)))
    (hT : ∀ h v ψ, T (π h v) ψ = T v (contragredient π h⁻¹ ψ)) :
    ∃ c : ℂ, ∀ v ψ, T v ψ = c * (ψ : Module.Dual ℂ V) v := by
  obtain ⟨E, hE⟩ := exists_intertwiningMap hπ.1 hπ T hT
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hπ.1).2 E
  refine ⟨c, fun v ψ => ?_⟩
  rw [hE, ← hc, Algebra.algebraMap_eq_smul_one]
  change (ψ : Module.Dual ℂ V) (c • v) = _
  rw [map_smul, smul_eq_mul]

/- English proof (translation)
Take `⟨E, hE⟩` from `exists_intertwiningMap hπs hσ T hT`. Break down `Representation.IsIrreducible.bijective_or_eq_zero E with hb | h0` into its components or cases. Conclude with `(hne.false (E.ofBijective hb)).elim`. Introduce `v ψ`. Rewrite using `[hE, h0]`.

Conclude with `map_zero _`.
-/
theorem eq_zero_of_intertwining (hπs : IsSmooth π) (hσ : IsAdmissible σ) [π.IsIrreducible]
    [σ.IsIrreducible] (hne : IsEmpty (π.Equiv σ))
    (T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual σ)))
    (hT : ∀ h v ψ, T (π h v) ψ = T v (contragredient σ h⁻¹ ψ)) :
    ∀ v ψ, T v ψ = 0 := by
  obtain ⟨E, hE⟩ := exists_intertwiningMap hπs hσ T hT
  rcases Representation.IsIrreducible.bijective_or_eq_zero E with hb | h0
  · exact (hne.false (E.ofBijective hb)).elim
  · intro v ψ
    rw [hE, h0]
    exact map_zero _

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne_zero_of_isIrreducible (ρ := π)`. Take `⟨K, hKc, hKo, hvK⟩` from `(isSmooth_iff_forall_exists π).1 hπs v`. Establish `hx : (⟨v, hvK⟩ : fixedVectors π K) ≠ 0` using `fun h => hv (congrArg Subtype.val h)`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual ℂ (fixedVectors π K), f ⟨v, hvK⟩ ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)`. Use `set e := fixedContragredientEquiv hπs hKc hKo`. Establish `hval : (((e.symm f : fixedVectors (contragredient π) K) : smoothVectors (Representation.dual π)) : Module.Dual ℂ V) v = f ⟨v, hvK⟩`. Establish `h2 : e (e.symm f) = f` using `e.apply_symm_apply f`.

Use `conv_rhs => rw [← h2]`. Rewrite using `[fixedContragredientEquiv_apply, restrictFixed_apply]`. Use `⟨v, (f ⟨v, hvK⟩)⁻¹ • ((e.symm f : fixedVectors (contragredient π) K) : smoothVectors (Representation.dual π)), ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, LinearMap.smul_apply, hval, smul_eq_mul, inv_mul_cancel₀ hf]`.
-/
theorem exists_dual_apply_eq_one (hπs : IsSmooth π) [π.IsIrreducible] :
    ∃ (v : V) (ψ : smoothVectors (Representation.dual π)), (ψ : Module.Dual ℂ V) v = 1 := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists π).1 hπs v
  have hx : (⟨v, hvK⟩ : fixedVectors π K) ≠ 0 := fun h => hv (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (fixedVectors π K), f ⟨v, hvK⟩ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  set e := fixedContragredientEquiv hπs hKc hKo
  have hval : (((e.symm f : fixedVectors (contragredient π) K) :
      smoothVectors (Representation.dual π)) : Module.Dual ℂ V) v = f ⟨v, hvK⟩ := by
    have h2 : e (e.symm f) = f := e.apply_symm_apply f
    conv_rhs => rw [← h2]
    rw [fixedContragredientEquiv_apply, restrictFixed_apply]
  refine ⟨v, (f ⟨v, hvK⟩)⁻¹ • ((e.symm f : fixedVectors (contragredient π) K) :
    smoothVectors (Representation.dual π)), ?_⟩
  rw [Submodule.coe_smul, LinearMap.smul_apply, hval, smul_eq_mul, inv_mul_cancel₀ hf]

end Intertwining

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

/- English proof (translation)
Use `isInvInvariant_of_isMulRightInvariant Z ν` as an intermediate fact. Set `T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual σ))` to `LinearMap.mk₂ ℂ (fun v ψ => pairing Z ν π σ v φ w ψ) (fun v₁ v₂ ψ => pairing_add_left hπ2 hσ2 hc hπ.1 hσ.1 v₁ v₂ φ w ψ) (fun c v ψ => by rw [smul_eq_mul]; exact pairing_smul_left c v φ w ψ) (fun v ψ₁ ψ₂ => pairing_add_right hπ2 hσ2 hc hπ.1 hσ.1 v φ w ψ₁ ψ₂) (fun c v ψ => by rw [s …`. Establish `hT : ∀ h v ψ, T (π h v) ψ = T v (contragredient σ h⁻¹ ψ)` using `fun h v ψ => pairing_apply_left hc h v φ w ψ`. Conclude with `eq_zero_of_intertwining hπ.1 hσ hne T hT v ψ`.
-/
theorem integral_eq_zero_of_isEmpty_equiv (hπ : IsAdmissible π) (hσ : IsAdmissible σ)
    [π.IsIrreducible] [σ.IsIrreducible] (hπ2 : IsSquareIntegrable Z ν π)
    (hσ2 : IsSquareIntegrable Z ν σ) (hc : SameCentralCharacter Z π σ)
    (hne : IsEmpty (π.Equiv σ)) (v : V) (φ : smoothVectors (Representation.dual π)) (w : W)
    (ψ : smoothVectors (Representation.dual σ)) :
    ∫ q : G ⧸ Z, (φ : Module.Dual ℂ V) (π q.out v) * (ψ : Module.Dual ℂ W) (σ q.out⁻¹ w) ∂ν =
      0 := by
  have := isInvInvariant_of_isMulRightInvariant Z ν
  let T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual σ)) :=
    LinearMap.mk₂ ℂ (fun v ψ => pairing Z ν π σ v φ w ψ)
      (fun v₁ v₂ ψ => pairing_add_left hπ2 hσ2 hc hπ.1 hσ.1 v₁ v₂ φ w ψ)
      (fun c v ψ => by rw [smul_eq_mul]; exact pairing_smul_left c v φ w ψ)
      (fun v ψ₁ ψ₂ => pairing_add_right hπ2 hσ2 hc hπ.1 hσ.1 v φ w ψ₁ ψ₂)
      (fun c v ψ => by rw [smul_eq_mul]; exact pairing_smul_right c v φ w ψ)
  have hT : ∀ h v ψ, T (π h v) ψ = T v (contragredient σ h⁻¹ ψ) :=
    fun h v ψ => pairing_apply_left hc h v φ w ψ
  exact eq_zero_of_intertwining hπ.1 hσ hne T hT v ψ

/- English proof (translation)
Use `isInvInvariant_of_isMulRightInvariant Z ν` as an intermediate fact. Establish `hc` using `sameCentralCharacter_self hπ2`. Establish `h1 : ∀ (φ : smoothVectors (Representation.dual π)) (w : V), ∃ c : ℂ, ∀ (v : V) (ψ : smoothVectors (Representation.dual π)), pairing Z ν π π v φ w ψ = c * (ψ : Module.Dual ℂ V) v`. Introduce `φ w`. Set `T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual π))` to `LinearMap.mk₂ ℂ (fun v ψ => pairing Z ν π π v φ w ψ) (fun v₁ v₂ ψ => pairing_add_left hπ2 hπ2 hc hπ.1 hπ.1 v₁ v₂ φ w ψ) (fun c v ψ => by rw [smul_eq_mul]; exact pairing_smul_left c v φ w ψ) (fun v ψ₁ ψ₂ => pairing_add_right hπ2 hπ2 hc hπ.1 hπ.1 v φ w ψ₁ ψ₂) (fun c v ψ => by rw [s …`.

Conclude with `exists_smul_of_intertwining hπ T fun h v ψ => pairing_apply_left hc h v φ w ψ`. Establish `h2 : ∀ (v : V) (ψ : smoothVectors (Representation.dual π)), ∃ c : ℂ, ∀ (w : V) (φ : smoothVectors (Representation.dual π)), pairing Z ν π π v φ w ψ = c * (φ : Module.Dual ℂ V) w`. Introduce `v ψ`. Set `T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual π))` to `LinearMap.mk₂ ℂ (fun w φ => pairing Z ν π π v φ w ψ) (fun w₁ w₂ φ => pairing_add_w hπ2 hπ2 hc hπ.1 hπ.1 v φ w₁ w₂ ψ) (fun c w φ => by rw [smul_eq_mul]; exact pairing_smul_w c v φ w ψ) (fun w φ₁ φ₂ => pairing_add_φ hπ2 hπ2 hc hπ.1 hπ.1 v φ₁ φ₂ w ψ) (fun c w φ => by rw [smul_eq_mul …`. Conclude with `exists_smul_of_intertwining hπ T fun h w φ => pairing_apply_w hc h v φ w ψ`.

Take `⟨v₀, ψ₀, h₀⟩` from `exists_dual_apply_eq_one hπ.1`. Take `⟨k, hk⟩` from `h2 v₀ ψ₀`. Use `⟨k, fun v φ w ψ => ?_⟩` and prove the remaining obligations. Take `⟨c, hcφw⟩` from `h1 φ w`. Establish `hck : c = k * (φ : Module.Dual ℂ V) w`.

Use `hcφw v₀ ψ₀` as an intermediate fact. Rewrite `this` using `[h₀, mul_one]`. Rewrite using `[← this, hk]`. Rewrite using `[hcφw, hck]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pairing_eq (hπ : IsAdmissible π) [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) :
    ∃ k : ℂ, ∀ (v : V) (φ : smoothVectors (Representation.dual π)) (w : V)
      (ψ : smoothVectors (Representation.dual π)),
      pairing Z ν π π v φ w ψ = k * ((φ : Module.Dual ℂ V) w * (ψ : Module.Dual ℂ V) v) := by
  have := isInvInvariant_of_isMulRightInvariant Z ν
  have hc := sameCentralCharacter_self hπ2
  have h1 : ∀ (φ : smoothVectors (Representation.dual π)) (w : V), ∃ c : ℂ, ∀ (v : V) (ψ : smoothVectors (Representation.dual π)),
      pairing Z ν π π v φ w ψ = c * (ψ : Module.Dual ℂ V) v := by
    intro φ w
    let T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual π)) :=
      LinearMap.mk₂ ℂ (fun v ψ => pairing Z ν π π v φ w ψ)
        (fun v₁ v₂ ψ => pairing_add_left hπ2 hπ2 hc hπ.1 hπ.1 v₁ v₂ φ w ψ)
        (fun c v ψ => by rw [smul_eq_mul]; exact pairing_smul_left c v φ w ψ)
        (fun v ψ₁ ψ₂ => pairing_add_right hπ2 hπ2 hc hπ.1 hπ.1 v φ w ψ₁ ψ₂)
        (fun c v ψ => by rw [smul_eq_mul]; exact pairing_smul_right c v φ w ψ)
    exact exists_smul_of_intertwining hπ T fun h v ψ => pairing_apply_left hc h v φ w ψ
  have h2 : ∀ (v : V) (ψ : smoothVectors (Representation.dual π)), ∃ c : ℂ, ∀ (w : V) (φ : smoothVectors (Representation.dual π)),
      pairing Z ν π π v φ w ψ = c * (φ : Module.Dual ℂ V) w := by
    intro v ψ
    let T : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual π)) :=
      LinearMap.mk₂ ℂ (fun w φ => pairing Z ν π π v φ w ψ)
        (fun w₁ w₂ φ => pairing_add_w hπ2 hπ2 hc hπ.1 hπ.1 v φ w₁ w₂ ψ)
        (fun c w φ => by rw [smul_eq_mul]; exact pairing_smul_w c v φ w ψ)
        (fun w φ₁ φ₂ => pairing_add_φ hπ2 hπ2 hc hπ.1 hπ.1 v φ₁ φ₂ w ψ)
        (fun c w φ => by rw [smul_eq_mul]; exact pairing_smul_φ c v φ w ψ)
    exact exists_smul_of_intertwining hπ T fun h w φ => pairing_apply_w hc h v φ w ψ
  obtain ⟨v₀, ψ₀, h₀⟩ := exists_dual_apply_eq_one hπ.1
  obtain ⟨k, hk⟩ := h2 v₀ ψ₀
  refine ⟨k, fun v φ w ψ => ?_⟩
  obtain ⟨c, hcφw⟩ := h1 φ w
  have hck : c = k * (φ : Module.Dual ℂ V) w := by
    have := hcφw v₀ ψ₀
    rw [h₀, mul_one] at this
    rw [← this, hk]
  rw [hcφw, hck]
  ring

end Main

section Hermitian

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

variable (Z ν π) in

def herm (φ₀ : Module.Dual ℂ V) (v w : V) : ℂ :=
  ∫ q : G ⧸ Z, φ₀ (π q.out v) * conj (φ₀ (π q.out w)) ∂ν

/- English proof (translation)
Introduce `g z hz`. Take `⟨c, hc1, hc⟩` from `hπ2.1 z hz`. Simplify using `only [map_mul, Module.End.mul_apply, hc, map_smul, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.mul_conj', hc1]`.

Simplify using the standard rewrite rules.
-/
theorem herm_integrand_mul_mem (hπ2 : IsSquareIntegrable Z ν π) (φ₀ : Module.Dual ℂ V)
    (v w : V) : ∀ g, ∀ z ∈ Z, φ₀ (π (g * z) v) * conj (φ₀ (π (g * z) w)) =
      φ₀ (π g v) * conj (φ₀ (π g w)) := by
  intro g z hz
  obtain ⟨c, hc1, hc⟩ := hπ2.1 z hz
  simp only [map_mul, Module.End.mul_apply, hc, map_smul, smul_eq_mul]
  calc c * φ₀ (π g v) * (conj c * conj (φ₀ (π g w)))
      = (c * conj c) * (φ₀ (π g v) * conj (φ₀ (π g w))) := by ring
    _ = φ₀ (π g v) * conj (φ₀ (π g w)) := by
        rw [Complex.mul_conj', hc1]
        simp

/- English proof (translation)
Establish `hprod` using `(hπ2.2 v φ₀).integrable_mul (hπ2.2 w φ₀)`. Use `hprod.mono' ?_ (ae_of_all _ fun q => ?_)` and prove the remaining obligations. Conclude with `(continuous_apply_out (herm_integrand_mul_mem hπ2 φ₀ v w) ((continuous_dual_orbit (hπs v) _).mul (Complex.continuous_conj.comp (continuous_dual_orbit (hπs w) _)))).aestronglyMeasurable`. Simplify using `only [norm_mul, Complex.norm_conj, Pi.mul_apply, le_refl]`.
-/
theorem integrable_herm (hπ2 : IsSquareIntegrable Z ν π) (hπs : IsSmooth π)
    (φ₀ : smoothVectors (Representation.dual π)) (v w : V) :
    Integrable (fun q : G ⧸ Z => (φ₀ : Module.Dual ℂ V) (π q.out v) *
      conj ((φ₀ : Module.Dual ℂ V) (π q.out w))) ν := by
  have hprod := (hπ2.2 v φ₀).integrable_mul (hπ2.2 w φ₀)
  refine hprod.mono' ?_ (ae_of_all _ fun q => ?_)
  · exact (continuous_apply_out (herm_integrand_mul_mem hπ2 φ₀ v w)
      ((continuous_dual_orbit (hπs v) _).mul
        (Complex.continuous_conj.comp (continuous_dual_orbit (hπs w) _)))).aestronglyMeasurable
  · simp only [norm_mul, Complex.norm_conj, Pi.mul_apply, le_refl]

/- English proof (translation)
Unfold `herm`. Rewrite using `[← integral_add (integrable_herm hπ2 hπs φ₀ v₁ w) (integrable_herm hπ2 hπs φ₀ v₂ w)]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [map_add, add_mul]`.
-/
theorem herm_add_left (hπ2 : IsSquareIntegrable Z ν π) (hπs : IsSmooth π)
    (φ₀ : smoothVectors (Representation.dual π)) (v₁ v₂ w : V) :
    herm Z ν π φ₀ (v₁ + v₂) w = herm Z ν π φ₀ v₁ w + herm Z ν π φ₀ v₂ w := by
  unfold herm
  rw [← integral_add (integrable_herm hπ2 hπs φ₀ v₁ w) (integrable_herm hπ2 hπs φ₀ v₂ w)]
  congr 1
  funext q
  simp only [map_add, add_mul]

/- English proof (translation)
Unfold `herm`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul_left (φ₀ : Module.Dual ℂ V) (c : ℂ) (v w : V) :
    herm Z ν π φ₀ (c • v) w = c * herm Z ν π φ₀ v w := by
  unfold herm
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [map_smul, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `herm`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [map_mul, Complex.conj_conj]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_swap (φ₀ : Module.Dual ℂ V) (v w : V) :
    herm Z ν π φ₀ w v = conj (herm Z ν π φ₀ v w) := by
  unfold herm
  rw [← integral_conj]
  congr 1
  funext q
  simp only [map_mul, Complex.conj_conj]
  ring

/- English proof (translation)
Unfold `herm`. Use `integral_out_mul (ν := ν) (F := fun g => φ₀ (π g v) * conj (φ₀ (π g w))) (herm_integrand_mul_mem hπ2 φ₀ v w) h` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use function extensionality and compare the values at `q`.

Simplify using `only [map_mul, Module.End.mul_apply]`.
-/
theorem herm_apply [ν.IsMulRightInvariant] (hπ2 : IsSquareIntegrable Z ν π)
    (φ₀ : Module.Dual ℂ V) (h : G) (v w : V) :
    herm Z ν π φ₀ (π h v) (π h w) = herm Z ν π φ₀ v w := by
  unfold herm
  have := integral_out_mul (ν := ν) (F := fun g => φ₀ (π g v) * conj (φ₀ (π g w)))
    (herm_integrand_mul_mem hπ2 φ₀ v w) h
  rw [← this]
  congr 1
  funext q
  simp only [map_mul, Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[integral_pos_iff_support_of_nonneg (fun q => hnn _) hint]`. Use `(continuous_apply_out hF hFc).isOpen_support.measure_pos ν ⟨(g₀ : G ⧸ Z), ?_⟩` and prove the remaining obligations. Rewrite using `[mem_support, apply_out_mk hF]`. Conclude with `hpos.ne'`.
-/
theorem integral_pos_of_apply_pos [ν.IsOpenPosMeasure] {F : G → ℝ}
    (hF : ∀ g, ∀ z ∈ Z, F (g * z) = F g) (hFc : Continuous F) (hnn : ∀ g, 0 ≤ F g)
    (hint : Integrable (fun q : G ⧸ Z => F q.out) ν) {g₀ : G} (hpos : 0 < F g₀) :
    0 < ∫ q : G ⧸ Z, F q.out ∂ν := by
  rw [integral_pos_iff_support_of_nonneg (fun q => hnn _) hint]
  refine (continuous_apply_out hF hFc).isOpen_support.measure_pos ν ⟨(g₀ : G ⧸ Z), ?_⟩
  rw [mem_support, apply_out_mk hF]
  exact hpos.ne'

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Set `S : Subrepresentation π` to `⟨⨅ g, LinearMap.ker (φ₀ ∘ₗ π g), fun h x hx => by`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, comp_apply] at hx ⊢`. Introduce `g`.

Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `hx _⟩`. Establish `hvS : v ∈ S.toSubmodule`. Simplify using `only [S, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, comp_apply]`. Conclude with `h`.

Break down `IsSimpleOrder.eq_bot_or_eq_top S with hS | hS` into its components or cases. Apply `hv` to reduce the goal to its premises. Rewrite `hvS` using `[hS]`. Conclude with `(Submodule.mem_bot ℂ).1 hvS`. Apply `hφ` to reduce the goal to its premises.

Use extensionality with `x`. Establish `hx : x ∈ S.toSubmodule` using `by rw [hS]; exact Submodule.mem_top`. Simplify using `only [S, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, comp_apply] at hx`. Simplify using `using hx 1`.
-/
theorem exists_apply_ne_zero [π.IsIrreducible] {v : V} (hv : v ≠ 0) {φ₀ : Module.Dual ℂ V}
    (hφ : φ₀ ≠ 0) : ∃ g, φ₀ (π g v) ≠ 0 := by
  by_contra h
  push Not at h
  let S : Subrepresentation π := ⟨⨅ g, LinearMap.ker (φ₀ ∘ₗ π g), fun h x hx => by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, comp_apply] at hx ⊢
    intro g
    rw [← Module.End.mul_apply, ← map_mul]
    exact hx _⟩
  have hvS : v ∈ S.toSubmodule := by
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, comp_apply]
    exact h
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
  · apply hv
    rw [hS] at hvS
    exact (Submodule.mem_bot ℂ).1 hvS
  · apply hφ
    ext x
    have hx : x ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, comp_apply] at hx
    simpa using hx 1

/- English proof (translation)
Unfold `herm`. Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Rewrite using `[Complex.mul_conj']`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem herm_self (φ₀ : Module.Dual ℂ V) (v : V) :
    herm Z ν π φ₀ v v = ((∫ q : G ⧸ Z, ‖φ₀ (π q.out v)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
  unfold herm
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  rw [Complex.mul_conj']
  push_cast
  rfl

/- English proof (translation)
Take `⟨g₀, hg₀⟩` from `exists_apply_ne_zero (π := π) hv hφ`. Use `integral_pos_of_apply_pos (F := fun g => ‖(φ₀ : Module.Dual ℂ V) (π g v)‖ ^ 2) (fun g z hz => by simp only [norm_coeff_mul_mem hπ2.1 v _ g z hz]) (by` and prove the remaining obligations. Conclude with `((continuous_dual_orbit (hπs v) _).norm).pow 2) (fun g => by positivity)`. Use the proof step `((hπ2.2 v φ₀).integrable_sq) (g₀ := g₀) (by positivity)`.
-/
theorem integral_herm_self_pos [ν.IsOpenPosMeasure] [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) (hπs : IsSmooth π)
    (φ₀ : smoothVectors (Representation.dual π)) (hφ : (φ₀ : Module.Dual ℂ V) ≠ 0) {v : V}
    (hv : v ≠ 0) : 0 < ∫ q : G ⧸ Z, ‖(φ₀ : Module.Dual ℂ V) (π q.out v)‖ ^ 2 ∂ν := by
  obtain ⟨g₀, hg₀⟩ := exists_apply_ne_zero (π := π) hv hφ
  refine integral_pos_of_apply_pos (F := fun g => ‖(φ₀ : Module.Dual ℂ V) (π g v)‖ ^ 2)
    (fun g z hz => by simp only [norm_coeff_mul_mem hπ2.1 v _ g z hz]) (by
      exact ((continuous_dual_orbit (hπs v) _).norm).pow 2) (fun g => by positivity)
    ((hπ2.2 v φ₀).integrable_sq) (g₀ := g₀) (by positivity)

end Hermitian

section Theorems

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

/- English proof (translation)
Use `isInvInvariant_of_isMulRightInvariant Z ν` as an intermediate fact. Take `⟨k, hk⟩` from `exists_pairing_eq hπ hπ2`. Take `⟨u, ψ₀, h₀⟩` from `exists_dual_apply_eq_one hπ.1`. Establish `hψ₀ : (ψ₀ : Module.Dual ℂ V) ≠ 0` using `fun h => by`. Rewrite `h₀` using `[h]`.

Simplify using `at h₀`. Establish `hu : u ≠ 0` using `fun h => by`. Rewrite `h₀` using `[h, map_zero]`. Conclude with `zero_ne_one h₀`. Use `set s := ∫ q : G ⧸ Z, ‖(ψ₀ : Module.Dual ℂ V) (π q.out u)‖ ^ 2 ∂ν with hs_def`.

Establish `hs : 0 < s` using `integral_herm_self_pos hπ2 hπ.1 ψ₀ hψ₀ hu`. Establish `hself : herm Z ν π ψ₀ u u = (s : ℂ)` using `herm_self _ u`. Set `Lₗ : Module.Dual ℂ V` to `{ toFun := fun x => herm Z ν π ψ₀ x u map_add' := fun x y => herm_add_left hπ2 hπ.1 ψ₀ x y u map_smul' := fun c x => herm_smul_left _ c x u }`. Establish `hLs : Lₗ ∈ smoothVectors (Representation.dual π)`. Use `Subgroup.isOpen_mono (H₁ := stabilizerOf π u) (fun h hh => ?_) (hπ.1 u)` and prove the remaining obligations.

Rewrite `hh`, the goal using `[mem_stabilizerOf]`. Establish `hh' : π h⁻¹ u = u` using `by conv_lhs => rw [← hh]`. Conclude with `rep_inv_apply_apply π h u`. Use extensionality with `x`. Rewrite using `[dual_apply_apply]`.

Express the relevant statement in the definitionally equal form `herm Z ν π ψ₀ (π h⁻¹ x) u = herm Z ν π ψ₀ x u`. Use `conv_lhs => rw [← hh']`. Conclude with `herm_apply hπ2 _ h⁻¹ x u`. Set `L : smoothVectors (Representation.dual π)` to `⟨Lₗ, hLs⟩`. Establish `hL : ∀ x, (L : Module.Dual ℂ V) x = herm Z ν π ψ₀ x u` using `fun _ => rfl`.

Establish `hpt : ∀ g : G, coeffProd π π u L u L g = ((‖herm Z ν π ψ₀ (π g u) u‖ ^ 2 : ℝ) : ℂ)`. Introduce `g`. Simplify using `only [coeffProd, hL]`. Establish `hinv : herm Z ν π ψ₀ (π g⁻¹ u) u = conj (herm Z ν π ψ₀ (π g u) u)`. Rewrite using `[← herm_apply hπ2 _ g (π g⁻¹ u) u, rep_apply_inv_apply, herm_swap]`.

Rewrite using `[hinv, Complex.mul_conj']`. Use `push_cast`. Both sides reduce to the same expression. Use `set r := ∫ q : G ⧸ Z, ‖herm Z ν π ψ₀ (π q.out u) u‖ ^ 2 ∂ν with hr_def`. Establish `hint` using `integrable_coeffProd hπ2 hπ2 (sameCentralCharacter_self hπ2) hπ.1 hπ.1 u L u L`.

Establish `hP : pairing Z ν π π u L u L = (r : ℂ)`. Unfold `pairing`. Simplify using `only [hpt]`. Conclude with `integral_complex_ofReal`. Establish `hr : 0 < r`.

Use `integral_pos_of_apply_pos (F := fun g => ‖herm Z ν π ψ₀ (π g u) u‖ ^ 2) ?_ ?_ (fun g => by positivity) ?_ (g₀ := 1) ?_` and prove the remaining obligations. Introduce `g z hz`. Take `⟨c, hc1, hc⟩` from `hπ2.1 z hz`. Simplify using `only [map_mul, Module.End.mul_apply, hc, map_smul]`. Rewrite using `[herm_smul_left, norm_mul, hc1, one_mul]`.

Conclude with `((continuous_dual_orbit (hπ.1 u) (L : Module.Dual ℂ V)).norm).pow 2`. Use `hint.re` as an intermediate fact. Simplify `this` using `only [hpt, RCLike.re_to_complex, Complex.ofReal_re]`. Simplify using `only [map_one, Module.End.one_apply]`. Rewrite using `[hself, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `pow_pos (abs_pos.2 hs.ne') 2`. Establish `hkval : k * ((s : ℂ) * s) = r`. Rewrite using `[← hP, hk, hL, hself]`. Establish `hss : (s : ℂ) * s ≠ 0` using `by exact_mod_cast (mul_pos hs hs).ne'`. Establish `hk' : k = (r : ℂ) / ((s : ℂ) * s)` using `by rw [eq_div_iff hss, hkval]`.

Use `⟨s * s / r, by positivity, fun v φ w ψ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pairing Z ν π π v φ w ψ = _`. Rewrite using `[hk, hk']`. Use `push_cast`. Rewrite using `[inv_div]`.
-/
theorem schur_orthogonality (hπ : IsAdmissible π) [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) :
    ∃ d : ℝ, 0 < d ∧ ∀ (v : V) (φ : smoothVectors (Representation.dual π)) (w : V)
      (ψ : smoothVectors (Representation.dual π)),
      ∫ q : G ⧸ Z, (φ : Module.Dual ℂ V) (π q.out v) * (ψ : Module.Dual ℂ V) (π q.out⁻¹ w) ∂ν =
        (d : ℂ)⁻¹ * ((φ : Module.Dual ℂ V) w * (ψ : Module.Dual ℂ V) v) := by
  have := isInvInvariant_of_isMulRightInvariant Z ν
  obtain ⟨k, hk⟩ := exists_pairing_eq hπ hπ2
  obtain ⟨u, ψ₀, h₀⟩ := exists_dual_apply_eq_one hπ.1
  have hψ₀ : (ψ₀ : Module.Dual ℂ V) ≠ 0 := fun h => by
    rw [h] at h₀
    simp at h₀
  have hu : u ≠ 0 := fun h => by
    rw [h, map_zero] at h₀
    exact zero_ne_one h₀
  set s := ∫ q : G ⧸ Z, ‖(ψ₀ : Module.Dual ℂ V) (π q.out u)‖ ^ 2 ∂ν with hs_def
  have hs : 0 < s := integral_herm_self_pos hπ2 hπ.1 ψ₀ hψ₀ hu
  have hself : herm Z ν π ψ₀ u u = (s : ℂ) := herm_self _ u
  let Lₗ : Module.Dual ℂ V :=
    { toFun := fun x => herm Z ν π ψ₀ x u
      map_add' := fun x y => herm_add_left hπ2 hπ.1 ψ₀ x y u
      map_smul' := fun c x => herm_smul_left _ c x u }
  have hLs : Lₗ ∈ smoothVectors (Representation.dual π) := by
    refine Subgroup.isOpen_mono (H₁ := stabilizerOf π u) (fun h hh => ?_) (hπ.1 u)
    rw [mem_stabilizerOf] at hh ⊢
    have hh' : π h⁻¹ u = u := by
      conv_lhs => rw [← hh]
      exact rep_inv_apply_apply π h u
    ext x
    rw [dual_apply_apply]
    change herm Z ν π ψ₀ (π h⁻¹ x) u = herm Z ν π ψ₀ x u
    conv_lhs => rw [← hh']
    exact herm_apply hπ2 _ h⁻¹ x u
  let L : smoothVectors (Representation.dual π) := ⟨Lₗ, hLs⟩
  have hL : ∀ x, (L : Module.Dual ℂ V) x = herm Z ν π ψ₀ x u := fun _ => rfl
  have hpt : ∀ g : G, coeffProd π π u L u L g = ((‖herm Z ν π ψ₀ (π g u) u‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coeffProd, hL]
    have hinv : herm Z ν π ψ₀ (π g⁻¹ u) u = conj (herm Z ν π ψ₀ (π g u) u) := by
      rw [← herm_apply hπ2 _ g (π g⁻¹ u) u, rep_apply_inv_apply, herm_swap]
    rw [hinv, Complex.mul_conj']
    push_cast
    rfl
  set r := ∫ q : G ⧸ Z, ‖herm Z ν π ψ₀ (π q.out u) u‖ ^ 2 ∂ν with hr_def
  have hint := integrable_coeffProd hπ2 hπ2 (sameCentralCharacter_self hπ2) hπ.1 hπ.1 u L u L
  have hP : pairing Z ν π π u L u L = (r : ℂ) := by
    unfold pairing
    simp only [hpt]
    exact integral_complex_ofReal
  have hr : 0 < r := by
    refine integral_pos_of_apply_pos (F := fun g => ‖herm Z ν π ψ₀ (π g u) u‖ ^ 2) ?_ ?_
      (fun g => by positivity) ?_ (g₀ := 1) ?_
    · intro g z hz
      obtain ⟨c, hc1, hc⟩ := hπ2.1 z hz
      simp only [map_mul, Module.End.mul_apply, hc, map_smul]
      rw [herm_smul_left, norm_mul, hc1, one_mul]
    · exact ((continuous_dual_orbit (hπ.1 u) (L : Module.Dual ℂ V)).norm).pow 2
    · have := hint.re
      simpa only [hpt, RCLike.re_to_complex, Complex.ofReal_re] using this
    · simp only [map_one, Module.End.one_apply]
      rw [hself, Complex.norm_real, Real.norm_eq_abs]
      exact pow_pos (abs_pos.2 hs.ne') 2
  have hkval : k * ((s : ℂ) * s) = r := by
    rw [← hP, hk, hL, hself]
  have hss : (s : ℂ) * s ≠ 0 := by exact_mod_cast (mul_pos hs hs).ne'
  have hk' : k = (r : ℂ) / ((s : ℂ) * s) := by rw [eq_div_iff hss, hkval]
  refine ⟨s * s / r, by positivity, fun v φ w ψ => ?_⟩
  change pairing Z ν π π v φ w ψ = _
  rw [hk, hk']
  push_cast
  rw [inv_div]

open Classical in
variable (ν π) in

def formalDegree : ℝ :=
  if h : ∃ d : ℝ, 0 < d ∧ ∀ (v : V) (φ : smoothVectors (Representation.dual π)) (w : V)
      (ψ : smoothVectors (Representation.dual π)),
      ∫ q : G ⧸ Z, (φ : Module.Dual ℂ V) (π q.out v) * (ψ : Module.Dual ℂ V) (π q.out⁻¹ w) ∂ν =
        (d : ℂ)⁻¹ * ((φ : Module.Dual ℂ V) w * (ψ : Module.Dual ℂ V) v) then h.choose else 0

/- English proof (translation)
Establish `h` using `schur_orthogonality hπ hπ2`. Rewrite using `[formalDegree, dif_pos h]`. Conclude with `h.choose_spec.1`.
-/
theorem formalDegree_pos (hπ : IsAdmissible π) [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) : 0 < formalDegree ν π := by
  have h := schur_orthogonality hπ hπ2
  rw [formalDegree, dif_pos h]
  exact h.choose_spec.1

/- English proof (translation)
Establish `h` using `schur_orthogonality hπ hπ2`. Rewrite using `[formalDegree, dif_pos h]`. Conclude with `h.choose_spec.2 v φ w ψ`.
-/
theorem integral_eq_formalDegree (hπ : IsAdmissible π) [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) (v : V) (φ : smoothVectors (Representation.dual π)) (w : V)
    (ψ : smoothVectors (Representation.dual π)) :
    ∫ q : G ⧸ Z, (φ : Module.Dual ℂ V) (π q.out v) * (ψ : Module.Dual ℂ V) (π q.out⁻¹ w) ∂ν =
      (formalDegree ν π : ℂ)⁻¹ * ((φ : Module.Dual ℂ V) w * (ψ : Module.Dual ℂ V) v) := by
  have h := schur_orthogonality hπ hπ2
  rw [formalDegree, dif_pos h]
  exact h.choose_spec.2 v φ w ψ

/- English proof (translation)
Take `⟨v₀, ψ₀, h₀⟩` from `exists_dual_apply_eq_one hπ.1`. Establish `h1` using `hd v₀ ψ₀ v₀ ψ₀`. Establish `h2` using `integral_eq_formalDegree hπ hπ2 v₀ ψ₀ v₀ ψ₀`. Rewrite `h1`, `h2` using `[h₀, mul_one, mul_one]`. Establish `h3 : (d : ℂ)⁻¹ = (formalDegree ν π : ℂ)⁻¹` using `h1.symm.trans h2`.

Conclude with `inv_injective h3` after adjusting the coercions.
-/
theorem eq_formalDegree (hπ : IsAdmissible π) [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) (d : ℝ)
    (hd : ∀ (v : V) (φ : smoothVectors (Representation.dual π)) (w : V)
      (ψ : smoothVectors (Representation.dual π)),
      ∫ q : G ⧸ Z, (φ : Module.Dual ℂ V) (π q.out v) * (ψ : Module.Dual ℂ V) (π q.out⁻¹ w) ∂ν =
        (d : ℂ)⁻¹ * ((φ : Module.Dual ℂ V) w * (ψ : Module.Dual ℂ V) v)) :
    d = formalDegree ν π := by
  obtain ⟨v₀, ψ₀, h₀⟩ := exists_dual_apply_eq_one hπ.1
  have h1 := hd v₀ ψ₀ v₀ ψ₀
  have h2 := integral_eq_formalDegree hπ hπ2 v₀ ψ₀ v₀ ψ₀
  rw [h₀, mul_one, mul_one] at h1 h2
  have h3 : (d : ℂ)⁻¹ = (formalDegree ν π : ℂ)⁻¹ := h1.symm.trans h2
  exact_mod_cast inv_injective h3

/- English proof (translation)
Take `⟨u, ψ₀, h₀⟩` from `exists_dual_apply_eq_one hπ.1`. Establish `hψ₀ : (ψ₀ : Module.Dual ℂ V) ≠ 0` using `fun h => by`. Rewrite `h₀` using `[h]`. Simplify using `at h₀`. Use `⟨herm Z ν π ψ₀, herm_add_left hπ2 hπ.1 ψ₀, herm_smul_left _, herm_swap _, herm_apply hπ2 _, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[herm_self, Complex.ofReal_re, Complex.ofReal_im]`. Conclude with `⟨integral_herm_self_pos hπ2 hπ.1 ψ₀ hψ₀ hv, rfl⟩`.
-/
theorem exists_invariant_hermitian (hπ : IsAdmissible π) [π.IsIrreducible]
    (hπ2 : IsSquareIntegrable Z ν π) :
    ∃ B : V → V → ℂ, (∀ v₁ v₂ w, B (v₁ + v₂) w = B v₁ w + B v₂ w) ∧
      (∀ (c : ℂ) v w, B (c • v) w = c * B v w) ∧ (∀ v w, B w v = conj (B v w)) ∧
      (∀ h v w, B (π h v) (π h w) = B v w) ∧ ∀ v, v ≠ 0 → 0 < (B v v).re ∧ (B v v).im = 0 := by
  obtain ⟨u, ψ₀, h₀⟩ := exists_dual_apply_eq_one hπ.1
  have hψ₀ : (ψ₀ : Module.Dual ℂ V) ≠ 0 := fun h => by
    rw [h] at h₀
    simp at h₀
  refine ⟨herm Z ν π ψ₀, herm_add_left hπ2 hπ.1 ψ₀, herm_smul_left _, herm_swap _,
    herm_apply hπ2 _, fun v hv => ?_⟩
  rw [herm_self, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨integral_herm_self_pos hπ2 hπ.1 ψ₀ hψ₀ hv, rfl⟩

end Theorems

end SchurOrthogonality

end GroundTheory.Automorphic
