import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Establish `hlc : IsLocallyConstant f`. Use `(IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_` and prove the remaining obligations. Establish `ho : IsOpen {g : G | rightReg ℂ G Y g f = f}` using `hf`. Establish `hc : Continuous fun y : G => x⁻¹ * y` using `by fun_prop`. Establish `: (fun y : G => x⁻¹ * y) ⁻¹' {g : G | rightReg ℂ G Y g f = f} ∈ nhds x` using `(ho.preimage hc).mem_nhds (by simp)`.

Use `filter_upwards [this] with y hy`. Establish `h2 : f (x * (x⁻¹ * y)) = f x` using `congrFun hy x`. Simplify using `using h2`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Use `(hlc.comp_continuous (continuous_subtype_val (p := (· ∈ K)))).range_finite` as an intermediate fact.

Rewrite `this` using `[Set.range_comp, Subtype.range_coe_subtype]`. Then use the resulting hypothesis.
-/
private theorem finite_image {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Y] [Module ℂ Y]
    (f : G → Y) (hf : f ∈ GlobalTheory.PRep.smoothPart (rightReg ℂ G Y)) (K : Set G) (hK : IsCompact K) : (f '' K).Finite := by
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have ho : IsOpen {g : G | rightReg ℂ G Y g f = f} := hf
    have hc : Continuous fun y : G => x⁻¹ * y := by fun_prop
    have : (fun y : G => x⁻¹ * y) ⁻¹' {g : G | rightReg ℂ G Y g f = f} ∈ nhds x :=
      (ho.preimage hc).mem_nhds (by simp)
    filter_upwards [this] with y hy
    have h2 : f (x * (x⁻¹ * y)) = f x := congrFun hy x
    simpa using h2
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have := (hlc.comp_continuous (continuous_subtype_val (p := (· ∈ K)))).range_finite
  rwa [Set.range_comp, Subtype.range_coe_subtype] at this

/- English proof (translation)
Introduce `G _ _ _ Γ _ V _ _ B _ _ P K ρ m hK hPK`. Establish `hact : ∀ (p : P) (v : V) (b : B), ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (v ⊗ₜ[ℂ] b) = ρ p v ⊗ₜ[ℂ] b`. Introduce `p v b`. Simplify using `[extTensor]`. Set `Φ₀ : GlobalTheory.PRep.smoothPart (ind P ρ) →ₗ[ℂ] B →ₗ[ℂ] IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤` to `LinearMap.mk₂ ℂ (fun a b => ⟨fun g => a.1.1 g ⊗ₜ[ℂ] b, ⟨fun _ => trivial, fun h g => by`.

Rewrite using `[hact, ← a.1.2 h g]; rfl⟩, by`. Use `GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds a.2 (by simp)) fun u hu => ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `h2 : a.1.1 (x * u) = a.1.1 x` using `congrFun (congrArg Subtype.val hu) x`. Use `show a.1.1 (x * u) ⊗ₜ[ℂ] b = a.1.1 x ⊗ₜ[ℂ] b`.

Rewrite using `[h2]⟩)`. Use the proof step `(fun a a' b => Subtype.ext (funext fun g => TensorProduct.add_tmul _ _ _))`. Use the proof step `(fun c a b => Subtype.ext (funext fun g => (TensorProduct.smul_tmul' _ _ _).symm))`. Use the proof step `(fun a b b' => Subtype.ext (funext fun g => TensorProduct.tmul_add _ _ _))`. Use the proof step `(fun c a b => Subtype.ext (funext fun g => TensorProduct.tmul_smul _ _ _))`.

Set `Φ` to `TensorProduct.lift Φ₀`. Establish `hΦ : ∀ a b g, (Φ (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ[ℂ] b` using `fun a b g => rfl`. Set `β` to `Module.Basis.ofVectorSpace ℂ B`. Set `ES` to `TensorProduct.equivFinsuppOfBasisRight (M := GlobalTheory.PRep.smoothPart (ind P ρ)) β`. Set `EV` to `TensorProduct.equivFinsuppOfBasisRight (M := V) β`.

Establish `key : ∀ x i g, (ES x i).1.1 g = EV ((Φ x).1 g) i`. Introduce `x i g`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`.

Rewrite using `[hΦ]`. Simplify using `only [ES, EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp [hx, hy]`. Establish `hEV : ∀ (p : P) y i, EV (((extTensor ρ m).comp (MonoidHom.inl P Γ)) p y) i = ρ p (EV y i)`.

Introduce `p y i`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[hact]`.

Simplify using `only [EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Use `⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩, hΦ⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero Φ).2 fun x hx => ?_` and prove the remaining obligations. Apply `ES.injective` to reduce the goal to its premises.

Use extensionality with `i g`. Rewrite using `[key, hx]`. Simplify using the standard rewrite rules. Introduce `f`. Establish `hlaw : ∀ (p : P) g, f.1 (p * g) = ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (f.1 g)` using `f.2.1.2`.

Set `c : _ → GlobalTheory.PRep.smoothPart (ind P ρ)` to `fun i => ⟨⟨fun g => EV (f.1 g) i, fun h g => by show EV (f.1 (h * g)) i = _`. Rewrite using `[hlaw, hEV]⟩, by`. Use `GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2.2 (by simp)) fun u hu => ?_)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Establish `h2 : f.1 (x * u) = f.1 x` using `congrFun hu x`. Use `show EV (f.1 (x * u)) i = EV (f.1 x) i`. Rewrite using `[h2]⟩`. Establish `hfin : (Function.support c).Finite`. Use `((finite_image f.1 f.2.2 K hK.1).biUnion (t := fun y => ((EV y).support : Set _)) fun y _ => Finset.finite_toSet _).subset fun i hi => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Apply `hi` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Take `⟨p, hp, k, hk, rfl⟩` from `hPK g`. Establish `h0 : EV (f.1 k) i = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hn (Set.mem_biUnion ⟨k, hk, rfl⟩ (Finsupp.mem_support_iff.2 h0))`. Use `show EV (f.1 (p * k)) i = 0`.

Rewrite using `[hlaw ⟨p, hp⟩ k, hEV, h0, map_zero]`. Use `⟨ES.symm (Finsupp.ofSupportFinite c hfin), Subtype.ext (funext fun g => EV.injective ?_)⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[← key, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indTens :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (P K : Subgroup G) (ρ : Representation ℂ P V) (m : Representation ℂ Γ B), CO K →
      (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
      ∃ e : smoothPart (ind P ρ) ⊗[ℂ] B ≃ₗ[ℂ] IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤,
        ∀ a b g, (e (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ b := by
  intro G _ _ _ Γ _ V _ _ B _ _ P K ρ m hK hPK
  have hact : ∀ (p : P) (v : V) (b : B),
      ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (v ⊗ₜ[ℂ] b) = ρ p v ⊗ₜ[ℂ] b := by
    intro p v b
    simp [extTensor]
  let Φ₀ : GlobalTheory.PRep.smoothPart (ind P ρ) →ₗ[ℂ] B →ₗ[ℂ]
      IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ :=
    LinearMap.mk₂ ℂ (fun a b => ⟨fun g => a.1.1 g ⊗ₜ[ℂ] b, ⟨fun _ => trivial, fun h g => by
        rw [hact, ← a.1.2 h g]; rfl⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds a.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : a.1.1 (x * u) = a.1.1 x := congrFun (congrArg Subtype.val hu) x
        show a.1.1 (x * u) ⊗ₜ[ℂ] b = a.1.1 x ⊗ₜ[ℂ] b
        rw [h2]⟩)
      (fun a a' b => Subtype.ext (funext fun g => TensorProduct.add_tmul _ _ _))
      (fun c a b => Subtype.ext (funext fun g => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun a b b' => Subtype.ext (funext fun g => TensorProduct.tmul_add _ _ _))
      (fun c a b => Subtype.ext (funext fun g => TensorProduct.tmul_smul _ _ _))
  let Φ := TensorProduct.lift Φ₀
  have hΦ : ∀ a b g, (Φ (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ[ℂ] b := fun a b g => rfl
  let β := Module.Basis.ofVectorSpace ℂ B
  let ES := TensorProduct.equivFinsuppOfBasisRight (M := GlobalTheory.PRep.smoothPart (ind P ρ)) β
  let EV := TensorProduct.equivFinsuppOfBasisRight (M := V) β
  have key : ∀ x i g, (ES x i).1.1 g = EV ((Φ x).1 g) i := by
    intro x i g
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hΦ]
      simp only [ES, EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      rfl
    | add x y hx hy => simp [hx, hy]
  have hEV : ∀ (p : P) y i, EV (((extTensor ρ m).comp (MonoidHom.inl P Γ)) p y) i = ρ p (EV y i) := by
    intro p y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hact]
      simp only [EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩, hΦ⟩
  · refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    apply ES.injective
    ext i g
    rw [key, hx]
    simp
  · intro f
    have hlaw : ∀ (p : P) g, f.1 (p * g) = ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (f.1 g) := f.2.1.2
    let c : _ → GlobalTheory.PRep.smoothPart (ind P ρ) := fun i =>
      ⟨⟨fun g => EV (f.1 g) i, fun h g => by
          show EV (f.1 (h * g)) i = _
          rw [hlaw, hEV]⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2.2 (by simp)) fun u hu => ?_)
        apply Subtype.ext
        funext x
        have h2 : f.1 (x * u) = f.1 x := congrFun hu x
        show EV (f.1 (x * u)) i = EV (f.1 x) i
        rw [h2]⟩
    have hfin : (Function.support c).Finite := by
      refine ((finite_image f.1 f.2.2 K hK.1).biUnion (t := fun y => ((EV y).support : Set _))
        fun y _ => Finset.finite_toSet _).subset fun i hi => ?_
      by_contra hn
      apply hi
      apply Subtype.ext
      apply Subtype.ext
      funext g
      obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
      have h0 : EV (f.1 k) i = 0 := by
        by_contra h0
        exact hn (Set.mem_biUnion ⟨k, hk, rfl⟩ (Finsupp.mem_support_iff.2 h0))
      show EV (f.1 (p * k)) i = 0
      rw [hlaw ⟨p, hp⟩ k, hEV, h0, map_zero]
    refine ⟨ES.symm (Finsupp.ofSupportFinite c hfin), Subtype.ext (funext fun g => EV.injective ?_)⟩
    ext i
    rw [← key, LinearEquiv.apply_symm_apply]
    rfl
