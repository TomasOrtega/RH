import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomConjOfTraceEqHarrisTaylorOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomMatrixLiftOfOrderActionExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwiningStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Unif

/- English proof (translation)
Take `⟨w, hw⟩` from `hsurj (toUnit _ ≫ lv a)`. Establish `hepow : ∀ n : ℕ, e (n • w) = e w ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Establish `h0` using `hadd 0 0`. Rewrite `h0` using `[add_zero]`. Simplify using `using (mul_eq_left.mp h0.symm)`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Establish `hlvpow : ∀ n : ℕ, lv (n • a) = lv a ^ n`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Establish `h0` using `hlv 0 0`. Rewrite `h0` using `[add_zero]`.

Simplify using `using (mul_eq_left.mp h0.symm)`. Consider the case `succ n ih => rw [succ_nsmul, hlv, ih, pow_succ]`. Use `⟨N • w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hepow, hw, ← comp_pow, ← hlvpow, hker, comp_one]`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`.

Rewrite using `[← hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN', one_smul]`.
-/
theorem eta_points {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {g : ℕ} {y : Sp ℂ ⟶ S}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {Λ' : Type} [AddCommGroup Λ'] {lv : Λ' → (𝟙_ (Over S) ⟶ G)} {N : ℕ}
    (hN : 0 < N) (hadd : ∀ z w, e (z + w) = e z * e w) (hsurj : Function.Surjective e)
    (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hker : ∀ x, lv (N • x) = 1) (a : Λ') :
    ∃ z, e z = 1 ∧ toUnit _ ≫ lv a = e ((N : ℂ)⁻¹ • z) := by
  obtain ⟨w, hw⟩ := hsurj (toUnit _ ≫ lv a)
  have hepow : ∀ n : ℕ, e (n • w) = e w ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hadd 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hlvpow : ∀ n : ℕ, lv (n • a) = lv a ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hlv 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hlv, ih, pow_succ]
  refine ⟨N • w, ?_, ?_⟩
  · rw [hepow, hw, ← comp_pow, ← hlvpow, hker, comp_one]
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN', one_smul]

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `hU`. Establish `hc' : ∀ a z, h.symm (ρ₂ a *ᵥ z) = ρ a *ᵥ h.symm z` using `fun a z => by`. Rewrite using `[LinearEquiv.symm_apply_eq, hc, LinearEquiv.apply_symm_apply]`. Establish `hs : ∀ (k : ℂ) x, h.symm (k • h (P x)) = k • P x` using `fun k x => by simp`. Use `⟨h1, GlobalTheory.T.comp_linearEquiv_intertwining O bar D' g ρ ρ₂ P h h2 hc, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.LocLift.IsExp.comp h3 (LinearEquiv.toContinuousLinearEquiv h.symm)`. Introduce `z`. Rewrite using `[h4]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`.

Conclude with `⟨x, by simp [hx]⟩`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, by simp⟩`. Introduce `a z`. Simplify using `only [hc']`.

Conclude with `h5 a _`. Introduce `k a b c hk hcc`. Simplify using `only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]`. Conclude with `h6 k a b c hk hcc`. Introduce `a`.

Simplify using `only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]`. Conclude with `h7 a`.
-/
theorem unifAt_change {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ} {R : Type}
    [CommRing R] {σ : R →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {N : ℕ} {D' : PLat O bar} {t : Λ → D'.La}
    {P : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ F.X} {e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F σ ρ N D' t P y e) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hc : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    UnifAt F σ ρ₂ N D' t (h.toLinearMap.toAddMonoidHom.comp P) y (fun z => e (h.symm z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hU
  have hc' : ∀ a z, h.symm (ρ₂ a *ᵥ z) = ρ a *ᵥ h.symm z := fun a z => by
    rw [LinearEquiv.symm_apply_eq, hc, LinearEquiv.apply_symm_apply]
  have hs : ∀ (k : ℂ) x, h.symm (k • h (P x)) = k • P x := fun k x => by simp
  refine ⟨h1, GlobalTheory.T.comp_linearEquiv_intertwining O bar D' g ρ ρ₂ P h h2 hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.LocLift.IsExp.comp h3 (LinearEquiv.toContinuousLinearEquiv h.symm)
  · intro z
    rw [h4]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simp⟩
  · intro a z
    simp only [hc']
    exact h5 a _
  · intro k a b c hk hcc
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h6 k a b c hk hcc
  · intro a
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h7 a

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hst : ∀ a z, z ∈ Λ → ρ' a *ᵥ z ∈ Λ` using `fun a z hz => by haveI := o.act.hom a`. Rewrite using `[← hk, hρ, (hk z).2 hz]`. Conclude with `one_comp _`. Set `φ : D.O →+* Module.End ℤ Λ` to `{ toFun := fun a => { toFun := fun x => ⟨ρ' a *ᵥ (x : Fin D.g → ℂ), hst a x x.2⟩ map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add]) map_smul' := fun n x => Subtype.ext (by show ρ' a *ᵥ (n • (x : Fin D.g → ℂ)) = n • (ρ' a *ᵥ (x : Fin D.g → ℂ))`. Conclude with `map_zsmul (Matrix.mulVecLin (ρ' a)) n (x : Fin D.g → ℂ)) }`.

Use the proof step `map_one' := by ext x i; simp`. Use the proof step `map_mul' := fun a b => by ext x i; simp [Matrix.mulVec_mulVec]`. Use the proof step `map_zero' := by ext x i; simp`. Use the proof step `map_add' := fun a b => by ext x i; simp [Matrix.add_mulVec] }`. Use `letI : Module D.O Λ := Module.compHom Λ φ`.

Use `haveI : IsZLattice ℝ Λ := ⟨hs⟩`. Set `Q : Λ →+ (Fin D.g → ℂ)` to `Λ.subtype.toAddMonoidHom`. Establish `hQi : Function.Injective Q` using `Subtype.val_injective`. Establish `hQk : ∀ z, e z = 1 ↔ z ∈ Q.range` using `fun z => by`. Rewrite using `[hk]`.

Simplify using `[Q]`. Establish `hQs : Submodule.span ℝ (Set.range Q) = ⊤`. Simplify `hs` using `[Q]`. Take `⟨Hm, EF, hH, hpos, him, hweil⟩` from `GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential (Sp ℂ) o.A D.g o.ab h (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) hL o.ample (𝟙 _) e Λ Q he hQi hQk`. Take `⟨halt, hnd⟩` from `GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice Λ D.g Q Hm EF hQi hQs hH hpos him`.

Establish `hmv : ∀ (a : D.O) (k : ℂ) (z : Fin D.g → ℂ), k • (ρ' a *ᵥ z) = ρ' a *ᵥ (k • z)` using `fun a k z => by`. Rewrite using `[Matrix.mulVec_smul]`. Establish `hadj : ∀ (a : D.O) x y, EF (φ a x) y = EF x (φ (D.inv a) y)`. Introduce `a`. Establish `hu : ∀ (c : D.O) (k : ℕ) (x : Λ), 0 < k → e ((k : ℂ)⁻¹ • Q ((φ c).toAddMonoidHom x)) = e ((k : ℂ)⁻¹ • Q x) ≫ o.act.act c` using `fun c k x _ => by show e ((k : ℂ)⁻¹ • (ρ' c *ᵥ (x : Fin D.g → ℂ))) = _`.

Rewrite using `[hmv, hρ]`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic o.A D.g o.ab h o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample e Λ Q EF he hQi hQk hweil (o.act.act a) (o.act.act (D.star a).unop) (φ a).toAddMonoidHom (φ (D.inv a)).toAddMonoidHom (o.act.hom a) (o.act.hom _) (hu a) (hu ( …`. Conclude with `key.1 (o.rosati a)`. Establish `het : ∀ a : D.La, ∃ z, e z = 1 ∧ toUnit _ ≫ o.eta a = e ((N : ℂ)⁻¹ • z)` using `eta_points hN he.1 he.2.1 o.eta_add o.eta_ker`.

Use `choose tz htz using het`. Set `D' : PLat D.O D.inv` to `{ La := Λ fin := ZLattice.module_finite ℝ Λ free := ZLattice.module_free ℝ Λ EF := EF alt := halt nondeg := hnd adj := fun a x y => hadj a x y }`. Use `⟨D', fun a => (⟨tz a, (hk _).1 (htz a).1⟩ : Λ), Q, Category.id_comp _, ⟨fun a x => rfl, hQi, ?_, hQs, Hm, hH, hpos, him⟩, he, hQk, hρ, hweil, fun a => (htz a).2⟩` and prove the remaining obligations. Establish `: Q.range = Λ.toAddSubgroup` using `by ext; simp [Q]`. Rewrite using `[this]`.

Conclude with `hd`.
-/
theorem exists_unifAt_of_exp (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ)
    (o : Obj b N (spMap σ)) (h : SmoothOfRelativeDimension D.g o.A.hom)
    (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) (hN : 0 < N)
    (ρ' : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ o.A))
    (Λ : Submodule ℤ (Fin D.g → ℂ)) (he : IsExp (𝟙 _) e) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin D.g → ℂ)) = ⊤) (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hρ : ∀ a z, e (ρ' a *ᵥ z) = e z ≫ o.act.act a) :
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ)), UnifAt (o.fam h hL) σ ρ' N D' t Q (𝟙 _) e := by
  have hst : ∀ a z, z ∈ Λ → ρ' a *ᵥ z ∈ Λ := fun a z hz => by
    haveI := o.act.hom a
    rw [← hk, hρ, (hk z).2 hz]
    exact one_comp _
  let φ : D.O →+* Module.End ℤ Λ :=
    { toFun := fun a =>
        { toFun := fun x => ⟨ρ' a *ᵥ (x : Fin D.g → ℂ), hst a x x.2⟩
          map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
          map_smul' := fun n x => Subtype.ext (by
            show ρ' a *ᵥ (n • (x : Fin D.g → ℂ)) = n • (ρ' a *ᵥ (x : Fin D.g → ℂ))
            exact map_zsmul (Matrix.mulVecLin (ρ' a)) n (x : Fin D.g → ℂ)) }
      map_one' := by ext x i; simp
      map_mul' := fun a b => by ext x i; simp [Matrix.mulVec_mulVec]
      map_zero' := by ext x i; simp
      map_add' := fun a b => by ext x i; simp [Matrix.add_mulVec] }
  letI : Module D.O Λ := Module.compHom Λ φ
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let Q : Λ →+ (Fin D.g → ℂ) := Λ.subtype.toAddMonoidHom
  have hQi : Function.Injective Q := Subtype.val_injective
  have hQk : ∀ z, e z = 1 ↔ z ∈ Q.range := fun z => by
    rw [hk]; simp [Q]
  have hQs : Submodule.span ℝ (Set.range Q) = ⊤ := by
    simpa [Q] using hs
  obtain ⟨Hm, EF, hH, hpos, him, hweil⟩ := GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential (Sp ℂ) o.A D.g o.ab h
    (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) hL o.ample (𝟙 _) e Λ Q he hQi hQk
  obtain ⟨halt, hnd⟩ := GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice Λ D.g Q Hm EF hQi hQs hH hpos him
  have hmv : ∀ (a : D.O) (k : ℂ) (z : Fin D.g → ℂ), k • (ρ' a *ᵥ z) = ρ' a *ᵥ (k • z) := fun a k z => by
    rw [Matrix.mulVec_smul]
  have hadj : ∀ (a : D.O) x y, EF (φ a x) y = EF x (φ (D.inv a) y) := by
    intro a
    have hu : ∀ (c : D.O) (k : ℕ) (x : Λ), 0 < k →
        e ((k : ℂ)⁻¹ • Q ((φ c).toAddMonoidHom x)) = e ((k : ℂ)⁻¹ • Q x) ≫ o.act.act c := fun c k x _ => by
      show e ((k : ℂ)⁻¹ • (ρ' c *ᵥ (x : Fin D.g → ℂ))) = _
      rw [hmv, hρ]
      rfl
    have key := GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic o.A D.g o.ab h o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample e Λ Q EF he hQi hQk hweil
      (o.act.act a) (o.act.act (D.star a).unop) (φ a).toAddMonoidHom (φ (D.inv a)).toAddMonoidHom (o.act.hom a)
      (o.act.hom _) (hu a) (hu (D.inv a))
    exact key.1 (o.rosati a)
  have het : ∀ a : D.La, ∃ z, e z = 1 ∧ toUnit _ ≫ o.eta a = e ((N : ℂ)⁻¹ • z) :=
    eta_points hN he.1 he.2.1 o.eta_add o.eta_ker
  choose tz htz using het
  let D' : PLat D.O D.inv :=
    { La := Λ
      fin := ZLattice.module_finite ℝ Λ
      free := ZLattice.module_free ℝ Λ
      EF := EF
      alt := halt
      nondeg := hnd
      adj := fun a x y => hadj a x y }
  refine ⟨D', fun a => (⟨tz a, (hk _).1 (htz a).1⟩ : Λ), Q, Category.id_comp _,
    ⟨fun a x => rfl, hQi, ?_, hQs, Hm, hH, hpos, him⟩, he, hQk, hρ, hweil, fun a => (htz a).2⟩
  have : Q.range = Λ.toAddSubgroup := by ext; simp [Q]
  rw [this]
  exact hd

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

/- English proof (translation)
Introduce `p _ D R _ b N σ ρ o h hL hN hNp hty`. Take `⟨e₀, Λ, hexp, hdisc, hspan, hker⟩` from `GlobalTheory.T.exists_complexFibreExponential_full_lattice (Sp ℂ) o.A D.g o.ab h (𝟙 _)`. Take `⟨ρ', hρ'⟩` from `GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential (Sp ℂ) o.A D.g D.O o.act.act o.ab h o.act.hom o.act.one o.act.mul o.act.add (𝟙 _) e₀ hexp`. Take `⟨D', t, Q, hU⟩` from `exists_unifAt_of_exp D b N σ o h hL hN ρ' e₀ Λ hexp hdisc hspan hker hρ'`. Establish `hty'` using `GlobalTheory.T.lieCondition_uniformisingSpace_isType p D R b N σ ρ' o h hL D' t Q e₀ hU`.

Take `⟨M, hMu, hM⟩` from `GlobalTheory.T.ringHom_conj_of_trace_eq_harrisTaylorOrder p D D.g ρ ρ' (fun c => by rw [hty c, hty' c])`. Use `set u := hMu.unit with hu`. Establish `hM' : ∀ a, ρ' a * (u : Matrix (Fin D.g) (Fin D.g) ℂ) = u * ρ a` using `fun a => by`. Rewrite using `[hu, IsUnit.unit_spec]`. Conclude with `hM a`.

Set `Mi : Matrix (Fin D.g) (Fin D.g) ℂ` to `((u⁻¹ : (Matrix (Fin D.g) (Fin D.g) ℂ)ˣ) : Matrix (Fin D.g) (Fin D.g) ℂ)`. Establish `hinv : ∀ a, Mi * ρ' a = ρ a * Mi` using `fun a => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.mul_inv, _root_.mul_one]`. Use `_ = Mi * (ρ' a * u) * Mi := by simp only [_root_.mul_assoc]`.

Use `_ = Mi * (u * ρ a) * Mi := by rw [hM']`. Use `_ = ρ a * Mi := by rw [← _root_.mul_assoc Mi, Units.inv_mul, _root_.one_mul]`. Set `hl : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)` to `Matrix.toLinearEquiv' Mi (Units.invertible u⁻¹)`. Establish `hc : ∀ a z, hl (ρ' a *ᵥ z) = ρ a *ᵥ hl z` using `fun a z => by show Mi *ᵥ (ρ' a *ᵥ z) = ρ a *ᵥ (Mi *ᵥ z)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]`.

Establish `hU2` using `unifAt_change hU hl hc`. Take `⟨t', hcls, ht'⟩` from `GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class p D R b N σ ρ o h hL D' t _ _ hN hNp hU2`. Establish `hmk : IsMarkedIsom N D' D' t t' (LinearEquiv.refl D.O D'.La)`. Use `⟨fun x y => rfl, fun a => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `ht' a`.

Conclude with `⟨-x, by rw [hx]; simp⟩`. Apply the tactic sequence `exact ⟨D', t', _, _, hcls, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ R σ D.La (o.fam h hL) N D' D' t t' _ _ (𝟙 _) _ (LinearEquiv.refl D.O D'.La) (LinearEquiv.refl ℂ (Fin D.g → ℂ)) hN hU2 hmk (fun x => rfl) hU2.2.1⟩`.
-/
theorem exists_unifAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ o h hL hN hNp hty
  obtain ⟨e₀, Λ, hexp, hdisc, hspan, hker⟩ := GlobalTheory.T.exists_complexFibreExponential_full_lattice (Sp ℂ) o.A D.g o.ab h (𝟙 _)
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential (Sp ℂ) o.A D.g D.O o.act.act o.ab h o.act.hom o.act.one o.act.mul o.act.add (𝟙 _) e₀ hexp
  obtain ⟨D', t, Q, hU⟩ := exists_unifAt_of_exp D b N σ o h hL hN ρ' e₀ Λ hexp hdisc hspan hker hρ'
  have hty' := GlobalTheory.T.lieCondition_uniformisingSpace_isType p D R b N σ ρ' o h hL D' t Q e₀ hU
  obtain ⟨M, hMu, hM⟩ := GlobalTheory.T.ringHom_conj_of_trace_eq_harrisTaylorOrder p D D.g ρ ρ' (fun c => by rw [hty c, hty' c])
  set u := hMu.unit with hu
  have hM' : ∀ a, ρ' a * (u : Matrix (Fin D.g) (Fin D.g) ℂ) = u * ρ a := fun a => by
    rw [hu, IsUnit.unit_spec]; exact hM a
  let Mi : Matrix (Fin D.g) (Fin D.g) ℂ := ((u⁻¹ : (Matrix (Fin D.g) (Fin D.g) ℂ)ˣ) : Matrix (Fin D.g) (Fin D.g) ℂ)
  have hinv : ∀ a, Mi * ρ' a = ρ a * Mi := fun a => by
    calc Mi * ρ' a = Mi * ρ' a * ((u : Matrix (Fin D.g) (Fin D.g) ℂ) * Mi) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = Mi * (ρ' a * u) * Mi := by simp only [_root_.mul_assoc]
      _ = Mi * (u * ρ a) * Mi := by rw [hM']
      _ = ρ a * Mi := by rw [← _root_.mul_assoc Mi, Units.inv_mul, _root_.one_mul]
  let hl : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ) := Matrix.toLinearEquiv' Mi (Units.invertible u⁻¹)
  have hc : ∀ a z, hl (ρ' a *ᵥ z) = ρ a *ᵥ hl z := fun a z => by
    show Mi *ᵥ (ρ' a *ᵥ z) = ρ a *ᵥ (Mi *ᵥ z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]
  have hU2 := unifAt_change hU hl hc
  obtain ⟨t', hcls, ht'⟩ := GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class p D R b N σ ρ o h hL D' t _ _ hN hNp hU2
  have hmk : IsMarkedIsom N D' D' t t' (LinearEquiv.refl D.O D'.La) := by
    refine ⟨fun x y => rfl, fun a => ?_⟩
    obtain ⟨x, hx⟩ := ht' a
    exact ⟨-x, by rw [hx]; simp⟩
  exact ⟨D', t', _, _, hcls, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ R σ D.La (o.fam h hL) N D' D' t t' _ _ (𝟙 _) _
    (LinearEquiv.refl D.O D'.La) (LinearEquiv.refl ℂ (Fin D.g → ℂ)) hN hU2 hmk (fun x => rfl) hU2.2.1⟩

end GlobalTheory.UPel.HT.Unif
