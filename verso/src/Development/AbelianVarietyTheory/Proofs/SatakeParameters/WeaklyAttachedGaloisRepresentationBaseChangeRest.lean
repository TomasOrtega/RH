import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.SemisimpleRestrictionToNormalSubgroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaloisRepTowerRestriction
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

noncomputable section

namespace GlobalTheory.WeakBaseChange

/- English proof (translation)
Introduce `W hW`. Take `⟨W', hW', hc⟩` from `h W (fun g v hv => hW g v hv)`. Set `ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k)` to `fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin`. Establish `hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v`. Introduce `g h v`.

Simplify using `[ρ, Matrix.mulVec_mulVec, map_mul]`. Establish `hρ1 : ∀ v, ρ 1 v = v` using `by intro v; simp [ρ]`. Establish `hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W` using `fun g v hv => hW g v hv`. Set `p : (Fin n → k) →ₗ[k] (Fin n → k)` to `W.subtype ∘ₗ W.linearProjOfIsCompl W' hc`. Establish `hpW : ∀ v, p v ∈ W` using `fun v => (W.linearProjOfIsCompl W' hc v).2`.

Establish `hpl : ∀ w ∈ W, p w = w` using `fun w hw => by`. Establish `e` using `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)`. Conclude with `e`. Establish `hpr : ∀ w ∈ W', p w = 0` using `fun w hw => by`. Establish `e` using `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)`.

Conclude with `e`. Establish `hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v)`. Introduce `m hm v`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')`. Establish `hb' : ρ m b ∈ W'` using `hW' ⟨m, hm⟩ b hb`.

Rewrite using `[show p (a + b) = a by rw [map_add, hpl a ha, hpr b hb, add_zero], map_add, map_add, hpl _ (hWρ m a ha), hpr _ hb', add_zero]`. Set `T : Γ → (Fin n → k) →ₗ[k] (Fin n → k)` to `fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹`. Establish `hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g`. Introduce `g m hm`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Simplify using `only [T, LinearMap.comp_apply]`. Rewrite using `[mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]`. Establish `hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v)`. Introduce `h g v`. Simplify using `only [T, LinearMap.comp_apply]`.

Rewrite using `[hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]`. Establish `hTW : ∀ g v, T g v ∈ W` using `fun g v => hWρ g _ (hpW _)`. Establish `hTfix : ∀ g, ∀ w ∈ W, T g w = w`. Introduce `g w hw`. Simplify using `only [T, LinearMap.comp_apply]`.

Rewrite using `[hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]`. Use `haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _`. Set `S : (Fin n → k) →ₗ[k] (Fin n → k)` to `∑ q : Γ ⧸ N, T q.out`. Establish `hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out)`. Introduce `h q`.

Establish `e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q` using `by conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Establish `hm : (h * q.out)⁻¹ * (h • q).out ∈ N` using `QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)`. Rewrite using `[← hTN (h * q.out) _ hm, mul_inv_cancel_left]`. Establish `hS : ∀ h v, ρ h (S v) = S (ρ h v)`.

Introduce `h v`. Simplify using `only [S, LinearMap.sum_apply, map_sum, hTc h]`. Rewrite using `[← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [MulAction.toPerm_apply]`.

Rewrite using `[hout]`. Use `set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def`. Establish `hc0 : c ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Set `P : (Fin n → k) →ₗ[k] (Fin n → k)` to `c⁻¹ • S`. Establish `hPW : ∀ v, P v ∈ W` using `fun v => by`.

Simplify using `only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]`. Conclude with `W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)`. Establish `hPfix : ∀ w ∈ W, P w = w` using `fun w hw => by`. Simplify using `only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.

Establish `hP : ∀ h v, ρ h (P v) = P (ρ h v)` using `fun h v => by`. Simplify using `only [P, LinearMap.smul_apply, map_smul, hS]`. Use `⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩` and prove the remaining obligations. Use `show P (ρ g v) = 0`. Rewrite using `[← hP, LinearMap.mem_ker.mp hv, map_zero]`.

Use `⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩` and prove the remaining obligations. Rewrite using `[← hPfix v hv]`. Conclude with `hv'`. Establish `: v = P v + (v - P v)` using `by abel`. Rewrite using `[this]`.

Use `Submodule.add_mem_sup (hPW v) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]`.
-/
theorem isSSRep_of_finiteIndex {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (N : Subgroup Γ) [N.FiniteIndex] (h : IsSSRep (r.comp N.subtype)) : IsSSRep r := by
  classical
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W (fun g v hv => hW g v hv)
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin
  have hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v := by
    intro g h v; simp [ρ, Matrix.mulVec_mulVec, map_mul]
  have hρ1 : ∀ v, ρ 1 v = v := by intro v; simp [ρ]
  have hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv => hW g v hv
  let p : (Fin n → k) →ₗ[k] (Fin n → k) := W.subtype ∘ₗ W.linearProjOfIsCompl W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (W.linearProjOfIsCompl W' hc v).2
  have hpl : ∀ w ∈ W, p w = w := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
    exact e
  have hpr : ∀ w ∈ W', p w = 0 := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)
    exact e
  have hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v) := by
    intro m hm v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
    have hb' : ρ m b ∈ W' := hW' ⟨m, hm⟩ b hb
    rw [show p (a + b) = a by rw [map_add, hpl a ha, hpr b hb, add_zero], map_add, map_add, hpl _ (hWρ m a ha),
      hpr _ hb', add_zero]
  let T : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹
  have hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g := by
    intro g m hm; refine LinearMap.ext fun v => ?_
    simp only [T, LinearMap.comp_apply]
    rw [mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]
  have hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v) := by
    intro h g v
    simp only [T, LinearMap.comp_apply]
    rw [hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]
  have hTW : ∀ g v, T g v ∈ W := fun g v => hWρ g _ (hpW _)
  have hTfix : ∀ g, ∀ w ∈ W, T g w = w := by
    intro g w hw
    simp only [T, LinearMap.comp_apply]
    rw [hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  let S : (Fin n → k) →ₗ[k] (Fin n → k) := ∑ q : Γ ⧸ N, T q.out
  have hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out) := by
    intro h q
    have e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hm : (h * q.out)⁻¹ * (h • q).out ∈ N := QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)
    rw [← hTN (h * q.out) _ hm, mul_inv_cancel_left]
  have hS : ∀ h v, ρ h (S v) = S (ρ h v) := by
    intro h v
    simp only [S, LinearMap.sum_apply, map_sum, hTc h]
    rw [← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [hout]
  set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • S
  have hPW : ∀ v, P v ∈ W := fun v => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    exact W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)
  have hPfix : ∀ w ∈ W, P w = w := fun w hw => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hP : ∀ h v, ρ h (P v) = P (ρ h v) := fun h v => by
    simp only [P, LinearMap.smul_apply, map_smul, hS]
  refine ⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩
  · show P (ρ g v) = 0
    rw [← hP, LinearMap.mem_ker.mp hv, map_zero]
  · refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩
    · rw [← hPfix v hv]; exact hv'
    · have : v = P v + (v - P v) := by abel
      rw [this]
      refine Submodule.add_mem_sup (hPW v) ?_
      rw [LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]

end GlobalTheory.WeakBaseChange

namespace GlobalTheory.WeakBaseChange

/- English proof (translation)
Use `haveI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite ℚ E M`. Set `f : G E Ω ⧸ (res E Ω M).range → (M →ₐ[E] Ω)` to `fun q => ((Quotient.out q : G E Ω) : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E M Ω)`. Establish `hf : Function.Injective f`. Introduce `q q' hqq`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']`.

Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Use `set a : G E Ω := Quotient.out q`. Use `set b : G E Ω := Quotient.out q'`. Establish `hab : ∀ x : M, a (algebraMap M Ω x) = b (algebraMap M Ω x)` using `fun x => DFunLike.congr_fun hqq x`. Set `ρ : G M Ω` to `AlgEquiv.ofRingEquiv (f := (a⁻¹ * b).toRingEquiv) (fun x => by show a.symm (b (algebraMap M Ω x)) = algebraMap M Ω x`.

Rewrite using `[← hab, AlgEquiv.symm_apply_apply])`. Conclude with `⟨ρ, AlgEquiv.ext fun x => rfl⟩`. Use `haveI : Finite (G E Ω ⧸ (res E Ω M).range) := Finite.of_injective f hf`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem finiteIndex_range_res (E M Ω : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] : (res E Ω M).range.FiniteIndex := by
  classical
  haveI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite ℚ E M
  let f : G E Ω ⧸ (res E Ω M).range → (M →ₐ[E] Ω) := fun q =>
    ((Quotient.out q : G E Ω) : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E M Ω)
  have hf : Function.Injective f := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.mpr
    set a : G E Ω := Quotient.out q
    set b : G E Ω := Quotient.out q'
    have hab : ∀ x : M, a (algebraMap M Ω x) = b (algebraMap M Ω x) := fun x => DFunLike.congr_fun hqq x
    let ρ : G M Ω := AlgEquiv.ofRingEquiv (f := (a⁻¹ * b).toRingEquiv) (fun x => by
      show a.symm (b (algebraMap M Ω x)) = algebraMap M Ω x
      rw [← hab, AlgEquiv.symm_apply_apply])
    exact ⟨ρ, AlgEquiv.ext fun x => rfl⟩
  haveI : Finite (G E Ω ⧸ (res E Ω M).range) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.WeakBaseChange

namespace GlobalTheory.WeakBaseChange

/- English proof (translation)
Set `g : Γ' ⧸ N.comap f → Γ ⧸ N` to `fun q => ((f (Quotient.out q) : Γ) : Γ ⧸ N)`. Establish `hg : Function.Injective g`. Introduce `q q' h`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises.

Use `QuotientGroup.eq.mp h` as an intermediate fact. Rewrite using `[Subgroup.mem_comap, map_mul, map_inv]`. Conclude with `this`. Use `haveI : Finite (Γ' ⧸ N.comap f) := Finite.of_injective g hg`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem finiteIndex_comap {Γ Γ' : Type} [Group Γ] [Group Γ'] (f : Γ' →* Γ) (N : Subgroup Γ) [N.FiniteIndex] :
    (N.comap f).FiniteIndex := by
  classical
  let g : Γ' ⧸ N.comap f → Γ ⧸ N := fun q => ((f (Quotient.out q) : Γ) : Γ ⧸ N)
  have hg : Function.Injective g := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.mpr
    have := QuotientGroup.eq.mp h
    rw [Subgroup.mem_comap, map_mul, map_inv]
    exact this
  haveI : Finite (Γ' ⧸ N.comap f) := Finite.of_injective g hg
  exact Subgroup.finiteIndex_of_finite_quotient

/- English proof (translation)
Establish `hr : ((((q : ℝ) ^ f) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ f`. Rewrite using `[← Complex.ofReal_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), ← Real.rpow_mul_natCast (Nat.cast_nonneg _), mul_comm]`. Proceed by induction on `B using Multiset.induction_on with`. Consider the case `empty => rfl`. Consider the case `cons b B ih`.

Simplify using `only [algSat, Multiset.map_cons] at ih ⊢`. Simplify using `[hr, mul_pow] at ih ⊢`.
-/
theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have hr : ((((q : ℝ) ^ f) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ f := by
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
      mul_comm]
  induction B using Multiset.induction_on with
  | empty => rfl
  | cons b B ih =>
    simp only [algSat, Multiset.map_cons] at ih ⊢
    simp [hr, mul_pow] at ih ⊢

end GlobalTheory.WeakBaseChange

open GlobalTheory.WeakBaseChange in

/- English proof (translation)
Introduce `E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr`. Take `⟨hc, hss, hatt⟩` from `hr`. Use `⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩` and prove the remaining obligations. Use `haveI := finiteIndex_range_res E M Ω set H := (res E Ω M).range with hH haveI : (H.normalCore.comap (res E Ω M)).FiniteIndex := finiteIndex_comap _ _`. Use `isSSRep_of_finiteIndex _ (H.normalCore.comap (res E Ω M)) ?_` and prove the remaining obligations.

Establish `hrange : ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype).range = H.normalCore`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`.

Introduce `hx`. Take `⟨y, hy⟩` from `(Subgroup.normalCore_le H hx : x ∈ (res E Ω M).range)`. Conclude with `⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩`. Use `UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype) (by rw [hrange]; exact Subgroup.normalCore_normal H) hss` as an intermediate fact. Rewrite using `[MonoidHom.comp_assoc]` and apply the resulting hypothesis.

Use `filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt] with w h`. Take `⟨B, hB, hF⟩` from `h`. Establish `h2` using `GlobalTheory.AttResTower.normV_under_pow (K := E) w`. Use `set f := w.asIdeal.inertiaDeg (𝓞 E)`. Use `⟨B.map (· ^ f), hL.sat w f B h2 hB, ?_⟩` and prove the remaining obligations.

Establish `h3` using `(UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF`. Rewrite using `[h2, algSat_pow]`. Conclude with `h3`.
-/
theorem GlobalTheory.GalCut.weak_comp_res : ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Field Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (P : CuspSub M a), IsLift π P → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M)) := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (res E Ω M).range with hH
    haveI : (H.normalCore.comap (res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (res E Ω M)) ?_
    have hrange : ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt] with w h
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    refine ⟨B.map (· ^ f), hL.sat w f B h2 hB, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
