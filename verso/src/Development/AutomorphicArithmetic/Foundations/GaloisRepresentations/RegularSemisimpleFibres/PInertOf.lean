import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.DetByType
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `key : ∀ g : KO k (Fin m), (g : GL (Fin m) k) = Matrix.GeneralLinearGroup.scalar (Fin m) (unitIncl k u) → levelZero π (redK k (Fin m) g) = ((ω (unitIncl k u) : ℂˣ) : ℂ) • (1 : Module.End ℂ _)`. Introduce `g hg`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[levelZero_apply, hg, h]`. Simplify using the standard rewrite rules. Rewrite using `[← redK_scalar, key _ rfl, map_one, map_smul, smul_eq_mul]`.
-/
private theorem tr_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin m) k) V)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) (u : 𝒪[k]ˣ) :
    LinearMap.trace ℂ _ (levelZero π (Matrix.GeneralLinearGroup.scalar (Fin m) (unitRes k u))) =
      (ω (unitIncl k u) : ℂ) * LinearMap.trace ℂ _ (levelZero π 1) := by
  have key : ∀ g : KO k (Fin m), (g : GL (Fin m) k) = Matrix.GeneralLinearGroup.scalar (Fin m) (unitIncl k u) →
      levelZero π (redK k (Fin m) g) = ((ω (unitIncl k u) : ℂˣ) : ℂ) • (1 : Module.End ℂ _) := by
    intro g hg
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [levelZero_apply, hg, h]
    simp
  rw [← redK_scalar, key _ rfl, map_one, map_smul, smul_eq_mul]

/- English proof (translation)
Take `⟨φ, h0, hφ⟩` from `h`. Use `⟨φ, h0, fun κ x => ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Establish `h1` using `detChar_of_mem_KO hμ (DiscreteGroups.sglob.DzIso.map_inc_mem_KO i hi κ)`. Use `show _ = (twist ρ (detChar _ μ)) (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m κ)) (φ x)`.

Rewrite using `[twist_apply, h1]`. Simplify using the standard rewrite rules.
-/
private theorem inflates_twist {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V) (τ : FDRep ℂ (GlobalTheory.GLq.Gn g m))
    {μ : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsUnram μ)
    (h : GlobalTheory.SerSys.TameGen.Inflates (ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates ((twist ρ (detChar _ μ)).comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ := by
  obtain ⟨φ, h0, hφ⟩ := h
  refine ⟨φ, h0, fun κ x => ?_⟩
  rw [hφ]
  have h1 := detChar_of_mem_KO hμ (DiscreteGroups.sglob.DzIso.map_inc_mem_KO i hi κ)
  show _ = (twist ρ (detChar _ μ)) (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m κ)) (φ x)
  rw [twist_apply, h1]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨Matrix.GeneralLinearGroup.map r.symm.toRingHom δ, by ext a b; simp⟩`.
-/
private theorem map_surj {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') {m : ℕ} (δ : GL (Fin m) F') :
    ∃ γ : GL (Fin m) F, Matrix.GeneralLinearGroup.map r.toRingHom γ = δ :=
  ⟨Matrix.GeneralLinearGroup.map r.symm.toRingHom δ, by ext a b; simp⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`. Establish `hχu : IsUnram (ω⁻¹ * ω')`. Introduce `x hx`. Take `⟨u, rfl⟩` from `valuation_eq_one_iff.mp hx`. Simplify using `[h u]`.

Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (((ω⁻¹ * ω') ϖ : ℂˣ) : ℂ) hm`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hm.ne']`. Conclude with `((ω⁻¹ * ω') ϖ).ne_zero hz.symm`.

Establish `hα : (Units.mk0 z hz0) ^ m = (ω⁻¹ * ω') ϖ` using `Units.ext (by simpa using hz)`. Establish `hχe` using `eq_unrChar hχu hϖ`. Use `⟨GlobalTheory.SmGL.unrChar k (Units.mk0 z hz0), isUnram_unrChar k _, ?_⟩` and prove the remaining obligations. Establish `hpow : GlobalTheory.SmGL.unrChar k (Units.mk0 z hz0) ^ m = ω⁻¹ * ω'`. Rewrite using `[hχe]`.

Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.unrChar_apply, ← hα, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]`. Rewrite using `[hpow, mul_inv_cancel_left]`.
-/
private theorem exists_unr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : ℕ} (hm : 0 < m) {ω ω' : kˣ →* ℂˣ} (h : ∀ u : 𝒪[k]ˣ, ω (unitIncl k u) = ω' (unitIncl k u)) :
    ∃ μ : kˣ →* ℂˣ, IsUnram μ ∧ ω * μ ^ m = ω' := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hχu : IsUnram (ω⁻¹ * ω') := by
    intro x hx
    obtain ⟨u, rfl⟩ := valuation_eq_one_iff.mp hx
    simp [h u]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((ω⁻¹ * ω') ϖ : ℂˣ) : ℂ) hm
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact ((ω⁻¹ * ω') ϖ).ne_zero hz.symm
  have hα : (Units.mk0 z hz0) ^ m = (ω⁻¹ * ω') ϖ := Units.ext (by simpa using hz)
  have hχe := eq_unrChar hχu hϖ
  refine ⟨GlobalTheory.SmGL.unrChar k (Units.mk0 z hz0), isUnram_unrChar k _, ?_⟩
  have hpow : GlobalTheory.SmGL.unrChar k (Units.mk0 z hz0) ^ m = ω⁻¹ * ω' := by
    rw [hχe]
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.pow_apply, GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.unrChar_apply, ← hα,
      ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [hpow, mul_inv_cancel_left]

/- English proof (translation)
Introduce `hTC hBQ E Ω _ _ _ _ _ A v hv g _ i hi m x y hxc hyc hxd hyd htr`. Take `⟨-, -, ⟨r⟩⟩` from `hBQ E v g i hi`. Establish `hcls : ∀ c : IrrCl (GL (Fin m) (v.adicCompletion E)), GlobalTheory.LocLanglands.cls c.rep = ⟨m, c⟩`. Introduce `c`. Unfold `GlobalTheory.LocLanglands.cls`.

Rewrite using `[IrrCl.cl_rep]`. Establish `hm : 0 < m` using `(UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, x⟩).2.2.2.1 hxc`. Take `⟨τx, hτx, hinfx⟩` from `(UpperTheory.Zero.LLC.typeEx E Ω A v hv g i hi m hm x.rep).1 (by rw [hcls]; exact hxc) (by rw [hcls]; exact hxd)`. Take `⟨τy, hτy, hinfy⟩` from `(UpperTheory.Zero.LLC.typeEx E Ω A v hv g i hi m hm y.rep).1 (by rw [hcls]; exact hyc) (by rw [hcls]; exact hyd)`. Establish `hch : τx.character = τy.character`.

Use function extensionality and compare the values at `δ`. Take `⟨γ, hγ⟩` from `map_surj r (δ : GL (Fin m) (ZMod g))`. Substitute `hγ` using the available equality. Establish `e1` using `hTC E v g i hi r ⟨m, x⟩ τx hτx hinfx γ`. Establish `e2` using `hTC E v g i hi r ⟨m, y⟩ τy hτy hinfy γ`.

Conclude with `e1.trans ((htr γ).trans e2.symm)`. Take `⟨ωx, -, hωx, -⟩` from `(UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, x⟩).1`. Take `⟨ωy, -, hωy, -⟩` from `(UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, y⟩).1`. Establish `hT : LinearMap.trace ℂ _ (levelZero x.rep.ρ 1) ≠ 0`. Establish `e1` using `hTC E v g i hi r ⟨m, x⟩ τx hτx hinfx 1`.

Simplify using `only [map_one, FDRep.char_one] at e1`. Establish `hinf` using `hinfx`. Unfold `GlobalTheory.SerSys.TameGen.Inflates at hinf`. Take `⟨φ, hφ, -⟩` from `hinf`. Establish `: Nontrivial τx.V`.

Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Conclude with `hφ (LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply])`. Rewrite using `[map_one]`. Use `fun h0 => ?_` and prove the remaining obligations.

Establish `h1 : (Module.finrank ℂ τx.V : ℂ) = 0` using `e1.trans h0`. Conclude with `(Module.finrank_pos (R := ℂ) (M := τx.V)).ne' (by exact_mod_cast h1)`. Establish `hωu : ∀ u, ωx (unitIncl _ u) = ωy (unitIncl _ u)`. Introduce `u`. Establish `a1` using `tr_scalar x.rep.ρ hωx u`.

Establish `a2` using `tr_scalar y.rep.ρ hωy u`. Establish `e` using `htr (Matrix.GeneralLinearGroup.scalar (Fin m) (unitRes _ u))`. Establish `e1` using `htr 1`. Rewrite `e` using `[a1, a2, ← e1]`. Conclude with `Units.ext (mul_right_cancel₀ hT e)`.

Take `⟨μ, hμ, hμω⟩` from `exists_unr hm hωu`. Establish `hμs` using `isSmoothChar_of_isUnram hμ`. Set `σ' : IrrRep (GL (Fin m) (v.adicCompletion E))` to `IrrRep.mk x.rep.V (twist x.rep.ρ (detChar (Fin m) μ)) (isSmooth_twist x.rep.smooth hμs.detChar) (isIrreducible_twist x.rep.irr _)`. Establish `hinfσ : GlobalTheory.SerSys.TameGen.Inflates (MonoidHom.comp σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)) τx` using `inflates_twist i hi x.rep.ρ τx hμ hinfx`. Establish `hωσ : HasCentralChar σ'.ρ ωy`.

Use `hasCentralChar_twist hωx μ` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin, hμω]`. Conclude with `this`. Establish `hcl` using `UpperTheory.Zero.LLC.detByType E Ω A v hv g i hi m hm y.rep σ' τy τx ωy hτy hch hinfy hinfσ hωy hωσ`. Unfold `IrrGL.Inert`.

Use `⟨μ, hμ, ?_⟩` and prove the remaining obligations. Establish `e3 : IrrGL.tw (⟨m, x⟩ : IrrGL _) μ hμs = GlobalTheory.LocLanglands.cls σ'` using `by conv_lhs => rw [← IrrGL.of_rep ⟨m, x⟩]`. Rewrite using `[IrrGL.tw_of]`. Both sides reduce to the same expression. Conclude with `(hcls y).symm.trans (hcl.symm.trans e3.symm)`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.inertOf :
    TypeChar → BaseQ → InertOf := by
  intro hTC hBQ E Ω _ _ _ _ _ A v hv g _ i hi m x y hxc hyc hxd hyd htr
  obtain ⟨-, -, ⟨r⟩⟩ := hBQ E v g i hi
  have hcls : ∀ c : IrrCl (GL (Fin m) (v.adicCompletion E)), GlobalTheory.LocLanglands.cls c.rep = ⟨m, c⟩ := by
    intro c
    unfold GlobalTheory.LocLanglands.cls
    rw [IrrCl.cl_rep]
  have hm : 0 < m := (UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, x⟩).2.2.2.1 hxc
  obtain ⟨τx, hτx, hinfx⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A v hv g i hi m hm x.rep).1
    (by rw [hcls]; exact hxc) (by rw [hcls]; exact hxd)
  obtain ⟨τy, hτy, hinfy⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A v hv g i hi m hm y.rep).1
    (by rw [hcls]; exact hyc) (by rw [hcls]; exact hyd)
  have hch : τx.character = τy.character := by
    funext δ
    obtain ⟨γ, hγ⟩ := map_surj r (δ : GL (Fin m) (ZMod g))
    subst hγ
    have e1 := hTC E v g i hi r ⟨m, x⟩ τx hτx hinfx γ
    have e2 := hTC E v g i hi r ⟨m, y⟩ τy hτy hinfy γ
    exact e1.trans ((htr γ).trans e2.symm)
  obtain ⟨ωx, -, hωx, -⟩ := (UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, x⟩).1
  obtain ⟨ωy, -, hωy, -⟩ := (UpperTheory.Zero.LLC.clBasic (v.adicCompletion E) ⟨m, y⟩).1
  have hT : LinearMap.trace ℂ _ (levelZero x.rep.ρ 1) ≠ 0 := by
    have e1 := hTC E v g i hi r ⟨m, x⟩ τx hτx hinfx 1
    simp only [map_one, FDRep.char_one] at e1
    have hinf := hinfx
    unfold GlobalTheory.SerSys.TameGen.Inflates at hinf
    obtain ⟨φ, hφ, -⟩ := hinf
    have : Nontrivial τx.V := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hφ (LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply])
    rw [map_one]
    refine fun h0 => ?_
    have h1 : (Module.finrank ℂ τx.V : ℂ) = 0 := e1.trans h0
    exact (Module.finrank_pos (R := ℂ) (M := τx.V)).ne' (by exact_mod_cast h1)
  have hωu : ∀ u, ωx (unitIncl _ u) = ωy (unitIncl _ u) := by
    intro u
    have a1 := tr_scalar x.rep.ρ hωx u
    have a2 := tr_scalar y.rep.ρ hωy u
    have e := htr (Matrix.GeneralLinearGroup.scalar (Fin m) (unitRes _ u))
    have e1 := htr 1
    rw [a1, a2, ← e1] at e
    exact Units.ext (mul_right_cancel₀ hT e)
  obtain ⟨μ, hμ, hμω⟩ := exists_unr hm hωu
  have hμs := isSmoothChar_of_isUnram hμ
  let σ' : IrrRep (GL (Fin m) (v.adicCompletion E)) :=
    IrrRep.mk x.rep.V (twist x.rep.ρ (detChar (Fin m) μ))
      (isSmooth_twist x.rep.smooth hμs.detChar) (isIrreducible_twist x.rep.irr _)
  have hinfσ : GlobalTheory.SerSys.TameGen.Inflates (MonoidHom.comp σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)) τx :=
    inflates_twist i hi x.rep.ρ τx hμ hinfx
  have hωσ : HasCentralChar σ'.ρ ωy := by
    have := hasCentralChar_twist hωx μ
    rw [Fintype.card_fin, hμω] at this
    exact this
  have hcl := UpperTheory.Zero.LLC.detByType E Ω A v hv g i hi m hm y.rep σ' τy τx ωy hτy hch hinfy hinfσ hωy hωσ
  unfold IrrGL.Inert
  refine ⟨μ, hμ, ?_⟩
  have e3 : IrrGL.tw (⟨m, x⟩ : IrrGL _) μ hμs = GlobalTheory.LocLanglands.cls σ' := by
    conv_lhs => rw [← IrrGL.of_rep ⟨m, x⟩]
    rw [IrrGL.tw_of]
    rfl
  exact (hcls y).symm.trans (hcl.symm.trans e3.symm)
