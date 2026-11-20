import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatKOSmulOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEllStatement

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Quad

/- English proof (translation)
Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Establish `e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O` using `Submodule.quotEquivOfEqBot _ (by simp)`. Rewrite using `[e.length_eq]`. Establish `: Module.length O O = ⊤`. Assume the negation of the conclusion as `h`.

Establish `h2` using `(isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2`. Establish `: IsArtinianRing O` using `h2`. Conclude with `IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)`. Rewrite using `[this]`. Conclude with `le_top`.

Establish `ha' : algebraMap O (FractionRing O) a ≠ 0`. Simplify using `using ha`. Set `x : KOG O 1` to `Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹`. Establish `hx : a • x = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Use `⟨fun _ => 1, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `[Algebra.smul_def, mul_inv_cancel₀ ha']`. Set `x' : Submodule.torsionBy O (KOG O 1) a` to `⟨x, hx⟩`. Set `f : O →ₗ[O] Submodule.torsionBy O (KOG O 1) a` to `LinearMap.toSpanSingleton O _ x'`.

Establish `hf : Ideal.span {a} ≤ LinearMap.ker f`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Subtype.ext hx`. Use `Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`.

Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H y`. Rewrite `hy` using `[Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨b, hb⟩` from `hy`. Use `⟨Submodule.Quotient.mk (b 0), Subtype.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `b 0 • x = Submodule.Quotient.mk y`. Rewrite using `[← Submodule.Quotient.mk_smul]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Establish `hj : j = 0` using `Subsingleton.elim _ _`.

Substitute `hj` using the available equality. Establish `h0 : algebraMap O (FractionRing O) (b 0) = algebraMap O (FractionRing O) a * y 0`. Simplify `congrFun hb 0` using `[Algebra.smul_def]`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, h0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O := Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq]
    have : Module.length O O = ⊤ := by
      by_contra h
      have h2 := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
      have : IsArtinianRing O := h2
      exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
    rw [this]; exact le_top
  · have ha' : algebraMap O (FractionRing O) a ≠ 0 := by
      simpa using ha
    let x : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
    have hx : a • x = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨fun _ => 1, ?_⟩
      funext j
      simp [Algebra.smul_def, mul_inv_cancel₀ ha']
    let x' : Submodule.torsionBy O (KOG O 1) a := ⟨x, hx⟩
    let f : O →ₗ[O] Submodule.torsionBy O (KOG O 1) a := LinearMap.toSpanSingleton O _ x'
    have hf : Ideal.span {a} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨b, hb⟩ := hy
      refine ⟨Submodule.Quotient.mk (b 0), Subtype.ext ?_⟩
      change b 0 • x = Submodule.Quotient.mk y
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have h0 : algebraMap O (FractionRing O) (b 0) = algebraMap O (FractionRing O) a * y 0 := by
        simpa [Algebra.smul_def] using congrFun hb 0
      simp only [Pi.smul_apply, Algebra.smul_def, h0]
      field_simp

/- English proof (translation)
Establish `h1 : f 1 = 0` using `by simpa using hadd 1 (one_mem _) 1 (one_mem _)`. Set `K : Subgroup (G E Ω)` to `{ carrier := {g | g ∈ Ine (F := E) A ∧ f g = 0} mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩ one_mem' := ⟨one_mem _, h1⟩ inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by`. Use `hadd a ha.1 a⁻¹ (inv_mem ha.1)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, h1, ha.2, zero_add]`. Conclude with `this.symm⟩ }`.

Use `closure_minimal (t := {g | f g = 0}) ?_ (hf.isClosed_fiber 0) (hγ.2 hσ)` and prove the remaining obligations. Introduce `g hg`. Use `((Subgroup.closure_le K).2 ?_ hg).2` and prove the remaining obligations. Introduce and unpack `g (rfl | hg)`. Conclude with `⟨hγ.1, h0⟩`.

Conclude with `⟨GlobalTheory.TameCharUnique.mem_Ine_of_wild hg, hw g hg⟩`.
-/
theorem eq_zero_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {γ : G E Ω} (hγ : TameGenAt A γ) {M : Type} [AddCommGroup M] (f : G E Ω → M)
    (hf : IsLocallyConstant f) (hadd : ∀ a ∈ Ine (F := E) A, ∀ b ∈ Ine (F := E) A, f (a * b) = f a + f b)
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → f σ = 0) (h0 : f γ = 0)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : f σ = 0 := by
  have h1 : f 1 = 0 := by simpa using hadd 1 (one_mem _) 1 (one_mem _)
  let K : Subgroup (G E Ω) :=
    { carrier := {g | g ∈ Ine (F := E) A ∧ f g = 0}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨one_mem _, h1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hadd a ha.1 a⁻¹ (inv_mem ha.1)
        rw [mul_inv_cancel, h1, ha.2, zero_add] at this
        exact this.symm⟩ }
  refine closure_minimal (t := {g | f g = 0}) ?_ (hf.isClosed_fiber 0) (hγ.2 hσ)
  intro g hg
  refine ((Subgroup.closure_le K).2 ?_ hg).2
  rintro g (rfl | hg)
  · exact ⟨hγ.1, h0⟩
  · exact ⟨GlobalTheory.TameCharUnique.mem_Ine_of_wild hg, hw g hg⟩

/- English proof (translation)
Take `⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩` from `hS`. Establish `hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g` using `⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩`. Establish `a1` using `h1 g (S.e.symm (0, fun _ => 1))`. Establish `a2` using `h2 _ hg (S.e.symm (0, fun _ => 1))`. Simplify using `only [hp] at a2`.

Establish `a3` using `congrFun (congrArg Prod.snd (a2.symm.trans a1)) c`. Simplify using `only [LinearEquiv.apply_symm_apply, mul_one] at a3`. Conclude with `IsFractionRing.injective _ _ a3`.
-/
theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : GoodCongruenceObjects D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

/- English proof (translation)
Introduce `D i r ρ π Xs S hr hS hπ v hv hq c`. Establish `hl` using `D.nd.SQ_l i v hv`. Establish `hchi : ∀ γ ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ := fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2`. Establish `hγ0` using `D.nd.locNd_chebotarevPlace_mem i v`. Establish `htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0`.

Introduce `f hf`. Use `Check.cocW_quad i r S Xs _ hq hf _ hγ0` as an intermediate fact. Rewrite `this` using `[Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0]`. Rewrite using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `this`.

Establish `hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 → ∀ σ ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 v), f σ = 0 := by`. Introduce `f hf h0`. Take `⟨hc, hz⟩` from `(GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c hf`. Establish `: DiscreteTopology (KOG (D.nd.O i) 1)` using `⟨rfl⟩`. Establish `hlc : IsLocallyConstant f` using `(IsLocallyConstant.iff_continuous f).2 hc`.

Establish `hadd : ∀ a ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f (a * b) = f a + f b := by`. Introduce `a ha b _`. Establish `e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1`. Express the relevant statement in the definitionally equal form `(((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _`. Rewrite using `[hchi a ha, mul_inv_cancel, Units.val_one]`.

Rewrite using `[hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]`. Conclude with `eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0`. Use `le_trans ?_ (length_torsionBy_le (D.nd.zeta i v - 1))` and prove the remaining obligations. Use `Module.length_le_of_injective (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Conclude with `htor f hf`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨_, f, hf, rfl⟩ h0`. Use `Subtype.ext (funext fun σ => ?_)` and prove the remaining obligations. Conclude with `hdet f hf (congrArg Subtype.val h0) σ.1 σ.2`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.Quad
