import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExhUnipRadOne

noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace UpperTheory.Zero.LLC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]`. Both sides reduce to the same expression.
-/
private theorem dualCl_fst' (x : IrrGL k) : (Zc.dualCl x).1 = x.1 := by
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, π, π', rfl, rfl, ⟨e⟩⟩`. Establish `ψ` using `GlobalTheory.ContraRefl.contraEquiv (equivRep π)`. Rewrite using `[GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm (cls π)]`. Conclude with `IrrGL.of_eq_of.2 ⟨e.trans ψ.symm⟩`.

Introduce and unpack `rfl`. Conclude with `⟨x.1, x.2.rep, ⟨_, contra x.rep, isSmooth_contra _, GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra Pr.adm _ x.2.rep.smooth x.2.rep.irr⟩, congrArg (Sigma.mk x.1) x.2.cl_rep.symm, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x, ⟨.refl _⟩⟩`.
-/
private theorem dualCl_iff (x y : IrrGL k) : DualCl x y ↔ y = Zc.dualCl x := by
  constructor
  · rintro ⟨n, π, π', rfl, rfl, ⟨e⟩⟩
    have ψ := GlobalTheory.ContraRefl.contraEquiv (equivRep π)
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm (cls π)]
    exact IrrGL.of_eq_of.2 ⟨e.trans ψ.symm⟩
  · rintro rfl
    exact ⟨x.1, x.2.rep, ⟨_, contra x.rep, isSmooth_contra _,
      GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra Pr.adm _ x.2.rep.smooth x.2.rep.irr⟩,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x, ⟨.refl _⟩⟩

/- English proof (translation)
Take `⟨e⟩` from `GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist Pr.adm x.rep x.2.rep.smooth x.2.rep.irr hχ hχ' (mul_inv_cancel χ)`. Establish `φ` using `GlobalTheory.ContraRefl.contraEquiv (x.twEquiv χ hχ)`. Rewrite using `[GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm (x.tw χ hχ), IrrGL.tw_of]`. Conclude with `IrrGL.of_eq_of.2 ⟨φ.trans e.symm⟩`.
-/
private theorem dualCl_tw (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ⁻¹) :
    Zc.dualCl (x.tw χ hχ) = (Zc.dualCl x).tw χ⁻¹ hχ' := by
  obtain ⟨e⟩ := GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist Pr.adm x.rep x.2.rep.smooth x.2.rep.irr hχ hχ'
    (mul_inv_cancel χ)
  have φ := GlobalTheory.ContraRefl.contraEquiv (x.twEquiv χ hχ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm (x.tw χ hχ), IrrGL.tw_of]
  exact IrrGL.of_eq_of.2 ⟨φ.trans e.symm⟩

/- English proof (translation)
Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Use `fun hb => hv0 (φ.toLinearEquiv.map_eq_zero_iff.1 ?_)` and prove the remaining obligations. Establish `hm : φ.toLinearEquiv v ∈ fixed σ K` using `GlobalTheory.Parabolic.mem_fixed.2 fun g hg => by show σ g (φ.toIntertwiningMap v) = φ.toIntertwiningMap v`. Rewrite using `[← φ.toIntertwiningMap.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hv g hg]`. Rewrite `hm` using `[hb]`.

Conclude with `hm`.
-/
private theorem fixed_ne_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (h : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine fun hb => hv0 (φ.toLinearEquiv.map_eq_zero_iff.1 ?_)
  have hm : φ.toLinearEquiv v ∈ fixed σ K := GlobalTheory.Parabolic.mem_fixed.2 fun g hg => by
    show σ g (φ.toIntertwiningMap v) = φ.toIntertwiningMap v
    rw [← φ.toIntertwiningMap.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hv g hg]
  rw [hb] at hm
  exact hm

/- English proof (translation)
Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Establish `hv' : (⟨v, hv⟩ : fixed π (KOne k (Fin n))) ≠ 0` using `fun e => hv0 (congrArg Subtype.val e)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : Module.Dual ℂ (fixed π (KOne k (Fin n))), m ⟨v, hv⟩ ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`.

Conclude with `hv' ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hn)`. Take `⟨l, hl, hlm⟩` from `GlobalTheory.ContraRefl.exists_fixed_contra hs GlobalTheory.StepData.isOpen_KOne GlobalTheory.DepthZeroJac.isCompact_KOne m`. Introduce `hb`. Establish `hlf : l ∈ fixed (contra π) (KOne k (Fin n))` using `GlobalTheory.Parabolic.mem_fixed.2 hl`. Rewrite `hlf` using `[hb]`.

Establish `hl0 : l = 0` using `hlf`. Use `hlm ⟨v, hv⟩` as an intermediate fact. Rewrite `this` using `[hl0]`. Conclude with `hm (by simpa using this.symm)`.
-/
private theorem fixed_contra_ne {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (h : fixed π (KOne k (Fin n)) ≠ ⊥) :
    fixed (contra π) (KOne k (Fin n)) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hv' : (⟨v, hv⟩ : fixed π (KOne k (Fin n))) ≠ 0 := fun e => hv0 (congrArg Subtype.val e)
  obtain ⟨m, hm⟩ : ∃ m : Module.Dual ℂ (fixed π (KOne k (Fin n))), m ⟨v, hv⟩ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv' ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hn)
  obtain ⟨l, hl, hlm⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hs GlobalTheory.StepData.isOpen_KOne GlobalTheory.DepthZeroJac.isCompact_KOne m
  intro hb
  have hlf : l ∈ fixed (contra π) (KOne k (Fin n)) := GlobalTheory.Parabolic.mem_fixed.2 hl
  rw [hb] at hlf
  have hl0 : l = 0 := hlf
  have := hlm ⟨v, hv⟩
  rw [hl0] at this
  exact hm (by simpa using this.symm)

/- English proof (translation)
Unfold `DZ`. Rewrite using `[GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]`. Conclude with `fixed_ne_of_equiv (IrrGL.equivOf _ _ _) (fixed_contra_ne x.rep x.2.rep.smooth h)`.
-/
private theorem dz_dualCl {x : IrrGL k} (h : DZ x) : DZ (Zc.dualCl x) := by
  unfold DZ
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]
  exact fixed_ne_of_equiv (IrrGL.equivOf _ _ _) (fixed_contra_ne x.rep x.2.rep.smooth h)

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]`. Use `hasCentralChar_of_equiv (IrrGL.equivOf _ _ _) fun z l => Subtype.ext (LinearMap.ext fun v => ?_)` and prove the remaining obligations. Establish `h1 : (GeneralLinearGroup.scalar (Fin x.1) z)⁻¹ = GeneralLinearGroup.scalar (Fin x.1) z⁻¹` using `(map_inv _ z).symm`. Rewrite using `[contra_apply, h1, h z⁻¹ v, map_smul, Submodule.coe_smul, LinearMap.smul_apply, MonoidHom.inv_apply, map_inv]`.
-/
private theorem central_dualCl {x : IrrGL k} {ω : kˣ →* ℂˣ} (h : HasCentralChar x.rep ω) :
    HasCentralChar (Zc.dualCl x).rep ω⁻¹ := by
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq Pr.adm x]
  refine hasCentralChar_of_equiv (IrrGL.equivOf _ _ _) fun z l => Subtype.ext (LinearMap.ext fun v => ?_)
  have h1 : (GeneralLinearGroup.scalar (Fin x.1) z)⁻¹ = GeneralLinearGroup.scalar (Fin x.1) z⁻¹ :=
    (map_inv _ z).symm
  rw [contra_apply, h1, h z⁻¹ v, map_smul, Submodule.coe_smul, LinearMap.smul_apply, MonoidHom.inv_apply, map_inv]

/- English proof (translation)
Simplify using `only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one]`.
-/
private theorem tw_tw_inv (y : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ⁻¹) :
    (y.tw χ hχ).tw χ⁻¹ hχ' = y := by
  simp only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one]

/- English proof (translation)
Break down `h with h | ⟨hg, y₀, χ₀, h₀, hd, rfl⟩` into its components or cases. Conclude with `.inl h`. Conclude with `.inr ⟨hg, y₀, χ₀ * χ, h₀.mul hχ, hd, IrrGL.tw_tw _ _ _ _ _⟩`.
-/
private theorem goodCusp_tw {y : IrrGL k} (h : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases h with h | ⟨hg, y₀, χ₀, h₀, hd, rfl⟩
  · exact .inl h
  · exact .inr ⟨hg, y₀, χ₀ * χ, h₀.mul hχ, hd, IrrGL.tw_tw _ _ _ _ _⟩

/- English proof (translation)
Break down `h with h | ⟨hg, y₀, χ₀, h₀, hd, rfl⟩` into its components or cases. Conclude with `.inl ((dualCl_fst' y).trans h)`. Conclude with `.inr ⟨hg, Zc.dualCl y₀, χ₀⁻¹, h₀.inv, dz_dualCl hd, dualCl_tw _ _ _ _⟩`.
-/
private theorem goodCusp_dualCl {y : IrrGL k} (h : GoodCusp y) : GoodCusp (Zc.dualCl y) := by
  rcases h with h | ⟨hg, y₀, χ₀, h₀, hd, rfl⟩
  · exact .inl ((dualCl_fst' y).trans h)
  · exact .inr ⟨hg, Zc.dualCl y₀, χ₀⁻¹, h₀.inv, dz_dualCl hd, dualCl_tw _ _ _ _⟩

/- English proof (translation)
Use `⟨⟨one_pos, c.rep.smooth, fun s d e he => absurd (exh_unipRad_one e) he⟩, ?_⟩` and prove the remaining obligations. Take `⟨ω, hω, hc⟩` from `exists_smooth_hasCentralChar c.rep.smooth c.rep.irr`. Use `⟨ω, hω, ?_⟩` and prove the remaining obligations. Establish `hact : ∀ (g : GL (Fin 1) k) v, c.rep.ρ g v = (ω (GeneralLinearGroup.det g) : ℂ) • v` using `fun g v => by`. Establish `hg : GeneralLinearGroup.scalar (Fin 1) (GeneralLinearGroup.det g) = g`.

Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Simplify using `[GeneralLinearGroup.scalar]`. Use `conv_lhs => rw [← hg]`. Conclude with `hc _ v`.

Use `haveI := c.rep.irr`. Use `Model.nontrivial_of_isIrreducible c.rep.irr` as an intermediate fact. Take `⟨v, hv⟩` from `exists_ne (0 : c.rep.V)`. Set `S : Subrepresentation c.rep.ρ` to `⟨Submodule.span ℂ {v}, fun g w hw => by`. Rewrite using `[hact]`.

Conclude with `Submodule.smul_mem _ _ hw⟩`. Establish `hS : S = ⊤` using `(eq_bot_or_eq_top S).resolve_left fun h => hv (by`. Establish `: v ∈ S` using `Submodule.mem_span_singleton_self v`. Rewrite `this` using `[h]`. Conclude with `this)`.

Set `f : (GlobalTheory.SmGL.ofChar (detChar (Fin 1) ω)).IntertwiningMap c.rep.ρ` to `{ toFun := fun a : ℂ => a • v map_add' := fun a b => add_smul a b v map_smul' := fun a b => mul_smul a b v isIntertwining' := fun g => LinearMap.ext fun a => by show ((ω (GeneralLinearGroup.det g) : ℂ) * a) • v = c.rep.ρ g (a • v)`. Rewrite using `[map_smul, hact, smul_smul, mul_comm] }`. Establish `hb : Function.Bijective f`. Use `⟨fun a b h => smul_left_injective ℂ hv h, fun w => ?_⟩` and prove the remaining obligations. Establish `: w ∈ S` using `by rw [hS]; trivial`.

Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 this`. Conclude with `⟨a, ha⟩`. Conclude with `(IrrGL.of_rep ⟨1, c⟩).symm.trans ((IrrGL.of_eq_of (π := c.rep.ρ) (σ := GlobalTheory.SmGL.ofChar (detChar (Fin 1) ω)) (hs := c.rep.smooth) (hi := c.rep.irr) (hs' := (IrrRep.det (Fin 1) ω hω).smooth) (hi' := (IrrRep.det (Fin 1) ω hω).irr)).2 ⟨(equivOfBijective f hb).symm⟩)`.
-/
private theorem deg_one (c : IrrCl (GL (Fin 1) k)) :
    IrrGL.IsCusp (⟨1, c⟩ : IrrGL k) ∧ ∃ χ hχ, (⟨1, c⟩ : IrrGL k) = IrrGL.ofChar χ hχ := by
  refine ⟨⟨one_pos, c.rep.smooth, fun s d e he => absurd (exh_unipRad_one e) he⟩, ?_⟩
  obtain ⟨ω, hω, hc⟩ := exists_smooth_hasCentralChar c.rep.smooth c.rep.irr
  refine ⟨ω, hω, ?_⟩
  have hact : ∀ (g : GL (Fin 1) k) v, c.rep.ρ g v = (ω (GeneralLinearGroup.det g) : ℂ) • v := fun g v => by
    have hg : GeneralLinearGroup.scalar (Fin 1) (GeneralLinearGroup.det g) = g := by
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp [GeneralLinearGroup.scalar]
    conv_lhs => rw [← hg]
    exact hc _ v
  haveI := c.rep.irr
  have := Model.nontrivial_of_isIrreducible c.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : c.rep.V)
  let S : Subrepresentation c.rep.ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [hact]; exact Submodule.smul_mem _ _ hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  let f : (GlobalTheory.SmGL.ofChar (detChar (Fin 1) ω)).IntertwiningMap c.rep.ρ :=
    { toFun := fun a : ℂ => a • v
      map_add' := fun a b => add_smul a b v
      map_smul' := fun a b => mul_smul a b v
      isIntertwining' := fun g => LinearMap.ext fun a => by
        show ((ω (GeneralLinearGroup.det g) : ℂ) * a) • v = c.rep.ρ g (a • v)
        rw [map_smul, hact, smul_smul, mul_comm] }
  have hb : Function.Bijective f := by
    refine ⟨fun a b h => smul_left_injective ℂ hv h, fun w => ?_⟩
    have : w ∈ S := by rw [hS]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨a, ha⟩
  exact (IrrGL.of_rep ⟨1, c⟩).symm.trans ((IrrGL.of_eq_of (π := c.rep.ρ) (σ := GlobalTheory.SmGL.ofChar (detChar (Fin 1) ω))
    (hs := c.rep.smooth) (hi := c.rep.irr) (hs' := (IrrRep.det (Fin 1) ω hω).smooth)
    (hi' := (IrrRep.det (Fin 1) ω hω).irr)).2 ⟨(equivOfBijective f hb).symm⟩)

/- English proof (translation)
Introduce `k _ _ _ _ _ y`. Establish `hnt` using `Model.nontrivial_of_isIrreducible y.2.rep.irr`. Use `⟨?_, fun χ hχ => ⟨rfl, ?_, ?_, fun χ' hχ' h'' => IrrGL.tw_tw _ _ _ _ _, fun ω hω => ?_⟩, fun h1 => IrrGL.tw_one _ _, fun h => h.1, fun h => ?_, ⟨_, (dualCl_iff y _).2 rfl⟩, fun y' hy' => ?_⟩` and prove the remaining obligations. Take `⟨ω, hs, hω⟩` from `exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr`. Conclude with `⟨ω, hs, hω, fun ω' hω' => centralChar_unique hω' hω⟩`.

Conclude with `⟨fun h => tw_tw_inv y χ hχ hχ.inv ▸ h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩`. Conclude with `⟨fun h => tw_tw_inv y χ hχ hχ.inv ▸ goodCusp_tw h χ⁻¹ hχ.inv, fun h => goodCusp_tw h χ hχ⟩`. Establish `h1` using `hasCentralChar_twist hω χ`. Rewrite `h1` using `[Fintype.card_fin]`. Conclude with `hasCentralChar_of_equiv (y.twEquiv _ _) h1`.

Take `⟨n, c⟩` from `y`. Take `rfl : n = 1` from `h`. Conclude with `deg_one c`. Take `rfl` from `(dualCl_iff y y').1 hy'`. Establish `hdd` using `GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl Pr.adm y`.

Use `⟨dualCl_fst' y, ⟨fun h => ?_, fun h => (GlobalTheory.T.dual_class_cuspidal Pr.adm y h).1⟩, ⟨fun h => ?_, dz_dualCl⟩, ⟨fun h => ?_, goodCusp_dualCl⟩, fun y'' h => (dualCl_iff y y'').1 h, fun χ hχ hχ' => (dualCl_iff _ _).2 (dualCl_tw y χ hχ hχ').symm, fun ω hω => central_dualCl hω⟩` and prove the remaining obligations. Conclude with `hdd ▸ (GlobalTheory.T.dual_class_cuspidal Pr.adm _ h).1`. Conclude with `hdd ▸ dz_dualCl h`. Conclude with `hdd ▸ goodCusp_dualCl h`.
-/
theorem clBasic : ClBasic := by
  intro k _ _ _ _ _ y
  have hnt := Model.nontrivial_of_isIrreducible y.2.rep.irr
  refine ⟨?_, fun χ hχ => ⟨rfl, ?_, ?_, fun χ' hχ' h'' => IrrGL.tw_tw _ _ _ _ _, fun ω hω => ?_⟩,
    fun h1 => IrrGL.tw_one _ _, fun h => h.1, fun h => ?_, ⟨_, (dualCl_iff y _).2 rfl⟩, fun y' hy' => ?_⟩
  · obtain ⟨ω, hs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
    exact ⟨ω, hs, hω, fun ω' hω' => centralChar_unique hω' hω⟩
  · exact ⟨fun h => tw_tw_inv y χ hχ hχ.inv ▸ h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩
  · exact ⟨fun h => tw_tw_inv y χ hχ hχ.inv ▸ goodCusp_tw h χ⁻¹ hχ.inv, fun h => goodCusp_tw h χ hχ⟩
  · have h1 := hasCentralChar_twist hω χ
    rw [Fintype.card_fin] at h1
    exact hasCentralChar_of_equiv (y.twEquiv _ _) h1
  · obtain ⟨n, c⟩ := y
    obtain rfl : n = 1 := h
    exact deg_one c
  · obtain rfl := (dualCl_iff y y').1 hy'
    have hdd := GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl Pr.adm y
    refine ⟨dualCl_fst' y, ⟨fun h => ?_, fun h => (GlobalTheory.T.dual_class_cuspidal Pr.adm y h).1⟩, ⟨fun h => ?_, dz_dualCl⟩,
      ⟨fun h => ?_, goodCusp_dualCl⟩, fun y'' h => (dualCl_iff y y'').1 h,
      fun χ hχ hχ' => (dualCl_iff _ _).2 (dualCl_tw y χ hχ hχ').symm, fun ω hω => central_dualCl hω⟩
    · exact hdd ▸ (GlobalTheory.T.dual_class_cuspidal Pr.adm _ h).1
    · exact hdd ▸ dz_dualCl h
    · exact hdd ▸ goodCusp_dualCl h

end UpperTheory.Zero.LLC

end
