import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.TopMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {D : D7} {V : HSp D}

/- English proof (translation)
Use `show (infHom V) h = 1 ↔ _`. Rewrite using `[Units.ext_iff]`. Conclude with `Iff.rfl`.
-/
theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (Eqv.matA D V h).map (infPart D) = 1 := by
  show (infHom V) h = 1 ↔ _
  rw [Units.ext_iff]
  exact Iff.rfl

/- English proof (translation)
Establish `h1` using `(mem_GfC' h).1 hh`. Unfold `Eqv.psiT`. Rewrite using `[RingHom.coe_comp, ← Matrix.map_map, h1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem psiT_of_mem_GfC' {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) : (Eqv.matA D V h).map (Eqv.psiT D τ) = 1 := by
  have h1 := (mem_GfC' h).1 hh
  unfold Eqv.psiT
  rw [RingHom.coe_comp, ← Matrix.map_map, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Introduce `a ha b hb`. Apply `Eqv.matA_inj D V` to reduce the goal to its premises. Rewrite using `[Eqv.matA_mul, Eqv.matA_mul]`. Apply `Eqv.mat_ext D` to reduce the goal to its premises. Introduce `τ`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, psiT_of_mem_GfC' hb τ, Matrix.mul_one, Matrix.one_mul]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, (Eqv.mem_GinfC D V a).1 ha, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem comm_GinfC_GfC' : ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a := by
  intro a ha b hb
  apply Eqv.matA_inj D V
  rw [Eqv.matA_mul, Eqv.matA_mul]
  apply Eqv.mat_ext D
  · intro τ
    rw [Matrix.map_mul, Matrix.map_mul, psiT_of_mem_GfC' hb τ, Matrix.mul_one, Matrix.one_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, (Eqv.mem_GinfC D V a).1 ha, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce and unpack `a ⟨ha, hb⟩`. Rewrite using `[Subgroup.mem_bot]`. Apply `Eqv.matA_inj D V` to reduce the goal to its premises. Rewrite using `[Eqv.matA_one]`.

Apply `Eqv.mat_ext D` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[psiT_of_mem_GfC' hb τ, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[(Eqv.mem_GinfC D V a).1 ha, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem inf_GinfC_GfC' : GinfC V ⊓ GfC V = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨ha, hb⟩
  rw [Subgroup.mem_bot]
  apply Eqv.matA_inj D V
  rw [Eqv.matA_one]
  apply Eqv.mat_ext D
  · intro τ
    rw [psiT_of_mem_GfC' hb τ, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [(Eqv.mem_GinfC D V a).1 ha, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[mem_GfC']`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply]`. Apply `(Eqv.splitEquiv D).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`.

Establish `e` using `congrFun (congrFun (hh τ) i) j`. Rewrite `e` using `[Matrix.map_apply]`. Rewrite using `[Eqv.splitEquiv_apply, Eqv.splitEquiv_apply]`. Express the relevant statement in the definitionally equal form `Eqv.psiT D τ (Eqv.matA D V h i j) = _`. Rewrite using `[e]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`.
-/
theorem mem_GfC_of_psiT {h : GA D V} (hh : ∀ τ, (Eqv.matA D V h).map (Eqv.psiT D τ) = 1) : h ∈ GfC V := by
  rw [mem_GfC']
  ext i j
  rw [Matrix.map_apply]
  apply (Eqv.splitEquiv D).injective
  funext τ
  have e := congrFun (congrFun (hh τ) i) j
  rw [Matrix.map_apply] at e
  rw [Eqv.splitEquiv_apply, Eqv.splitEquiv_apply]
  change Eqv.psiT D τ (Eqv.matA D V h i j) = _
  rw [e]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

/- English proof (translation)
Use `⟨g * (Eqv.infOnly D V g)⁻¹, mem_GfC_of_psiT fun τ => ?_, Eqv.infOnly D V g, Eqv.infOnly_mem_GinfC D V g, (inv_mul_cancel_right g _).symm⟩` and prove the remaining obligations. Establish `h1 : (Eqv.matA D V g).map (Eqv.psiT D τ) = (Eqv.matA D V (Eqv.infOnly D V g)).map (Eqv.psiT D τ)`. Rewrite using `[← Eqv.infMat_thetaC, ← Eqv.infMat_thetaC, Eqv.infMat_infOnly]`. Rewrite using `[Eqv.matA_mul, Matrix.map_mul, h1, ← Matrix.map_mul, ← Eqv.matA_mul, mul_inv_cancel, Eqv.matA_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem ga_decomp (g : GA D V) : ∃ h ∈ GfC V, ∃ a ∈ GinfC V, g = h * a := by
  refine ⟨g * (Eqv.infOnly D V g)⁻¹, mem_GfC_of_psiT fun τ => ?_, Eqv.infOnly D V g, Eqv.infOnly_mem_GinfC D V g,
    (inv_mul_cancel_right g _).symm⟩
  have h1 : (Eqv.matA D V g).map (Eqv.psiT D τ) = (Eqv.matA D V (Eqv.infOnly D V g)).map (Eqv.psiT D τ) := by
    rw [← Eqv.infMat_thetaC, ← Eqv.infMat_thetaC, Eqv.infMat_infOnly]
  rw [Eqv.matA_mul, Matrix.map_mul, h1, ← Matrix.map_mul, ← Eqv.matA_mul, mul_inv_cancel, Eqv.matA_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Take `rfl` from `Eqv.eq_thetaC D hθ`. Use `set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (Eqv.thetaC D τ) a`. Establish `hgs : Eqv.IsUnitFam D V gs` using `Eqv.infMat_unitary' D V a`. Establish `hu : ∀ s : Finset D.what₂.Tau, Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1)`. Introduce `s τ`.

Distinguish the cases in `hτ : τ ∈ s`. Simplify using `only [hτ, if_true]`. Conclude with `hgs τ`. Simplify using `only [hτ, if_false]`. Simplify using the standard rewrite rules.

Establish `key : ∀ s : Finset D.what₂.Tau, Eqv.famH D V _ (hu s) ∈ Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau (Eqv.thetaC D) V τ g}`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `e : Eqv.famH D V _ (hu ∅) = 1`.

Apply `Eqv.matA_inj D V` to reduce the goal to its premises. Rewrite using `[Eqv.matA_famH, Eqv.matA_one]`. Use `Eqv.famM_one D V using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `Submonoid.one_mem _`. Consider the case `insert τ0 s hτ0 ih`. Establish `e : Eqv.famH D V _ (hu (insert τ0 s)) = Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Eqv.famH D V _ (hu s)`. Apply `Eqv.matA_inj D V` to reduce the goal to its premises.

Rewrite using `[Eqv.matA_famH, Eqv.matA_mul, Eqv.matA_atH, Eqv.matA_famH]`. Apply `Eqv.mat_ext D` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[Matrix.map_mul, Eqv.psi_famM, Eqv.psi_atM, Eqv.psi_famM]`. Distinguish the cases in `h : τ = τ0`.

Substitute `h` using the available equality. Simplify using `[hτ0]`. Simplify using `[h]`. Rewrite using `[Matrix.map_mul, Eqv.fin_famM, Eqv.fin_atM, Eqv.fin_famM, Matrix.one_mul]`. Rewrite using `[e]`.

Use `Submonoid.mul_mem _ (Submonoid.subset_closure ⟨τ0, gs τ0, hgs τ0, ?_⟩) ih` and prove the remaining obligations. Conclude with `(Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)).symm`. Establish `e : a = Eqv.famH D V _ (hu Finset.univ)` using `Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])`. Rewrite using `[e]`. Conclude with `key Finset.univ`.
-/
theorem ginf_mem_closure {θ : Datum.InfFam D} (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) :
    a ∈ Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau θ V τ g} := by
  obtain rfl := Eqv.eq_thetaC D hθ
  classical
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (Eqv.thetaC D τ) a
  have hgs : Eqv.IsUnitFam D V gs := Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, Eqv.famH D V _ (hu s) ∈
      Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau (Eqv.thetaC D) V τ g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : Eqv.famH D V _ (hu ∅) = 1 := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_one]
        convert Eqv.famM_one D V using 2
        funext τ
        simp
      rw [e]
      exact Submonoid.one_mem _
    | insert τ0 s hτ0 ih =>
      have e : Eqv.famH D V _ (hu (insert τ0 s)) = Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Eqv.famH D V _ (hu s) := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_mul, Eqv.matA_atH, Eqv.matA_famH]
        apply Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Eqv.psi_famM, Eqv.psi_atM, Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Eqv.fin_famM, Eqv.fin_atM, Eqv.fin_famM, Matrix.one_mul]
      rw [e]
      refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨τ0, gs τ0, hgs τ0, ?_⟩) ih
      exact (Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)).symm
  have e : a = Eqv.famH D V _ (hu Finset.univ) :=
    Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  rw [e]
  exact key Finset.univ

end Adelic

section GenAd

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_adF_iff : F ∈ Bridge.AdForms ι ρ J χ ↔ ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := Iff.rfl

/- English proof (translation)
Simplify using `using hF 1 h k`.
-/
theorem adF_mul (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : G) (k : J) : F (h * k) = (χ k : ℂ) • F h := by
  simpa using hF 1 h k

/- English proof (translation)
Simplify using `using hF γ h 1`.
-/
theorem adF_rat (hF : F ∈ Bridge.AdForms ι ρ J χ) (γ : Γ) (h : G) : F (ι γ * h) = ρ γ (F h) := by
  simpa using hF γ h 1

/- English proof (translation)
Rewrite using `[map_mul]`. Conclude with `adF_mul hF (f g) ⟨f k, hk⟩`.
-/
theorem adF_comp_mul {G' : Type} [Group G'] (hF : F ∈ Bridge.AdForms ι ρ J χ) (f : G' →* G) (g k : G')
    (hk : f k ∈ J) : F (f (g * k)) = (χ ⟨f k, hk⟩ : ℂ) • F (f g) := by
  rw [map_mul]
  exact adF_mul hF (f g) ⟨f k, hk⟩

/- English proof (translation)
Rewrite using `[adF_comp_mul hF f g k hk, h1]`. Simplify using the standard rewrite rules.
-/
theorem adF_comp_mul_one {G' : Type} [Group G'] (hF : F ∈ Bridge.AdForms ι ρ J χ) (f : G' →* G) (g k : G')
    (hk : f k ∈ J) (h1 : χ ⟨f k, hk⟩ = 1) : F (f (g * k)) = F (f g) := by
  rw [adF_comp_mul hF f g k hk, h1]
  simp

/- English proof (translation)
Rewrite using `[adF_mul hF h k, hk]`. Simplify using the standard rewrite rules.
-/
theorem adF_mul_one (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : G) (k : J) (hk : χ k = 1) : F (h * k) = F h := by
  rw [adF_mul hF h k, hk]
  simp

end GenAd

section GenHom

variable {G H : Type} [Group G] [Group H] (f : G →* H)

/- English proof (translation)
Establish `h1 : f.rangeRestrict a = 1` using `Subtype.ext (by simpa [MonoidHom.mem_ker] using ha)`. Rewrite using `[map_mul, h1, mul_one]`.
-/
theorem rr_mul_ker (g a : G) (ha : a ∈ f.ker) : f.rangeRestrict (g * a) = f.rangeRestrict g := by
  have h1 : f.rangeRestrict a = 1 := Subtype.ext (by simpa [MonoidHom.mem_ker] using ha)
  rw [map_mul, h1, mul_one]

/- English proof (translation)
The claim follows from `map_mul _ g k`.
-/
theorem rr_mul (g k : G) : f.rangeRestrict (g * k) = f.rangeRestrict g * f.rangeRestrict k := map_mul _ g k

end GenHom

section Generic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) (c : CoefA V)
  (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)

def OpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) (χ' : J' →* ℂˣ) : Prop :=
  ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
    ∀ k ∈ U, ∃ hk : (finHom V).rangeRestrict k ∈ J', χ' ⟨_, hk⟩ = 1

def SmStable : Prop :=
  ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x ∈ M.sm τ, M.rep τ g x ∈ M.sm τ

/- English proof (translation)
Rewrite using `[mul_inv_rev, map_mul]`. Both sides reduce to the same expression.
-/
theorem rho_inv_mul (a b : GA D V) (w : c.W) : c.ρ (a * b)⁻¹ w = c.ρ b⁻¹ (c.ρ a⁻¹ w) := by
  rw [mul_inv_rev, map_mul]
  rfl

/- English proof (translation)
Use `show (c.ρ a⁻¹ * c.ρ a) w = w`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression.
-/
theorem rho_inv_self (a : GA D V) (w : c.W) : c.ρ a⁻¹ (c.ρ a w) = w := by
  show (c.ρ a⁻¹ * c.ρ a) w = w
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/- English proof (translation)
Use `show (c.ρ a * c.ρ a⁻¹) w = w`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.
-/
theorem rho_mul_inv (a : GA D V) (w : c.W) : c.ρ a (c.ρ a⁻¹ w) = w := by
  show (c.ρ a * c.ρ a⁻¹) w = w
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

/- English proof (translation)
Rewrite using `[hc.1 a ha]`. Both sides reduce to the same expression.
-/
theorem rho_of_GfC (hc : c.Is) {a : GA D V} (ha : a ∈ GfC V) (w : c.W) : c.ρ a w = w := by
  rw [hc.1 a ha]
  rfl

/- English proof (translation)
The claim follows from `Subtype.ext (MonoidHom.mem_ker.mp ha)`.
-/
theorem rr_of_GinfC {a : GA D V} (ha : a ∈ GinfC V) : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.mp ha)

/- English proof (translation)
Unfold `atTau`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `Subgroup.one_mem _`.
-/
theorem atTau_mem_GinfC (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact Subgroup.one_mem _

variable {θ M c pr}

def phiF (F : Bridge.Gf V → c.W) (t : SmT M) : GA D V → ℂ := fun g => pr (c.ρ g⁻¹ (F ((finHom V).rangeRestrict g))) t

/- English proof (translation)
Rewrite using `[PiTensorProduct.lift_symm]`. Both sides reduce to the same expression.
-/
theorem lift_symm_toMap_apply (F : Bridge.Gf V → c.W) (v : M.Vec) :
    PiTensorProduct.lift.symm (c.toMap pr F) v = phiF (pr := pr) F (PiTensorProduct.tprod ℂ v) := by
  rw [PiTensorProduct.lift_symm]
  rfl

variable {J' : Subgroup (Bridge.Gf V)} {χ' : J' →* ℂˣ} {F : Bridge.Gf V → c.W}

/- English proof (translation)
The claim follows from `adF_mul hF h k`.
-/
theorem adForms_mul (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ')
    (h : Bridge.Gf V) (k : J') : F (h * k) = (χ' k : ℂ) • F h := adF_mul hF h k

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratF_eq (γ : GA D V) (hγ : γ ∈ GQ V) : Bridge.ratF V ⟨γ, hγ⟩ = (finHom V).rangeRestrict γ := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coef_rho (γ : GA D V) (hγ : γ ∈ GQ V) (w : c.W) : c.coef.ρ ⟨γ, hγ⟩ w = c.ρ γ w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratF_eq' (γ : GQ V) : Bridge.ratF V γ = (finHom V).rangeRestrict (γ : GA D V) := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coef_rho' (γ : GQ V) (w : c.W) : c.coef.ρ γ w = c.ρ (γ : GA D V) w := rfl

/- English proof (translation)
Establish `e` using `adF_rat hF ⟨γ, hγ⟩ h`. Rewrite `e` using `[ratF_eq, coef_rho]`. Then use the resulting hypothesis.
-/
theorem adForms_rat (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ')
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : Bridge.Gf V) : F ((finHom V).rangeRestrict γ * h) = c.ρ γ (F h) := by
  have e := adF_rat hF ⟨γ, hγ⟩ h
  rwa [ratF_eq, coef_rho] at e

/- English proof (translation)
Establish `hℓ : Continuous ℓ` using `LinearMap.continuous_of_finiteDimensional ℓ`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g0`. Establish `hc : Continuous fun g => ℓ (ρ g⁻¹ (F (f g0)))` using `hℓ.comp ((hρ _).comp continuous_inv)`. Establish `hmem : ⇑(Homeomorph.mulLeft g0) '' (U : Set G) ∈ nhds g0` using `((Homeomorph.mulLeft g0).isOpenMap _ hUo).mem_nhds ⟨1, U.one_mem, by simp⟩`.

Establish `hn : (fun g => ℓ (ρ g⁻¹ (F (f g0)))) =ᶠ[nhds g0] (fun g => ℓ (ρ g⁻¹ (F (f g))))` using `by filter_upwards [hmem] with g hg`. Take `⟨u, hu, rfl⟩` from `hg`. Simplify using `only [Homeomorph.coe_mulLeft, hU g0 u hu]`. Conclude with `hc.continuousAt.congr hn`.
-/
theorem continuous_of_locConst {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : G →* Module.End ℂ W) (hρ : ∀ x, Continuous fun h => ρ h x) (f : G →* H) (F : H → W) (ℓ : W →ₗ[ℂ] ℂ)
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) (hU : ∀ g, ∀ u ∈ U, F (f (g * u)) = F (f g)) :
    Continuous fun g => ℓ (ρ g⁻¹ (F (f g))) := by
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  rw [continuous_iff_continuousAt]
  intro g0
  have hc : Continuous fun g => ℓ (ρ g⁻¹ (F (f g0))) := hℓ.comp ((hρ _).comp continuous_inv)
  have hmem : ⇑(Homeomorph.mulLeft g0) '' (U : Set G) ∈ nhds g0 :=
    ((Homeomorph.mulLeft g0).isOpenMap _ hUo).mem_nhds ⟨1, U.one_mem, by simp⟩
  have hn : (fun g => ℓ (ρ g⁻¹ (F (f g0)))) =ᶠ[nhds g0] (fun g => ℓ (ρ g⁻¹ (F (f g)))) := by
    filter_upwards [hmem] with g hg
    obtain ⟨u, hu, rfl⟩ := hg
    simp only [Homeomorph.coe_mulLeft, hU g0 u hu]
  exact hc.continuousAt.congr hn

/- English proof (translation)
Set `Φ : (W →ₗ[ℂ] ℂ) →ₗ[ℂ] (G → ℂ)` to `{ toFun := fun m g => m (ρ g⁻¹ (y g)) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hle : Submodule.span ℂ {ψ : G → ℂ | ∃ k ∈ K, ψ = fun g => ℓ (ρ (g * k)⁻¹ (y (g * k)))} ≤ LinearMap.range Φ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `ψ ⟨k, hk, rfl⟩`. Use `⟨ℓ.comp (ρ k⁻¹), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Simplify using `only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, hy g k hk, mul_inv_rev, map_mul, Module.End.mul_apply]`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem fd_span_translates {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W) (y : G → W) (K : Subgroup G)
    (hy : ∀ g, ∀ k ∈ K, y (g * k) = y g) (ℓ : W →ₗ[ℂ] ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ {ψ : G → ℂ | ∃ k ∈ K, ψ = fun g => ℓ (ρ (g * k)⁻¹ (y (g * k)))}) := by
  let Φ : (W →ₗ[ℂ] ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun m g => m (ρ g⁻¹ (y g))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : Submodule.span ℂ {ψ : G → ℂ | ∃ k ∈ K, ψ = fun g => ℓ (ρ (g * k)⁻¹ (y (g * k)))} ≤
      LinearMap.range Φ := by
    rw [Submodule.span_le]
    rintro ψ ⟨k, hk, rfl⟩
    refine ⟨ℓ.comp (ρ k⁻¹), ?_⟩
    funext g
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, hy g k hk, mul_inv_rev, map_mul,
      Module.End.mul_apply]
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Introduce `γ hγ g`. Simplify using `only [phiF]`. Rewrite using `[map_mul, adForms_rat hF γ hγ, rho_inv_mul, rho_inv_self]`.
-/
theorem phiF_left (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ') (t : SmT M) :
    ∀ γ ∈ GQ V, ∀ g, phiF (pr := pr) F t (γ * g) = phiF (pr := pr) F t g := by
  intro γ hγ g
  simp only [phiF]
  rw [map_mul, adForms_rat hF γ hγ, rho_inv_mul, rho_inv_self]

/- English proof (translation)
Introduce `k hk hkG g`. Take `⟨hk', h1⟩` from `hUk k hk`. Simplify using `only [phiF]`. Establish `e : F ((finHom V).rangeRestrict g * (finHom V).rangeRestrict k) = F ((finHom V).rangeRestrict g)` using `adF_mul_one hF _ ⟨_, hk'⟩ h1`. Rewrite using `[map_mul, e, rho_inv_mul, rho_of_GfC c hc (inv_mem hkG)]`.
-/
theorem phiF_level (hc : c.Is) (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ') (t : SmT M)
    (U : Subgroup (GA D V)) (hUk : ∀ k ∈ U, ∃ hk : (finHom V).rangeRestrict k ∈ J', χ' ⟨_, hk⟩ = 1) :
    ∀ k ∈ U, k ∈ GfC V → ∀ g, phiF (pr := pr) F t (g * k) = phiF (pr := pr) F t g := by
  intro k hk hkG g
  obtain ⟨hk', h1⟩ := hUk k hk
  simp only [phiF]
  have e : F ((finHom V).rangeRestrict g * (finHom V).rangeRestrict k) = F ((finHom V).rangeRestrict g) :=
    adF_mul_one hF _ ⟨_, hk'⟩ h1
  rw [map_mul, e, rho_inv_mul, rho_of_GfC c hc (inv_mem hkG)]

/- English proof (translation)
Take `⟨U, hUo, hUk⟩` from `hU`. Establish `hcont : Continuous (phiF (pr` using `pr) F t) := by`. Use `(Eqv.ga_facts D V).1` as an intermediate fact. Use `continuous_of_locConst c.ρ hc.2.2.1 (finHom V).rangeRestrict F (pr.flip t) U hUo ?_` and prove the remaining obligations. Introduce `g u hu`.

Take `⟨hk', hχ⟩` from `hUk u hu`. Conclude with `adF_comp_mul_one hF (finHom V).rangeRestrict g u hk' hχ`. Use `⟨⟨phiF_left hF t, ⟨U, hUo, phiF_level hc hF t U hUk⟩, hcont⟩, ?_⟩` and prove the remaining obligations. Establish `hy : ∀ g, ∀ k ∈ GinfC V, F ((finHom V).rangeRestrict (g * k)) = F ((finHom V).rangeRestrict g)`. Introduce `g k hk`.

Rewrite using `[rr_mul_ker (finHom V) g k hk]`. Conclude with `fd_span_translates c.ρ (fun g => F ((finHom V).rangeRestrict g)) (GinfC V) hy (pr.flip t)`.
-/
theorem isAutFunDef_phiF (hc : c.Is) (hU : OpenLev V J' χ')
    (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ') (t : SmT M) : IsAutFunDef V (phiF (pr := pr) F t) := by
  obtain ⟨U, hUo, hUk⟩ := hU
  have hcont : Continuous (phiF (pr := pr) F t) := by
    have := (Eqv.ga_facts D V).1
    refine continuous_of_locConst c.ρ hc.2.2.1 (finHom V).rangeRestrict F (pr.flip t) U hUo ?_
    intro g u hu
    obtain ⟨hk', hχ⟩ := hUk u hu
    exact adF_comp_mul_one hF (finHom V).rangeRestrict g u hk' hχ
  refine ⟨⟨phiF_left hF t, ⟨U, hUo, phiF_level hc hF t U hUk⟩, hcont⟩, ?_⟩
  have hy : ∀ g, ∀ k ∈ GinfC V, F ((finHom V).rangeRestrict (g * k)) = F ((finHom V).rangeRestrict g) := by
    intro g k hk; rw [rr_mul_ker (finHom V) g k hk]
  exact fd_span_translates c.ρ (fun g => F ((finHom V).rangeRestrict g)) (GinfC V) hy (pr.flip t)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `k hk g`. Take `⟨hkG, hk', hχ⟩` from `hlev k hk`. Simplify using `only [phiF]`. Establish `e : F ((finHom V).rangeRestrict g * (finHom V).rangeRestrict k) = (χ' ⟨_, hk'⟩ : ℂ) • F ((finHom V).rangeRestrict g)` using `adForms_mul hF _ ⟨_, hk'⟩`. Rewrite using `[map_mul, e, rho_inv_mul, rho_of_GfC c hc (inv_mem hkG), map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, hχ]`.
-/
theorem toMap_lev (hc : c.Is) (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ') {J : Set (GA D V)}
    {χ : GA D V → ℂ} (hlev : ∀ k ∈ J, k ∈ GfC V ∧ ∃ hk : (finHom V).rangeRestrict k ∈ J', χ k = χ' ⟨_, hk⟩)
    (t : SmT M) : ∀ k ∈ J, ∀ g, phiF (pr := pr) F t (g * k) = χ k * phiF (pr := pr) F t g := by
  intro k hk g
  obtain ⟨hkG, hk', hχ⟩ := hlev k hk
  simp only [phiF]
  have e : F ((finHom V).rangeRestrict g * (finHom V).rangeRestrict k) =
      (χ' ⟨_, hk'⟩ : ℂ) • F ((finHom V).rangeRestrict g) := adForms_mul hF _ ⟨_, hk'⟩
  rw [map_mul, e, rho_inv_mul, rho_of_GfC c hc (inv_mem hkG), map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hχ]

open Classical in
/- English proof (translation)
Establish `ha` using `atTau_mem_GinfC (V := V) θ τ g`. Simplify using `only [phiF]`. Rewrite using `[rr_mul_ker (finHom V) x _ ha, rho_inv_mul]`. Use `hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ (c.ρ x⁻¹ (F ((finHom V).rangeRestrict x)))) v w hw` as an intermediate fact. Rewrite `this` using `[rho_mul_inv]`.

Conclude with `this`.
-/
theorem toMap_equiv (hpr : IsDualPair θ M c pr) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) (x : GA D V) :
    phiF (pr := pr) F (PiTensorProduct.tprod ℂ (Function.update v τ w)) x =
      phiF (pr := pr) F (PiTensorProduct.tprod ℂ v) (x * atTau θ V τ g) := by
  have ha := atTau_mem_GinfC (V := V) θ τ g
  simp only [phiF]
  rw [rr_mul_ker (finHom V) x _ ha, rho_inv_mul]
  have := hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ (c.ρ x⁻¹ (F ((finHom V).rangeRestrict x)))) v w hw
  rw [rho_mul_inv] at this
  exact this

open Classical in
/- English proof (translation)
Use `haveI := hfd τ`. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ((LinearMap.proj x).comp ((PiTensorProduct.lift.symm (c.toMap pr F)).toLinearMap v τ))`. Use `⟨ℓ, ⟨[[]], ‖LinearMap.toContinuousLinearMap ℓ‖, by simp, fun w _ => ?_⟩, fun w => ?_⟩` and prove the remaining obligations. Simplify using `using (LinearMap.toContinuousLinearMap ℓ).le_opNorm w`. Use `LinearMap.congr_fun hℓ w` as an intermediate fact.

Simplify using `using this`.
-/
theorem toMap_cont (hfd : ∀ τ, FiniteDimensional ℂ (M.H τ)) (F : Bridge.Gf V → c.W) (τ : D.what₂.Tau) (v : M.Vec)
    (x : GA D V) : ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = PiTensorProduct.lift.symm (c.toMap pr F) (Function.update v τ w) x := by
  haveI := hfd τ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend
    ((LinearMap.proj x).comp ((PiTensorProduct.lift.symm (c.toMap pr F)).toLinearMap v τ))
  refine ⟨ℓ, ⟨[[]], ‖LinearMap.toContinuousLinearMap ℓ‖, by simp, fun w _ => ?_⟩, fun w => ?_⟩
  · simpa using (LinearMap.toContinuousLinearMap ℓ).le_opNorm w
  · have := LinearMap.congr_fun hℓ w
    simpa using this

open Classical in

/- English proof (translation)
Establish `e : ∀ v, PiTensorProduct.lift.symm (c.toMap pr F) v = phiF (pr` using `pr) F (PiTensorProduct.tprod ℂ v) := lift_symm_toMap_apply F`. Use `⟨fun v => ?_, fun v => ?_, fun v => ?_, fun τ g hg v w hw => ?_, toMap_cont hfd F⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(hsm θ hθ V hsig hdef _).1 (isAutFunDef_phiF hc hU hF _)`. Introduce `r C hC`.

Conclude with `(hani r C hC).elim`. Rewrite using `[e]`. Conclude with `toMap_lev hc hF hlev _`. Rewrite using `[e, e]`. Use function extensionality and compare the values at `x`.

Conclude with `toMap_equiv hpr τ g hg v w hw x`.
-/
theorem isMultMap_toMap (hc : c.Is) (hpr : IsDualPair θ M c pr) (hθ : IsInfFam θ) (hsm : AutFunDefIffSm D)
    (hsig : V.SigOK) (hdef : V.IsDefinite)
    (hani : ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), ¬ IsIsoFrame V C)
    (hfd : ∀ τ, FiniteDimensional ℂ (M.H τ)) (hU : OpenLev V J' χ') {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hlev : ∀ k ∈ J, k ∈ GfC V ∧ ∃ hk : (finHom V).rangeRestrict k ∈ J', χ k = χ' ⟨_, hk⟩)
    (hF : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ') :
    IsMultMap θ M J χ (PiTensorProduct.lift.symm (c.toMap pr F)) := by
  have e : ∀ v, PiTensorProduct.lift.symm (c.toMap pr F) v = phiF (pr := pr) F (PiTensorProduct.tprod ℂ v) :=
    lift_symm_toMap_apply F
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun τ g hg v w hw => ?_, toMap_cont hfd F⟩
  · rw [e]; exact (hsm θ hθ V hsig hdef _).1 (isAutFunDef_phiF hc hU hF _)
  · intro r C hC; exact (hani r C hC).elim
  · rw [e]; exact toMap_lev hc hF hlev _
  · rw [e, e]; funext x; exact toMap_equiv hpr τ g hg v w hw x

def evL (T : MMap M) (x : GA D V) : SmT M →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (PiTensorProduct.lift T)

/- English proof (translation)
Simplify using `[evL]`.
-/
theorem evL_tprod (T : MMap M) (x : GA D V) (v : M.Vec) : evL T x (PiTensorProduct.tprod ℂ v) = T v x := by
  simp [evL]

/- English proof (translation)
Apply `PiTensorProduct.ext` to reduce the goal to its premises. Use extensionality with `v`. Rewrite using `[LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, h, evL_tprod]`.
-/
theorem evL_ext (T : MMap M) (ℓ : SmT M →ₗ[ℂ] ℂ) (x : GA D V) (h : ∀ v, ℓ (PiTensorProduct.tprod ℂ v) = T v x) :
    ℓ = evL T x := by
  apply PiTensorProduct.ext
  ext v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, h, evL_tprod]

/- English proof (translation)
Use `symm`. Apply `evL_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[evL_tprod T z v]`. Conclude with `((hT.aut v).left γ hγ z).symm`.
-/
theorem evL_left {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (γ : GA D V)
    (hγ : γ ∈ GQ V) (z : GA D V) : evL T (γ * z) = evL T z := by
  symm; apply evL_ext; intro v
  rw [evL_tprod T z v]; exact ((hT.aut v).left γ hγ z).symm

/- English proof (translation)
Apply `PiTensorProduct.ext` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, evL_tprod, smul_eq_mul]`. Conclude with `hT.lev v κ hκ z`.
-/
theorem evL_lev {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (κ : GA D V)
    (hκ : κ ∈ J) (z : GA D V) : evL T (z * κ) = χ κ • evL T z := by
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, evL_tprod, smul_eq_mul]
  exact hT.lev v κ hκ z

open Classical in

/- English proof (translation)
Introduce `a ha`. Use `Submonoid.closure_induction (motive := fun a _ => ∀ x (w : c.W), pr w = evL T x → pr (c.ρ a⁻¹ w) = evL T (x * a)) ?_ ?_ ?_ (ginf_mem_closure hθ ha)` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, g, hg, rfl⟩ x w hw`. Apply `evL_ext` to reduce the goal to its premises. Introduce `v`.

Set `u : M.sm τ` to `⟨M.rep τ g (v τ), hst τ g hg _ (v τ).2⟩`. Establish `h1` using `hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ w) v u rfl`. Rewrite `h1` using `[rho_mul_inv]`. Rewrite using `[← h1, hw, evL_tprod]`. Establish `h2` using `congrFun (hT.equiv τ g hg v u rfl) x`.

Rewrite using `[h2]`. Both sides reduce to the same expression. Introduce `x w hw`. Rewrite using `[inv_one, map_one, mul_one]`. Conclude with `hw`.

Introduce `a b _ _ iha ihb x w hw`. Rewrite using `[rho_inv_mul, ← mul_assoc]`. Conclude with `ihb _ _ (iha x w hw)`.
-/
theorem pr_rho_inv (hpr : IsDualPair θ M c pr) (hθ : IsInfFam θ) (hst : SmStable M) {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) :
    ∀ a ∈ GinfC V, ∀ x (w : c.W), pr w = evL T x → pr (c.ρ a⁻¹ w) = evL T (x * a) := by
  intro a ha
  refine Submonoid.closure_induction
    (motive := fun a _ => ∀ x (w : c.W), pr w = evL T x → pr (c.ρ a⁻¹ w) = evL T (x * a))
    ?_ ?_ ?_ (ginf_mem_closure hθ ha)
  · rintro _ ⟨τ, g, hg, rfl⟩ x w hw
    apply evL_ext
    intro v
    let u : M.sm τ := ⟨M.rep τ g (v τ), hst τ g hg _ (v τ).2⟩
    have h1 := hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ w) v u rfl
    rw [rho_mul_inv] at h1
    rw [← h1, hw, evL_tprod]
    have h2 := congrFun (hT.equiv τ g hg v u rfl) x
    rw [h2]; rfl
  · intro x w hw
    rw [inv_one, map_one, mul_one]; exact hw
  · intro a b _ _ iha ihb x w hw
    rw [rho_inv_mul, ← mul_assoc]
    exact ihb _ _ (iha x w hw)

/- English proof (translation)
Take `⟨g, rfl⟩` from `(finHom V).rangeRestrict_surjective y`. Take `⟨h, hh, a, ha, rfl⟩` from `ga_decomp g`. Conclude with `⟨h, hh, by rw [map_mul, rr_of_GinfC ha, mul_one]⟩`.
-/
theorem exists_lift (y : Bridge.Gf V) : ∃ h, h ∈ GfC V ∧ (finHom V).rangeRestrict h = y := by
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective y
  obtain ⟨h, hh, a, ha, rfl⟩ := ga_decomp g
  exact ⟨h, hh, by rw [map_mul, rr_of_GinfC ha, mul_one]⟩

/- English proof (translation)
Establish `h1 : h⁻¹ * h' ∈ GinfC V` using `by show h⁻¹ * h' ∈ (finHom V).ker`. Establish `e2` using `congrArg Subtype.val e`. Simplify using `only [MonoidHom.coe_rangeRestrict] at e2`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]`. Establish `h2 : h⁻¹ * h' ∈ GfC V` using `mul_mem (inv_mem hh) hh'`.

Establish `h3 : h⁻¹ * h' ∈ GinfC V ⊓ GfC V` using `⟨h1, h2⟩`. Rewrite `h3` using `[inf_GinfC_GfC', Subgroup.mem_bot]`. Conclude with `inv_mul_eq_one.mp h3`.
-/
theorem lift_unique {h h' : GA D V} (hh : h ∈ GfC V) (hh' : h' ∈ GfC V)
    (e : (finHom V).rangeRestrict h = (finHom V).rangeRestrict h') : h = h' := by
  have h1 : h⁻¹ * h' ∈ GinfC V := by
    show h⁻¹ * h' ∈ (finHom V).ker
    have e2 := congrArg Subtype.val e
    simp only [MonoidHom.coe_rangeRestrict] at e2
    rw [MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]
  have h2 : h⁻¹ * h' ∈ GfC V := mul_mem (inv_mem hh) hh'
  have h3 : h⁻¹ * h' ∈ GinfC V ⊓ GfC V := ⟨h1, h2⟩
  rw [inf_GinfC_GfC', Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3

set_option maxHeartbeats 4000000 in
open Classical in

/- English proof (translation)
Introduce `γ h k`. Establish `hkm : (finHom V).rangeRestrict (lf k) ∈ J'` using `by rw [hlf]; exact k.2`. Take `⟨hκJ, hχκ⟩` from `hlev (lf k) (hlfG k) hkm`. Establish `hk' : (⟨_, hkm⟩ : J') = k` using `Subtype.ext (hlf _)`. Rewrite `hχκ` using `[hk']`.

Establish `hz : (finHom V).rangeRestrict ((γ : GA D V) * (lf h * lf k)) = Bridge.ratF V γ * h * k`. Rewrite using `[map_mul, map_mul, hlf, hlf, ← ratF_eq', mul_assoc]`. Establish `ha : (lf (Bridge.ratF V γ * h * k))⁻¹ * ((γ : GA D V) * (lf h * lf k)) ∈ GinfC V` using `by show _ ∈ (finHom V).ker`. Establish `e2` using `congrArg Subtype.val ((hlf (Bridge.ratF V γ * h * k)).trans hz.symm)`. Simplify using `only [MonoidHom.coe_rangeRestrict] at e2`.

Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]`. Establish `key` using `K _ ha _ _ (hF (Bridge.ratF V γ * h * k))`. Rewrite `key` using `[mul_inv_cancel_left, evL_left hT (γ : GA D V) γ.2, evL_lev hT (lf k) hκJ, hχκ, ← hF h, ← map_smul pr]`. Establish `e1` using `hperf.1 key`. Establish `hρa : c.ρ ((lf (Bridge.ratF V γ * h * k))⁻¹ * ((γ : GA D V) * (lf h * lf k))) = c.ρ (γ : GA D V)`.

Rewrite using `[map_mul, map_mul, hc.1 _ (inv_mem (hlfG _)), hc.1 _ (mul_mem (hlfG h) (hlfG k)), one_mul, mul_one]`. Generalize the expression as in `(lf (Bridge.ratF V γ * h * k))⁻¹ * ((γ : GA D V) * (lf h * lf k)) = a at e1 hρa`. Establish `e4` using `congrArg (c.ρ a) e1`. Rewrite `e4` using `[rho_mul_inv, map_smul, hρa]`. Rewrite using `[e4]`.

Both sides reduce to the same expression.
-/
theorem adForms_of_lift (hc : c.Is) (hperf : Function.Bijective pr) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hlev : ∀ κ ∈ GfC V, ∀ hk : (finHom V).rangeRestrict κ ∈ J', κ ∈ J ∧ χ κ = χ' ⟨_, hk⟩)
    {T : MMap M} (hT : IsMultMap θ M J χ T)
    (K : ∀ a ∈ GinfC V, ∀ x (w : c.W), pr w = evL T x → pr (c.ρ a⁻¹ w) = evL T (x * a))
    (lf : Bridge.Gf V → GA D V) (hlfG : ∀ y, lf y ∈ GfC V) (hlf : ∀ y, (finHom V).rangeRestrict (lf y) = y)
    (F : Bridge.Gf V → c.W) (hF : ∀ y, pr (F y) = evL T (lf y)) :
    F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ' := by
  intro γ h k
  have hkm : (finHom V).rangeRestrict (lf k) ∈ J' := by rw [hlf]; exact k.2
  obtain ⟨hκJ, hχκ⟩ := hlev (lf k) (hlfG k) hkm
  have hk' : (⟨_, hkm⟩ : J') = k := Subtype.ext (hlf _)
  rw [hk'] at hχκ
  have hz : (finHom V).rangeRestrict ((γ : GA D V) * (lf h * lf k)) = Bridge.ratF V γ * h * k := by
    rw [map_mul, map_mul, hlf, hlf, ← ratF_eq', mul_assoc]
  have ha : (lf (Bridge.ratF V γ * h * k))⁻¹ * ((γ : GA D V) * (lf h * lf k)) ∈ GinfC V := by
    show _ ∈ (finHom V).ker
    have e2 := congrArg Subtype.val ((hlf (Bridge.ratF V γ * h * k)).trans hz.symm)
    simp only [MonoidHom.coe_rangeRestrict] at e2
    rw [MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]
  have key := K _ ha _ _ (hF (Bridge.ratF V γ * h * k))
  rw [mul_inv_cancel_left, evL_left hT (γ : GA D V) γ.2, evL_lev hT (lf k) hκJ, hχκ, ← hF h, ← map_smul pr] at key
  have e1 := hperf.1 key
  have hρa : c.ρ ((lf (Bridge.ratF V γ * h * k))⁻¹ * ((γ : GA D V) * (lf h * lf k))) = c.ρ (γ : GA D V) := by
    rw [map_mul, map_mul, hc.1 _ (inv_mem (hlfG _)), hc.1 _ (mul_mem (hlfG h) (hlfG k)), one_mul, mul_one]
  generalize (lf (Bridge.ratF V γ * h * k))⁻¹ * ((γ : GA D V) * (lf h * lf k)) = a at e1 hρa
  have e4 := congrArg (c.ρ a) e1
  rw [rho_mul_inv, map_smul, hρa] at e4
  rw [e4]
  rfl

open Classical in

/- English proof (translation)
Use `choose lf hlfG hlf using (exists_lift (V := V))`. Set `F : Bridge.Gf V → c.W` to `fun y => (Equiv.ofBijective pr hperf).symm (evL T (lf y))`. Establish `hF : ∀ y, pr (F y) = evL T (lf y)` using `fun y => (Equiv.ofBijective pr hperf).apply_symm_apply _`. Establish `K` using `pr_rho_inv hpr hθ hst hT`. Use `⟨F, adForms_of_lift hc hperf hlev hT K lf hlfG hlf F hF, ?_⟩` and prove the remaining obligations.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use function extensionality and compare the values at `h`. Establish `hxG : lf ((finHom V).rangeRestrict h) ∈ GfC V` using `hlfG _`. Establish `ha : (lf ((finHom V).rangeRestrict h))⁻¹ * h ∈ GinfC V` using `by show _ ∈ (finHom V).ker`.

Establish `e2` using `congrArg Subtype.val (hlf ((finHom V).rangeRestrict h))`. Simplify using `only [MonoidHom.coe_rangeRestrict] at e2`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]`. Establish `key` using `K _ ha _ (F ((finHom V).rangeRestrict h)) (hF _)`. Rewrite `key` using `[mul_inv_cancel_left]`.

Establish `e3 : c.ρ h⁻¹ (F ((finHom V).rangeRestrict h)) = c.ρ ((lf ((finHom V).rangeRestrict h))⁻¹ * h)⁻¹ (F ((finHom V).rangeRestrict h))`. Rewrite using `[rho_inv_mul, rho_of_GfC c hc (inv_mem (inv_mem hxG))]`. Use `show pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h))) v = evL T h v`. Rewrite using `[e3, key]`.
-/
theorem exists_adForm (hc : c.Is) (hpr : IsDualPair θ M c pr) (hθ : IsInfFam θ) (hperf : Function.Bijective pr)
    (hst : SmStable M) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hlev : ∀ κ ∈ GfC V, ∀ hk : (finHom V).rangeRestrict κ ∈ J', κ ∈ J ∧ χ κ = χ' ⟨_, hk⟩)
    {T : MMap M} (hT : IsMultMap θ M J χ T) :
    ∃ F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J' χ', c.toMap pr F = PiTensorProduct.lift T := by
  choose lf hlfG hlf using (exists_lift (V := V))
  let F : Bridge.Gf V → c.W := fun y => (Equiv.ofBijective pr hperf).symm (evL T (lf y))
  have hF : ∀ y, pr (F y) = evL T (lf y) := fun y => (Equiv.ofBijective pr hperf).apply_symm_apply _
  have K := pr_rho_inv hpr hθ hst hT
  refine ⟨F, adForms_of_lift hc hperf hlev hT K lf hlfG hlf F hF, ?_⟩
  apply LinearMap.ext
  intro v
  funext h
  have hxG : lf ((finHom V).rangeRestrict h) ∈ GfC V := hlfG _
  have ha : (lf ((finHom V).rangeRestrict h))⁻¹ * h ∈ GinfC V := by
    show _ ∈ (finHom V).ker
    have e2 := congrArg Subtype.val (hlf ((finHom V).rangeRestrict h))
    simp only [MonoidHom.coe_rangeRestrict] at e2
    rw [MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]
  have key := K _ ha _ (F ((finHom V).rangeRestrict h)) (hF _)
  rw [mul_inv_cancel_left] at key
  have e3 : c.ρ h⁻¹ (F ((finHom V).rangeRestrict h)) =
      c.ρ ((lf ((finHom V).rangeRestrict h))⁻¹ * h)⁻¹ (F ((finHom V).rangeRestrict h)) := by
    rw [rho_inv_mul, rho_of_GfC c hc (inv_mem (inv_mem hxG))]
  show pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h))) v = evL T h v
  rw [e3, key]

end Generic

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def TopMultBody (R : RealDat D A Ks) : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
    Mult.MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

open Classical in

/- English proof (translation)
Introduce `t`. Establish `hlev1 : ∀ k ∈ levS _ R.βX (R.datXt t), k ∈ GfC D.sp.X' ∧ ∃ hk : (finHom D.sp.X').rangeRestrict k ∈ (levEnv _ R.βX (R.datXt t)).J, levChi _ R.βX (R.datXt t) k = (levEnv _ R.βX (R.datXt t)).χ ⟨_, hk⟩` using `fun k hk => ⟨hk.1, hk.2, rfl⟩`. Establish `hlev2 : ∀ κ ∈ GfC D.sp.X', ∀ hk : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv _ R.βX (R.datXt t)).J, κ ∈ levS _ R.βX (R.datXt t) ∧ levChi _ R.βX (R.datXt t) κ = (levEnv _ R.βX (R.datXt t)).χ ⟨_, hk⟩` using `fun κ hκ hk => ⟨⟨hκ, hk⟩, rfl⟩`. Rewrite using `[LinearMap.range_comp, (hHX t).2.1]`. Unfold `Mult.MultT Mult.Mult`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Use `⟨PiTensorProduct.lift.symm (R.cX.toMap R.prX F), Submodule.subset_span ?_, LinearEquiv.apply_symm_apply _ _⟩` and prove the remaining obligations. Conclude with `isMultMap_toMap hcX hprX hinf hsm hsig hdef hani hfd (hU t) hlev1 hF`. Rewrite using `[Submodule.map_span_le]`.

Introduce `T hT`. Take `⟨F, hF, hFT⟩` from `exists_adForm hcX hprX hinf hperf hst hlev2 hT`. Conclude with `⟨F, hF, hFT⟩`.
-/
theorem topMult_of (R : RealDat D A Ks) (hcX : R.cX.Is) (hprX : IsDualPair R.θ R.MX R.cX R.prX)
    (hHX : R.models_HX) (hinf : IsInfFam R.θ) (hsm : AutFunDefIffSm D) (hsig : D.sp.X'.SigOK)
    (hdef : D.sp.X'.IsDefinite)
    (hani : ∀ (r : ℕ) (C : Matrix (Fin D.sp.X'.rank) (Fin r) D.host.E), ¬ IsIsoFrame D.sp.X' C)
    (hfd : ∀ τ, FiniteDimensional ℂ (R.MX.H τ)) (hst : SmStable R.MX) (hperf : Function.Bijective R.prX)
    (hU : ∀ t, OpenLev D.sp.X' (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ) :
    TopMultBody R := by
  intro t
  have hlev1 : ∀ k ∈ levS _ R.βX (R.datXt t), k ∈ GfC D.sp.X' ∧
      ∃ hk : (finHom D.sp.X').rangeRestrict k ∈ (levEnv _ R.βX (R.datXt t)).J,
        levChi _ R.βX (R.datXt t) k = (levEnv _ R.βX (R.datXt t)).χ ⟨_, hk⟩ :=
    fun k hk => ⟨hk.1, hk.2, rfl⟩
  have hlev2 : ∀ κ ∈ GfC D.sp.X', ∀ hk : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv _ R.βX (R.datXt t)).J,
      κ ∈ levS _ R.βX (R.datXt t) ∧ levChi _ R.βX (R.datXt t) κ = (levEnv _ R.βX (R.datXt t)).χ ⟨_, hk⟩ :=
    fun κ hκ hk => ⟨⟨hκ, hk⟩, rfl⟩
  rw [LinearMap.range_comp, (hHX t).2.1]
  unfold Mult.MultT Mult.Mult
  apply le_antisymm
  · rintro _ ⟨F, hF, rfl⟩
    refine ⟨PiTensorProduct.lift.symm (R.cX.toMap R.prX F), Submodule.subset_span ?_, LinearEquiv.apply_symm_apply _ _⟩
    exact isMultMap_toMap hcX hprX hinf hsm hsig hdef hani hfd (hU t) hlev1 hF
  · rw [Submodule.map_span_le]
    intro T hT
    obtain ⟨F, hF, hFT⟩ := exists_adForm hcX hprX hinf hperf hst hlev2 hT
    exact ⟨F, hF, hFT⟩

/- English proof (translation)
The claim follows from `topMult_of R hcX hprX hHX hinf hsm hsig hdef hani hfd hst hperf hU`.
-/
theorem topMultH_of (R : RealDat D A Ks) (hcX : R.cX.Is) (hprX : IsDualPair R.θ R.MX R.cX R.prX)
    (hHX : R.models_HX) (hinf : IsInfFam R.θ) (hsm : AutFunDefIffSm D) (hsig : D.sp.X'.SigOK)
    (hdef : D.sp.X'.IsDefinite)
    (hani : ∀ (r : ℕ) (C : Matrix (Fin D.sp.X'.rank) (Fin r) D.host.E), ¬ IsIsoFrame D.sp.X' C)
    (hfd : ∀ τ, FiniteDimensional ℂ (R.MX.H τ)) (hst : SmStable R.MX) (hperf : Function.Bijective R.prX)
    (hU : ∀ t, OpenLev D.sp.X' (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ) :
    Formalism.IndefR.RecTie.TopMultH R := topMult_of R hcX hprX hHX hinf hsm hsig hdef hani hfd hst hperf hU

end Real

end Formalism.IndefR.TopMult
