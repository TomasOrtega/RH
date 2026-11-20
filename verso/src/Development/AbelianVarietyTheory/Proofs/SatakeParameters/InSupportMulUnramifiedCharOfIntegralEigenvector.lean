import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenform
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.SphSupport

open ValuativeRel Cardinal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[Matrix.mul_apply, mul_comm]`.
-/
theorem gl_one_comm (x y : GL (Fin 1) k) : x * y = y * x := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

/- English proof (translation)
The claim follows from `funext fun a => gl_one_comm (g a) (h a)`.
-/
theorem levi_comm {m : ℕ} (g h : Levi k (fun _ : Fin m => Fin 1)) : g * h = h * g :=
  funext fun a => gl_one_comm (g a) (h a)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_one]`.
-/
theorem scalar_det_fin_one (g : GL (Fin 1) k) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g) = g := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_one]

/- English proof (translation)
Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`.
-/
theorem det_scalar_fin_one (z : kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

/- English proof (translation)
Introduce `h0`. Set `σ' : Representation ℂ (GL (Fin m) k) V` to `twist σ (detChar (Fin m) χ⁻¹)`. Set `π : Irr k m` to `⟨V, σ', isSmooth_twist hs hχ.inv.detChar, GlobalTheory.LocGL.isIrreducible_twist hi _⟩`. Establish `hker : twKer σ' (unipRad k e) 1 = twKer σ (unipRad k e) 1`. Unfold `twKer`.

Use `congr 1`. Use extensionality with `w`. Apply the tactic sequence `constructor <;> rintro ⟨u, v, rfl⟩ <;> refine ⟨u, v, ?_⟩ <;>`. Simplify using `[σ', det_eq_one_of_mem_unipRad k u.2]`. Establish `hle : KOne k (Fin m) ⊔ (unipRad k e ⊓ KO k (Fin m)) ≤ KO k (Fin m)` using `sup_le (Subgroup.map_le_range _ _) inf_le_right`.

Use `hy (hD k m s d e π y ?_ ?_)` and prove the remaining obligations. Introduce `h`. Establish `hKO` using `hle h.2`. Use `show σ' h y = _`. Simplify using `only [σ', twist_apply, detChar_apply, hK _ hKO, smul_smul, MonoidHom.inv_apply]`.

Simplify using the standard rewrite rules. Use `show (Submodule.Quotient.mk y : V ⧸ twKer σ' (unipRad k e) 1) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, hker]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 h0`.
-/
theorem mk_ne_zero (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hχ : IsSmoothChar χ) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y)
    {s : ℕ} (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin m) :
    (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) ≠ 0 := by
  intro h0
  let σ' : Representation ℂ (GL (Fin m) k) V := twist σ (detChar (Fin m) χ⁻¹)
  let π : Irr k m := ⟨V, σ', isSmooth_twist hs hχ.inv.detChar, GlobalTheory.LocGL.isIrreducible_twist hi _⟩
  have hker : twKer σ' (unipRad k e) 1 = twKer σ (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor <;> rintro ⟨u, v, rfl⟩ <;> refine ⟨u, v, ?_⟩ <;>
      simp [σ', det_eq_one_of_mem_unipRad k u.2]
  have hle : KOne k (Fin m) ⊔ (unipRad k e ⊓ KO k (Fin m)) ≤ KO k (Fin m) :=
    sup_le (Subgroup.map_le_range _ _) inf_le_right
  refine hy (hD k m s d e π y ?_ ?_)
  · intro h
    have hKO := hle h.2
    show σ' h y = _
    simp only [σ', twist_apply, detChar_apply, hK _ hKO, smul_smul, MonoidHom.inv_apply]
    simp
  · show (Submodule.Quotient.mk y : V ⧸ twKer σ' (unipRad k e) 1) = 0
    rw [Submodule.Quotient.mk_eq_zero, hker]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0

/- English proof (translation)
Set `e : (Σ _ : Fin m, Fin 1) ≃ Fin m` to `Equiv.sigmaUnique (Fin m) fun _ => Fin 1`. Establish `hy'` using `mk_ne_zero hD σ χ y hs hi hχ hy hK (fun _ : Fin m => 1) e`. Set `a0 : Fin m` to `⟨0, hm⟩`. Set `S : Set (Levi k (fun _ : Fin m => Fin 1))` to `{g | ∀ a, valuation k ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) = 1}`. Set `θ : Levi k (fun _ : Fin m => Fin 1) → ℂ` to `fun g => (((deltaHalf k (fun _ : Fin m => Fin 1) g)⁻¹ : ℂˣ) : ℂ) * (χ (Matrix.GeneralLinearGroup.det (leviEmb k e g)) : ℂ)`.

Establish `hKOlevi : ∀ g ∈ S, leviEmb k e g ∈ KO k (Fin m)`. Introduce `g hg`. Establish `h1 : leviEmb k e g = diagT k (Fin m) (fun j => Matrix.GeneralLinearGroup.det (g j))` using `by conv_lhs => rw [GlobalTheory.EigenSupport.eq_torusToLevi m g]`. Conclude with `GlobalTheory.SmGL.EmptyBlocks.leviEmb_torusToLevi k e _`. Rewrite using `[h1]`.

Conclude with `iwahori_le_KO k (Fin m) (diagT_mem_iwahori (t := fun j => Matrix.GeneralLinearGroup.det (g j)) hg)`. Establish `hδ : ∀ g ∈ S, deltaHalf k (fun _ : Fin m => Fin 1) g = 1`. Introduce `g hg`. Rewrite using `[deltaHalf_apply]`. Conclude with `Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ (hg a)`.

Establish `hθ : ∀ g ∈ S, jac e σ g (Submodule.Quotient.mk y) = θ g • (Submodule.Quotient.mk y : Jacquet σ (unipRad k e))`. Introduce `g hg`. Rewrite using `[jac_mk, hK _ (hKOlevi g hg), Submodule.Quotient.mk_smul, smul_smul]`. Take `⟨Y, _, _, τ, hτi, hτs, y₀, hy₀, hy₀θ⟩` from `GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen _ _ (jac e σ) S θ _ hy' hθ`. Establish `hrank : Module.rank ℂ Y ≤ ℵ₀`.

Take `⟨S', f, hf⟩` from `hτs`. Use `haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin m)`. Conclude with `(LinearMap.rank_le_of_surjective f.toLinearMap hf).trans ((Submodule.rank_le _).trans ((LinearMap.rank_le_of_surjective _ (Submodule.mkQ_surjective _)).trans (GlobalTheory.LocGL.rank_le_aleph0_of_isIrreducible hs hi)))`. Establish `hc : ∀ g : GL (Fin 1) k, ∃ c : ℂ, ∀ w, τ (Pi.mulSingle a0 g) w = c • w` using `fun g => GlobalTheory.LocGL.exists_eq_smul_of_rank_le hτi hrank ⟨τ (Pi.mulSingle a0 g), fun h => by`. Rewrite using `[← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, levi_comm]⟩`.

Use `choose c hc using hc`. Establish `hc1 : c 1 = 1` using `smul_left_injective ℂ hy₀ (by show c 1 • y₀ = (1 : ℂ) • y₀`. Rewrite using `[← hc, Pi.mulSingle_one, map_one, one_smul]`. Use the proof step `rfl)`. Establish `hcmul : ∀ g h, c (g * h) = c g * c h` using `fun g h => smul_left_injective ℂ hy₀ (by show c (g * h) • y₀ = (c g * c h) • y₀`.

Rewrite using `[← hc, Pi.mulSingle_mul, map_mul, Module.End.mul_apply, hc h, hc g, smul_smul])`. Set `ω' : GL (Fin 1) k →* ℂˣ` to `MonoidHom.toHomUnits ⟨⟨c, hc1⟩, hcmul⟩`. Set `ω : kˣ →* ℂˣ` to `ω'.comp (Matrix.GeneralLinearGroup.scalar (Fin 1))`. Establish `hω : ∀ u : kˣ, valuation k (u : k) = 1 → ω u = χ u`. Introduce `u hu`.

Set `g : Levi k (fun _ : Fin m => Fin 1)` to `Pi.mulSingle a0 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)`. Establish `hg : g ∈ S`. Introduce `a`. Distinguish the cases in `ha : a = a0`. Substitute `ha` using the available equality.

Simplify using `[g, det_scalar_fin_one, hu]`. Simplify using `[g, Pi.mulSingle_eq_of_ne ha]`. Establish `hdet : Matrix.GeneralLinearGroup.det (leviEmb k e g) = u`. Rewrite using `[det_leviEmb, Finset.prod_eq_single a0]`. Simplify using `[g, det_scalar_fin_one]`.

Introduce `b _ hb`. Simplify using `[g, Pi.mulSingle_eq_of_ne hb]`. Simplify using the standard rewrite rules. Establish `h1` using `(hc _ y₀).symm.trans (hy₀θ g hg)`. Simplify using `only [θ, hδ g hg, hdet, inv_one, Units.val_one, one_mul] at h1`.

Conclude with `Units.ext (smul_left_injective ℂ hy₀ h1)`. Take `⟨α, hα⟩` from `GlobalTheory.JacSuppCount.eq_mul_unrChar_of_eq_on_units k χ ω hω`. Use `⟨α, m, fun _ => 1, e, a0, rfl, Y, inferInstance, inferInstance, τ, hτi, hτs, fun g w => ?_⟩` and prove the remaining obligations. Rewrite using `[← hα]`. Use `show τ (Pi.mulSingle a0 g) w = c (Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g)) • w`.

Rewrite using `[scalar_det_fin_one, hc]`.
-/
theorem inSupport_of_KO_eigen (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ)
    (hi : σ.IsIrreducible) (hχ : IsSmoothChar χ) (hm : 0 < m) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) :
    ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  let e : (Σ _ : Fin m, Fin 1) ≃ Fin m := Equiv.sigmaUnique (Fin m) fun _ => Fin 1
  have hy' := mk_ne_zero hD σ χ y hs hi hχ hy hK (fun _ : Fin m => 1) e
  let a0 : Fin m := ⟨0, hm⟩
  let S : Set (Levi k (fun _ : Fin m => Fin 1)) :=
    {g | ∀ a, valuation k ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) = 1}
  let θ : Levi k (fun _ : Fin m => Fin 1) → ℂ := fun g =>
    (((deltaHalf k (fun _ : Fin m => Fin 1) g)⁻¹ : ℂˣ) : ℂ) *
      (χ (Matrix.GeneralLinearGroup.det (leviEmb k e g)) : ℂ)
  have hKOlevi : ∀ g ∈ S, leviEmb k e g ∈ KO k (Fin m) := by
    intro g hg
    have h1 : leviEmb k e g = diagT k (Fin m) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
      conv_lhs => rw [GlobalTheory.EigenSupport.eq_torusToLevi m g]
      exact GlobalTheory.SmGL.EmptyBlocks.leviEmb_torusToLevi k e _
    rw [h1]
    exact iwahori_le_KO k (Fin m) (diagT_mem_iwahori (t := fun j => Matrix.GeneralLinearGroup.det (g j)) hg)
  have hδ : ∀ g ∈ S, deltaHalf k (fun _ : Fin m => Fin 1) g = 1 := by
    intro g hg
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ (hg a)
  have hθ : ∀ g ∈ S, jac e σ g (Submodule.Quotient.mk y) = θ g • (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) := by
    intro g hg
    rw [jac_mk, hK _ (hKOlevi g hg), Submodule.Quotient.mk_smul, smul_smul]
  obtain ⟨Y, _, _, τ, hτi, hτs, y₀, hy₀, hy₀θ⟩ :=
    GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen _ _ (jac e σ) S θ _ hy' hθ
  have hrank : Module.rank ℂ Y ≤ ℵ₀ := by
    obtain ⟨S', f, hf⟩ := hτs
    haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin m)
    exact (LinearMap.rank_le_of_surjective f.toLinearMap hf).trans ((Submodule.rank_le _).trans
      ((LinearMap.rank_le_of_surjective _ (Submodule.mkQ_surjective _)).trans (GlobalTheory.LocGL.rank_le_aleph0_of_isIrreducible hs hi)))
  have hc : ∀ g : GL (Fin 1) k, ∃ c : ℂ, ∀ w, τ (Pi.mulSingle a0 g) w = c • w := fun g =>
    GlobalTheory.LocGL.exists_eq_smul_of_rank_le hτi hrank ⟨τ (Pi.mulSingle a0 g), fun h => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, levi_comm]⟩
  choose c hc using hc
  have hc1 : c 1 = 1 := smul_left_injective ℂ hy₀ (by
    show c 1 • y₀ = (1 : ℂ) • y₀
    rw [← hc, Pi.mulSingle_one, map_one, one_smul]; rfl)
  have hcmul : ∀ g h, c (g * h) = c g * c h := fun g h => smul_left_injective ℂ hy₀ (by
    show c (g * h) • y₀ = (c g * c h) • y₀
    rw [← hc, Pi.mulSingle_mul, map_mul, Module.End.mul_apply, hc h, hc g, smul_smul])
  let ω' : GL (Fin 1) k →* ℂˣ := MonoidHom.toHomUnits ⟨⟨c, hc1⟩, hcmul⟩
  let ω : kˣ →* ℂˣ := ω'.comp (Matrix.GeneralLinearGroup.scalar (Fin 1))
  have hω : ∀ u : kˣ, valuation k (u : k) = 1 → ω u = χ u := by
    intro u hu
    let g : Levi k (fun _ : Fin m => Fin 1) := Pi.mulSingle a0 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)
    have hg : g ∈ S := by
      intro a
      by_cases ha : a = a0
      · subst ha; simp [g, det_scalar_fin_one, hu]
      · simp [g, Pi.mulSingle_eq_of_ne ha]
    have hdet : Matrix.GeneralLinearGroup.det (leviEmb k e g) = u := by
      rw [det_leviEmb, Finset.prod_eq_single a0]
      · simp [g, det_scalar_fin_one]
      · intro b _ hb; simp [g, Pi.mulSingle_eq_of_ne hb]
      · simp
    have h1 := (hc _ y₀).symm.trans (hy₀θ g hg)
    simp only [θ, hδ g hg, hdet, inv_one, Units.val_one, one_mul] at h1
    exact Units.ext (smul_left_injective ℂ hy₀ h1)
  obtain ⟨α, hα⟩ := GlobalTheory.JacSuppCount.eq_mul_unrChar_of_eq_on_units k χ ω hω
  refine ⟨α, m, fun _ => 1, e, a0, rfl, Y, inferInstance, inferInstance, τ, hτi, hτs, fun g w => ?_⟩
  rw [← hα]
  show τ (Pi.mulSingle a0 g) w = c (Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g)) • w
  rw [scalar_det_fin_one, hc]

end GlobalTheory.SphSupport

/- English proof (translation)
Introduce `_ _ hD k _ _ _ _ m V _ _ σ χ y hs hi hχ hm hy hK`. Conclude with `GlobalTheory.SphSupport.inSupport_of_KO_eigen hD σ χ y hs hi hχ hm hy hK`.
-/
theorem GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  intro _ _ hD k _ _ _ _ m V _ _ σ χ y hs hi hχ hm hy hK
  exact GlobalTheory.SphSupport.inSupport_of_KO_eigen hD σ χ y hs hi hχ hm hy hK
