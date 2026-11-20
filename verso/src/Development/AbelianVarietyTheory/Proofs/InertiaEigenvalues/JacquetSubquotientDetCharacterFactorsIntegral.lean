import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

open GlobalTheory.SmGL.DepthZero ValuativeRel Matrix

/- English proof (translation)
Introduce `F _ _ _ _ n β _ _ _ _ c f V _ _ σ ψ s ⟨E⟩ hsub j g hg v`. Establish `hσ : ∀ (h : GL n F) (x : V), σ h x = (ψ (GeneralLinearGroup.det h) : ℂ) • x`. Introduce `h x`. Apply `E.toLinearEquiv.injective` to reduce the goal to its premises. Establish `h1` using `E.toIntertwiningMap.isIntertwining σ (detRep n ψ) h x`.

Establish `h2 : E.toLinearEquiv (σ h x) = E.toIntertwiningMap (σ h x)` using `rfl`. Establish `h3 : E.toLinearEquiv x = E.toIntertwiningMap x` using `rfl`. Rewrite using `[h2, h1, map_smul, h3]`. Simplify using `[detRep]`. Establish `hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {h : GL d F}, h ∈ KO F d → valuation F (GeneralLinearGroup.det h : F) = 1`.

Introduce `d _ _ h hh`. Take `⟨h, rfl⟩` from `hh`. Establish `h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[F] F) h) : Fˣ) : F) = algebraMap 𝒪[F] F (GeneralLinearGroup.det h : 𝒪[F]ˣ)` using `((algebraMap 𝒪[F] F).map_det _).symm`. Rewrite using `[h1]`. Conclude with `(Valuation.integer.integers (valuation F)).one_of_isUnit (Units.isUnit _)`.

Use `set l : Levi F (fun j => Fin (c j)) := Pi.mulSingle j g with hl`. Establish `hlK : ∀ b, l b ∈ KO F (Fin (c b))`. Introduce `b`. Distinguish the cases in `hb : b = j`. Substitute `hb` using the available equality.

Simplify using `[l, hg]`. Simplify using `[l, Pi.mulSingle_eq_of_ne hb, one_mem]`. Establish `hdet : GeneralLinearGroup.det (leviEmb F f l) = GeneralLinearGroup.det g`. Rewrite using `[det_leviEmb, Finset.prod_eq_single j]`. Simplify using `[l]`.

Introduce `b _ hb`. Simplify using `[l, Pi.mulSingle_eq_of_ne hb]`. Simplify using the standard rewrite rules. Establish `hδ : deltaHalf F (fun j => Fin (c j)) l = 1`. Rewrite using `[deltaHalf_apply]`.

Conclude with `Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ (hval (hlK b))`. Establish `hjac : ∀ x, jac f σ l x = (ψ (GeneralLinearGroup.det g) : ℂ) • x`. Introduce `x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[jac_mk, hδ, inv_one, Units.val_one, one_smul, hσ, hdet, Submodule.Quotient.mk_smul]`.

Establish `hT` using `Model.scalar_of_isSubquotient hsub hjac`. Establish `hnt : ∀ b, Nontrivial (s b).V` using `fun b => Model.nontrivial_of_isIrreducible (s b).irr`. Establish `hφ : ∀ b, ∃ x : (s b).V, ∃ φ : (s b).V →ₗ[ℂ] ℂ, φ x ≠ 0`. Introduce `b`. Take `⟨x, hx⟩` from `exists_ne (0 : (s b).V)`.

Take `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (s b).V, φ x ≠ 0` from `by by_contra! h`. Conclude with `hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 h)`. Conclude with `⟨x, φ, hφ⟩`. Use `choose x φ hxφ using hφ`. Set `y : ∀ b, (s b).V` to `Function.update x j v`.

Establish `hc : (∏ b ∈ Finset.univ.erase j, φ b (y b)) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun b hb => ?_` and prove the remaining obligations. Rewrite using `[show y b = x b from Function.update_of_ne (Finset.ne_of_mem_erase hb) _ _]`. Conclude with `hxφ b`. Establish `hyj : y j = v` using `Function.update_self _ _ _`.

Establish `key` using `contract_piTensor (fun b => (s b).ρ) φ j g (PiTensorProduct.tprod ℂ y)`. Rewrite `key` using `[hT, map_smul, contract_tprod, hyj, map_smul]`. Rewrite `key` using `[smul_comm]`. Conclude with `(smul_right_injective _ hc key).symm`.
-/
theorem factor_eq_det_of_isSubquotient_jac : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  intro F _ _ _ _ n β _ _ _ _ c f V _ _ σ ψ s ⟨E⟩ hsub j g hg v
  classical

  have hσ : ∀ (h : GL n F) (x : V), σ h x = (ψ (GeneralLinearGroup.det h) : ℂ) • x := by
    intro h x
    apply E.toLinearEquiv.injective
    have h1 := E.toIntertwiningMap.isIntertwining σ (detRep n ψ) h x
    have h2 : E.toLinearEquiv (σ h x) = E.toIntertwiningMap (σ h x) := rfl
    have h3 : E.toLinearEquiv x = E.toIntertwiningMap x := rfl
    rw [h2, h1, map_smul, h3]
    simp [detRep]

  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {h : GL d F}, h ∈ KO F d →
      valuation F (GeneralLinearGroup.det h : F) = 1 := by
    intro d _ _ h hh
    obtain ⟨h, rfl⟩ := hh
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[F] F) h) : Fˣ) : F) =
        algebraMap 𝒪[F] F (GeneralLinearGroup.det h : 𝒪[F]ˣ) :=
      ((algebraMap 𝒪[F] F).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation F)).one_of_isUnit (Units.isUnit _)
  set l : Levi F (fun j => Fin (c j)) := Pi.mulSingle j g with hl
  have hlK : ∀ b, l b ∈ KO F (Fin (c b)) := by
    intro b
    by_cases hb : b = j
    · subst hb; simp [l, hg]
    · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
  have hdet : GeneralLinearGroup.det (leviEmb F f l) = GeneralLinearGroup.det g := by
    rw [det_leviEmb, Finset.prod_eq_single j]
    · simp [l]
    · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
    · simp
  have hδ : deltaHalf F (fun j => Fin (c j)) l = 1 := by
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ (hval (hlK b))

  have hjac : ∀ x, jac f σ l x = (ψ (GeneralLinearGroup.det g) : ℂ) • x := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [jac_mk, hδ, inv_one, Units.val_one, one_smul, hσ, hdet, Submodule.Quotient.mk_smul]

  have hT := Model.scalar_of_isSubquotient hsub hjac

  have hnt : ∀ b, Nontrivial (s b).V := fun b => Model.nontrivial_of_isIrreducible (s b).irr
  have hφ : ∀ b, ∃ x : (s b).V, ∃ φ : (s b).V →ₗ[ℂ] ℂ, φ x ≠ 0 := by
    intro b
    obtain ⟨x, hx⟩ := exists_ne (0 : (s b).V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (s b).V, φ x ≠ 0 := by
      by_contra! h
      exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 h)
    exact ⟨x, φ, hφ⟩
  choose x φ hxφ using hφ
  let y : ∀ b, (s b).V := Function.update x j v
  have hc : (∏ b ∈ Finset.univ.erase j, φ b (y b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun b hb => ?_
    rw [show y b = x b from Function.update_of_ne (Finset.ne_of_mem_erase hb) _ _]
    exact hxφ b
  have hyj : y j = v := Function.update_self _ _ _
  have key := contract_piTensor (fun b => (s b).ρ) φ j g (PiTensorProduct.tprod ℂ y)
  rw [hT, map_smul, contract_tprod, hyj, map_smul] at key
  rw [smul_comm] at key
  exact (smul_right_injective _ hc key).symm

end GlobalTheory.LevelType
