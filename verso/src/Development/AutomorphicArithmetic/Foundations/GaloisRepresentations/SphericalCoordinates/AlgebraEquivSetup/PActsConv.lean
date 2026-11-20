import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Simplify using `only [conv, hAct, one_mul, smul_eq_mul]`.
-/
private theorem conv_eq_hAct {X : Type} [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X) :
    conv K f f' g = hAct K f (fun x => f' (x⁻¹ * g)) 1 := by
  simp only [conv, hAct, one_mul, smul_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hΦ : T.IsTy (fun x => T.tf h' (x⁻¹ * g))`. Introduce `k hk x`. Establish `hk' : k⁻¹ ∈ T.K` using `T.K.inv_mem hk`. Simplify using `only [_root_.mul_inv_rev, mul_assoc]`.

Rewrite using `[((hA X M T h' hh').2 k⁻¹ hk' (x⁻¹ * g)).1, smul_eq_mul]`. Use `congr 1`. Establish `e : ∀ (p1 : T.L.pr k⁻¹ ∈ T.J) (p2 : T.L.pr k ∈ T.J), (⟨T.L.pr k⁻¹, p1⟩ : T.J) = (⟨T.L.pr k, p2⟩ : T.J)⁻¹` using `fun p1 p2 => Subtype.ext (map_inv _ _)`. Rewrite using `[e _ (T.fact.2 k hk)]`. Simplify using the standard rewrite rules.

Establish `key` using `congrFun (hψ.2.2 ℂ _ hΦ) 1`. Rewrite using `[Pi.smul_apply, conv_eq_hAct, conv_eq_hAct, key, Pi.smul_apply]`.
-/
private theorem conv_tf {X M : Type} [Group X] [Group M] (hA : TfAdm) (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h h' : X)
    (hψ : T.Acts ψ c h) (hh' : T.L.pr h' = 1) :
    conv T.K₀ ψ (T.tf h') = c • conv T.K₀ (T.tf h) (T.tf h') := by
  funext g
  have hΦ : T.IsTy (fun x => T.tf h' (x⁻¹ * g)) := by
    intro k hk x
    have hk' : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [_root_.mul_inv_rev, mul_assoc]
    rw [((hA X M T h' hh').2 k⁻¹ hk' (x⁻¹ * g)).1, smul_eq_mul]
    congr 1
    have e : ∀ (p1 : T.L.pr k⁻¹ ∈ T.J) (p2 : T.L.pr k ∈ T.J),
        (⟨T.L.pr k⁻¹, p1⟩ : T.J) = (⟨T.L.pr k, p2⟩ : T.J)⁻¹ := fun p1 p2 =>
      Subtype.ext (map_inv _ _)
    rw [e _ (T.fact.2 k hk)]
    simp
  have key := congrFun (hψ.2.2 ℂ _ hΦ) 1
  rw [Pi.smul_apply, conv_eq_hAct, conv_eq_hAct, key, Pi.smul_apply]

/- English proof (translation)
Introduce `hA hI X M _ _ T ψ c h hψ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[conv_tf hA T ψ c h 1 hψ (map_one _), (hI X M T h hψ.2.1).2.1]`. Introduce `c' h' hh'`. Establish `hlin : ∀ f : X → ℂ, conv T.K₀ ψ (c' • f) = c' • conv T.K₀ ψ f`.

Introduce `f`. Use function extensionality and compare the values at `g`. Rewrite using `[Pi.smul_apply]`. Unfold `conv`. Rewrite using `[smul_finsum]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hlin, conv_tf hA T ψ c h h' hψ hh', smul_smul, mul_comm c' c]`.
-/
theorem UpperTheory.Gal.W2.Seed.pActsConv :
    TfAdm → TfIdem → ActsConv := by
  intro hA hI X M _ _ T ψ c h hψ
  constructor
  · rw [conv_tf hA T ψ c h 1 hψ (map_one _), (hI X M T h hψ.2.1).2.1]
  · intro c' h' hh'
    have hlin : ∀ f : X → ℂ, conv T.K₀ ψ (c' • f) = c' • conv T.K₀ ψ f := by
      intro f
      funext g
      rw [Pi.smul_apply]
      unfold conv
      rw [smul_finsum]
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, conv_tf hA T ψ c h h' hψ hh', smul_smul, mul_comm c' c]
