import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacterStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ n χ V _ _ π hπ hχ v hv he`. Take `⟨h1, h2⟩` from `GlobalTheory.T.principalSeriesType_constant_family_det_character k n χ`. Establish `hs : IsSmoothChar (detChar (Fin n) χ)⁻¹`. Establish `hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ)` using `Matrix.GeneralLinearGroup.continuous_det`. Establish `ho : IsOpen ((χ.ker : Set kˣ))` using `hχ`.

Use `ho.preimage hc` as an intermediate fact. Unfold `IsSmoothChar`. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `[detChar, MonoidHom.mem_ker]`.

Establish `hk : twKer (twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1`. Unfold `twKer`. Use `congr 1`. Use extensionality with `w`. Use `exists_congr fun u => exists_congr fun x => ?_` and prove the remaining obligations.

Establish `hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1` using `det_eq_one_of_mem_unipRad k u.2`. Establish `: twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x`. Simplify using `[twist, detChar, hd]`. Rewrite using `[this]`. Use `GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel k n V (twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_` and prove the remaining obligations.

Introduce `g hg`. Establish `h3` using `he g (by rw [h1]; exact hg)`. Rewrite `h3` using `[h2 g hg]`. Use `show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v`. Rewrite using `[h3, smul_smul]`.

Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_isEig_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  intro k _ _ _ _ n χ V _ _ π hπ hχ v hv he
  obtain ⟨h1, h2⟩ := GlobalTheory.T.principalSeriesType_constant_family_det_character k n χ
  have hs : IsSmoothChar (detChar (Fin n) χ)⁻¹ := by
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ) :=
      Matrix.GeneralLinearGroup.continuous_det
    have ho : IsOpen ((χ.ker : Set kˣ)) := hχ
    have := ho.preimage hc
    unfold IsSmoothChar
    convert this using 1
    ext g
    simp [detChar, MonoidHom.mem_ker]
  have hk : twKer (twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1 := by
    unfold twKer
    congr 1
    ext w
    refine exists_congr fun u => exists_congr fun x => ?_
    have hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have : twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x := by
      simp [twist, detChar, hd]
    rw [this]
  refine GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel k n V (twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_
  intro g hg
  have h3 := he g (by rw [h1]; exact hg)
  rw [h2 g hg] at h3
  show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v
  rw [h3, smul_smul]
  simp

end GlobalTheory.PsType
