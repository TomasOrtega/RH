import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

/- English proof (translation)
Establish `hw : (z⁻¹ * z') ^ n = 1` using `by rw [mul_pow, inv_pow, hz, hz', inv_mul_cancel]`. Establish `e : z' = z * (z⁻¹ * z')` using `(mul_inv_cancel_left z z').symm`. Rewrite using `[e, hs.2 D' φ z _ hz hw, hs'.2 D' φ z _ hz hw]`. Normalize the expressions using the abelian group laws.
-/
theorem isSec_sub_root_eq {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z z' : Pt A D') (hz : z ^ n = spOver φ ≫ x) (hz' : z' ^ n = spOver φ ≫ x) :
    s D' φ z' - s' D' φ z' = s D' φ z - s' D' φ z := by
  have hw : (z⁻¹ * z') ^ n = 1 := by rw [mul_pow, inv_pow, hz, hz', inv_mul_cancel]
  have e : z' = z * (z⁻¹ * z') := (mul_inv_cancel_left z z').symm
  rw [e, hs.2 D' φ z _ hz hw, hs'.2 D' φ z _ hz hw]
  abel

/- English proof (translation)
Rewrite using `[hs.1 D' D'' φ ψ z hz, hs'.1 D' D'' φ ψ z hz, map_sub]`.
-/
theorem isSec_sub_natural {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) :
    s D'' (ψ.comp φ) (spOver ψ ≫ z) - s' D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z - s' D' φ z) := by
  rw [hs.1 D' D'' φ ψ z hz, hs'.1 D' D'' φ ψ z hz, map_sub]

/- English proof (translation)
Rewrite using `[← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]`.
-/
theorem root_spOver {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) : (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

/- English proof (translation)
Introduce `R _ A _ _ n hR b D _ _ x s s' hs hs'`. Take `⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩` from `hR D x`. Establish `hdesc` using `GlobalTheory.ff_descent_pairs R D D₁ ψ hψ (s D₁ ψ z₀ - s' D₁ ψ z₀) (fun E _ _ α β hαβ ↦ by`. Rewrite using `[← isSec_sub_natural hs hs' ψ α z₀ hz₀, ← isSec_sub_natural hs hs' ψ β z₀ hz₀]`. Establish `h1` using `root_spOver ψ α z₀ hz₀`.

Establish `h2` using `root_spOver ψ β z₀ hz₀`. Rewrite `h1`, the goal using `[hαβ]`. Conclude with `isSec_sub_root_eq hs hs' _ _ _ h2 h1)`. Take `⟨e, he, heu⟩` from `hdesc`. Establish `key : ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e`.

Introduce `D' _ _ φ z hz`. Take `⟨E', _, _, ψ', φ', hψ', hsq⟩` from `GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ`. Establish `hinj : Function.Injective ψ'`. Use `letI : Algebra D' E' := (ψ' : D' →+* E').toAlgebra`. Use `haveI : Module.FaithfullyFlat D' E' := hψ'`.

Conclude with `FaithfulSMul.algebraMap_injective D' E'`. Apply `hinj` to reduce the goal to its premises. Establish `h1` using `root_spOver φ ψ' z hz`. Establish `h2` using `root_spOver ψ φ' z₀ hz₀`. Rewrite using `[← isSec_sub_natural hs hs' φ ψ' z hz]`.

Rewrite `h1`, the goal using `[hsq]`. Rewrite using `[isSec_sub_root_eq hs hs' _ _ _ h2 h1, isSec_sub_natural hs hs' ψ φ' z₀ hz₀, ← he]`. Conclude with `(congrArg (fun f : D →ₐ[R] E' ↦ f e) hsq).symm`. Conclude with `⟨e, key, fun e' he' ↦ heu e' ((he' D₁ ψ z₀ hz₀).symm)⟩`.
-/
theorem isSec_sub_existsUnique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ (b : Fn0 A) (D : Type) [CommRing D] [Algebra R D] (x : Pt A D) (s s' : RootFn A D),
    IsSec n b x s → IsSec n b x s' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e := by
  intro R _ A _ _ n hR b D _ _ x s s' hs hs'
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  have hdesc := GlobalTheory.ff_descent_pairs R D D₁ ψ hψ (s D₁ ψ z₀ - s' D₁ ψ z₀) (fun E _ _ α β hαβ ↦ by
    rw [← isSec_sub_natural hs hs' ψ α z₀ hz₀, ← isSec_sub_natural hs hs' ψ β z₀ hz₀]
    have h1 := root_spOver ψ α z₀ hz₀
    have h2 := root_spOver ψ β z₀ hz₀
    rw [hαβ] at h1 ⊢
    exact isSec_sub_root_eq hs hs' _ _ _ h2 h1)
  obtain ⟨e, he, heu⟩ := hdesc
  have key : ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x →
      s D' φ z - s' D' φ z = φ e := by
    intro D' _ _ φ z hz
    obtain ⟨E', _, _, ψ', φ', hψ', hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
    have hinj : Function.Injective ψ' := by
      letI : Algebra D' E' := (ψ' : D' →+* E').toAlgebra
      haveI : Module.FaithfullyFlat D' E' := hψ'
      exact FaithfulSMul.algebraMap_injective D' E'
    apply hinj
    have h1 := root_spOver φ ψ' z hz
    have h2 := root_spOver ψ φ' z₀ hz₀
    rw [← isSec_sub_natural hs hs' φ ψ' z hz]
    rw [hsq] at h1 ⊢
    rw [isSec_sub_root_eq hs hs' _ _ _ h2 h1, isSec_sub_natural hs hs' ψ φ' z₀ hz₀, ← he]
    exact (congrArg (fun f : D →ₐ[R] E' ↦ f e) hsq).symm
  exact ⟨e, key, fun e' he' ↦ heu e' ((he' D₁ ψ z₀ hz₀).symm)⟩

end GlobalTheory.PtExt
