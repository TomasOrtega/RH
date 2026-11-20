import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Introduce `l _ P K LL W hK a`. Establish `hle : K.1 ≤ K0 K` using `le_inf le_rfl hK`. Establish `hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)`. Introduce `x`. Conclude with `⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩`.

Set `e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1` to `AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩`. Use `⟨(W.emb a).comp e.symm.toAlgHom, ?_, ?_⟩` and prove the remaining obligations. Use `show ((W.emb a).comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a`. Use extensionality with `x`. Establish `: e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) x) = x` using `e.symm_apply_apply x`.

Simplify using `only [AlgHom.comp_apply]`. Conclude with `congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) this`. Introduce `τ hτ`. Establish `hτ' : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a` using `hτ`. Use extensionality with `x`.

Take `⟨y, rfl⟩` from `hsurj x`. Establish `h1 : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) y) = y` using `e.symm_apply_apply y`. Establish `h2` using `congrArg (fun f => f y) hτ'`. Simplify using `only [AlgHom.comp_apply] at h2 ⊢`. Rewrite using `[h2]`.

Conclude with `congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) h1.symm`.
-/
theorem existsUnique_over : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL),
    K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  intro l _ P K LL W hK a
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro x
    exact ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨(W.emb a).comp e.symm.toAlgHom, ?_, ?_⟩
  · show ((W.emb a).comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a
    ext x
    have : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) x) = x := e.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) this
  · intro τ hτ
    have hτ' : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a := hτ
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    have h1 : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) y) = y := e.symm_apply_apply y
    have h2 := congrArg (fun f => f y) hτ'
    simp only [AlgHom.comp_apply] at h2 ⊢
    rw [h2]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) h1.symm

end GlobalTheory.HTW.Rec
