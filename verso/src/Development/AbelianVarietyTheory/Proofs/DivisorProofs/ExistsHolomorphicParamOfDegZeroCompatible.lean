import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZeroStatement

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

/- English proof (translation)
Set `a : ∀ k, Hol (K.W k)` to `fun k ↦ G (K.triv k)`. Establish `h1 : ∀ k k' (e : K.le 0 k' k), sh e (a k) = a k'` using `fun k k' e ↦ (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm`. Establish `h2 : ∀ k i, dw i (a k) = 0` using `fun k i ↦ by`. Establish `e0 : G (K.jet k) = TrivSqZeroExt.inl (sh (K.le_refl k) (a k))` using `hG _ _ (jet0 k) rfl`. Establish `e1 : G (K.jet k) = tszeSec dw (a k)` using `hG _ _ (jet1 k) rfl`.

Establish `e2` using `congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)`. Conclude with `(snd_tszeSec dw (a k) i).symm.trans e2`. Take `⟨p, hp⟩` from `GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2`. Use `⟨p, fun T ↦ ?_⟩` and prove the remaining obligations. Establish `e : G T = T.ρ (sh (K.le_refl T.k) (a T.k))` using `hG _ _ (ptHom T (K.le_refl T.k)) rfl`.

Rewrite using `[e, sh_refl, hp, T.ρ_cst]`.
-/
theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (sh (K.le_refl k) (a k)) := hG _ _ (jet0 k) rfl
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ (jet1 k) rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
