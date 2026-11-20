import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.TameType

/- English proof (translation)
Set `f : Subrepresentation (twist ρ ν) → Subrepresentation ρ` to `fun S => ⟨S.toSubmodule, fun g v hv => by`. Establish `h1` using `S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)`. Simplify `h1⟩` using `[smul_smul]`. Establish `hn : (⊥ : Submodule ℂ V) ≠ ⊤` using `fun e => (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)`. Establish `: Nontrivial (Subrepresentation (twist ρ ν))` using `⟨⊥, ⊤, fun e => hn (congrArg Subrepresentation.toSubmodule e)⟩`.

Use `⟨fun S => ?_⟩` and prove the remaining obligations. Break down `eq_bot_or_eq_top (f S) with e | e` into its components or cases. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))`. Conclude with `Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))`.
-/
theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (h : ρ.IsIrreducible) (ν : Γ →* ℂˣ) : (twist ρ ν).IsIrreducible := by
  let f : Subrepresentation (twist ρ ν) → Subrepresentation ρ := fun S =>
    ⟨S.toSubmodule, fun g v hv => by
      have h1 := S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)
      simpa [smul_smul] using h1⟩
  have hn : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
    (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
  have : Nontrivial (Subrepresentation (twist ρ ν)) := ⟨⊥, ⊤, fun e =>
    hn (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with e | e
  · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))

/- English proof (translation)
Rewrite using `[← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem charpoly_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (z : ℂ) :
    (z • (1 : Module.End ℂ V)).charpoly = (X - C z) ^ Module.finrank ℂ V := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

section WD

open GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

/- English proof (translation)
Proceed by induction on `a using WD.ind`. Conclude with `(WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1`.
-/
theorem weilDeligneParameter_monodromy_zero_of_unramified {a : WD h} (ha : a.unr) : a.mono0 := by
  induction a using WD.ind
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1

/- English proof (translation)
Proceed by induction on `a using WD.ind`. Rewrite using `[WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]`.
-/
theorem inePol_of_unr {a : WD h} (ha : a.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) :
    a.inePol σ = (X - 1) ^ a.lpDim := by
  induction a using WD.ind
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]

/- English proof (translation)
Rewrite using `[← WD.lpDim_char a c hc]`. Proceed by induction on `a using WD.ind with`. Consider the case `hP m a`. Proceed by induction on `c using WD.ind with`. Consider the case `hP n c`.

Rewrite `hz` using `[WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk]`. Establish `h1` using `LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))`. Rewrite `h1` using `[hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ, ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]`.
-/
theorem inePol_char_of_unr {a c : WD h} (ha : a.unr) (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (X - C z) ^ a.lpDim := by
  rw [← WD.lpDim_char a c hc]
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ,
      ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]

end WD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `R H what₂ N A T S i w hw hTS hL hT hmu P`. Take `⟨htame, hram, hv⟩` from `hT`. Take `⟨v, hv0, hv⟩` from `hv P`. Establish `L` using `hL i w hw`. Establish `hs` using `(S i w hw).mu_ok.1`.

Take `⟨π₁, π₂, h1, h2, he⟩` from `hTS w _ _ _ _ v hs htame hram hv0 hv`. Set `c : Irr (w.adicCompletion H.E) 1` to `{ V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar, irr := isIrreducible_ofChar _ }`. Set `τ : Irr (w.adicCompletion H.E) R.t` to `{ V := π₂.V, π := twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar, irr := irreducible_twist π₂.irr _ }`. Establish `hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu))` using `⟨Representation.Equiv.refl _⟩`. Establish `e1` using `L.prod _ _ π₁ τ _ he`.

Establish `e2` using `L.twist _ _ c π₂ τ hc ⟨Representation.Equiv.refl _⟩`. Establish `u1` using `(L.sph _ π₁).2 h1`. Establish `u2` using `(L.sph _ π₂).2 h2`. Establish `eV` using `(S i w hw).locV P`. Establish `eM` using `(S i w hw).locMu c hc`.

Rewrite `eV` using `[e1, e2]`. Use `⟨?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]`. Conclude with `⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩`. Establish `hz` using `hmu σ hσ`.

Rewrite `hz` using `[T.inePol _ _ _ hσ, eM]`. Rewrite using `[T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ, inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]`.
-/
theorem inertialType_of_tame : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), TameSplitAll H.E → Laws S → TypeTame S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := L.twist _ _ c π₂ τ hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]

end GlobalTheory.TameType
