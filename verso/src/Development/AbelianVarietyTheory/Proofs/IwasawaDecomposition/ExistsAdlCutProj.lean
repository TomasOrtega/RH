import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallOfSmallSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePlacesLgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtEqOfResidueFieldHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonemptyOffCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ProjTest

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z]

/- English proof (translation)
Establish `h : RegAt (below y) (algebraMap _ Z.functionField a)` using `⟨a, rfl⟩`. Rewrite using `[valAt, dif_pos h, IsFractionRing.injective _ _ h.choose_spec]`.
-/
theorem valAt_algebraMap (y : Sp K ⟶ Z) (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ _ h.choose_spec]

/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `hf.exists_fnOf`. Establish `h` using `CxPts.mem_ptsIn.2 hU`. Rewrite using `[ratVal_fnOf h, ← algebraMap_germ hU, valAt_algebraMap, CxPts.ev, valR, dif_pos (show ⊤ ≤ y.1 ⁻¹ᵁ U from h)]`. Establish `e` using `congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U hU)`. Use `Eq.trans ?_ e.symm` and prove the remaining obligations.

Simplify using `[Scheme.Hom.appLE]`. Both sides reduce to the same expression.
-/
theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    {f : Z.functionField} (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have h := CxPts.mem_ptsIn.2 hU
  rw [ratVal_fnOf h, ← algebraMap_germ hU, valAt_algebraMap, CxPts.ev, valR,
    dif_pos (show ⊤ ≤ y.1 ⁻¹ᵁ U from h)]
  have e := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U hU)
  refine Eq.trans ?_ e.symm
  simp [Scheme.Hom.appLE]
  rfl

end Val

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

omit [NumberField F] in

/- English proof (translation)
The claim follows from `(Δ.exists_isEqn x).choose_spec`.
-/
theorem isEqn_eqn (Δ : Y.Dv) (x : Y.X) : Δ.IsEqn x (eqn Δ x) := (Δ.exists_isEqn x).choose_spec

/- English proof (translation)
Take `⟨-, r, hr, h, -⟩` from `h`. Take `⟨i, hi⟩` from `exists_chart hr.isLB (under z)`. Establish `hf' : (((1 : ℕ+) : ℕ) • A.D).GeneratesAt (under z) f` using `by simpa using hf`. Establish `h₁` using `h σ z ⟨z.1 ≫ M.j, by`. Rewrite using `[Category.assoc, M.pb.w, ← Category.assoc, z.2, ← Spec.map_comp]`.

Use the proof step `rfl⟩ i f rfl hi hf'.regularAt`. Establish `h₂` using `C.pn_mPow Y σ A.D 1 (A.m σ) f z hf`. Simplify using `only [pow_one] at h₂`. Establish `h₃` using `ratVal_ne_zero ((hr.isEqn i _ hi).generatesAt_iff.1 hf')`. Conclude with `((mul_pos_iff_of_pos_left (Real.exp_pos _)).1 (lt_of_lt_of_eq (by positivity) h₁.symm)).trans_eq h₂`.
-/
theorem pn_pos {M : TrueGeo.Model Y} {L : HermLB M.p} (h : A.Induced M L 1 0) (σ : F →+* ℂ) (z : Pts Y σ)
    (f : Y.Fn) (hf : A.D.GeneratesAt (under z) f) : 0 < C.pn Y σ A.D (A.m σ) (C.cx Y σ f) z := by
  obtain ⟨-, r, hr, h, -⟩ := h
  obtain ⟨i, hi⟩ := exists_chart hr.isLB (under z)
  have hf' : (((1 : ℕ+) : ℕ) • A.D).GeneratesAt (under z) f := by simpa using hf
  have h₁ := h σ z ⟨z.1 ≫ M.j, by
    rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, ← Spec.map_comp]; rfl⟩ i f rfl hi hf'.regularAt
  have h₂ := C.pn_mPow Y σ A.D 1 (A.m σ) f z hf
  simp only [pow_one] at h₂
  have h₃ := ratVal_ne_zero ((hr.isEqn i _ hi).generatesAt_iff.1 hf')
  exact ((mul_pos_iff_of_pos_left (Real.exp_pos _)).1 (lt_of_lt_of_eq (by positivity) h₁.symm)).trans_eq h₂

variable (F) (n : ℕ)

def pick (i : Fin n) (l : Fin (n + 1)) : 𝓞 F := if l = i.succ then 1 else 0

end GlobalTheory.TrueGeo.ProjTest

namespace GlobalTheory.TrueGeo

end GlobalTheory.TrueGeo
