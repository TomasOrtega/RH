import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformMemUnitaryLatticeStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertTwoFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `e : mat (g * h) = mat g * mat h` using `rfl`. Establish `e' : mat (g * h)⁻¹ = mat h⁻¹ * mat g⁻¹` using `by rw [mul_inv_rev]; rfl`. Use `⟨fun u hu => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1 : u • (mat g - 1) = 0` using `hg.1 u hu`. Establish `h2 : u • (mat h - 1) = 0` using `hh.1 u hu`.

Establish `: mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1)` using `by rw [e]; noncomm_ring`. Rewrite using `[this, smul_add, ← Matrix.smul_mul, h1, h2, Matrix.zero_mul, add_zero]`. Rewrite using `[e, e', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩`.
-/
theorem mul_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g h : UA σ W.J}
    (hg : g ∈ GlobalTheory.InertSph.KAt σ W v) (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : g * h ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e : mat (g * h) = mat g * mat h := rfl
  have e' : mat (g * h)⁻¹ = mat h⁻¹ * mat g⁻¹ := by rw [mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h1 : u • (mat g - 1) = 0 := hg.1 u hu
    have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [e]; noncomm_ring
    rw [this, smul_add, ← Matrix.smul_mul, h1, h2, Matrix.zero_mul, add_zero]
  · rw [e, e', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

/- English proof (translation)
Establish `e1 : mat h⁻¹ * mat h = 1` using `by show mat (h⁻¹ * h) = 1`. Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression. Use `⟨fun u hu => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h2 : u • (mat h - 1) = 0` using `hh.1 u hu`.

Establish `: mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1))` using `by rw [Matrix.mul_sub, e1]; noncomm_ring`. Rewrite using `[this, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]`. Rewrite using `[inv_inv]`. Conclude with `⟨(hh.2 z hz).2, (hh.2 z hz).1⟩`.
-/
theorem inv_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {h : UA σ W.J}
    (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : h⁻¹ ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e1 : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by rw [Matrix.mul_sub, e1]; noncomm_ring
    rw [this, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hh.2 z hz).2, (hh.2 z hz).1⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk`. Take `⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩` from `GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer F E σ B a a' G X om om' hT v w hin k hk`. Take `⟨h, hh, hhY⟩` from `GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ (a + a') G.W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm`. Establish `h2 : (2 : 𝓞 F) ∉ v.asIdeal` using `(hT.base.inert v w hin).1`. Establish `eH : mat h = (1 - Y) * Np` using `by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]`.

Establish `eH' : (1 + Y) * mat h = 1 - Y`. Rewrite using `[eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1, Matrix.mul_one]`. Establish `eI : mat h⁻¹ * mat h = 1` using `by show mat (h⁻¹ * h) = 1`. Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression.

Establish `intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v` using `fun z hz => by`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Conclude with `add_mem hz (hYint z hz)`. Use `⟨k * h, mul_mem_KAt hk hh, h⁻¹, inv_mem_KAt hh, ?_, ?_, by group⟩` and prove the remaining obligations. Establish `e : mat (k * h) = mat k * mat h` using `rfl`.

Establish `h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1`. Establish `: (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y)`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]`. Rewrite using `[e, ← Matrix.mul_assoc, this, hND1]`. Use `⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `intY1 _ (hNDi z hz)`. Establish `h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1`. Rewrite using `[Matrix.mul_smul]`. Establish `: (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))`.

Establish `c : (1 + Y) * mat h = mat h * (1 + Y)` using `eH'.trans hhY.symm`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, smul_smul, invOf_mul_self, one_smul]`. Use `⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E (a + a') G.W v h2 _ (intY1 _ (hh.2 z hz).1)`.
-/
theorem twoFac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  obtain ⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩ :=
    GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer F E σ B a a' G X om om' hT v w hin k hk
  obtain ⟨h, hh, hhY⟩ := GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ (a + a') G.W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  have eH : mat h = (1 - Y) * Np := by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]
  have eH' : (1 + Y) * mat h = 1 - Y := by
    rw [eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1,
      Matrix.mul_one]
  have eI : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  have intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]; exact add_mem hz (hYint z hz)
  refine ⟨k * h, mul_mem_KAt hk hh, h⁻¹, inv_mem_KAt hh, ?_, ?_, by group⟩
  · have e : mat (k * h) = mat k * mat h := rfl
    have h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1 := by
      have : (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]
      rw [e, ← Matrix.mul_assoc, this, hND1]
    refine ⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [← Matrix.mulVec_mulVec]; exact intY1 _ (hNDi z hz)
  · have h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1 := by
      rw [Matrix.mul_smul]
      have : (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
        have c : (1 + Y) * mat h = mat h * (1 + Y) := eH'.trans hhY.symm
        rw [Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]
        abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    refine ⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E (a + a') G.W v h2 _ (intY1 _ (hh.2 z hz).1)

end GlobalTheory.InertTwoFac
