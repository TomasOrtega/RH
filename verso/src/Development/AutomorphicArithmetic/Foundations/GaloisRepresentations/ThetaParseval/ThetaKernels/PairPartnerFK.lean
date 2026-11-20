import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtension
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.WeilPairPartnerF
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b`. Establish `hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)), X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)` using `fun X => Matrix.ext fun i j => rfl`. Establish `ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA` using `a.2`. Use `set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef`. Establish `hJA : incM F JA = (incM F JT)ᵀ`.

Rewrite using `[hA]`. Both sides reduce to the same expression. Rewrite `ha` using `[hJA]`. Establish `ha'` using `congrArg Matrix.transpose ha`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'`.

Establish `hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT` using `by show Formalism.UG.cT _ a.1.val * _ * a.1.val = _`. Simplify using `only [Formalism.UG.cT, hmap]`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `ha'`. Take `⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f` from `⟨_, rfl⟩`.

Establish `hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB`. Rewrite using `[← hcR, hmap]`. Conclude with `b.2`. Establish `hBB : b.1.val * (b⁻¹).1.val = 1`. Rewrite using `[Subgroup.coe_inv]`.

Conclude with `(b.1).mul_inv`. Establish `hBB' : (b⁻¹).1.val * b.1.val = 1`. Rewrite using `[Subgroup.coe_inv]`. Conclude with `(b.1).inv_mul`. Take `⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M` from `⟨_, rfl⟩`.

Take `⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M` from `⟨_, rfl⟩`. Rewrite `hb`, `hBB`, `hBB'` using `[hBdef]`. Rewrite `hBB`, `hBB'` using `[hBidef]`. Establish `hdet : JS.det ≠ 0` using `hS.2`. Establish `hGN` using `GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet`.

Establish `hNG` using `GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet`. Establish `hsm : incM F (ξ₀ • JS⁻¹) = inclR (F` using `F) (AF F) ξ₀ • incM F JS⁻¹ := GlobalTheory.WeilPairPartner.map_smul_eq _ _ _`. Establish `hu : IsUnit (inclR (F` using `F) (E := E) (AF F) ξ₀) := (isUnit_iff_ne_zero.mpr hξ₀).map _`. Establish `hcore` using `GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS) (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG`. Establish `hTT : Biᵀ * Bmᵀ = 1`.

Rewrite using `[← Matrix.transpose_mul, hBB, Matrix.transpose_one]`. Set `gU : GL (Fin nS) (AF F ⊗[F] E)` to `⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩`. Establish `hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS` using `by show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS`. Rewrite using `[hcR]`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]`.

Conclude with `hcore`. Use `⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩` and prove the remaining obligations. Use `show Biᵀ = ((b⁻¹).1.val)ᵀ`. Rewrite using `[hBidef]`.
-/
theorem pair_partnerF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    fun X => Matrix.ext fun i j => rfl
  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'
  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]
end GlobalTheory.WeilPairPartnerF
end
