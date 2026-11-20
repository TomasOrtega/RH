import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPreservingOperatorLocalStructureStatement

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ArchComm
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finOne : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
The claim follows from `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0 from map_zero _`.
-/
theorem evI_finOne : evI F (finOne (F := F)) = 0 :=
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0 from map_zero _

/- English proof (translation)
Use `show evalV F v (sndA F finOne) = 1`. Establish `: sndA F (finOne (F` using `F)) = 1 := rfl`. Rewrite using `[this, map_one]`.
-/
theorem evFin_finOne (v : Pl F) : evFin F v finOne = 1 := by
  show evalV F v (sndA F finOne) = 1
  have : sndA F (finOne (F := F)) = 1 := rfl
  rw [this, map_one]

/- English proof (translation)
Rewrite using `[map_sub, map_one, evFin_finOne, sub_self]`.
-/
theorem evFin_one_sub_finOne (v : Pl F) : evFin F v (1 - finOne) = 0 := by
  rw [map_sub, map_one, evFin_finOne, sub_self]

section Mat
variable {m n k : ℕ}

/- English proof (translation)
Establish `h1 : w = (finOne (F` using `F)) • w := by`. Use `hw (1 - finOne (F := F)) (evFin_one_sub_finOne v)` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h2 : (finOne (F` using `F)) • z = 0 := hz finOne evI_finOne`. Rewrite using `[h1, Matrix.mul_smul, ← Matrix.smul_mul, h2, Matrix.zero_mul]`.
-/
theorem mul_eq_zero_of_at {z : Matrix (Fin m) (Fin n) (AE F E)} (hz : At (evI F) z) {v : Pl F}
    {w : Matrix (Fin n) (Fin k) (AE F E)} (hw : At (evFin F v) w) : z * w = 0 := by
  have h1 : w = (finOne (F := F)) • w := by
    have := hw (1 - finOne (F := F)) (evFin_one_sub_finOne v)
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have h2 : (finOne (F := F)) • z = 0 := hz finOne evI_finOne
  rw [h1, Matrix.mul_smul, ← Matrix.smul_mul, h2, Matrix.zero_mul]

/- English proof (translation)
Establish `h1 : w = (finOne (F` using `F)) • w := by`. Use `hw (1 - finOne (F := F)) (evFin_one_sub_finOne v)` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h2 : (finOne (F` using `F)) • z = 0 := hz finOne evI_finOne`. Rewrite using `[h1, Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, h2, Matrix.transpose_zero, Matrix.mul_zero]`.
-/
theorem mul_transpose_eq_zero_of_at {z : Matrix (Fin k) (Fin n) (AE F E)} (hz : At (evI F) z) {v : Pl F}
    {w : Matrix (Fin m) (Fin n) (AE F E)} (hw : At (evFin F v) w) : w * zᵀ = 0 := by
  have h1 : w = (finOne (F := F)) • w := by
    have := hw (1 - finOne (F := F)) (evFin_one_sub_finOne v)
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have h2 : (finOne (F := F)) • z = 0 := hz finOne evI_finOne
  rw [h1, Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, h2, Matrix.transpose_zero, Matrix.mul_zero]

end Mat

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Use `show mat g * w * (mat h)ᵀ = w`. Establish `e1 : mat g * w = w`. Use `mul_eq_zero_of_at (k := d) hg hw` as an intermediate fact. Rewrite `this` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `e2 : w * (mat h)ᵀ = w`.

Use `mul_transpose_eq_zero_of_at (m := n) hh hw` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[e1, e2]`.
-/
theorem actAB_eq_of_at {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) {v : Pl F}
    {w : Matrix (Fin n) (Fin d) (AE F E)} (hw : At (evFin F v) w) : actAB (cA σ) (g, h) w = w := by
  show mat g * w * (mat h)ᵀ = w
  have e1 : mat g * w = w := by
    have := mul_eq_zero_of_at (k := d) hg hw
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have e2 : w * (mat h)ᵀ = w := by
    have := mul_transpose_eq_zero_of_at (m := n) hh hw
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  rw [e1, e2]

/- English proof (translation)
Rewrite using `[(IsUWeilPair.isUSplitting hW).impl (g, h) w Φ hΦ, actAB_eq_of_at hg hh hw]`.
-/
theorem weil_rho_comm {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W}
    (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)) (hw : At (evFin F v) w) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om (g, h) (M.co.rho ψ w Φ) = M.co.rho ψ w (om (g, h) Φ) := by
  rw [(IsUWeilPair.isUSplitting hW).impl (g, h) w Φ hΦ, actAB_eq_of_at hg hh hw]

end GlobalTheory.ArchComm

namespace GlobalTheory.ThK

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' hT g' hg' h hh Φ' hΦ'`. Establish `hS` using `IsUWeilPair.isUSplitting hT.weil'`. Unfold `Model.So at hΦ' ⊢`. Use `(Submodule.span_le (p := (Submodule.span ℂ _).comap (om' (g', h)))).2 ?_ hΦ'` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, hφ, hcof, h1, rfl⟩`.

Take `⟨f₁, hf₁⟩` from `GlobalTheory.T.schwartz_preserving_operator_local_structure hK.base F E σ B a' (a + a') G.V' G.W G.M' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' (om' (g', h)) (fun Φ hΦ => hS.pres (g', h) Φ hΦ) (fun v w hw Φ hΦ => GlobalTheory.ArchComm.weil_rho_comm hT.weil' hg' hh v w hw Φ …`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, hf₁]`. Conclude with `Submodule.subset_span ⟨f₁, φ, hφ, hcof, h1, rfl⟩`.
-/
theorem so_stable_arch : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F), ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
      om' (g', h) Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT g' hg' h hh Φ' hΦ'
  have hS := IsUWeilPair.isUSplitting hT.weil'
  unfold Model.So at hΦ' ⊢
  refine (Submodule.span_le (p := (Submodule.span ℂ _).comap (om' (g', h)))).2 ?_ hΦ'
  rintro _ ⟨f, φ, hφ, hcof, h1, rfl⟩
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.schwartz_preserving_operator_local_structure hK.base F E σ B a' (a + a') G.V' G.W G.M' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM'
    (om' (g', h)) (fun Φ hΦ => hS.pres (g', h) Φ hΦ)
    (fun v w hw Φ hΦ => GlobalTheory.ArchComm.weil_rho_comm hT.weil' hg' hh v w hw Φ hΦ) f φ hφ hcof
  rw [SetLike.mem_coe, Submodule.mem_comap, hf₁]
  exact Submodule.subset_span ⟨f₁, φ, hφ, hcof, h1, rfl⟩

end GlobalTheory.ThK
