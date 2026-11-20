import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

/- English proof (translation)
Take `⟨h1, h2⟩` from `(sumOp_transversal h A B hB).2.2 hle`. Rewrite using `[normOp, h1, h2 e he, map_one, inv_one, one_smul]`.
-/
theorem normOp_eq_self_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B)
    (hle : B ≤ A) {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

end Abstract

variable {nS nT : ℕ}

/- English proof (translation)
Establish `h : (mtF σ J g).map (finPartF F E) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hg)`. Apply `GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.zero_apply, sub_eq_zero]`. Use `(congrFun (congrFun h i) j).trans ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.map_one (finPartF F E) (finPartF F E).map_zero (finPartF F E).map_one]`. Both sides reduce to the same expression.
-/
theorem fin_smul_mtF_sub_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ J) : pairA F 0 1 • (mtF σ J g - 1) = 0 := by
  have h : (mtF σ J g).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  apply GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF
  ext i j
  rw [Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.zero_apply, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPartF F E) (finPartF F E).map_zero (finPartF F E).map_one]
  rfl

/- English proof (translation)
Establish `h1 : pairA F 1 0 • (x : WOF F E nS nT) = 0` using `GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF x.fin`. Establish `h2 : pairA F 0 1 = 1 - pairA F 1 0` using `Prod.ext (by show (0 : Ainf F) = 1 - 1; rw [sub_self]) (by show (1 : Af F) = 1 - 0; rw [sub_zero])`. Rewrite using `[h2, sub_smul, one_smul, h1, sub_zero]`.
-/
theorem fin_smul_XFF (x : XFF F E nS nT) : pairA F 0 1 • (x : WOF F E nS nT) = x := by
  have h1 : pairA F 1 0 • (x : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF x.fin
  have h2 : pairA F 0 1 = 1 - pairA F 1 0 := Prod.ext (by show (0 : Ainf F) = 1 - 1; rw [sub_self])
    (by show (1 : Af F) = 1 - 0; rw [sub_zero])
  rw [h2, sub_smul, one_smul, h1, sub_zero]

/- English proof (translation)
Apply `XFF.ext` to reduce the goal to its premises. Rewrite using `[coe_rhoFF]`. Establish `hL : mtF σ JT h * (x : WOF F E nS nT) = x`. Establish `: (mtF σ JT h - 1) * (x : WOF F E nS nT) = 0`. Rewrite using `[← fin_smul_XFF x, Matrix.mul_smul, ← Matrix.smul_mul, fin_smul_mtF_sub_one hh, Matrix.zero_mul]`.

Rewrite `this` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hR : (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x`. Establish `: (x : WOF F E nS nT) * (mtF σ JS g⁻¹ - 1) = 0`. Rewrite using `[← fin_smul_XFF x, Matrix.smul_mul, ← Matrix.mul_smul, fin_smul_mtF_sub_one (Subgroup.inv_mem _ hg), Matrix.mul_zero]`. Rewrite `this` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Then use the resulting hypothesis.

Use `show mtF σ JT h * (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x`. Rewrite using `[hL, hR]`.
-/
theorem rhoFF_real {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (x : XFF F E nS nT) : rhoFF σ JS JT (g, h) x = x := by
  apply XFF.ext
  rw [coe_rhoFF]
  have hL : mtF σ JT h * (x : WOF F E nS nT) = x := by
    have : (mtF σ JT h - 1) * (x : WOF F E nS nT) = 0 := by
      rw [← fin_smul_XFF x, Matrix.mul_smul, ← Matrix.smul_mul, fin_smul_mtF_sub_one hh, Matrix.zero_mul]
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hR : (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x := by
    have : (x : WOF F E nS nT) * (mtF σ JS g⁻¹ - 1) = 0 := by
      rw [← fin_smul_XFF x, Matrix.smul_mul, ← Matrix.mul_smul,
        fin_smul_mtF_sub_one (Subgroup.inv_mem _ hg), Matrix.mul_zero]
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  show mtF σ JT h * (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x
  rw [hL, hR]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh f`. Establish `hσ : ∀ z : E, σ (σ z) = z` using `fun z => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Establish `H` using `isHeis_opFF hσ hS hT hξ hc hR.hw`.

Establish `key : Om (g, h) = LinearMap.id`. Use `LinearMap.ext_on hR.span ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, e, he, rfl⟩`. Establish `hfix : Om (g, h) e = e`. Rewrite using `[hR.vac _ e he]`.

Conclude with `normOp_eq_self_of_le H lam (hR.sd' _) (by rintro _ ⟨a, ha, rfl⟩; rw [rhoFF_real hg hh]; exact ha) he`. Rewrite using `[hR.op, rhoFF_real hg hh, hfix, LinearMap.id_apply]`. Rewrite using `[key, LinearMap.id_apply]`.
-/
theorem IsLatRepF.real_triv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh f
  have hσ : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have key : Om (g, h) = LinearMap.id := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have hfix : Om (g, h) e = e := by
      rw [hR.vac _ e he]
      exact normOp_eq_self_of_le H lam (hR.sd' _)
        (by rintro _ ⟨a, ha, rfl⟩; rw [rhoFF_real hg hh]; exact ha) he
    rw [hR.op, rhoFF_real hg hh, hfix, LinearMap.id_apply]
  rw [key, LinearMap.id_apply]

end GlobalTheory.FinLatF

end
