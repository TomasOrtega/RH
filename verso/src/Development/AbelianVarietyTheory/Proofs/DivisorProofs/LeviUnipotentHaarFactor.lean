import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureProductGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalHomeomorphHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingLinearEquivUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulusAdapted

section

open GlobalTheory.LeviModulus GlobalTheory.UnipMass GlobalTheory.LeviModulus.HCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `GlobalTheory.LeviRatHerm.det_low_ne_zero (cm_conj_conj hB.cm) hX.herm (det_ne_of_sig_c B X.J hX.sig) hX.lat hH`.
-/
theorem det_low {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {r s i₀ i₁ : ℕ} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) : X₁.J.det ≠ 0 :=
  GlobalTheory.LeviRatHerm.det_low_ne_zero (cm_conj_conj hB.cm) hX.herm (det_ne_of_sig_c B X.J hX.sig) hX.lat hH

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X X₁ r s i₀ i₁ H hB hX hH`. Use `haveI := (topAE F E).1`. Establish `hσ : ∀ a, σ (σ a) = a` using `cm_conj_conj hB.cm`. Establish `hJ` using `hX.herm`. Establish `hd : X₁.J.det ≠ 0` using `det_low hB hX hH`.

Establish `hdec : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (X.L : Set (Fin n → E))`. Rewrite using `[hX.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, t, u, -, -, -, hz⟩` from `hH.split z hz`. Conclude with `⟨s, t, u, hz⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨s, t, u, rfl⟩` from `hy`. Take `⟨s', t', u', rfl⟩` from `hz`. Conclude with `⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩`. Consider the case `smul a y _ hy`.

Take `⟨s, t, u, rfl⟩` from `hy`. Conclude with `⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩`. Establish `hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0` using `by rw [hA_incV', hH.xx, map_zero]`. Establish `hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1` using `by rw [hA_incV', hH.xy, map_one]`. Establish `hYX : hA σ X.J (incV F H.y) (incV F H.x) = 1` using `by rw [hA_herm σ X.J hσ hJ, hXY, map_one]`.

Establish `hιX : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0` using `hA_ι_incV σ X.J H.ι H.x (fun u => (hH.orth u).1)`. Establish `hιY : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0` using `hA_ι_incV σ X.J H.ι H.y (fun u => (hH.orth u).2)`. Establish `hXι : ∀ z, hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0` using `fun z => by`. Rewrite using `[hA_herm σ X.J hσ hJ, hιX, map_zero]`. Establish `hYι : ∀ z, hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0` using `fun z => by`.

Rewrite using `[hA_herm σ X.J hσ hJ, hιY, map_zero]`. Establish `hιι : ∀ a w, hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ w) = hA σ X₁.J a w` using `hA_ιι σ X.J X₁.J H.ι hH.gram`. Establish `hself : ∀ v, cA σ (hA σ X.J v v) = hA σ X.J v v` using `fun v => (hA_herm σ X.J hσ hJ v v).symm`. Use `set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def`. Establish `hhalf : (2 : AE F E) * half = 1`.

Rewrite using `[hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]`. Establish `hσhalf : cA σ half = half` using `by rw [hhalf_def, cA_inclR', map_inv₀, map_ofNat]`. Establish `hcf : ∀ (a : Fin n₁ → AE F E) (k : imA σ), ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) + cA σ ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) = -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)`. Introduce `a k`. Establish `hk : cA σ (k : AE F E) = -k` using `k.2`.

Rewrite using `[map_sub, map_mul, hk, hσhalf, hself]`. Take the linear combination `(-hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * hhalf`. Set `Ψf : (Fin n₁ → AE F E) × imA σ → unip σ X H` to `fun p => elt hσ hJ hXX hιX p.1 _ (hcf p.1 p.2)`. Establish `hmatΨ : ∀ p, mat ((Ψf p : unip σ X H) : UA σ X.J) = hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ p.1) ((p.2 : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1))` using `fun p => rfl`. Set `A : Matrix (Fin n) (Fin n) (AE F E) → Fin n₁ → AE F E` to `fun M => Matrix.vecMul (rv σ X H M) (incM F X₁.J⁻¹)`.

Set `K : Matrix (Fin n) (Fin n) (AE F E) → AE F E` to `fun M => hA σ X.J (M *ᵥ incV F H.y - incV F H.y) (incV F H.y) + half * hA σ X.J (incM F H.ι *ᵥ A M) (incM F H.ι *ᵥ A M)`. Establish `hdy : ∀ a c, hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ incV F H.y - incV F H.y = incM F H.ι *ᵥ a + c • incV F H.x`. Introduce `a c`. Rewrite using `[hmat_mulVec, hYX, hYι, one_smul, zero_smul, sub_zero, add_sub_cancel_left]`. Establish `hA_h : ∀ a c, A (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = a`.

Introduce `a c`. Establish `e : rv σ X H (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = Matrix.vecMul a (incM F X₁.J)`. Use function extensionality and compare the values at `j`. Simplify using `only [rv]`. Rewrite using `[hdy, hA_add_l, hA_smul_l, hXι, mul_zero, add_zero, hιι, hA_single]`.

Simplify using `only [A]`. Rewrite using `[e, Matrix.vecMul_vecMul, incM_mul_inv _ hd, Matrix.vecMul_one]`. Establish `hK_h : ∀ a c, K (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = c + half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)`. Introduce `a c`. Simplify using `only [K]`.

Rewrite using `[hA_h, hdy, hA_add_l, hA_smul_l, hιY, hXY, mul_one, zero_add]`. Establish `hmemK : ∀ g : unip σ X H, K (mat (g : UA σ X.J)) ∈ imA σ`. Introduce `g`. Take `⟨b, c, hc, hg⟩` from `unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2`. Rewrite using `[hg, hK_h, mem_imA, map_add, map_mul, hσhalf, hself]`.

Take the linear combination `hc + hA σ X.J (incM F H.ι *ᵥ b) (incM F H.ι *ᵥ b) * hhalf`. Set `invf : unip σ X H → (Fin n₁ → AE F E) × imA σ` to `fun g => (A (mat (g : UA σ X.J)), ⟨K (mat (g : UA σ X.J)), hmemK g⟩)`. Establish `hmc : Continuous fun g : unip σ X H => mat (g : UA σ X.J)` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Establish `hAc : Continuous A` using `continuous_rv.matrix_vecMul continuous_const`. Establish `hKc : Continuous K` using `(continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const).add (continuous_const.mul (continuous_hA X.J (continuous_const.matrix_mulVec hAc) (continuous_const.matrix_mulVec hAc)))`.

Establish `hQc : Continuous fun p : (Fin n₁ → AE F E) × imA σ => hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1)` using `continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_fst)`. Set `Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H` to `{ toFun := Ψf invFun := invf left_inv := fun p => by`. Use `Prod.ext (hA_h _ _) (Subtype.ext ?_)` and prove the remaining obligations. Use `show K (mat ((Ψf p : unip σ X H) : UA σ X.J)) = p.2`. Rewrite using `[hmatΨ, hK_h]`.

Expand and normalize the polynomial expressions, which then agree. Use `right_inv := fun g => by`. Apply `unip_ext'` to reduce the goal to its premises. Take `⟨b, c, hc, hg⟩` from `unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2`. Rewrite using `[hmatΨ]`.

Use `show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ A (mat (g : UA σ X.J))) (K (mat (g : UA σ X.J)) - half * hA σ X.J (incM F H.ι *ᵥ A (mat (g : UA σ X.J))) (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))) = mat (g : UA σ X.J)`. Rewrite using `[hg, hK_h, hA_h, add_sub_cancel_right]`. Use `continuous_toFun := by`. Use `Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _` and prove the remaining obligations. Conclude with `continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst) ((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc))`.

Conclude with `continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst).neg (((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc)).neg.sub hQc)`. Use `continuous_invFun := by`. Use `Continuous.prodMk (hAc.comp hmc) (Continuous.subtype_mk (hKc.comp hmc) _) }` and prove the remaining obligations. Establish `hωmem : ∀ a a' : Fin n₁ → AE F E, half * (hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a') - hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) ∈ imA σ`. Introduce `a a'`.

Rewrite using `[mem_imA, map_mul, map_sub, hσhalf, ← hA_herm σ X.J hσ hJ, ← hA_herm σ X.J hσ hJ]`. Expand and normalize the polynomial expressions, which then agree. Set `ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ` to `fun a a' => ⟨_, hωmem a a'⟩`. Use `⟨Ψ, ω, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (continuous_const.mul ((continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_snd)).sub (continuous_hA X.J (continuous_const.matrix_mulVec continuous_snd) (continuous_const.matrix_mulVec continuous_fst)) …`.

Introduce `a b a' b'`. Apply `unip_ext'` to reduce the goal to its premises. Use `show mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) * mat ((Ψf (a', b') : unip σ X H) : UA σ X.J) = mat ((Ψf (a + a', b + b' + ω a a') : unip σ X H) : UA σ X.J)`. Rewrite using `[hmatΨ, hmatΨ, hmatΨ, hmat_mul hσ hJ _ _ _ _ _ hXX (hιX a) (hιX a'), ← Matrix.mulVec_add]`. Use `congr 1`.

Simplify using `only [AddSubgroup.coe_add, ω, Matrix.mulVec_add, hA_add_l, hA_add_r]`. Take the linear combination `(hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) * hhalf`. Introduce `l g₀ m hL a b`. Establish `hpmem : l.1 * cA σ l.1 * (b : AE F E) ∈ imA σ`. Establish `hb : cA σ (b : AE F E) = -b` using `b.2`.

Rewrite using `[mem_imA, map_mul, map_mul, cA_cA σ hσ, hb]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩), ?_, rfl, rfl⟩` and prove the remaining obligations. Use `set M := mat m with hM`. Establish `hMx : M *ᵥ incV F H.x = l.1 • incV F H.x` using `hL.1`.

Establish `hMι : ∀ w, M *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g₀ *ᵥ w)` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, hL.2.2, ← Matrix.mulVec_mulVec]`. Establish `hx' : M *ᵥ ((l⁻¹).1 • incV F H.x) = incV F H.x`. Rewrite using `[Matrix.mulVec_smul, hMx, smul_smul, Units.inv_mul, one_smul]`. Establish `hMvx : ∀ v, hA σ X.J (M *ᵥ v) (incV F H.x) = cA σ (l⁻¹).1 * hA σ X.J v (incV F H.x)` using `fun v => by`.

Establish `e` using `hA_mat m v ((l⁻¹).1 • incV F H.x)`. Rewrite `e` using `[← hM, hx', hA_smul_r]`. Conclude with `e`. Establish `hιp : incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a)) = cA σ l.1 • (M *ᵥ (incM F H.ι *ᵥ a))`. Rewrite using `[Matrix.mulVec_smul, hMι]`.

Establish `hMvu : ∀ v, hA σ X.J (M *ᵥ v) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) = l.1 * hA σ X.J v (incM F H.ι *ᵥ a)` using `fun v => by`. Rewrite using `[hιp, hA_smul_r, cA_cA σ hσ, hM, hA_mat]`. Establish `hQp : hA σ X.J (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) = cA σ l.1 * l.1 * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)`. Rewrite using `[hιp, hA_smul_l, hA_smul_r, cA_cA σ hσ, hM, hA_mat]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinv : cA σ (l⁻¹).1 * cA σ l.1 = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`. Establish `hMMi : M * mat m⁻¹ = 1`. Rewrite using `[hM, show mat m * mat m⁻¹ = mat (m * m⁻¹) from rfl, mul_inv_cancel]`. Both sides reduce to the same expression. Use `set T := mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) with hT`.

Use `set T' := mat ((Ψf (cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩) : unip σ X H) : UA σ X.J) with hT'`. Establish `key : M * T = T' * M`. Use `hmat_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT, hT', hmatΨ, hmatΨ, hmat_mulVec, hmat_mulVec, hMvx, hMvu, hQp]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hMx, hMι, hιp]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(-(hA σ X.J v (incV F H.x) * (incM F H.ι *ᵥ (mat g₀ *ᵥ a)) i + hA σ X.J v (incV F H.x) * incV F H.x i * ((b : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * l.1)) * hinv`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `show M * T * mat m⁻¹ = T'`. Rewrite using `[key, Matrix.mul_assoc, hMMi, Matrix.mul_one]`.
-/
theorem heis_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∃ (Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H) (ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ),
      Continuous (fun p : (Fin n₁ → AE F E) × (Fin n₁ → AE F E) => ω p.1 p.2) ∧
      (∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a')) ∧
      ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi H l g₀ m → ∀ a b,
        ∃ p : (Fin n₁ → AE F E) × imA σ, m * ((Ψ (a, b) : unip σ X H) : UA σ X.J) * m⁻¹ = ((Ψ p : unip σ X H) : UA σ X.J) ∧
          p.1 = cA σ l • (mat g₀ *ᵥ a) ∧ ((p.2 : imA σ) : AE F E) = l * cA σ l * b := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s i₀ i₁ H hB hX hH
  haveI := (topAE F E).1
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hJ := hX.herm
  have hd : X₁.J.det ≠ 0 := det_low hB hX hH
  have hdec : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
      rw [hX.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have hXX : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV', hH.xx, map_zero]
  have hXY : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV', hH.xy, map_one]
  have hYX : hA σ X.J (incV F H.y) (incV F H.x) = 1 := by rw [hA_herm σ X.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 :=
    hA_ι_incV σ X.J H.ι H.x (fun u => (hH.orth u).1)
  have hιY : ∀ z, hA σ X.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 :=
    hA_ι_incV σ X.J H.ι H.y (fun u => (hH.orth u).2)
  have hXι : ∀ z, hA σ X.J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιX, map_zero]
  have hYι : ∀ z, hA σ X.J (incV F H.y) (incM F H.ι *ᵥ z) = 0 := fun z => by
    rw [hA_herm σ X.J hσ hJ, hιY, map_zero]
  have hιι : ∀ a w, hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ w) = hA σ X₁.J a w :=
    hA_ιι σ X.J X₁.J H.ι hH.gram
  have hself : ∀ v, cA σ (hA σ X.J v v) = hA σ X.J v v := fun v => (hA_herm σ X.J hσ hJ v v).symm
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR', map_inv₀, map_ofNat]
  have hcf : ∀ (a : Fin n₁ → AE F E) (k : imA σ),
      ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) +
        cA σ ((k : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) =
        -hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
    intro a k
    have hk : cA σ (k : AE F E) = -k := k.2
    rw [map_sub, map_mul, hk, hσhalf, hself]
    linear_combination (-hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * hhalf

  let Ψf : (Fin n₁ → AE F E) × imA σ → unip σ X H := fun p => elt hσ hJ hXX hιX p.1 _ (hcf p.1 p.2)
  have hmatΨ : ∀ p, mat ((Ψf p : unip σ X H) : UA σ X.J) = hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ p.1)
      ((p.2 : AE F E) - half * hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1)) := fun p => rfl
  let A : Matrix (Fin n) (Fin n) (AE F E) → Fin n₁ → AE F E := fun M => Matrix.vecMul (rv σ X H M) (incM F X₁.J⁻¹)
  let K : Matrix (Fin n) (Fin n) (AE F E) → AE F E := fun M =>
    hA σ X.J (M *ᵥ incV F H.y - incV F H.y) (incV F H.y) + half * hA σ X.J (incM F H.ι *ᵥ A M) (incM F H.ι *ᵥ A M)
  have hdy : ∀ a c, hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c *ᵥ incV F H.y - incV F H.y =
      incM F H.ι *ᵥ a + c • incV F H.x := by
    intro a c; rw [hmat_mulVec, hYX, hYι, one_smul, zero_smul, sub_zero, add_sub_cancel_left]
  have hA_h : ∀ a c, A (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = a := by
    intro a c
    have e : rv σ X H (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) = Matrix.vecMul a (incM F X₁.J) := by
      funext j; simp only [rv]; rw [hdy, hA_add_l, hA_smul_l, hXι, mul_zero, add_zero, hιι, hA_single]
    simp only [A]; rw [e, Matrix.vecMul_vecMul, incM_mul_inv _ hd, Matrix.vecMul_one]
  have hK_h : ∀ a c, K (hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ a) c) =
      c + half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
    intro a c; simp only [K]; rw [hA_h, hdy, hA_add_l, hA_smul_l, hιY, hXY, mul_one, zero_add]
  have hmemK : ∀ g : unip σ X H, K (mat (g : UA σ X.J)) ∈ imA σ := by
    intro g
    obtain ⟨b, c, hc, hg⟩ := unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2
    rw [hg, hK_h, mem_imA, map_add, map_mul, hσhalf, hself]
    linear_combination hc + hA σ X.J (incM F H.ι *ᵥ b) (incM F H.ι *ᵥ b) * hhalf
  let invf : unip σ X H → (Fin n₁ → AE F E) × imA σ := fun g =>
    (A (mat (g : UA σ X.J)), ⟨K (mat (g : UA σ X.J)), hmemK g⟩)
  have hmc : Continuous fun g : unip σ X H => mat (g : UA σ X.J) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hAc : Continuous A := continuous_rv.matrix_vecMul continuous_const
  have hKc : Continuous K :=
    (continuous_hA X.J ((continuous_id.matrix_mulVec continuous_const).sub continuous_const) continuous_const).add
      (continuous_const.mul (continuous_hA X.J (continuous_const.matrix_mulVec hAc)
        (continuous_const.matrix_mulVec hAc)))
  have hQc : Continuous fun p : (Fin n₁ → AE F E) × imA σ =>
      hA σ X.J (incM F H.ι *ᵥ p.1) (incM F H.ι *ᵥ p.1) :=
    continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst) (continuous_const.matrix_mulVec continuous_fst)
  let Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H :=
    { toFun := Ψf
      invFun := invf
      left_inv := fun p => by
        refine Prod.ext (hA_h _ _) (Subtype.ext ?_)
        show K (mat ((Ψf p : unip σ X H) : UA σ X.J)) = p.2
        rw [hmatΨ, hK_h]; ring
      right_inv := fun g => by
        apply unip_ext'
        obtain ⟨b, c, hc, hg⟩ := unip_eq_hmat σ hσ X H hJ hH.xx hH.yy hH.xy hH.orth hdec _ g.2
        rw [hmatΨ]
        show hmat σ X.J (incV F H.x) (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))
          (K (mat (g : UA σ X.J)) - half * hA σ X.J (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))
            (incM F H.ι *ᵥ A (mat (g : UA σ X.J)))) = mat (g : UA σ X.J)
        rw [hg, hK_h, hA_h, add_sub_cancel_right]
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _
        · exact continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst)
            ((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc))
        · exact continuous_hmat X.J _ (continuous_const.matrix_mulVec continuous_fst).neg
            (((continuous_subtype_val.comp continuous_snd).sub (continuous_const.mul hQc)).neg.sub hQc)
      continuous_invFun := by
        refine Continuous.prodMk (hAc.comp hmc) (Continuous.subtype_mk (hKc.comp hmc) _) }

  have hωmem : ∀ a a' : Fin n₁ → AE F E, half * (hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a') -
      hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) ∈ imA σ := by
    intro a a'
    rw [mem_imA, map_mul, map_sub, hσhalf, ← hA_herm σ X.J hσ hJ, ← hA_herm σ X.J hσ hJ]
    ring
  let ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ := fun a a' => ⟨_, hωmem a a'⟩
  refine ⟨Ψ, ω, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_const.mul
      ((continuous_hA X.J (continuous_const.matrix_mulVec continuous_fst)
        (continuous_const.matrix_mulVec continuous_snd)).sub
      (continuous_hA X.J (continuous_const.matrix_mulVec continuous_snd)
        (continuous_const.matrix_mulVec continuous_fst)))) _
  · intro a b a' b'
    apply unip_ext'
    show mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) * mat ((Ψf (a', b') : unip σ X H) : UA σ X.J) =
      mat ((Ψf (a + a', b + b' + ω a a') : unip σ X H) : UA σ X.J)
    rw [hmatΨ, hmatΨ, hmatΨ, hmat_mul hσ hJ _ _ _ _ _ hXX (hιX a) (hιX a'), ← Matrix.mulVec_add]
    congr 1
    simp only [AddSubgroup.coe_add, ω, Matrix.mulVec_add, hA_add_l, hA_add_r]
    linear_combination (hA σ X.J (incM F H.ι *ᵥ a') (incM F H.ι *ᵥ a)) * hhalf
  · intro l g₀ m hL a b
    have hpmem : l.1 * cA σ l.1 * (b : AE F E) ∈ imA σ := by
      have hb : cA σ (b : AE F E) = -b := b.2
      rw [mem_imA, map_mul, map_mul, cA_cA σ hσ, hb]; ring
    refine ⟨(cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩), ?_, rfl, rfl⟩
    set M := mat m with hM
    have hMx : M *ᵥ incV F H.x = l.1 • incV F H.x := hL.1
    have hMι : ∀ w, M *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g₀ *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hL.2.2, ← Matrix.mulVec_mulVec]
    have hx' : M *ᵥ ((l⁻¹).1 • incV F H.x) = incV F H.x := by
      rw [Matrix.mulVec_smul, hMx, smul_smul, Units.inv_mul, one_smul]
    have hMvx : ∀ v, hA σ X.J (M *ᵥ v) (incV F H.x) = cA σ (l⁻¹).1 * hA σ X.J v (incV F H.x) := fun v => by
      have e := hA_mat m v ((l⁻¹).1 • incV F H.x)
      rw [← hM, hx', hA_smul_r] at e
      exact e
    have hιp : incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a)) = cA σ l.1 • (M *ᵥ (incM F H.ι *ᵥ a)) := by
      rw [Matrix.mulVec_smul, hMι]
    have hMvu : ∀ v, hA σ X.J (M *ᵥ v) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) =
        l.1 * hA σ X.J v (incM F H.ι *ᵥ a) := fun v => by
      rw [hιp, hA_smul_r, cA_cA σ hσ, hM, hA_mat]
    have hQp : hA σ X.J (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) (incM F H.ι *ᵥ (cA σ l • (mat g₀ *ᵥ a))) =
        cA σ l.1 * l.1 * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a) := by
      rw [hιp, hA_smul_l, hA_smul_r, cA_cA σ hσ, hM, hA_mat]; ring
    have hinv : cA σ (l⁻¹).1 * cA σ l.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hMMi : M * mat m⁻¹ = 1 := by
      rw [hM, show mat m * mat m⁻¹ = mat (m * m⁻¹) from rfl, mul_inv_cancel]; rfl
    set T := mat ((Ψf (a, b) : unip σ X H) : UA σ X.J) with hT
    set T' := mat ((Ψf (cA σ l • (mat g₀ *ᵥ a), ⟨_, hpmem⟩) : unip σ X H) : UA σ X.J) with hT'
    have key : M * T = T' * M := by
      refine hmat_ext fun v => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT, hT', hmatΨ, hmatΨ, hmat_mulVec, hmat_mulVec,
        hMvx, hMvu, hQp]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hMx, hMι, hιp]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(hA σ X.J v (incV F H.x) * (incM F H.ι *ᵥ (mat g₀ *ᵥ a)) i +
        hA σ X.J v (incV F H.x) * incV F H.x i * ((b : AE F E) -
          half * hA σ X.J (incM F H.ι *ᵥ a) (incM F H.ι *ᵥ a)) * l.1)) * hinv
    apply Subtype.ext; apply Units.ext
    show M * T * mat m⁻¹ = T'
    rw [key, Matrix.mul_assoc, hMMi, Matrix.mul_one]

end

section

open GlobalTheory.LeviModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n₁ X₁ hB hX _ _ _ _ l g₀ L hL`. Use `haveI : IsTotallyReal F := hB.cm.1`. Take `⟨-, -, hsc, -⟩` from `topAE F E`. Use `haveI := hsc`. Use `haveI : LocallyCompactSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n₁ → Fin 1 → AE F E))`.

Use `haveI : SecondCountableTopology (Matrix (Fin n₁) (Fin 1) (AE F E)) := inferInstanceAs (SecondCountableTopology (Fin n₁ → Fin 1 → AE F E))`. Use `letI : MeasurableSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := borel _`. Use `haveI : BorelSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := ⟨rfl⟩`. Set `c : (AE F E)ˣ` to `GlobalTheory.Doubling.conjUnit σ l`. Set `g : GL (Fin n₁) (AE F E)` to `Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c * g₀.1`.

Establish `hg : (g : Matrix (Fin n₁) (Fin n₁) (AE F E)) = (c : AE F E) • mat g₀` using `by show Matrix.scalar (Fin n₁) (c : AE F E) * mat g₀ = _`. Rewrite using `[Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]`. Set `e : Matrix (Fin n₁) (Fin 1) (AE F E) ≃ₜ+ (Fin n₁ → AE F E)` to `{ toFun := fun u i => u i 0 invFun := fun a => Matrix.of fun i _ => a i left_inv := fun u => by`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim j 0]`.

Both sides reduce to the same expression. Use `right_inv := fun a => rfl`. Use the proof step `map_add' := fun u v => rfl`. Use `continuous_toFun := continuous_pi fun i => continuous_id.matrix_elem i 0`. Use `continuous_invFun := continuous_matrix fun i _ => continuous_apply i }`.

Establish `htr` using `GlobalTheory.ModuLR.addEquivAddHaarChar_transport e (GlobalTheory.ModuLR.lrCE g 1)`. Establish `hext : (e.symm.trans (GlobalTheory.ModuLR.lrCE g 1)).trans e = L`. Use extensionality with `a i`. Rewrite using `[hL]`. Use `show ((g : Matrix (Fin n₁) (Fin n₁) (AE F E)) * Matrix.of (fun i (_ : Fin 1) => a i) * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0 = ((c : AE F E) • (mat g₀ *ᵥ a)) i`.

Rewrite using `[hg, Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite `htr` using `[hext]`. Rewrite using `[htr, GlobalTheory.ModuLR.chi_lr F E n₁ 1 g 1, map_one, map_one, one_pow, mul_one, pow_one, map_mul, map_mul, GlobalTheory.LeviModulus.CharVec.absE_det_eq_one σ hX g₀, mul_one]`. Establish `hdet : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c) = c ^ n₁`.

Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]`. Rewrite using `[hdet, map_pow, GlobalTheory.Doubling.absE_conjUnit]`.
-/
theorem haarChar_smul_mulVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X₁ : Spc F E n₁), B.IsGood σ → X₁.J.det ≠ 0 →
    ∀ [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [MeasurableSpace (Fin n₁ → AE F E)]
      [BorelSpace (Fin n₁ → AE F E)] (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (L : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E)),
      (∀ a, L a = cA σ l • (mat g₀ *ᵥ a)) → addEquivAddHaarChar L = absE F E l ^ n₁ := by
  intro F E _ _ _ _ _ σ B n₁ X₁ hB hX _ _ _ _ l g₀ L hL
  haveI : IsTotallyReal F := hB.cm.1
  obtain ⟨-, -, hsc, -⟩ := topAE F E
  haveI := hsc
  haveI : LocallyCompactSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n₁ → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n₁) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n₁ → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin n₁) (Fin 1) (AE F E)) := ⟨rfl⟩
  let c : (AE F E)ˣ := GlobalTheory.Doubling.conjUnit σ l
  let g : GL (Fin n₁) (AE F E) :=
    Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c * g₀.1
  have hg : (g : Matrix (Fin n₁) (Fin n₁) (AE F E)) = (c : AE F E) • mat g₀ := by
    show Matrix.scalar (Fin n₁) (c : AE F E) * mat g₀ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  let e : Matrix (Fin n₁) (Fin 1) (AE F E) ≃ₜ+ (Fin n₁ → AE F E) :=
    { toFun := fun u i => u i 0
      invFun := fun a => Matrix.of fun i _ => a i
      left_inv := fun u => by
        ext i j
        rw [Subsingleton.elim j 0]
        rfl
      right_inv := fun a => rfl
      map_add' := fun u v => rfl
      continuous_toFun := continuous_pi fun i => continuous_id.matrix_elem i 0
      continuous_invFun := continuous_matrix fun i _ => continuous_apply i }
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport e (GlobalTheory.ModuLR.lrCE g 1)
  have hext : (e.symm.trans (GlobalTheory.ModuLR.lrCE g 1)).trans e = L := by
    ext a i
    rw [hL]
    show ((g : Matrix (Fin n₁) (Fin n₁) (AE F E)) * Matrix.of (fun i (_ : Fin 1) => a i) *
      ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0 = ((c : AE F E) • (mat g₀ *ᵥ a)) i
    rw [hg, Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hext] at htr
  rw [htr, GlobalTheory.ModuLR.chi_lr F E n₁ 1 g 1, map_one, map_one, one_pow, mul_one, pow_one, map_mul, map_mul,
    GlobalTheory.LeviModulus.CharVec.absE_det_eq_one σ hX g₀, mul_one]
  have hdet : Matrix.GeneralLinearGroup.det
      (Units.map (Matrix.scalar (Fin n₁) : AE F E →+* Matrix (Fin n₁) (Fin n₁) (AE F E)).toMonoidHom c) = c ^ n₁ := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]
  rw [hdet, map_pow, GlobalTheory.Doubling.absE_conjUnit]

/- English proof (translation)
Take `⟨hx, hy, hι⟩` from `h`. Establish `hinv : mat m⁻¹ * mat m = 1` using `GlobalTheory.StabHaar.mat_inv_mul m`. Establish `hinv₁ : mat g₀ * mat g₀⁻¹ = 1` using `GlobalTheory.StabHaar.mat_mul_inv g₀`. Establish `hcl : cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (l : AE F E) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul]`. Use `_ = _ := by rw [← hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Rewrite using `[inv_inv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_smul, smul_smul, mul_comm, hcl, one_smul]`. Use `_ = _ := by rw [← hy, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isLevi_inv {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} (H : Plane E n n₁) {l : (AE F E)ˣ}
    {g₀ : UA σ X₁.J} {m : UA σ X.J} (h : IsLevi H l g₀ m) : IsLevi H l⁻¹ g₀⁻¹ m⁻¹ := by
  obtain ⟨hx, hy, hι⟩ := h
  have hinv : mat m⁻¹ * mat m = 1 := GlobalTheory.StabHaar.mat_inv_mul m
  have hinv₁ : mat g₀ * mat g₀⁻¹ = 1 := GlobalTheory.StabHaar.mat_mul_inv g₀
  have hcl : cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (l : AE F E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨?_, ?_, ?_⟩
  · calc mat m⁻¹ *ᵥ incV F H.x
        = ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat m⁻¹ *ᵥ ((l : AE F E) • incV F H.x)) := by
          rw [Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [← hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · rw [inv_inv]
    calc mat m⁻¹ *ᵥ incV F H.y
        = cA σ (l : AE F E) • (mat m⁻¹ *ᵥ (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y)) := by
          rw [Matrix.mulVec_smul, smul_smul, mul_comm, hcl, one_smul]
      _ = _ := by rw [← hy, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * (mat g₀ * mat g₀⁻¹)) := by rw [hinv₁, Matrix.mul_one]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat g₀⁻¹ := by rw [hι]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat g₀⁻¹ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

/- English proof (translation)
Rewrite `*` using `[mem_imA]`. Rewrite using `[map_mul, ha, hz, mul_neg]`.
-/
theorem mul_mem_imA {a z : AE F E} (ha : cA σ a = a) (hz : z ∈ imA σ) : a * z ∈ imA σ := by
  rw [mem_imA] at *
  rw [map_mul, ha, hz, mul_neg]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X X₁ r s i₀ i₁ H hB hX hH m hm μN hμ l g₀ f hf`. Take `⟨hR, hLC, hSC, hT2⟩` from `topAE F E`. Use `haveI := hR`. Use `haveI := hLC`. Use `haveI := hSC`.

Use `haveI := hT2`. Take `⟨hTG, hLCU, hSCU, hT2U⟩` from `topUA σ X.J`. Use `haveI := hTG`. Use `haveI := hLCU`. Use `haveI := hSCU`.

Use `haveI := hT2U`. Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Establish `hx0 : H.x ≠ 0` using `fun h0 => by`. Establish `h1` using `hH.xy`. Rewrite `h1` using `[h0]`.

Simplify using `[form] at h1`. Establish `hcl` using `GlobalTheory.UnipClosed.isClosed_unip F E σ n n₁ X H hx0`. Use `haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Take `⟨Ψ, ω, hω, hlaw, hconj⟩` from `heis_coords F E σ B n n₁ X X₁ r s i₀ i₁ H hB hX hH`.

Establish `hmem : ∀ (l' : (AE F E)ˣ) (g' : UA σ X₁.J) (m' : UA σ X.J), IsLevi H l' g' m' → ∀ u ∈ unip σ X H, m' * u * m'⁻¹ ∈ unip σ X H`. Introduce `l' g' m' hl' u hu`. Take `⟨p, hp, -, -⟩` from `hconj l' g' m' hl' (Ψ.symm ⟨u, hu⟩).1 (Ψ.symm ⟨u, hu⟩).2`. Rewrite `hp` using `[Prod.mk.eta, Homeomorph.apply_symm_apply]`. Rewrite using `[hp]`.

Conclude with `(Ψ p).2`. Establish `hm0` using `hm l g₀`. Establish `h₁` using `hmem l g₀ (m l g₀) hm0`. Establish `h₂ : ∀ u ∈ unip σ X H, (m l g₀)⁻¹ * u * m l g₀ ∈ unip σ X H` using `fun u hu => by`. Simplify using `using hmem _ _ _ (isLevi_inv H hm0) u hu`.

Set `φ` to `conjOn (unip σ X H) (m l g₀) h₁ h₂`. Establish `hσσ : ∀ a, σ (σ a) = a` using `cm_conj_conj hB.cm`. Establish `hcc : ∀ z : AE F E, cA σ (cA σ z) = z` using `cA_cA σ hσσ`. Establish `hcu : ∀ u : (AE F E)ˣ, cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (u : AE F E) = 1` using `fun u => by`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Establish `hcu' : ∀ u : (AE F E)ˣ, cA σ (u : AE F E) * cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) = 1` using `fun u => by`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hN : ∀ u : (AE F E)ˣ, cA σ ((u : AE F E) * cA σ u) = u * cA σ u` using `fun u => by`. Rewrite using `[map_mul, hcc, mul_comm]`. Establish `hmc : Continuous fun a : Fin n₁ → AE F E => a` using `continuous_id`.

Set `L₁ : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E)` to `{ toFun := fun a => cA σ (l : AE F E) • (mat g₀ *ᵥ a) invFun := fun a => cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat g₀⁻¹ *ᵥ a) left_inv := fun a => by`. Simplify using `only`. Rewrite using `[Matrix.mulVec_smul, smul_smul, hcu, one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]`. Use `right_inv := fun a => by`. Simplify using `only`.

Rewrite using `[Matrix.mulVec_smul, smul_smul, hcu', one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec]`. Use the proof step `map_add' := fun a b => by simp only [Matrix.mulVec_add, smul_add]`. Use `continuous_toFun := (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ (l : AE F E))`. Use `continuous_invFun := (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E)) }`. Set `L₂ : imA σ ≃ₜ+ imA σ` to `{ toFun := fun b => ⟨(l : AE F E) * cA σ l * b, mul_mem_imA (hN l) b.2⟩ invFun := fun b => ⟨((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * b, mul_mem_imA (hN l⁻¹) b.2⟩ left_inv := fun b => Subtype.ext (by`.

Simplify using `only`. Rewrite using `[← mul_assoc, mul_mul_mul_comm, Units.inv_mul, hcu, one_mul, one_mul])`. Use `right_inv := fun b => Subtype.ext (by`. Simplify using `only`. Rewrite using `[← mul_assoc, mul_mul_mul_comm, Units.mul_inv, hcu', one_mul, one_mul])`.

Use the proof step `map_add' := fun a b => Subtype.ext (by simp only [AddSubgroup.coe_add, mul_add])`. Use `continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _`. Use `continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _ }`. Establish `hφΨ : ∀ a b, φ (Ψ (a, b)) = Ψ (L₁ a, L₂ b)`. Introduce `a b`.

Take `⟨p, hp, hp1, hp2⟩` from `hconj l g₀ (m l g₀) hm0 a b`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[conjOn_apply, hp]`. Use `congr 2`. Conclude with `Prod.ext hp1 (Subtype.ext hp2)`.

Use `letI : MeasurableSpace (Fin n₁ → AE F E) := borel _`. Use `haveI : BorelSpace (Fin n₁ → AE F E) := ⟨rfl⟩`. Use `letI : MeasurableSpace (imA σ) := borel _`. Use `haveI : BorelSpace (imA σ) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (imA σ) := (isClosed_imA σ).isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (imA σ) := (isClosed_imA σ).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Establish `hchar : mulEquivHaarChar φ = absE F E l ^ n₁ * absE F E l`. Rewrite using `[GlobalTheory.mulEquivHaarChar_heisenberg_chart _ _ _ Ψ ω hω hlaw φ L₁ L₂ hφΨ, haarChar_smul_mulVec F E σ B n₁ X₁ hB (det_low hB hX hH) l g₀ L₁ (fun a => rfl), GlobalTheory.ImaginaryModulus.addEquivAddHaarChar_imA F E σ B hB l L₂ (fun b => rfl)]`. Use `haveI : IsTopologicalGroup (unip σ X H) := inferInstance`. Use `haveI : T2Space (unip σ X H) := inferInstance`.

Use `haveI : RegularSpace (unip σ X H) := by first`. Consider the case `exact IsTopologicalGroup.regularSpace _`. Consider the case `exact TopologicalGroup.regularSpace _`. Consider the case `exact inferInstanceAs (RegularSpace (Subtype _))`. Use `haveI : T1Space (unip σ X H) := T2Space.t1Space`.

Use `haveI : T0Space (unip σ X H) := T1Space.t0Space`. Use `haveI : T3Space (unip σ X H) := T3Space.mk`. Use `haveI : TopologicalSpace.MetrizableSpace (unip σ X H) := TopologicalSpace.metrizableSpace_of_t3_secondCountable _`. Use `haveI : μN.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _`. Establish `hsm` using `mulEquivHaarChar_smul_map μN φ`.

Rewrite `hsm` using `[hchar]`. Establish `hpos : absE F E l ≠ 0` using `((Group.isUnit l).map (absE F E)).ne_zero`. Use `set c : ℝ≥0 := absE F E l ^ n₁ * absE F E l with hc`. Establish `hc0 : c ≠ 0` using `mul_ne_zero (pow_ne_zero _ hpos) hpos`. Establish `hmap : μN.map φ = c⁻¹ • μN` using `by conv_rhs => rw [← hsm]`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Establish `e1 : ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ∫⁻ u, f u.1 ∂(μN.map φ)` using `(lintegral_map_equiv (fun v : unip σ X H => f v.1) φ.toHomeomorph.toMeasurableEquiv).symm`. Rewrite using `[e1, hmap, lintegral_smul_measure]`. Establish `hn : (n : ℝ) = n₁ + 2` using `by rw [hH.rank]; push_cast; ring`. Establish `e2 : ((absE F E l : ℝ)) ^ (1 - (n : ℝ)) = ((c⁻¹ : ℝ≥0) : ℝ)`.

Rewrite using `[hn, show (1 : ℝ) - (n₁ + 2) = -((n₁ + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (NNReal.coe_nonneg _), Real.rpow_natCast, hc, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_pow, pow_succ]`. Rewrite using `[e2, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]`.
-/
theorem lintegral_conj_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s i₀ i₁ : ℕ) (H : Plane E n n₁), B.IsGood σ → X.IsHerm σ B r s →
    H.IsAdapted σ B X X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ (μN : Measure (unip σ X H)), μN.IsHaarMeasure → ∀ l g₀ (f : UA σ X.J → ENNReal), Measurable f →
      ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) * ∫⁻ u, f u.1 ∂μN := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s i₀ i₁ H hB hX hH m hm μN hμ l g₀ f hf
  obtain ⟨hR, hLC, hSC, hT2⟩ := topAE F E
  haveI := hR; haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTG, hLCU, hSCU, hT2U⟩ := topUA σ X.J
  haveI := hTG; haveI := hLCU; haveI := hSCU; haveI := hT2U
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hcl := GlobalTheory.UnipClosed.isClosed_unip F E σ n n₁ X H hx0
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  obtain ⟨Ψ, ω, hω, hlaw, hconj⟩ := heis_coords F E σ B n n₁ X X₁ r s i₀ i₁ H hB hX hH
  have hmem : ∀ (l' : (AE F E)ˣ) (g' : UA σ X₁.J) (m' : UA σ X.J), IsLevi H l' g' m' →
      ∀ u ∈ unip σ X H, m' * u * m'⁻¹ ∈ unip σ X H := by
    intro l' g' m' hl' u hu
    obtain ⟨p, hp, -, -⟩ := hconj l' g' m' hl' (Ψ.symm ⟨u, hu⟩).1 (Ψ.symm ⟨u, hu⟩).2
    rw [Prod.mk.eta, Homeomorph.apply_symm_apply] at hp
    rw [hp]
    exact (Ψ p).2
  have hm0 := hm l g₀
  have h₁ := hmem l g₀ (m l g₀) hm0
  have h₂ : ∀ u ∈ unip σ X H, (m l g₀)⁻¹ * u * m l g₀ ∈ unip σ X H := fun u hu => by
    simpa using hmem _ _ _ (isLevi_inv H hm0) u hu
  let φ := conjOn (unip σ X H) (m l g₀) h₁ h₂
  have hσσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hcc : ∀ z : AE F E, cA σ (cA σ z) = z := cA_cA σ hσσ
  have hcu : ∀ u : (AE F E)ˣ, cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (u : AE F E) = 1 := fun u => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hcu' : ∀ u : (AE F E)ˣ, cA σ (u : AE F E) * cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have hN : ∀ u : (AE F E)ˣ, cA σ ((u : AE F E) * cA σ u) = u * cA σ u := fun u => by
    rw [map_mul, hcc, mul_comm]
  have hmc : Continuous fun a : Fin n₁ → AE F E => a := continuous_id
  let L₁ : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E) :=
    { toFun := fun a => cA σ (l : AE F E) • (mat g₀ *ᵥ a)
      invFun := fun a => cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat g₀⁻¹ *ᵥ a)
      left_inv := fun a => by
        simp only
        rw [Matrix.mulVec_smul, smul_smul, hcu, one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul,
          Matrix.one_mulVec]
      right_inv := fun a => by
        simp only
        rw [Matrix.mulVec_smul, smul_smul, hcu', one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv,
          Matrix.one_mulVec]
      map_add' := fun a b => by simp only [Matrix.mulVec_add, smul_add]
      continuous_toFun := (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ (l : AE F E))
      continuous_invFun :=
        (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E)) }
  let L₂ : imA σ ≃ₜ+ imA σ :=
    { toFun := fun b => ⟨(l : AE F E) * cA σ l * b, mul_mem_imA (hN l) b.2⟩
      invFun := fun b => ⟨((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * b, mul_mem_imA (hN l⁻¹) b.2⟩
      left_inv := fun b => Subtype.ext (by
        simp only
        rw [← mul_assoc, mul_mul_mul_comm, Units.inv_mul, hcu, one_mul, one_mul])
      right_inv := fun b => Subtype.ext (by
        simp only
        rw [← mul_assoc, mul_mul_mul_comm, Units.mul_inv, hcu', one_mul, one_mul])
      map_add' := fun a b => Subtype.ext (by simp only [AddSubgroup.coe_add, mul_add])
      continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _ }
  have hφΨ : ∀ a b, φ (Ψ (a, b)) = Ψ (L₁ a, L₂ b) := by
    intro a b
    obtain ⟨p, hp, hp1, hp2⟩ := hconj l g₀ (m l g₀) hm0 a b
    apply Subtype.ext
    rw [conjOn_apply, hp]
    congr 2
    exact Prod.ext hp1 (Subtype.ext hp2)
  letI : MeasurableSpace (Fin n₁ → AE F E) := borel _
  haveI : BorelSpace (Fin n₁ → AE F E) := ⟨rfl⟩
  letI : MeasurableSpace (imA σ) := borel _
  haveI : BorelSpace (imA σ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (imA σ) := (isClosed_imA σ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (imA σ) :=
    (isClosed_imA σ).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have hchar : mulEquivHaarChar φ = absE F E l ^ n₁ * absE F E l := by
    rw [GlobalTheory.mulEquivHaarChar_heisenberg_chart _ _ _ Ψ ω hω hlaw φ L₁ L₂ hφΨ, haarChar_smul_mulVec F E σ B n₁ X₁ hB (det_low hB hX hH) l g₀ L₁ (fun a => rfl),
      GlobalTheory.ImaginaryModulus.addEquivAddHaarChar_imA F E σ B hB l L₂ (fun b => rfl)]
  haveI : IsTopologicalGroup (unip σ X H) := inferInstance
  haveI : T2Space (unip σ X H) := inferInstance
  haveI : RegularSpace (unip σ X H) := by
    first
    | exact IsTopologicalGroup.regularSpace _
    | exact TopologicalGroup.regularSpace _
    | exact inferInstanceAs (RegularSpace (Subtype _))
  haveI : T1Space (unip σ X H) := T2Space.t1Space
  haveI : T0Space (unip σ X H) := T1Space.t0Space
  haveI : T3Space (unip σ X H) := T3Space.mk
  haveI : TopologicalSpace.MetrizableSpace (unip σ X H) := TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : μN.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hsm := mulEquivHaarChar_smul_map μN φ
  rw [hchar] at hsm
  have hpos : absE F E l ≠ 0 := ((Group.isUnit l).map (absE F E)).ne_zero
  set c : ℝ≥0 := absE F E l ^ n₁ * absE F E l with hc
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hpos) hpos
  have hmap : μN.map φ = c⁻¹ • μN := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 : ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ∫⁻ u, f u.1 ∂(μN.map φ) :=
    (lintegral_map_equiv (fun v : unip σ X H => f v.1) φ.toHomeomorph.toMeasurableEquiv).symm
  rw [e1, hmap, lintegral_smul_measure]
  have hn : (n : ℝ) = n₁ + 2 := by rw [hH.rank]; push_cast; ring
  have e2 : ((absE F E l : ℝ)) ^ (1 - (n : ℝ)) = ((c⁻¹ : ℝ≥0) : ℝ) := by
    rw [hn, show (1 : ℝ) - (n₁ + 2) = -((n₁ + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (NNReal.coe_nonneg _),
      Real.rpow_natCast, hc, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_pow, pow_succ]
  rw [e2, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB _ hXY hH m hm μN hμ l g₀ f hf`. Conclude with `lintegral_conj_levi F E σ B n n₁ (reS X Y) X₁ r s i₀ i₁ H hB hXY hH m hm μN hμ l g₀ f hf`.
-/
theorem lintegral_conj_levi_reS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ (μN : Measure (unip σ X H)), μN.IsHaarMeasure → ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (f : UA σ X.J → ℝ≥0∞), Measurable f → ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) * ∫⁻ u, f u.1 ∂μN := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB _ hXY hH m hm μN hμ l g₀ f hf
  exact lintegral_conj_levi F E σ B n n₁ (reS X Y) X₁ r s i₀ i₁ H hB hXY hH m hm μN hμ l g₀ f hf

end GlobalTheory.LeviModulusAdapted

end
