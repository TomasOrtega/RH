import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TargetFact

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MatAlg

variable {K : Type*} [Field K] {n : ℕ}

/- English proof (translation)
Establish `hu : IsUnit A.det` using `by rw [det_lo' hA]; exact isUnit_one`. Rewrite using `[Matrix.add_mul, Matrix.mul_nonsing_inv A hu, Matrix.smul_mul]`.
-/
theorem lam_form {A Δ : Matrix (Fin n) (Fin n) K} (hA : IsLo A) (a : K) :
    (A + a • Δ) * A⁻¹ = 1 + a • (Δ * A⁻¹) := by
  have hu : IsUnit A.det := by rw [det_lo' hA]; exact isUnit_one
  rw [Matrix.add_mul, Matrix.mul_nonsing_inv A hu, Matrix.smul_mul]

/- English proof (translation)
Establish `hu : IsUnit B.det` using `by rw [det_up' hB]; exact isUnit_one`. Rewrite using `[Matrix.mul_add, Matrix.nonsing_inv_mul B hu, Matrix.mul_smul]`.
-/
theorem mu_form {B Δ : Matrix (Fin n) (Fin n) K} (hB : IsUp B) (a : K) :
    B⁻¹ * (B + a • Δ) = 1 + a • (B⁻¹ * Δ) := by
  have hu : IsUnit B.det := by rw [det_up' hB]; exact isUnit_one
  rw [Matrix.mul_add, Matrix.nonsing_inv_mul B hu, Matrix.mul_smul]

/- English proof (translation)
Rewrite using `[Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem one_smul_apply (a : K) (N : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (1 + a • N) i j = (if i = j then 1 else 0) + a * N i j := by
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

end MatAlg

section Typed

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

/- English proof (translation)
Use `haveI := (D.s.atP p).lf`. Conclude with `Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) k`.
-/
theorem sgn_mem_O (p : PlF D) (k : ℕ) :
    (-1 : (D.s.atP p).Fp) ^ k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) k

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `w O hO`. Take `⟨Y, -, ⟨w₀, -, ⟨ξ, η⟩, hYeq⟩, rfl⟩` from `hO`. Use `haveI := (D.s.atP p).lf`. Establish `hAg` using `(hA p).2.2.2.2.2`. Break down `hM' : (M p).split with _ | g` into its components or cases.

Conclude with `absurd hM' hMp`. Break down `hR : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `only [hM', hR] at hAg`. Simplify using `only [hM', hR] at hAg`. Take `⟨hge, hgq⟩` from `hAg`.

Use `set Zd : LocDat D := ⟨δ, M, hA⟩`. Use `set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1`. Use `set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2`. Use `set S := Sg (D.s.atP p).Fp D.R.rS with hS`. Use `set s : Fin (D.R.rS + 1) → (D.s.atP p).Fp := fun a => (-1) ^ (D.R.rS - a.val) with hsdef`.

Establish `hSd : S = Matrix.diagonal s` using `rfl`. Establish `hs : ∀ a, s a * s a = 1` using `fun a => sgn_sq' D.R.rS a`. Establish `hSS : S * S = 1` using `sg_sq _`. Use `set cfv := cf Zd p with hcfv`. Use `set cfiv := cfi Zd p with hcfiv`.

Establish `hcc : ∀ a, cfv a * cfiv a = 1` using `cf_cfi Zd p`. Establish `hcc' : ∀ a, cfiv a * cfv a = 1` using `cfi_cf Zd p`. Establish `hdd : Matrix.diagonal cfv * Matrix.diagonal cfiv = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `[hcc]`.

Establish `hdd' : Matrix.diagonal cfiv * Matrix.diagonal cfv = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `[hcc']`. Establish `conj1 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv = X`. Introduce `X`.

Rewrite using `[show Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv = (Matrix.diagonal cfv * Matrix.diagonal cfiv) * X * (Matrix.diagonal cfv * Matrix.diagonal cfiv) by`. Simplify using `only [Matrix.mul_assoc], hdd, Matrix.one_mul, Matrix.mul_one]`. Establish `conj2 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv = X`. Introduce `X`. Rewrite using `[show Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv = (Matrix.diagonal cfiv * Matrix.diagonal cfv) * X * (Matrix.diagonal cfiv * Matrix.diagonal cfv) by`.

Simplify using `only [Matrix.mul_assoc], hdd', Matrix.one_mul, Matrix.mul_one]`. Establish `hSt : S.transpose = S` using `Matrix.diagonal_transpose _`. Establish `sconj : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, S * (S * X * S) * S = X`. Introduce `X`. Rewrite using `[show S * (S * X * S) * S = (S * S) * X * (S * S) by simp only [Matrix.mul_assoc], hSS, Matrix.one_mul, Matrix.mul_one]`.

Take `⟨Gl, Gu, hGl, hGu, hM0⟩` from `target_fact Zd p sg hR g hM' hge hgq u u' w`. Establish `hGlu : IsUnit Gl.det` using `by rw [det_lo' hGl]; exact isUnit_one`. Establish `hGuu : IsUnit Gu.det` using `by rw [det_up' hGu]; exact isUnit_one`. Use `set Λ₀ := Loc.uLow ξ * Gl⁻¹ with hΛ₀`. Use `set V₀ := Gu⁻¹ * Loc.uUp w₀ η with hV₀`.

Establish `hΛ₀lo : IsLo Λ₀` using `isLo_mul (isLo_uLow ξ) (isLo_inv hGl)`. Establish `hV₀up : IsUp V₀` using `isUp_mul (isUp_inv hGu) (isUp_uUp w₀ η)`. Establish `hY : Y = Λ₀ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * V₀`. Rewrite using `[hYeq, hΛ₀, hV₀]`. Rewrite using `[show Loc.uLow ξ * Gl⁻¹ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * (Gu⁻¹ * Loc.uUp w₀ η) = Loc.uLow ξ * (Gl⁻¹ * Gl) * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * (Gu * Gu⁻¹) * Loc.uUp w₀ η by`.

Simplify using `only [Matrix.mul_assoc], Matrix.nonsing_inv_mul Gl hGlu, Matrix.mul_nonsing_inv Gu hGuu, Matrix.mul_one,`. Use the proof step `Matrix.mul_one]`. Use `set A1 := Λ₀.map (p1 sg.e) with hA1`. Use `set A2 := Λ₀.map (p2 sg.e) with hA2`. Use `set B1 := V₀.map (p1 sg.e) with hB1`.

Use `set B2 := V₀.map (p2 sg.e) with hB2`. Establish `hA1lo : IsLo A1` using `isLo_map _ hΛ₀lo`. Establish `hA2lo : IsLo A2` using `isLo_map _ hΛ₀lo`. Establish `hB1up : IsUp B1` using `isUp_map _ hV₀up`. Establish `hB2up : IsUp B2` using `isUp_map _ hV₀up`.

Establish `hΛ₀glue : Λ₀ = glue sg.e A1 A2` using `mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])`. Establish `hV₀glue : V₀ = glue sg.e B1 B2` using `mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])`. Use `set Lp := glue sg.e (Matrix.diagonal cfiv * A1 * Matrix.diagonal cfv) (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S).transpose with hLp`. Use `set Up := glue sg.e (Matrix.diagonal cfv * B1 * Matrix.diagonal cfiv) (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S).transpose with hUp`. Establish `hLplo : IsLo Lp` using `isLo_glue sg.e (isLo_conj hA1lo cfiv cfv hcc') (isLo_transpose (isUp_sconj s cfv cfiv hSd hs hcc hB2up))`.

Establish `hUpup : IsUp Up` using `isUp_glue sg.e (isUp_conj hB1up cfv cfiv hcc) (isUp_transpose (isLo_sconj s cfiv cfv hSd hs hcc' hA2lo))`. Take `⟨c', hc'0, hc'⟩` from `clear_Fp p (ι := (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕ (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1))) (Sum.elim (fun t => cfv t.2.1 * cfiv t.2.2.1 * (if t.1 = 0 then A1⁻¹ else A2⁻¹) t.2.2.1 t.2.2.2) (fun t => (if t.1 = 0 then B1⁻¹ e …`. Use `haveI := (D.s.atP p).ellPrime`. Use `set ℓ : 𝓞 D.host.F := ((Loc.resChar p : ℕ) : 𝓞 D.host.F) with hℓ`. Establish `hℓ0 : ℓ ≠ 0`.

Rewrite using `[hℓ, Ne, Nat.cast_eq_zero]`. Conclude with `(Fact.out : (Loc.resChar p).Prime).ne_zero`. Establish `hℓq : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F ℓ) = (sg.q : (D.s.atP p).Fp)`. Rewrite using `[hℓ, map_natCast, map_natCast, sg.q_eq]`. Use `⟨Lp, Up, ℓ * c', mul_ne_zero hℓ0 hc'0, hLplo, hUpup, ?_⟩` and prove the remaining obligations.

Introduce `L B hL hB hLc hBc`. Use `choose oL hoL hLeq using hLc`. Use `choose oB hoB hBeq using hBc`. Use `set a' := (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c') with ha'`. Use `set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hq`.

Establish `ha : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F (ℓ * c')) = q * a'`. Rewrite using `[map_mul, map_mul, hℓq]`. Simplify using `only [ha] at hLeq hBeq`. Establish `hOc : ∀ x ∈ (D.s.atP p).O, p1 sg.e x ∈ 𝒪[(D.s.atP p).Fp] ∧ p2 sg.e x ∈ 𝒪[(D.s.atP p).Fp]`. Introduce `x hx`.

Establish `hO : (M p).L.O = (D.s.atP p).O` using `(hA p).2.2.2.1`. Rewrite `hx` using `[← hO]`. Establish `h1` using `IntegralGeneration.fst_mem (g := g) hx`. Establish `h2` using `IntegralGeneration.snd_mem (g := g) hx`. Rewrite `h1`, `h2` using `[hge]`.

Conclude with `⟨h1, h2⟩`. Use `set oL1 := (Matrix.of oL).map (p1 sg.e) with hoL1`. Use `set oL2 := (Matrix.of oL).map (p2 sg.e) with hoL2`. Use `set oB1 := (Matrix.of oB).map (p1 sg.e) with hoB1`. Use `set oB2 := (Matrix.of oB).map (p2 sg.e) with hoB2`.

Establish `hcomp : ∀ (X : PairVal.MatR D) (Xp : MatP D p) (o : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → (D.s.atP p).Ep), (∀ i j, (D.s.atP p).ιE (X i j) - Xp i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (q * a') * o i j) → X.map φ1 = Xp.map (p1 sg.e) + (q * a') • (Matrix.of o).map (p1 sg.e) ∧ …`. Introduce `X Xp o h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h'` using `congrArg (p1 sg.e) (h i j)`.

Rewrite `h'` using `[map_sub, map_mul, fst_proj_algebraMap]`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ1, RingHom.comp_apply]`. Rewrite using `[← h']`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `i j`.

Establish `h'` using `congrArg (p2 sg.e) (h i j)`. Rewrite `h'` using `[map_sub, map_mul, snd_proj_algebraMap]`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ2, RingHom.comp_apply]`. Rewrite using `[← h']`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨hL1, hL2⟩` from `hcomp L Lp oL hLeq`. Take `⟨hB1', hB2'⟩` from `hcomp B Up oB hBeq`. Establish `sS : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, S * (S * X * S) * S = X` using `sconj`. Establish `hΛ1 : Matrix.diagonal cfv * L.map φ1 * Matrix.diagonal cfiv = A1 + (q * a') • (Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv)`. Rewrite using `[hL1, hLp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj1, Matrix.mul_smul, Matrix.smul_mul]`.

Establish `hV1 : Matrix.diagonal cfiv * B.map φ1 * Matrix.diagonal cfv = B1 + (q * a') • (Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv)`. Rewrite using `[hB1', hUp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj2, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hΛ2 : Matrix.diagonal cfv * (S * (B.map φ2).transpose * S) * Matrix.diagonal cfiv = A2 + (q * a') • (Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv)`. Rewrite using `[hB2', hUp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S = Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv by`.

Rewrite using `[show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S = (S * S) * (Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv) * (S * S) by simp only [Matrix.mul_assoc], hSS, Matrix.one_mul, Matrix.mul_one], conj1]`. Establish `hV2 : Matrix.diagonal cfiv * (S * (L.map φ2).transpose * S) * Matrix.diagonal cfv = B2 + (q * a') • (Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv)`. Rewrite using `[hL2, hLp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S = Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv by`. Rewrite using `[show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S = (S * S) * (Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv) * (S * S) by simp only [Matrix.mul_assoc], hSS, Matrix.one_mul, Matrix.mul_one], conj2]`.

Establish `hA1u : IsUnit A1.det` using `by rw [det_lo' hA1lo]; exact isUnit_one`. Establish `hA2u : IsUnit A2.det` using `by rw [det_lo' hA2lo]; exact isUnit_one`. Establish `hB1u : IsUnit B1.det` using `by rw [det_up' hB1up]; exact isUnit_one`. Establish `hB2u : IsUnit B2.det` using `by rw [det_up' hB2up]; exact isUnit_one`. Use `set Δ1 := Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv with hΔ1`.

Use `set Δ2 := Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv with hΔ2`. Use `set E1 := Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv with hE1`. Use `set E2 := Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv with hE2`. Use `set lam := glue sg.e ((A1 + (q * a') • Δ1) * A1⁻¹) ((A2 + (q * a') • Δ2) * A2⁻¹) with hlam`. Use `set mu := glue sg.e (B1⁻¹ * (B1 + (q * a') • E1)) (B2⁻¹ * (B2 + (q * a') • E2)) with hmu`.

Establish `hlamL : (glue sg.e (A1 + (q * a') • Δ1) (A2 + (q * a') • Δ2) : MatP D p) = lam * Λ₀`. Use `mat_eq sg.e ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, hlam, glue_map_fst, glue_map_fst] show A1 + (q * a') • Δ1 = (A1 + (q * a') • Δ1) * A1⁻¹ * A1`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul A1 hA1u, Matrix.mul_one]`. Rewrite using `[Matrix.map_mul, hlam, glue_map_snd, glue_map_snd] show A2 + (q * a') • Δ2 = (A2 + (q * a') • Δ2) * A2⁻¹ * A2`.

Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul A2 hA2u, Matrix.mul_one]`. Establish `hVmu : (glue sg.e (B1 + (q * a') • E1) (B2 + (q * a') • E2) : MatP D p) = V₀ * mu`. Use `mat_eq sg.e ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, hmu, glue_map_fst, glue_map_fst] show B1 + (q * a') • E1 = B1 * (B1⁻¹ * (B1 + (q * a') • E1))`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv B1 hB1u, Matrix.one_mul]`.

Rewrite using `[Matrix.map_mul, hmu, glue_map_snd, glue_map_snd] show B2 + (q * a') • E2 = B2 * (B2⁻¹ * (B2 + (q * a') • E2))`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv B2 hB2u, Matrix.one_mul]`. Establish `h1 : CntLocal.ZZP (M` using `M) δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p = lam * Y * mu := by`. Establish `hZ` using `zz_fact Zd p sg hR g hM' hge hgq u u' w hL hB`. Rewrite `hZ` using `[hM0, hΛ1, hΛ2, hV1, hV2, hlamL, hVmu]`.

Rewrite using `[hZ, hY]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hqO : q ∈ 𝒪[(D.s.atP p).Fp]` using `sg.q.2`. Establish `hR_of : ∀ x : (D.s.atP p).Ep, ∀ t1 t2 : (D.s.atP p).Fp, t1 ∈ 𝒪[(D.s.atP p).Fp] → t2 ∈ 𝒪[(D.s.atP p).Fp] → ∀ d : (D.s.atP p).Fp, d ∈ 𝒪[(D.s.atP p).Fp] → sg.e x = (d + q * t1, d + q * t2) → x ∈ (M p).R`. Introduce `x t1 t2 ht1 ht2 d hd hx`.

Rewrite using `[IntegralGeneration.mem_R_of_split hM' x, hge, hx, hgq]`. Use `⟨Subring.add_mem _ hd (Subring.mul_mem _ hqO ht1), Subring.add_mem _ hd (Subring.mul_mem _ hqO ht2), t1 - t2, Subring.sub_mem _ ht1 ht2, by ring⟩` and prove the remaining obligations. Establish `hδO : ∀ i j : Fin (D.R.rS + 1), (if i = j then (1 : (D.s.atP p).Fp) else 0) ∈ 𝒪[(D.s.atP p).Fp]`. Introduce `i j`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Establish `hoL1 : ∀ i j, oL1 i j ∈ 𝒪[(D.s.atP p).Fp]` using `fun i j => (hOc _ (hoL i j)).1`. Establish `hoL2 : ∀ i j, oL2 i j ∈ 𝒪[(D.s.atP p).Fp]` using `fun i j => (hOc _ (hoL i j)).2`. Establish `hoB1 : ∀ i j, oB1 i j ∈ 𝒪[(D.s.atP p).Fp]` using `fun i j => (hOc _ (hoB i j)).1`.

Establish `hoB2 : ∀ i j, oB2 i j ∈ 𝒪[(D.s.atP p).Fp]` using `fun i j => (hOc _ (hoB i j)).2`. Establish `hsO : ∀ a, s a ∈ 𝒪[(D.s.atP p).Fp]` using `fun a => sgn_mem_O p _`. Establish `hSe : ∀ (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) (i k : Fin (D.R.rS + 1)), (S * X.transpose * S) i k = s i * X k i * s k`. Introduce `X i k`. Rewrite using `[hSd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]`.

Establish `hT1 : ∀ i j, a' * (Δ1 * A1⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp]`. Introduce `i j`. Rewrite using `[hΔ1, conj_mul_apply, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `hz` using `hc' (Sum.inl (0, i, k, j))`.

Simplify using `only [Sum.elim_inl, if_true] at hz`. Rewrite using `[show a' * (cfv i * oL1 i k * cfiv k * A1⁻¹ k j) = oL1 i k * (a' * (cfv i * cfiv k * A1⁻¹ k j)) by ring]`. Conclude with `Subring.mul_mem _ (hoL1 i k) hz`. Establish `hT2 : ∀ i j, a' * (Δ2 * A2⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp]`. Introduce `i j`.

Rewrite using `[hΔ2, conj_mul_apply, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `hz` using `hc' (Sum.inl (1, i, k, j))`. Simplify using `only [Sum.elim_inl, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz`. Rewrite using `[hSe, show a' * (cfv i * (s i * oB2 k i * s k) * cfiv k * A2⁻¹ k j) = (s i * oB2 k i * s k) * (a' * (cfv i * cfiv k * A2⁻¹ k j)) by ring]`.

Conclude with `Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO i) (hoB2 k i)) (hsO k)) hz`. Establish `hU1 : ∀ i j, a' * (B1⁻¹ * E1) i j ∈ 𝒪[(D.s.atP p).Fp]`. Introduce `i j`. Rewrite using `[hE1, mul_conj_apply, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Establish `hz` using `hc' (Sum.inr (0, i, k, j))`. Simplify using `only [Sum.elim_inr, if_true] at hz`. Rewrite using `[show a' * (B1⁻¹ i k * (cfiv k * oB1 k j * cfv j)) = oB1 k j * (a' * (B1⁻¹ i k * cfiv k * cfv j)) by ring]`. Conclude with `Subring.mul_mem _ (hoB1 k j) hz`. Establish `hU2 : ∀ i j, a' * (B2⁻¹ * E2) i j ∈ 𝒪[(D.s.atP p).Fp]`.

Introduce `i j`. Rewrite using `[hE2, mul_conj_apply, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `hz` using `hc' (Sum.inr (1, i, k, j))`. Simplify using `only [Sum.elim_inr, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz`.

Rewrite using `[hSe, show a' * (B2⁻¹ i k * (cfiv k * (s k * oL2 j k * s j) * cfv j)) = (s k * oL2 j k * s j) * (a' * (B2⁻¹ i k * cfiv k * cfv j)) by ring]`. Conclude with `Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO k) (hoL2 j k)) (hsO j)) hz`. Establish `hlo1 : IsLo (A1 + (q * a') • Δ1)`. Rewrite using `[← hΛ1]`. Conclude with `isLo_conj (isLo_map φ1 hL) _ _ hcc`.

Establish `hlo2 : IsLo (A2 + (q * a') • Δ2)`. Rewrite using `[← hΛ2]`. Conclude with `isLo_conj (isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc`. Establish `hup1 : IsUp (B1 + (q * a') • E1)`. Rewrite using `[← hV1]`.

Conclude with `isUp_conj (isUp_map φ1 hB) _ _ hcc'`. Establish `hup2 : IsUp (B2 + (q * a') • E2)`. Rewrite using `[← hV2]`. Conclude with `isUp_conj (isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc'`. Establish `hlamI : TieN.IntLow (M p) lam`.

Establish `hlo : IsLo lam` using `isLo_glue sg.e (isLo_mul hlo1 (isLo_inv hA1lo)) (isLo_mul hlo2 (isLo_inv hA2lo))`. Use `⟨hlo.1, hlo.2, fun i j => ?_⟩` and prove the remaining obligations. Use `hR_of (lam i j) (a' * (Δ1 * A1⁻¹) i j) (a' * (Δ2 * A2⁻¹) i j) (hT1 i j) (hT2 i j) _ (hδO i j) ?_` and prove the remaining obligations. Rewrite using `[hlam, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, lam_form hA1lo, lam_form hA2lo, one_smul_apply, one_smul_apply]`. Put the polynomial expressions in normal form.

Establish `hmuI : TieN.IntUp (M p) mu`. Establish `hup : IsUp mu` using `isUp_glue sg.e (isUp_mul (isUp_inv hB1up) hup1) (isUp_mul (isUp_inv hB2up) hup2)`. Use `⟨hup.1, fun i j hij => hup.2 j i hij, fun i j => ?_⟩` and prove the remaining obligations. Use `hR_of (mu i j) (a' * (B1⁻¹ * E1) i j) (a' * (B2⁻¹ * E2) i j) (hU1 i j) (hU2 i j) _ (hδO i j) ?_` and prove the remaining obligations. Rewrite using `[hmu, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, mu_form hB1up, mu_form hB2up, one_smul_apply, one_smul_apply]`.

Put the polynomial expressions in normal form. Establish `hlamu : IsUnit lam.det` using `by rw [det_lo' ⟨hlamI.1, hlamI.2.1⟩]; exact isUnit_one`. Establish `hmuu : IsUnit mu.det` using `by rw [det_up' ⟨hmuI.1, fun a b hab => hmuI.2.1 b a hab⟩]; exact isUnit_one`. Establish `h2 : Y = lam⁻¹ * (lam * Y * mu) * mu⁻¹`. Rewrite using `[show lam⁻¹ * (lam * Y * mu) * mu⁻¹ = (lam⁻¹ * lam) * Y * (mu * mu⁻¹) by simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul lam hlamu, Matrix.mul_nonsing_inv mu hmuu, Matrix.one_mul, Matrix.mul_one]`.

Unfold `tupZ`. Conclude with `kkOrb_eq_of hlamI hmuI (intLow_inv hlamI) (intUp_inv hmuI) h1 (by rw [h1]; exact h2)`.
-/
theorem locReal_typed (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (hMp : (M p).split ≠ none) :
    LocRealAt M δ u u' p := by
  intro w O hO
  obtain ⟨Y, -, ⟨w₀, -, ⟨ξ, η⟩, hYeq⟩, rfl⟩ := hO
  haveI := (D.s.atP p).lf
  have hAg := (hA p).2.2.2.2.2
  rcases hM' : (M p).split with _ | g
  · exact absurd hM' hMp
  rcases hR : (D.s.atP p).split with _ | sg
  · simp only [hM', hR] at hAg
  simp only [hM', hR] at hAg
  obtain ⟨hge, hgq⟩ := hAg
  set Zd : LocDat D := ⟨δ, M, hA⟩
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  set s : Fin (D.R.rS + 1) → (D.s.atP p).Fp := fun a => (-1) ^ (D.R.rS - a.val) with hsdef
  have hSd : S = Matrix.diagonal s := rfl
  have hs : ∀ a, s a * s a = 1 := fun a => sgn_sq' D.R.rS a
  have hSS : S * S = 1 := sg_sq _
  set cfv := cf Zd p with hcfv
  set cfiv := cfi Zd p with hcfiv
  have hcc : ∀ a, cfv a * cfiv a = 1 := cf_cfi Zd p
  have hcc' : ∀ a, cfiv a * cfv a = 1 := cfi_cf Zd p
  have hdd : Matrix.diagonal cfv * Matrix.diagonal cfiv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hcc]
  have hdd' : Matrix.diagonal cfiv * Matrix.diagonal cfv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hcc']
  have conj1 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv = X := by
    intro X
    rw [show Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv =
      (Matrix.diagonal cfv * Matrix.diagonal cfiv) * X * (Matrix.diagonal cfv * Matrix.diagonal cfiv) by
        simp only [Matrix.mul_assoc], hdd, Matrix.one_mul, Matrix.mul_one]
  have conj2 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv = X := by
    intro X
    rw [show Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv =
      (Matrix.diagonal cfiv * Matrix.diagonal cfv) * X * (Matrix.diagonal cfiv * Matrix.diagonal cfv) by
        simp only [Matrix.mul_assoc], hdd', Matrix.one_mul, Matrix.mul_one]
  have hSt : S.transpose = S := Matrix.diagonal_transpose _
  have sconj : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, S * (S * X * S) * S = X := by
    intro X
    rw [show S * (S * X * S) * S = (S * S) * X * (S * S) by simp only [Matrix.mul_assoc], hSS, Matrix.one_mul,
      Matrix.mul_one]

  obtain ⟨Gl, Gu, hGl, hGu, hM0⟩ := target_fact Zd p sg hR g hM' hge hgq u u' w
  have hGlu : IsUnit Gl.det := by rw [det_lo' hGl]; exact isUnit_one
  have hGuu : IsUnit Gu.det := by rw [det_up' hGu]; exact isUnit_one
  set Λ₀ := Loc.uLow ξ * Gl⁻¹ with hΛ₀
  set V₀ := Gu⁻¹ * Loc.uUp w₀ η with hV₀
  have hΛ₀lo : IsLo Λ₀ := isLo_mul (isLo_uLow ξ) (isLo_inv hGl)
  have hV₀up : IsUp V₀ := isUp_mul (isUp_inv hGu) (isUp_uUp w₀ η)
  have hY : Y = Λ₀ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * V₀ := by
    rw [hYeq, hΛ₀, hV₀]
    rw [show Loc.uLow ξ * Gl⁻¹ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * (Gu⁻¹ * Loc.uUp w₀ η) =
      Loc.uLow ξ * (Gl⁻¹ * Gl) * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * (Gu * Gu⁻¹) * Loc.uUp w₀ η by
        simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul Gl hGlu, Matrix.mul_nonsing_inv Gu hGuu, Matrix.mul_one,
      Matrix.mul_one]
  set A1 := Λ₀.map (p1 sg.e) with hA1
  set A2 := Λ₀.map (p2 sg.e) with hA2
  set B1 := V₀.map (p1 sg.e) with hB1
  set B2 := V₀.map (p2 sg.e) with hB2
  have hA1lo : IsLo A1 := isLo_map _ hΛ₀lo
  have hA2lo : IsLo A2 := isLo_map _ hΛ₀lo
  have hB1up : IsUp B1 := isUp_map _ hV₀up
  have hB2up : IsUp B2 := isUp_map _ hV₀up
  have hΛ₀glue : Λ₀ = glue sg.e A1 A2 := mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])
  have hV₀glue : V₀ = glue sg.e B1 B2 := mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])

  set Lp := glue sg.e (Matrix.diagonal cfiv * A1 * Matrix.diagonal cfv)
    (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S).transpose with hLp
  set Up := glue sg.e (Matrix.diagonal cfv * B1 * Matrix.diagonal cfiv)
    (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S).transpose with hUp
  have hLplo : IsLo Lp := isLo_glue sg.e (isLo_conj hA1lo cfiv cfv hcc')
    (isLo_transpose (isUp_sconj s cfv cfiv hSd hs hcc hB2up))
  have hUpup : IsUp Up := isUp_glue sg.e (isUp_conj hB1up cfv cfiv hcc)
    (isUp_transpose (isLo_sconj s cfiv cfv hSd hs hcc' hA2lo))

  obtain ⟨c', hc'0, hc'⟩ := clear_Fp p
    (ι := (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕
      (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (Sum.elim (fun t => cfv t.2.1 * cfiv t.2.2.1 * (if t.1 = 0 then A1⁻¹ else A2⁻¹) t.2.2.1 t.2.2.2)
      (fun t => (if t.1 = 0 then B1⁻¹ else B2⁻¹) t.2.1 t.2.2.1 * cfiv t.2.2.1 * cfv t.2.2.2))
  haveI := (D.s.atP p).ellPrime
  set ℓ : 𝓞 D.host.F := ((Loc.resChar p : ℕ) : 𝓞 D.host.F) with hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rw [hℓ, Ne, Nat.cast_eq_zero]; exact (Fact.out : (Loc.resChar p).Prime).ne_zero
  have hℓq : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F ℓ) = (sg.q : (D.s.atP p).Fp) := by
    rw [hℓ, map_natCast, map_natCast, sg.q_eq]
  refine ⟨Lp, Up, ℓ * c', mul_ne_zero hℓ0 hc'0, hLplo, hUpup, ?_⟩
  intro L B hL hB hLc hBc
  choose oL hoL hLeq using hLc
  choose oB hoB hBeq using hBc
  set a' := (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c') with ha'
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hq
  have ha : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F (ℓ * c')) = q * a' := by
    rw [map_mul, map_mul, hℓq]
  simp only [ha] at hLeq hBeq
  have hOc : ∀ x ∈ (D.s.atP p).O, p1 sg.e x ∈ 𝒪[(D.s.atP p).Fp] ∧ p2 sg.e x ∈ 𝒪[(D.s.atP p).Fp] := by
    intro x hx
    have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
    rw [← hO] at hx
    have h1 := IntegralGeneration.fst_mem (g := g) hx
    have h2 := IntegralGeneration.snd_mem (g := g) hx
    rw [hge] at h1 h2
    exact ⟨h1, h2⟩
  set oL1 := (Matrix.of oL).map (p1 sg.e) with hoL1
  set oL2 := (Matrix.of oL).map (p2 sg.e) with hoL2
  set oB1 := (Matrix.of oB).map (p1 sg.e) with hoB1
  set oB2 := (Matrix.of oB).map (p2 sg.e) with hoB2
  have hcomp : ∀ (X : PairVal.MatR D) (Xp : MatP D p) (o : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      (∀ i j, (D.s.atP p).ιE (X i j) - Xp i j =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (q * a') * o i j) →
      X.map φ1 = Xp.map (p1 sg.e) + (q * a') • (Matrix.of o).map (p1 sg.e) ∧
      X.map φ2 = Xp.map (p2 sg.e) + (q * a') • (Matrix.of o).map (p2 sg.e) := by
    intro X Xp o h
    refine ⟨?_, ?_⟩
    · ext i j
      have h' := congrArg (p1 sg.e) (h i j)
      rw [map_sub, map_mul, fst_proj_algebraMap] at h'
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ1,
        RingHom.comp_apply]
      rw [← h']; ring
    · ext i j
      have h' := congrArg (p2 sg.e) (h i j)
      rw [map_sub, map_mul, snd_proj_algebraMap] at h'
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ2,
        RingHom.comp_apply]
      rw [← h']; ring
  obtain ⟨hL1, hL2⟩ := hcomp L Lp oL hLeq
  obtain ⟨hB1', hB2'⟩ := hcomp B Up oB hBeq
  have sS : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      S * (S * X * S) * S = X := sconj
  have hΛ1 : Matrix.diagonal cfv * L.map φ1 * Matrix.diagonal cfiv =
      A1 + (q * a') • (Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv) := by
    rw [hL1, hLp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj1, Matrix.mul_smul, Matrix.smul_mul]
  have hV1 : Matrix.diagonal cfiv * B.map φ1 * Matrix.diagonal cfv =
      B1 + (q * a') • (Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv) := by
    rw [hB1', hUp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj2, Matrix.mul_smul, Matrix.smul_mul]
  have hΛ2 : Matrix.diagonal cfv * (S * (B.map φ2).transpose * S) * Matrix.diagonal cfiv =
      A2 + (q * a') • (Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv) := by
    rw [hB2', hUp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S =
      Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv by
        rw [show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S =
          (S * S) * (Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv) * (S * S) by simp only [Matrix.mul_assoc],
          hSS, Matrix.one_mul, Matrix.mul_one], conj1]
  have hV2 : Matrix.diagonal cfiv * (S * (L.map φ2).transpose * S) * Matrix.diagonal cfv =
      B2 + (q * a') • (Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv) := by
    rw [hL2, hLp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S =
      Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv by
        rw [show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S =
          (S * S) * (Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv) * (S * S) by simp only [Matrix.mul_assoc],
          hSS, Matrix.one_mul, Matrix.mul_one], conj2]
  have hA1u : IsUnit A1.det := by rw [det_lo' hA1lo]; exact isUnit_one
  have hA2u : IsUnit A2.det := by rw [det_lo' hA2lo]; exact isUnit_one
  have hB1u : IsUnit B1.det := by rw [det_up' hB1up]; exact isUnit_one
  have hB2u : IsUnit B2.det := by rw [det_up' hB2up]; exact isUnit_one
  set Δ1 := Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv with hΔ1
  set Δ2 := Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv with hΔ2
  set E1 := Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv with hE1
  set E2 := Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv with hE2
  set lam := glue sg.e ((A1 + (q * a') • Δ1) * A1⁻¹) ((A2 + (q * a') • Δ2) * A2⁻¹) with hlam
  set mu := glue sg.e (B1⁻¹ * (B1 + (q * a') • E1)) (B2⁻¹ * (B2 + (q * a') • E2)) with hmu
  have hlamL : (glue sg.e (A1 + (q * a') • Δ1) (A2 + (q * a') • Δ2) : MatP D p) = lam * Λ₀ := by
    refine mat_eq sg.e ?_ ?_
    · rw [Matrix.map_mul, hlam, glue_map_fst, glue_map_fst]
      show A1 + (q * a') • Δ1 = (A1 + (q * a') • Δ1) * A1⁻¹ * A1
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A1 hA1u, Matrix.mul_one]
    · rw [Matrix.map_mul, hlam, glue_map_snd, glue_map_snd]
      show A2 + (q * a') • Δ2 = (A2 + (q * a') • Δ2) * A2⁻¹ * A2
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A2 hA2u, Matrix.mul_one]
  have hVmu : (glue sg.e (B1 + (q * a') • E1) (B2 + (q * a') • E2) : MatP D p) = V₀ * mu := by
    refine mat_eq sg.e ?_ ?_
    · rw [Matrix.map_mul, hmu, glue_map_fst, glue_map_fst]
      show B1 + (q * a') • E1 = B1 * (B1⁻¹ * (B1 + (q * a') • E1))
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B1 hB1u, Matrix.one_mul]
    · rw [Matrix.map_mul, hmu, glue_map_snd, glue_map_snd]
      show B2 + (q * a') • E2 = B2 * (B2⁻¹ * (B2 + (q * a') • E2))
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B2 hB2u, Matrix.one_mul]
  have h1 : CntLocal.ZZP (M := M) δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      lam * Y * mu := by
    have hZ := zz_fact Zd p sg hR g hM' hge hgq u u' w hL hB
    rw [hM0, hΛ1, hΛ2, hV1, hV2, hlamL, hVmu] at hZ
    rw [hZ, hY]
    simp only [Matrix.mul_assoc]

  have hqO : q ∈ 𝒪[(D.s.atP p).Fp] := sg.q.2
  have hR_of : ∀ x : (D.s.atP p).Ep, ∀ t1 t2 : (D.s.atP p).Fp, t1 ∈ 𝒪[(D.s.atP p).Fp] → t2 ∈ 𝒪[(D.s.atP p).Fp] →
      ∀ d : (D.s.atP p).Fp, d ∈ 𝒪[(D.s.atP p).Fp] → sg.e x = (d + q * t1, d + q * t2) → x ∈ (M p).R := by
    intro x t1 t2 ht1 ht2 d hd hx
    rw [IntegralGeneration.mem_R_of_split hM' x, hge, hx, hgq]
    refine ⟨Subring.add_mem _ hd (Subring.mul_mem _ hqO ht1), Subring.add_mem _ hd (Subring.mul_mem _ hqO ht2),
      t1 - t2, Subring.sub_mem _ ht1 ht2, by ring⟩
  have hδO : ∀ i j : Fin (D.R.rS + 1), (if i = j then (1 : (D.s.atP p).Fp) else 0) ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j; split_ifs; exact Subring.one_mem _; exact Subring.zero_mem _
  have hoL1 : ∀ i j, oL1 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoL i j)).1
  have hoL2 : ∀ i j, oL2 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoL i j)).2
  have hoB1 : ∀ i j, oB1 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoB i j)).1
  have hoB2 : ∀ i j, oB2 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoB i j)).2
  have hsO : ∀ a, s a ∈ 𝒪[(D.s.atP p).Fp] := fun a => sgn_mem_O p _
  have hSe : ∀ (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) (i k : Fin (D.R.rS + 1)),
      (S * X.transpose * S) i k = s i * X k i * s k := by
    intro X i k
    rw [hSd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hT1 : ∀ i j, a' * (Δ1 * A1⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hΔ1, conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inl (0, i, k, j))
    simp only [Sum.elim_inl, if_true] at hz
    rw [show a' * (cfv i * oL1 i k * cfiv k * A1⁻¹ k j) = oL1 i k * (a' * (cfv i * cfiv k * A1⁻¹ k j)) by ring]
    exact Subring.mul_mem _ (hoL1 i k) hz
  have hT2 : ∀ i j, a' * (Δ2 * A2⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hΔ2, conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inl (1, i, k, j))
    simp only [Sum.elim_inl, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz
    rw [hSe, show a' * (cfv i * (s i * oB2 k i * s k) * cfiv k * A2⁻¹ k j) =
      (s i * oB2 k i * s k) * (a' * (cfv i * cfiv k * A2⁻¹ k j)) by ring]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO i) (hoB2 k i)) (hsO k)) hz
  have hU1 : ∀ i j, a' * (B1⁻¹ * E1) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hE1, mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inr (0, i, k, j))
    simp only [Sum.elim_inr, if_true] at hz
    rw [show a' * (B1⁻¹ i k * (cfiv k * oB1 k j * cfv j)) = oB1 k j * (a' * (B1⁻¹ i k * cfiv k * cfv j)) by ring]
    exact Subring.mul_mem _ (hoB1 k j) hz
  have hU2 : ∀ i j, a' * (B2⁻¹ * E2) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hE2, mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inr (1, i, k, j))
    simp only [Sum.elim_inr, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz
    rw [hSe, show a' * (B2⁻¹ i k * (cfiv k * (s k * oL2 j k * s j) * cfv j)) =
      (s k * oL2 j k * s j) * (a' * (B2⁻¹ i k * cfiv k * cfv j)) by ring]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO k) (hoL2 j k)) (hsO j)) hz
  have hlo1 : IsLo (A1 + (q * a') • Δ1) := by
    rw [← hΛ1]; exact isLo_conj (isLo_map φ1 hL) _ _ hcc
  have hlo2 : IsLo (A2 + (q * a') • Δ2) := by
    rw [← hΛ2]
    exact isLo_conj (isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc
  have hup1 : IsUp (B1 + (q * a') • E1) := by
    rw [← hV1]; exact isUp_conj (isUp_map φ1 hB) _ _ hcc'
  have hup2 : IsUp (B2 + (q * a') • E2) := by
    rw [← hV2]
    exact isUp_conj (isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc'
  have hlamI : TieN.IntLow (M p) lam := by
    have hlo : IsLo lam := isLo_glue sg.e (isLo_mul hlo1 (isLo_inv hA1lo)) (isLo_mul hlo2 (isLo_inv hA2lo))
    refine ⟨hlo.1, hlo.2, fun i j => ?_⟩
    refine hR_of (lam i j) (a' * (Δ1 * A1⁻¹) i j) (a' * (Δ2 * A2⁻¹) i j) (hT1 i j) (hT2 i j) _ (hδO i j) ?_
    rw [hlam, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, lam_form hA1lo, lam_form hA2lo, one_smul_apply,
      one_smul_apply]
    ring_nf
  have hmuI : TieN.IntUp (M p) mu := by
    have hup : IsUp mu := isUp_glue sg.e (isUp_mul (isUp_inv hB1up) hup1) (isUp_mul (isUp_inv hB2up) hup2)
    refine ⟨hup.1, fun i j hij => hup.2 j i hij, fun i j => ?_⟩
    refine hR_of (mu i j) (a' * (B1⁻¹ * E1) i j) (a' * (B2⁻¹ * E2) i j) (hU1 i j) (hU2 i j) _ (hδO i j) ?_
    rw [hmu, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, mu_form hB1up, mu_form hB2up, one_smul_apply,
      one_smul_apply]
    ring_nf
  have hlamu : IsUnit lam.det := by rw [det_lo' ⟨hlamI.1, hlamI.2.1⟩]; exact isUnit_one
  have hmuu : IsUnit mu.det := by rw [det_up' ⟨hmuI.1, fun a b hab => hmuI.2.1 b a hab⟩]; exact isUnit_one
  have h2 : Y = lam⁻¹ * (lam * Y * mu) * mu⁻¹ := by
    rw [show lam⁻¹ * (lam * Y * mu) * mu⁻¹ = (lam⁻¹ * lam) * Y * (mu * mu⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul lam hlamu, Matrix.mul_nonsing_inv mu hmuu, Matrix.one_mul, Matrix.mul_one]
  unfold tupZ
  exact kkOrb_eq_of hlamI hmuI (intLow_inv hlamI) (intUp_inv hmuI) h1 (by rw [h1]; exact h2)

/- English proof (translation)
The claim follows from `exist_of u u' hA (fun p hp => locReal_typed hA u u' p hp)`.
-/
theorem exist_holds (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) : Exist M δ u u' :=
  exist_of u u' hA (fun p hp => locReal_typed hA u u' p hp)

end Typed

end Formalism.L2.SG.Pf.PCountEx
