import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeStabP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTorusHyperbolicPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.UnipComm
open Matrix GlobalTheory.LeviTorusExists

section Gen
variable {R : Type} [CommRing R] {d d₁ : ℕ} {c : R →+* R} {j : Matrix (Fin d) (Fin d) R}

def tv (c : R →+* R) (j : Matrix (Fin d) (Fin d) R) (x : Fin d → R) (b : R) : Matrix (Fin d) (Fin d) R :=
  1 - b • vecMulVec x (j *ᵥ fun i => c (x i))

/- English proof (translation)
Rewrite using `[tv, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec_eq, smul_smul, sub_eq_add_neg, neg_smul, sesq, mul_comm]`.
-/
theorem tv_mulVec (x : Fin d → R) (b : R) (v : Fin d → R) :
    tv c j x b *ᵥ v = v + (-(sesq c j v x * b)) • x := by
  rw [tv, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec_eq, smul_smul, sub_eq_add_neg, neg_smul, sesq, mul_comm]

/- English proof (translation)
Use `Matrix.ext_of_mulVec_single fun k => ?_` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec]`. Generalize the expression as in `(Pi.single k 1 : Fin d → R) = v`. Rewrite using `[tv_mulVec, tv_mulVec, tv_mulVec, sesq_add_left, sesq_smul_left, hxx]`. Use extensionality with `i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tv_mul {x : Fin d → R} (hxx : sesq c j x x = 0) (b b' : R) : tv c j x b * tv c j x b' = tv c j x (b + b') := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← mulVec_mulVec]
  generalize (Pi.single k 1 : Fin d → R) = v
  rw [tv_mulVec, tv_mulVec, tv_mulVec, sesq_add_left, sesq_smul_left, hxx]
  ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Establish `hxw : sesq c j x w = -c (sesq c j w x)` using `sesq_skew hcc hj _ _`. Rewrite using `[tv_mulVec, tv_mulVec]`. Simplify using `only [sesq_add_left, sesq_add_right, sesq_smul_left, sesq_smul_right, hxx, hxw, map_mul, map_neg, hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sesq_tv (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k) {x : Fin d → R} (hxx : sesq c j x x = 0)
    {b : R} (hb : c b = b) (v w : Fin d → R) : sesq c j (tv c j x b *ᵥ v) (tv c j x b *ᵥ w) = sesq c j v w := by
  have hxw : sesq c j x w = -c (sesq c j w x) := sesq_skew hcc hj _ _
  rw [tv_mulVec, tv_mulVec]
  simp only [sesq_add_left, sesq_add_right, sesq_smul_left, sesq_smul_right, hxx, hxw, map_mul, map_neg, hb]
  ring

/- English proof (translation)
Use extensionality with `i k`. Establish `h` using `sesq_tv hcc hj hxx hb (Pi.single i 1) (Pi.single k 1)`. Establish `hs : ∀ (M : Matrix (Fin d) (Fin d) R), (Pi.single i (1 : R)) ⬝ᵥ M *ᵥ (fun l => c ((Pi.single k (1 : R) : Fin d → R) l)) = M i k`. Introduce `M`. Establish `: (fun l => c ((Pi.single k (1 : R) : Fin d → R) l)) = Pi.single k 1`.

Use extensionality with `l`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`.

Rewrite using `[this]`. Simplify using `[mulVec_single_one]`. Rewrite `h` using `[sesq_mulVec, hs, sesq]`. Rewrite using `[h, hs j]`.
-/
theorem tv_unitary (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k) {x : Fin d → R} (hxx : sesq c j x x = 0)
    {b : R} (hb : c b = b) : (tv c j x b)ᵀ * j * (tv c j x b).map c = j := by
  ext i k
  have h := sesq_tv hcc hj hxx hb (Pi.single i 1) (Pi.single k 1)
  have hs : ∀ (M : Matrix (Fin d) (Fin d) R), (Pi.single i (1 : R)) ⬝ᵥ M *ᵥ (fun l => c ((Pi.single k (1 : R) : Fin d → R) l)) = M i k := by
    intro M
    have : (fun l => c ((Pi.single k (1 : R) : Fin d → R) l)) = Pi.single k 1 := by
      ext l; by_cases hl : l = k
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [this]; simp [mulVec_single_one]
  rw [sesq_mulVec, hs, sesq] at h
  rw [h, hs j]

/- English proof (translation)
Establish `: (fun i => c ((ι *ᵥ z') i)) = ι.map c *ᵥ fun i => c (z' i)`. Use extensionality with `i`. Conclude with `RingHom.map_mulVec c ι z' i`. Rewrite using `[sesq, this, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (ι *ᵥ z), dotProduct_mulVec, dotProduct_comm]`.
-/
theorem sesq_mulVec_rect (ι : Matrix (Fin d) (Fin d₁) R) (z z' : Fin d₁ → R) :
    sesq c j (ι *ᵥ z) (ι *ᵥ z') = z ⬝ᵥ (ιᵀ * j * ι.map c) *ᵥ fun i => c (z' i) := by
  have : (fun i => c ((ι *ᵥ z') i)) = ι.map c *ᵥ fun i => c (z' i) := by
    ext i; exact RingHom.map_mulVec c ι z' i
  rw [sesq, this, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (ι *ᵥ z), dotProduct_mulVec,
    dotProduct_comm]

/- English proof (translation)
Establish `h0 : z ᵥ* j₁ = 0`. Use extensionality with `k`. Use `h (Pi.single k 1)` as an intermediate fact. Establish `hs : (fun l => c ((Pi.single k (1 : R) : Fin d₁ → R) l)) = Pi.single k 1`. Use extensionality with `l`.

Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`. Rewrite `this` using `[sesq_mulVec_rect, hgram, hs, mulVec_single_one, dotProduct_comm]`.

Rewrite using `[Pi.zero_apply, ← this, vecMul, dotProduct_comm]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nondeg {ι : Matrix (Fin d) (Fin d₁) R} {j₁ : Matrix (Fin d₁) (Fin d₁) R} (hgram : ιᵀ * j * ι.map c = j₁)
    (hdet : IsUnit j₁.det) (z : Fin d₁ → R) (h : ∀ z', sesq c j (ι *ᵥ z) (ι *ᵥ z') = 0) : z = 0 := by
  have h0 : z ᵥ* j₁ = 0 := by
    ext k
    have := h (Pi.single k 1)
    have hs : (fun l => c ((Pi.single k (1 : R) : Fin d₁ → R) l)) = Pi.single k 1 := by
      ext l; by_cases hl : l = k
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [sesq_mulVec_rect, hgram, hs, mulVec_single_one, dotProduct_comm] at this
    rw [Pi.zero_apply, ← this, vecMul, dotProduct_comm]
    rfl
  calc z = z ᵥ* (j₁ * j₁⁻¹) := by rw [mul_nonsing_inv _ hdet, vecMul_one]
    _ = 0 := by rw [← vecMul_vecMul, h0, zero_vecMul]

/- English proof (translation)
Simplify using `[sesq, sub_dotProduct]`.
-/
theorem sesq_sub_left' (u u' w : Fin d → R) : sesq c j (u - u') w = sesq c j u w - sesq c j u' w := by
  simp [sesq, sub_dotProduct]

end Gen

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `A' : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]`. Establish `h2 : (A'ᵀ * M * A'.map star).det ≠ 0`. Rewrite using `[h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_neg]`.

Introduce `h0`. Apply `h2` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_of_hasSig' {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

/- English proof (translation)
Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Use `det_ne_of_hasSig' (h w)` as an intermediate fact. Introduce `h0`. Apply `this` to reduce the goal to its premises. Establish `e` using `RingHom.map_det (B.emb w).1 J`.

Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[Matrix.det_smul, ← e, h0, map_zero, mul_zero]`.
-/
theorem det_ne_of_skew (B : Base F E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig' (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

/- English proof (translation)
Establish `hinv : ∀ g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', c g * c g⁻¹ = 1` using `fun g hg => by`. Rewrite using `[← hc g hg g⁻¹ (inv_mem hg), mul_inv_cancel, hc1]`. Rewrite using `[hc _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb), hc _ (mul_mem ha hb) _ (inv_mem ha), hc _ ha _ hb]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem char_comm {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} (c : UA σ W.J → ℂ)
    (hc : ∀ g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∀ h ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', c (g * h) = c g * c h) (hc1 : c 1 = 1)
    {a b : UA σ W.J} (ha : a ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H') (hb : b ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H') :
    c (a * b * a⁻¹ * b⁻¹) = 1 := by
  have hinv : ∀ g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', c g * c g⁻¹ = 1 := fun g hg => by
    rw [← hc g hg g⁻¹ (inv_mem hg), mul_inv_cancel, hc1]
  rw [hc _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb), hc _ (mul_mem ha hb) _ (inv_mem ha), hc _ ha _ hb]
  calc c a * c b * c a⁻¹ * c b⁻¹ = (c a * c a⁻¹) * (c b * c b⁻¹) := by ring
    _ = 1 := by rw [hinv a ha, hinv b hb, one_mul]

/- English proof (translation)
Rewrite using `[sesq_mulVec]`. Establish `hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J` using `g.2`. Conclude with `congrArg (fun M => u ⬝ᵥ M *ᵥ fun i => (cA σ) (v i)) hg`.
-/
theorem sesq_UA {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (g : UA σ J) (u v : Fin d → AE F E) :
    sesq (cA σ).toRingHom (incM F J) (mat g *ᵥ u) (mat g *ᵥ v) = sesq (cA σ).toRingHom (incM F J) u v := by
  rw [sesq_mulVec]
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  exact congrArg (fun M => u ⬝ᵥ M *ᵥ fun i => (cA σ) (v i)) hg

end Main

section Thm
open Matrix GlobalTheory.LeviTorusExists

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d W d₁ W₁ H' i₀ i₁ r' s' r₁ s₁ hB hW hW₁ hH c hc hc1`. Establish `hcm : IsCMExt F E σ` using `hB.cm`. Use `set cc : AE F E →+* AE F E := (cA σ).toRingHom with hcc_def`. Establish `hcc : ∀ z, cc (cc z) = z` using `fun z => cA_cA hcm z`. Establish `hj : ∀ i k, cc (incM F W.J k i) = -incM F W.J i k`.

Introduce `i k`. Simplify using `[cc, incM, cA_inclR, hW.skew i k]`. Establish `hxx : sesq cc (incM F W.J) (incV F H'.x) (incV F H'.x) = 0` using `by rw [sesq_incV, hH.xx, map_zero]`. Establish `hyy : sesq cc (incM F W.J) (incV F H'.y) (incV F H'.y) = 0` using `by rw [sesq_incV, hH.yy, map_zero]`. Establish `hxy : sesq cc (incM F W.J) (incV F H'.x) (incV F H'.y) = 1` using `by rw [sesq_incV, hH.xy, map_one]`.

Establish `hyx : sesq cc (incM F W.J) (incV F H'.y) (incV F H'.x) = -1` using `by rw [sesq_skew hcc hj, hxy, map_one]`. Establish `hT : ∀ (z : Fin d₁ → AE F E) (u : Fin d → AE F E), (incM F H'.ι *ᵥ z) ⬝ᵥ u = z ⬝ᵥ ((incM F H'.ι)ᵀ *ᵥ u)`. Introduce `z u`. Rewrite using `[mulVec_transpose, dotProduct_comm z, dotProduct_comm (incM F H'.ι *ᵥ z), dotProduct_mulVec]`. Establish `hcol : ∀ k, incM F H'.ι *ᵥ Pi.single k 1 = incV F (H'.ι *ᵥ Pi.single k 1)`.

Introduce `k`. Use extensionality with `i`. Simplify using `[mulVec_single_one, incV, incM]`. Establish `horth : ∀ z, sesq cc (incM F W.J) (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 ∧ sesq cc (incM F W.J) (incM F H'.ι *ᵥ z) (incV F H'.y) = 0`. Introduce `z`.

Establish `key : ∀ w : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) w = 0) → sesq cc (incM F W.J) (incM F H'.ι *ᵥ z) (incV F w) = 0`. Introduce `w hw`. Rewrite using `[sesq, hT]`. Establish `: (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun i => cc (incV F w i)) = 0`. Use extensionality with `k`.

Establish `h2 : sesq cc (incM F W.J) (incM F H'.ι *ᵥ Pi.single k 1) (incV F w) = 0`. Rewrite using `[hcol, sesq_incV, hw, map_zero]`. Rewrite `h2` using `[sesq, hT]`. Simplify using `using h2`. Rewrite using `[this, dotProduct_zero]`.

Conclude with `⟨key _ fun u => (hH.orth u).1, key _ fun u => (hH.orth u).2⟩`. Establish `hxι : ∀ z, sesq cc (incM F W.J) (incV F H'.x) (incM F H'.ι *ᵥ z) = 0`. Introduce `z`. Rewrite using `[sesq_skew hcc hj, (horth z).1, map_zero, neg_zero]`. Establish `hgram : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map cc = incM F W₁.J`.

Rewrite using `[← hH.gram]`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map]`. Use `congr 2`. Establish `hdet : IsUnit (incM F W₁.J).det`. Establish `h0 : W₁.J.det ≠ 0` using `GlobalTheory.UnipComm.det_ne_of_skew B W₁.J hW₁.sig`.

Establish `e` using `RingHom.map_det (inclR (F := F) (AF F)) W₁.J`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Use `show IsUnit (W₁.J.map (inclR (AF F))).det`. Rewrite using `[← e]`. Conclude with `(Ne.isUnit h0).map _`.

Use `set h2 : AE F E := inclR (AF F) ((2 : E)⁻¹) with hh2`. Establish `h2two : (2 : AE F E) * h2 = 1`. Rewrite using `[hh2, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]`. Establish `hc2 : cc 2 = 2` using `map_ofNat cc 2`. Establish `hch2 : cc h2 = h2`.

Rewrite using `[hh2, hcc_def]`. Use `show cA σ (inclR (AF F) ((2 : E)⁻¹)) = _`. Rewrite using `[cA_inclR, map_inv₀, map_ofNat]`. Use `set m := torusMat cc (incM F W.J) (incV F H'.x) (incV F H'.y) 2 h2 with hm`. Use `set m' := torusMat cc (incM F W.J) (incV F H'.x) (incV F H'.y) h2 2 with hm'`.

Establish `hmm' : m * m' = 1` using `torusMat_mul hcc hj hxx hyy hxy h2two (by rw [mul_comm, h2two])`. Establish `hm'm : m' * m = 1` using `torusMat_mul hcc hj hxx hyy hxy (by rw [mul_comm, h2two]) h2two`. Establish `hmU : mᵀ * incM F W.J * m.map cc = incM F W.J` using `torusMat_unitary hcc hj hxx hyy hxy (by rw [hch2, h2two]) (by rw [hc2, h2two])`. Set `mg : UA σ W.J` to `⟨⟨m, m', hmm', hm'm⟩, hmU⟩`. Establish `hmat : mat mg = m` using `rfl`.

Establish `hmat' : mat mg⁻¹ = m'` using `rfl`. Establish `hmx : m *ᵥ incV F H'.x = (2 : AE F E) • incV F H'.x`. Rewrite using `[hm, torusMat_mulVec, hxy, hxx]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmι : ∀ z, m *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z`. Introduce `z`. Rewrite using `[hm, torusMat_mulVec, (horth z).1, (horth z).2]`. Simplify using the standard rewrite rules.

Establish `hm'x : m' *ᵥ incV F H'.x = h2 • incV F H'.x`. Rewrite using `[hm', torusMat_mulVec, hxy, hxx]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hm'ι : ∀ z, m' *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z`. Introduce `z`. Rewrite using `[hm', torusMat_mulVec, (horth z).1, (horth z).2]`. Simplify using the standard rewrite rules. Establish `hm's : ∀ v, sesq cc (incM F W.J) (m' *ᵥ v) (incV F H'.x) = 2 * sesq cc (incM F W.J) v (incV F H'.x)`.

Introduce `v`. Rewrite using `[hm', torusMat_mulVec, sesq_add_left, sesq_add_left, sesq_smul_left, sesq_smul_left, hxx, hyx]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmm'v : ∀ v, m *ᵥ (m' *ᵥ v) = v` using `fun v => by rw [mulVec_mulVec, hmm', one_mulVec]`. Set `u2 : (AE F E)ˣ` to `⟨2, h2, h2two, by rw [mul_comm]; exact h2two⟩`.

Establish `hmS : mg ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H'`. Use `⟨⟨u2, ?_⟩, fun z => ⟨0, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hmat, hmx]`. Rewrite using `[hmat, hmι, zero_smul, add_zero]`. Establish `hU : ∀ (g : UA σ W.J) (u v : Fin d → AE F E), sesq cc (incM F W.J) (mat g *ᵥ u) (mat g *ᵥ v) = sesq cc (incM F W.J) u v` using `fun g u v => sesq_UA W.J g u v`.

Establish `hyι : ∀ z, sesq cc (incM F W.J) (incV F H'.y) (incM F H'.ι *ᵥ z) = 0`. Introduce `z`. Rewrite using `[sesq_skew hcc hj, (horth z).2, map_zero, neg_zero]`. Establish `hdec` using `GlobalTheory.T.levi_torus_hyperbolic_pair _ cc d d₁ (incM F W.J) (incM F W₁.J) (incV F H'.x) (incV F H'.y) (incM F H'.ι) hcc hj hH.rank hxx hyy hxy horth hgram hdet`. Establish `hZ : ∀ w : UA σ W.J, mat w *ᵥ incV F H'.x = incV F H'.x → (∀ z, mat w *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z) → ∃ β : AE F E, cc β = β ∧ ∀ v, mat w *ᵥ v = v + (-(sesq cc (incM F W.J) v (incV F H'.x) * β)) • incV F H'.x`.

Introduce `w hwx hwι`. Use `set q := mat w *ᵥ incV F H'.y - incV F H'.y with hq`. Establish `hqx : sesq cc (incM F W.J) q (incV F H'.x) = 0`. Use `hU w (incV F H'.y) (incV F H'.x)` as an intermediate fact. Rewrite `this` using `[hwx]`.

Rewrite using `[hq, sesq_sub_left', this, sub_self]`. Establish `hqι : ∀ z, sesq cc (incM F W.J) q (incM F H'.ι *ᵥ z) = 0`. Introduce `z`. Use `hU w (incV F H'.y) (incM F H'.ι *ᵥ z)` as an intermediate fact. Rewrite `this` using `[hwι]`.

Rewrite using `[hq, sesq_sub_left', this, sub_self]`. Take `⟨zq, hzq⟩` from `hdec q`. Rewrite `hzq` using `[hqx, zero_smul, sub_zero]`. Establish `hz0 : zq = 0` using `nondeg hgram hdet zq (fun z' => by`. Use `hqι z'` as an intermediate fact.

Rewrite `this` using `[hzq, sesq_add_left, sesq_smul_left, hxι, mul_zero, zero_add]`. Conclude with `this)`. Rewrite `hzq` using `[hz0, mulVec_zero, add_zero]`. Establish `hwy : mat w *ᵥ incV F H'.y = incV F H'.y + sesq cc (incM F W.J) q (incV F H'.y) • incV F H'.x`. Rewrite using `[← hzq, hq]`.

Normalize the expressions using the abelian group laws. Use `⟨sesq cc (incM F W.J) q (incV F H'.y), ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `hU w (incV F H'.y) (incV F H'.y)`. Rewrite `h1` using `[hwy]`. Simplify using `only [sesq_add_left, sesq_add_right, sesq_smul_left, sesq_smul_right, hxx, hyy, hxy, hyx] at h1`.

Take the linear combination `-h1`. Take `⟨z, hz⟩` from `hdec v`. Generalize the expression as in `sesq cc (incM F W.J) v (incV F H'.y) = a at hz`. Generalize the expression as in `hb : sesq cc (incM F W.J) v (incV F H'.x) = b at hz ⊢`. Substitute `hz` using the available equality.

Rewrite using `[mulVec_add, mulVec_sub, mulVec_smul, mulVec_smul, hwx, hwι, hwy]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `htvU : ∀ b : AE F E, cc b = b → ∃ g : UA σ W.J, mat g = tv cc (incM F W.J) (incV F H'.x) b ∧ mat g⁻¹ = tv cc (incM F W.J) (incV F H'.x) (-b)`.

Introduce `b hb`. Establish `h1 : tv cc (incM F W.J) (incV F H'.x) b * tv cc (incM F W.J) (incV F H'.x) (-b) = 1`. Rewrite using `[tv_mul hxx, add_neg_cancel]`. Simplify using `[tv]`. Establish `h2 : tv cc (incM F W.J) (incV F H'.x) (-b) * tv cc (incM F W.J) (incV F H'.x) b = 1`.

Rewrite using `[tv_mul hxx, neg_add_cancel]`. Simplify using `[tv]`. Conclude with `⟨⟨⟨_, _, h1, h2⟩, tv_unitary hcc hj hxx hb⟩, rfl, rfl⟩`. Use `set h3 : AE F E := inclR (AF F) ((3 : E)⁻¹) with hh3`. Establish `h3three : (3 : AE F E) * h3 = 1`.

Rewrite using `[hh3, ← map_ofNat (inclR (F := F) (AF F)) 3, ← map_mul, mul_inv_cancel₀ three_ne_zero, map_one]`. Establish `hch3 : cc h3 = h3`. Rewrite using `[hh3, hcc_def]`. Use `show cA σ (inclR (AF F) ((3 : E)⁻¹)) = _`. Rewrite using `[cA_inclR, map_inv₀, map_ofNat]`.

Establish `hgen : ∀ u : UA σ W.J, (mat u *ᵥ incV F H'.x = incV F H'.x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x) → c u = 1`. Introduce `u hu`. Establish `huS : u ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H'` using `GlobalTheory.UnipEv.unip_le_stabP W H' (Subgroup.subset_closure hu)`. Use `choose a ha using hu.2`. Establish `hinv : ∀ v, mat u⁻¹ *ᵥ (mat u *ᵥ v) = v` using `fun v => by`.

Rewrite using `[mulVec_mulVec, GlobalTheory.UnipEv.mat_inv_mul', one_mulVec]`. Establish `hux' : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x`. Use `hinv (incV F H'.x)` as an intermediate fact. Rewrite `this` using `[hu.1]`. Then use the resulting hypothesis. Establish `huι' : ∀ z, mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z - a z • incV F H'.x`.

Introduce `z`. Use `hinv (incM F H'.ι *ᵥ z)` as an intermediate fact. Rewrite `this` using `[ha z, mulVec_add, mulVec_smul, hux']`. Conclude with `eq_sub_of_add_eq this`. Use `set wc := u⁻¹ * (mg * u * mg⁻¹ * u⁻¹) with hwc`.

Establish `hwcx : mat wc *ᵥ incV F H'.x = incV F H'.x`. Simplify using `only [hwc, GlobalTheory.UnipEv.mat_mul', ← mulVec_mulVec, hmat, hmat', hux', mulVec_smul, hm'x, hu.1, hmx, smul_smul]`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(incV F H'.x i) * h2two`.

Establish `hwcι : ∀ z, mat wc *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z`. Introduce `z`. Simplify using `only [hwc, GlobalTheory.UnipEv.mat_mul', ← mulVec_mulVec, hmat, hmat', huι', mulVec_sub, mulVec_add, mulVec_smul, hm'ι, hm'x, ha, hu.1, hmι, hmx, hux', smul_smul]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Take the linear combination `(-(a z * incV F H'.x i)) * h2two`. Take `⟨β, hβc, hβ⟩` from `hZ wc hwcx hwcι`. Take `⟨w', hw', hw'i⟩` from `htvU (h3 * β) (by rw [map_mul, hch3, hβc])`. Establish `hw'S : w' ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H'`. Use `⟨⟨1, ?_⟩, fun z => ⟨0, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hw', tv_mulVec, hxx]`. Simplify using the standard rewrite rules. Rewrite using `[hw', tv_mulVec, (horth z).1]`. Simplify using the standard rewrite rules. Establish `hcomm : mg * w' * mg⁻¹ * w'⁻¹ = wc`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mat (mg * w' * mg⁻¹ * w'⁻¹) = mat wc`. Use `Matrix.ext_of_mulVec_single fun k => ?_` and prove the remaining obligations. Generalize the expression as in `(Pi.single k 1 : Fin d → AE F E) = v`.

Rewrite using `[hβ v]`. Simplify using `only [GlobalTheory.UnipEv.mat_mul', ← mulVec_mulVec, hmat, hmat', hw', hw'i]`. Simplify using `only [tv_mulVec, mulVec_add, mulVec_smul, hm'x, hmx, hmm'v, sesq_add_left, sesq_smul_left, hm's, hxx]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Take the linear combination `(sesq cc (incM F W.J) v (incV F H'.x) * β * h3 * incV F H'.x i) * h2two - (sesq cc (incM F W.J) v (incV F H'.x) * β * incV F H'.x i) * h3three`. Establish `hwcS : wc ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H'` using `mul_mem (inv_mem huS) (mul_mem (mul_mem (mul_mem hmS huS) (inv_mem hmS)) (inv_mem huS))`. Establish `e1 : c wc = 1` using `by rw [← hcomm]; exact char_comm c hc hc1 hmS hw'S`. Establish `e2 : c wc = c u⁻¹`. Rewrite using `[hwc, hc _ (inv_mem huS) _ (mul_mem (mul_mem (mul_mem hmS huS) (inv_mem hmS)) (inv_mem huS)), char_comm c hc hc1 hmS huS, mul_one]`.

Establish `hinvu : c u * c u⁻¹ = 1` using `by rw [← hc u huS u⁻¹ (inv_mem huS), mul_inv_cancel, hc1]`. Rewrite `hinvu` using `[← e2, e1, mul_one]`. Conclude with `hinvu`. Introduce `u hu`. Establish `key : ∀ g ∈ unip σ W H', g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H' ∧ c g = 1`.

Introduce `g hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg => exact ⟨GlobalTheory.UnipEv.unip_le_stabP W H' (Subgroup.subset_closure hg), hgen g hg⟩`. Consider the case `one => exact ⟨one_mem _, hc1⟩`. Consider the case `mul a b _ _ ha hb => exact ⟨mul_mem ha.1 hb.1, by rw [hc _ ha.1 _ hb.1, ha.2, hb.2, one_mul]⟩`.

Consider the case `inv a _ ha`. Use `⟨inv_mem ha.1, ?_⟩` and prove the remaining obligations. Use `hc a ha.1 a⁻¹ (inv_mem ha.1)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hc1, ha.2, one_mul]`. Conclude with `this.symm`.

Conclude with `(key u hu).2`.
-/
theorem char_trivial_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ) (W : Spc F E d)
    (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ), B.IsGood σ → W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ →
      H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ c : UA σ W.J → ℂ,
        (∀ g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∀ h ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', c (g * h) = c g * c h) → c 1 = 1 →
        ∀ u ∈ unip σ W H', c u = 1 := by
  intro F E _ _ _ _ _ σ B d W d₁ W₁ H' i₀ i₁ r' s' r₁ s₁ hB hW hW₁ hH c hc hc1
  classical
  have hcm : IsCMExt F E σ := hB.cm
  set cc : AE F E →+* AE F E := (cA σ).toRingHom with hcc_def
  have hcc : ∀ z, cc (cc z) = z := fun z => cA_cA hcm z
  have hj : ∀ i k, cc (incM F W.J k i) = -incM F W.J i k := by
    intro i k
    simp [cc, incM, cA_inclR, hW.skew i k]
  have hxx : sesq cc (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [sesq_incV, hH.xx, map_zero]
  have hyy : sesq cc (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [sesq_incV, hH.yy, map_zero]
  have hxy : sesq cc (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [sesq_incV, hH.xy, map_one]
  have hyx : sesq cc (incM F W.J) (incV F H'.y) (incV F H'.x) = -1 := by rw [sesq_skew hcc hj, hxy, map_one]
  have hT : ∀ (z : Fin d₁ → AE F E) (u : Fin d → AE F E), (incM F H'.ι *ᵥ z) ⬝ᵥ u = z ⬝ᵥ ((incM F H'.ι)ᵀ *ᵥ u) := by
    intro z u
    rw [mulVec_transpose, dotProduct_comm z, dotProduct_comm (incM F H'.ι *ᵥ z), dotProduct_mulVec]
  have hcol : ∀ k, incM F H'.ι *ᵥ Pi.single k 1 = incV F (H'.ι *ᵥ Pi.single k 1) := by
    intro k; ext i; simp [mulVec_single_one, incV, incM]
  have horth : ∀ z, sesq cc (incM F W.J) (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 ∧
      sesq cc (incM F W.J) (incM F H'.ι *ᵥ z) (incV F H'.y) = 0 := by
    intro z
    have key : ∀ w : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) w = 0) →
        sesq cc (incM F W.J) (incM F H'.ι *ᵥ z) (incV F w) = 0 := by
      intro w hw
      rw [sesq, hT]
      have : (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun i => cc (incV F w i)) = 0 := by
        ext k
        have h2 : sesq cc (incM F W.J) (incM F H'.ι *ᵥ Pi.single k 1) (incV F w) = 0 := by
          rw [hcol, sesq_incV, hw, map_zero]
        rw [sesq, hT] at h2
        simpa using h2
      rw [this, dotProduct_zero]
    exact ⟨key _ fun u => (hH.orth u).1, key _ fun u => (hH.orth u).2⟩
  have hxι : ∀ z, sesq cc (incM F W.J) (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := by
    intro z; rw [sesq_skew hcc hj, (horth z).1, map_zero, neg_zero]
  have hgram : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map cc = incM F W₁.J := by
    rw [← hH.gram]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map]
    congr 2
  have hdet : IsUnit (incM F W₁.J).det := by
    have h0 : W₁.J.det ≠ 0 := GlobalTheory.UnipComm.det_ne_of_skew B W₁.J hW₁.sig
    have e := RingHom.map_det (inclR (F := F) (AF F)) W₁.J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (W₁.J.map (inclR (AF F))).det
    rw [← e]
    exact (Ne.isUnit h0).map _

  set h2 : AE F E := inclR (AF F) ((2 : E)⁻¹) with hh2
  have h2two : (2 : AE F E) * h2 = 1 := by
    rw [hh2, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hc2 : cc 2 = 2 := map_ofNat cc 2
  have hch2 : cc h2 = h2 := by
    rw [hh2, hcc_def]; show cA σ (inclR (AF F) ((2 : E)⁻¹)) = _; rw [cA_inclR, map_inv₀, map_ofNat]
  set m := torusMat cc (incM F W.J) (incV F H'.x) (incV F H'.y) 2 h2 with hm
  set m' := torusMat cc (incM F W.J) (incV F H'.x) (incV F H'.y) h2 2 with hm'
  have hmm' : m * m' = 1 := torusMat_mul hcc hj hxx hyy hxy h2two (by rw [mul_comm, h2two])
  have hm'm : m' * m = 1 := torusMat_mul hcc hj hxx hyy hxy (by rw [mul_comm, h2two]) h2two
  have hmU : mᵀ * incM F W.J * m.map cc = incM F W.J :=
    torusMat_unitary hcc hj hxx hyy hxy (by rw [hch2, h2two]) (by rw [hc2, h2two])
  let mg : UA σ W.J := ⟨⟨m, m', hmm', hm'm⟩, hmU⟩
  have hmat : mat mg = m := rfl
  have hmat' : mat mg⁻¹ = m' := rfl
  have hmx : m *ᵥ incV F H'.x = (2 : AE F E) • incV F H'.x := by
    rw [hm, torusMat_mulVec, hxy, hxx]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hmι : ∀ z, m *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := by
    intro z; rw [hm, torusMat_mulVec, (horth z).1, (horth z).2]; simp
  have hm'x : m' *ᵥ incV F H'.x = h2 • incV F H'.x := by
    rw [hm', torusMat_mulVec, hxy, hxx]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hm'ι : ∀ z, m' *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := by
    intro z; rw [hm', torusMat_mulVec, (horth z).1, (horth z).2]; simp
  have hm's : ∀ v, sesq cc (incM F W.J) (m' *ᵥ v) (incV F H'.x) = 2 * sesq cc (incM F W.J) v (incV F H'.x) := by
    intro v; rw [hm', torusMat_mulVec, sesq_add_left, sesq_add_left, sesq_smul_left, sesq_smul_left, hxx, hyx]; ring
  have hmm'v : ∀ v, m *ᵥ (m' *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hmm', one_mulVec]
  let u2 : (AE F E)ˣ := ⟨2, h2, h2two, by rw [mul_comm]; exact h2two⟩
  have hmS : mg ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H' := by
    refine ⟨⟨u2, ?_⟩, fun z => ⟨0, ?_⟩⟩
    · rw [hmat, hmx]
    · rw [hmat, hmι, zero_smul, add_zero]
  have hU : ∀ (g : UA σ W.J) (u v : Fin d → AE F E),
      sesq cc (incM F W.J) (mat g *ᵥ u) (mat g *ᵥ v) = sesq cc (incM F W.J) u v := fun g u v => sesq_UA W.J g u v
  have hyι : ∀ z, sesq cc (incM F W.J) (incV F H'.y) (incM F H'.ι *ᵥ z) = 0 := by
    intro z; rw [sesq_skew hcc hj, (horth z).2, map_zero, neg_zero]
  have hdec := GlobalTheory.T.levi_torus_hyperbolic_pair _ cc d d₁ (incM F W.J) (incM F W₁.J) (incV F H'.x) (incV F H'.y) (incM F H'.ι) hcc hj hH.rank
    hxx hyy hxy horth hgram hdet

  have hZ : ∀ w : UA σ W.J, mat w *ᵥ incV F H'.x = incV F H'.x → (∀ z, mat w *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z) →
      ∃ β : AE F E, cc β = β ∧ ∀ v, mat w *ᵥ v = v + (-(sesq cc (incM F W.J) v (incV F H'.x) * β)) • incV F H'.x := by
    intro w hwx hwι
    set q := mat w *ᵥ incV F H'.y - incV F H'.y with hq
    have hqx : sesq cc (incM F W.J) q (incV F H'.x) = 0 := by
      have := hU w (incV F H'.y) (incV F H'.x)
      rw [hwx] at this
      rw [hq, sesq_sub_left', this, sub_self]
    have hqι : ∀ z, sesq cc (incM F W.J) q (incM F H'.ι *ᵥ z) = 0 := by
      intro z
      have := hU w (incV F H'.y) (incM F H'.ι *ᵥ z)
      rw [hwι] at this
      rw [hq, sesq_sub_left', this, sub_self]
    obtain ⟨zq, hzq⟩ := hdec q
    rw [hqx, zero_smul, sub_zero] at hzq
    have hz0 : zq = 0 := nondeg hgram hdet zq (fun z' => by
      have := hqι z'
      rw [hzq, sesq_add_left, sesq_smul_left, hxι, mul_zero, zero_add] at this
      exact this)
    rw [hz0, mulVec_zero, add_zero] at hzq
    have hwy : mat w *ᵥ incV F H'.y = incV F H'.y + sesq cc (incM F W.J) q (incV F H'.y) • incV F H'.x := by
      rw [← hzq, hq]; abel
    refine ⟨sesq cc (incM F W.J) q (incV F H'.y), ?_, fun v => ?_⟩
    · have h1 := hU w (incV F H'.y) (incV F H'.y)
      rw [hwy] at h1
      simp only [sesq_add_left, sesq_add_right, sesq_smul_left, sesq_smul_right, hxx, hyy, hxy, hyx] at h1
      linear_combination -h1
    · obtain ⟨z, hz⟩ := hdec v
      generalize sesq cc (incM F W.J) v (incV F H'.y) = a at hz
      generalize hb : sesq cc (incM F W.J) v (incV F H'.x) = b at hz ⊢
      subst hz
      rw [mulVec_add, mulVec_sub, mulVec_smul, mulVec_smul, hwx, hwι, hwy]
      ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

  have htvU : ∀ b : AE F E, cc b = b → ∃ g : UA σ W.J, mat g = tv cc (incM F W.J) (incV F H'.x) b ∧
      mat g⁻¹ = tv cc (incM F W.J) (incV F H'.x) (-b) := by
    intro b hb
    have h1 : tv cc (incM F W.J) (incV F H'.x) b * tv cc (incM F W.J) (incV F H'.x) (-b) = 1 := by
      rw [tv_mul hxx, add_neg_cancel]; simp [tv]
    have h2 : tv cc (incM F W.J) (incV F H'.x) (-b) * tv cc (incM F W.J) (incV F H'.x) b = 1 := by
      rw [tv_mul hxx, neg_add_cancel]; simp [tv]
    exact ⟨⟨⟨_, _, h1, h2⟩, tv_unitary hcc hj hxx hb⟩, rfl, rfl⟩
  set h3 : AE F E := inclR (AF F) ((3 : E)⁻¹) with hh3
  have h3three : (3 : AE F E) * h3 = 1 := by
    rw [hh3, ← map_ofNat (inclR (F := F) (AF F)) 3, ← map_mul, mul_inv_cancel₀ three_ne_zero, map_one]
  have hch3 : cc h3 = h3 := by
    rw [hh3, hcc_def]; show cA σ (inclR (AF F) ((3 : E)⁻¹)) = _; rw [cA_inclR, map_inv₀, map_ofNat]

  have hgen : ∀ u : UA σ W.J, (mat u *ᵥ incV F H'.x = incV F H'.x ∧ ∀ z, ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x) → c u = 1 := by
    intro u hu
    have huS : u ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H' := GlobalTheory.UnipEv.unip_le_stabP W H' (Subgroup.subset_closure hu)
    choose a ha using hu.2
    have hinv : ∀ v, mat u⁻¹ *ᵥ (mat u *ᵥ v) = v := fun v => by
      rw [mulVec_mulVec, GlobalTheory.UnipEv.mat_inv_mul', one_mulVec]
    have hux' : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      have := hinv (incV F H'.x); rwa [hu.1] at this
    have huι' : ∀ z, mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z - a z • incV F H'.x := by
      intro z
      have := hinv (incM F H'.ι *ᵥ z)
      rw [ha z, mulVec_add, mulVec_smul, hux'] at this
      exact eq_sub_of_add_eq this
    set wc := u⁻¹ * (mg * u * mg⁻¹ * u⁻¹) with hwc
    have hwcx : mat wc *ᵥ incV F H'.x = incV F H'.x := by
      simp only [hwc, GlobalTheory.UnipEv.mat_mul', ← mulVec_mulVec, hmat, hmat', hux', mulVec_smul, hm'x, hu.1, hmx, smul_smul]
      ext i; simp only [Pi.smul_apply, smul_eq_mul]; linear_combination (incV F H'.x i) * h2two
    have hwcι : ∀ z, mat wc *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := by
      intro z
      simp only [hwc, GlobalTheory.UnipEv.mat_mul', ← mulVec_mulVec, hmat, hmat', huι', mulVec_sub, mulVec_add, mulVec_smul,
        hm'ι, hm'x, ha, hu.1, hmι, hmx, hux', smul_smul]
      ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(a z * incV F H'.x i)) * h2two
    obtain ⟨β, hβc, hβ⟩ := hZ wc hwcx hwcι
    obtain ⟨w', hw', hw'i⟩ := htvU (h3 * β) (by rw [map_mul, hch3, hβc])
    have hw'S : w' ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H' := by
      refine ⟨⟨1, ?_⟩, fun z => ⟨0, ?_⟩⟩
      · rw [hw', tv_mulVec, hxx]; simp
      · rw [hw', tv_mulVec, (horth z).1]; simp
    have hcomm : mg * w' * mg⁻¹ * w'⁻¹ = wc := by
      apply Subtype.ext; apply Units.ext
      show mat (mg * w' * mg⁻¹ * w'⁻¹) = mat wc
      refine Matrix.ext_of_mulVec_single fun k => ?_
      generalize (Pi.single k 1 : Fin d → AE F E) = v
      rw [hβ v]
      simp only [GlobalTheory.UnipEv.mat_mul', ← mulVec_mulVec, hmat, hmat', hw', hw'i]
      simp only [tv_mulVec, mulVec_add, mulVec_smul, hm'x, hmx, hmm'v, sesq_add_left, sesq_smul_left, hm's, hxx]
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (sesq cc (incM F W.J) v (incV F H'.x) * β * h3 * incV F H'.x i) * h2two -
        (sesq cc (incM F W.J) v (incV F H'.x) * β * incV F H'.x i) * h3three
    have hwcS : wc ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H' :=
      mul_mem (inv_mem huS) (mul_mem (mul_mem (mul_mem hmS huS) (inv_mem hmS)) (inv_mem huS))
    have e1 : c wc = 1 := by rw [← hcomm]; exact char_comm c hc hc1 hmS hw'S
    have e2 : c wc = c u⁻¹ := by
      rw [hwc, hc _ (inv_mem huS) _ (mul_mem (mul_mem (mul_mem hmS huS) (inv_mem hmS)) (inv_mem huS)),
        char_comm c hc hc1 hmS huS, mul_one]
    have hinvu : c u * c u⁻¹ = 1 := by rw [← hc u huS u⁻¹ (inv_mem huS), mul_inv_cancel, hc1]
    rw [← e2, e1, mul_one] at hinvu
    exact hinvu
  intro u hu
  have key : ∀ g ∈ unip σ W H', g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H' ∧ c g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact ⟨GlobalTheory.UnipEv.unip_le_stabP W H' (Subgroup.subset_closure hg), hgen g hg⟩
    | one => exact ⟨one_mem _, hc1⟩
    | mul a b _ _ ha hb => exact ⟨mul_mem ha.1 hb.1, by rw [hc _ ha.1 _ hb.1, ha.2, hb.2, one_mul]⟩
    | inv a _ ha =>
      refine ⟨inv_mem ha.1, ?_⟩
      have := hc a ha.1 a⁻¹ (inv_mem ha.1)
      rw [mul_inv_cancel, hc1, ha.2, one_mul] at this
      exact this.symm
  exact (key u hu).2
end Thm

end GlobalTheory.UnipComm
