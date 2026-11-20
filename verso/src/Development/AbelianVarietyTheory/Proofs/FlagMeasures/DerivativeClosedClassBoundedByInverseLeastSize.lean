import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.SobolevBound

/- English proof (translation)
Establish `hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε` using `Formalism.REAL.Jm_conjTranspose ε`. Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1` using `Formalism.REAL.Jm_mul_self ε`. Establish `hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Establish `hmem : ∀ X : Matrix (Fin n) (Fin n) ℂ, X ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε ↔ Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0` using `fun X => Iff.rfl`.

Establish `hA : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε`. Introduce `Z`. Rewrite using `[hmem]`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']`. Normalize the expressions using the abelian group laws.

Establish `hB : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε`. Introduce `Z`. Rewrite using `[hmem]`. Simplify using `only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ', smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_I, neg_smul, sm …`. Normalize the expressions using the abelian group laws.

Set `L : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε × GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun p => (p.1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (p.2 : Matrix (Fin n) (Fin n) ℂ) map_add' := fun p q => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun r p => by`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]`.

Rewrite using `[smul_comm r Complex.I] }`. Establish `hsurj : Function.Surjective L`. Introduce `Z`. Use `⟨(⟨(2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε), (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hA Z)⟩, ⟨(-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε)), (GlobalTheory.IndefiniteRowSideFullHec …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) + Complex.I • ((-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε))) = Z`.

Generalize the expression as in `Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε = W`. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]`. Use `push_cast`. Take the linear combination `(-(1 : ℂ) / 2 * (Z a b + W a b)) * Complex.I_sq`.

Establish `hfin : n ^ 2 ≤ Module.finrank ℝ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε)`. Establish `h1` using `LinearMap.finrank_le_finrank_of_surjective hsurj`. Rewrite `h1` using `[Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex]`. Use polynomial arithmetic with `[h1]`. Set `Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool)` to `{ toFun := fun X => WithLp.toLp 2 (fun q => if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im) map_add' := fun X Y => by`.

Use extensionality with `q`. Apply the tactic sequence `by_cases h : q.2.2 <;> simp [h]`. Use the proof step `map_smul' := fun r X => by`. Use extensionality with `q`. Apply the tactic sequence `by_cases h : q.2.2 <;> simp [h] }`.

Establish `hΦapp : ∀ X q, (Φ X) q = if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im` using `fun _ _ => rfl`. Establish `hΦ : ∀ X Y, inner ℝ (Φ X) (Φ Y) = ((X * Yᴴ).trace).re`. Introduce `X Y`. Rewrite using `[PiLp.inner_apply]`. Simplify using `only [hΦapp, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [RCLike.inner_apply, conj_trivial]`. Expand and normalize the polynomial expressions, which then agree. Establish `hΦinj : Function.Injective Φ`. Introduce `X Y h`.

Use extensionality with `a b`. Apply `Complex.ext` to reduce the goal to its premises. Establish `h1` using `congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, true)) h`. Simplify `h1` using `[hΦapp]`. Establish `h1` using `congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, false)) h`.

Simplify `h1` using `[hΦapp]`. Set `Ψ` to `Φ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).subtype`. Establish `hΨ : Function.Injective Ψ`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hΦinj` to reduce the goal to its premises. Simplify `h` using `[Ψ]`. Establish `hS : n ^ 2 ≤ Module.finrank ℝ (LinearMap.range Ψ)`. Rewrite using `[LinearMap.finrank_range_of_inj hΨ]`. Conclude with `hfin`.

Set `b` to `stdOrthonormalBasis ℝ (LinearMap.range Ψ)`. Apply the tactic sequence `have hbo : Orthonormal ℝ (fun i => ((b i : LinearMap.range Ψ) : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := b.orthonormal.comp_linearIsometry (LinearMap.range Ψ).subtypeₗᵢ`. Establish `hpre : ∀ i, ∃ X : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε, Φ (X : Matrix (Fin n) (Fin n) ℂ) = b i`. Introduce `i`. Take `⟨X, hX⟩` from `LinearMap.mem_range.1 (b i).2`.

Conclude with `⟨X, by simpa [Ψ] using hX⟩`. Use `choose X hX using hpre`. Use `⟨fun j => X (Fin.castLE hS j), fun i j => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← hΦ, hX, hX]`.

Establish `h2` using `orthonormal_iff_ite.1 hbo (Fin.castLE hS i) (Fin.castLE hS j)`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
private lemma exists_re_trace_orthonormal_gLie {n : ℕ} (ε : Fin n → Bool) :
    ∃ E : Fin (n ^ 2) → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε,
      ∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
        if i = j then 1 else 0 := by

  classical
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hmem : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε ↔ Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := fun X => Iff.rfl

  have hA : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']
    abel
  have hB : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ,
      Matrix.mul_one, hJJ', smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_I, neg_smul,
      smul_add, neg_mul]
    abel
  let L : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε × GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => (p.1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (p.2 : Matrix (Fin n) (Fin n) ℂ)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := fun r p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm r Complex.I] }
  have hsurj : Function.Surjective L := by
    intro Z
    refine ⟨(⟨(2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hA Z)⟩,
      ⟨(-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε)),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hB Z)⟩), ?_⟩
    change (2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) +
      Complex.I • ((-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε))) = Z
    generalize Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε = W
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(1 : ℂ) / 2 * (Z a b + W a b)) * Complex.I_sq
  have hfin : n ^ 2 ≤ Module.finrank ℝ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) := by
    have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex] at h1
    nlinarith [h1]

  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
    { toFun := fun X => WithLp.toLp 2 (fun q => if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im)
      map_add' := fun X Y => by
        ext q
        by_cases h : q.2.2 <;> simp [h]
      map_smul' := fun r X => by
        ext q
        by_cases h : q.2.2 <;> simp [h] }
  have hΦapp : ∀ X q, (Φ X) q = if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im := fun _ _ => rfl
  have hΦ : ∀ X Y, inner ℝ (Φ X) (Φ Y) = ((X * Yᴴ).trace).re := by
    intro X Y
    rw [PiLp.inner_apply]
    simp only [hΦapp, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hΦinj : Function.Injective Φ := by
    intro X Y h
    ext a b
    apply Complex.ext
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, true)) h
      simpa [hΦapp] using h1
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, false)) h
      simpa [hΦapp] using h1
  let Ψ := Φ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).subtype
  have hΨ : Function.Injective Ψ := by
    intro x y h
    apply Subtype.ext
    apply hΦinj
    simpa [Ψ] using h
  have hS : n ^ 2 ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    rw [LinearMap.finrank_range_of_inj hΨ]
    exact hfin
  let b := stdOrthonormalBasis ℝ (LinearMap.range Ψ)
  have hbo : Orthonormal ℝ (fun i => ((b i : LinearMap.range Ψ) : EuclideanSpace ℝ (Fin n × Fin n × Bool))) :=
    b.orthonormal.comp_linearIsometry (LinearMap.range Ψ).subtypeₗᵢ
  have hpre : ∀ i, ∃ X : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε, Φ (X : Matrix (Fin n) (Fin n) ℂ) = b i := by
    intro i
    obtain ⟨X, hX⟩ := LinearMap.mem_range.1 (b i).2
    exact ⟨X, by simpa [Ψ] using hX⟩
  choose X hX using hpre
  refine ⟨fun j => X (Fin.castLE hS j), fun i j => ?_⟩
  dsimp only
  rw [← hΦ, hX, hX]
  have h2 := orthonormal_iff_ite.1 hbo (Fin.castLE hS i) (Fin.castLE hS j)
  rw [h2]
  simp

/- English proof (translation)
Introduce `B hn hg`. Use `⟨2 * (B.I.n ^ 2 * B.I.f), ?_⟩` and prove the remaining obligations. Introduce `W hW f hf`. Use `choose E hE using fun v : InfinitePlace B.I.F => exists_re_trace_orthonormal_gLie (B.I.ε v)`. Use `choose c hc using fun v : InfinitePlace B.I.F => GlobalTheory.GaugeConst.gauge_exists_pos_unique B.I.n (B.I.ε v)`.

Set `e : Fin (Fintype.card (InfinitePlace B.I.F)) ≃ InfinitePlace B.I.F` to `(Fintype.equivFin (InfinitePlace B.I.F)).symm`. Establish `hnr : (1 : ℝ) ≤ B.I.n` using `by exact_mod_cast hn`. Establish `hn0 : (0 : ℝ) < B.I.n` using `by linarith`. Establish `hp5 : (0 : ℝ) < (B.I.n : ℝ) ^ 5` using `pow_pos hn0 5`. Establish `h35 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 5` using `pow_le_pow_right₀ hnr (by norm_num)`.

Establish `hden : (0 : ℝ) < 12 * (B.I.n : ℝ) ^ 5` using `by linarith`. Establish `hs : (0 : ℝ) < 1 / (12 * (B.I.n : ℝ) ^ 5)` using `div_pos one_pos hden`. Establish `h3 : 12 * (B.I.n : ℝ) ^ 3 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1`. Rewrite using `[mul_one_div, div_le_one hden]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : 8 * (B.I.n : ℝ) ^ 5 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1`. Rewrite using `[mul_one_div, div_le_one hden]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨C0, hC0, hsob⟩` from `GlobalTheory.sobolev_iterated_one_parameter_subgroups_words B.I.GA (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) (fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat))) (1 / (12 * (B.I.n : ℝ) ^ 5)) hs (fun l => onePar_spec B _)`. Establish `hder : ∀ g ∈ W, ∀ l : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ∃ g' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => g (y * onePar B (atPlace B (e l.divNat) (E _ l.modNat)) t)) (g' y) 0` using `fun g hgW l => (hW g hgW).2.2 (e l.divNat) (E _ l.modNat)`.

Use `choose! D hDW hD using hder`. Set `F : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)) → B.I.GA → ℂ` to `fun l => l.foldr (fun i g => D g i) f`. Establish `hFW : ∀ l, F l ∈ W`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil => exact hf`. Consider the case `cons i l ih => exact hDW _ ih i`. Establish `hrep : ∀ l, ∃ Fv, GlobalTheory.Dec.IsContRep B Fv (F l)` using `fun l => (hW (F l) (hFW l)).1`. Use `choose Fv hFv using hrep`. Use `set Mx : ℝ := ∑ k ∈ Finset.range ((Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) + 1), ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 with hMx`.

Establish `hMx0 : 0 ≤ Mx` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity`. Establish `hle : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) → ‖Fv l‖ ^ 2 ≤ Mx`. Introduce `l hl`. Combine the equalities or inequalities in the displayed calculation. Establish `hP : 0 ≤ ∏ v, c v` using `Finset.prod_nonneg fun v _ => (hc v).1.le`.

Use `set K : ℝ := Real.exp B.I.f * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal with hK`. Establish `hK0 : 0 ≤ K` using `div_nonneg (mul_nonneg (Real.exp_pos _).le hP) ENNReal.toReal_nonneg`. Use `set a : ℝ := 4 * Real.sqrt B.I.n with ha`. Establish `ha0 : 0 ≤ a` using `by rw [ha]; positivity`. Use `set p := 2 * (B.I.n ^ 2 * B.I.f) with hp`.

Use `⟨Real.sqrt (C0 * K * Mx * (1 + a) ^ p), fun y => ?_⟩` and prove the remaining obligations. Establish `hτ : 0 < tau1 B.I y` using `GlobalTheory.TauLipschitz.trunc_pos B.I hn y`. Establish `hτ1 : tau1 B.I y ≤ 1`. Establish `: tau1 B.I y ≤ 1 / 2`. Unfold `GlobalTheory.Count.tau1`.

Conclude with `min_le_left _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu0 : 0 < (tau1 B.I y)⁻¹` using `inv_pos.2 hτ`. Establish `hu1 : 1 ≤ (tau1 B.I y)⁻¹`. Establish `h1` using `mul_le_mul_of_nonneg_right hτ1 hu0.le`.

Rewrite `h1` using `[mul_inv_cancel₀ hτ.ne', one_mul]`. Conclude with `h1`. Establish `hu2 : 1 ≤ ((tau1 B.I y)⁻¹) ^ 2` using `by nlinarith`. Establish `hfrac : a / tau1 B.I y ^ 2 = a * ((tau1 B.I y)⁻¹) ^ 2` using `by rw [div_eq_mul_inv, inv_pow]`. Establish `hbase : 1 + a / tau1 B.I y ^ 2 ≤ (1 + a) * ((tau1 B.I y)⁻¹) ^ 2`.

Rewrite using `[hfrac]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hX1 : 0 ≤ 1 + a / tau1 B.I y ^ 2`. Use `div_nonneg ha0 (sq_nonneg (tau1 B.I y))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpow : (1 + a / tau1 B.I y ^ 2) ^ p ≤ (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]`. Establish `hcube : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) → ∫ t in Set.pi Set.univ (fun _ : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => Set.Icc (0 : ℝ) (1 / (12 * (B.I.n : ℝ) ^ 5))), ‖F l (y …`. Introduce `l hl`.

Establish `h1` using `cube_bound B c (1 / (12 * (B.I.n : ℝ) ^ 5)) e E hn hg (fun v => (hc v).2.1) hE hs h3 h5 (Fv l) (F l) (hFv l) (hW (F l) (hFW l)).2.1 y`. Establish `h2 : Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal = K * (1 + a / tau1 B.I y ^ 2) ^ p`. Rewrite using `[hK, ha, hp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2]`.

Use `h1.trans ?_` and prove the remaining obligations. Establish `hX0 : 0 ≤ K * (1 + a / tau1 B.I y ^ 2) ^ p` using `mul_nonneg hK0 (pow_nonneg hX1 _)`. Conclude with `mul_le_mul_of_nonneg_left (hle l hl) hX0`. Establish `hmain` using `hsob F (fun l => (hFv l).1) (fun l i x => hD (F l) (hFW l) i x) y (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) hcube`. Establish `hsq : ‖f y‖ ^ 2 ≤ (Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2`.

Establish `hA : 0 ≤ C0 * K * Mx * (1 + a) ^ p` using `mul_nonneg (mul_nonneg (mul_nonneg hC0 hK0) hMx0) (pow_nonneg (by linarith) _)`. Rewrite using `[mul_pow, Real.sq_sqrt hA]`. Establish `hQ : 0 ≤ C0 * K * Mx` using `mul_nonneg (mul_nonneg hC0 hK0) hMx0`. Combine the equalities or inequalities in the displayed calculation. Establish `hnn : 0 ≤ Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p` using `mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hu0.le _)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem derivative_closed_class_bound : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  intro B hn hg
  classical
  refine ⟨2 * (B.I.n ^ 2 * B.I.f), ?_⟩
  intro W hW f hf

  choose E hE using fun v : InfinitePlace B.I.F => exists_re_trace_orthonormal_gLie (B.I.ε v)
  choose c hc using fun v : InfinitePlace B.I.F => GlobalTheory.GaugeConst.gauge_exists_pos_unique B.I.n (B.I.ε v)
  let e : Fin (Fintype.card (InfinitePlace B.I.F)) ≃ InfinitePlace B.I.F :=
    (Fintype.equivFin (InfinitePlace B.I.F)).symm

  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < B.I.n := by linarith
  have hp5 : (0 : ℝ) < (B.I.n : ℝ) ^ 5 := pow_pos hn0 5
  have h35 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 5 := pow_le_pow_right₀ hnr (by norm_num)
  have hden : (0 : ℝ) < 12 * (B.I.n : ℝ) ^ 5 := by linarith
  have hs : (0 : ℝ) < 1 / (12 * (B.I.n : ℝ) ^ 5) := div_pos one_pos hden
  have h3 : 12 * (B.I.n : ℝ) ^ 3 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  have h5 : 8 * (B.I.n : ℝ) ^ 5 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨C0, hC0, hsob⟩ := GlobalTheory.sobolev_iterated_one_parameter_subgroups_words B.I.GA
    (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)
    (fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat))) (1 / (12 * (B.I.n : ℝ) ^ 5)) hs
    (fun l => onePar_spec B _)

  have hder : ∀ g ∈ W, ∀ l : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ∃ g' ∈ W, ∀ y,
      HasDerivAt (fun t : ℝ => g (y * onePar B (atPlace B (e l.divNat) (E _ l.modNat)) t)) (g' y) 0 :=
    fun g hgW l => (hW g hgW).2.2 (e l.divNat) (E _ l.modNat)
  choose! D hDW hD using hder
  let F : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)) → B.I.GA → ℂ :=
    fun l => l.foldr (fun i g => D g i) f
  have hFW : ∀ l, F l ∈ W := by
    intro l
    induction l with
    | nil => exact hf
    | cons i l ih => exact hDW _ ih i
  have hrep : ∀ l, ∃ Fv, GlobalTheory.Dec.IsContRep B Fv (F l) := fun l => (hW (F l) (hFW l)).1
  choose Fv hFv using hrep

  set Mx : ℝ := ∑ k ∈ Finset.range ((Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) + 1), ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 with hMx
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hle : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) → ‖Fv l‖ ^ 2 ≤ Mx := by
    intro l hl
    calc ‖Fv l‖ ^ 2 = ‖Fv (List.ofFn l.get)‖ ^ 2 := by rw [List.ofFn_get]
      _ ≤ ∑ w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 :=
          Finset.single_le_sum (f := fun w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      _ ≤ Mx :=
          Finset.single_le_sum (f := fun k => ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hP : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => (hc v).1.le
  set K : ℝ := Real.exp B.I.f * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (Real.exp_pos _).le hP) ENNReal.toReal_nonneg
  set a : ℝ := 4 * Real.sqrt B.I.n with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set p := 2 * (B.I.n ^ 2 * B.I.f) with hp
  refine ⟨Real.sqrt (C0 * K * Mx * (1 + a) ^ p), fun y => ?_⟩
  have hτ : 0 < tau1 B.I y := GlobalTheory.TauLipschitz.trunc_pos B.I hn y
  have hτ1 : tau1 B.I y ≤ 1 := by
    have : tau1 B.I y ≤ 1 / 2 := by
      unfold GlobalTheory.Count.tau1
      exact min_le_left _ _
    linarith
  have hu0 : 0 < (tau1 B.I y)⁻¹ := inv_pos.2 hτ
  have hu1 : 1 ≤ (tau1 B.I y)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hτ1 hu0.le
    rw [mul_inv_cancel₀ hτ.ne', one_mul] at h1
    exact h1
  have hu2 : 1 ≤ ((tau1 B.I y)⁻¹) ^ 2 := by nlinarith
  have hfrac : a / tau1 B.I y ^ 2 = a * ((tau1 B.I y)⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
  have hbase : 1 + a / tau1 B.I y ^ 2 ≤ (1 + a) * ((tau1 B.I y)⁻¹) ^ 2 := by
    rw [hfrac]
    nlinarith
  have hX1 : 0 ≤ 1 + a / tau1 B.I y ^ 2 := by
    have := div_nonneg ha0 (sq_nonneg (tau1 B.I y))
    linarith
  have hpow : (1 + a / tau1 B.I y ^ 2) ^ p ≤ (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    calc (1 + a / tau1 B.I y ^ 2) ^ p ≤ ((1 + a) * ((tau1 B.I y)⁻¹) ^ 2) ^ p :=
          pow_le_pow_left₀ hX1 hbase p
      _ = (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]

  have hcube : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) →
      ∫ t in Set.pi Set.univ (fun _ : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => Set.Icc (0 : ℝ) (1 / (12 * (B.I.n : ℝ) ^ 5))),
        ‖F l (y * (List.ofFn fun i => onePar B (atPlace B (e i.divNat) (E _ i.modNat)) (t i)).prod)‖ ^ 2 ≤
        K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx := by
    intro l hl
    have h1 := cube_bound B c (1 / (12 * (B.I.n : ℝ) ^ 5)) e E hn hg (fun v => (hc v).2.1) hE hs h3 h5
      (Fv l) (F l) (hFv l) (hW (F l) (hFW l)).2.1 y
    have h2 : Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
        (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal = K * (1 + a / tau1 B.I y ^ 2) ^ p := by
      rw [hK, ha, hp]
      ring
    rw [h2] at h1
    refine h1.trans ?_
    have hX0 : 0 ≤ K * (1 + a / tau1 B.I y ^ 2) ^ p := mul_nonneg hK0 (pow_nonneg hX1 _)
    exact mul_le_mul_of_nonneg_left (hle l hl) hX0
  have hmain := hsob F (fun l => (hFv l).1) (fun l i x => hD (F l) (hFW l) i x) y
    (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) hcube
  have hsq : ‖f y‖ ^ 2 ≤ (Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    have hA : 0 ≤ C0 * K * Mx * (1 + a) ^ p :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hK0) hMx0) (pow_nonneg (by linarith) _)
    rw [mul_pow, Real.sq_sqrt hA]
    have hQ : 0 ≤ C0 * K * Mx := mul_nonneg (mul_nonneg hC0 hK0) hMx0
    calc ‖f y‖ ^ 2 ≤ C0 * (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) := hmain
      _ = (C0 * K * Mx) * (1 + a / tau1 B.I y ^ 2) ^ p := by ring
      _ ≤ (C0 * K * Mx) * ((1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left hpow hQ
      _ = C0 * K * Mx * (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by ring
  have hnn : 0 ≤ Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hu0.le _)
  calc ‖f y‖ = Real.sqrt (‖f y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * (tau1 B.I y)⁻¹ ^ p := Real.sqrt_sq hnn

end GlobalTheory.SobolevBound
