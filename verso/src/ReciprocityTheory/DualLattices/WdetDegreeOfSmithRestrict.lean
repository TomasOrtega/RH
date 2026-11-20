import ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.SumValCoord
import ReciprocityTheory.DualLattices.VDetEqOneOfIntegral

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

/- English proof (translation)
Set `f : (ι → S) →ₗ[S] (ι → S)` to `Matrix.mulVecLin P`. Establish `hidem : ∀ x, f (f x) = f x` using `fun x => by`. Simplify using `only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]`. Set `M` to `LinearMap.range f`. Establish `hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨y, x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hidem]`. Use `haveI : Module.Projective S M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit`.

Use `haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing`. Set `b` to `Module.finBasis S M`. Establish `hBw : Matrix.mulVecLin (Matrix.of fun i j => (b j : ι → S) i) = M.subtype ∘ₗ b.equivFun.symm.toLinearMap`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `c`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]`. Use `⟨Module.finrank S M, Matrix.of fun i j => (b j : ι → S) i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hBw, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]`. Rewrite using `[hBw, LinearMap.ker_eq_bot]`.

Conclude with `M.injective_subtype.comp b.equivFun.symm.injective`.
-/
lemma idem_basis {S : Type} [CommRing S] [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι S) (hP : P * P = P) : ∃ (r : ℕ) (Bw : Matrix ι (Fin r) S),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin P) ∧
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ := by
  classical
  let f : (ι → S) →ₗ[S] (ι → S) := Matrix.mulVecLin P
  have hidem : ∀ x, f (f x) = f x := fun x => by
    simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  let M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, x, rfl⟩
    apply Subtype.ext
    simp [hidem]
  haveI : Module.Projective S M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis S M
  have hBw : Matrix.mulVecLin (Matrix.of fun i j => (b j : ι → S) i) =
      M.subtype ∘ₗ b.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank S M, Matrix.of fun i j => (b j : ι → S) i, ?_, ?_⟩
  · rw [hBw, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · rw [hBw, LinearMap.ker_eq_bot]
    exact M.injective_subtype.comp b.equivFun.symm.injective

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw d X hd hX`. Establish `hv` using `hSet.integers`. Establish `hidem : e w * e w = e w` using `by rw [horth, if_pos rfl]`. Establish `hρidem : H.ρ (e w) * H.ρ (e w) = H.ρ (e w)` using `by rw [← map_mul, hidem]`. Take `⟨r, Bw, hrange, hker⟩` from `idem_basis (H.ρ (e w)) hρidem`.

Take `⟨Λ, dj, hΛ, hdjspan, hdjv, hXeq⟩` from `hS p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker X hX`. Take `⟨AW, hAWc, hOm⟩` from `hR p g C v R O σ cp hSet H (e w) hidem r Bw hrange hker d hd`. Establish `hcl` using `fun j => hC p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker (Λ j) (dj j) (hdjspan j) (hdjv j)`. Use `choose x hxmem hxapp using hcl`. Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`.

Establish `hcp0 : v (algebraMap R C cp) ≠ 0`. Introduce `h0`. Establish `h1` using `hSet.cp_val`. Rewrite `h1` using `[h0, zero_pow (by omega)]`. Conclude with `hSet.p_ne h1.symm`.

Establish `hdj0 : ∀ j, algebraMap R C (dj j) ≠ 0` using `fun j h0 => by`. Establish `h1` using `hdjv j`. Rewrite `h1` using `[h0, map_zero, le_zero_iff]`. Conclude with `hcp0 h1`. Establish `hpC : v (p : C) < 1`.

Establish `h1` using `hSet.p_lt`. Rewrite `h1` using `[map_natCast]`. Then use the resulting hypothesis. Use `set u : Fin r → (Fin r → ZMod p) → C := fun j y => (algebraMap R C (dj j))⁻¹ * x j y with hudef`. Establish `hred : ∀ y : Fin r → ZMod p, (fun i => PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p])) = y`. Introduce `y`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hU2 : ∀ j y, v (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) < 1`. Introduce `j y`. Establish `h1` using `hxapp j (fun i => (((y i).val : ℕ) : ℤ_[p]))`.

Rewrite `h1` using `[hred y]`. Simplify using `only [map_natCast] at h1`. Establish `e1 : u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R)) = (x j y - algebraMap R C (dj j * ∑ i, Λ j i * ((y i).val : R))) / algebraMap R C (dj j)`. Simplify using `only [hudef, map_mul]`. Clear denominators, using `[hdj0 j]` for the nonvanishing conditions.

Rewrite using `[e1, map_div₀]`. Conclude with `(div_lt_one (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (hdj0 j)))).2 h1`. Establish `hU1 : ∀ j y, v (u j y) ≤ 1`. Introduce `j y`. Establish `e1 : u j y = (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) + algebraMap R C (∑ i, Λ j i * ((y i).val : R))` using `by ring`.

Rewrite using `[e1]`. Conclude with `(Valuation.map_add v _ _).trans (max_le (hU2 j y).le (hv.map_le_one _))`. Establish `h5` using `(u5 p C v R hv hpC (Fin r) Λ u hΛ hU1 hU2).2 (fun j => algebraMap R C (dj j))`. Establish `hxu : ∀ j y, algebraMap R C (dj j) * u j y = x j y` using `fun j y => by`. Simplify using `only [hudef]`.

Rewrite using `[mul_inv_cancel_left₀ (hdj0 j)]`. Simplify using `only [hxu] at h5`. Establish `hxW : ∀ j, x j ∈ AW.carrier` using `fun j => hAWc ▸ hxmem j`. Establish `hpow : ∀ (f : (Fin r → ZMod p) → C), f ∈ AW.carrier → ∀ k : ℕ, f ^ k ∈ AW.carrier`. Introduce `f hf k`.

Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `AW.one_mem`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `AW.mul_mem _ _ ih hf`.

Establish `hmon : ∀ α : Fin r → ZMod p, (fun y => ∏ j, x j y ^ (α j).val) ∈ AW.carrier`. Introduce `α`. Establish `key : ∀ s : Finset (Fin r), (∏ j ∈ s, x j ^ (α j).val) ∈ AW.carrier`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => rw [Finset.prod_empty]`. Conclude with `AW.one_mem`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `AW.mul_mem _ _ (hpow _ (hxW a) _) ih`.

Use `key Finset.univ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Simplify using `[Finset.prod_apply]`. Take `⟨B, hBu, hBc⟩` from `AW.lat`. Establish `hcol : ∀ α : Fin r → ZMod p, ∃ c : (Fin r → ZMod p) → R, ∑ j', c j' • (fun y => B y j') = fun y => ∏ j, x j y ^ (α j).val`.

Introduce `α`. Establish `h1` using `hmon α`. Rewrite `h1` using `[hBc]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun R).1 h1`. Use `choose c hc using hcol`.

Establish `hMon : (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val) = B * Matrix.of fun j' α => algebraMap R C (c α j')`. Use extensionality with `y α`. Establish `e` using `congrFun (hc α) y`. Simplify using `only [Finset.sum_apply, Pi.smul_apply] at e`. Rewrite using `[Matrix.of_apply, ← e, Matrix.mul_apply]`.

Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvMon : v (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val).det ≤ v B.det`. Rewrite using `[hMon, Matrix.det_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hColen : HasColen R v AW.carrier (v B.det)` using `⟨B, hBc, rfl⟩`. Establish `hN : ∀ y : Fin r → ZMod p, p • y = 0`. Introduce `y`. Use function extensionality and compare the values at `i`.

Simplify using `[nsmul_eq_mul, ZMod.natCast_self]`. Establish `h4` using `u4 p C v R hv hpC (Fin r → ZMod p) hN AW (v B.det) _ hColen hOm`. Establish `hcard : Fintype.card (Fin r → ZMod p) = p ^ r` using `by simp`. Rewrite `h4` using `[hcard]`. Use `set Y := ∏ j, v (algebraMap R C (dj j)) with hYdef`.

Use `set K := p ^ (Fintype.card (Fin r) - 1) * (p * (p - 1) / 2) with hKdef`. Establish `hYK : Y ^ K ≤ v B.det`. Rewrite using `[hYdef, ← Finset.prod_pow]`. Conclude with `h5 ▸ hvMon`. Establish `hchain : Y ^ (2 * K) ≤ (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hSet.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hXeq]`.

Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `hY1 : Y = 1` using `by simp [hYdef]`. Rewrite `hchain`, the goal using `[hY1]`. Rewrite `hchain` using `[one_pow]`.

Break down `Nat.eq_zero_or_pos d with hd0 | hd0` into its components or cases. Substitute `hd0` using the available equality. Simplify using the standard rewrite rules. It suffices to derive a contradiction. Establish `hlt : (v (algebraMap R C cp) ^ d) ^ (p ^ 0 * (p - 1)) < 1`.

Use `pow_lt_one₀ zero_le' (pow_lt_one₀ zero_le' ?_ (by omega)) (by simp; omega)` and prove the remaining obligations. Establish `h1` using `hSet.cp_val`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `h2 : 1 ≤ v (algebraMap R C cp) ^ (p - 1)` using `one_le_pow₀ hge`.

Rewrite `h2` using `[h1]`. Conclude with `absurd hSet.p_lt (not_lt.2 h2)`. Conclude with `absurd hchain (not_le.2 hlt)`. Establish `h2K : 2 * K = p ^ r * (p - 1)`. Rewrite using `[hKdef, Fintype.card_fin, ← mul_assoc, mul_comm 2, mul_assoc, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self p)]`.

Establish `: p ^ (r - 1) * p = p ^ r` using `by rw [← pow_succ]; congr 1; omega`. Rewrite using `[← mul_assoc, this]`. Rewrite `hchain` using `[h2K]`. Conclude with `(pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))).1 hchain`.
-/
theorem wdetDegree_of_smith_restrict (hS : EigenQuotientSmithStatement) (hR : RestrictedHopfOrderStatement) (hC : RestrictedHopfOrderApproximationStatement) :
    WdetDegStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw d X hd hX
  classical
  have hv := hSet.integers
  have hidem : e w * e w = e w := by rw [horth, if_pos rfl]
  have hρidem : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, hidem]
  obtain ⟨r, Bw, hrange, hker⟩ := idem_basis (H.ρ (e w)) hρidem
  obtain ⟨Λ, dj, hΛ, hdjspan, hdjv, hXeq⟩ :=
    hS p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker X hX
  obtain ⟨AW, hAWc, hOm⟩ := hR p g C v R O σ cp hSet H (e w) hidem r Bw hrange hker d hd
  have hcl := fun j => hC p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange
    hker (Λ j) (dj j) (hdjspan j) (hdjv j)
  choose x hxmem hxapp using hcl
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcp0 : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h1 := hSet.cp_val
    rw [h0, zero_pow (by omega)] at h1
    exact hSet.p_ne h1.symm
  have hdj0 : ∀ j, algebraMap R C (dj j) ≠ 0 := fun j h0 => by
    have h1 := hdjv j
    rw [h0, map_zero, le_zero_iff] at h1
    exact hcp0 h1
  have hpC : v (p : C) < 1 := by
    have h1 := hSet.p_lt
    rwa [map_natCast] at h1
  set u : Fin r → (Fin r → ZMod p) → C := fun j y => (algebraMap R C (dj j))⁻¹ * x j y with hudef
  have hred : ∀ y : Fin r → ZMod p, (fun i => PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p])) = y := by
    intro y
    funext i
    simp
  have hU2 : ∀ j y, v (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) < 1 := by
    intro j y
    have h1 := hxapp j (fun i => (((y i).val : ℕ) : ℤ_[p]))
    rw [hred y] at h1
    simp only [map_natCast] at h1
    have e1 : u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R)) =
        (x j y - algebraMap R C (dj j * ∑ i, Λ j i * ((y i).val : R))) / algebraMap R C (dj j) := by
      simp only [hudef, map_mul]
      field_simp [hdj0 j]
    rw [e1, map_div₀]
    exact (div_lt_one (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (hdj0 j)))).2 h1
  have hU1 : ∀ j y, v (u j y) ≤ 1 := by
    intro j y
    have e1 : u j y = (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) +
        algebraMap R C (∑ i, Λ j i * ((y i).val : R)) := by ring
    rw [e1]
    exact (Valuation.map_add v _ _).trans (max_le (hU2 j y).le (hv.map_le_one _))
  have h5 := (u5 p C v R hv hpC (Fin r) Λ u hΛ hU1 hU2).2 (fun j => algebraMap R C (dj j))
  have hxu : ∀ j y, algebraMap R C (dj j) * u j y = x j y := fun j y => by
    simp only [hudef]
    rw [mul_inv_cancel_left₀ (hdj0 j)]
  simp only [hxu] at h5
  have hxW : ∀ j, x j ∈ AW.carrier := fun j => hAWc ▸ hxmem j
  have hpow : ∀ (f : (Fin r → ZMod p) → C), f ∈ AW.carrier → ∀ k : ℕ, f ^ k ∈ AW.carrier := by
    intro f hf k
    induction k with
    | zero => rw [pow_zero]; exact AW.one_mem
    | succ k ih => rw [pow_succ]; exact AW.mul_mem _ _ ih hf
  have hmon : ∀ α : Fin r → ZMod p, (fun y => ∏ j, x j y ^ (α j).val) ∈ AW.carrier := by
    intro α
    have key : ∀ s : Finset (Fin r), (∏ j ∈ s, x j ^ (α j).val) ∈ AW.carrier := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact AW.one_mem
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact AW.mul_mem _ _ (hpow _ (hxW a) _) ih
    convert key Finset.univ using 1
    funext y
    simp [Finset.prod_apply]
  obtain ⟨B, hBu, hBc⟩ := AW.lat
  have hcol : ∀ α : Fin r → ZMod p, ∃ c : (Fin r → ZMod p) → R,
      ∑ j', c j' • (fun y => B y j') = fun y => ∏ j, x j y ^ (α j).val := by
    intro α
    have h1 := hmon α
    rw [hBc] at h1
    exact (Submodule.mem_span_range_iff_exists_fun R).1 h1
  choose c hc using hcol
  have hMon : (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val) =
      B * Matrix.of fun j' α => algebraMap R C (c α j') := by
    ext y α
    have e := congrFun (hc α) y
    simp only [Finset.sum_apply, Pi.smul_apply] at e
    rw [Matrix.of_apply, ← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [Matrix.of_apply, Algebra.smul_def]
    ring
  have hvMon : v (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val).det ≤ v B.det := by
    rw [hMon, Matrix.det_mul, map_mul]
    calc v B.det * v (Matrix.of fun j' α => algebraMap R C (c α j')).det ≤ v B.det * 1 :=
          mul_le_mul' le_rfl (IsIntegralMat.det_le_one (v := v) fun j' α => hv.map_le_one _)
      _ = v B.det := mul_one _
  have hColen : HasColen R v AW.carrier (v B.det) := ⟨B, hBc, rfl⟩
  have hN : ∀ y : Fin r → ZMod p, p • y = 0 := by
    intro y
    funext i
    simp [nsmul_eq_mul, ZMod.natCast_self]
  have h4 := u4 p C v R hv hpC (Fin r → ZMod p) hN AW (v B.det) _ hColen hOm
  have hcard : Fintype.card (Fin r → ZMod p) = p ^ r := by simp
  rw [hcard] at h4
  set Y := ∏ j, v (algebraMap R C (dj j)) with hYdef
  set K := p ^ (Fintype.card (Fin r) - 1) * (p * (p - 1) / 2) with hKdef
  have hYK : Y ^ K ≤ v B.det := by
    rw [hYdef, ← Finset.prod_pow]
    exact h5 ▸ hvMon
  have hchain : Y ^ (2 * K) ≤ (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
    calc Y ^ (2 * K) = (Y ^ K) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ v B.det ^ 2 := by gcongr
      _ ≤ (v (algebraMap R C (p : R)) ^ d) ^ p ^ r := h4
      _ = (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
        rw [← hSet.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
  rw [hXeq]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hY1 : Y = 1 := by simp [hYdef]
    rw [hY1] at hchain ⊢
    rw [one_pow] at hchain
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp
    · exfalso
      have hlt : (v (algebraMap R C cp) ^ d) ^ (p ^ 0 * (p - 1)) < 1 := by
        refine pow_lt_one₀ zero_le' (pow_lt_one₀ zero_le' ?_ (by omega)) (by simp; omega)
        have h1 := hSet.cp_val
        by_contra hge
        push_neg at hge
        have h2 : 1 ≤ v (algebraMap R C cp) ^ (p - 1) := one_le_pow₀ hge
        rw [h1] at h2
        exact absurd hSet.p_lt (not_lt.2 h2)
      exact absurd hchain (not_le.2 hlt)
  · have h2K : 2 * K = p ^ r * (p - 1) := by
      rw [hKdef, Fintype.card_fin, ← mul_assoc, mul_comm 2, mul_assoc,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self p)]
      have : p ^ (r - 1) * p = p ^ r := by rw [← pow_succ]; congr 1; omega
      rw [← mul_assoc, this]
    rw [h2K] at hchain
    exact (pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))).1 hchain

end ReciprocityTheory.PGsh.Up
