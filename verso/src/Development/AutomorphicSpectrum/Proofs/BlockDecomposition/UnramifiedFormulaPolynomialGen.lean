import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardPreimageHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeriesEqDens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterOrthogonality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianRepCountFourierExpansion

noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.LocalDens Filter Topology Polynomial

namespace GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨hTc, hdet⟩` from `hT`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, c * T.det = ϖ ^ 0 := by`. Take `⟨w, hw⟩` from `hdet.exists_left_inv`. Conclude with `⟨w, by simpa using hw⟩`. Establish `hσ` using `hU.fix_ϖ`.

Establish `hfin : ∀ k, Finite (R ⧸ lev ϖ k)` using `fun k => finite_lev (by`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[hU.card]`. Conclude with `pow_ne_zero _ (by have := hU.one_lt; omega)) k`. Establish `h1 : T * (c • T.adjugate) = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R)`.

Rewrite using `[Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc]`. Establish `h2 : cT σ (c • T.adjugate) * T = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R)`. Use `congrArg (cT σ) h1` as an intermediate fact. Rewrite `this` using `[cT_mul, hTc, cT_smul σ (ϖ ^ 0), cT_one, map_pow, hσ]`. Conclude with `this`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, t + σ t = 1 := by`. Take `⟨u, hu, -⟩` from `hU.basis`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `h3 : (u - σ u) * σ w = -1`. Use `congrArg σ hw` as an intermediate fact.

Simplify using `only [map_mul, map_sub, hU.inv, map_one] at this`. Take the linear combination `-this`. Establish `h4 : σ w = -w` using `by linear_combination (-σ w) * hw + w * h3`. Use `⟨u * w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h4]`.

Take the linear combination `hw`. Use `dens_step hfin hU.inv hσ S T _ hS.1 hTc (fun h hh hk => ?_)` and prove the remaining obligations. Rewrite `hk` using `[red_eq_iff]`. Use `choose C hC using hk`. Establish `hhT : h = T + ϖ ^ (0 + b + 1) • Matrix.of C`.

Use extensionality with `i j`. Use `hC i j` as an intermediate fact. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hCh : cT σ (Matrix.of C) = Matrix.of C`. Use extensionality with `i j`. Establish `e1` using `congrFun (congrFun (hh) i) j`. Establish `e2` using `congrArg σ (hC j i)`. Establish `e3` using `congrFun (congrFun hTc i) j`.

Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply] at e1 e3`. Simplify using `only [map_sub, map_mul, map_pow, hσ, e1, e3] at e2`. Use `(hU.reg.pow (0 + b + 1)) (a₁ := σ (C j i)) (a₂ := C i j) (by` as an intermediate fact. Simplify using `only [smul_eq_mul]`. Rewrite using `[← e2, hC i j])`.

Simplify `this` using `[cT]`. Take `⟨g, h', hgh, hhg, hg⟩` from `twist hσ ht hCh 0 b h1 h2`. Rewrite `hg` using `[← hhT]`. Rewrite using `[solCount_eq, ← sol_congr σ ϖ S _ hg, ← solCount_eq]`. Conclude with `solCount_congr hσ S T g h' _ hgh hhg`.
-/
theorem densAt_succ {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T) (b : ℕ) :
    densAt σ ϖ S T (0 + b + 1) = densAt σ ϖ S T (0 + b + 1 + 1) := by
  obtain ⟨hTc, hdet⟩ := hT
  obtain ⟨c, hc⟩ : ∃ c, c * T.det = ϖ ^ 0 := by
    obtain ⟨w, hw⟩ := hdet.exists_left_inv
    exact ⟨w, by simpa using hw⟩
  have hσ := hU.fix_ϖ
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hU.card]
    exact pow_ne_zero _ (by have := hU.one_lt; omega)) k
  have h1 : T * (c • T.adjugate) = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc]
  have h2 : cT σ (c • T.adjugate) * T = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    have := congrArg (cT σ) h1
    rw [cT_mul, hTc, cT_smul σ (ϖ ^ 0), cT_one, map_pow, hσ] at this
    exact this
  obtain ⟨t, ht⟩ : ∃ t, t + σ t = 1 := by
    obtain ⟨u, hu, -⟩ := hU.basis
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : (u - σ u) * σ w = -1 := by
      have := congrArg σ hw
      simp only [map_mul, map_sub, hU.inv, map_one] at this
      linear_combination -this
    have h4 : σ w = -w := by linear_combination (-σ w) * hw + w * h3
    refine ⟨u * w, ?_⟩
    rw [map_mul, h4]
    linear_combination hw
  refine dens_step hfin hU.inv hσ S T _ hS.1 hTc (fun h hh hk => ?_)
  rw [red_eq_iff] at hk
  choose C hC using hk
  have hhT : h = T + ϖ ^ (0 + b + 1) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hCh : cT σ (Matrix.of C) = Matrix.of C := by
    ext i j
    have e1 := congrFun (congrFun (hh) i) j
    have e2 := congrArg σ (hC j i)
    have e3 := congrFun (congrFun hTc i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at e1 e3
    simp only [map_sub, map_mul, map_pow, hσ, e1, e3] at e2
    have := (hU.reg.pow (0 + b + 1)) (a₁ := σ (C j i)) (a₂ := C i j) (by
      simp only [smul_eq_mul]
      rw [← e2, hC i j])
    simpa [cT] using this
  obtain ⟨g, h', hgh, hhg, hg⟩ := twist hσ ht hCh 0 b h1 h2
  rw [← hhT] at hg
  rw [solCount_eq, ← sol_congr σ ϖ S _ hg, ← solCount_eq]
  exact solCount_congr hσ S T g h' _ hgh hhg

/- English proof (translation)
Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ k hk ih`. Take `⟨b, rfl⟩ : ∃ b, k = 0 + b + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[← densAt_succ hU S T hS hT b, ih]`.
-/
theorem densAt_eq_densAt_one_of_isUnimod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = densAt σ ϖ S T 1 := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = 0 + b + 1 := ⟨k - 1, by omega⟩
    rw [← densAt_succ hU S T hS hT b, ih]

/- English proof (translation)
Establish `h1 : Tendsto (densAt σ ϖ S T) atTop (𝓝 (densAt σ ϖ S T 1))`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with j hj`. Conclude with `(densAt_eq_densAt_one_of_isUnimod hU S T hS hT j hj).symm`. Rewrite using `[densAt_eq_densAt_one_of_isUnimod hU S T hS hT k hk]`.

Conclude with `tendsto_nhds_unique h1 hα`.
-/
theorem densAt_eq_of_isDens {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    {α : ℝ} (hα : IsDens σ ϖ S T α) (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = α := by
  have h1 : Tendsto (densAt σ ϖ S T) atTop (𝓝 (densAt σ ϖ S T 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (densAt_eq_densAt_one_of_isUnimod hU S T hS hT j hj).symm
  rw [densAt_eq_densAt_one_of_isUnimod hU S T hS hT k hk]
  exact tendsto_nhds_unique h1 hα

/- English proof (translation)
Assemble the required witnesses or components as `⟨cT_one σ, by simp⟩`.
-/
theorem isUnimod_one (σ : R →+* R) (m : ℕ) : IsUnimod σ (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨cT_one σ, by simp⟩

/- English proof (translation)
Introduce `hF R _ σ ϖ q ε hR ψ hψ n T hT k hk t`. Establish `hfin : ∀ k, Finite (R ⧸ lev ϖ k)` using `fun k => finite_lev (by`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[hR.card]`. Conclude with `pow_ne_zero _ (by have := hR.one_lt; omega)) k`.

Use `letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _`. Use `haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) := inferInstanceAs (Finite (Fin n → Fin n → R ⧸ lev ϖ k))`. Use `haveI : Finite (hermMod σ ϖ n k) := Subtype.finite`. Use `letI : Fintype (hermMod σ ϖ n k) := Fintype.ofFinite _`. Establish `hq1 : 1 < q` using `hR.one_lt`.

Establish `hqC : (q : ℂ) ≠ 0` using `by exact_mod_cast (by omega : q ≠ 0)`. Establish `hε : (ε : ℂ) ^ 2 = 1`. Apply the tactic sequence `rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp`. Establish `hnε : ‖(ε : ℂ)‖ = 1`. Apply the tactic sequence `rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp`.

Set `P : ℂ[X]` to `∑ B : hermMod σ ϖ n k, C (ψ k (Matrix.trace (red ϖ k T * B.1))) * X ^ Nat.log (q ^ 2) (nuAt ϖ B.1)`. Set `Q : ℂ[X]` to `∏ i : Fin n, (1 - X * C (((ε : ℂ) * q) ^ (i : ℕ)))`. Establish `hP : ∀ x : ℂ, P.eval x = ∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) * x ^ Nat.log (q ^ 2) (nuAt ϖ B.1)`. Introduce `x`. Rewrite using `[tsum_fintype]`.

Simplify using `[P, Polynomial.eval_finset_sum]`. Establish `hQ : ∀ x : ℂ, Q.eval x = ∏ i : Fin n, (1 - x * ((ε : ℂ) * q) ^ (i : ℕ))`. Introduce `x`. Simplify using `[Q, Polynomial.eval_prod]`. Establish `hval : ∀ m, n ≤ m → P.eval (((ε : ℂ) / q) ^ m) = Q.eval (((ε : ℂ) / q) ^ m)`.

Introduce `m hm`. Establish `hS` using `isUnimod_one σ m`. Establish `hs : siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ (1 : Matrix (Fin m) (Fin m) R) T k : ℝ) : ℂ)` using `GlobalTheory.CompanionTheory.SiegLoc.level_identity R σ ϖ q ε hR ψ hψ m n k 1 T hS.1 hT.1 (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod R σ ϖ q ε hR ψ hψ n k) (fun B hB => GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hψ hε k 1 hS B hB)`. Establish `hc : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m`. Rewrite using `[div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]`.

Rewrite using `[hP, hQ]`. Unfold `siegAt at hs`. Rewrite `hs` using `[hc]`. Rewrite using `[hs, densAt_eq_of_isDens hR 1 T hS hT (hF R σ ϖ q ε hR m n hm 1 T hS hT) k hk]`. Use `push_cast`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi : (i : ℕ) ≤ m` using `by have := i.2; omega`. Establish `e1 : ((ε : ℂ) / q) ^ m = ((ε : ℂ) / q) ^ (m - (i : ℕ)) * ((ε : ℂ) / q) ^ (i : ℕ)`. Rewrite using `[← pow_add, Nat.sub_add_cancel hi]`. Establish `e2 : ((ε : ℂ) / q) ^ (i : ℕ) * ((ε : ℂ) * q) ^ (i : ℕ) = 1`.

Rewrite using `[← mul_pow]`. Establish `: (ε : ℂ) / q * ((ε : ℂ) * q) = 1`. Clear the denominators using the available nonvanishing facts. Simplify using `using hε`. Rewrite using `[this, one_pow]`.

Rewrite using `[e1, mul_assoc, e2, mul_one]`. Establish `hinj : Function.Injective (fun j : ℕ => ((ε : ℂ) / q) ^ (n + j))`. Introduce `a b hab`. Establish `h1 : ‖((ε : ℂ) / q) ^ (n + a)‖ = ‖((ε : ℂ) / q) ^ (n + b)‖` using `congrArg norm hab`. Establish `hnorm : ‖(ε : ℂ) / q‖ = (q : ℝ)⁻¹`.

Rewrite using `[norm_div, hnε]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[norm_pow, norm_pow, hnorm]`. Establish `hq0 : (0 : ℝ) < (q : ℝ)⁻¹`. Establish `: (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`.

Check the signs of the components of the expression. Establish `hq2 : (q : ℝ)⁻¹ ≠ 1`. Establish `: (1 : ℝ) < q` using `by exact_mod_cast hq1`. Conclude with `(inv_lt_one_of_one_lt₀ this).ne`. Use `pow_right_injective₀ hq0 hq2 h1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hPQ : P = Q` using `Polynomial.eq_of_infinite_eval_eq P Q (Set.infinite_of_injective_forall_mem hinj fun j => hval (n + j) (by omega))`. Use `congrArg (Polynomial.eval t) hPQ` as an intermediate fact. Rewrite `this` using `[hP, hQ]`. Conclude with `this`.
-/
theorem unrPoly : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  intro hF R _ σ ϖ q ε hR ψ hψ n T hT k hk t
  classical
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hR.card]
    exact pow_ne_zero _ (by have := hR.one_lt; omega)) k
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
    inferInstanceAs (Finite (Fin n → Fin n → R ⧸ lev ϖ k))
  haveI : Finite (hermMod σ ϖ n k) := Subtype.finite
  letI : Fintype (hermMod σ ϖ n k) := Fintype.ofFinite _
  have hq1 : 1 < q := hR.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnε : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  let P : ℂ[X] := ∑ B : hermMod σ ϖ n k,
    C (ψ k (Matrix.trace (red ϖ k T * B.1))) * X ^ Nat.log (q ^ 2) (nuAt ϖ B.1)
  let Q : ℂ[X] := ∏ i : Fin n, (1 - X * C (((ε : ℂ) * q) ^ (i : ℕ)))
  have hP : ∀ x : ℂ, P.eval x = ∑' B : hermMod σ ϖ n k,
      ψ k (Matrix.trace (red ϖ k T * B.1)) * x ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    intro x
    rw [tsum_fintype]
    simp [P, Polynomial.eval_finset_sum]
  have hQ : ∀ x : ℂ, Q.eval x = ∏ i : Fin n, (1 - x * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro x
    simp [Q, Polynomial.eval_prod]
  have hval : ∀ m, n ≤ m → P.eval (((ε : ℂ) / q) ^ m) = Q.eval (((ε : ℂ) / q) ^ m) := by
    intro m hm
    have hS := isUnimod_one σ m
    have hs : siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ (1 : Matrix (Fin m) (Fin m) R) T k : ℝ) : ℂ) :=
      GlobalTheory.CompanionTheory.SiegLoc.level_identity R σ ϖ q ε hR ψ hψ m n k 1 T hS.1 hT.1
        (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod R σ ϖ q ε hR ψ hψ n k)
        (fun B hB => GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hψ hε k 1 hS B hB)
    have hc : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
      rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hP, hQ]
    unfold siegAt at hs
    rw [hc] at hs
    rw [hs, densAt_eq_of_isDens hR 1 T hS hT (hF R σ ϖ q ε hR m n hm 1 T hS hT) k hk]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := by have := i.2; omega
    have e1 : ((ε : ℂ) / q) ^ m = ((ε : ℂ) / q) ^ (m - (i : ℕ)) * ((ε : ℂ) / q) ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have e2 : ((ε : ℂ) / q) ^ (i : ℕ) * ((ε : ℂ) * q) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      have : (ε : ℂ) / q * ((ε : ℂ) * q) = 1 := by
        field_simp
        simpa using hε
      rw [this, one_pow]
    rw [e1, mul_assoc, e2, mul_one]
  have hinj : Function.Injective (fun j : ℕ => ((ε : ℂ) / q) ^ (n + j)) := by
    intro a b hab
    have h1 : ‖((ε : ℂ) / q) ^ (n + a)‖ = ‖((ε : ℂ) / q) ^ (n + b)‖ := congrArg norm hab
    have hnorm : ‖(ε : ℂ) / q‖ = (q : ℝ)⁻¹ := by
      rw [norm_div, hnε]
      simp
    rw [norm_pow, norm_pow, hnorm] at h1
    have hq0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    have hq2 : (q : ℝ)⁻¹ ≠ 1 := by
      have : (1 : ℝ) < q := by exact_mod_cast hq1
      exact (inv_lt_one_of_one_lt₀ this).ne
    have := pow_right_injective₀ hq0 hq2 h1
    omega
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q
    (Set.infinite_of_injective_forall_mem hinj fun j => hval (n + j) (by omega))
  have := congrArg (Polynomial.eval t) hPQ
  rw [hP, hQ] at this
  exact this

end GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

end
