import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub

open Formalism.BasicNotions UpperTheory.TP.RP MvPolynomial

namespace UpperTheory.TP.RP

/- English proof (translation)
Simplify using `only [rightSub, xv, aeval_X]`.
-/
private theorem rightSub_xv {n d : ℕ} (g : Matrix (Fin d) (Fin d) ℂ) (b : Fin n) (c : Fin d) :
    rightSub g (xv b c) = ∑ a, C (g a c) * xv b a := by
  simp only [rightSub, xv, aeval_X]

private noncomputable def sSub (n d : ℕ) : MvPolynomial (Fin d × Fin d) ℂ →ₐ[ℂ] PP n d :=
  aeval fun v => if hv : (v.2 : ℕ) < n then xv ⟨v.2, hv⟩ v.1 else 0

/- English proof (translation)
Simplify using `only [sSub, aeval_X]`.
-/
private theorem sSub_X {n d : ℕ} (a b : Fin d) :
    sSub n d (X (a, b)) = if hv : (b : ℕ) < n then xv ⟨b, hv⟩ a else 0 := by
  simp only [sSub, aeval_X]

/- English proof (translation)
Establish `e : (sSub n d).comp (Formalism.GradedWeylDivisibility.rowAct ℂ g.transpose) = (rightSub g).comp (sSub n d)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, b⟩`. Simplify using `only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, Matrix.transpose_apply, algHom_C, sSub_X]`. Distinguish the cases in `hb : (b : ℕ) < n`.

Simplify using `[hb, rightSub_xv, algebraMap_eq]`. Simplify using `[hb]`. Conclude with `DFunLike.congr_fun e f`.
-/
private theorem sSub_rowAct {n d : ℕ} (g : Matrix (Fin d) (Fin d) ℂ)
    (f : MvPolynomial (Fin d × Fin d) ℂ) :
    sSub n d (Formalism.GradedWeylDivisibility.rowAct ℂ g.transpose f) = rightSub g (sSub n d f) := by
  have e : (sSub n d).comp (Formalism.GradedWeylDivisibility.rowAct ℂ g.transpose) = (rightSub g).comp (sSub n d) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, b⟩
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, Matrix.transpose_apply,
      algHom_C, sSub_X]
    by_cases hb : (b : ℕ) < n
    · simp [hb, rightSub_xv, algebraMap_eq]
    · simp [hb]
  exact DFunLike.congr_fun e f

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[AlgHom.map_det, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Establish `hq : ((Fin.castLE hn q : Fin n) : ℕ) = q` using `rfl`.

Simplify using `[sSub_X, ofTall, xv, show (q : ℕ) < n by omega]`. Both sides reduce to the same expression.
-/
private theorem sSub_lp {n d s : ℕ} (hd : s ≤ d) (hn : s ≤ n) :
    sSub n d (Formalism.GradedWeylDivisibility.lpMinor ℂ s hd hd) = ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ s hd hn) := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext p q
  have hq : ((Fin.castLE hn q : Fin n) : ℕ) = q := rfl
  simp [sSub_X, ofTall, xv, show (q : ℕ) < n by omega]
  rfl

private noncomputable def dTop {n d : ℕ} (h : n ≤ d) : PP n d :=
  ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ n h le_rfl)

/- English proof (translation)
Establish `hM : dTop (le_refl d) = (Matrix.of fun p q : Fin d => (xv q p : PP d d)).det`. Unfold `dTop Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`.

Simplify using `[ofTall, xv]`. Rewrite using `[hM, AlgHom.map_det]`. Establish `e : (rightSub g).mapMatrix (Matrix.of fun p q : Fin d => (xv q p : PP d d)) = (g.map C).transpose * Matrix.of fun p q : Fin d => (xv q p : PP d d)` using `by ext1 p q`. Simplify using `[Matrix.mul_apply, rightSub_xv]`. Rewrite using `[e, Matrix.det_mul, Matrix.det_transpose]`.

Use `congr 1`. Conclude with `(RingHom.map_det (C : ℂ →+* PP d d) g).symm`.
-/
private theorem rightSub_dTop {d : ℕ} (g : Matrix (Fin d) (Fin d) ℂ) :
    rightSub g (dTop (le_refl d)) = C g.det * dTop (le_refl d) := by
  have hM : dTop (le_refl d) = (Matrix.of fun p q : Fin d => (xv q p : PP d d)).det := by
    unfold dTop Formalism.GradedWeylDivisibility.lpMinor
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [ofTall, xv]
  rw [hM, AlgHom.map_det]
  have e : (rightSub g).mapMatrix (Matrix.of fun p q : Fin d => (xv q p : PP d d)) =
      (g.map C).transpose * Matrix.of fun p q : Fin d => (xv q p : PP d d) := by
    ext1 p q
    simp [Matrix.mul_apply, rightSub_xv]
  rw [e, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (C : ℂ →+* PP d d) g).symm

/- English proof (translation)
Unfold `joint Formalism.GradedWeylDivisibility.hw`. Rewrite using `[map_prod, map_prod]`. Use `symm`. Apply `Fintype.prod_of_injective (Fin.castLE h) (Fin.castLE_injective h)` to reduce the goal to its premises. Introduce `i hi`.

Establish `hin : ¬ (i : ℕ) < n` using `fun hh => hi ⟨⟨i, hh⟩, Fin.ext rfl⟩`. Establish `: ν i = 0` using `by rw [hν]; simp [hin]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Introduce `k`.

Establish `hk1 : (k : ℕ) + 1 ≤ n` using `k.2`. Rewrite using `[map_pow, map_pow]`. Establish `e1` using `sSub_lp (n := n) (d := d) (s := (k : ℕ) + 1) (by omega) hk1`. Establish `a : ν (Fin.castLE h k) = μ k` using `by rw [hν]; simp`. Establish `b : Formalism.GradedWeylDivisibility.nuNext ν (Fin.castLE h k) = Formalism.GradedWeylDivisibility.nuNext μ k`.

Unfold `Formalism.GradedWeylDivisibility.nuNext`. Distinguish the cases in `hk : (k : ℕ) + 1 < n`. Simplify using `[hk, show (k : ℕ) + 1 < d by omega, hν]`. Simplify using `[hk, show (k : ℕ) + 1 < d by omega, hν]`. Rewrite using `[a, b]`.

Conclude with `congrArg (· ^ _) e1.symm`.
-/
private theorem hw_lt {n d : ℕ} (h : n ≤ d) (hlt : n < d) (ν : Fin d → ℕ) (μ : Fin n → ℕ)
    (hν : ∀ k : Fin d, ν k = if hk : (k : ℕ) < n then μ ⟨k, hk⟩ else 0) :
    sSub n d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) = joint h μ := by
  unfold joint Formalism.GradedWeylDivisibility.hw
  rw [map_prod, map_prod]
  symm
  apply Fintype.prod_of_injective (Fin.castLE h) (Fin.castLE_injective h)
  · intro i hi
    have hin : ¬ (i : ℕ) < n := fun hh => hi ⟨⟨i, hh⟩, Fin.ext rfl⟩
    have : ν i = 0 := by rw [hν]; simp [hin]
    rw [this]
    simp
  · intro k
    have hk1 : (k : ℕ) + 1 ≤ n := k.2
    rw [map_pow, map_pow]
    have e1 := sSub_lp (n := n) (d := d) (s := (k : ℕ) + 1) (by omega) hk1
    have a : ν (Fin.castLE h k) = μ k := by rw [hν]; simp
    have b : Formalism.GradedWeylDivisibility.nuNext ν (Fin.castLE h k) = Formalism.GradedWeylDivisibility.nuNext μ k := by
      unfold Formalism.GradedWeylDivisibility.nuNext
      by_cases hk : (k : ℕ) + 1 < n
      · simp [hk, show (k : ℕ) + 1 < d by omega, hν]
      · simp [hk, show (k : ℕ) + 1 < d by omega, hν]
    rw [a, b]
    exact congrArg (· ^ _) e1.symm

/- English proof (translation)
Break down `d with _ | m` into its components or cases. Simplify using `[joint, Formalism.GradedWeylDivisibility.hw, dTop, Formalism.GradedWeylDivisibility.lpMinor]`. Unfold `joint Formalism.GradedWeylDivisibility.hw`. Establish `f : ∀ k : Fin (m + 1), sSub (m + 1) (m + 1) (Formalism.GradedWeylDivisibility.lpMinor ℂ ((k : ℕ) + 1) (by omega) (by omega)) = ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ ((k : ℕ) + 1) (by omega) (by omega))` using `fun k => sSub_lp _ (by omega)`. Rewrite using `[map_prod, map_prod]`.

Simplify using `only [map_pow, f]`. Rewrite using `[Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]`. Establish `e_last : ν (Fin.last m) = 0` using `hl _ (by simp)`. Establish `n_last : ∀ ξ : Fin (m + 1) → ℕ, Formalism.GradedWeylDivisibility.nuNext ξ (Fin.last m) = 0` using `fun ξ => by`. Simplify using `[Formalism.GradedWeylDivisibility.nuNext]`.

Establish `e_cs : ∀ k : Fin m, ν k.castSucc - Formalism.GradedWeylDivisibility.nuNext ν k.castSucc = μ k.castSucc - Formalism.GradedWeylDivisibility.nuNext μ k.castSucc`. Introduce `k`. Unfold `Formalism.GradedWeylDivisibility.nuNext`. Establish `hk : (k.castSucc : ℕ) + 1 < m + 1` using `by simp`. Rewrite using `[dif_pos hk, dif_pos hk]`.

Establish `h1` using `hν k.castSucc`. Establish `h2` using `hν ⟨(k.castSucc : ℕ) + 1, hk⟩`. Use linear arithmetic over natural numbers and integers. Establish `hμl : μ (Fin.last m) = t`. Use `hν (Fin.last m)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [e_cs, e_last, n_last, hμl, Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one]`. Both sides reduce to the same expression.
-/
private theorem hw_eq {d : ℕ} (ν μ : Fin d → ℕ) (t : ℕ) (hν : ∀ k, ν k + t = μ k)
    (hl : ∀ k : Fin d, (k : ℕ) + 1 = d → ν k = 0) :
    sSub d d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) * dTop (le_refl d) ^ t = joint (le_refl d) μ := by
  rcases d with _ | m
  · simp [joint, Formalism.GradedWeylDivisibility.hw, dTop, Formalism.GradedWeylDivisibility.lpMinor]
  · unfold joint Formalism.GradedWeylDivisibility.hw
    have f : ∀ k : Fin (m + 1), sSub (m + 1) (m + 1) (Formalism.GradedWeylDivisibility.lpMinor ℂ ((k : ℕ) + 1) (by omega) (by omega)) =
        ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ ((k : ℕ) + 1) (by omega) (by omega)) := fun k => sSub_lp _ (by omega)
    rw [map_prod, map_prod]
    simp only [map_pow, f]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have e_last : ν (Fin.last m) = 0 := hl _ (by simp)
    have n_last : ∀ ξ : Fin (m + 1) → ℕ, Formalism.GradedWeylDivisibility.nuNext ξ (Fin.last m) = 0 := fun ξ => by
      simp [Formalism.GradedWeylDivisibility.nuNext]
    have e_cs : ∀ k : Fin m, ν k.castSucc - Formalism.GradedWeylDivisibility.nuNext ν k.castSucc =
        μ k.castSucc - Formalism.GradedWeylDivisibility.nuNext μ k.castSucc := by
      intro k
      unfold Formalism.GradedWeylDivisibility.nuNext
      have hk : (k.castSucc : ℕ) + 1 < m + 1 := by simp
      rw [dif_pos hk, dif_pos hk]
      have h1 := hν k.castSucc
      have h2 := hν ⟨(k.castSucc : ℕ) + 1, hk⟩
      omega
    have hμl : μ (Fin.last m) = t := by
      have := hν (Fin.last m)
      omega
    simp only [e_cs, e_last, n_last, hμl, Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one]
    rfl

end UpperTheory.TP.RP

/- English proof (translation)
Introduce `n d h lam' c μ hμ`. Establish `hanti : Antitone lam'.natW` using `fun i j hij => by`. Use `lam'.anti hij` as an intermediate fact. Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers.

Establish `key : (∀ g : GL (Fin d) ℂ, C (detPow ℂ d g lam'.detShift) * dTop h ^ (lam'.detShift - c).toNat = C (detPow ℂ d g c) * (rightSub g.1 (dTop h)) ^ (lam'.detShift - c).toNat) ∧ sSub n d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam'.natW) * dTop h ^ (lam'.detShift - c).toNat = jo …`. Break down `h.lt_or_eq with hlt | rfl` into its components or cases. Establish `hs : lam'.detShift = c`. Establish `h0 : 0 < d` using `by omega`. Simplify using `only [DomWeight.detShift, dif_pos h0]`.

Rewrite using `[hμ]`. Simplify using `[show ¬ (d - 1 < n) by omega]`. Rewrite using `[hs]`. Use `⟨fun g => by simp, ?_⟩` and prove the remaining obligations. Simplify using `only [sub_self, Int.toNat_zero, pow_zero, mul_one]`.

Apply `hw_lt h hlt` to reduce the goal to its premises. Introduce `k`. Simplify using `only [DomWeight.natW, hs]`. Rewrite using `[hμ]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hμ' : ∀ k, lam'.w k = (μ k : ℤ) + c` using `fun k => by rw [hμ, dif_pos k.2]`. Establish `hsh : ∀ h0 : 0 < n, lam'.detShift = (μ ⟨n - 1, by omega⟩ : ℤ) + c` using `fun h0 => by`. Simplify using `only [DomWeight.detShift, dif_pos h0, hμ']`. Use `⟨fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rightSub_dTop, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]`.

Use `congr 2`. Break down `Nat.eq_zero_or_pos n with rfl | h0` into its components or cases. Establish `: Matrix.GeneralLinearGroup.det g = 1` using `Units.ext (by simp)`. Simplify using `[detPow, this]`. Establish `e : lam'.detShift = c + ((lam'.detShift - c).toNat : ℤ)`.

Use `hsh h0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e2 : g.1.det = ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)` using `by simp`. Use `conv_lhs => rw [e]`. Rewrite using `[e2]`.

Simplify using `only [detPow, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]`. Apply `hw_eq` to reduce the goal to its premises. Introduce `k`. Establish `h0 : 0 < n` using `by have := k.2; omega`. Establish `h1` using `hsh h0`.

Establish `h2` using `lam'.anti (show k ≤ ⟨n - 1, by omega⟩ from Fin.le_def.mpr (by have := k.2; simp only; omega))`. Rewrite `h2` using `[hμ', hμ']`. Simplify using `only [DomWeight.natW, hμ']`. Use linear arithmetic over natural numbers and integers. Introduce `k hk`.

Establish `h0 : 0 < n` using `by omega`. Establish `e : (⟨n - 1, by omega⟩ : Fin n) = k` using `Fin.ext (by simp; omega)`. Simplify using `[DomWeight.natW, DomWeight.detShift, h0, e]`. Use `⟨(LinearMap.mulRight ℂ (dTop h ^ (lam'.detShift - c).toNat)) ∘ₗ (sSub n d).toLinearMap ∘ₗ (nablaSq ℂ d lam').subtype, ?_, ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ d d le_rfl _ hanti⟩, ?_⟩` and prove the remaining obligations. Introduce `g x`.

Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply, GlobalTheory.Branching.sqRep_coe, sqAct, act2, LinearMap.smul_apply]`. Rewrite using `[map_smul, sSub_rowAct, map_mul, map_pow, smul_eq_C_mul, smul_eq_C_mul]`. Take the linear combination `rightSub g.1 (sSub n d x) * key.1 g`. Conclude with `key.2`.
-/
theorem UpperTheory.TP.RP.exists_act2_equivariant_nablaSq_map_hitting_joint :
    ∀ {n d : ℕ} (h : n ≤ d) (lam' : DomWeight d) (c : ℤ) (μ : Fin n → ℕ),
      (∀ k : Fin d, lam'.w k = (if hk : (k : ℕ) < n then (μ ⟨k, hk⟩ : ℤ) else 0) + c) →
      ∃ i : nablaSq ℂ d lam' →ₗ[ℂ] PP n d, (∀ g x, i (GlobalTheory.Branching.sqRep ℂ d lam' g x) = act2 c g (i x)) ∧ ∃ x₀, i x₀ = joint h μ := by
  intro n d h lam' c μ hμ
  have hanti : Antitone lam'.natW := fun i j hij => by
    have := lam'.anti hij
    simp only [DomWeight.natW]
    omega
  have key : (∀ g : GL (Fin d) ℂ, C (detPow ℂ d g lam'.detShift) * dTop h ^ (lam'.detShift - c).toNat =
        C (detPow ℂ d g c) * (rightSub g.1 (dTop h)) ^ (lam'.detShift - c).toNat) ∧
      sSub n d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam'.natW) * dTop h ^ (lam'.detShift - c).toNat = joint h μ := by
    rcases h.lt_or_eq with hlt | rfl
    · have hs : lam'.detShift = c := by
        have h0 : 0 < d := by omega
        simp only [DomWeight.detShift, dif_pos h0]
        rw [hμ]
        simp [show ¬ (d - 1 < n) by omega]
      rw [hs]
      refine ⟨fun g => by simp, ?_⟩
      simp only [sub_self, Int.toNat_zero, pow_zero, mul_one]
      apply hw_lt h hlt
      intro k
      simp only [DomWeight.natW, hs]
      rw [hμ]
      split_ifs <;> simp
    · have hμ' : ∀ k, lam'.w k = (μ k : ℤ) + c := fun k => by rw [hμ, dif_pos k.2]
      have hsh : ∀ h0 : 0 < n, lam'.detShift = (μ ⟨n - 1, by omega⟩ : ℤ) + c := fun h0 => by
        simp only [DomWeight.detShift, dif_pos h0, hμ']
      refine ⟨fun g => ?_, ?_⟩
      · rw [rightSub_dTop, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
        congr 2
        rcases Nat.eq_zero_or_pos n with rfl | h0
        · have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
          simp [detPow, this]
        · have e : lam'.detShift = c + ((lam'.detShift - c).toNat : ℤ) := by
            have := hsh h0
            omega
          have e2 : g.1.det = ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) := by simp
          conv_lhs => rw [e]
          rw [e2]
          simp only [detPow, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      · apply hw_eq
        · intro k
          have h0 : 0 < n := by have := k.2; omega
          have h1 := hsh h0
          have h2 := lam'.anti (show k ≤ ⟨n - 1, by omega⟩ from Fin.le_def.mpr (by have := k.2; simp only; omega))
          rw [hμ', hμ'] at h2
          simp only [DomWeight.natW, hμ']
          omega
        · intro k hk
          have h0 : 0 < n := by omega
          have e : (⟨n - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
          simp [DomWeight.natW, DomWeight.detShift, h0, e]
  refine ⟨(LinearMap.mulRight ℂ (dTop h ^ (lam'.detShift - c).toNat)) ∘ₗ (sSub n d).toLinearMap ∘ₗ
    (nablaSq ℂ d lam').subtype, ?_, ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ d d le_rfl _ hanti⟩, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, GlobalTheory.Branching.sqRep_coe, sqAct, act2, LinearMap.smul_apply]
    rw [map_smul, sSub_rowAct, map_mul, map_pow, smul_eq_C_mul, smul_eq_C_mul]
    linear_combination rightSub g.1 (sSub n d x) * key.1 g
  · exact key.2
