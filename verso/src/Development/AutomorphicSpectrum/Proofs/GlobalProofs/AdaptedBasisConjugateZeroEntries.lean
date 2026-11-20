import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemUnipOfArchFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UnipOne

/- English proof (translation)
Introduce `a b h`. Assume the negation of the conclusion as `hq`. Apply `h` to reduce the goal to its premises. Establish `hnil : B ^ (n + 1) = 0`. Use extensionality with `i j`.

Assume the negation of the conclusion as `h'`. Establish `h1` using `(GlobalTheory.CompanionTheory.GoodPos.pow_support Q hQt hQlt B hB n i j h').2`. Establish `h2` using `j.2`. Use linear arithmetic over natural numbers and integers. Establish `hexp : NormedSpace.exp B = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) • B ^ k`.

Rewrite using `[NormedSpace.exp_eq_tsum_rat]`. Use `tsum_eq_sum fun k hk => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le (not_lt.1 (fun h' => hk (Finset.mem_range.2 h')))`. Rewrite using `[pow_add, hnil, zero_mul, smul_zero]`. Establish `e : NormedSpace.exp B - 1 = ∑ k ∈ Finset.range n, (((k + 1).factorial : ℚ)⁻¹) • B ^ (k + 1)`.

Rewrite using `[hexp, Finset.sum_range_succ']`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.sum_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply]`.

Distinguish the cases in `h0 : (B ^ (k + 1)) a b = 0`. Rewrite using `[h0, smul_zero]`. Conclude with `absurd (GlobalTheory.CompanionTheory.GoodPos.pow_support Q hQt hQlt B hB k a b h0).1 hq`.
-/
theorem exp_sub_one_pattern {n : ℕ} (Q : Fin n → Fin n → Prop) (hQt : ∀ i l j, Q i l → Q l j → Q i j)
    (hQlt : ∀ i l, Q i l → i < l) (B : Matrix (Fin n) (Fin n) ℂ) (hB : ∀ a b, B a b ≠ 0 → Q a b) :
    ∀ a b, (NormedSpace.exp B - 1) a b ≠ 0 → Q a b := by
  intro a b h
  by_contra hq
  apply h
  have hnil : B ^ (n + 1) = 0 := by
    ext i j
    by_contra h'
    have h1 := (GlobalTheory.CompanionTheory.GoodPos.pow_support Q hQt hQlt B hB n i j h').2
    have h2 := j.2
    omega
  have hexp : NormedSpace.exp B = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) • B ^ k := by
    rw [NormedSpace.exp_eq_tsum_rat]
    refine tsum_eq_sum fun k hk => ?_
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 (fun h' => hk (Finset.mem_range.2 h')))
    rw [pow_add, hnil, zero_mul, smul_zero]
  have e : NormedSpace.exp B - 1 = ∑ k ∈ Finset.range n, (((k + 1).factorial : ℚ)⁻¹) • B ^ (k + 1) := by
    rw [hexp, Finset.sum_range_succ']
    simp
  rw [e, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.smul_apply]
  by_cases h0 : (B ^ (k + 1)) a b = 0
  · rw [h0, smul_zero]
  · exact absurd (GlobalTheory.CompanionTheory.GoodPos.pow_support Q hQt hQlt B hB k a b h0).1 hq

/- English proof (translation)
Establish `hmn : m ≤ n` using `by omega`. Set `emb : Fin m → Fin n` to `Fin.castLE hmn`. Set `Em : Matrix (Fin n) (Fin m) ℂ` to `Matrix.of fun i j => if i.val = j.val then 1 else 0`. Establish `hXE : Xc = P * Em`. Use extensionality with `k j`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (emb j)]`. Simplify using `[Em, emb, hX (emb j) j rfl k]`. Introduce `b _ hb`. Establish `: b.val ≠ j.val` using `fun h => hb (Fin.ext h)`. Simplify using `[Em, this]`.

Simplify using the standard rewrite rules. Establish `hEm : ∀ z : Fin n → ℂ, (∀ i : Fin n, m ≤ i.val → z i = 0) → Em *ᵥ (z ∘ emb) = z`. Introduce `z hz`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i.val < m`.

Use `show ∑ j, Em i j * z (emb j) = z i`. Rewrite using `[Finset.sum_eq_single (⟨i.val, hi⟩ : Fin m)]`. Establish `: emb ⟨i.val, hi⟩ = i` using `Fin.ext rfl`. Simplify using `[Em, this]`. Introduce `b _ hb`.

Establish `: i.val ≠ b.val` using `fun h => hb (Fin.ext h.symm)`. Simplify using `[Em, this]`. Simplify using the standard rewrite rules. Rewrite using `[hz i (by omega)] show ∑ j, Em i j * z (emb j) = 0`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Establish `: i.val ≠ j.val` using `by have := j.2; omega`. Simplify using `[Em, this]`. Use `⟨N₀.submatrix emb emb, ?_, fun i j h => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hNE : N₀ * Em = Em * N₀.submatrix emb emb`. Use extensionality with `a j`.

Establish `h1 : (N₀ * Em) a j = N₀ a (emb j)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (emb j)]`. Simplify using `[Em, emb]`. Introduce `b _ hb`. Establish `: b.val ≠ j.val` using `fun h => hb (Fin.ext h)`.

Simplify using `[Em, this]`. Simplify using the standard rewrite rules. Establish `h2 : (Em * N₀.submatrix emb emb) a j = (Em *ᵥ ((fun b => N₀ b (emb j)) ∘ emb)) a` using `rfl`. Rewrite using `[h1, h2, hEm]`. Introduce `i hi`.

Assume the negation of the conclusion as `hc`. Take `⟨e, -, h3, h4⟩` from `hN i (emb j) hc`. Use `j.2` as an intermediate fact. Establish `: (emb j).val = j.val` using `rfl`. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hXE]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = P * Em + P * (Em * N₀.submatrix emb emb) := by`. Rewrite using `[hP', Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc, hNE]`.

Use `_ = Xc + Xc * N₀.submatrix emb emb := by rw [hXE, Matrix.mul_assoc]`. Take `⟨e, h1, h2, h3⟩` from `hN (emb i) (emb j) h`. Establish `e1 : (emb i).val = i.val` using `rfl`. Establish `e2 : (emb j).val = j.val` using `rfl`. Establish `hj` using `j.2`.

Use `⟨e, ?_, by omega, by omega⟩` and prove the remaining obligations. Break down `h1 with h1 | h1 | h1 | h1` into its components or cases. Conclude with `Or.inl h1`. Conclude with `Or.inr h1`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Use `set w := Pinv *ᵥ v with hw`. Establish `hPw : P *ᵥ w = v` using `by rw [hw, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]`. Establish `hzero : ∀ b : Fin n, n ≤ b.val + l + d → w b = 0`. Introduce `b hb`.

Establish `hb'` using `b.2`. Set `i : Fin m` to `⟨n - 1 - b.val, by omega⟩`. Establish `h1` using `hv i (by show n - 1 - b.val < l + d; omega)`. Rewrite `h1` using `[← hPw, Matrix.mulVec_mulVec]`. Establish `h2 : ((R * P) *ᵥ w) i = ∑ c, (R * P) i c * w c` using `rfl`.

Rewrite `h1` using `[h2, Finset.sum_eq_single b]`. Rewrite `h1` using `[hR, if_pos (by show b.val + (n - 1 - b.val) + 1 = n; omega), one_mul]`. Conclude with `h1`. Introduce `c _ hc`. Establish `: c.val + i.val + 1 ≠ n`.

Establish `: i.val = n - 1 - b.val` using `rfl`. Introduce `h`. Conclude with `hc (Fin.ext (by omega))`. Rewrite using `[hR, if_neg this, zero_mul]`. Simplify using the standard rewrite rules.

Use `set y := N₀ *ᵥ w with hy`. Establish `hysupp : ∀ i : Fin n, y i ≠ 0 → i.val < l + d`. Introduce `i hi`. Take `⟨b, -, hb⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (show ∑ b, N₀ i b * w b ≠ 0 from hi)`. Take `⟨e, h1, h2, h3⟩` from `hN i b (left_ne_zero_of_mul hb)`.

Establish `h4 : b.val + l + d < n`. Assume the negation of the conclusion as `hc`. Conclude with `right_ne_zero_of_mul hb (hzero b (by omega))`. Use linear arithmetic over natural numbers and integers. Use `⟨y ∘ emb, fun i hi => hysupp (emb i) hi, ?_⟩` and prove the remaining obligations.

Establish `hEy : Em *ᵥ (y ∘ emb) = y` using `hEm y fun i hi => by`. Assume the negation of the conclusion as `hc`. Use `hysupp i hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e1 : (P * (1 + N₀) * Pinv) *ᵥ v = P *ᵥ ((1 + N₀) *ᵥ w)`.

Rewrite using `[hw]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `e2 : (P * Em) *ᵥ (y ∘ emb) = P *ᵥ y` using `by rw [← Matrix.mulVec_mulVec, hEy]`. Rewrite using `[e1, hXE, e2, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, hPw, add_sub_cancel_left]`.
-/
theorem conj_frame {n m l d : ℕ} (hnm : 2 * m ≤ n) (hld : l + d ≤ m) (P Pinv N₀ : Matrix (Fin n) (Fin n) ℂ)
    (hP : P * Pinv = 1) (hP' : Pinv * P = 1) (Xc : Matrix (Fin n) (Fin m) ℂ)
    (hX : ∀ (i : Fin n) (j : Fin m), i.val = j.val → ∀ k, P k i = Xc k j) (R : Matrix (Fin m) (Fin n) ℂ)
    (hR : ∀ (i : Fin m) (b : Fin n), (R * P) i b = if b.val + i.val + 1 = n then 1 else 0)
    (hN : ∀ a b, N₀ a b ≠ 0 → ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = n ∨ e + l = n) ∧ a.val < e ∧ e ≤ b.val) :
    ∃ N : Matrix (Fin m) (Fin m) ℂ, (P * (1 + N₀) * Pinv) * Xc = Xc + Xc * N ∧
      (∀ i j, N i j ≠ 0 → ∃ e : ℕ, (e = l ∨ e = l + d) ∧ i.val < e ∧ e ≤ j.val) ∧
      ∀ v : Fin n → ℂ, (∀ i : Fin m, i.val < l + d → (R *ᵥ v) i = 0) →
        ∃ a : Fin m → ℂ, (∀ i, a i ≠ 0 → i.val < l + d) ∧ (P * (1 + N₀) * Pinv) *ᵥ v - v = Xc *ᵥ a := by
  classical
  have hmn : m ≤ n := by omega
  let emb : Fin m → Fin n := Fin.castLE hmn
  let Em : Matrix (Fin n) (Fin m) ℂ := Matrix.of fun i j => if i.val = j.val then 1 else 0
  have hXE : Xc = P * Em := by
    ext k j
    rw [Matrix.mul_apply, Finset.sum_eq_single (emb j)]
    · simp [Em, emb, hX (emb j) j rfl k]
    · intro b _ hb
      have : b.val ≠ j.val := fun h => hb (Fin.ext h)
      simp [Em, this]
    · simp
  have hEm : ∀ z : Fin n → ℂ, (∀ i : Fin n, m ≤ i.val → z i = 0) → Em *ᵥ (z ∘ emb) = z := by
    intro z hz
    funext i
    by_cases hi : i.val < m
    · show ∑ j, Em i j * z (emb j) = z i
      rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin m)]
      · have : emb ⟨i.val, hi⟩ = i := Fin.ext rfl
        simp [Em, this]
      · intro b _ hb
        have : i.val ≠ b.val := fun h => hb (Fin.ext h.symm)
        simp [Em, this]
      · simp
    · rw [hz i (by omega)]
      show ∑ j, Em i j * z (emb j) = 0
      refine Finset.sum_eq_zero fun j _ => ?_
      have : i.val ≠ j.val := by have := j.2; omega
      simp [Em, this]
  refine ⟨N₀.submatrix emb emb, ?_, fun i j h => ?_, fun v hv => ?_⟩
  · have hNE : N₀ * Em = Em * N₀.submatrix emb emb := by
      ext a j
      have h1 : (N₀ * Em) a j = N₀ a (emb j) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (emb j)]
        · simp [Em, emb]
        · intro b _ hb
          have : b.val ≠ j.val := fun h => hb (Fin.ext h)
          simp [Em, this]
        · simp
      have h2 : (Em * N₀.submatrix emb emb) a j = (Em *ᵥ ((fun b => N₀ b (emb j)) ∘ emb)) a := rfl
      rw [h1, h2, hEm]
      intro i hi
      by_contra hc
      obtain ⟨e, -, h3, h4⟩ := hN i (emb j) hc
      have := j.2
      have : (emb j).val = j.val := rfl
      omega
    calc (P * (1 + N₀) * Pinv) * Xc = P * (1 + N₀) * (Pinv * P) * Em := by
          rw [hXE]; simp only [Matrix.mul_assoc]
      _ = P * Em + P * (Em * N₀.submatrix emb emb) := by
          rw [hP', Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc, hNE]
      _ = Xc + Xc * N₀.submatrix emb emb := by rw [hXE, Matrix.mul_assoc]
  · obtain ⟨e, h1, h2, h3⟩ := hN (emb i) (emb j) h
    have e1 : (emb i).val = i.val := rfl
    have e2 : (emb j).val = j.val := rfl
    have hj := j.2
    refine ⟨e, ?_, by omega, by omega⟩
    rcases h1 with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · omega
    · omega
  · set w := Pinv *ᵥ v with hw
    have hPw : P *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
    have hzero : ∀ b : Fin n, n ≤ b.val + l + d → w b = 0 := by
      intro b hb
      have hb' := b.2
      let i : Fin m := ⟨n - 1 - b.val, by omega⟩
      have h1 := hv i (by show n - 1 - b.val < l + d; omega)
      rw [← hPw, Matrix.mulVec_mulVec] at h1
      have h2 : ((R * P) *ᵥ w) i = ∑ c, (R * P) i c * w c := rfl
      rw [h2, Finset.sum_eq_single b] at h1
      · rw [hR, if_pos (by show b.val + (n - 1 - b.val) + 1 = n; omega), one_mul] at h1
        exact h1
      · intro c _ hc
        have : c.val + i.val + 1 ≠ n := by
          have : i.val = n - 1 - b.val := rfl
          intro h
          exact hc (Fin.ext (by omega))
        rw [hR, if_neg this, zero_mul]
      · simp
    set y := N₀ *ᵥ w with hy
    have hysupp : ∀ i : Fin n, y i ≠ 0 → i.val < l + d := by
      intro i hi
      obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show ∑ b, N₀ i b * w b ≠ 0 from hi)
      obtain ⟨e, h1, h2, h3⟩ := hN i b (left_ne_zero_of_mul hb)
      have h4 : b.val + l + d < n := by
        by_contra hc
        exact right_ne_zero_of_mul hb (hzero b (by omega))
      omega
    refine ⟨y ∘ emb, fun i hi => hysupp (emb i) hi, ?_⟩
    have hEy : Em *ᵥ (y ∘ emb) = y := hEm y fun i hi => by
      by_contra hc
      have := hysupp i hc
      omega
    have e1 : (P * (1 + N₀) * Pinv) *ᵥ v = P *ᵥ ((1 + N₀) *ᵥ w) := by
      rw [hw]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (P * Em) *ᵥ (y ∘ emb) = P *ᵥ y := by rw [← Matrix.mulVec_mulVec, hEy]
    rw [e1, hXE, e2, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, hPw, add_sub_cancel_left]

/- English proof (translation)
Take `⟨N, h1, h2, h3⟩` from `h`. Set `g : ℂ → R'` to `Function.surjInv hf.2`. Establish `hg : ∀ z, f (g z) = z` using `Function.surjInv_eq hf.2`. Establish `hN' : (N.map g).map f = N` using `Matrix.ext fun i j => hg _`. Use `⟨N.map g, ?_, fun i j h => h2 i j fun h0 => h (hf.1 ?_), fun v hv => ?_⟩` and prove the remaining obligations.

Apply `Matrix.map_injective hf.1 show (M * X').map f = (X' + X' * N.map g).map f` to reduce the goal to its premises. Rewrite using `[Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hN', h1]`. Use `show f (g (N i j)) = f 0`. Rewrite using `[hg, h0, map_zero]`. Take `⟨a, ha, hav⟩` from `h3 (f ∘ v) fun i hi => by`.

Rewrite using `[← RingHom.map_mulVec, hv i hi, map_zero]`. Use `⟨g ∘ a, fun i hi => ha i fun h0 => hi (hf.1 ?_), ?_⟩` and prove the remaining obligations. Use `show f (g (a i)) = f 0`. Rewrite using `[hg, h0, map_zero]`. Use function extensionality and compare the values at `i`.

Apply `hf.1` to reduce the goal to its premises. Establish `e` using `congrFun hav i`. Use `show f ((M *ᵥ v) i - v i) = f ((X' *ᵥ (g ∘ a)) i)`. Establish `hfa : f ∘ g ∘ a = a` using `funext fun i => hg _`. Rewrite using `[map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hfa]`.

Conclude with `e`.
-/
theorem frame_descend {R' : Type*} [CommRing R'] {n m : ℕ} (f : R' →+* ℂ) (hf : Function.Bijective f)
    (M : Matrix (Fin n) (Fin n) R') (X' : Matrix (Fin n) (Fin m) R') (Rw : Matrix (Fin m) (Fin n) R')
    (Pn : Fin m → Fin m → Prop) (Pr : Fin m → Prop)
    (h : ∃ N : Matrix (Fin m) (Fin m) ℂ, M.map f * X'.map f = X'.map f + X'.map f * N ∧ (∀ i j, N i j ≠ 0 → Pn i j) ∧
      ∀ v : Fin n → ℂ, (∀ i, Pr i → (Rw.map f *ᵥ v) i = 0) →
        ∃ a : Fin m → ℂ, (∀ i, a i ≠ 0 → Pr i) ∧ M.map f *ᵥ v - v = X'.map f *ᵥ a) :
    ∃ N : Matrix (Fin m) (Fin m) R', M * X' = X' + X' * N ∧ (∀ i j, N i j ≠ 0 → Pn i j) ∧
      ∀ v : Fin n → R', (∀ i, Pr i → (Rw *ᵥ v) i = 0) →
        ∃ a : Fin m → R', (∀ i, a i ≠ 0 → Pr i) ∧ M *ᵥ v - v = X' *ᵥ a := by
  obtain ⟨N, h1, h2, h3⟩ := h
  let g : ℂ → R' := Function.surjInv hf.2
  have hg : ∀ z, f (g z) = z := Function.surjInv_eq hf.2
  have hN' : (N.map g).map f = N := Matrix.ext fun i j => hg _
  refine ⟨N.map g, ?_, fun i j h => h2 i j fun h0 => h (hf.1 ?_), fun v hv => ?_⟩
  · apply Matrix.map_injective hf.1
    show (M * X').map f = (X' + X' * N.map g).map f
    rw [Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hN', h1]
  · show f (g (N i j)) = f 0
    rw [hg, h0, map_zero]
  · obtain ⟨a, ha, hav⟩ := h3 (f ∘ v) fun i hi => by
      rw [← RingHom.map_mulVec, hv i hi, map_zero]
    refine ⟨g ∘ a, fun i hi => ha i fun h0 => hi (hf.1 ?_), ?_⟩
    · show f (g (a i)) = f 0
      rw [hg, h0, map_zero]
    · funext i
      apply hf.1
      have e := congrFun hav i
      show f ((M *ᵥ v) i - v i) = f ((X' *ᵥ (g ∘ a)) i)
      have hfa : f ∘ g ∘ a = a := funext fun i => hg _
      rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hfa]
      exact e

/- English proof (translation)
Establish `col : ∀ (Z : Matrix (Fin n) (Fin r) E) (j : Fin r), (∀ k, C.1 k b = Z k j) → ((Formalism.UG.cT (σ : E →+* E) X * J) * C.1) i b = ((Formalism.UG.cT (σ : E →+* E) X * J) * Z) i j` using `fun Z j h => by show ∑ k, _ * C.1 k b = ∑ k, _ * Z k j`. Simplify using `only [h]`. Establish `hle` using `hC.le`. Establish `hi` using `i.2`. Establish `hb` using `b.2`.

Distinguish the cases in `h1 : b.val < r`. Rewrite using `[col X ⟨b.val, h1⟩ (hC.colX b ⟨b.val, h1⟩ rfl), hW.xx, if_neg (by omega)]`. Both sides reduce to the same expression. Distinguish the cases in `h2 : b.val + r < n`. Rewrite using `[if_neg (by omega)]`.

Conclude with `congrFun (hC.perpX b (by omega) h2) i`. Set `j : Fin r` to `⟨n - 1 - b.val, by omega⟩`. Establish `hj : j.val = n - 1 - b.val` using `rfl`. Rewrite using `[col Y j (hC.columnBlock b j (by omega)), hW.xy, Matrix.one_apply]`. Use `if_congr ⟨fun h => ?_, fun h => Fin.ext (by omega)⟩ rfl rfl` and prove the remaining obligations.

Rewrite using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem frame_pairing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E)
    (hW : IsWittFrame σ J X Y) (C : GL (Fin n) E) (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (i : Fin r) (b : Fin n) :
    ((Formalism.UG.cT (σ : E →+* E) X * J) * C.1) i b = if b.val + i.val + 1 = n then 1 else 0 := by
  have col : ∀ (Z : Matrix (Fin n) (Fin r) E) (j : Fin r), (∀ k, C.1 k b = Z k j) →
      ((Formalism.UG.cT (σ : E →+* E) X * J) * C.1) i b = ((Formalism.UG.cT (σ : E →+* E) X * J) * Z) i j := fun Z j h => by
    show ∑ k, _ * C.1 k b = ∑ k, _ * Z k j
    simp only [h]
  have hle := hC.le
  have hi := i.2
  have hb := b.2
  by_cases h1 : b.val < r
  · rw [col X ⟨b.val, h1⟩ (hC.colX b ⟨b.val, h1⟩ rfl), hW.xx, if_neg (by omega)]
    rfl
  · by_cases h2 : b.val + r < n
    · rw [if_neg (by omega)]
      exact congrFun (hC.perpX b (by omega) h2) i
    · let j : Fin r := ⟨n - 1 - b.val, by omega⟩
      have hj : j.val = n - 1 - b.val := rfl
      rw [col Y j (hC.columnBlock b j (by omega)), hW.xy, Matrix.one_apply]
      refine if_congr ⟨fun h => ?_, fun h => Fin.ext (by omega)⟩ rfl rfl
      rw [h]
      omega

/- English proof (translation)
Introduce `D θ hθ V m X Y hW T l d hld ⟨k₀, hk₀, hk₀'⟩ hl C hC τ A hA hpat t`. Establish `hAt` using `GlobalTheory.Mem.Lift.isAtTau_oneP hθ hA t`. Use `GlobalTheory.CompanionTheory.GoodPos.mem_unip_of_arch_frame _ _ D.sp.cm.sig V.rank V.gram m X T _ hAt.1 fun w => ?_` and prove the remaining obligations. Take `⟨ρ, rfl⟩` from `(placeOf_bijective D).2 w`. Establish `hbij` using `GlobalTheory.AdelicU.infEmb_bijective (isCMExt_host D) (embOverOf D ρ)`.

Establish `hM : (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (projArch D.sp.cm.sig V.gram (placeOf D ρ) (oneP θ V τ A t))).1.map (infEmb (embOverOf D ρ)) = infMat D.sp.cm.sig V.gram (θ ρ) (oneP θ V τ A t)`. Rewrite using `[eq_infProj hθ (embOverOf D ρ) rfl, infMat_infProj V.gram (isCMExt_host D)]`. Both sides reduce to the same expression. Establish `hmap : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) D.host.E), (Z.map (inclR (F` using `D.host.F) (placeOf D ρ).Completion)).map (infEmb (embOverOf D ρ)) = Z.map (tauE D ρ) := by`. Introduce `a b Z`.

Use extensionality with `r s`. Simplify using `[inclR]`. Use `frame_descend (infEmb (embOverOf D ρ)) hbij _ _ _ (fun i j => ∃ k ∈ T, i ≤ k ∧ k < j) (fun i => ∃ k ∈ T, i ≤ k) ?_` and prove the remaining obligations. Rewrite using `[hM, hmap, hmap]`. Distinguish the cases in `hρ : ρ = τ`.

Substitute `hρ` using the available equality. Rewrite using `[hAt.2.1]`. Establish `hPu : IsUnit (C.1.map (tauE D ρ))` using `(Matrix.GeneralLinearGroup.map (tauE D ρ) C).isUnit`. Establish `hdet` using `(Matrix.isUnit_iff_isUnit_det _).1 hPu`. Take `⟨P, hPdef⟩ : ∃ P, P = C.1.map (tauE D ρ)` from `⟨_, rfl⟩`.

Rewrite `hPu`, `hdet`, `hpat` using `[← hPdef]`. Establish `hP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hdet`. Establish `hP' : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hdet`. Take `⟨A₀, hA₀⟩ : ∃ B, B = P⁻¹ * A * P` from `⟨_, rfl⟩`. Rewrite `hpat` using `[← hA₀]`.

Establish `hAA : A = P * A₀ * P⁻¹`. Rewrite using `[hA₀]`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp : NormedSpace.exp (t • A) = P * NormedSpace.exp (t • A₀) * P⁻¹`. Rewrite using `[← Matrix.exp_conj P _ hPu, Matrix.mul_smul, Matrix.smul_mul, ← hAA]`.

Set `Q : Fin V.rank → Fin V.rank → Prop` to `fun a b => ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val`. Establish `hQt : ∀ i l j, Q i l → Q l j → Q i j` using `fun i l j ⟨e, _, h1, h2⟩ ⟨e', h', h1', h2'⟩ => ⟨e', h', by omega, h2'⟩`. Establish `hQlt : ∀ i l, Q i l → i < l` using `fun i l ⟨e, _, h1, h2⟩ => by`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.

Establish `hB : ∀ a b, (t • A₀) a b ≠ 0 → Q a b` using `fun a b h => hpat a b fun h0 => h (by simp [h0])`. Establish `hN` using `exp_sub_one_pattern Q hQt hQlt (t • A₀) hB`. Take `⟨N₀, hN₀⟩ : ∃ N, N = NormedSpace.exp (t • A₀) - 1` from `⟨_, rfl⟩`. Rewrite `hN` using `[← hN₀]`. Establish `hE1 : NormedSpace.exp (t • A₀) = 1 + N₀` using `by rw [hN₀, add_sub_cancel]`.

Rewrite using `[hexp, hE1]`. Take `⟨N, h1, h2, h3⟩` from `conj_frame hC.le hld P P⁻¹ N₀ hP hP' (X.map (tauE D ρ)) (fun i j h k => by rw [hPdef]; show tauE D ρ (C.1 k i) = tauE D ρ (X k j); rw [hC.colX i j h k]) ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D ρ)) (fun i b => by`. Rewrite using `[hPdef, ← Matrix.map_mul]`. Use `show tauE D ρ _ = _`. Rewrite using `[frame_pairing D.sp.cm.sig V.gram X Y hW C hC]`.

Apply the tactic sequence `split_ifs <;> simp) hN`. Use `⟨N, h1, fun i j h => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨e, he, h4, h5⟩` from `h2 i j h`. Break down `he with rfl | rfl` into its components or cases. Break down `hl with h0 | ⟨p, hp, hp'⟩` into its components or cases.

Use linear arithmetic over natural numbers and integers. Conclude with `⟨p, hp, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩`. Conclude with `⟨k₀, hk₀, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩`. Take `⟨a, ha, hav⟩` from `h3 v fun i hi => hv i ⟨k₀, hk₀, by rw [Fin.le_def]; omega⟩`. Conclude with `⟨a, fun i hi => ⟨k₀, hk₀, by have := ha i hi; rw [Fin.le_def]; omega⟩, hav⟩`.

Rewrite using `[hAt.2.2 ρ hρ]`. Conclude with `⟨0, by simp, by simp, fun v _ => ⟨0, by simp, by simp⟩⟩`.
-/
theorem oneP_mem_unip : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (l d : ℕ), l + d ≤ m →
    (∃ k ∈ T, k.val + 1 = l + d) → (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A ∈ lieAt V τ →
    (∀ a b : Fin V.rank, ((C.1.map (tauE D τ))⁻¹ * A * C.1.map (tauE D τ)) a b ≠ 0 →
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val) →
    ∀ t : ℝ, oneP θ V τ A t ∈ unip D.sp.cm.sig V.gram X T := by
  intro D θ hθ V m X Y hW T l d hld ⟨k₀, hk₀, hk₀'⟩ hl C hC τ A hA hpat t
  classical
  have hAt := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hA t
  refine GlobalTheory.CompanionTheory.GoodPos.mem_unip_of_arch_frame _ _ D.sp.cm.sig V.rank V.gram m X T _ hAt.1 fun w => ?_
  obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
  have hbij := GlobalTheory.AdelicU.infEmb_bijective (isCMExt_host D) (embOverOf D ρ)
  have hM : (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (projArch D.sp.cm.sig V.gram (placeOf D ρ) (oneP θ V τ A t))).1.map
      (infEmb (embOverOf D ρ)) = infMat D.sp.cm.sig V.gram (θ ρ) (oneP θ V τ A t) := by
    rw [eq_infProj hθ (embOverOf D ρ) rfl, infMat_infProj V.gram (isCMExt_host D)]
    rfl
  have hmap : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) D.host.E),
      (Z.map (inclR (F := D.host.F) (placeOf D ρ).Completion)).map (infEmb (embOverOf D ρ)) = Z.map (tauE D ρ) := by
    intro a b Z
    ext r s
    simp [inclR]
  refine frame_descend (infEmb (embOverOf D ρ)) hbij _ _ _ (fun i j => ∃ k ∈ T, i ≤ k ∧ k < j) (fun i => ∃ k ∈ T, i ≤ k) ?_
  rw [hM, hmap, hmap]
  by_cases hρ : ρ = τ
  · subst hρ
    rw [hAt.2.1]
    have hPu : IsUnit (C.1.map (tauE D ρ)) := (Matrix.GeneralLinearGroup.map (tauE D ρ) C).isUnit
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hPu
    obtain ⟨P, hPdef⟩ : ∃ P, P = C.1.map (tauE D ρ) := ⟨_, rfl⟩
    rw [← hPdef] at hPu hdet hpat
    have hP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
    have hP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    obtain ⟨A₀, hA₀⟩ : ∃ B, B = P⁻¹ * A * P := ⟨_, rfl⟩
    rw [← hA₀] at hpat
    have hAA : A = P * A₀ * P⁻¹ := by
      rw [hA₀]
      calc A = (P * P⁻¹) * A * (P * P⁻¹) := by rw [hP, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hexp : NormedSpace.exp (t • A) = P * NormedSpace.exp (t • A₀) * P⁻¹ := by
      rw [← Matrix.exp_conj P _ hPu, Matrix.mul_smul, Matrix.smul_mul, ← hAA]
    let Q : Fin V.rank → Fin V.rank → Prop := fun a b =>
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val
    have hQt : ∀ i l j, Q i l → Q l j → Q i j := fun i l j ⟨e, _, h1, h2⟩ ⟨e', h', h1', h2'⟩ =>
      ⟨e', h', by omega, h2'⟩
    have hQlt : ∀ i l, Q i l → i < l := fun i l ⟨e, _, h1, h2⟩ => by
      rw [Fin.lt_def]
      omega
    have hB : ∀ a b, (t • A₀) a b ≠ 0 → Q a b := fun a b h => hpat a b fun h0 => h (by simp [h0])
    have hN := exp_sub_one_pattern Q hQt hQlt (t • A₀) hB
    obtain ⟨N₀, hN₀⟩ : ∃ N, N = NormedSpace.exp (t • A₀) - 1 := ⟨_, rfl⟩
    rw [← hN₀] at hN
    have hE1 : NormedSpace.exp (t • A₀) = 1 + N₀ := by rw [hN₀, add_sub_cancel]
    rw [hexp, hE1]
    obtain ⟨N, h1, h2, h3⟩ := conj_frame hC.le hld P P⁻¹ N₀ hP hP' (X.map (tauE D ρ))
      (fun i j h k => by rw [hPdef]; show tauE D ρ (C.1 k i) = tauE D ρ (X k j); rw [hC.colX i j h k])
      ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D ρ))
      (fun i b => by
        rw [hPdef, ← Matrix.map_mul]
        show tauE D ρ _ = _
        rw [frame_pairing D.sp.cm.sig V.gram X Y hW C hC]
        split_ifs <;> simp) hN
    refine ⟨N, h1, fun i j h => ?_, fun v hv => ?_⟩
    · obtain ⟨e, he, h4, h5⟩ := h2 i j h
      rcases he with rfl | rfl
      · rcases hl with h0 | ⟨p, hp, hp'⟩
        · omega
        · exact ⟨p, hp, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
      · exact ⟨k₀, hk₀, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
    · obtain ⟨a, ha, hav⟩ := h3 v fun i hi => hv i ⟨k₀, hk₀, by rw [Fin.le_def]; omega⟩
      exact ⟨a, fun i hi => ⟨k₀, hk₀, by have := ha i hi; rw [Fin.le_def]; omega⟩, hav⟩
  · rw [hAt.2.2 ρ hρ]
    exact ⟨0, by simp, by simp, fun v _ => ⟨0, by simp, by simp⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UnipOne
