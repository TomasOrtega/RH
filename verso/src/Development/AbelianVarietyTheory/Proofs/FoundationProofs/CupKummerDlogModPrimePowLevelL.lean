import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HodgeTateCupKummerClassesEqDlogDeterminantStatement

noncomputable section

namespace GlobalTheory.K5.LevelDown

open Polynomial GlobalTheory.K5 GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `set S := Algebra.adjoin (O0 p) {xn p L, yn p L}`. Establish `hx : xn p L ∈ S` using `Algebra.subset_adjoin (by simp)`. Establish `hy : yn p L ∈ S` using `Algebra.subset_adjoin (by simp)`. Establish `hb : ∀ b : O0 p, Ideal.Quotient.mk (towerIdeal p L) (C (C b)) ∈ S`.

Introduce `b`. Apply the tactic sequence `have : Ideal.Quotient.mk (towerIdeal p L) (C (C b)) = algebraMap (O0 p) (On p L) b := by first | rfl | simp [Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_apply]`. Rewrite using `[this]`. Conclude with `S.algebraMap_mem b`. Establish `hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p L) (C a) ∈ S`.

Introduce `a`. Proceed by induction on `a using Polynomial.induction_on with`. Consider the case `C b => exact hb b`. Consider the case `add f g hf hg => rw [C_add, map_add]`. Conclude with `S.add_mem hf hg`.

Consider the case `monomial k b _`. Rewrite using `[C_mul, C_pow, map_mul, map_pow]`. Conclude with `S.mul_mem (hb b) (S.pow_mem hx _)`. Proceed by induction on `f using Polynomial.induction_on with`. Consider the case `C a => exact hC a`.

Consider the case `add f g hf hg => rw [map_add]`. Conclude with `S.add_mem hf hg`. Consider the case `monomial k a _ => rw [map_mul, map_pow]`. Conclude with `S.mul_mem (hC a) (S.pow_mem hy _)`.
-/
theorem mem_adjoin (L : ℕ) (x : On p L) : x ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  set S := Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hb : ∀ b : O0 p, Ideal.Quotient.mk (towerIdeal p L) (C (C b)) ∈ S := by
    intro b
    have : Ideal.Quotient.mk (towerIdeal p L) (C (C b)) = algebraMap (O0 p) (On p L) b := by
      first | rfl | simp [Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_apply]
    rw [this]; exact S.algebraMap_mem b
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p L) (C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hb b
    | add f g hf hg => rw [C_add, map_add]; exact S.add_mem hf hg
    | monomial k b _ =>
      rw [C_mul, C_pow, map_mul, map_pow]
      exact S.mul_mem (hb b) (S.pow_mem hx _)
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
  | monomial k a _ => rw [map_mul, map_pow]; exact S.mul_mem (hC a) (S.pow_mem hy _)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]`.
-/
theorem zeta_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ p ^ k = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]`.
-/
theorem qq_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ p ^ k = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

/- English proof (translation)
Rewrite using `[IsInt, ← map_natCast (algebraMap (O0 p) Ω)]`. Conclude with `isIntegral_algebraMap`.
-/
theorem isInt_nat (m : ℕ) : IsInt p (m : Ω) := by
  rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω)]; exact isIntegral_algebraMap

/- English proof (translation)
Establish `h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤ (integralClosure (O0 p) Ω).comap ι`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `z (rfl | rfl)`. Use `show ι (xn p L) ∈ integralClosure (O0 p) Ω`. Rewrite using `[mem_integralClosure_iff, hι.1]`.

Conclude with `IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [(T.prim L).pow_eq_one]; exact isIntegral_one)`. Use `show ι (yn p L) ∈ integralClosure (O0 p) Ω`. Rewrite using `[mem_integralClosure_iff, hι.2]`. Use `IsIntegral.of_pow (pow_pos hp.out.pos L) ?_` and prove the remaining obligations. Rewrite using `[qq_pow]`.

Conclude with `isIntegral_algebraMap`. Conclude with `h (mem_adjoin L x)`.
-/
theorem isInt_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (x : On p L) : IsInt p (ι x) := by
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤ (integralClosure (O0 p) Ω).comap ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show ι (xn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.1]
      exact IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [(T.prim L).pow_eq_one]; exact isIntegral_one)
    · show ι (yn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.2]
      refine IsIntegral.of_pow (pow_pos hp.out.pos L) ?_
      rw [qq_pow]; exact isIntegral_algebraMap
  exact h (mem_adjoin L x)

/- English proof (translation)
Establish `hg'` using `(mem_gn T L g).1 hg`. Establish `h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤ AlgHom.equalizer ((g : Ω →ₐ[O0 p] Ω).comp ι) ι`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `z (rfl | rfl)`. Use `show g (ι (xn p L)) = ι (xn p L)`.

Rewrite using `[hι.1]`. Conclude with `hg'.1`. Use `show g (ι (yn p L)) = ι (yn p L)`. Rewrite using `[hι.2]`. Conclude with `hg'.2`.

Conclude with `h (mem_adjoin L x)`.
-/
theorem fix_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (g : Gal p Ω) (hg : g ∈ Gn T L) (x : On p L) : g (ι x) = ι x := by
  have hg' := (mem_gn T L g).1 hg
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤
      AlgHom.equalizer ((g : Ω →ₐ[O0 p] Ω).comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show g (ι (xn p L)) = ι (xn p L)
      rw [hι.1]; exact hg'.1
    · show g (ι (yn p L)) = ι (yn p L)
      rw [hι.2]; exact hg'.2
  exact h (mem_adjoin L x)

/- English proof (translation)
Take `⟨z, hz, e⟩` from `hc`. Use `⟨(p : Ω) ^ (m - k) * z, IsIntegral.mul (IsIntegral.pow (isInt_nat p) _) hz, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]`.
-/
theorem cong_mono {k m : ℕ} (h : k ≤ m) {x y : Ω} (hc : Cong p m x y) : Cong p k x y := by
  obtain ⟨z, hz, e⟩ := hc
  refine ⟨(p : Ω) ^ (m - k) * z, IsIntegral.mul (IsIntegral.pow (isInt_nat p) _) hz, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hw.1, fun g => by obtain ⟨S, hS⟩ := hw.2 g exact ⟨S, fun h' hh => cong_mono h (hS h' hh)⟩⟩`.
-/
theorem locallyConstantModPrimePow_of_le {k m : ℕ} (h : k ≤ m) {w : Gal p Ω → Ω} (hw : LocallyConstantOneCochain m w) : LocallyConstantOneCochain k w :=
  ⟨hw.1, fun g => by
    obtain ⟨S, hS⟩ := hw.2 g
    exact ⟨S, fun h' hh => cong_mono h (hS h' hh)⟩⟩

/- English proof (translation)
Take `⟨a, ha, e⟩` from `h`. Take `⟨b, hb, e'⟩` from `h'`. Conclude with `⟨a * x' + y * b, (ha.mul hx').add (hy.mul hb), by linear_combination x' * e + y * e'⟩`.
-/
theorem cong_mul' {k : ℕ} {x y x' y' : Ω} (h : Cong p k x y) (h' : Cong p k x' y')
    (hx' : IsInt p x') (hy : IsInt p y) : Cong p k (x * x') (y * y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a * x' + y * b, (ha.mul hx').add (hy.mul hb), by linear_combination x' * e + y * e'⟩

/- English proof (translation)
Establish `e1` using `ha g hg`. Rewrite `e1` using `[map_pow, haL g hg, mul_pow, ← pow_mul, mul_comm ((aL g).val), pow_mul]`. Establish `hz : T.ζ L ^ p ^ (L - n) = T.ζ n`. Use `zeta_pow_sub T n (L - n)` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel' hnL]`. Then use the resulting hypothesis.

Rewrite `e1` using `[hz]`. Establish `e2` using `mul_right_cancel₀ (pow_ne_zero _ hR) e1`. Conclude with `((zeta_pow_eq_iff T n _ _).1 e2).symm`.
-/
theorem kum_down (T : GlobalTheory.K5.Tower p Ω) {n L : ℕ} (hnL : n ≤ L) {H : Subgroup (Gal p Ω)} {R : Ω}
    (hR : R ≠ 0) {aL : Gal p Ω → ZMod (p ^ L)} (haL : IsKum T L H R aL)
    {a : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H (R ^ p ^ (L - n)) a) {g : Gal p Ω}
    (hg : g ∈ H) : (a g).val ≡ (aL g).val [MOD p ^ n] := by
  have e1 := ha g hg
  rw [map_pow, haL g hg, mul_pow, ← pow_mul, mul_comm ((aL g).val), pow_mul] at e1
  have hz : T.ζ L ^ p ^ (L - n) = T.ζ n := by
    have := zeta_pow_sub T n (L - n); rwa [Nat.add_sub_cancel' hnL] at this
  rw [hz] at e1
  have e2 := mul_right_cancel₀ (pow_ne_zero _ hR) e1
  exact ((zeta_pow_eq_iff T n _ _).1 e2).symm

end GlobalTheory.K5.LevelDown

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

/- English proof (translation)
Introduce `p _ hp2`. Take `⟨c, hc⟩` from `GlobalTheory.T.hodgeTate_cup_kummer_classes_eq_dlog_determinant p hp2`. Use `⟨c, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ hclo T L n hnL hn ι hι u v α β α' β' hu hv r s hr hs a b lz lq ha hb hlz hlq`. Use `haveI := hclo.clo`.

Establish `hpr : p.Prime` using `Fact.out`. Establish `hL : 1 ≤ L` using `le_trans hn hnL`. Establish `hpos : ∀ k, 0 < p ^ k` using `fun k => pow_pos hpr.pos k`. Establish `hunit : ∀ w : (On p L)ˣ, ι (w : On p L) ≠ 0` using `fun w h => by`. Use `congrArg ι w.mul_inv` as an intermediate fact.

Rewrite `this` using `[map_mul, h, zero_mul, map_one]`. Conclude with `zero_ne_one this`. Establish `hroot : ∀ (w : (On p L)ˣ) (x : Ω), x ^ p ^ n = ι (w : On p L) → ∃ X : Ω, X ≠ 0 ∧ X ^ p ^ (L - n) = x ∧ X ^ p ^ L = (T.ζ L - 1) ^ (0 : ℤ) * ι (w : On p L)`. Introduce `w x hx`. Take `⟨X, hX⟩` from `IsAlgClosed.exists_pow_nat_eq x (hpos (L - n))`.

Use `⟨X, ?_, hX, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hX` using `[zero_pow (pow_ne_zero _ hpr.ne_zero)]`. Rewrite `hx` using `[← hX, zero_pow (pow_ne_zero _ hpr.ne_zero)]`. Conclude with `hunit w hx.symm`.

Rewrite using `[zpow_zero, one_mul, ← hx, ← hX, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnL]`. Take `⟨R, hR0, hR, hRL⟩` from `hroot u r hr`. Take `⟨S, hS0, hS, hSL⟩` from `hroot v s hs`. Establish `hfix` using `LevelDown.fix_emb T L ι hι`. Establish `hgn` using `fun g (hg : g ∈ Gn T L) => (Basic.mem_gn T L g).1 hg`.

Take `⟨aL, haL⟩` from `Basic.exists_isKum T L (Gn T L) hR0 (fun g hg => by`. Rewrite using `[hRL, zpow_zero, one_mul]`. Conclude with `hfix g hg _)`. Take `⟨bL, hbL⟩` from `Basic.exists_isKum T L (Gn T L) hS0 (fun g hg => by`. Rewrite using `[hSL, zpow_zero, one_mul]`.

Conclude with `hfix g hg _)`. Establish `hZ0 : T.ζ (2 * L) ≠ 0` using `(T.prim _).ne_zero (pow_ne_zero _ hpr.ne_zero)`. Establish `hZL : T.ζ (2 * L) ^ p ^ L = T.ζ L`. Rewrite using `[two_mul]`. Conclude with `LevelDown.zeta_pow_sub T L L`.

Establish `hQL : T.qq (2 * L) ^ p ^ L = T.qq L`. Rewrite using `[two_mul]`. Conclude with `LevelDown.qq_pow_sub T L L`. Take `⟨zL, hzL⟩` from `Basic.exists_isKum T L (Gn T L) hZ0 (fun g hg => by`. Rewrite using `[hZL]`.

Conclude with `(hgn g hg).1)`. Take `⟨qL, hqL⟩` from `Basic.exists_isKum T L (Gn T L) (Basic.qq_ne_zero T _) (fun g hg => by`. Rewrite using `[hQL]`. Conclude with `(hgn g hg).2)`. Take `⟨w, hw, hcong⟩` from `hc Ω hclo T L hL ι hι 0 0 u v α β α' β' hu hv R S hRL hSL aL bL zL qL haL hbL hzL hqL`.

Establish `e2 : L + n + (L - n) = 2 * L` using `by omega`. Establish `hZn : T.ζ (2 * L) ^ p ^ (L - n) = T.ζ (L + n)`. Rewrite using `[← e2]`. Conclude with `LevelDown.zeta_pow_sub T (L + n) (L - n)`. Establish `hQn : T.qq (2 * L) ^ p ^ (L - n) = T.qq (L + n)`.

Rewrite using `[← e2]`. Conclude with `LevelDown.qq_pow_sub T (L + n) (L - n)`. Establish `hX : ι (fPi p L 0 0 α β α' β') / (T.ζ L - 1) = ι (α * β' - β * α')`. Establish `hne : T.ζ L - 1 ≠ 0` using `sub_ne_zero.2 ((T.prim L).ne_one (Nat.one_lt_pow (by omega) hpr.one_lt))`. Rewrite using `[div_eq_iff hne]`.

Establish `: fPi p L 0 0 α β α' β' = (xn p L - 1) * (α * β' - β * α')`. Simplify using `only [fPi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_mul, map_sub, hι.1, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨w, LevelDown.locallyConstantModPrimePow_of_le hnL hw, fun g hg h hh => ?_⟩` and prove the remaining obligations. Use `Basic.cong_trans ?_ (LevelDown.cong_mono hnL (hcong g hg h hh))` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hX]`.

Establish `hA : Cong p n ((a g).val : Ω) ((aL g).val : Ω)` using `Basic.cong_natCast (LevelDown.kum_down T hnL hR0 haL (by rw [hR]; exact ha) hg)`. Establish `hB : Cong p n ((b h).val : Ω) ((bL h).val : Ω)` using `Basic.cong_natCast (LevelDown.kum_down T hnL hS0 hbL (by rw [hS]; exact hb) hh)`. Establish `hC : Cong p n ((lz g).val : Ω) ((zL g).val : Ω)` using `Basic.cong_natCast (LevelDown.kum_down T hnL hZ0 hzL (by rw [hZn]; exact hlz) hg)`. Establish `hD : Cong p n ((lq h).val : Ω) ((qL h).val : Ω)` using `Basic.cong_natCast (LevelDown.kum_down T hnL (Basic.qq_ne_zero T _) hqL (by rw [hQn]; exact hlq) hh)`. Establish `iN` using `fun m : ℕ => (LevelDown.isInt_nat (p := p) (Ω := Ω) m)`.

Establish `iP : IsInt p ((p : Ω) ^ c)` using `IsIntegral.pow (iN p) c`. Establish `iX : IsInt p (ι (α * β' - β * α'))` using `LevelDown.isInt_emb T L ι hι _`. Use `Basic.cong_add ?_ ?_` and prove the remaining obligations. Conclude with `LevelDown.cong_mul' (Basic.cong_refl _ _) (LevelDown.cong_mul' hA hB (iN _) (iN _)) ((iN _).mul (iN _)) iP`. Conclude with `LevelDown.cong_mul' (Basic.cong_refl _ _) (LevelDown.cong_mul' hC hD (iN _) (iN _)) ((iN _).mul (iN _)) (iP.mul iX)`.
-/
theorem GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.hodgeTate_cup_kummer_classes_eq_dlog_determinant p hp2
  refine ⟨c, ?_⟩
  intro Ω _ _ hclo T L n hnL hn ι hι u v α β α' β' hu hv r s hr hs a b lz lq ha hb hlz hlq
  haveI := hclo.clo
  have hpr : p.Prime := Fact.out
  have hL : 1 ≤ L := le_trans hn hnL
  have hpos : ∀ k, 0 < p ^ k := fun k => pow_pos hpr.pos k
  have hunit : ∀ w : (On p L)ˣ, ι (w : On p L) ≠ 0 := fun w h => by
    have := congrArg ι w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hroot : ∀ (w : (On p L)ˣ) (x : Ω), x ^ p ^ n = ι (w : On p L) → ∃ X : Ω, X ≠ 0 ∧
      X ^ p ^ (L - n) = x ∧ X ^ p ^ L = (T.ζ L - 1) ^ (0 : ℤ) * ι (w : On p L) := by
    intro w x hx
    obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq x (hpos (L - n))
    refine ⟨X, ?_, hX, ?_⟩
    · rintro rfl
      rw [zero_pow (pow_ne_zero _ hpr.ne_zero)] at hX
      rw [← hX, zero_pow (pow_ne_zero _ hpr.ne_zero)] at hx
      exact hunit w hx.symm
    · rw [zpow_zero, one_mul, ← hx, ← hX, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnL]
  obtain ⟨R, hR0, hR, hRL⟩ := hroot u r hr
  obtain ⟨S, hS0, hS, hSL⟩ := hroot v s hs
  have hfix := LevelDown.fix_emb T L ι hι
  have hgn := fun g (hg : g ∈ Gn T L) => (Basic.mem_gn T L g).1 hg
  obtain ⟨aL, haL⟩ := Basic.exists_isKum T L (Gn T L) hR0 (fun g hg => by
    rw [hRL, zpow_zero, one_mul]; exact hfix g hg _)
  obtain ⟨bL, hbL⟩ := Basic.exists_isKum T L (Gn T L) hS0 (fun g hg => by
    rw [hSL, zpow_zero, one_mul]; exact hfix g hg _)
  have hZ0 : T.ζ (2 * L) ≠ 0 := (T.prim _).ne_zero (pow_ne_zero _ hpr.ne_zero)
  have hZL : T.ζ (2 * L) ^ p ^ L = T.ζ L := by
    rw [two_mul]; exact LevelDown.zeta_pow_sub T L L
  have hQL : T.qq (2 * L) ^ p ^ L = T.qq L := by
    rw [two_mul]; exact LevelDown.qq_pow_sub T L L
  obtain ⟨zL, hzL⟩ := Basic.exists_isKum T L (Gn T L) hZ0 (fun g hg => by
    rw [hZL]; exact (hgn g hg).1)
  obtain ⟨qL, hqL⟩ := Basic.exists_isKum T L (Gn T L) (Basic.qq_ne_zero T _) (fun g hg => by
    rw [hQL]; exact (hgn g hg).2)
  obtain ⟨w, hw, hcong⟩ := hc Ω hclo T L hL ι hι 0 0 u v α β α' β' hu hv R S hRL hSL aL bL zL qL
    haL hbL hzL hqL
  have e2 : L + n + (L - n) = 2 * L := by omega
  have hZn : T.ζ (2 * L) ^ p ^ (L - n) = T.ζ (L + n) := by
    rw [← e2]; exact LevelDown.zeta_pow_sub T (L + n) (L - n)
  have hQn : T.qq (2 * L) ^ p ^ (L - n) = T.qq (L + n) := by
    rw [← e2]; exact LevelDown.qq_pow_sub T (L + n) (L - n)
  have hX : ι (fPi p L 0 0 α β α' β') / (T.ζ L - 1) = ι (α * β' - β * α') := by
    have hne : T.ζ L - 1 ≠ 0 :=
      sub_ne_zero.2 ((T.prim L).ne_one (Nat.one_lt_pow (by omega) hpr.one_lt))
    rw [div_eq_iff hne]
    have : fPi p L 0 0 α β α' β' = (xn p L - 1) * (α * β' - β * α') := by
      simp only [fPi]; push_cast; ring
    rw [this, map_mul, map_sub, hι.1, map_one]; ring
  refine ⟨w, LevelDown.locallyConstantModPrimePow_of_le hnL hw, fun g hg h hh => ?_⟩
  refine Basic.cong_trans ?_ (LevelDown.cong_mono hnL (hcong g hg h hh))
  beta_reduce
  rw [hX]
  have hA : Cong p n ((a g).val : Ω) ((aL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hR0 haL (by rw [hR]; exact ha) hg)
  have hB : Cong p n ((b h).val : Ω) ((bL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hS0 hbL (by rw [hS]; exact hb) hh)
  have hC : Cong p n ((lz g).val : Ω) ((zL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hZ0 hzL (by rw [hZn]; exact hlz) hg)
  have hD : Cong p n ((lq h).val : Ω) ((qL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL (Basic.qq_ne_zero T _) hqL (by rw [hQn]; exact hlq) hh)
  have iN := fun m : ℕ => (LevelDown.isInt_nat (p := p) (Ω := Ω) m)
  have iP : IsInt p ((p : Ω) ^ c) := IsIntegral.pow (iN p) c
  have iX : IsInt p (ι (α * β' - β * α')) := LevelDown.isInt_emb T L ι hι _
  refine Basic.cong_add ?_ ?_
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hA hB (iN _) (iN _)) ((iN _).mul (iN _)) iP
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hC hD (iN _) (iN _)) ((iN _).mul (iN _)) (iP.mul iX)
