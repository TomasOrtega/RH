import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMCB

namespace Formalism.InvariantFactorPaths.MC.GI

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas

variable {p : ℕ} [hp : Fact p.Prime]

def kapE (N r B : ℕ) : ℕ := (N + 4) * (r * B) + 6 * B

/- English proof (translation)
Conclude with `le_refl _`.
-/
theorem kapE_ge (N r B : ℕ) (_hr : 1 ≤ r) : (N + 4) * (r * B) + 6 * B ≤ kapE N r B := by
  exact le_refl _

section term2
variable {N r : ℕ}

/- English proof (translation)
Establish `hpp : p.Prime` using `hp.out`. Establish `hF : ∀ n : ℕ, n.factorial ≠ 0` using `fun n => Nat.factorial_ne_zero n`. Establish `hmul : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → padicValNat p (x * y) = padicValNat p x + padicValNat p y` using `fun x y hx hy => padicValNat.mul hx hy`. Establish `hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ), (∀ i, f i ≠ 0) → padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i)`. Introduce `ι s f hf`.

Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `x s hx ih`. Rewrite using `[Finset.prod_insert hx, Finset.sum_insert hx, hmul _ _ (hf x) (Finset.prod_ne_zero_iff.2 (fun i _ => hf i)), ih]`. Establish `hlog : ∀ m, m ≤ LL.total + LL.deg (Fin.last N) + r → Nat.log p m ≤ B` using `fun m hm => (Nat.log_mono_right hm).trans hB`.

Establish `hch : ∀ n k : ℕ, n ≤ LL.total + LL.deg (Fin.last N) + r → padicValNat p (n.choose k) ≤ B`. Introduce `n k hn`. Rewrite using `[← Nat.factorization_def _ hpp]`. Conclude with `Nat.factorization_choose_le_log.trans (hlog n hn)`. Establish `hsplit : ∀ n k : ℕ, k ≤ n → padicValNat p n.factorial = padicValNat p (n.choose k) + padicValNat p k.factorial + padicValNat p (n - k).factorial`.

Introduce `n k hk`. Rewrite using `[← Nat.choose_mul_factorial_mul_factorial hk, hmul _ _ (mul_ne_zero (Nat.choose_pos hk).ne' (hF _)) (hF _), hmul _ _ (Nat.choose_pos hk).ne' (hF _)]`. Establish `hgroup : ∀ (s : Finset (Fin r)) (x : Fin r → ℕ), ∑ i ∈ s, x i ≤ LL.total + LL.deg (Fin.last N) + r → padicValNat p (∑ i ∈ s, x i).factorial ≤ ∑ i ∈ s, padicValNat p (x i).factorial + s.card * B`. Introduce `s x`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Introduce `_`. Simplify using the standard rewrite rules. Introduce `y s hy ih hle`. Rewrite `hle` using `[Finset.sum_insert hy]`. Rewrite using `[Finset.sum_insert hy, Finset.sum_insert hy, Finset.card_insert_of_notMem hy]`.

Establish `h1` using `hsplit (x y + ∑ i ∈ s, x i) (x y) (Nat.le_add_right _ _)`. Rewrite `h1` using `[Nat.add_sub_cancel_left]`. Establish `h2` using `hch (x y + ∑ i ∈ s, x i) (x y) hle`. Establish `h3` using `ih (le_trans (Nat.le_add_left _ _) hle)`. Rewrite using `[h1]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hT : ∀ i, LL.deg i ≤ LL.total` using `fun i => by`. Unfold `Letters.total`. Conclude with `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `hD : LL.deg (Fin.last N) ≤ LL.total` using `hT _`.

Establish `hδv : ∀ k, δv δ k = ∑ ρ, δ (k, ρ)` using `fun _ => rfl`. Establish `hgδ : ∀ k, δv δ k ≤ LL.total + LL.deg (Fin.last N) + r → padicValNat p (δv δ k).factorial ≤ ∑ ρ, padicValNat p (δ (k, ρ)).factorial + r * B`. Introduce `k hk`. Rewrite `hk`, the goal using `[hδv]`. Establish `h` using `hgroup Finset.univ (fun ρ => δ (k, ρ)) hk`.

Rewrite `h` using `[Finset.card_univ, Fintype.card_fin]`. Then use the resulting hypothesis. Establish `hC1 : j.choose a ≠ 0` using `(Nat.choose_pos ha).ne'`. Establish `hC2 : j.choose a' ≠ 0` using `(Nat.choose_pos ha').ne'`. Establish `hCDj : (LL.deg (Fin.last N)).choose j ≠ 0` using `(Nat.choose_pos hj).ne'`. Establish `hPne : ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun v _ => hF _)`.

Establish `hP2 : ∏ i, (LL.deg i).factorial ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun i _ => hF _)`. Establish `P1 : padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial * ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) = padicValNat p (j.choose a) + padicValNat p (j.choose a') + padicValNat p d1 + padicValNat p d2 + padicValNat p a'.factorial + ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin …`. Rewrite using `[hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _)) hPne, hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _), hmul _ _ (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2', hmul _ _ (mul_ne_zero hC1 hC2) hd1', hmul _ _ hC1 …`. Establish `P2 : padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial * ∏ i, (LL.deg i).factorial) = padicValNat p ((LL.deg (Fin.last N)).choose j) + (padicValNat p j.factorial + padicValNat p j.factorial) + padicValNat p LL.total.factorial + ∑ i, padicValNat …`. Rewrite using `[hmul _ _ (mul_ne_zero (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _)) hP2, hmul _ _ (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _), hmul _ _ hCDj (pow_ne_zero _ (hF _)), sq, hmul _ _ (hF _) (hF _), hprod _ _ (fun i => hF _)]`.

Establish `S1 : ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial = ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial + ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.last N), ρ)).factorial + ∑ ρ : Fin r, padicValNat p (δ (Fin.la …`. Rewrite using `[Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]`. Establish `S2 : ∑ i, padicValNat p (LL.deg i).factorial = ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial + padicValNat p (LL.deg (Fin.last N)).factorial`. Rewrite using `[Fin.sum_univ_castSucc]`. Establish `G1 : ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial ≤ ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial + N * (r * B)`.

Establish `h` using `Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun k _ => by`. Establish `hk'` using `hgδ (Fin.castSucc (Fin.castSucc k)) (by rw [hk k]; have := hT (Fin.castSucc k); omega)`. Rewrite `hk'` using `[hk k]`. Conclude with `hk')`. Rewrite `h` using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.

Conclude with `h`. Establish `GW` using `hgδ (Fin.castSucc (Fin.last N)) (by rw [hW]; omega)`. Rewrite `GW` using `[hW]`. Establish `GY` using `hgδ (Fin.last (N + 1)) (by rw [hY]; omega)`. Rewrite `GY` using `[hY]`.

Establish `hja : j - a ≤ LL.total` using `by omega`. Establish `E1` using `hsplit j a ha`. Establish `E2` using `hsplit j a' ha'`. Establish `E3` using `hsplit (LL.deg (Fin.last N)) j hj`. Establish `E4` using `hsplit LL.total (j - a) hja`.

Establish `B1` using `hch (LL.deg (Fin.last N)) j (by omega)`. Establish `B2` using `hch LL.total (j - a) (by omega)`. Establish `B3` using `hch j a' (by omega)`. Rewrite using `[P1, P2, S1, S2]`. Unfold `kapE`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem term_valE (LL : Letters (N + 1)) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hk : ∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k))
    (hW : δv δ (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) - j)
    (hY : δv δ (Fin.last (N + 1)) = LL.total - (j - a))
    (d1 d2 : ℕ) (hd1 : padicValNat p a.factorial ≤ padicValNat p d1) (hd1' : d1 ≠ 0)
    (hd2 : padicValNat p a'.factorial ≤ padicValNat p d2) (hd2' : d2 ≠ 0) :
    -(kapE N r B : ℤ) + ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))) +
      ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ))) -
      (padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) +
      (padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) : ℤ) ≤ 0 := by
  have hpp : p.Prime := hp.out
  have hF : ∀ n : ℕ, n.factorial ≠ 0 := fun n => Nat.factorial_ne_zero n
  have hmul : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → padicValNat p (x * y) = padicValNat p x + padicValNat p y :=
    fun x y hx hy => padicValNat.mul hx hy
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ), (∀ i, f i ≠ 0) →
      padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
    intro ι s f hf
    classical
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro x s hx ih
      rw [Finset.prod_insert hx, Finset.sum_insert hx,
        hmul _ _ (hf x) (Finset.prod_ne_zero_iff.2 (fun i _ => hf i)), ih]
  have hlog : ∀ m, m ≤ LL.total + LL.deg (Fin.last N) + r → Nat.log p m ≤ B :=
    fun m hm => (Nat.log_mono_right hm).trans hB
  have hch : ∀ n k : ℕ, n ≤ LL.total + LL.deg (Fin.last N) + r → padicValNat p (n.choose k) ≤ B := by
    intro n k hn
    rw [← Nat.factorization_def _ hpp]
    exact Nat.factorization_choose_le_log.trans (hlog n hn)
  have hsplit : ∀ n k : ℕ, k ≤ n → padicValNat p n.factorial =
      padicValNat p (n.choose k) + padicValNat p k.factorial + padicValNat p (n - k).factorial := by
    intro n k hk
    rw [← Nat.choose_mul_factorial_mul_factorial hk,
      hmul _ _ (mul_ne_zero (Nat.choose_pos hk).ne' (hF _)) (hF _),
      hmul _ _ (Nat.choose_pos hk).ne' (hF _)]
  have hgroup : ∀ (s : Finset (Fin r)) (x : Fin r → ℕ),
      ∑ i ∈ s, x i ≤ LL.total + LL.deg (Fin.last N) + r →
      padicValNat p (∑ i ∈ s, x i).factorial ≤ ∑ i ∈ s, padicValNat p (x i).factorial + s.card * B := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · intro _; simp
    · intro y s hy ih hle
      rw [Finset.sum_insert hy] at hle
      rw [Finset.sum_insert hy, Finset.sum_insert hy, Finset.card_insert_of_notMem hy]
      have h1 := hsplit (x y + ∑ i ∈ s, x i) (x y) (Nat.le_add_right _ _)
      rw [Nat.add_sub_cancel_left] at h1
      have h2 := hch (x y + ∑ i ∈ s, x i) (x y) hle
      have h3 := ih (le_trans (Nat.le_add_left _ _) hle)
      rw [h1]
      nlinarith
  have hT : ∀ i, LL.deg i ≤ LL.total := fun i => by
    unfold Letters.total
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hD : LL.deg (Fin.last N) ≤ LL.total := hT _
  have hδv : ∀ k, δv δ k = ∑ ρ, δ (k, ρ) := fun _ => rfl
  have hgδ : ∀ k, δv δ k ≤ LL.total + LL.deg (Fin.last N) + r →
      padicValNat p (δv δ k).factorial ≤ ∑ ρ, padicValNat p (δ (k, ρ)).factorial + r * B := by
    intro k hk
    rw [hδv] at hk ⊢
    have h := hgroup Finset.univ (fun ρ => δ (k, ρ)) hk
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hC1 : j.choose a ≠ 0 := (Nat.choose_pos ha).ne'
  have hC2 : j.choose a' ≠ 0 := (Nat.choose_pos ha').ne'
  have hCDj : (LL.deg (Fin.last N)).choose j ≠ 0 := (Nat.choose_pos hj).ne'
  have hPne : ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun v _ => hF _)
  have hP2 : ∏ i, (LL.deg i).factorial ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hF _)
  have P1 : padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) =
      padicValNat p (j.choose a) + padicValNat p (j.choose a') + padicValNat p d1 + padicValNat p d2 +
        padicValNat p a'.factorial +
        ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _)) hPne,
      hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _),
      hmul _ _ (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2',
      hmul _ _ (mul_ne_zero hC1 hC2) hd1', hmul _ _ hC1 hC2, hprod _ _ (fun v => hF _),
      Fintype.sum_prod_type]
  have P2 : padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) =
      padicValNat p ((LL.deg (Fin.last N)).choose j) +
        (padicValNat p j.factorial + padicValNat p j.factorial) +
        padicValNat p LL.total.factorial + ∑ i, padicValNat p (LL.deg i).factorial := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _)) hP2,
      hmul _ _ (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _),
      hmul _ _ hCDj (pow_ne_zero _ (hF _)), sq, hmul _ _ (hF _) (hF _), hprod _ _ (fun i => hF _)]
  have S1 : ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial =
      ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial +
        ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.last N), ρ)).factorial +
        ∑ ρ : Fin r, padicValNat p (δ (Fin.last (N + 1), ρ)).factorial := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have S2 : ∑ i, padicValNat p (LL.deg i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial +
        padicValNat p (LL.deg (Fin.last N)).factorial := by
    rw [Fin.sum_univ_castSucc]
  have G1 : ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial ≤
      ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial +
        N * (r * B) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun k _ => by
      have hk' := hgδ (Fin.castSucc (Fin.castSucc k)) (by rw [hk k]; have := hT (Fin.castSucc k); omega)
      rw [hk k] at hk'
      exact hk')
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    exact h
  have GW := hgδ (Fin.castSucc (Fin.last N)) (by rw [hW]; omega)
  rw [hW] at GW
  have GY := hgδ (Fin.last (N + 1)) (by rw [hY]; omega)
  rw [hY] at GY
  have hja : j - a ≤ LL.total := by omega
  have E1 := hsplit j a ha
  have E2 := hsplit j a' ha'
  have E3 := hsplit (LL.deg (Fin.last N)) j hj
  have E4 := hsplit LL.total (j - a) hja
  have B1 := hch (LL.deg (Fin.last N)) j (by omega)
  have B2 := hch LL.total (j - a) (by omega)
  have B3 := hch j a' (by omega)
  rw [P1, P2, S1, S2]
  unfold kapE
  push_cast
  nlinarith

end term2

section term3
variable {N r : ℕ}

/- English proof (translation)
Establish `hxy` using `xW_ne_yE (N := N) ρ`. Use `set s : Fin (N + 1 + 1) × Fin r →₀ ℕ := Finsupp.single (xW ρ) 1 + Finsupp.single (yE ρ) 1 with hs`. Distinguish the cases in `h1 : β (xW ρ) < a`. Apply `(IVP.zero (p := p) _).congr` to reduce the goal to its premises. Introduce `m`.

Unfold `termF`. Rewrite using `[X_pow_mul_monomial, Dop_pow_monomial_lt _ _ hxy a _ h (by simp [Finsupp.single_apply, hxy]; exact h1), fock_zero_left]`. Simplify using the standard rewrite rules. Distinguish the cases in `h2 : γ (xW ρ) < a'`. Apply `(IVP.zero (p := p) _).congr` to reduce the goal to its premises.

Introduce `m`. Unfold `termF`. Rewrite using `[X_pow_mul_monomial (yE ρ) m γ, Dop_pow_monomial_lt _ _ hxy a' _ h' (by simp [Finsupp.single_apply, hxy]; exact h2), fock_zero_right']`. Simplify using the standard rewrite rules. Use `push_neg at h1 h2`.

Establish `hle : ∀ (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (t : ℕ), t ≤ δ (xW ρ) → δ (xW ρ) ≤ δ (yE ρ) → t • s ≤ δ`. Introduce `δ t ht1 ht2 v`. Simplify using `only [hs, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]`. Distinguish the cases in `hv1 : xW ρ = v`. Substitute `hv1` using the available equality.

Simplify using `[Ne.symm hxy]`. Conclude with `ht1`. Distinguish the cases in `hv2 : yE ρ = v`. Substitute `hv2` using the available equality. Simplify using `[hv1]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[hv1, hv2]`. Take `⟨β₀, rfl⟩ : ∃ β₀, β = β₀ + a • s` from `⟨β - a • s, (tsub_add_cancel_of_le (hle β a h1 hβp)).symm⟩`. Take `⟨γ₀, rfl⟩ : ∃ γ₀, γ = γ₀ + a' • s` from `⟨γ - a' • s, (tsub_add_cancel_of_le (hle γ a' h2 hγp)).symm⟩`. Distinguish the cases in `hb : β₀ = γ₀`.

Use `swap`. Apply `(IVP.zero (p := p) _).congr` to reduce the goal to its premises. Introduce `m`. Unfold `termF`. Rewrite using `[fock_Dop_term _ _ hxy, if_neg hb]`.

Simplify using the standard rewrite rules. Substitute `hb` using the available equality. Use `set o := LL.deg (Fin.last N) with ho`. Use `set S := LL.total with hS`. Establish `hoS : o ≤ S` using `deg_le_total LL (Fin.last N)`.

Establish `hsδ : ∀ t : ℕ, δv (t • s) = Pi.single (Fin.castSucc (Fin.last N)) t + Pi.single (Fin.last (N + 1)) t`. Introduce `t`. Rewrite using `[hs, smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one, δv_add, δv_single', δv_single']`. Establish `hβd' : δv β₀ + Pi.single (Fin.castSucc (Fin.last N)) a + Pi.single (Fin.last (N + 1)) a + (j - a) • eWY = (LL.snoc LL.total).deg`. Rewrite using `[← hβd, δv_add, hsδ, add_assoc (δv β₀)]`.

Take `⟨hk, hW, hY⟩` from `comp_facts LL (j - a) β₀ a a hβd'`. Use `set e := β₀ (yE ρ) + a with he`. Use `set e' := β₀ (yE ρ) + a' with he'`. Establish `heS : e ≤ S - (j - a)`. Use `le_δv β₀ (Fin.last (N + 1)) ρ` as an intermediate fact.

Simplify using `only [yE] at he`. Use linear arithmetic over natural numbers and integers. Use `set c1 := o + S + r + z - 1 - j with hc1`. Use `set d1 := (β₀ (xW ρ) + a).descFactorial a with hd1`. Use `set d2 := (β₀ (xW ρ) + a').descFactorial a' with hd2`.

Use `set δh := β₀ + Finsupp.single (yE ρ) a with hδh`. Use `set Num := j.choose a * j.choose a' * d1 * d2 * a'.factorial * ∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial with hNum`. Use `set Den := o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial with hDen`. Use `set K : ℚ_[p] := (p : ℚ_[p]) ^ (kapE N r B) * ((-1 : ℚ_[p]) ^ j * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p])) with hK`. Establish `nd1 : d1 ≠ 0`.

Rewrite using `[hd1]`. Introduce `h0`. Rewrite `h0` using `[Nat.descFactorial_eq_zero_iff_lt]`. Use linear arithmetic over natural numbers and integers. Establish `nd2 : d2 ≠ 0`.

Rewrite using `[hd2]`. Introduce `h0`. Rewrite `h0` using `[Nat.descFactorial_eq_zero_iff_lt]`. Use linear arithmetic over natural numbers and integers. Establish `hNum0 : Num ≠ 0`.

Rewrite using `[hNum]`. Use `Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos ha).ne' (Nat.choose_pos ha').ne') nd1) nd2) (Nat.factorial_pos _).ne') ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')`. Establish `hDen0 : Den ≠ 0`. Rewrite using `[hDen]`.

Use `Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos hj).ne' (pow_ne_zero _ (Nat.factorial_pos _).ne')) (Nat.factorial_pos _).ne') ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')`. Establish `hδv : δv δh = δv β₀ + Pi.single (Fin.last (N + 1)) a` using `by rw [hδh, δv_add, δv_single']`. Establish `hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k` using `fun k h => Fin.castSucc_ne_last k h.symm`. Establish `hKn : ‖K‖ ≤ 1`.

Rewrite using `[hK]`. Use `norm_K _ h h' _ _ hh hh' Num Den hNum0 hDen0 _ (by simp) ?_` and prove the remaining obligations. Rewrite using `[hNum, hDen]`. Use `term_valE LL hr B hB j a a' hj ha ha' δh ?_ ?_ ?_ d1 d2 ?_ nd1 ?_ nd2` and prove the remaining obligations. Introduce `k`.

Rewrite using `[hδv, Pi.add_apply, Pi.single_apply, if_neg (hne _).symm, add_zero, hk k]`. Rewrite using `[hδv, Pi.add_apply, Pi.single_apply, if_neg (Fin.castSucc_ne_last _), add_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hδv, Pi.add_apply, Pi.single_apply, if_pos rfl]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hd1]; exact vdesc_ge _ _ (by omega)`. Rewrite using `[hd2]; exact vdesc_ge _ _ (by omega)`. Establish `I1` using `((IVP.choose_add (p := p) c1 (o - j)).mul (IVP.choose_add e e)).mul (IVP.choose_add e' a')`. Use `((I1.smul K hKn).mono (by omega)).congr ?_` and prove the remaining obligations. Introduce `m`.

Unfold `termF`. Rewrite using `[fock_Dop_term _ _ hxy, if_pos rfl, Nat.add_sub_cancel]`. Establish `hjM : j ≤ o + (m + S) + r + z - 1` using `by omega`. Establish `hMj : o + (m + S) + r + z - 1 - j = m + c1` using `by omega`. Establish `hMo : (((o + (m + S) + r + z - 1).choose o : ℕ) : ℚ_[p]) = (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) * (((o + (m + S) + r + z - 1 - j).choose (o - j) : ℕ) : ℚ_[p]) / ((o.choose j : ℕ) : ℚ_[p])`.

Use `Nat.choose_mul (n := o + (m + S) + r + z - 1) (k := o) (s := j) hj` as an intermediate fact. Rewrite using `[eq_div_iff (by exact_mod_cast (Nat.choose_pos hj).ne')]`. Conclude with `this` after adjusting the coercions. Rewrite using `[hMo, hMj, Nat.descFactorial_eq_factorial_mul_choose (m + e') a']`. Establish `hwf : wf (p` using `p) δh = ((∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial : ℕ) : ℚ_[p]) := by`.

Unfold `wf`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hwf, hK, hNum, hDen]`. Establish `n1 : (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) ≠ 0`.

Conclude with `(Nat.choose_pos hjM).ne'` after adjusting the coercions. Establish `n2 : ((o.choose j : ℕ) : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Nat.choose_pos hj).ne'`. Establish `n3 : ((j.factorial : ℕ) : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos _).ne'`. Establish `n4 : ((S.factorial : ℕ) : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos _).ne'`. Establish `n5 : ((m.factorial : ℕ) : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos _).ne'`.

Establish `n6 : ((∏ i, (LL.deg i).factorial : ℕ) : ℚ_[p]) ≠ 0`. Conclude with `Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')` after adjusting the coercions. Move the coercions through the operations in `at n6 ⊢`. Rewrite using `[← hd1, ← hd2, ← he, ← ho, ← hS]`. Establish `hc` using `mul_inv_cancel₀ n1`.

Establish `hm` using `mul_inv_cancel₀ n5`. Simplify using `only [div_eq_mul_inv, mul_inv]`. Take the linear combination `(-((p : ℚ_[p]) ^ kapE N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) * ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) * (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) * (((m + e).choose e …`.
-/
theorem termF_IVPE (LL : Letters (N + 1)) (ρ : Fin r) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (z j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hβd : δv β + (j - a) • eWY = (LL.snoc LL.total).deg) (hβp : β (xW ρ) ≤ β (yE ρ))
    (hγd : δv γ + (j - a') • eWY = (LL.snoc LL.total).deg) (hγp : γ (xW ρ) ≤ γ (yE ρ))
    (h h' : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))))
    (hh' : ‖h'‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ)))) :
    IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kapE N r B) * termF LL ρ z j a a' β γ h h' m) := by
  have hxy := xW_ne_yE (N := N) ρ
  set s : Fin (N + 1 + 1) × Fin r →₀ ℕ := Finsupp.single (xW ρ) 1 + Finsupp.single (yE ρ) 1 with hs
  by_cases h1 : β (xW ρ) < a
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial, Dop_pow_monomial_lt _ _ hxy a _ h
      (by simp [Finsupp.single_apply, hxy]; exact h1), fock_zero_left]
    simp
  by_cases h2 : γ (xW ρ) < a'
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial (yE ρ) m γ, Dop_pow_monomial_lt _ _ hxy a' _ h'
      (by simp [Finsupp.single_apply, hxy]; exact h2), fock_zero_right']
    simp
  push_neg at h1 h2
  have hle : ∀ (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (t : ℕ), t ≤ δ (xW ρ) → δ (xW ρ) ≤ δ (yE ρ) → t • s ≤ δ := by
    intro δ t ht1 ht2 v
    simp only [hs, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hv1 : xW ρ = v
    · subst hv1; simp [Ne.symm hxy]; exact ht1
    · by_cases hv2 : yE ρ = v
      · subst hv2; simp [hv1]; omega
      · simp [hv1, hv2]
  obtain ⟨β₀, rfl⟩ : ∃ β₀, β = β₀ + a • s := ⟨β - a • s, (tsub_add_cancel_of_le (hle β a h1 hβp)).symm⟩
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀, γ = γ₀ + a' • s := ⟨γ - a' • s, (tsub_add_cancel_of_le (hle γ a' h2 hγp)).symm⟩
  by_cases hb : β₀ = γ₀
  swap
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [fock_Dop_term _ _ hxy, if_neg hb]
    simp
  subst hb
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  have hoS : o ≤ S := deg_le_total LL (Fin.last N)

  have hsδ : ∀ t : ℕ, δv (t • s) = Pi.single (Fin.castSucc (Fin.last N)) t + Pi.single (Fin.last (N + 1)) t := by
    intro t
    rw [hs, smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one, δv_add,
      δv_single', δv_single']
  have hβd' : δv β₀ + Pi.single (Fin.castSucc (Fin.last N)) a + Pi.single (Fin.last (N + 1)) a + (j - a) • eWY =
      (LL.snoc LL.total).deg := by
    rw [← hβd, δv_add, hsδ, add_assoc (δv β₀)]
  obtain ⟨hk, hW, hY⟩ := comp_facts LL (j - a) β₀ a a hβd'
  set e := β₀ (yE ρ) + a with he
  set e' := β₀ (yE ρ) + a' with he'
  have heS : e ≤ S - (j - a) := by
    have := le_δv β₀ (Fin.last (N + 1)) ρ
    simp only [yE] at he
    omega
  set c1 := o + S + r + z - 1 - j with hc1
  set d1 := (β₀ (xW ρ) + a).descFactorial a with hd1
  set d2 := (β₀ (xW ρ) + a').descFactorial a' with hd2
  set δh := β₀ + Finsupp.single (yE ρ) a with hδh
  set Num := j.choose a * j.choose a' * d1 * d2 * a'.factorial * ∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial
    with hNum
  set Den := o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial with hDen
  set K : ℚ_[p] := (p : ℚ_[p]) ^ (kapE N r B) * ((-1 : ℚ_[p]) ^ j * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p]))
    with hK
  have nd1 : d1 ≠ 0 := by
    rw [hd1]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have nd2 : d2 ≠ 0 := by
    rw [hd2]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have hNum0 : Num ≠ 0 := by
    rw [hNum]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero
      (Nat.choose_pos ha).ne' (Nat.choose_pos ha').ne') nd1) nd2) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos hj).ne'
      (pow_ne_zero _ (Nat.factorial_pos _).ne')) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')

  have hδv : δv δh = δv β₀ + Pi.single (Fin.last (N + 1)) a := by rw [hδh, δv_add, δv_single']
  have hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k :=
    fun k h => Fin.castSucc_ne_last k h.symm
  have hKn : ‖K‖ ≤ 1 := by
    rw [hK]
    refine norm_K _ h h' _ _ hh hh' Num Den hNum0 hDen0 _ (by simp) ?_
    rw [hNum, hDen]
    refine term_valE LL hr B hB j a a' hj ha ha' δh ?_ ?_ ?_ d1 d2 ?_ nd1 ?_ nd2
    · intro k
      rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (hne _).symm, add_zero, hk k]
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (Fin.castSucc_ne_last _), add_zero]; omega
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_pos rfl]; omega
    · rw [hd1]; exact vdesc_ge _ _ (by omega)
    · rw [hd2]; exact vdesc_ge _ _ (by omega)
  have I1 := ((IVP.choose_add (p := p) c1 (o - j)).mul (IVP.choose_add e e)).mul (IVP.choose_add e' a')
  refine ((I1.smul K hKn).mono (by omega)).congr ?_
  intro m
  unfold termF
  rw [fock_Dop_term _ _ hxy, if_pos rfl, Nat.add_sub_cancel]
  have hjM : j ≤ o + (m + S) + r + z - 1 := by omega
  have hMj : o + (m + S) + r + z - 1 - j = m + c1 := by omega
  have hMo : (((o + (m + S) + r + z - 1).choose o : ℕ) : ℚ_[p]) =
      (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) *
        (((o + (m + S) + r + z - 1 - j).choose (o - j) : ℕ) : ℚ_[p]) / ((o.choose j : ℕ) : ℚ_[p]) := by
    have := Nat.choose_mul (n := o + (m + S) + r + z - 1) (k := o) (s := j) hj
    rw [eq_div_iff (by exact_mod_cast (Nat.choose_pos hj).ne')]
    exact_mod_cast this
  rw [hMo, hMj, Nat.descFactorial_eq_factorial_mul_choose (m + e') a']
  have hwf : wf (p := p) δh = ((∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial : ℕ) : ℚ_[p]) := by
    unfold wf; push_cast; rfl
  rw [hwf, hK, hNum, hDen]
  have n1 : (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjM).ne'
  have n2 : ((o.choose j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have n3 : ((j.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n4 : ((S.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n5 : ((m.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n6 : ((∏ i, (LL.deg i).factorial : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  push_cast at n6 ⊢
  rw [← hd1, ← hd2, ← he, ← ho, ← hS]
  have hc := mul_inv_cancel₀ n1
  have hm := mul_inv_cancel₀ n5
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-((p : ℚ_[p]) ^ kapE N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹)) * hc +
    (-((p : ℚ_[p]) ^ kapE N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹) *
      ((((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) * (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹)) * hm

end term3

end Formalism.InvariantFactorPaths.MC.GI

namespace Formalism.InvariantFactorPaths.MC

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas Formalism.InvariantFactorPaths.MC.GI

/- English proof (translation)
Introduce `p _ N r LL ρ z f f' hr hW hf hf'`. Use `set B := Nat.log p (LL.total + LL.deg (Fin.last N) + r) with hB`. Establish `hκ : (N + 4) * (r * B) + 6 * B = kapE N r B` using `rfl`. Establish `hwe : ∀ c : Fin r, wv (N` using `N) c ≠ ev c := by`. Introduce `c`.

Simplify using `[wv, ev, Fin.castSucc_ne_last]`. Establish `facts : ∀ g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p], g ∈ PolZ p r LL → (∀ b ≤ LL.total + LL.deg (Fin.last N) + r, ∀ β, ‖coeff β ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g))‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)))) ∧ (∀ b, ∀ β ∈ …`. Introduce `g hg`. Establish `hgP : g ∈ Pol p r LL` using `(Submodule.mem_inf.mp hg).1`. Establish `hgI : g ∈ IntPol p (Fin (N + 1) × Fin r)` using `(Submodule.mem_inf.mp hg).2`.

Establish `hG` using `aeval_int LL ρ g (intPol_coeff g hgI)`. Establish `hGg` using `aeval_good LL ρ hW g hgP`. Use `⟨fun b hb β => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `FT_pow_coeff_norm (p := p) wv ev hwe (LL.total + LL.deg (Fin.last N) + r) B le_rfl 1 (aeval (freezeSub p LL ρ) g) hG (univ.erase ρ) b hb β`. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[one_mul]`. Apply `zpow_mono'` to reduce the goal to its premises. Establish `: (univ.erase ρ).card * B ≤ r * B`. Apply `Nat.mul_le_mul_right` to reduce the goal to its premises. Rewrite using `[card_erase_of_mem (mem_univ ρ), card_univ, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Establish `: (((univ.erase ρ).card * B : ℕ) : ℤ) ≤ ((r * B : ℕ) : ℤ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `supp_FT_pow wv ev (univ.erase ρ) (fun b β => δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) ?_ hwe _ ?_` and prove the remaining obligations. Introduce `b β c hc ⟨h1, h2⟩`.

Establish `hcρ : c ≠ ρ` using `ne_of_mem_erase hc`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, δv_add, δv_add, δv_single, δv_single, succ_nsmul, eWY]`. Normalize the expressions using the abelian group laws. Simplify `h2` using `[Finsupp.single_apply, xW, yE, wv, ev, hcρ, Ne.symm hcρ, Fin.castSucc_ne_last]`.

Introduce `β hβ`. Take `⟨h1, h2⟩` from `hGg β hβ`. Conclude with `⟨by rw [zero_smul, add_zero]; exact h1, h2⟩`. Take `⟨hc1, hs1⟩` from `facts f hf`. Take `⟨hc2, hs2⟩` from `facts f' hf'`.

Establish `hIVP : IVP p (LL.total + LL.deg (Fin.last N)) (fun m => (p : ℚ_[p]) ^ (kapE N r B) * tieGam p LL ρ z (m + LL.total) f f')`. Simplify using `only [tieGam_expand, Finset.mul_sum]`. Apply `IVP.sum` to reduce the goal to its premises. Introduce `j hj`. Apply `IVP.sum` to reduce the goal to its premises.

Introduce `a ha`. Apply `IVP.sum` to reduce the goal to its premises. Introduce `a' ha'`. Apply `IVP.sum` to reduce the goal to its premises. Introduce `β hβ`.

Apply `IVP.sum` to reduce the goal to its premises. Introduce `γ hγ`. Rewrite `hj`, `ha`, `ha'` using `[mem_range]`. Establish `hjo : j ≤ LL.deg (Fin.last N)` using `by omega`. Establish `hoS` using `deg_le_total LL (Fin.last N)`.

Take `⟨hβd, hβp⟩` from `hs1 (j - a) β hβ`. Take `⟨hγd, hγp⟩` from `hs2 (j - a') γ hγ`. Conclude with `termF_IVPE LL ρ hr B le_rfl z j a a' hjo (by omega) (by omega) β γ hβd hβp hγd hγp _ _ (hc1 (j - a) (by omega) β) (hc2 (j - a') (by omega) γ)`. Take `⟨c, hc⟩` from `hIVP.toChoose (S := LL.total)`. Use `⟨c, fun n hn => ?_⟩` and prove the remaining obligations.

Use `hc n hn` as an intermediate fact. Simplify using `only [Nat.sub_add_cancel hn] at this`. Rewrite using `[hκ]`. Conclude with `this`.
-/
theorem gamma_integral_holds : GamIntC := by
  intro p _ N r LL ρ z f f' hr hW hf hf'
  set B := Nat.log p (LL.total + LL.deg (Fin.last N) + r) with hB
  have hκ : (N + 4) * (r * B) + 6 * B = kapE N r B := rfl
  have hwe : ∀ c : Fin r, wv (N := N) c ≠ ev c := by
    intro c; simp [wv, ev, Fin.castSucc_ne_last]

  have facts : ∀ g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p], g ∈ PolZ p r LL →
      (∀ b ≤ LL.total + LL.deg (Fin.last N) + r, ∀ β,
        ‖coeff β ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g))‖ ≤
          (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)))) ∧
      (∀ b, ∀ β ∈ ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g)).support,
        δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) := by
    intro g hg
    have hgP : g ∈ Pol p r LL := (Submodule.mem_inf.mp hg).1
    have hgI : g ∈ IntPol p (Fin (N + 1) × Fin r) := (Submodule.mem_inf.mp hg).2
    have hG := aeval_int LL ρ g (intPol_coeff g hgI)
    have hGg := aeval_good LL ρ hW g hgP
    refine ⟨fun b hb β => ?_, ?_⟩
    · have h1 := FT_pow_coeff_norm (p := p) wv ev hwe (LL.total + LL.deg (Fin.last N) + r) B le_rfl 1
        (aeval (freezeSub p LL ρ) g) hG (univ.erase ρ) b hb β
      refine h1.trans ?_
      rw [one_mul]
      apply zpow_mono'
      have : (univ.erase ρ).card * B ≤ r * B := by
        apply Nat.mul_le_mul_right
        rw [card_erase_of_mem (mem_univ ρ), card_univ, Fintype.card_fin]; omega
      have : (((univ.erase ρ).card * B : ℕ) : ℤ) ≤ ((r * B : ℕ) : ℤ) := by exact_mod_cast this
      linarith
    · refine supp_FT_pow wv ev (univ.erase ρ)
        (fun b β => δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) ?_ hwe _ ?_
      · intro b β c hc ⟨h1, h2⟩
        have hcρ : c ≠ ρ := ne_of_mem_erase hc
        refine ⟨?_, ?_⟩
        · rw [← h1, δv_add, δv_add, δv_single, δv_single, succ_nsmul, eWY]
          abel
        · simpa [Finsupp.single_apply, xW, yE, wv, ev, hcρ, Ne.symm hcρ, Fin.castSucc_ne_last] using h2
      · intro β hβ
        obtain ⟨h1, h2⟩ := hGg β hβ
        exact ⟨by rw [zero_smul, add_zero]; exact h1, h2⟩
  obtain ⟨hc1, hs1⟩ := facts f hf
  obtain ⟨hc2, hs2⟩ := facts f' hf'
  have hIVP : IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kapE N r B) * tieGam p LL ρ z (m + LL.total) f f') := by
    simp only [tieGam_expand, Finset.mul_sum]
    apply IVP.sum; intro j hj
    apply IVP.sum; intro a ha
    apply IVP.sum; intro a' ha'
    apply IVP.sum; intro β hβ
    apply IVP.sum; intro γ hγ
    rw [mem_range] at hj ha ha'
    have hjo : j ≤ LL.deg (Fin.last N) := by omega
    have hoS := deg_le_total LL (Fin.last N)
    obtain ⟨hβd, hβp⟩ := hs1 (j - a) β hβ
    obtain ⟨hγd, hγp⟩ := hs2 (j - a') γ hγ
    exact termF_IVPE LL ρ hr B le_rfl z j a a' hjo (by omega) (by omega) β γ hβd hβp hγd hγp _ _
      (hc1 (j - a) (by omega) β) (hc2 (j - a') (by omega) γ)
  obtain ⟨c, hc⟩ := hIVP.toChoose (S := LL.total)
  refine ⟨c, fun n hn => ?_⟩
  have := hc n hn
  simp only [Nat.sub_add_cancel hn] at this
  rw [hκ]
  exact this

end Formalism.InvariantFactorPaths.MC
