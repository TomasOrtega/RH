import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.NatCastNeOfCop
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Establish `h` using `smul_rz M (p : ℤ) (b • a)`. Rewrite `h` using `[Int.cast_natCast]`. Rewrite using `[h]`. Apply `rz_congr` to reduce the goal to its premises. Introduce `i`.

Establish `e : a i - ((p : ℤ) • b • a) i = -((b * p - 1) * a i)`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(Dvd.dvd.mul_right hb _).neg_right`.
-/
private theorem rows_p (M p : ℕ) (b : ℤ) (hb : (M : ℤ) ∣ b * p - 1) (a : Fin 2 → ℤ) :
    (p : ZMod M) • rz M (b • a) = rz M a := by
  have h := smul_rz M (p : ℤ) (b • a)
  rw [Int.cast_natCast] at h
  rw [h]
  apply rz_congr
  intro i
  have e : a i - ((p : ℤ) • b • a) i = -((b * p - 1) * a i) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact (Dvd.dvd.mul_right hb _).neg_right

/- English proof (translation)
Rewrite using `[up_rz]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, rz, tp, Pi.smul_apply, smul_eq_mul, hc i]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem up_rz_add_tp_eq_rz_mul_of_eq (M p : ℕ) [NeZero M] (t : Fin 2 → ZMod p) (a c : Fin 2 → ℤ)
    (hc : ∀ i, c i = p * a i + M * ((t i).val : ℤ)) :
    up p M (rz M a) + tp p M t = rz (p * M) c := by
  rw [up_rz]
  funext i
  simp only [Pi.add_apply, rz, tp, Pi.smul_apply, smul_eq_mul, hc i]
  push_cast
  rfl

/- English proof (translation)
Introduce `l N p L _ _ _ x hl2 hlN hp hL`. Establish `hl : l.Prime` using `Fact.out`. Establish `hpp : p.Prime` using `Fact.out`. Establish `hb0` using `bar_mul (l := l) (N := N) (p := p) L hl.ne_zero (NeZero.ne N) hp`. Generalize the expression as in `hM : N * l ^ L = M at hb0 ⊢`.

Establish `hM0 : M ≠ 0` using `hM ▸ Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)`. Use `haveI : NeZero M := ⟨hM0⟩`. Use `haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hpp.ne_zero hM0⟩`. Establish `hlM : l ∣ M` using `hM ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N`. Establish `h1` using `rows_p M p _ hb0 (aU l L N x)`.

Establish `h2` using `rows_p M p _ hb0 (aV l L N)`. Establish `hok` using `ok_UV hl hl2 hlN hL hlM x`. Establish `hokT` using `ok_UVT (M := p * M) hl hl2 hlN hL (dvd_mul_of_dvd_right hlM p) hp x`. Establish `hU : up p M (rz M (bar l L N p • aU l L N x)) + tp p M ![1, 0] = rz (p * M) (aUT l L N p x)`. Apply `up_rz_add_tp_eq_rz_mul_of_eq M p ![1, 0]` to reduce the goal to its premises.

Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [aU, aUT, ZMod.val_one, ← hM] <;> ring`. Establish `hV : up p M (rz M (bar l L N p • aV l L N)) + tp p M ![0, 1] = rz (p * M) (aVT l L N p)`. Apply `up_rz_add_tp_eq_rz_mul_of_eq M p ![0, 1]` to reduce the goal to its premises. Introduce `i`.

Apply the tactic sequence `fin_cases i <;> simp [aV, aVT, ZMod.val_one, ← hM] <;> ring`. Use `⟨rz M (bar l L N p • aU l L N x), rz M (bar l L N p • aV l L N), ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h2, hU, hV]`. Use `⟨⟨?_, ?_⟩, hok, hokT, fun i => ixU_toQ hM.symm x i, fun i => ixV_toQ hM.symm i, fun i => ixUT_toQ (by rw [← hM]; ring) x i, fun i => ixVT_toQ (by rw [← hM]; ring) i⟩` and prove the remaining obligations. Introduce `h`.

Apply `hok.1` to reduce the goal to its premises. Rewrite using `[← h1, smul_comm, h, smul_zero]`. Introduce `h`. Apply `hok.2` to reduce the goal to its premises. Rewrite using `[← h2, smul_comm, h, smul_zero]`.
-/
theorem UpperTheory.exists_rows_hecke_compatible_level_prime_pow :
    ∀ (l N p L : ℕ) [Fact l.Prime] [NeZero N] [Fact p.Prime] (x : ZMod N), l ≠ 2 → Nat.Coprime l N → Nat.Coprime p (l * N) → 1 ≤ L →
        ∃ xb yb : Row (N * l ^ L), Ok xb yb ∧ Ok ((p : ZMod (N * l ^ L)) • xb) ((p : ZMod (N * l ^ L)) • yb) ∧
          Ok (up p (N * l ^ L) xb + tp p (N * l ^ L) ![1, 0]) (up p (N * l ^ L) yb + tp p (N * l ^ L) ![0, 1]) ∧
          (∀ i, ∃ j : ℤ, ixU l L N x i = toQ (N * l ^ L) ((p : ZMod (N * l ^ L)) • xb) i + j) ∧
          (∀ i, ∃ j : ℤ, ixV l L N i = toQ (N * l ^ L) ((p : ZMod (N * l ^ L)) • yb) i + j) ∧
          (∀ i, ∃ j : ℤ, ixUT l L N p x i = toQ (p * (N * l ^ L)) (up p (N * l ^ L) xb + tp p (N * l ^ L) ![1, 0]) i + j) ∧
          (∀ i, ∃ j : ℤ, ixVT l L N p i = toQ (p * (N * l ^ L)) (up p (N * l ^ L) yb + tp p (N * l ^ L) ![0, 1]) i + j) := by
  intro l N p L _ _ _ x hl2 hlN hp hL
  have hl : l.Prime := Fact.out
  have hpp : p.Prime := Fact.out
  have hb0 := bar_mul (l := l) (N := N) (p := p) L hl.ne_zero (NeZero.ne N) hp
  generalize hM : N * l ^ L = M at hb0 ⊢
  have hM0 : M ≠ 0 := hM ▸ Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)
  haveI : NeZero M := ⟨hM0⟩
  haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hpp.ne_zero hM0⟩
  have hlM : l ∣ M := hM ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N
  have h1 := rows_p M p _ hb0 (aU l L N x)
  have h2 := rows_p M p _ hb0 (aV l L N)
  have hok := ok_UV hl hl2 hlN hL hlM x
  have hokT := ok_UVT (M := p * M) hl hl2 hlN hL (dvd_mul_of_dvd_right hlM p) hp x
  have hU : up p M (rz M (bar l L N p • aU l L N x)) + tp p M ![1, 0] = rz (p * M) (aUT l L N p x) := by
    apply up_rz_add_tp_eq_rz_mul_of_eq M p ![1, 0]
    intro i
    fin_cases i <;> simp [aU, aUT, ZMod.val_one, ← hM] <;> ring
  have hV : up p M (rz M (bar l L N p • aV l L N)) + tp p M ![0, 1] = rz (p * M) (aVT l L N p) := by
    apply up_rz_add_tp_eq_rz_mul_of_eq M p ![0, 1]
    intro i
    fin_cases i <;> simp [aV, aVT, ZMod.val_one, ← hM] <;> ring
  refine ⟨rz M (bar l L N p • aU l L N x), rz M (bar l L N p • aV l L N), ?_⟩
  rw [h1, h2, hU, hV]
  refine ⟨⟨?_, ?_⟩, hok, hokT, fun i => ixU_toQ hM.symm x i, fun i => ixV_toQ hM.symm i,
    fun i => ixUT_toQ (by rw [← hM]; ring) x i, fun i => ixVT_toQ (by rw [← hM]; ring) i⟩
  · intro h
    apply hok.1
    rw [← h1, smul_comm, h, smul_zero]
  · intro h
    apply hok.2
    rw [← h2, smul_comm, h, smul_zero]
