import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ.DiamU

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Establish `h1 : d = 1` using `(Nat.coprime_zero_right d).1 hd`. Substitute `h1` using the available equality. Conclude with `Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩`. Conclude with `Betti.isDiam_sgD hN.ne' hl hd`.
-/
theorem isDiam_sgD_of_coprime' {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := (Nat.coprime_zero_right d).1 hd
    subst h1
    exact Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩
  · exact Betti.isDiam_sgD hN.ne' hl hd

/- English proof (translation)
Take `⟨h0, hd⟩` from `hσ`. Rewrite `h0` using `[Subgroup.mem_inf]`. Establish `hcN` using `CongruenceSubgroup.Gamma0_mem.1 h0.1`. Establish `hcl` using `CongruenceSubgroup.Gamma0_mem.1 h0.2`. Establish `hdet` using `σ.det_coe`.

Rewrite `hdet` using `[Matrix.det_fin_two]`. Simplify using `only [en] at hd`. Establish `hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hk hcl ⊢`.

Rewrite using `[hcl]`. Take the linear combination `-hk`. Take `⟨q, hq⟩` from `hdiv`. Use `set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0`. Use `set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1`.

Use `set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0`. Use `set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1`. Use `set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef`. Establish `hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)]`. Use extensionality with `i i'`.

Apply the tactic sequence `fin_cases i <;> fin_cases i' <;>`. Apply the tactic sequence `simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq`. Establish `hS : S.det = 1`. Establish `h` using `congrArg Matrix.det hM`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, σ.det_coe]`.

Simplify using `only [Matrix.det_fin_two_of] at h`. Establish `hl' : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.ne'`. Establish `: ((l : ℤ)) * 1 = S.det * (l : ℤ)` using `by linarith`. Conclude with `(mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))`. Use `⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩` and prove the remaining obligations.

Use `CongruenceSubgroup.Gamma0_mem.2 ?_ show ((l * c : ℤ) : ZMod N) = 0` and prove the remaining obligations. Rewrite using `[Int.cast_mul, hcN, mul_zero]`. Use `CongruenceSubgroup.Gamma0_mem.2 ?_ show ((l * c : ℤ) : ZMod l) = 0` and prove the remaining obligations. Rewrite using `[Int.cast_mul, hcl, mul_zero]`. Simplify using `only [en]`.

Simplify using `[hSdef]`. Rewrite using `[hcN]`. Simplify using `using hd`.
-/
theorem upper_mul_eq {N l d : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (hl : 0 < l) (j k : ℕ)
    (hk : (k : ZMod l) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod l) =
      (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod l)) :
    ∃ s : SL(2, ℤ), IsDiam N l d s ∧
      !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (s : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (k : ℤ); 0, (l : ℤ)] := by
  obtain ⟨h0, hd⟩ := hσ
  rw [Subgroup.mem_inf] at h0
  have hcN := CongruenceSubgroup.Gamma0_mem.1 h0.1
  have hcl := CongruenceSubgroup.Gamma0_mem.1 h0.2
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [en] at hd
  have hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk hcl ⊢
    rw [hcl]
    linear_combination -hk
  obtain ⟨q, hq⟩ := hdiv
  set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef
  have hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)] := by
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq
  have hS : S.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, σ.det_coe] at h
    simp only [Matrix.det_fin_two_of] at h
    have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
    have : ((l : ℤ)) * 1 = S.det * (l : ℤ) := by linarith
    exact (mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))
  refine ⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod l) = 0
    rw [Int.cast_mul, hcl, mul_zero]
  · simp only [en]
    simp [hSdef]
    rw [hcN]; simpa using hd

private def res (l : ℕ) (x : ℤ) : ℕ := (x % (l : ℤ)).toNat

/- English proof (translation)
Establish `h1` using `Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)`. Establish `h2` using `Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')`. Unfold `res`. Use linear arithmetic over natural numbers and integers.
-/
private theorem res_lt {l : ℕ} (hl : 0 < l) (x : ℤ) : res l x < l := by
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  unfold res; omega

/- English proof (translation)
Establish `h2` using `Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')`. Rewrite using `[← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]`.
-/
private theorem res_cast {l : ℕ} (hl : 0 < l) (x : ℤ) : ((res l x : ℕ) : ZMod l) = (x : ZMod l) := by
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  rw [← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]

/- English proof (translation)
Rewrite `h` using `[← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)]`. Conclude with `h`.
-/
private theorem res_eq {l : ℕ} (hl : 0 < l) {x : ℤ} {j : ℕ} (hj : j < l) (h : (x : ZMod l) = j) : res l x = j := by
  rw [← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)] at h
  exact h

/- English proof (translation)
Introduce `Ω _ _ ε X N l _ w d hd _ b hb`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `hσ` using `isDiam_sgD_of_coprime' hl.ne' hd`. Establish `hcl` using `CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2`. Establish `hdet` using `(sgD N l d).det_coe`.

Rewrite `hdet` using `[Matrix.det_fin_two]`. Establish `hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det` using `fun g => by rw [g.det_coe]; exact one_pos`. Establish `hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det` using `fun j => by`. Rewrite using `[Matrix.det_fin_two_of]`. Simplify using `using hl`.

Establish `key` using `fun j k => upper_mul_eq hσ hl j k`. Generalize the expression as in `hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key`. Generalize the expression as in `hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key`. Generalize the expression as in `hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key`. Establish `hae : (A : ZMod l) * E = 1`.

Establish `h` using `congrArg (Int.cast : ℤ → ZMod l) hdet`. Move the coercions through the operations in `at h`. Rewrite `h` using `[hcl]`. Take the linear combination `h`. Simplify using `only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]`.

Use `Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A)) (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Use `res_eq hl (Finset.mem_range.1 hj) ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[res_cast hl]`.

Use `push_cast`. Take the linear combination `((j : ZMod l) + (B + j * E) * A) * hae`. Introduce `k hk`. Use `res_eq hl (Finset.mem_range.1 hk) ?_` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[res_cast hl]`. Use `push_cast`. Take the linear combination `((k : ZMod l) + (k * A - B) * E) * hae`. Introduce `j _`. Take `⟨s, hs, hM⟩` from `key j (res l ((B + j * E) * E)) (by`.

Rewrite using `[res_cast hl]`. Use `push_cast`. Take the linear combination `((B : ZMod l) + j * E) * hae)`. Rewrite using `[Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _), X.act_isDiam_eq hb hs]`.
-/
theorem act_sgD_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) =
      X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ ε X N l _ w d hd _ b hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hσ := isDiam_sgD_of_coprime' hl.ne' hd
  have hcl := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2
  have hdet := (sgD N l d).det_coe
  rw [Matrix.det_fin_two] at hdet
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using hl
  have key := fun j k => upper_mul_eq hσ hl j k
  generalize hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key
  generalize hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key
  generalize hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key
  have hae : (A : ZMod l) * E = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  simp only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A))
    (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_
  · intro j hj
    refine res_eq hl (Finset.mem_range.1 hj) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((j : ZMod l) + (B + j * E) * A) * hae
  · intro k hk
    refine res_eq hl (Finset.mem_range.1 hk) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((k : ZMod l) + (k * A - B) * E) * hae
  · intro j _
    obtain ⟨s, hs, hM⟩ := key j (res l ((B + j * E) * E)) (by
      rw [res_cast hl]
      push_cast
      linear_combination ((B : ZMod l) + j * E) * hae)
    rw [Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _),
      X.act_isDiam_eq hb hs]

end GlobalTheory.KZ.DiamU
