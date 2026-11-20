import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.HeckeUNormInv

/- English proof (translation)
Simplify using `[toGQ, h]`.
-/
theorem coe_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

/- English proof (translation)
Simplify using `[ofSL]`.
-/
theorem coe_ofSL (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  simp [ofSL]

/- English proof (translation)
Simplify using `[Matrix.det_fin_two]`. Conclude with `hl`.
-/
theorem det_mj (j l : ℤ) (hl : 0 < l) : 0 < (!![1, j; 0, l] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  simp [Matrix.det_fin_two]; exact hl

/- English proof (translation)
Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `this`. Take `⟨ha, hd, hc⟩` from `(CongruenceSubgroup.Gamma1_mem _ _).1 hγ`.

Establish `hdvd : l ∣ N * l ^ n` using `dvd_mul_of_dvd_right (dvd_pow_self l hn.ne') N`. Establish `ha' : ((γ 0 0 : ℤ) : ZMod l) = 1`. Use `congrArg (ZMod.castHom hdvd (ZMod l)) ha` as an intermediate fact. Rewrite `this` using `[map_intCast, map_one]`. Then use the resulting hypothesis. Establish `hd' : ((γ 1 1 : ℤ) : ZMod l) = 1`.

Use `congrArg (ZMod.castHom hdvd (ZMod l)) hd` as an intermediate fact. Rewrite `this` using `[map_intCast, map_one]`. Then use the resulting hypothesis. Establish `hc' : ((γ 1 0 : ℤ) : ZMod l) = 0`. Use `congrArg (ZMod.castHom hdvd (ZMod l)) hc` as an intermediate fact. Rewrite `this` using `[map_intCast, map_zero]`. Then use the resulting hypothesis.

Establish `hk : ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ) = (γ 0 1 + j) % (l : ℤ)` using `Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))`. Rewrite using `[hk]`. Use `set k : ℤ := (γ 0 1 + j) % (l : ℤ) with hkdef`. Choose the witnesses or unpack the hypotheses as in `⟨b', hb'⟩ : (l : ℤ) ∣ γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0) := by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Use `push_cast`. Rewrite using `[ha', hd', hc', hkdef, ZMod.intCast_mod]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `γ' : SL(2, ℤ)` to `⟨!![γ 0 0 + j * γ 1 0, b'; l * γ 1 0, γ 1 1 - k * γ 1 0], by`.

Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `hdet + γ 1 0 * hb'⟩`. Establish `hbq : ((γ 0 1 : ℚ) + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) = l * b'` using `by exact_mod_cast hb'`. Use `⟨γ', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[CongruenceSubgroup.Gamma1_mem]`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp [γ'] <;> push_cast <;> simp [ha, hd, hc]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Units.val_mul]`. Rewrite using `[coe_toGQ _ (det_mj _ _ (by omega)), coe_toGQ _ (det_mj _ _ (by omega)), coe_ofSL, coe_ofSL]`.

Use extensionality with `i i'`. Apply the tactic sequence `fin_cases i <;> fin_cases i' <;> simp [Matrix.mul_apply, γ'] <;> push_cast <;> first | linear_combination | linear_combination hbq`.
-/
theorem key (N l n : ℕ) (hn : 0 < n) (hl : 0 < l) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n))
    (j : ℕ) : ∃ γ' ∈ CongruenceSubgroup.Gamma1 (N * l ^ n),
      toGQ !![1, (j : ℤ); 0, (l : ℤ)] * ofSL γ =
        ofSL γ' * toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)] := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨ha, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 hγ
  have hdvd : l ∣ N * l ^ n := dvd_mul_of_dvd_right (dvd_pow_self l hn.ne') N
  have ha' : ((γ 0 0 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) ha; rwa [map_intCast, map_one] at this
  have hd' : ((γ 1 1 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hd; rwa [map_intCast, map_one] at this
  have hc' : ((γ 1 0 : ℤ) : ZMod l) = 0 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hc; rwa [map_intCast, map_zero] at this
  have hk : ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ) = (γ 0 1 + j) % (l : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [hk]
  set k : ℤ := (γ 0 1 + j) % (l : ℤ) with hkdef
  obtain ⟨b', hb'⟩ : (l : ℤ) ∣ γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha', hd', hc', hkdef, ZMod.intCast_mod]
    push_cast; ring
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0 + j * γ 1 0, b'; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + γ 1 0 * hb'⟩
  have hbq : ((γ 0 1 : ℚ) + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) = l * b' := by exact_mod_cast hb'
  refine ⟨γ', ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [γ'] <;> push_cast <;> simp [ha, hd, hc]
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [coe_toGQ _ (det_mj _ _ (by omega)), coe_toGQ _ (det_mj _ _ (by omega)), coe_ofSL, coe_ofSL]
    ext i i'
    fin_cases i <;> fin_cases i' <;> simp [Matrix.mul_apply, γ'] <;> push_cast <;> first | linear_combination | linear_combination hbq

/- English proof (translation)
Establish `h1` using `Int.emod_nonneg x (show (l : ℤ) ≠ 0 by omega)`. Establish `h2` using `Int.emod_lt_of_pos x (show (0 : ℤ) < l by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem emod_toNat_lt (x : ℤ) {l : ℕ} (hl : 0 < l) : (x % (l : ℤ)).toNat < l := by
  have h1 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by omega)
  omega

/- English proof (translation)
Rewrite using `[Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.sub_emod, Int.emod_emod, ← Int.sub_emod, add_sub_cancel_left, Int.emod_eq_of_lt (by omega) (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem emod_inv (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((((((b + a) % (l : ℤ)).toNat : ℕ) : ℤ) - b) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.sub_emod, Int.emod_emod, ← Int.sub_emod,
    add_sub_cancel_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

/- English proof (translation)
Rewrite using `[Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.add_emod, Int.emod_emod, ← Int.add_emod, add_sub_cancel, Int.emod_eq_of_lt (by omega) (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem emod_inv' (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((b + ((((a : ℤ) - b) % (l : ℤ)).toNat : ℤ)) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.add_emod, Int.emod_emod, ← Int.add_emod,
    add_sub_cancel, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

end GlobalTheory.HeckeUNormInv

open GlobalTheory.HeckeUNormInv in

/- English proof (translation)
Introduce `Ω _ _ ε X N l _ n hn g hg γ hγ`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Rewrite using `[map_prod]`. Establish `step : ∀ j : ℕ, X.sl (ofSL γ) (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) = X.sl (toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)]) g`. Introduce `j`.

Take `⟨γ', hγ', heq⟩` from `key N l n hn hl γ hγ j`. Rewrite using `[← X.sl_mul, heq, X.sl_mul, hg γ' hγ']`. Rewrite using `[Finset.prod_congr rfl (fun j _ => step j)]`. Conclude with `Finset.prod_nbij' (fun j => ((γ 0 1 + j) % (l : ℤ)).toNat) (fun k => (((k : ℤ) - γ 0 1) % (l : ℤ)).toNat) (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl)) (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl)) (fun a ha => emod_inv _ hl a (Finset.mem_range.1 ha)) (fun a ha => e …`.
-/
theorem GlobalTheory.normInv_gamma1 : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  intro Ω _ _ ε X N l _ n hn g hg γ hγ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  rw [map_prod]
  have step : ∀ j : ℕ, X.sl (ofSL γ) (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) =
      X.sl (toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)]) g := by
    intro j
    obtain ⟨γ', hγ', heq⟩ := key N l n hn hl γ hγ j
    rw [← X.sl_mul, heq, X.sl_mul, hg γ' hγ']
  rw [Finset.prod_congr rfl (fun j _ => step j)]
  exact Finset.prod_nbij' (fun j => ((γ 0 1 + j) % (l : ℤ)).toNat) (fun k => (((k : ℤ) - γ 0 1) % (l : ℤ)).toNat)
    (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl)) (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl))
    (fun a ha => emod_inv _ hl a (Finset.mem_range.1 ha)) (fun a ha => emod_inv' _ hl a (Finset.mem_range.1 ha))
    (fun _ _ => rfl)
