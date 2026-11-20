import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

/- English proof (translation)
Introduce `l _ Ω _ _ _ A c Z m c₂ c' ζ ι _ P o h hc`. Take `⟨hζ, hco, hoO, hne, hK⟩` from `h`. Take `⟨hζ₂, -, hu, ho, hs⟩` from `hK`. Establish `hl : l.Prime` using `Fact.out`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`.

Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by`. Establish `: NeZero ((l ^ i : ℕ) : Ω)` using `⟨by exact_mod_cast (pow_pos hl.pos i).ne'⟩`. Use `infer_instance`. Use `set n' := m - c' with hn'`.

Use `set d := (m - c₂) - n' with hd`. Establish `hdn : d + n' = m - c₂` using `by omega`. Establish `hpow : (ζ ^ l ^ c₂) ^ l ^ d = ζ ^ l ^ c'`. Rewrite using `[← pow_mul, ← pow_add]`. Break down `Nat.lt_or_ge m c' with h | h` into its components or cases.

Use `swap`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `e1 : m ≤ c₂ + d` using `by omega`. Rewrite using `[(hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l e1), (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l h.le)]`.

Establish `hζ' : IsPrimitiveRoot (ζ ^ l ^ c') (l ^ n')`. Rewrite using `[← hpow]`. Conclude with `hζ₂.pow (pow_pos hl.pos _) (by rw [← pow_add, hdn])`. Use `⟨hζ, hco, hoO, hne, hζ', by omega, hu, ho, ?_⟩` and prove the remaining obligations. Introduce `s hsI hcyc _`.

Establish `hfix : s (ζ ^ l ^ c₂) = ζ ^ l ^ c₂`. Use `GlobalTheory.Col.fix_of_cycMod (le_refl m) hcyc ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Take `⟨k, hkv, hcg⟩` from `hs s hsI hcyc hfix`. Use `⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨v, hv, hsv⟩` from `hkv i`. Use `⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, hdn, hv], ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.val_natCast, map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, hpow, ← pow_eq_pow_mod _ hζ'.pow_eq_one]`. Establish `hN : ∀ a : ℕ, ‖(a : Qbar l)‖ ≤ 1` using `fun a => IsUltrametricDist.norm_natCast_le_one _ a`. Establish `key : ∀ i, ‖o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖`.

Introduce `i`. Establish `e : (((k i).val : ℕ) : Qbar l) = ((l : ℕ) : Qbar l) ^ n' * (((k i).val / l ^ n' : ℕ) : Qbar l) + (((k i).val % l ^ n' : ℕ) : Qbar l)`. Conclude with `(Nat.div_add_mod (k i).val (l ^ n')).symm` after adjusting the coercions. Establish `e2 : o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l) = ((l : ℕ) : Qbar l) ^ n' * (o i * (((k i).val / l ^ n' : ℕ) : Qbar l))`. Rewrite using `[ZMod.val_natCast]`.

Take the linear combination `(o i) * e`. Rewrite using `[e2, norm_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (ho i) (norm_nonneg _) (hN _))`. Establish `h1 : ‖Z m s 1 - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖`. Use `le_trans hcg ?_` and prove the remaining obligations.

Rewrite using `[norm_pow, norm_pow]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) (hN l) (by omega)`. Establish `h2 : ‖∑ i, (o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => key i)`. Establish `h3` using `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`. Rewrite `h3` using `[Finset.sum_sub_distrib, sub_add_sub_cancel]`.

Conclude with `h3`.
-/
theorem htPresNu7_mono_loss : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
  (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₂ c' : ℕ) (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l),
  HTPresNuOfPolys A c m c₂ Z ζ P o → c₂ ≤ c' → HTPresNuOfPolys A c m c' Z ζ P o := by
  intro l _ Ω _ _ _ A c Z m c₂ c' ζ ι _ P o h hc
  obtain ⟨hζ, hco, hoO, hne, hK⟩ := h
  obtain ⟨hζ₂, -, hu, ho, hs⟩ := hK
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    have : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hl.pos i).ne'⟩
    infer_instance
  set n' := m - c' with hn'
  set d := (m - c₂) - n' with hd
  have hdn : d + n' = m - c₂ := by omega
  have hpow : (ζ ^ l ^ c₂) ^ l ^ d = ζ ^ l ^ c' := by
    rw [← pow_mul, ← pow_add]
    rcases Nat.lt_or_ge m c' with h | h
    swap
    · congr 2; omega
    · have e1 : m ≤ c₂ + d := by omega
      rw [(hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l e1), (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l h.le)]
  have hζ' : IsPrimitiveRoot (ζ ^ l ^ c') (l ^ n') := by
    rw [← hpow]
    exact hζ₂.pow (pow_pos hl.pos _) (by rw [← pow_add, hdn])
  refine ⟨hζ, hco, hoO, hne, hζ', by omega, hu, ho, ?_⟩
  intro s hsI hcyc _
  have hfix : s (ζ ^ l ^ c₂) = ζ ^ l ^ c₂ := by
    refine GlobalTheory.Col.fix_of_cycMod (le_refl m) hcyc ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨k, hkv, hcg⟩ := hs s hsI hcyc hfix
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hkv i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, hdn, hv], ?_⟩
    rw [ZMod.val_natCast, map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, hpow,
      ← pow_eq_pow_mod _ hζ'.pow_eq_one]
  · have hN : ∀ a : ℕ, ‖(a : Qbar l)‖ ≤ 1 := fun a => IsUltrametricDist.norm_natCast_le_one _ a
    have key : ∀ i, ‖o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      intro i
      have e : (((k i).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (((k i).val / l ^ n' : ℕ) : Qbar l) + (((k i).val % l ^ n' : ℕ) : Qbar l) := by
        exact_mod_cast (Nat.div_add_mod (k i).val (l ^ n')).symm
      have e2 : o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (o i * (((k i).val / l ^ n' : ℕ) : Qbar l)) := by
        rw [ZMod.val_natCast]
        linear_combination (o i) * e
      rw [e2, norm_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (ho i) (norm_nonneg _) (hN _))
    have h1 : ‖Z m s 1 - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine le_trans hcg ?_
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hN l) (by omega)
    have h2 : ‖∑ i, (o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => key i)
    have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    rw [Finset.sum_sub_distrib, sub_add_sub_cancel] at h3
    exact h3

end GlobalTheory.KZ
