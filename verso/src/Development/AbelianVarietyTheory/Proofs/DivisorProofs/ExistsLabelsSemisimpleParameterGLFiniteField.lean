import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hp : 0 < p ^ d - 1` using `Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)`. Use `haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩`. Establish `hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1)` using `L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _`. Establish `h0 : L.gen d ≠ 0` using `hprim.ne_zero hp.ne'`. Establish `hprimC : IsPrimitiveRoot (L.teich (L.gen d)) (p ^ d - 1)`.

Use `⟨by rw [← map_pow, hprim.pow_eq_one, map_one], fun l hl => hprim.dvd_of_pow_eq_one l ?_⟩` and prove the remaining obligations. Conclude with `L.teich_inj _ _ (pow_ne_zero _ h0) one_ne_zero (by rw [map_pow, hl, map_one])`. Set `γ : Tor p d` to `⟨Units.mk0 _ h0, by`. Rewrite using `[mem_rootsOfUnity]`. Conclude with `Units.ext (by simpa using hprim.pow_eq_one)⟩`.

Establish `hγ : γ ^ (p ^ d - 1) = 1` using `Subtype.ext ((mem_rootsOfUnity _ _).1 γ.2)`. Take `⟨k, -, hk⟩` from `hprimC.eq_pow_of_pow_eq_one (ξ := ((θ γ : ℂˣ) : ℂ)) (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hγ, map_one, Units.val_one])`. Use `⟨L.gen d ^ k, by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow], fun u => ?_⟩` and prove the remaining obligations. Establish `hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]`.

Take `⟨n, -, hn⟩` from `hprim.eq_pow_of_pow_eq_one hu`. Establish `hex : ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n` using `⟨n, hn.symm⟩`. Unfold `GlobalTheory.GLq.thetaOf`. Rewrite using `[dif_pos hex]`. Establish `e : u = γ ^ hex.choose` using `Subtype.ext (Units.ext (by simpa [γ] using hex.choose_spec))`.

Rewrite using `[map_pow, hk, ← Units.val_pow_eq_pow_val, ← map_pow, ← e]`.
-/
theorem exists_labelsChar_of_pos (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) :
    ∃ x : Fbar p, LabelsChar L θ x := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h0 : L.gen d ≠ 0 := hprim.ne_zero hp.ne'
  have hprimC : IsPrimitiveRoot (L.teich (L.gen d)) (p ^ d - 1) := by
    refine ⟨by rw [← map_pow, hprim.pow_eq_one, map_one], fun l hl => hprim.dvd_of_pow_eq_one l ?_⟩
    exact L.teich_inj _ _ (pow_ne_zero _ h0) one_ne_zero (by rw [map_pow, hl, map_one])
  let γ : Tor p d := ⟨Units.mk0 _ h0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hprim.pow_eq_one)⟩
  have hγ : γ ^ (p ^ d - 1) = 1 := Subtype.ext ((mem_rootsOfUnity _ _).1 γ.2)
  obtain ⟨k, -, hk⟩ := hprimC.eq_pow_of_pow_eq_one (ξ := ((θ γ : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hγ, map_one, Units.val_one])
  refine ⟨L.gen d ^ k, by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow], fun u => ?_⟩
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  have hex : ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := ⟨n, hn.symm⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos hex]
  have e : u = γ ^ hex.choose := Subtype.ext (Units.ext (by simpa [γ] using hex.choose_spec))
  rw [map_pow, hk, ← Units.val_pow_eq_pow_val, ← map_pow, ← e]

/- English proof (translation)
Establish `hxd : x ^ p ^ d = x`. Establish `h1 : p ^ d = (p ^ d - 1) + 1` using `(Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).symm`. Rewrite using `[h1, pow_succ, hx, one_mul]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d]`. Establish `hfix : (∏ i ∈ Finset.range d, (X - C (x ^ p ^ i) : (Fbar p)[X])).map (frobenius (Fbar p) p) = ∏ i ∈ Finset.range d, (X - C (x ^ p ^ i))`.

Establish `h1` using `Finset.prod_range_succ (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d`. Rewrite `h1` using `[Finset.prod_range_succ', hxd, pow_zero, pow_one]`. Rewrite using `[Polynomial.map_prod, ← mul_right_cancel₀ (X_sub_C_ne_zero x) h1]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.map_sub, map_X, map_C, frobenius_def, pow_succ, pow_mul]`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Establish `h2` using `congrArg (fun q => q.coeff n) hfix`. Simplify using `only [coeff_map, frobenius_def] at h2`. Take `⟨m, hm⟩` from `(mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)`.

Conclude with `⟨(m : ZMod p), by rw [map_intCast, hm]⟩`.
-/
theorem prod_frobenius_orbit_mem_lifts {d : ℕ} {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    (∏ i : Fin d, (X - C (x ^ p ^ (i : ℕ)))) ∈ Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
  have hxd : x ^ p ^ d = x := by
    have h1 : p ^ d = (p ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).symm
    rw [h1, pow_succ, hx, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d]
  have hfix : (∏ i ∈ Finset.range d, (X - C (x ^ p ^ i) : (Fbar p)[X])).map (frobenius (Fbar p) p) =
      ∏ i ∈ Finset.range d, (X - C (x ^ p ^ i)) := by
    have h1 := Finset.prod_range_succ (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d
    rw [Finset.prod_range_succ', hxd, pow_zero, pow_one] at h1
    rw [Polynomial.map_prod, ← mul_right_cancel₀ (X_sub_C_ne_zero x) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, frobenius_def, pow_succ, pow_mul]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  have h2 := congrArg (fun q => q.coeff n) hfix
  simp only [coeff_map, frobenius_def] at h2
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)
  exact ⟨(m : ZMod p), by rw [map_intCast, hm]⟩

/- English proof (translation)
Use `choose x hx using fun c : Cyc s.1 => exists_labelsChar_of_pos L (cycLen_pos s.1 c) (s.2 c)`. Establish `hl : (∏ y : Σ c : Cyc s.1, Fin (cycLen s.1 c), (X - C (rootElt x y))) ∈ Polynomial.lifts (algebraMap (ZMod p) (Fbar p))`. Rewrite using `[Fintype.prod_sigma]`. Use `Subsemiring.prod_mem _ fun c _ => ?_` and prove the remaining obligations. Simplify using `only [rootElt]`.

Conclude with `prod_frobenius_orbit_mem_lifts (d := cycLen s.1 c) (x := x c) (hx c).1`. Take `⟨f, hf, -, hm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C _)`. Use `⟨x, f, hx, fun c => (hx c).1, hm, ?_⟩` and prove the remaining obligations. Unfold `Formalism.CyclotomicNorms.rootsBar`. Rewrite using `[hf, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (rootElt x)), Multiset.map_map]`.

Both sides reduce to the same expression.
-/
theorem exists_labels (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r) :
    ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  choose x hx using fun c : Cyc s.1 => exists_labelsChar_of_pos L (cycLen_pos s.1 c) (s.2 c)
  have hl : (∏ y : Σ c : Cyc s.1, Fin (cycLen s.1 c), (X - C (rootElt x y))) ∈
      Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
    rw [Fintype.prod_sigma]
    refine Subsemiring.prod_mem _ fun c _ => ?_
    simp only [rootElt]
    exact prod_frobenius_orbit_mem_lifts (d := cycLen s.1 c) (x := x c) (hx c).1
  obtain ⟨f, hf, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C _)
  refine ⟨x, f, hx, fun c => (hx c).1, hm, ?_⟩
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [hf, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (rootElt x)), Multiset.map_map]
  rfl

end GlobalTheory.ParamLabel
