import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ColMeas

open GlobalTheory.Col PowerSeries

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp hp2 m A _ f`. Establish `hpp : p.Prime` using `hp.out`. Use `haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hpp.ne_zero⟩`. Establish `hcop : ∀ (c : (ZMod p)ˣ) (l : ℕ), Nat.Coprime ((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l) (p ^ (m + 1))`. Introduce `c l`.

Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Apply `Nat.Coprime.mul` to reduce the goal to its premises. Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_comm, hpp.coprime_iff_not_dvd]`. Introduce `h`.

Establish `h0 : (((c : ZMod p).val : ℕ) : ZMod p) = 0` using `(ZMod.natCast_eq_zero_iff _ _).2 h`. Rewrite `h0` using `[ZMod.natCast_zmod_val]`. Conclude with `c.ne_zero h0`. Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_comm, hpp.coprime_iff_not_dvd]`.

Introduce `h`. Establish `h1 : p ∣ 1` using `(Nat.dvd_add_right (dvd_refl p)).1 (by rwa [add_comm] at h)`. Conclude with `hpp.one_lt.ne' (Nat.dvd_one.1 h1)`. Set `g : (ZMod p)ˣ × Fin (p ^ m) → (ZMod (p ^ (m + 1)))ˣ` to `fun x => ZMod.unitOfCoprime _ (hcop x.1 x.2)`. Establish `hg : ∀ x, (g x : ZMod (p ^ (m + 1))) = (((x.1 : ZMod p).val ^ (p ^ m) * (1 + p) ^ (x.2 : ℕ) : ℕ) : ZMod (p ^ (m + 1)))` using `fun x => rfl`.

Establish `hinj : Function.Injective g`. Introduce and unpack `⟨c, l⟩ ⟨c', l'⟩ h`. Establish `h'` using `congrArg (fun u : (ZMod (p ^ (m + 1)))ˣ => (u : ZMod (p ^ (m + 1)))) h`. Simplify using `only [hg] at h'`. Establish `hc : c = c'`.

Establish `h2` using `congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero m)) (ZMod p)) h'`. Simplify using `only [map_natCast] at h2`. Move the coercions through the operations in `at h2`. Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id, ZMod.natCast_self, add_zero, one_pow, mul_one, ZMod.pow_card_pow] at h2`. Conclude with `Units.ext h2`.

Substitute `hc` using the available equality. Establish `hu : IsUnit ((((c : ZMod p).val ^ (p ^ m) : ℕ) : ZMod (p ^ (m + 1))))` using `(ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) (hcop c 0))`. Establish `h3 : ((1 + p : ZMod (p ^ (m + 1)))) ^ (l : ℕ) = (1 + p) ^ (l' : ℕ)`. Rewrite `h'` using `[Nat.cast_mul, Nat.cast_mul]`. Establish `h4` using `hu.mul_left_cancel h'`.

Move the coercions through the operations in `at h4`. Conclude with `h4`. Establish `hu1 : IsUnit ((1 + p : ℕ) : ZMod (p ^ (m + 1)))`. Use `(ZMod.isUnit_iff_coprime _ _).2 ?_` and prove the remaining obligations. Establish `h5` using `Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) (hcop c 1)`.

Rewrite `h5` using `[pow_one]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `hu1`. Move the coercions through the operations in `at hu`. Establish `h6 : u ^ (l : ℕ) = u ^ (l' : ℕ)` using `Units.ext (by push_cast [hu]; exact h3)`. Rewrite `h6` using `[pow_inj_mod, ← orderOf_units, hu, ZMod.orderOf_one_add_prime hpp hp2, Nat.mod_eq_of_lt l.2, Nat.mod_eq_of_lt l'.2]`.

Conclude with `Prod.ext rfl (Fin.ext h6)`. Establish `hcard : Fintype.card ((ZMod p)ˣ × Fin (p ^ m)) = Fintype.card (ZMod (p ^ (m + 1)))ˣ`. Rewrite using `[Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Fintype.card_fin, Nat.totient_prime_pow_succ hpp, Nat.totient_prime hpp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbij : Function.Bijective g` using `(Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩`.

Rewrite using `[← Fintype.sum_bijective g hbij (fun x => f (g x : ZMod (p ^ (m + 1)))) (fun b => f b) (fun _ => rfl), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Conclude with `Fin.sum_univ_eq_sum_range (fun l => f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1)))) (p ^ m)`.
-/
theorem sum_units_primePow_teichmuller_reindex :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (m : ℕ) (A : Type) [AddCommMonoid A] (f : ZMod (p ^ (m + 1)) → A),
      ∑ b : (ZMod (p ^ (m + 1)))ˣ, f (b : ZMod (p ^ (m + 1))) =
        ∑ c : (ZMod p)ˣ, ∑ l ∈ Finset.range (p ^ m),
          f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1))) := by
  intro p hp hp2 m A _ f
  have hpp : p.Prime := hp.out
  haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hcop : ∀ (c : (ZMod p)ˣ) (l : ℕ),
      Nat.Coprime ((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l) (p ^ (m + 1)) := by
    intro c l
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h0 : (((c : ZMod p).val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [ZMod.natCast_zmod_val] at h0
      exact c.ne_zero h0
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).1 (by rwa [add_comm] at h)
      exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
  let g : (ZMod p)ˣ × Fin (p ^ m) → (ZMod (p ^ (m + 1)))ˣ :=
    fun x => ZMod.unitOfCoprime _ (hcop x.1 x.2)
  have hg : ∀ x, (g x : ZMod (p ^ (m + 1))) =
      (((x.1 : ZMod p).val ^ (p ^ m) * (1 + p) ^ (x.2 : ℕ) : ℕ) : ZMod (p ^ (m + 1))) := fun x => rfl
  have hinj : Function.Injective g := by
    rintro ⟨c, l⟩ ⟨c', l'⟩ h
    have h' := congrArg (fun u : (ZMod (p ^ (m + 1)))ˣ => (u : ZMod (p ^ (m + 1)))) h
    simp only [hg] at h'
    have hc : c = c' := by
      have h2 := congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero m)) (ZMod p)) h'
      simp only [map_natCast] at h2
      push_cast at h2
      simp only [ZMod.natCast_val, ZMod.cast_id', id, ZMod.natCast_self, add_zero, one_pow, mul_one,
        ZMod.pow_card_pow] at h2
      exact Units.ext h2
    subst hc
    have hu : IsUnit ((((c : ZMod p).val ^ (p ^ m) : ℕ) : ZMod (p ^ (m + 1)))) :=
      (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) (hcop c 0))
    have h3 : ((1 + p : ZMod (p ^ (m + 1)))) ^ (l : ℕ) = (1 + p) ^ (l' : ℕ) := by
      rw [Nat.cast_mul, Nat.cast_mul] at h'
      have h4 := hu.mul_left_cancel h'
      push_cast at h4
      exact h4
    have hu1 : IsUnit ((1 + p : ℕ) : ZMod (p ^ (m + 1))) := by
      refine (ZMod.isUnit_iff_coprime _ _).2 ?_
      have h5 := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) (hcop c 1)
      rwa [pow_one] at h5
    obtain ⟨u, hu⟩ := hu1
    push_cast at hu
    have h6 : u ^ (l : ℕ) = u ^ (l' : ℕ) := Units.ext (by push_cast [hu]; exact h3)
    rw [pow_inj_mod, ← orderOf_units, hu, ZMod.orderOf_one_add_prime hpp hp2, Nat.mod_eq_of_lt l.2,
      Nat.mod_eq_of_lt l'.2] at h6
    exact Prod.ext rfl (Fin.ext h6)
  have hcard : Fintype.card ((ZMod p)ˣ × Fin (p ^ m)) = Fintype.card (ZMod (p ^ (m + 1)))ˣ := by
    rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Fintype.card_fin,
      Nat.totient_prime_pow_succ hpp, Nat.totient_prime hpp]
    ring
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩
  rw [← Fintype.sum_bijective g hbij (fun x => f (g x : ZMod (p ^ (m + 1)))) (fun b => f b)
    (fun _ => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Fin.sum_univ_eq_sum_range
    (fun l => f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1)))) (p ^ m)

end GlobalTheory
