import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]`. Establish `r1 : ∀ X : Ideal R, A * X ≤ A` using `fun X => Ideal.mul_le.mpr fun x hx y _ => Ideal.mul_mem_right y _ hx`. Establish `r2 : ∀ X : Ideal R, X * A ≤ A` using `fun X => Ideal.mul_le.mpr fun x _ y hy => Ideal.mul_mem_left _ x hy`. Conclude with `sup_le (sup_le (r1 _) (r1 _)) (sup_le (r2 _) h)`.

Combine the equalities or inequalities in the displayed calculation. Use `sup_le ?_ (Ideal.mul_mono le_sup_left le_sup_right)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `Ideal.mul_mono le_sup_right le_sup_left`.
-/
theorem sup_mul_sup_eq {R : Type*} [CommRing R] (A M N : Ideal R) (hMN : M ⊔ N = ⊤)
    (h : M * N ≤ A) : (A ⊔ M) * (A ⊔ N) = A := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    have r1 : ∀ X : Ideal R, A * X ≤ A := fun X => Ideal.mul_le.mpr fun x hx y _ => Ideal.mul_mem_right y _ hx
    have r2 : ∀ X : Ideal R, X * A ≤ A := fun X => Ideal.mul_le.mpr fun x _ y hy => Ideal.mul_mem_left _ x hy
    exact sup_le (sup_le (r1 _) (r1 _)) (sup_le (r2 _) h)
  · calc A = A * (M ⊔ N) := by rw [hMN, Ideal.mul_top]
      _ = A * M ⊔ A * N := Ideal.mul_sup _ _ _
      _ ≤ (A ⊔ M) * (A ⊔ N) := by
        refine sup_le ?_ (Ideal.mul_mono le_sup_left le_sup_right)
        rw [mul_comm]
        exact Ideal.mul_mono le_sup_right le_sup_left

/- English proof (translation)
Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n : ℤ) = 1`. Rewrite using `[← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]`. Simplify using the standard rewrite rules. Establish `h2 : ((m : S) * (Nat.gcdA m n : S) + (n : S) * (Nat.gcdB m n : S)) = 1`.

Use `congrArg (Int.cast : ℤ → S) h1` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[← h2]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))`.
-/
theorem span_natCast_sup_eq_top {S : Type*} [CommRing S] {m n : ℕ} (h : m.Coprime n) :
    Ideal.span {(m : S)} ⊔ Ideal.span {(n : S)} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    simp
  have h2 : ((m : S) * (Nat.gcdA m n : S) + (n : S) * (Nat.gcdB m n : S)) = 1 := by
    have := congrArg (Int.cast : ℤ → S) h1
    push_cast at this
    exact this
  rw [← h2]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[← hI]`. Conclude with `Ideal.span_singleton_absNorm_le I`.
-/
theorem span_le_of_absNorm {I : Ideal (𝓞 K)} {m : ℕ} (hI : Ideal.absNorm I = m) :
    Ideal.span {(m : 𝓞 K)} ≤ I := by
  rw [← hI]
  exact Ideal.span_singleton_absNorm_le I

/- English proof (translation)
Unfold `cnt`. Rewrite using `[Nat.card_eq_one_iff_exists]`. Conclude with `⟨⟨⊤, Ideal.absNorm_top⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩`.
-/
theorem cnt_one : cnt K 1 = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩

/- English proof (translation)
Establish `hcop : IsCoprime I J'`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← span_natCast_sup_eq_top hmn]`. Conclude with `sup_le_sup (span_le_of_absNorm hI) (span_le_of_absNorm hJ')`. Establish `hd : I ∣ I' * J'` using `⟨J, h.symm⟩`. Conclude with `Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_right hd)`.
-/
theorem le_of_mul_eq {m n : ℕ} (hmn : m.Coprime n) {I J I' J' : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m) (hJ' : Ideal.absNorm J' = n) (h : I * J = I' * J') : I' ≤ I := by
  have hcop : IsCoprime I J' := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← span_natCast_sup_eq_top hmn]
    exact sup_le_sup (span_le_of_absNorm hI) (span_le_of_absNorm hJ')
  have hd : I ∣ I' * J' := ⟨J, h.symm⟩
  exact Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_right hd)

/- English proof (translation)
Establish `hprod : (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A`. Use `sup_mul_sup_eq A _ _ (span_natCast_sup_eq_top hmn) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul]`. Conclude with `span_le_of_absNorm hA`. Establish `hN` using `congrArg Ideal.absNorm hprod`.

Rewrite `hN` using `[map_mul, hA]`. Use `set a := Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)})`. Use `set c := Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)})`. Establish `ha : a ∣ m ^ Module.finrank ℤ (𝓞 K)`. Rewrite using `[← Ideal.absNorm_span_natCast]`.

Conclude with `Ideal.absNorm_dvd_absNorm_of_le le_sup_right`. Establish `hc : c ∣ n ^ Module.finrank ℤ (𝓞 K)`. Rewrite using `[← Ideal.absNorm_span_natCast]`. Conclude with `Ideal.absNorm_dvd_absNorm_of_le le_sup_right`. Establish `ha' : a ∣ m`.

Establish `hcop : a.Coprime n` using `Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.pow_left _ hmn)`. Conclude with `hcop.dvd_of_dvd_mul_right ⟨c, hN.symm⟩`. Establish `hc' : c ∣ n`. Establish `hcop : c.Coprime m` using `Nat.Coprime.coprime_dvd_left hc (Nat.Coprime.pow_left _ hmn.symm)`. Conclude with `hcop.dvd_of_dvd_mul_left ⟨a, by rw [← hN]; ring⟩`.

Establish `ha1 : a ≤ m` using `Nat.le_of_dvd hm ha'`. Establish `hc1 : c ≤ n` using `Nat.le_of_dvd hn hc'`. Establish `hae : a = m`. Assume the negation of the conclusion as `hne`. Establish `hlt : a < m` using `lt_of_le_of_ne ha1 hne`.

Establish `: a * c < m * n`. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers. Establish `hce : c = n`. Rewrite `hN` using `[hae]`.

Conclude with `Nat.eq_of_mul_eq_mul_left hm hN`. Conclude with `⟨hprod, hae, hce⟩`.
-/
theorem sup_parts {m n : ℕ} (hmn : m.Coprime n) (hm : 0 < m) (hn : 0 < n) {A : Ideal (𝓞 K)}
    (hA : Ideal.absNorm A = m * n) :
    (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A ∧
      Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)}) = m ∧
      Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)}) = n := by
  have hprod : (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A := by
    refine sup_mul_sup_eq A _ _ (span_natCast_sup_eq_top hmn) ?_
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul]
    exact span_le_of_absNorm hA
  have hN := congrArg Ideal.absNorm hprod
  rw [map_mul, hA] at hN
  set a := Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)})
  set c := Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)})
  have ha : a ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hc : c ∣ n ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have ha' : a ∣ m := by
    have hcop : a.Coprime n := Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.pow_left _ hmn)
    exact hcop.dvd_of_dvd_mul_right ⟨c, hN.symm⟩
  have hc' : c ∣ n := by
    have hcop : c.Coprime m := Nat.Coprime.coprime_dvd_left hc (Nat.Coprime.pow_left _ hmn.symm)
    exact hcop.dvd_of_dvd_mul_left ⟨a, by rw [← hN]; ring⟩
  have ha1 : a ≤ m := Nat.le_of_dvd hm ha'
  have hc1 : c ≤ n := Nat.le_of_dvd hn hc'
  have hae : a = m := by
    by_contra hne
    have hlt : a < m := lt_of_le_of_ne ha1 hne
    have : a * c < m * n := by
      calc a * c ≤ a * n := Nat.mul_le_mul_left _ hc1
        _ < m * n := Nat.mul_lt_mul_of_pos_right hlt hn
    omega
  have hce : c = n := by
    rw [hae] at hN
    exact Nat.eq_of_mul_eq_mul_left hm hN
  exact ⟨hprod, hae, hce⟩

/- English proof (translation)
Introduce `K _ _ m n hmn`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Rewrite `hmn` using `[Nat.coprime_zero_left]`. Substitute `hmn` using the available equality. Simplify using `[cnt_one]`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite `hmn` using `[Nat.coprime_zero_right]`. Substitute `hmn` using the available equality. Simplify using `[cnt_one]`. Set `Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} → {A : Ideal (𝓞 K) // Ideal.absNorm A = m * n}` to `fun x => ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩`.

Establish `hΦ : Function.Bijective Φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h`. Establish `h' : I * J = I' * J'` using `congrArg Subtype.val h`. Establish `hII : I = I'` using `le_antisymm (le_of_mul_eq hmn hI' hJ h'.symm) (le_of_mul_eq hmn hI hJ' h')`.

Substitute `hII` using the available equality. Establish `hI0 : I ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, ne_eq, ← Ideal.absNorm_eq_zero_iff, hI]`. Use linear arithmetic over natural numbers and integers. Establish `hJJ : J = J'` using `mul_left_cancel₀ hI0 h'`.

Substitute `hJJ` using the available equality. Both sides reduce to the same expression. Introduce and unpack `⟨A, hA⟩`. Take `⟨hprod, hI, hJ⟩` from `sup_parts hmn hm hn hA`. Conclude with `⟨⟨⟨_, hI⟩, ⟨_, hJ⟩⟩, Subtype.ext hprod⟩`.

Unfold `cnt`. Rewrite using `[← Nat.card_prod]`. Conclude with `(Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm`.
-/
theorem cntMul : CntMul := by
  intro K _ _ m n hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    subst hmn
    simp [cnt_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    subst hmn
    simp [cnt_one]
  let Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} →
      {A : Ideal (𝓞 K) // Ideal.absNorm A = m * n} :=
    fun x => ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
      have h' : I * J = I' * J' := congrArg Subtype.val h
      have hII : I = I' :=
        le_antisymm (le_of_mul_eq hmn hI' hJ h'.symm) (le_of_mul_eq hmn hI hJ' h')
      subst hII
      have hI0 : I ≠ 0 := by
        rw [Ideal.zero_eq_bot, ne_eq, ← Ideal.absNorm_eq_zero_iff, hI]
        omega
      have hJJ : J = J' := mul_left_cancel₀ hI0 h'
      subst hJJ
      rfl
    · rintro ⟨A, hA⟩
      obtain ⟨hprod, hI, hJ⟩ := sup_parts hmn hm hn hA
      exact ⟨⟨⟨_, hI⟩, ⟨_, hJ⟩⟩, Subtype.ext hprod⟩
  unfold cnt
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

end PI.ClassNumImQ.ZetaNonvanishing₂
