import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdPrimesDvd

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq f y s hp hn hd`.
-/
private theorem finset_prod_dvd_of_prime_of_dvd_imp_eq {M ι : Type} [CommRing M] (f : ι → M) (y : M) (s : Finset ι)
    (hp : ∀ a ∈ s, Prime (f a)) (hn : ∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) (hd : ∀ a ∈ s, f a ∣ y) :
    ∏ a ∈ s, f a ∣ y :=
  _root_.UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq f y s hp hn hd

private def sb {n : ℕ} (i j : Fin n) : Fin n → Fin n := fun k => if k = j then i else k

/- English proof (translation)
Proceed by induction on `y using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq`. Use `dvd_add hp hq` as an intermediate fact. Rewrite using `[map_add]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p k hp`. Establish `hk : (X j - X i : MvPolynomial (Fin n) R) ∣ X k - X (sb i j k)`. Unfold `sb`.

Use `split_ifs with h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Use `dvd_add (hp.mul_right (X k)) (hk.mul_left (rename (sb i j) p))` as an intermediate fact. Rewrite using `[map_mul, rename_X]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dvd_sub_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y - rename (sb i j) y := by
  induction y using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    rw [map_add]
    convert this using 1
    ring
  | mul_X p k hp =>
    have hk : (X j - X i : MvPolynomial (Fin n) R) ∣ X k - X (sb i j k) := by
      unfold sb
      split_ifs with h
      · rw [h]
      · simp
    have := dvd_add (hp.mul_right (X k)) (hk.mul_left (rename (sb i j) p))
    rw [map_mul, rename_X]
    convert this using 1
    ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Establish `: sb i j j = sb i j i` using `by simp [sb]`. Rewrite using `[map_mul, map_sub, rename_X, rename_X, this, sub_self, zero_mul]`. Introduce `h`.

Use `dvd_sub_sb i j y` as an intermediate fact. Rewrite `this` using `[h, sub_zero]`. Then use the resulting hypothesis.
-/
private theorem dvd_iff_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y ↔ rename (sb i j) y = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    have : sb i j j = sb i j i := by simp [sb]
    rw [map_mul, map_sub, rename_X, rename_X, this, sub_self, zero_mul]
  · intro h
    have := dvd_sub_sb i j y
    rwa [h, sub_zero] at this

/- English proof (translation)
Use `⟨fun e => h.symm (X_injective (sub_eq_zero.1 e)), fun hu => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Use `(dvd_iff_sb i j (1 : MvPolynomial (Fin n) R)).1 hu.dvd` as an intermediate fact. Simplify using `at this`. Rewrite `hab` using `[dvd_iff_sb, map_mul, mul_eq_zero]`. Rewrite using `[dvd_iff_sb, dvd_iff_sb]` and apply the resulting hypothesis.
-/
private theorem prime_sb {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Prime (X j - X i : MvPolynomial (Fin n) R) := by
  refine ⟨fun e => h.symm (X_injective (sub_eq_zero.1 e)), fun hu => ?_, fun a b hab => ?_⟩
  · have := (dvd_iff_sb i j (1 : MvPolynomial (Fin n) R)).1 hu.dvd
    simp at this
  · rw [dvd_iff_sb, map_mul, mul_eq_zero] at hab
    rwa [dvd_iff_sb, dvd_iff_sb]

/- English proof (translation)
Establish `hs : ∀ k, sb i j (swap i j k) = sb i j k`. Introduce `k`. Distinguish the cases in `h1 : k = i`. Substitute `h1` using the available equality. Simplify using `[sb]`.

Distinguish the cases in `h2 : k = j`. Substitute `h2` using the available equality. Simplify using `[sb]`. Rewrite using `[swap_apply_of_ne_of_ne h1 h2]`. Rewrite using `[alt, map_sum]`.

Use `Finset.sum_involution (fun w _ => swap i j * w) (fun w _ => ?_) (fun w _ _ e => ?_) (fun w _ => Finset.mem_univ _) (fun w _ => ?_)` and prove the remaining obligations. Establish `e : sb i j ∘ (swap i j * w : Perm (Fin n)) = sb i j ∘ w` using `funext fun k => hs _`. Rewrite using `[Units.smul_def, Units.smul_def, map_zsmul, map_zsmul, rename_rename, rename_rename, e, Perm.sign_mul, Perm.sign_swap h]`. Simplify using the standard rewrite rules. Use `mul_eq_right.1 e` as an intermediate fact.

Conclude with `h (swap_eq_one_iff.1 this)`. Simplify using `[← mul_assoc]`.
-/
private theorem alt_sb {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (x : MvPolynomial (Fin n) R) :
    rename (sb i j) (alt x) = 0 := by
  have hs : ∀ k, sb i j (swap i j k) = sb i j k := by
    intro k
    by_cases h1 : k = i
    · subst h1; simp [sb]
    · by_cases h2 : k = j
      · subst h2; simp [sb]
      · rw [swap_apply_of_ne_of_ne h1 h2]
  rw [alt, map_sum]
  refine Finset.sum_involution (fun w _ => swap i j * w) (fun w _ => ?_) (fun w _ _ e => ?_)
    (fun w _ => Finset.mem_univ _) (fun w _ => ?_)
  · have e : sb i j ∘ (swap i j * w : Perm (Fin n)) = sb i j ∘ w := funext fun k => hs _
    rw [Units.smul_def, Units.smul_def, map_zsmul, map_zsmul, rename_rename, rename_rename, e, Perm.sign_mul,
      Perm.sign_swap h]
    simp
  · have := mul_eq_right.1 e
    exact h (swap_eq_one_iff.1 this)
  · simp [← mul_assoc]

/- English proof (translation)
Introduce `R _ _ n x`. Establish `hlt : ∀ p ∈ pairs n, p.1 < p.2` using `fun p hp => by simpa [pairs] using hp`. Establish `hd : De R n ∣ alt x`. Use `finset_prod_dvd_of_prime_of_dvd_imp_eq _ _ _ (fun p hp => prime_sb (hlt p hp).ne) (fun p hp q hq hpq => ?_) (fun p hp => (dvd_iff_sb _ _ _).2 (alt_sb (hlt p hp).ne x))` and prove the remaining obligations. Rewrite `hpq` using `[dvd_iff_sb, map_sub, rename_X, rename_X, sub_eq_zero]`.

Establish `e` using `X_injective hpq`. Establish `h1` using `hlt p hp`. Establish `h2` using `hlt q hq`. Unfold `sb at e`. Use `split_ifs at e with a b b`.

Conclude with `absurd (b.trans a.symm) h2.ne`. Conclude with `Prod.ext e a.symm`. Rewrite `h2` using `[e, b]`. Conclude with `absurd h1 h2.not_gt`. Conclude with `absurd e h2.ne'`.

Take `⟨y, hy⟩` from `hd`. Establish `h : ∃ y, De R n * y = alt x` using `⟨y, hy.symm⟩`. Rewrite using `[dd, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem UpperTheory.V.AlgebraTools.hkDdSpec :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (x : MvPolynomial (Fin n) R), De R n * dd x = alt x := by
  intro R _ _ n x
  have hlt : ∀ p ∈ pairs n, p.1 < p.2 := fun p hp => by simpa [pairs] using hp
  have hd : De R n ∣ alt x := by
    refine finset_prod_dvd_of_prime_of_dvd_imp_eq _ _ _ (fun p hp => prime_sb (hlt p hp).ne) (fun p hp q hq hpq => ?_)
      (fun p hp => (dvd_iff_sb _ _ _).2 (alt_sb (hlt p hp).ne x))
    rw [dvd_iff_sb, map_sub, rename_X, rename_X, sub_eq_zero] at hpq
    have e := X_injective hpq
    have h1 := hlt p hp
    have h2 := hlt q hq
    unfold sb at e
    split_ifs at e with a b b
    · exact absurd (b.trans a.symm) h2.ne
    · exact Prod.ext e a.symm
    · rw [e, b] at h2
      exact absurd h1 h2.not_gt
    · exact absurd e h2.ne'
  obtain ⟨y, hy⟩ := hd
  have h : ∃ y, De R n * y = alt x := ⟨y, hy.symm⟩
  rw [dd, dif_pos h]
  exact h.choose_spec
