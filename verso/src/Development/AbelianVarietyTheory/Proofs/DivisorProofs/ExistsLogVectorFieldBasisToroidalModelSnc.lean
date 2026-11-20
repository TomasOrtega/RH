import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequenceExtendCoords

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogBasis

section Algebra

/- English proof (translation)
Set `b : ℕ → R` to `fun n => d^[n] a`. Establish `hb : ∀ n, b (n + 1) = d (b n)` using `fun n => Function.iterate_succ_apply' _ _ _`. Establish `h1 : ∀ n : ℕ, t * b (n + 1) + ((n : R) + 1) * b n ∈ I`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Use `hI _ ha` as an intermediate fact. Rewrite `this` using `[d.leibniz, ht]`. Simplify `this` using `[hb, b]`. Consider the case `succ n ih`.

Use `hI _ ih` as an intermediate fact. Establish `hn : d ((n : R) + 1) = 0` using `by simp`. Rewrite `this` using `[map_add, d.leibniz, d.leibniz, ht, hn, ← hb, ← hb]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1' : ∀ n : ℕ, ∃ u : R, b n - u * t * b (n + 1) ∈ I`. Introduce `n`. Take `⟨v, hv⟩` from `(hQ n).exists_left_inv`.

Use `⟨-v, ?_⟩` and prove the remaining obligations. Use `I.mul_mem_left v (h1 n) using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-b n) * hv`. Establish `h2 : ∀ n : ℕ, t ^ (n + 1) * b n ∈ I`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simpa [b] using ha`. Consider the case `succ n ih`. Use `I.sub_mem (I.mul_mem_left (t ^ (n + 1)) (h1 n)) (I.mul_mem_left ((n : R) + 1) ih) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : ∀ n : ℕ, b n ∈ I → a ∈ I`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact id`. Consider the case `succ n ih`.

Introduce `h`. Take `⟨u, hu⟩` from `h1' n`. Conclude with `ih (by simpa using I.add_mem hu (I.mul_mem_left (u * t) h))`. Set `J : ℕ →o Ideal R` to `⟨fun n => I ⊔ Ideal.span {b n}, monotone_nat_of_le_succ fun n => by`. Use `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)` and prove the remaining obligations.

Take `⟨u, hu⟩` from `h1' n`. Use `Ideal.add_mem (I ⊔ Ideal.span {b (n + 1)}) (Ideal.mem_sup_left hu) (Ideal.mem_sup_right (Ideal.mul_mem_left _ (u * t) (Ideal.mem_span_singleton_self _)))` as an intermediate fact. Simplify using `using this⟩`. Take `⟨N, hN⟩` from `monotone_stabilizes_iff_noetherian.2 inferInstance J`. Establish `h4 : b (N + 1) ∈ I ⊔ Ideal.span {b N}`.

Establish `: J N = J (N + 1)` using `hN (N + 1) (Nat.le_succ N)`. Conclude with `this.ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Take `⟨i, hi, y, hy, hiy⟩` from `Submodule.mem_sup.1 h4`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Take `⟨u, hu⟩` from `h1' N`.

Establish `h5 : b N - (u * c * t) * b N ∈ I`. Use `I.add_mem hu (I.mul_mem_left (u * t) hi) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← hiy]`. Expand and normalize the polynomial expressions, which then agree. Establish `h6 : ∀ k : ℕ, b N - (u * c * t) ^ k * b N ∈ I`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Use `I.add_mem ih (I.mul_mem_left ((u * c * t) ^ k) h5) using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `h3 N ?_` and prove the remaining obligations. Use `I.add_mem (h6 (N + 1)) (I.mul_mem_left ((u * c) ^ (N + 1)) (h2 N)) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_of_mul_mem {R : Type} [CommRing R] [IsNoetherianRing R] (hQ : ∀ n : ℕ, IsUnit ((n : R) + 1))
    (d : Derivation ℤ R R) (I : Ideal R) (hI : ∀ r ∈ I, d r ∈ I) {t a : R} (ht : d t = 1) (ha : t * a ∈ I) :
    a ∈ I := by
  let b : ℕ → R := fun n => d^[n] a
  have hb : ∀ n, b (n + 1) = d (b n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n : ℕ, t * b (n + 1) + ((n : R) + 1) * b n ∈ I := by
    intro n
    induction n with
    | zero =>
      have := hI _ ha
      rw [d.leibniz, ht] at this
      simpa [hb, b] using this
    | succ n ih =>
      have := hI _ ih
      have hn : d ((n : R) + 1) = 0 := by simp
      rw [map_add, d.leibniz, d.leibniz, ht, hn, ← hb, ← hb] at this
      convert this using 1
      simp only [smul_eq_mul]
      push_cast
      ring
  have h1' : ∀ n : ℕ, ∃ u : R, b n - u * t * b (n + 1) ∈ I := by
    intro n
    obtain ⟨v, hv⟩ := (hQ n).exists_left_inv
    refine ⟨-v, ?_⟩
    convert I.mul_mem_left v (h1 n) using 1
    linear_combination (-b n) * hv
  have h2 : ∀ n : ℕ, t ^ (n + 1) * b n ∈ I := by
    intro n
    induction n with
    | zero => simpa [b] using ha
    | succ n ih =>
      convert I.sub_mem (I.mul_mem_left (t ^ (n + 1)) (h1 n)) (I.mul_mem_left ((n : R) + 1) ih) using 1
      ring
  have h3 : ∀ n : ℕ, b n ∈ I → a ∈ I := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
      intro h
      obtain ⟨u, hu⟩ := h1' n
      exact ih (by simpa using I.add_mem hu (I.mul_mem_left (u * t) h))
  let J : ℕ →o Ideal R := ⟨fun n => I ⊔ Ideal.span {b n}, monotone_nat_of_le_succ fun n => by
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    obtain ⟨u, hu⟩ := h1' n
    have := Ideal.add_mem (I ⊔ Ideal.span {b (n + 1)}) (Ideal.mem_sup_left hu)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ (u * t) (Ideal.mem_span_singleton_self _)))
    simpa using this⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance J
  have h4 : b (N + 1) ∈ I ⊔ Ideal.span {b N} := by
    have : J N = J (N + 1) := hN (N + 1) (Nat.le_succ N)
    exact this.ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 h4
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨u, hu⟩ := h1' N
  have h5 : b N - (u * c * t) * b N ∈ I := by
    convert I.add_mem hu (I.mul_mem_left (u * t) hi) using 1
    rw [← hiy]; ring
  have h6 : ∀ k : ℕ, b N - (u * c * t) ^ k * b N ∈ I := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      convert I.add_mem ih (I.mul_mem_left ((u * c * t) ^ k) h5) using 1
      ring
  refine h3 N ?_
  convert I.add_mem (h6 (N + 1)) (I.mul_mem_left ((u * c) ^ (N + 1)) (h2 N)) using 1
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, d.leibniz, smul_eq_mul, smul_eq_mul]`. Use `dvd_add (mul_dvd_mul_left _ (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_` and prove the remaining obligations.

Rewrite using `[mul_comm (t j)]`. Conclude with `mul_dvd_mul_left _ (h j (Finset.mem_insert_self _ _))`.
-/
theorem prod_mem_span {R ι : Type} [CommRing R] (d : Derivation ℤ R R) (t : ι → R) (s : Finset ι)
    (h : ∀ i ∈ s, t i ∣ d (t i)) : ∏ i ∈ s, t i ∣ d (∏ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, d.leibniz, smul_eq_mul, smul_eq_mul]
    refine dvd_add (mul_dvd_mul_left _ (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_
    rw [mul_comm (t j)]
    exact mul_dvd_mul_left _ (h j (Finset.mem_insert_self _ _))

/- English proof (translation)
Introduce `r hr`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite using `[Ideal.mem_span_singleton, d.leibniz, smul_eq_mul, smul_eq_mul]`. Conclude with `dvd_add (Dvd.dvd.mul_left h c) (dvd_mul_right _ _)`.
-/
theorem mem_span_of_dvd {R : Type} [CommRing R] (d : Derivation ℤ R R) {p : R} (h : p ∣ d p) :
    ∀ r ∈ Ideal.span {p}, d r ∈ Ideal.span {p} := by
  intro r hr
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [Ideal.mem_span_singleton, d.leibniz, smul_eq_mul, smul_eq_mul]
  exact dvd_add (Dvd.dvd.mul_left h c) (dvd_mul_right _ _)

/- English proof (translation)
Set `u : Fin n → R` to `fun k => if k ∈ Set.range e then z k else 1`. Establish `hu : ∀ i k, (u k • d k) (z (e i)) = if k = e i then z (e i) else 0`. Introduce `i k`. Rewrite using `[Derivation.smul_apply, hd]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using `[u]`. Simplify using the standard rewrite rules. Establish `hv : ∀ k, u k • d k ∈ M`. Introduce `k`.

Use `(hM _).2 ⟨fun a => by simp [h0], mem_span_of_dvd _ (prod_mem_span _ _ _ fun i _ => ?_)⟩` and prove the remaining obligations. Rewrite using `[hu]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hsum : ∀ (g : Fin n → R) (l : Fin n), (∑ k, g k • d k) (z l) = g l`. Introduce `g l`.

Use `map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := R) (M := R)) (fun k => g k • d k) Finset.univ` as an intermediate fact. Establish `h3` using `congrFun this (z l)`. Rewrite `h3` using `[Finset.sum_apply]`. Use `h3.trans ?_` and prove the remaining obligations. Simplify using `[hd]`.

Set `v : Fin n → M` to `fun k => ⟨u k • d k, hv k⟩`. Establish `hli : LinearIndependent R v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg l`. Establish `h1 : ∑ k, (g k * u k) • d k = 0`.

Use `congrArg Subtype.val hg` as an intermediate fact. Simplify `this` using `[v, mul_smul]`. Establish `h2 : g l * u l = 0`. Rewrite using `[← hsum (fun k => g k * u k) l, h1]`. Both sides reduce to the same expression.

Distinguish the cases in `hl : l ∈ Set.range e`. Simplify using `only [u, if_pos hl] at h2`. Conclude with `mem_of_mul_mem hQ (d l) ⊥ (fun r hr => by rw [Ideal.mem_bot.1 hr, map_zero]; exact zero_mem _) (t := z l) (by simp [hd]) (by rw [mul_comm, h2]; exact zero_mem _)`. Simplify `h2` using `only [u, if_neg hl, mul_one]`. Establish `hsp : ⊤ ≤ Submodule.span R (Set.range v)`.

Introduce and unpack `⟨D, hD⟩ -`. Take `⟨hD0, hD1⟩` from `(hM D).1 hD`. Establish `hdiv : ∀ k, u k ∣ D (z k)`. Introduce `k`. Distinguish the cases in `hk : k ∈ Set.range e`.

Simplify using `only [u, if_pos hk]`. Take `⟨j, rfl⟩` from `hk`. Establish `h1` using `Ideal.mem_span_singleton.1 (hD1 _ (Ideal.mem_span_singleton_self _))`. Rewrite `h1` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ j), D.leibniz, smul_eq_mul, smul_eq_mul]`. Establish `h2 : z (e j) ∣ (∏ i ∈ Finset.univ.erase j, z (e i)) * D (z (e j))` using `(dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans h1)`.

Establish `h3 : ∀ s : Finset (Fin m), j ∉ s → ∀ a, z (e j) ∣ (∏ i ∈ s, z (e i)) * a → z (e j) ∣ a`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`.

Introduce `hj a ha`. Rewrite `ha` using `[Finset.prod_insert hi, mul_assoc]`. Use `ih (fun h => hj (Finset.mem_insert_of_mem h)) a ?_` and prove the remaining obligations. Establish `hij : e i ≠ e j` using `fun h => hj (he h ▸ Finset.mem_insert_self _ _)`. Conclude with `Ideal.mem_span_singleton.1 (mem_of_mul_mem hQ (d (e i)) _ (mem_span_of_dvd _ (by simp [hd, hij])) (by simp [hd]) (Ideal.mem_span_singleton.2 ha))`.

Conclude with `h3 _ (Finset.notMem_erase _ _) _ h2`. Simplify using `only [u, if_neg hk, one_dvd]`. Use `choose g hg using hdiv`. Use `(Submodule.mem_span_range_iff_exists_fun R).2 ⟨g, Subtype.ext ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [show (⟨D, hD⟩ : M).1 = D from rfl, hspan D hD0]`.

Simplify using `[v, hg, smul_smul, mul_comm]`. Use `⟨Module.Basis.mk hli hsp, fun i k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.mk_apply]`. Conclude with `hu i k`.
-/
theorem exists_basis_of_dual {K R : Type} [CommRing R] [IsNoetherianRing R] (hQ : ∀ n : ℕ, IsUnit ((n : R) + 1))
    (φ : K → R) {n m : ℕ} (z : Fin n → R) (d : Fin n → Derivation ℤ R R)
    (hd : ∀ k l, d k (z l) = if k = l then 1 else 0) (h0 : ∀ k a, d k (φ a) = 0)
    (hspan : ∀ D : Derivation ℤ R R, (∀ a, D (φ a) = 0) → D = ∑ k, D (z k) • d k)
    (e : Fin m → Fin n) (he : Function.Injective e) (M : Submodule R (Derivation ℤ R R))
    (hM : ∀ D, D ∈ M ↔ (∀ a, D (φ a) = 0) ∧ ∀ f ∈ Ideal.span {∏ i, z (e i)}, D f ∈ Ideal.span {∏ i, z (e i)}) :
    ∃ b : Module.Basis (Fin n) R M, ∀ i k, (b k).1 (z (e i)) = if k = e i then z (e i) else 0 := by
  classical
  let u : Fin n → R := fun k => if k ∈ Set.range e then z k else 1
  have hu : ∀ i k, (u k • d k) (z (e i)) = if k = e i then z (e i) else 0 := by
    intro i k
    rw [Derivation.smul_apply, hd]
    split_ifs with h
    · subst h
      simp [u]
    · simp
  have hv : ∀ k, u k • d k ∈ M := by
    intro k
    refine (hM _).2 ⟨fun a => by simp [h0], mem_span_of_dvd _ (prod_mem_span _ _ _ fun i _ => ?_)⟩
    rw [hu]
    split_ifs <;> simp
  have hsum : ∀ (g : Fin n → R) (l : Fin n), (∑ k, g k • d k) (z l) = g l := by
    intro g l
    have := map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := R) (M := R)) (fun k => g k • d k) Finset.univ
    have h3 := congrFun this (z l)
    rw [Finset.sum_apply] at h3
    refine h3.trans ?_
    simp [hd]
  let v : Fin n → M := fun k => ⟨u k • d k, hv k⟩
  have hli : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 : ∑ k, (g k * u k) • d k = 0 := by
      have := congrArg Subtype.val hg
      simpa [v, mul_smul] using this
    have h2 : g l * u l = 0 := by
      rw [← hsum (fun k => g k * u k) l, h1]; rfl
    by_cases hl : l ∈ Set.range e
    · simp only [u, if_pos hl] at h2
      exact mem_of_mul_mem hQ (d l) ⊥ (fun r hr => by rw [Ideal.mem_bot.1 hr, map_zero]; exact zero_mem _)
        (t := z l) (by simp [hd]) (by rw [mul_comm, h2]; exact zero_mem _)
    · simpa only [u, if_neg hl, mul_one] using h2
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    rintro ⟨D, hD⟩ -
    obtain ⟨hD0, hD1⟩ := (hM D).1 hD
    have hdiv : ∀ k, u k ∣ D (z k) := by
      intro k
      by_cases hk : k ∈ Set.range e
      · simp only [u, if_pos hk]
        obtain ⟨j, rfl⟩ := hk
        have h1 := Ideal.mem_span_singleton.1 (hD1 _ (Ideal.mem_span_singleton_self _))
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), D.leibniz, smul_eq_mul, smul_eq_mul] at h1
        have h2 : z (e j) ∣ (∏ i ∈ Finset.univ.erase j, z (e i)) * D (z (e j)) :=
          (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans h1)
        have h3 : ∀ s : Finset (Fin m), j ∉ s → ∀ a, z (e j) ∣ (∏ i ∈ s, z (e i)) * a → z (e j) ∣ a := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert i s hi ih =>
            intro hj a ha
            rw [Finset.prod_insert hi, mul_assoc] at ha
            refine ih (fun h => hj (Finset.mem_insert_of_mem h)) a ?_
            have hij : e i ≠ e j := fun h => hj (he h ▸ Finset.mem_insert_self _ _)
            exact Ideal.mem_span_singleton.1 (mem_of_mul_mem hQ (d (e i)) _
              (mem_span_of_dvd _ (by simp [hd, hij])) (by simp [hd]) (Ideal.mem_span_singleton.2 ha))
        exact h3 _ (Finset.notMem_erase _ _) _ h2
      · simp only [u, if_neg hk, one_dvd]
    choose g hg using hdiv
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨g, Subtype.ext ?_⟩
    conv_rhs => rw [show (⟨D, hD⟩ : M).1 = D from rfl, hspan D hD0]
    simp [v, hg, smul_smul, mul_comm]
  refine ⟨Module.Basis.mk hli hsp, fun i k => ?_⟩
  rw [Module.Basis.mk_apply]
  exact hu i k

/- English proof (translation)
Establish `hQ : ∀ n : ℕ, IsUnit ((n : R) + 1)` using `fun n => by`. Use `(IsUnit.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n)).map (algebraMap K R)` as an intermediate fact. Simplify using `using this`. Set `d : Fin n → Derivation ℤ R R` to `fun k => (KaehlerDifferential.linearMapEquivDerivation K R (bΩ.coord k)).restrictScalars ℤ`. Establish `hd' : ∀ k r, d k r = bΩ.repr (KaehlerDifferential.D K R r) k` using `fun k r => rfl`.

Take `⟨b, hb'⟩` from `exists_basis_of_dual hQ (algebraMap K R) z d (fun k l => by rw [hd', ← hb]; simp [Finsupp.single_apply, eq_comm]) (fun k a => by rw [hd']; simp) (fun D hD => by`. Set `D' : Derivation K R R` to `Derivation.mk' { toFun := D map_add' := map_add D map_smul' := fun a r => by`. Simplify using `only [Algebra.smul_def, D.leibniz, hD, RingHom.id_apply]`. Simplify using `}`. Use the proof step `(fun x y => D.leibniz x y)`.

Establish `hD' : ∀ r, D' r = D r` using `fun _ => rfl`. Use extensionality with `r`. Use `map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := R) (M := R)) (fun k => D (z k) • d k) Finset.univ` as an intermediate fact. Establish `h3` using `congrFun this r`. Rewrite `h3` using `[Finset.sum_apply]`.

Use `Eq.trans ?_ h3.symm` and prove the remaining obligations. Rewrite using `[← hD', ← D'.liftKaehlerDifferential_comp_D r, ← bΩ.sum_repr (KaehlerDifferential.D K R r), map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hb, D'.liftKaehlerDifferential_comp_D, hD']`. Simplify using `[hd', mul_comm]) e he M hM`.

Establish `hm : m ≤ n` using `by simpa using Fintype.card_le_of_injective e he`. Take `⟨σ, hσ⟩` from `Equiv.Perm.exists_extending_pair _ _ (Fin.castLE_injective hm) he`. Use `⟨b.reindex σ.symm, fun i k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.reindex_apply, Equiv.symm_symm, hb', ← hσ]`. Simplify using `[Fin.ext_iff]`.
-/
theorem exists_basis_of_kaehler {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] [IsNoetherianRing R]
    {n m : ℕ} (z : Fin n → R) (bΩ : Module.Basis (Fin n) R Ω[R⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K R (z i))
    (e : Fin m → Fin n) (he : Function.Injective e) (M : Submodule R (Derivation ℤ R R))
    (hM : ∀ D, D ∈ M ↔ (∀ a, D (algebraMap K R a) = 0) ∧
      ∀ f ∈ Ideal.span {∏ i, z (e i)}, D f ∈ Ideal.span {∏ i, z (e i)}) :
    ∃ b : Module.Basis (Fin n) R M, ∀ (i : Fin m) (k : Fin n),
      (b k).1 (z (e i)) = if (k : ℕ) = i then z (e i) else 0 := by
  classical
  have hQ : ∀ n : ℕ, IsUnit ((n : R) + 1) := fun n => by
    have := (IsUnit.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n)).map (algebraMap K R)
    simpa using this
  let d : Fin n → Derivation ℤ R R := fun k =>
    (KaehlerDifferential.linearMapEquivDerivation K R (bΩ.coord k)).restrictScalars ℤ
  have hd' : ∀ k r, d k r = bΩ.repr (KaehlerDifferential.D K R r) k := fun k r => rfl
  obtain ⟨b, hb'⟩ := exists_basis_of_dual hQ (algebraMap K R) z d
    (fun k l => by rw [hd', ← hb]; simp [Finsupp.single_apply, eq_comm])
    (fun k a => by rw [hd']; simp)
    (fun D hD => by
      let D' : Derivation K R R := Derivation.mk'
        { toFun := D
          map_add' := map_add D
          map_smul' := fun a r => by
            simp only [Algebra.smul_def, D.leibniz, hD, RingHom.id_apply]
            simp }
        (fun x y => D.leibniz x y)
      have hD' : ∀ r, D' r = D r := fun _ => rfl
      ext r
      have := map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := R) (M := R)) (fun k => D (z k) • d k) Finset.univ
      have h3 := congrFun this r
      rw [Finset.sum_apply] at h3
      refine Eq.trans ?_ h3.symm
      rw [← hD', ← D'.liftKaehlerDifferential_comp_D r, ← bΩ.sum_repr (KaehlerDifferential.D K R r), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hb, D'.liftKaehlerDifferential_comp_D, hD']
      simp [hd', mul_comm]) e he M hM
  have hm : m ≤ n := by simpa using Fintype.card_le_of_injective e he
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ (Fin.castLE_injective hm) he
  refine ⟨b.reindex σ.symm, fun i k => ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb', ← hσ]
  simp [Fin.ext_iff]

/- English proof (translation)
Establish `hbc` using `KaehlerDifferential.isBaseChange_of_formallyEtale k A B`. Set `v : Fin n → Ω[B⁄k]` to `fun i => KaehlerDifferential.D k B (algebraMap A B (z i))`. Establish `hv : ∀ i, v i = ∑ l, algebraMap A B (c i l) • hbc.basis b l`. Introduce `i`. Simplify using `only [v, ← KaehlerDifferential.map_D k k A B, hc, map_sum, map_smul, IsBaseChange.basis_apply, algebraMap_smul]`.

Establish `hm : (hbc.basis b).toMatrix v = (c.map (algebraMap A B)).transpose`. Use extensionality with `l i`. Rewrite using `[Module.Basis.toMatrix_apply, hv, Module.Basis.repr_sum_self]`. Both sides reduce to the same expression. Establish `hdet : IsUnit ((hbc.basis b).det v)`.

Rewrite using `[Module.Basis.det_apply, hm, Matrix.det_transpose]`. Rewrite `hu` using `[RingHom.map_det]`. Then use the resulting hypothesis. Take `⟨h1, h2⟩` from `(hbc.basis b).is_basis_iff_det.2 hdet`. Conclude with `⟨Module.Basis.mk h1 h2.ge, fun i => Module.Basis.mk_apply _ _ _⟩`.
-/
theorem exists_basis_map {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Algebra.FormallyEtale A B] {n : ℕ} (b : Module.Basis (Fin n) A Ω[A⁄k])
    (z : Fin n → A) (c : Matrix (Fin n) (Fin n) A)
    (hc : ∀ i, KaehlerDifferential.D k A (z i) = ∑ l, c i l • b l) (hu : IsUnit (algebraMap A B c.det)) :
    ∃ b' : Module.Basis (Fin n) B Ω[B⁄k], ∀ i, b' i = KaehlerDifferential.D k B (algebraMap A B (z i)) := by
  classical
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k A B
  let v : Fin n → Ω[B⁄k] := fun i => KaehlerDifferential.D k B (algebraMap A B (z i))
  have hv : ∀ i, v i = ∑ l, algebraMap A B (c i l) • hbc.basis b l := by
    intro i
    simp only [v, ← KaehlerDifferential.map_D k k A B, hc, map_sum, map_smul, IsBaseChange.basis_apply,
      algebraMap_smul]
  have hm : (hbc.basis b).toMatrix v = (c.map (algebraMap A B)).transpose := by
    ext l i
    rw [Module.Basis.toMatrix_apply, hv, Module.Basis.repr_sum_self]
    rfl
  have hdet : IsUnit ((hbc.basis b).det v) := by
    rw [Module.Basis.det_apply, hm, Matrix.det_transpose]
    rwa [RingHom.map_det] at hu
  obtain ⟨h1, h2⟩ := (hbc.basis b).is_basis_iff_det.2 hdet
  exact ⟨Module.Basis.mk h1 h2.ge, fun i => Module.Basis.mk_apply _ _ _⟩

end Algebra

section Geometry

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.AdaptedFrame
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

/- English proof (translation)
Set `f : Fin m → X.presheaf.stalk y` to `fun i => X.presheaf.germ O y hyO (s i)`. Establish `hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)` using `fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩`. Establish `hli` using `GlobalTheory.ParamFrame.linearIndependent_toCotangent f hrsp hf`. Take `⟨U, x, b, hUO, hyU, hU, hb⟩` from `exists_basis_dFun p n hyO`. Set `z₀ : Fin m → Γ(X, U)` to `fun j => resG X hUO (s j)`.

Establish `hz₀ (j : Fin m) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j`. Rewrite using `[germ_resG]`. Set `a : Fin m → Fin n → Γ(X, U)` to `fun j l => b.repr (dFun (algX p U) (z₀ j)) l`. Establish `ha (j : Fin m) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l)` using `by conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]`. Simplify using `only [hb, a]`.

Use `letI iΓ : Algebra k Γ(X, U) := (algX p U).toAlgebra`. Use `letI iA : Algebra k (X.presheaf.stalk y) := ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra`. Use `letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra`. Use `haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI := formallySmooth_residueField (n := n) p hU y hyU rfl`.

Establish `hw` using `linearIndependent_tmul_D (k := k) f hf hli`. Set `ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y)` to `(IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom`. Set `ab : Fin m → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y)` to `fun j l => ρ (a j l)`. Establish `hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab`. Set `wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y] Ω[(X.presheaf.stalk y)⁄k]` to `fun l => 1 ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))`.

Use `LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_` and prove the remaining obligations. Establish `key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab = fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y] KaehlerDifferential.D k (X.presheaf.stalk y) (f j)`. Use function extensionality and compare the values at `j`. Rewrite using `[Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]`. Establish `e1` using `congrArg (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)) (ha j)`.

Rewrite `e1` using `[map_sum]`. Express the relevant statement in the definitionally equal form `KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y) (KaehlerDifferential.D k Γ(X, U) (z₀ j)) = _ at e1`. Rewrite `e1` using `[KaehlerDifferential.map_D]`. Express the relevant statement in the definitionally equal form `KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1`. Rewrite using `[e1, TensorProduct.tmul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `_ = 1 ⊗ₜ (a j l • KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y) (KaehlerDifferential.D k Γ(X, U) (x l)))`. Rewrite using `[KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l), TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]`. Both sides reduce to the same expression.

Rewrite using `[key]`. Conclude with `hw`. Take `⟨e, he, hdet⟩` from `GlobalTheory.extend_linearIndependent_rows_by_standard_basis ab hab`. Set `z : Fin n → Γ(X, U)` to `Function.extend e z₀ x`. Set `c : Matrix (Fin n) (Fin n) Γ(X, U)` to `Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))`.

Establish `hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l)`. Distinguish the cases in `hi : ∃ j, e j = i`. Take `⟨j, rfl⟩` from `hi`. Simplify using `only [z, c, Matrix.of_apply, he.extend_apply]`. Conclude with `ha j`.

Simplify using `only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]`. Simplify using `[Pi.single_apply]`. Establish `hρ : ρ c.det ≠ 0`. Establish `hm : c.map ρ = Matrix.of (Function.extend e ab (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y))))`. Use extensionality with `i l`.

Distinguish the cases in `hi : ∃ j, e j = i`. Take `⟨j, rfl⟩` from `hi`. Simplify using `only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]`. Simplify using `only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]`. Distinguish the cases in `hil : l = i`.

Substitute `hil` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hil]`. Rewrite using `[RingHom.map_det]`. Conclude with `(congrArg Matrix.det hm).trans_ne hdet`.

Establish `hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det)` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ`. Establish `hyW : y ∈ X.basicOpen c.det` using `(X.mem_basicOpen c.det y hyU).2 hunit`. Establish `hVU : X.basicOpen c.det ≤ U` using `X.basicOpen_le _`. Use `⟨X.basicOpen c.det, hVU.trans hUO, e, hyW, he, fun W hW hWa => ?_⟩` and prove the remaining obligations. Establish `hWU : W ≤ U` using `hW.trans hVU`.

Use `letI : Algebra k Γ(X, W) := (algX p W).toAlgebra`. Use `letI : Algebra Γ(X, U) Γ(X, W) := (resG X hWU).toAlgebra`. Use `haveI : IsScalarTower k Γ(X, U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' (resG_comp_algX p hWU).symm`. Use `haveI : Algebra.FormallyEtale Γ(X, U) Γ(X, W) := by`. Establish `h` using `HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨U, hU⟩ ⟨W, hWa⟩ hWU`.

Establish `e : ((𝟙 X : X ⟶ X).appLE U W hWU).hom = resG X hWU`. Use extensionality with `r`. Both sides reduce to the same expression. Rewrite `h` using `[e]`. Use `haveI : Algebra.Etale Γ(X, U) Γ(X, W) := h`.

Use `infer_instance`. Establish `hu : IsUnit (algebraMap Γ(X, U) Γ(X, W) c.det)`. Use `(RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det).map (resG X hW)` as an intermediate fact. Conclude with `(resG_resG _ _ _).symm ▸ this`. Take `⟨b', hb'⟩` from `exists_basis_map (k := k) (B := Γ(X, W)) b z c (fun i => by simpa only [hb] using hdz i) hu`.

Use `⟨fun i => resG X hWU (z i), b', fun j => ?_, hb'⟩` and prove the remaining obligations. Simplify using `only [z, z₀, he.extend_apply]`. Conclude with `resG_resG _ _ _`.
-/
theorem exists_coords {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsLocallyNoetherian X] (p : X ⟶ Sp k) (n : ℕ)
    [SmoothOfRelativeDimension n p] (y : X) (O : X.Opens) (hyO : y ∈ O) {m : ℕ} (s : Fin m → Γ(X, O))
    (hrsp : FinalTheorems.Rsp (X.presheaf.stalk y) m (fun i => X.presheaf.germ O y hyO (s i))) :
    ∃ (V : X.Opens) (hV : V ≤ O) (e : Fin m → Fin n), y ∈ V ∧ Function.Injective e ∧
      ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
        ∃ (z : Fin n → Γ(X, W)) (b : Module.Basis (Fin n) Γ(X, W) (Omega (algX p W))),
          (∀ j, z (e j) = resG X (hW.trans hV) (s j)) ∧ ∀ i, b i = dFun (algX p W) (z i) := by
  classical
  let f : Fin m → X.presheaf.stalk y := fun i => X.presheaf.germ O y hyO (s i)
  have hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hli := GlobalTheory.ParamFrame.linearIndependent_toCotangent f hrsp hf
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : Fin m → Γ(X, U) := fun j => resG X hUO (s j)
  have hz₀ (j : Fin m) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]
  let a : Fin m → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : Fin m) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]
  letI iΓ : Algebra k Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra k (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := k) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : Fin m → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄k] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D k (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)) (ha j)
      rw [map_sum] at e1
      change KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw
  obtain ⟨e, he, hdet⟩ := GlobalTheory.extend_linearIndependent_rows_by_standard_basis ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hVU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hVU.trans hUO, e, hyW, he, fun W hW hWa => ?_⟩
  have hWU : W ≤ U := hW.trans hVU
  letI : Algebra k Γ(X, W) := (algX p W).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, W) := (resG X hWU).toAlgebra
  haveI : IsScalarTower k Γ(X, U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' (resG_comp_algX p hWU).symm
  haveI : Algebra.FormallyEtale Γ(X, U) Γ(X, W) := by
    have h := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨U, hU⟩ ⟨W, hWa⟩ hWU
    have e : ((𝟙 X : X ⟶ X).appLE U W hWU).hom = resG X hWU := by
      ext r
      rfl
    rw [e] at h
    haveI : Algebra.Etale Γ(X, U) Γ(X, W) := h
    infer_instance
  have hu : IsUnit (algebraMap Γ(X, U) Γ(X, W) c.det) := by
    have := (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det).map (resG X hW)
    exact (resG_resG _ _ _).symm ▸ this
  obtain ⟨b', hb'⟩ := exists_basis_map (k := k) (B := Γ(X, W)) b z c (fun i => by simpa only [hb] using hdz i) hu
  refine ⟨fun i => resG X hWU (z i), b', fun j => ?_, hb'⟩
  simp only [z, z₀, he.extend_apply]
  exact resG_resG _ _ _

/- English proof (translation)
Use `haveI : Smooth p := SmoothOfRelativeDimension.smooth n p`. Use `haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p`. Take `⟨-, O, hxO, r, s, J, hrsp, hO⟩` from `hI x`. Take `⟨V, hV, e, hxV, he, H⟩` from `exists_coords p n x O.1 hxO s hrsp`. Take `⟨f, hfV, hxf⟩` from `U.2.exists_basicOpen_le ⟨x, hxV⟩ hx`.

Set `W : X.affineOpens` to `⟨X.basicOpen f, U.2.basicOpen f⟩`. Take `⟨z, bΩ, hz, hb⟩` from `H W.1 hfV W.2`. Set `ix : Fin J.card → Fin r` to `fun i => (J.equivFin.symm i).1`. Establish `hix : Function.Injective ix` using `fun i j h => J.equivFin.symm.injective (Subtype.ext h)`. Establish `hWO : W ≤ O` using `hfV.trans hV`.

Establish `hideal : I.ideal W = Ideal.span {∏ i, z (e (ix i))}`. Rewrite using `[← I.map_ideal hWO, hO, Ideal.map_span, Set.image_singleton, map_prod, ← Finset.prod_coe_sort J, ← J.equivFin.symm.prod_comp]`. Simplify using `only [hz]`. Both sides reduce to the same expression. Use `letI : Algebra k Γ(X, W.1) := (algX p W.1).toAlgebra`.

Use `haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W`. Take `⟨b, hb'⟩` from `exists_basis_of_kaehler (K := k) z bΩ hb (e ∘ ix) (he.comp hix) (LogKS.logDer p I W) (fun D => by`. Express the relevant statement in the definitionally equal form `((∀ a, D (constFn p W.1 a) = 0) ∧ ∀ g ∈ I.ideal W, D g ∈ I.ideal W) ↔ _`. Rewrite using `[hideal]`. Use the proof step `rfl)`.

Conclude with `⟨f, W, J.card, fun i => z (e (ix i)), b, hxf, rfl, hideal, hb'⟩`.
-/
theorem exists_logDer_basis_of_snc {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℕ)
    [SmoothOfRelativeDimension n p] (I : X.IdealSheafData) (hI : FinalTheorems.Snc I) (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    ∃ (f : Γ(X, U.1)) (W : X.affineOpens) (m : ℕ) (t : Fin m → Γ(X, W.1))
      (b : Module.Basis (Fin n) Γ(X, W.1) (LogKS.logDer p I W)), x ∈ W.1 ∧ W.1 = X.basicOpen f ∧
      I.ideal W = Ideal.span {∏ i, t i} ∧
      ∀ (i : Fin m) (l : Fin n), ((b l).1 : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (t i) = if (l : ℕ) = i then t i else 0 := by
  classical
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨-, O, hxO, r, s, J, hrsp, hO⟩ := hI x
  obtain ⟨V, hV, e, hxV, he, H⟩ := exists_coords p n x O.1 hxO s hrsp
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hx
  let W : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  obtain ⟨z, bΩ, hz, hb⟩ := H W.1 hfV W.2
  let ix : Fin J.card → Fin r := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hWO : W ≤ O := hfV.trans hV
  have hideal : I.ideal W = Ideal.span {∏ i, z (e (ix i))} := by
    rw [← I.map_ideal hWO, hO, Ideal.map_span, Set.image_singleton, map_prod, ← Finset.prod_coe_sort J,
      ← J.equivFin.symm.prod_comp]
    simp only [hz]
    rfl
  letI : Algebra k Γ(X, W.1) := (algX p W.1).toAlgebra
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  obtain ⟨b, hb'⟩ := exists_basis_of_kaehler (K := k) z bΩ hb (e ∘ ix) (he.comp hix) (LogKS.logDer p I W)
    (fun D => by
      change ((∀ a, D (constFn p W.1 a) = 0) ∧ ∀ g ∈ I.ideal W, D g ∈ I.ideal W) ↔ _
      rw [hideal]
      rfl)
  exact ⟨f, W, J.card, fun i => z (e (ix i)), b, hxf, rfl, hideal, hb'⟩

end Geometry

end GlobalTheory.LogBasis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y _ hs hsnc U x hx`. Use `haveI := smooth_gen_iff.1 hs`. Take `⟨f, W, m, t, b, h1, h2, h3, h4⟩` from `GlobalTheory.LogBasis.exists_logDer_basis_of_snc Y.s Dw.dim _ (snc_gen_iff.1 hsnc) U x hx`. Establish `h3' : (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W = Ideal.span {∏ i, t i}` using `h3`. Conclude with `⟨f, W, h2 ▸ Y.X.basicOpen_le f, m, t, b, h1, h2, fun g hg => h3' ▸ hg, h3' ▸ Ideal.mem_span_singleton_self _, h4⟩`.
-/
theorem GlobalTheory.LogBasis.exists_logDer_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (x : Y.X), x ∈ U.1 → ∃ (f : Γ(Y.X, U.1)) (W : Y.X.affineOpens) (hW : W.1 ≤ U.1) (m : ℕ) (t : Fin m → Γ(Y.X, W.1)) (b : Module.Basis (Fin Dw.dim) Γ(Y.X, W.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) W)), x ∈ W.1 ∧ W.1 = Y.X.basicOpen f ∧ (∀ g ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W, g ∈ Ideal.span {∏ i, t i}) ∧ ∏ i, t i ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W ∧ ∀ (i : Fin m) (k : Fin Dw.dim), ((b k).1 : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (t i) = if (k : ℕ) = i then t i else 0 := by
  intro E _ _ _ H Dw l Xo c Y _ hs hsnc U x hx
  haveI := smooth_gen_iff.1 hs
  obtain ⟨f, W, m, t, b, h1, h2, h3, h4⟩ :=
    GlobalTheory.LogBasis.exists_logDer_basis_of_snc Y.s Dw.dim _ (snc_gen_iff.1 hsnc) U x hx
  have h3' : (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W = Ideal.span {∏ i, t i} := h3
  exact ⟨f, W, h2 ▸ Y.X.basicOpen_le f, m, t, b, h1, h2, fun g hg => h3' ▸ hg,
    h3' ▸ Ideal.mem_span_singleton_self _, h4⟩
