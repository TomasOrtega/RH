import Formalism.LagrangeIdealLifts.Statement

noncomputable section

namespace Formalism.LIFT

open Finset

section XH

variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)

def Comps (ℓ : ℕ) (x : A) : Prop :=
  ∃ e : Fin ℓ → A, (∀ i, e i ∈ aa) ∧ x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ => aa.zero_mem, by simp⟩`.
-/
theorem comps_zero : Comps φA ε aa ℓ 0 :=
  ⟨0, fun _ => aa.zero_mem, by simp⟩

/- English proof (translation)
Take `⟨e, he, rfl⟩` from `hx`. Take `⟨e', he', rfl⟩` from `hy`. Use `⟨e + e', fun i => aa.add_mem (he i) (he' i), ?_⟩` and prove the remaining obligations. Simplify using `[map_add, mul_add, sum_add_distrib]`.
-/
theorem comps_add {x y : A} (hx : Comps φA ε aa ℓ x) (hy : Comps φA ε aa ℓ y) :
    Comps φA ε aa ℓ (x + y) := by
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨e', he', rfl⟩ := hy
  refine ⟨e + e', fun i => aa.add_mem (he i) (he' i), ?_⟩
  simp [map_add, mul_add, sum_add_distrib]

/- English proof (translation)
Take `⟨e, he, rfl⟩` from `hx`. Use `⟨fun i => s * e i, fun i => aa.mul_mem_left s (he i), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_sum]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem comps_mul_phi (s : A) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (φA s * x) := by
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨fun i => s * e i, fun i => aa.mul_mem_left s (he i), ?_⟩
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, ℓ = k + 1` from `⟨ℓ - 1, by omega⟩`. Take `⟨e, he, rfl⟩` from `hx`. Use `⟨Fin.cons (ε * e (Fin.last k)) (fun i => e i.castSucc), ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using aa.mul_mem_left ε (he (Fin.last k))`. Simplify using `using he j.castSucc`. Rewrite using `[Fin.sum_univ_castSucc, Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, map_mul, hε, pow_zero, one_mul, mul_add, mul_sum]`. Rewrite using `[add_comm]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comps_mul_eps (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (ε * x) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨Fin.cons (ε * e (Fin.last k)) (fun i => e i.castSucc), ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using aa.mul_mem_left ε (he (Fin.last k))
    · simpa using he j.castSucc
  · rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, map_mul, hε, pow_zero, one_mul, mul_add, mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine sum_congr rfl fun i _ => ?_
      ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hx`. Consider the case `succ n ih`. Rewrite using `[pow_succ', mul_assoc]`. Conclude with `comps_mul_eps φA ε aa hℓ hε ih`.
-/
theorem comps_mul_pow (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) (n : ℕ) {x : A}
    (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (ε ^ n * x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact comps_mul_eps φA ε aa hℓ hε ih

/- English proof (translation)
The claim follows from `Finset.sum_induction _ _ (fun _ _ => comps_add φA ε aa) (comps_zero φA ε aa) h`.
-/
theorem comps_sum {ι : Type} (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, Comps φA ε aa ℓ (f i)) :
    Comps φA ε aa ℓ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ _ (fun _ _ => comps_add φA ε aa) (comps_zero φA ε aa) h

/- English proof (translation)
Take `⟨e, he⟩` from `(hU r).exists`. Rewrite using `[he, sum_mul]`. Use `comps_sum φA ε aa _ _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `comps_mul_pow φA ε aa hℓ hε _ (comps_mul_phi φA ε aa _ hx)`.
-/
theorem comps_mul (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (r : A) {x : A} (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (r * x) := by
  obtain ⟨e, he⟩ := (hU r).exists
  rw [he, sum_mul]
  refine comps_sum φA ε aa _ _ fun i _ => ?_
  rw [mul_assoc]
  exact comps_mul_pow φA ε aa hℓ hε _ (comps_mul_phi φA ε aa _ hx)

/- English proof (translation)
Use `⟨fun i => if (i : ℕ) = 0 then a else 0, fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs`. Conclude with `ha`. Conclude with `aa.zero_mem`. Rewrite using `[Fintype.sum_eq_single ⟨0, hℓ⟩]`.

Simplify using the standard rewrite rules. Introduce `i hi`. Establish `: (i : ℕ) ≠ 0` using `fun h => hi (Fin.ext h)`. Simplify using `[this]`.
-/
theorem comps_phi (hℓ : 0 < ℓ) {a : A} (ha : a ∈ aa) : Comps φA ε aa ℓ (φA a) := by
  refine ⟨fun i => if (i : ℕ) = 0 then a else 0, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ha
    · exact aa.zero_mem
  · rw [Fintype.sum_eq_single ⟨0, hℓ⟩]
    · simp
    · intro i hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]

/- English proof (translation)
Set `S : Ideal A` to `{ carrier := {x | Comps φA ε aa ℓ x} add_mem' := fun ha hb => comps_add φA ε aa ha hb zero_mem' := comps_zero φA ε aa smul_mem' := fun r _ hx => comps_mul φA ε aa hℓ hε hU r hx }`. Establish `hle : Ideal.map φA aa ≤ S` using `Ideal.map_le_iff_le_comap.2 fun a ha => comps_phi φA ε aa hℓ ha`. Conclude with `hle hx`.
-/
theorem comps_of_mem_map (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) : Comps φA ε aa ℓ x := by
  let S : Ideal A :=
    { carrier := {x | Comps φA ε aa ℓ x}
      add_mem' := fun ha hb => comps_add φA ε aa ha hb
      zero_mem' := comps_zero φA ε aa
      smul_mem' := fun r _ hx => comps_mul φA ε aa hℓ hε hU r hx }
  have hle : Ideal.map φA aa ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun a ha => comps_phi φA ε aa hℓ ha
  exact hle hx

/- English proof (translation)
Take `⟨e', he', hx'⟩` from `comps_of_mem_map φA ε aa hℓ hε hU hx`. Establish `: e = e'` using `(hU x).unique he hx'`. Rewrite using `[this]`. Conclude with `he' i`.
-/
theorem comp_mem (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (he : x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) (i : Fin ℓ) : e i ∈ aa := by
  obtain ⟨e', he', hx'⟩ := comps_of_mem_map φA ε aa hℓ hε hU hx
  have : e = e' := (hU x).unique he hx'
  rw [this]
  exact he' i

/- English proof (translation)
Establish `h1` using `hQ _ h`. Establish `h2 : Q ^ H * (X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (X ^ H * e i)`. Simplify using `only [map_mul, map_pow, hX, mul_sum]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Conclude with `comp_mem φA ε aa hℓ hε hU h1 (fun i => X ^ H * e i) h2 i`.
-/
theorem xh_comp (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (h : X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) ∈ aa) (i : Fin ℓ) :
    X ^ H * e i ∈ aa := by
  have h1 := hQ _ h
  have h2 : Q ^ H * (X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) =
      ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (X ^ H * e i) := by
    simp only [map_mul, map_pow, hX, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  exact comp_mem φA ε aa hℓ hε hU h1 (fun i => X ^ H * e i) h2 i

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Nat.mul_succ, sum_range_add, ← ih]`. Simplify using `only [sum_range_succ, sum_add_distrib]`.

Use `congr 1`. Rewrite using `[Finset.sum_range (fun x => F (a * N + x))]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[add_comm]`.
-/
theorem sum_split {M : Type} [AddCommMonoid M] (F : ℕ → M) (a N : ℕ) :
    ∑ i : Fin a, ∑ j ∈ range N, F (i + a * j) = ∑ k ∈ range (a * N), F k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ← ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    rw [Finset.sum_range (fun x => F (a * N + x))]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `m h k hk`. Establish `hk0 : k = 0` using `by simpa using hk`. Substitute `hk0` using the available equality.

Simplify using `using h`. Consider the case `succ n ih`. Introduce `m h k hk`. Set `e : Fin ℓ → A` to `fun i => ∑ j ∈ range (ℓ ^ n), (m (i + ℓ * j) : A) * ε ^ j`. Establish `hdec : ∑ k ∈ range (ℓ ^ (n + 1)), (m k : A) * ε ^ k = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)`.

Rewrite using `[pow_succ', ← sum_split (fun k => (m k : A) * ε ^ k) ℓ (ℓ ^ n)]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [e, map_sum, map_mul, map_intCast, map_pow, hε, mul_sum]`. Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_add, ← pow_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hdec]`. Establish `hb` using `xh_comp φA ε aa hℓ hε hU X Q H hX hQ e h ⟨k % ℓ, Nat.mod_lt _ hℓ⟩`. Establish `hk' : k / ℓ < ℓ ^ n`. Rewrite using `[Nat.div_lt_iff_lt_mul hℓ]`.

Rewrite `hk` using `[pow_succ]`. Conclude with `hk`. Use `ih (fun j => m (k % ℓ + ℓ * j)) hb (k / ℓ) hk'` as an intermediate fact. Simplify `this` using `[Nat.mod_add_div]`.
-/
theorem xh_coeffs (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (n : ℕ) :
    ∀ m : ℕ → ℤ, X ^ H * ∑ k ∈ range (ℓ ^ n), (m k : A) * ε ^ k ∈ aa →
      ∀ k < ℓ ^ n, X ^ H * (m k : A) ∈ aa := by
  induction n with
  | zero =>
    intro m h k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simpa using h
  | succ n ih =>
    intro m h k hk
    let e : Fin ℓ → A := fun i => ∑ j ∈ range (ℓ ^ n), (m (i + ℓ * j) : A) * ε ^ j
    have hdec : ∑ k ∈ range (ℓ ^ (n + 1)), (m k : A) * ε ^ k =
        ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) := by
      rw [pow_succ', ← sum_split (fun k => (m k : A) * ε ^ k) ℓ (ℓ ^ n)]
      refine sum_congr rfl fun i _ => ?_
      simp only [e, map_sum, map_mul, map_intCast, map_pow, hε, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add, ← pow_mul]
      ring
    rw [hdec] at h
    have hb := xh_comp φA ε aa hℓ hε hU X Q H hX hQ e h ⟨k % ℓ, Nat.mod_lt _ hℓ⟩
    have hk' : k / ℓ < ℓ ^ n := by
      rw [Nat.div_lt_iff_lt_mul hℓ]
      rw [pow_succ] at hk
      exact hk
    have := ih (fun j => m (k % ℓ + ℓ * j)) hb (k / ℓ) hk'
    simpa [Nat.mod_add_div] using this

end XH

/- English proof (translation)
Introduce `ℓ _ A _ φA ε X Q H c aa _ hε hU hX hQ hc`. Establish `hℓ : 0 < ℓ` using `(Fact.out : ℓ.Prime).pos`. Establish `h1 : 1 < ℓ` using `(Fact.out : ℓ.Prime).one_lt`. Take `⟨n, hn⟩ : ∃ n, c < ℓ ^ n` from `⟨c, Nat.lt_pow_self h1⟩`. Set `p : Polynomial ℤ` to `(Polynomial.X - Polynomial.C 1) ^ c`.

Establish `hmon : p.Monic` using `(Polynomial.monic_X_sub_C (1 : ℤ)).pow c`. Establish `hdeg : p.natDegree = c`. Simplify using `only [p]`. Rewrite using `[Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]`. Establish `hsum : (ε - 1) ^ c = ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k`.

Use `Polynomial.aeval_eq_sum_range' (p := p) (by omega : p.natDegree < ℓ ^ n) ε` as an intermediate fact. Simplify using `only [zsmul_eq_mul] at this`. Rewrite using `[← this]`. Simplify using `[p]`. Establish `hmem : X ^ H * ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k ∈ aa`.

Rewrite using `[← hsum]`. Conclude with `aa.mul_mem_left _ hc`. Use `xh_coeffs φA ε aa hℓ hε hU X Q H hX hQ n (fun k => p.coeff k) hmem c hn` as an intermediate fact. Establish `hcoef : p.coeff c = 1`. Use `hmon.coeff_natDegree` as an intermediate fact.

Rewrite `this` using `[hdeg]`. Then use the resulting hypothesis. Simplify `this` using `[hcoef]`.
-/
theorem xHKills_proof : XHKills := by
  intro ℓ _ A _ φA ε X Q H c aa _ hε hU hX hQ hc
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have h1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  obtain ⟨n, hn⟩ : ∃ n, c < ℓ ^ n := ⟨c, Nat.lt_pow_self h1⟩
  let p : Polynomial ℤ := (Polynomial.X - Polynomial.C 1) ^ c
  have hmon : p.Monic := (Polynomial.monic_X_sub_C (1 : ℤ)).pow c
  have hdeg : p.natDegree = c := by
    simp only [p]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hsum : (ε - 1) ^ c = ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k := by
    have := Polynomial.aeval_eq_sum_range' (p := p) (by omega : p.natDegree < ℓ ^ n) ε
    simp only [zsmul_eq_mul] at this
    rw [← this]
    simp [p]
  have hmem : X ^ H * ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k ∈ aa := by
    rw [← hsum]
    exact aa.mul_mem_left _ hc
  have := xh_coeffs φA ε aa hℓ hε hU X Q H hX hQ n (fun k => p.coeff k) hmem c hn
  have hcoef : p.coeff c = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  simpa [hcoef] using this

end Formalism.LIFT
