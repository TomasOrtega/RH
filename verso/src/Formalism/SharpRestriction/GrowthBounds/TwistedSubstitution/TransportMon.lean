import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.PlaneCoeff

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.PlaneGramData Formalism.MainNotions.Pf14

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def LowDiv (mo : TV n' (m + 1) →₀ ℕ) : Prop :=
  (∀ x (a : Fin r), lowP Fr p x ∣ mo (plVar Fr hk nL x a)) ∧ ∀ x (b : Fin K), lowP Fr p x ∣ mo (noVar Fr hk nL x b)

/- English proof (translation)
Establish `e1 : ∀ x a, (mo₁ + mo₂) (plVar Fr hk nL x a) % lowP Fr p x = mo₁ (plVar Fr hk nL x a) % lowP Fr p x`. Introduce `x a`. Take `⟨k, hk'⟩` from `h.1 x a`. Rewrite using `[Finsupp.add_apply, hk', Nat.add_mul_mod_self_left]`. Establish `e2 : ∀ x b, (mo₁ + mo₂) (noVar Fr hk nL x b) % lowP Fr p x = mo₁ (noVar Fr hk nL x b) % lowP Fr p x`.

Introduce `x b`. Take `⟨k, hk'⟩` from `h.2 x b`. Rewrite using `[Finsupp.add_apply, hk', Nat.add_mul_mod_self_left]`. Unfold `InLow`. Simplify using `only [e1, e2]`.
-/
theorem inLow_add (rho : TL J nL r × Fin (r + K) → ℕ) (mo₁ mo₂ : TV n' (m + 1) →₀ ℕ)
    (h : LowDiv Fr p hk nL mo₂) : InLow Fr p hk nL rho (mo₁ + mo₂) ↔ InLow Fr p hk nL rho mo₁ := by
  have e1 : ∀ x a, (mo₁ + mo₂) (plVar Fr hk nL x a) % lowP Fr p x = mo₁ (plVar Fr hk nL x a) % lowP Fr p x := by
    intro x a
    obtain ⟨k, hk'⟩ := h.1 x a
    rw [Finsupp.add_apply, hk', Nat.add_mul_mod_self_left]
  have e2 : ∀ x b, (mo₁ + mo₂) (noVar Fr hk nL x b) % lowP Fr p x = mo₁ (noVar Fr hk nL x b) % lowP Fr p x := by
    intro x b
    obtain ⟨k, hk'⟩ := h.2 x b
    rw [Finsupp.add_apply, hk', Nat.add_mul_mod_self_left]
  unfold InLow
  simp only [e1, e2]

/- English proof (translation)
The claim follows from `pow_pos hp _`.
-/
theorem lowP_pos (hp : 0 < p) (x : TL J nL r) : 0 < lowP Fr p x := pow_pos hp _

/- English proof (translation)
Use extensionality with `⟨x, a⟩`. Simplify using `only [plMon, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]`. Take `⟨c, hc⟩` from `h.1 x a`. Rewrite using `[hc, Nat.add_mul_div_left _ _ (lowP_pos Fr p nL hp x), Nat.mul_div_cancel_left _ (lowP_pos Fr p nL hp x)]`.
-/
theorem plMon_add (hp : 0 < p) (mo₁ mo₂ : TV n' (m + 1) →₀ ℕ) (h : LowDiv Fr p hk nL mo₂) :
    plMon Fr p hk nL (mo₁ + mo₂) = plMon Fr p hk nL mo₁ + plMon Fr p hk nL mo₂ := by
  ext ⟨x, a⟩
  simp only [plMon, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
  obtain ⟨c, hc⟩ := h.1 x a
  rw [hc, Nat.add_mul_div_left _ _ (lowP_pos Fr p nL hp x), Nat.mul_div_cancel_left _ (lowP_pos Fr p nL hp x)]

/- English proof (translation)
Use extensionality with `⟨x, b⟩`. Simplify using `only [noMon, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]`. Take `⟨c, hc⟩` from `h.2 x b`. Rewrite using `[hc, Nat.add_mul_div_left _ _ (lowP_pos Fr p nL hp x), Nat.mul_div_cancel_left _ (lowP_pos Fr p nL hp x)]`.
-/
theorem noMon_add (hp : 0 < p) (mo₁ mo₂ : TV n' (m + 1) →₀ ℕ) (h : LowDiv Fr p hk nL mo₂) :
    noMon Fr p hk nL (mo₁ + mo₂) = noMon Fr p hk nL mo₁ + noMon Fr p hk nL mo₂ := by
  ext ⟨x, b⟩
  simp only [noMon, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
  obtain ⟨c, hc⟩ := h.2 x b
  rw [hc, Nat.add_mul_div_left _ _ (lowP_pos Fr p nL hp x), Nat.mul_div_cancel_left _ (lowP_pos Fr p nL hp x)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x a => by rw [Finsupp.add_apply]; exact dvd_add (h1.1 x a) (h2.1 x a), fun x b => by rw [Finsupp.add_apply]; exact dvd_add (h1.2 x b) (h2.2 x b)⟩`.
-/
theorem lowDiv_add {mo₁ mo₂ : TV n' (m + 1) →₀ ℕ} (h1 : LowDiv Fr p hk nL mo₁) (h2 : LowDiv Fr p hk nL mo₂) :
    LowDiv Fr p hk nL (mo₁ + mo₂) :=
  ⟨fun x a => by rw [Finsupp.add_apply]; exact dvd_add (h1.1 x a) (h2.1 x a),
   fun x b => by rw [Finsupp.add_apply]; exact dvd_add (h1.2 x b) (h2.2 x b)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => by simp, fun _ _ => by simp⟩`.
-/
theorem lowDiv_zero : LowDiv Fr p hk nL (0 : TV n' (m + 1) →₀ ℕ) :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

def GeoOK : Prop :=
  ∀ (j : ℕ), j < Fr.J → ∀ y ∈ Fr.letters (j : ℤ), ∀ x' : TL J nL r,
    posOf n' (posTL Fr x') = posOf n' y → lowP Fr p x' ∣ p ^ Fr.dist (j : ℤ) y

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x a`. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs with hv`. Conclude with `h x (Or.inl ⟨a, hv.symm⟩)`.

Conclude with `dvd_zero _`. Introduce `x b`. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs with hv`. Conclude with `h x (Or.inr ⟨b, hv.symm⟩)`.

Conclude with `dvd_zero _`.
-/
theorem lowDiv_single (v : TV n' (m + 1)) (N : ℕ)
    (h : ∀ x' : TL J nL r, (∃ a, plVar Fr hk nL x' a = v) ∨ (∃ b, noVar Fr hk nL x' b = v) → lowP Fr p x' ∣ N) :
    LowDiv Fr p hk nL (Finsupp.single v N) := by
  constructor
  · intro x a
    rw [Finsupp.single_apply]
    split_ifs with hv
    · exact h x (Or.inl ⟨a, hv.symm⟩)
    · exact dvd_zero _
  · intro x b
    rw [Finsupp.single_apply]
    split_ifs with hv
    · exact h x (Or.inr ⟨b, hv.symm⟩)
    · exact dvd_zero _

/- English proof (translation)
Apply `lowDiv_single` to reduce the goal to its premises. Introduce `x' hx'`. Establish `hpos : posOf n' (posTL Fr x') = posOf n' y`. Break down `hx' with ⟨a, ha⟩ | ⟨b, hb⟩` into its components or cases. Conclude with `congrArg Prod.fst ha`.

Conclude with `congrArg Prod.fst hb`. Conclude with `Dvd.dvd.mul_right (hG j hj y hy x' hpos) e`.
-/
theorem lowDiv_phVar (hG : GeoOK Fr p nL) (j : ℕ) (hj : j < Fr.J) (y : ℤ) (hy : y ∈ Fr.letters (j : ℤ))
    (c : Fin (m + 1)) (e : ℕ) :
    LowDiv Fr p hk nL (Finsupp.single (posOf n' y, c) (p ^ Fr.dist (j : ℤ) y * e)) := by
  apply lowDiv_single
  intro x' hx'
  have hpos : posOf n' (posTL Fr x') = posOf n' y := by
    rcases hx' with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact congrArg Prod.fst ha
    · exact congrArg Prod.fst hb
  exact Dvd.dvd.mul_right (hG j hj y hy x' hpos) e

def LD {R : Type*} [CommSemiring R] (P : MvPolynomial (TV n' (m + 1)) R) : Prop :=
  ∀ mo ∈ P.support, LowDiv Fr p hk nL mo

/- English proof (translation)
Introduce `mo hmo`. Break down `Finset.mem_union.1 (MvPolynomial.support_add hmo) with h | h` into its components or cases. Conclude with `hP mo h`. Conclude with `hQ mo h`.
-/
theorem LD_add {R : Type*} [CommSemiring R] {P Q : MvPolynomial (TV n' (m + 1)) R} (hP : LD Fr p hk nL P)
    (hQ : LD Fr p hk nL Q) : LD Fr p hk nL (P + Q) := by
  intro mo hmo
  rcases Finset.mem_union.1 (MvPolynomial.support_add hmo) with h | h
  · exact hP mo h
  · exact hQ mo h

/- English proof (translation)
Introduce `mo hmo`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 (MvPolynomial.support_mul P Q hmo)`. Conclude with `lowDiv_add Fr p hk nL (hP a ha) (hQ b hb)`.
-/
theorem LD_mul {R : Type*} [CommSemiring R] {P Q : MvPolynomial (TV n' (m + 1)) R} (hP : LD Fr p hk nL P)
    (hQ : LD Fr p hk nL Q) : LD Fr p hk nL (P * Q) := by
  intro mo hmo
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hmo)
  exact lowDiv_add Fr p hk nL (hP a ha) (hQ b hb)

/- English proof (translation)
Introduce `mo hmo`. Rewrite `hmo` using `[mem_support_iff, coeff_C]`. Use `split_ifs at hmo with h0`. Substitute `h0` using the available equality. Conclude with `lowDiv_zero Fr p hk nL`.

Conclude with `absurd rfl hmo`.
-/
theorem LD_C {R : Type*} [CommSemiring R] (c : R) : LD Fr p hk nL (C c : MvPolynomial (TV n' (m + 1)) R) := by
  intro mo hmo
  rw [mem_support_iff, coeff_C] at hmo
  split_ifs at hmo with h0
  · subst h0
    exact lowDiv_zero Fr p hk nL
  · exact absurd rfl hmo

/- English proof (translation)
Introduce `mo' hmo`. Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset hmo)]`. Conclude with `h`.
-/
theorem LD_monomial {R : Type*} [CommSemiring R] (mo : TV n' (m + 1) →₀ ℕ) (c : R) (h : LowDiv Fr p hk nL mo) :
    LD Fr p hk nL (monomial mo c) := by
  intro mo' hmo
  rw [Finset.mem_singleton.mp (support_monomial_subset hmo)]
  exact h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using LD_C Fr p hk nL (1 : R)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `LD_mul Fr p hk nL (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem LD_prod {R : Type*} [CommSemiring R] {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial (TV n' (m + 1)) R)
    (h : ∀ i ∈ s, LD Fr p hk nL (f i)) : LD Fr p hk nL (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using LD_C Fr p hk nL (1 : R)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact LD_mul Fr p hk nL (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Rewrite `hx` using `[MvPolynomial.supported_eq_adjoin_X]`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem v hv`. Take `⟨w, hw, rfl⟩` from `hv`. Rewrite using `[phSeg, aeval_X, map_pow, rename_X, X_pow_eq_monomial]`.

Apply `LD_monomial` to reduce the goal to its premises. Use `lowDiv_phVar Fr p hk nL hG j hj w.1 hw (Fin.cast (by omega) w.2) 1` as an intermediate fact. Simplify `this` using `[castV]`. Consider the case `algebraMap c`. Rewrite using `[AlgHom.commutes, algebraMap_eq, rename_C]`.

Conclude with `LD_C Fr p hk nL c`. Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add, map_add]`. Conclude with `LD_add Fr p hk nL ha hb`. Consider the case `mul a b _ _ ha hb`.

Rewrite using `[map_mul, map_mul]`. Conclude with `LD_mul Fr p hk nL ha hb`.
-/
theorem LD_phSeg (hG : GeoOK Fr p nL) {O : Type} [CommRing O] (j : ℕ) (hj : j < Fr.J) (x : SegRing O r K)
    (hx : x ∈ MvPolynomial.supported O {v : ℤ × Fin (r + K) | v.1 ∈ Fr.letters (j : ℤ)}) :
    LD Fr p hk nL (rename (castV hk) (phSeg O K p Fr (j : ℤ) x)) := by
  rw [MvPolynomial.supported_eq_adjoin_X] at hx
  induction hx using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    rw [phSeg, aeval_X, map_pow, rename_X, X_pow_eq_monomial]
    apply LD_monomial
    have := lowDiv_phVar Fr p hk nL hG j hj w.1 hw (Fin.cast (by omega) w.2) 1
    simpa [castV] using this
  | algebraMap c =>
    rw [AlgHom.commutes, algebraMap_eq, rename_C]
    exact LD_C Fr p hk nL c
  | add a b _ _ ha hb =>
    rw [map_add, map_add]
    exact LD_add Fr p hk nL ha hb
  | mul a b _ _ ha hb =>
    rw [map_mul, map_mul]
    exact LD_mul Fr p hk nL ha hb

end Formalism.MainNotions.TestSideWords
