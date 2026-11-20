import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open PowerSeries

namespace LateralTheory.E.LeafNewtonPf

def nser {A : Type 1} [CommRing A] (c : ℕ → A) : PowerSeries A :=
  -(X * derivative A (mk c)) * (mk c).invOfUnit 1

/- English proof (translation)
Rewrite using `[← h, mul_assoc, mul_invOfUnit f 1 (by simp [hf]), mul_one]`.
-/
lemma uniq {A : Type 1} [CommRing A] {f g s : PowerSeries A} (hf : constantCoeff f = 1) (h : s * f = g) :
    g * f.invOfUnit 1 = s := by
  rw [← h, mul_assoc, mul_invOfUnit f 1 (by simp [hf]), mul_one]

/- English proof (translation)
The claim follows from `uniq h0 h`.
-/
lemma nser_eq {A : Type 1} [CommRing A] (c : ℕ → A) {s : PowerSeries A} (h0 : constantCoeff (mk c) = 1)
    (h : s * mk c = -(X * derivative A (mk c))) : nser c = s := uniq h0 h

/- English proof (translation)
Unfold `nser`. Rewrite using `[mul_assoc, invOfUnit_mul (mk c) 1 (by simp [h0]), mul_one]`.
-/
lemma nser_spec {A : Type 1} [CommRing A] (c : ℕ → A) (h0 : c 0 = 1) :
    nser c * mk c = -(X * derivative A (mk c)) := by
  unfold nser
  rw [mul_assoc, invOfUnit_mul (mk c) 1 (by simp [h0]), mul_one]

/- English proof (translation)
Use extensionality with `n`. Simplify using `[coeff_derivative, coeff_map, map_mul, map_natCast]`.
-/
lemma map_deriv {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (f : PowerSeries A) :
    map φ (derivative A f) = derivative B (map φ f) := by
  ext n
  simp [coeff_derivative, coeff_map, map_mul, map_natCast]

/- English proof (translation)
Establish `hm : map φ (mk c) = mk (fun j => φ (c j))` using `by ext n; simp [coeff_map]`. Establish `key : nser (fun j => φ (c j)) = map φ (nser c)`. Apply `nser_eq _ (by simp [h0])` to reduce the goal to its premises. Use `congrArg (map φ) (nser_spec c h0)` as an intermediate fact. Rewrite `this` using `[map_mul, hm, map_neg, map_mul, map_X, map_deriv, hm]`.

Conclude with `this`. Use `show φ (coeff k (nser c)) = coeff k (nser (fun j => φ (c j)))`. Rewrite using `[key, coeff_map]`.
-/
lemma part1 {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A) (h0 : c 0 = 1) (k : ℕ) :
    φ (LateralTheory.E.D2.newton c k) = LateralTheory.E.D2.newton (fun j => φ (c j)) k := by
  have hm : map φ (mk c) = mk (fun j => φ (c j)) := by ext n; simp [coeff_map]
  have key : nser (fun j => φ (c j)) = map φ (nser c) := by
    apply nser_eq _ (by simp [h0])
    have := congrArg (map φ) (nser_spec c h0)
    rw [map_mul, hm, map_neg, map_mul, map_X, map_deriv, hm] at this
    exact this
  show φ (coeff k (nser c)) = coeff k (nser (fun j => φ (c j)))
  rw [key, coeff_map]

/- English proof (translation)
Establish `hm : mk e = mk c * mk d` using `by ext n; rw [coeff_mk, he, coeff_mul]; simp [coeff_mk]`. Establish `he0 : e 0 = 1` using `by rw [he]; simp [hc, hd]`. Establish `key : nser e = nser c + nser d`. Apply `nser_eq _ (by simp [he0])` to reduce the goal to its premises. Rewrite using `[hm, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`.

Establish `h1` using `nser_spec c hc`. Establish `h2` using `nser_spec d hd`. Take the linear combination `(mk d) * h1 + (mk c) * h2`. Use `show coeff k (nser e) = coeff k (nser c) + coeff k (nser d)`. Rewrite using `[key, map_add]`.
-/
lemma part2 {A : Type 1} [CommRing A] (c d e : ℕ → A) (hc : c 0 = 1) (hd : d 0 = 1)
    (he : ∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) (k : ℕ) :
    LateralTheory.E.D2.newton e k = LateralTheory.E.D2.newton c k + LateralTheory.E.D2.newton d k := by
  have hm : mk e = mk c * mk d := by ext n; rw [coeff_mk, he, coeff_mul]; simp [coeff_mk]
  have he0 : e 0 = 1 := by rw [he]; simp [hc, hd]
  have key : nser e = nser c + nser d := by
    apply nser_eq _ (by simp [he0])
    rw [hm, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := nser_spec c hc
    have h2 := nser_spec d hd
    linear_combination (mk d) * h1 + (mk c) * h2
  show coeff k (nser e) = coeff k (nser c) + coeff k (nser d)
  rw [key, map_add]

/- English proof (translation)
Use extensionality with `n`. Break down `n with _ | n` into its components or cases. Simplify using `[mul_sub]`. Rewrite using `[mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C x), coeff_succ_mul_X, coeff_C_mul]`. Simplify using `[pow_succ, mul_comm]`.
-/
lemma geom {A : Type 1} [CommRing A] (x : A) : mk (fun k => x ^ k) * (1 - C x * X) = 1 := by
  ext n
  rcases n with _ | n
  · simp [mul_sub]
  · rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C x), coeff_succ_mul_X, coeff_C_mul]
    simp [pow_succ, mul_comm]

/- English proof (translation)
Establish `hm : mk c = 1 - C x * X`. Use extensionality with `n`. Break down `n with _ | _ | n` into its components or cases. Simplify using `[h0]`. Simplify using `[h1]`.

Rewrite using `[coeff_mk, h2 _ (by omega)]`. Simplify using `[coeff_one]`. Establish `key : nser c = C x * X * mk (fun k => x ^ k)`. Apply `nser_eq _ (by simp [h0])` to reduce the goal to its premises. Rewrite using `[mul_assoc, hm, geom, mul_one]`.

Simplify using `[map_sub, mul_comm]`. Use `show coeff k (nser c) = x ^ k`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[key, mul_comm (C x) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_mk, pow_succ, mul_comm]`.
-/
lemma part3 {A : Type 1} [CommRing A] (c : ℕ → A) (x : A) (h0 : c 0 = 1) (h1 : c 1 = -x)
    (h2 : ∀ j, 1 < j → c j = 0) (k : ℕ) (hk : 0 < k) : LateralTheory.E.D2.newton c k = x ^ k := by
  have hm : mk c = 1 - C x * X := by
    ext n
    rcases n with _ | _ | n
    · simp [h0]
    · simp [h1]
    · rw [coeff_mk, h2 _ (by omega)]
      simp [coeff_one]
  have key : nser c = C x * X * mk (fun k => x ^ k) := by
    apply nser_eq _ (by simp [h0])
    rw [mul_assoc, hm, geom, mul_one]
    simp [map_sub, mul_comm]
  show coeff k (nser c) = x ^ k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [key, mul_comm (C x) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_mk, pow_succ, mul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ φ c h0 k => part1 φ c h0 k, fun _ _ c d e hc hd he k => part2 c d e hc hd he k, fun _ _ c x h0 h1 h2 k hk => part3 c x h0 h1 h2 k hk⟩`.
-/
theorem LeafNewton_of : LateralTheory.E.D2.LeafNewton :=
  ⟨fun _ _ _ _ φ c h0 k => part1 φ c h0 k,
   fun _ _ c d e hc hd he k => part2 c d e hc hd he k,
   fun _ _ c x h0 h1 h2 k hk => part3 c x h0 h1 h2 k hk⟩

end LateralTheory.E.LeafNewtonPf
