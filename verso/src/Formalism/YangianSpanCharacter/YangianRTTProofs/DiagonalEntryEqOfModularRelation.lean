import Formalism.YangianSpanCharacter.StatementY

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y

section Alg

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem comm_of_inv {a b bi : A} (h1 : b * bi = 1) (h2 : bi * b = 1) (hab : a * b = b * a) :
    a * bi = bi * a := by
  calc a * bi = (bi * b) * (a * bi) := by rw [h2, one_mul]
    _ = bi * (a * b) * bi := by rw [hab]; simp only [mul_assoc]
    _ = bi * a := by simp only [mul_assoc]; rw [h1, mul_one]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem smul_cancel {c : 𝕜} (hc : c ≠ 0) {x y : A} (h : c • x = c • y) : x = y := by
  calc x = c⁻¹ • c • x := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • c • y := by rw [h]
    _ = y := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem left_cancel {b bi x y : A} (h2 : bi * b = 1) (h : b * x = b * y) : x = y := by
  calc x = bi * b * x := by rw [h2, one_mul]
    _ = bi * (b * y) := by rw [mul_assoc, h]
    _ = y := by rw [← mul_assoc, h2, one_mul]

/- English proof (translation)
Rewrite using `[mul_add]`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem from_comm {a l e : A} (h : a * l - l * a = -(a * e)) : l * a = a * (l + e) := by
  rw [mul_add]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/- English proof (translation)
Rewrite using `[mul_sub]`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem from_comm' {b m e : A} (h : b * m - m * b = b * e) : m * b = b * (m - e) := by
  rw [mul_sub]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/- English proof (translation)
Establish `hc' : a * bi = bi * a` using `comm_of_inv hb1 hb2 hab`. Establish `hc'' : a * (bi * y) = bi * (a * y)` using `by rw [← mul_assoc, hc', mul_assoc]`. Establish `hay : a * y - y * a = c⁻¹ • (a * y - b * x)`. Rewrite using `[← hR, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Establish `hbx : bi * (b * x) = x` using `by rw [← mul_assoc, hb2, one_mul]`.

Establish `hax : a * (ai * x) = x` using `by rw [← mul_assoc, ha1, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc'', mul_sub, mul_assoc]`. Use `_ = c⁻¹ • (bi * (a * y) - x) := by`. Rewrite using `[hay, mul_smul_comm, mul_sub, hbx]`.

Use `_ = -(a * (c⁻¹ • (ai * x - bi * y))) := by`. Rewrite using `[mul_smul_comm, mul_sub, hax, hc'', ← smul_neg, neg_sub]`.
-/
theorem conj_commutator_of_scaled_relation {a b ai bi x y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR : c • (a * y - y * a) = a * y - b * x) (hb1 : b * bi = 1) (hb2 : bi * b = 1)
    (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * y) - bi * y * a = -(a * (c⁻¹ • (ai * x - bi * y))) := by
  have hc' : a * bi = bi * a := comm_of_inv hb1 hb2 hab
  have hc'' : a * (bi * y) = bi * (a * y) := by rw [← mul_assoc, hc', mul_assoc]
  have hay : a * y - y * a = c⁻¹ • (a * y - b * x) := by
    rw [← hR, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hbx : bi * (b * x) = x := by rw [← mul_assoc, hb2, one_mul]
  have hax : a * (ai * x) = x := by rw [← mul_assoc, ha1, one_mul]
  calc a * (bi * y) - bi * y * a = bi * (a * y - y * a) := by
        rw [hc'', mul_sub, mul_assoc]
    _ = c⁻¹ • (bi * (a * y) - x) := by
        rw [hay, mul_smul_comm, mul_sub, hbx]
    _ = -(a * (c⁻¹ • (ai * x - bi * y))) := by
        rw [mul_smul_comm, mul_sub, hax, hc'', ← smul_neg, neg_sub]

/- English proof (translation)
Establish `hc' : a * bi = bi * a` using `comm_of_inv hb1 hb2 hab`. Establish `hc'' : a * (bi * Y) = bi * (a * Y)` using `by rw [← mul_assoc, hc', mul_assoc]`. Establish `hD : a * Y - Y * a = b * X - X * b`. Apply `smul_cancel hc` to reduce the goal to its premises. Rewrite using `[hR1, ← neg_sub (Y * a) (X * b), ← hR2, neg_smul, neg_neg]`.

Establish `hXb : X * b = b * X - (a * Y - Y * a)` using `by rw [hD]; abel`. Establish `hbX : bi * (b * X) = X` using `by rw [← mul_assoc, hb2, one_mul]`. Establish `haX : a * (ai * X) = X` using `by rw [← mul_assoc, ha1, one_mul]`. Establish `hL : a * (bi * Y) - bi * Y * a = bi * (a * Y - Y * a)`. Rewrite using `[hc'', mul_sub, mul_assoc]`.

Apply `smul_cancel hc` to reduce the goal to its premises. Rewrite using `[hL, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul, ← mul_smul_comm, hR1]`. Rewrite using `[hXb]`. Simplify using `only [mul_sub]`. Rewrite using `[hbX, haX, hc'']`.

Normalize the expressions using the abelian group laws.
-/
theorem y1'_alg {a b ai bi X Y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR1 : c • (a * Y - Y * a) = X * b - Y * a) (hR2 : (-c) • (b * X - X * b) = Y * a - X * b)
    (hb1 : b * bi = 1) (hb2 : bi * b = 1) (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * Y) - bi * Y * a = a * (c⁻¹ • (ai * X - bi * Y)) := by
  have hc' : a * bi = bi * a := comm_of_inv hb1 hb2 hab
  have hc'' : a * (bi * Y) = bi * (a * Y) := by rw [← mul_assoc, hc', mul_assoc]
  have hD : a * Y - Y * a = b * X - X * b := by
    apply smul_cancel hc
    rw [hR1, ← neg_sub (Y * a) (X * b), ← hR2, neg_smul, neg_neg]
  have hXb : X * b = b * X - (a * Y - Y * a) := by rw [hD]; abel
  have hbX : bi * (b * X) = X := by rw [← mul_assoc, hb2, one_mul]
  have haX : a * (ai * X) = X := by rw [← mul_assoc, ha1, one_mul]
  have hL : a * (bi * Y) - bi * Y * a = bi * (a * Y - Y * a) := by
    rw [hc'', mul_sub, mul_assoc]
  apply smul_cancel hc
  rw [hL, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul, ← mul_smul_comm, hR1]
  rw [hXb]
  simp only [mul_sub]
  rw [hbX, haX, hc'']
  abel

/- English proof (translation)
Establish `e : a * (b * ((lu + η) * lv)) = a * (b * ((lv + η) * lu))`. Combine the equalities or inequalities in the displayed calculation. Establish `e3` using `left_cancel hb2 (left_cancel ha2 e)`. Rewrite `e3` using `[add_mul, add_mul]`. Rewrite using `[mul_sub, ← sub_eq_zero]`.

Establish `e4 : lu * lv - lv * lu - (η * lu - η * lv) = (lu * lv + η * lv) - (lv * lu + η * lu)`. Normalize the expressions using the abelian group laws. Rewrite using `[e4, e3, sub_self]`.
-/
theorem commutator_eq_of_shift_relations {a b ai bi lu lv η : A} (hxy : a * lu * (b * lv) = b * lv * (a * lu))
    (h1 : lv * a = a * (lv + η)) (h2 : lu * b = b * (lu + η)) (hab : a * b = b * a)
    (ha2 : ai * a = 1) (hb2 : bi * b = 1) : lu * lv - lv * lu = η * (lu - lv) := by
  have e : a * (b * ((lu + η) * lv)) = a * (b * ((lv + η) * lu)) := by
    calc a * (b * ((lu + η) * lv)) = a * (lu * b) * lv := by rw [h2]; simp only [mul_assoc]
      _ = a * lu * (b * lv) := by simp only [mul_assoc]
      _ = b * lv * (a * lu) := hxy
      _ = b * (lv * a) * lu := by simp only [mul_assoc]
      _ = b * (a * ((lv + η) * lu)) := by rw [h1]; simp only [mul_assoc]
      _ = a * (b * ((lv + η) * lu)) := by rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have e3 := left_cancel hb2 (left_cancel ha2 e)
  rw [add_mul, add_mul] at e3
  rw [mul_sub, ← sub_eq_zero]
  have e4 : lu * lv - lv * lu - (η * lu - η * lv) = (lu * lv + η * lv) - (lv * lu + η * lu) := by
    abel
  rw [e4, e3, sub_self]

/- English proof (translation)
Establish `hτz : τ * z = x10 * τ'` using `neg_add_eq_zero.mp e2`. Establish `hz : z = τi * (x10 * τ')` using `by rw [← hτz, ← mul_assoc, h2, one_mul]`. Establish `h4 : (x00 - x01 * τi * x10) * τ' = k • (1 : A)`. Rewrite using `[← e1, hz, sub_mul]`. Simplify using `only [mul_assoc]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc _ τ' τ'i, h3, mul_one]`. Use `_ = k • τ'i := by rw [h4, smul_mul_assoc, one_mul]`.
-/
theorem qdet_alg {x00 x01 x10 τ τi τ' τ'i z : A} {k : 𝕜}
    (e1 : -(x01 * z) + x00 * τ' = k • 1) (e2 : -(τ * z) + x10 * τ' = 0)
    (h2 : τi * τ = 1) (h3 : τ' * τ'i = 1) : x00 - x01 * τi * x10 = k • τ'i := by
  have hτz : τ * z = x10 * τ' := neg_add_eq_zero.mp e2
  have hz : z = τi * (x10 * τ') := by rw [← hτz, ← mul_assoc, h2, one_mul]
  have h4 : (x00 - x01 * τi * x10) * τ' = k • (1 : A) := by
    rw [← e1, hz, sub_mul]
    simp only [mul_assoc]
    abel
  calc x00 - x01 * τi * x10 = (x00 - x01 * τi * x10) * τ' * τ'i := by
        rw [mul_assoc _ τ' τ'i, h3, mul_one]
    _ = k • τ'i := by rw [h4, smul_mul_assoc, one_mul]

/- English proof (translation)
Establish `hA : a * mu * (b * lv) = a * (b * ((mu - μ) * lv))`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : b * lv * (a * mu) = a * (b * ((lv + η) * mu))`. Combine the equalities or inequalities in the displayed calculation. Establish `hC : b * (a * (mu * lu + hu)) = a * (b * (mu * lu + hu))`.

Rewrite using `[← mul_assoc b a, ← hab, mul_assoc a b]`. Establish `e : a * (b * (c • ((mu - μ) * lv - (lv + η) * mu))) = a * (b * (mv * lv + hv - (mu * lu + hu)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA, hB, ← mul_sub, ← mul_sub, mul_smul_comm, mul_smul_comm]`. Use `_ = a * (b * (mv * lv + hv - (mu * lu + hu))) := by`.

Rewrite using `[hR, hC, ← mul_sub, ← mul_sub]`. Establish `e2` using `left_cancel hb2 (left_cancel ha2 e)`. Establish `hμ' : c • (μ * lv) = (mu - mv) * lv` using `by rw [← smul_mul_assoc, hμ]`. Establish `hη' : c • (η * mu) = (lu - lv) * mu` using `by rw [← smul_mul_assoc, hη]`. Rewrite `e2` using `[sub_mul, add_mul, smul_sub, smul_sub, smul_add, hμ', hη']`.

Establish `key : c • (mu * lv) - c • (lv * mu) = mv * lv + hv - (mu * lu + hu) + (mu - mv) * lv + (lu - lv) * mu`. Rewrite using `[← e2]`. Normalize the expressions using the abelian group laws. Rewrite using `[sub_smul, one_smul, smul_sub, key, sub_mul, sub_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem key_alg {a b ai bi mu lu mv lv hu hv η μ : A} {c : 𝕜}
    (ha2 : ai * a = 1) (hb2 : bi * b = 1) (hab : a * b = b * a)
    (h1 : lv * a = a * (lv + η)) (h2 : mu * b = b * (mu - μ)) (hη : c • η = lu - lv)
    (hμ : c • μ = mu - mv)
    (hR : c • (a * mu * (b * lv) - b * lv * (a * mu)) =
      a * (b * (mv * lv + hv)) - b * (a * (mu * lu + hu))) :
    (c - 1) • (mu * lv - lv * mu) = hv - hu - (mu * lu - lu * mu) := by
  have hA : a * mu * (b * lv) = a * (b * ((mu - μ) * lv)) := by
    calc a * mu * (b * lv) = a * (mu * b) * lv := by simp only [mul_assoc]
      _ = a * (b * ((mu - μ) * lv)) := by rw [h2]; simp only [mul_assoc]
  have hB : b * lv * (a * mu) = a * (b * ((lv + η) * mu)) := by
    calc b * lv * (a * mu) = b * (lv * a) * mu := by simp only [mul_assoc]
      _ = b * (a * ((lv + η) * mu)) := by rw [h1]; simp only [mul_assoc]
      _ = a * (b * ((lv + η) * mu)) := by rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have hC : b * (a * (mu * lu + hu)) = a * (b * (mu * lu + hu)) := by
    rw [← mul_assoc b a, ← hab, mul_assoc a b]
  have e : a * (b * (c • ((mu - μ) * lv - (lv + η) * mu))) =
      a * (b * (mv * lv + hv - (mu * lu + hu))) := by
    calc a * (b * (c • ((mu - μ) * lv - (lv + η) * mu)))
        = c • (a * mu * (b * lv) - b * lv * (a * mu)) := by
          rw [hA, hB, ← mul_sub, ← mul_sub, mul_smul_comm, mul_smul_comm]
      _ = a * (b * (mv * lv + hv - (mu * lu + hu))) := by
          rw [hR, hC, ← mul_sub, ← mul_sub]
  have e2 := left_cancel hb2 (left_cancel ha2 e)
  have hμ' : c • (μ * lv) = (mu - mv) * lv := by rw [← smul_mul_assoc, hμ]
  have hη' : c • (η * mu) = (lu - lv) * mu := by rw [← smul_mul_assoc, hη]
  rw [sub_mul, add_mul, smul_sub, smul_sub, smul_add, hμ', hη'] at e2
  have key : c • (mu * lv) - c • (lv * mu) =
      mv * lv + hv - (mu * lu + hu) + (mu - mv) * lv + (lu - lv) * mu := by
    rw [← e2]
    abel
  rw [sub_smul, one_smul, smul_sub, key, sub_mul, sub_mul]
  abel

end Alg

section Mod

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}

/- English proof (translation)
Simplify using `only [lf, eta]`. Conclude with `conj_commutator_of_scaled_relation (sub_ne_zero.mpr huv) (H.1 u v 1 1 1 0) (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2 (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq`.
-/
theorem commutator_of_modular_relation (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v) := by
  simp only [lf, eta]
  exact conj_commutator_of_scaled_relation (sub_ne_zero.mpr huv) (H.1 u v 1 1 1 0) (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2
    (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq

/- English proof (translation)
Simplify using `only [mf, mu]`. Conclude with `y1'_alg (sub_ne_zero.mpr huv) (H.1 u v 1 1 0 1) (by rw [neg_sub]; exact H.1 v u 1 1 0 1) (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2 (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq`.
-/
theorem y1'_mod (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v := by
  simp only [mf, mu]
  exact y1'_alg (sub_ne_zero.mpr huv) (H.1 u v 1 1 0 1)
    (by rw [neg_sub]; exact H.1 v u 1 1 0 1)
    (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2 (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq

/- English proof (translation)
Simplify using `only [eta]`. Rewrite using `[← neg_sub u v, inv_neg, neg_smul, ← smul_neg, neg_sub]`.
-/
theorem eta_symm (u v : 𝕜) : eta t τinv v u = eta t τinv u v := by
  simp only [eta]
  rw [← neg_sub u v, inv_neg, neg_smul, ← smul_neg, neg_sub]

/- English proof (translation)
Simplify using `only [mu]`. Rewrite using `[← neg_sub u v, inv_neg, neg_smul, ← smul_neg, neg_sub]`.
-/
theorem mu_symm (u v : 𝕜) : mu t τinv v u = mu t τinv u v := by
  simp only [mu]
  rw [← neg_sub u v, inv_neg, neg_smul, ← smul_neg, neg_sub]

/- English proof (translation)
Establish `hinvu` using `H.2.2.2.1 u hu`. Establish `hinvv` using `H.2.2.2.1 v hv`. Establish `hal : t u 1 1 * lf t τinv u = t u 1 0`. Simplify using `only [lf]`. Rewrite using `[← mul_assoc, hinvu.1, one_mul]`.

Establish `hbl : t v 1 1 * lf t τinv v = t v 1 0`. Simplify using `only [lf]`. Rewrite using `[← mul_assoc, hinvv.1, one_mul]`. Establish `hxy : t u 1 1 * lf t τinv u * (t v 1 1 * lf t τinv v) = t v 1 1 * lf t τinv v * (t u 1 1 * lf t τinv u)`. Rewrite using `[hal, hbl]`.

Conclude with `(H.2.2.2.2.2 u v).eq`. Establish `h1 : lf t τinv v * t u 1 1 = t u 1 1 * (lf t τinv v + eta t τinv u v)` using `from_comm (commutator_of_modular_relation H hu hv huv)`. Establish `h2 : lf t τinv u * t v 1 1 = t v 1 1 * (lf t τinv u + eta t τinv u v)`. Establish `h` using `commutator_of_modular_relation H hv hu (Ne.symm huv)`. Rewrite `h` using `[eta_symm]`.

Conclude with `from_comm h`. Conclude with `commutator_eq_of_shift_relations hxy h1 h2 (H.2.2.2.2.1 u v).eq hinvu.2 hinvv.2`.
-/
theorem commutator_eq_eta_mul_sub (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    lf t τinv u * lf t τinv v - lf t τinv v * lf t τinv u =
      eta t τinv u v * (lf t τinv u - lf t τinv v) := by
  have hinvu := H.2.2.2.1 u hu
  have hinvv := H.2.2.2.1 v hv
  have hal : t u 1 1 * lf t τinv u = t u 1 0 := by
    simp only [lf]; rw [← mul_assoc, hinvu.1, one_mul]
  have hbl : t v 1 1 * lf t τinv v = t v 1 0 := by
    simp only [lf]; rw [← mul_assoc, hinvv.1, one_mul]
  have hxy : t u 1 1 * lf t τinv u * (t v 1 1 * lf t τinv v) =
      t v 1 1 * lf t τinv v * (t u 1 1 * lf t τinv u) := by
    rw [hal, hbl]; exact (H.2.2.2.2.2 u v).eq
  have h1 : lf t τinv v * t u 1 1 = t u 1 1 * (lf t τinv v + eta t τinv u v) :=
    from_comm (commutator_of_modular_relation H hu hv huv)
  have h2 : lf t τinv u * t v 1 1 = t v 1 1 * (lf t τinv u + eta t τinv u v) := by
    have h := commutator_of_modular_relation H hv hu (Ne.symm huv)
    rw [eta_symm] at h
    exact from_comm h
  exact commutator_eq_of_shift_relations hxy h1 h2 (H.2.2.2.2.1 u v).eq hinvu.2 hinvv.2

/- English proof (translation)
Establish `hm` using `H.2.2.1 Y`. Establish `e1 : -(t Y 0 1 * t (Y + 1) 1 0) + t Y 0 0 * t (Y + 1) 1 1 = q Y • (1 : A)`. Establish `h01` using `congrFun (congrFun hm 0) 1`. Simplify `h01` using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]`. Establish `e2 : -(t Y 1 1 * t (Y + 1) 1 0) + t Y 1 0 * t (Y + 1) 1 1 = 0`.

Establish `h11` using `congrFun (congrFun hm 1) 1`. Simplify `h11` using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]`. Conclude with `qdet_alg e1 e2 (H.2.2.2.1 Y hY).2 (H.2.2.2.1 (Y + 1) hY1).1`.
-/
theorem qdet_mod (H : ModHyp t τinv q S) {Y : 𝕜} (hY : Y ∈ S) (hY1 : Y + 1 ∈ S) :
    t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0 = q Y • τinv (Y + 1) := by
  have hm := H.2.2.1 Y
  have e1 : -(t Y 0 1 * t (Y + 1) 1 0) + t Y 0 0 * t (Y + 1) 1 1 = q Y • (1 : A) := by
    have h01 := congrFun (congrFun hm 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h01
  have e2 : -(t Y 1 1 * t (Y + 1) 1 0) + t Y 1 0 * t (Y + 1) 1 1 = 0 := by
    have h11 := congrFun (congrFun hm 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h11
  exact qdet_alg e1 e2 (H.2.2.2.1 Y hY).2 (H.2.2.2.1 (Y + 1) hY1).1

/- English proof (translation)
Establish `hq` using `qdet_mod H hu hu1`. Establish `hinv` using `(H.2.2.2.1 u hu).1`. Establish `hx : t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0)) = t u 0 1 * τinv u * t u 1 0`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mf, lf, hf]`.

Rewrite using `[mul_add, mul_smul_comm, ← mul_assoc (t u 1 1) (τinv u) (τinv (u + 1)), hinv, one_mul, hx, ← hq]`. Normalize the expressions using the abelian group laws.
-/
theorem diagonal_entry_eq_of_modular_relation (H : ModHyp t τinv q S) {u : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) :
    t u 0 0 = t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u) := by
  have hq := qdet_mod H hu hu1
  have hinv := (H.2.2.2.1 u hu).1
  have hx : t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0)) = t u 0 1 * τinv u * t u 1 0 := by
    calc t u 1 1 * (τinv u * t u 0 1 * (τinv u * t u 1 0))
        = t u 1 1 * τinv u * t u 0 1 * (τinv u * t u 1 0) := by simp only [mul_assoc]
      _ = t u 0 1 * τinv u * t u 1 0 := by rw [hinv, one_mul, mul_assoc]
  simp only [mf, lf, hf]
  rw [mul_add, mul_smul_comm, ← mul_assoc (t u 1 1) (τinv u) (τinv (u + 1)), hinv, one_mul, hx,
    ← hq]
  abel

/- English proof (translation)
Establish `huv' : u - v ≠ 0` using `sub_ne_zero.mpr huv`. Establish `hau : t u 1 1 * mf t τinv u = t u 0 1`. Simplify using `only [mf]`. Rewrite using `[← mul_assoc, (H.2.2.2.1 u hu).1, one_mul]`. Establish `hbv : t v 1 1 * lf t τinv v = t v 1 0`.

Simplify using `only [lf]`. Rewrite using `[← mul_assoc, (H.2.2.2.1 v hv).1, one_mul]`. Establish `hR : (u - v) • (t u 1 1 * mf t τinv u * (t v 1 1 * lf t τinv v) - t v 1 1 * lf t τinv v * (t u 1 1 * mf t τinv u)) = t u 1 1 * (t v 1 1 * (mf t τinv v * lf t τinv v + hf τinv q v)) - t v 1 1 * (t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u))`. Rewrite using `[hau, hbv, ← diagonal_entry_eq_of_modular_relation H hv hv1, ← diagonal_entry_eq_of_modular_relation H hu hu1]`. Conclude with `H.1 u v 0 1 1 0`.

Establish `h1` using `from_comm (commutator_of_modular_relation H hu hv huv)`. Establish `h2 : mf t τinv u * t v 1 1 = t v 1 1 * (mf t τinv u - mu t τinv u v)`. Establish `h` using `y1'_mod H hv hu (Ne.symm huv)`. Rewrite `h` using `[mu_symm]`. Conclude with `from_comm' h`.

Establish `hη : (u - v) • eta t τinv u v = lf t τinv u - lf t τinv v`. Simplify using `only [eta]`. Rewrite using `[smul_smul, mul_inv_cancel₀ huv', one_smul]`. Establish `hμ : (u - v) • mu t τinv u v = mf t τinv u - mf t τinv v`. Simplify using `only [mu]`.

Rewrite using `[smul_smul, mul_inv_cancel₀ huv', one_smul]`. Conclude with `key_alg (H.2.2.2.1 u hu).2 (H.2.2.2.1 v hv).2 (H.2.2.2.2.1 u v).eq h1 h2 hη hμ hR`.
-/
theorem key_mod (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) (hv : v ∈ S)
    (hv1 : v + 1 ∈ S) (huv : u ≠ v) :
    (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
      hf τinv q v - hf τinv q u - (mf t τinv u * lf t τinv u - lf t τinv u * mf t τinv u) := by
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hau : t u 1 1 * mf t τinv u = t u 0 1 := by
    simp only [mf]; rw [← mul_assoc, (H.2.2.2.1 u hu).1, one_mul]
  have hbv : t v 1 1 * lf t τinv v = t v 1 0 := by
    simp only [lf]; rw [← mul_assoc, (H.2.2.2.1 v hv).1, one_mul]
  have hR : (u - v) • (t u 1 1 * mf t τinv u * (t v 1 1 * lf t τinv v) -
      t v 1 1 * lf t τinv v * (t u 1 1 * mf t τinv u)) =
      t u 1 1 * (t v 1 1 * (mf t τinv v * lf t τinv v + hf τinv q v)) -
        t v 1 1 * (t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u)) := by
    rw [hau, hbv, ← diagonal_entry_eq_of_modular_relation H hv hv1, ← diagonal_entry_eq_of_modular_relation H hu hu1]
    exact H.1 u v 0 1 1 0
  have h1 := from_comm (commutator_of_modular_relation H hu hv huv)
  have h2 : mf t τinv u * t v 1 1 = t v 1 1 * (mf t τinv u - mu t τinv u v) := by
    have h := y1'_mod H hv hu (Ne.symm huv)
    rw [mu_symm] at h
    exact from_comm' h
  have hη : (u - v) • eta t τinv u v = lf t τinv u - lf t τinv v := by
    simp only [eta]; rw [smul_smul, mul_inv_cancel₀ huv', one_smul]
  have hμ : (u - v) • mu t τinv u v = mf t τinv u - mf t τinv v := by
    simp only [mu]; rw [smul_smul, mul_inv_cancel₀ huv', one_smul]
  exact key_alg (H.2.2.2.1 u hu).2 (H.2.2.2.1 v hv).2 (H.2.2.2.2.1 u v).eq h1 h2 hη hμ hR

end Mod

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S H u v hu hv huv`. Conclude with `commutator_of_modular_relation H hu hv huv`.
-/
theorem wedgeMapInLieAlgebra : Formalism.YangianSpanCharacter.Y.Y1 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact commutator_of_modular_relation H hu hv huv

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S H u v hu hv huv`. Conclude with `y1'_mod H hu hv huv`.
-/
theorem yangian_relation_first_alt_holds : Formalism.YangianSpanCharacter.Y.Y1' := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact y1'_mod H hu hv huv

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S H u v hu hv huv`. Conclude with `commutator_eq_eta_mul_sub H hu hv huv`.
-/
theorem shift_commutator_relation_holds : Formalism.YangianSpanCharacter.Y.Y2 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hv huv
  exact commutator_eq_eta_mul_sub H hu hv huv

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S H u v hu hu1 hum hv hv1 huv`. Rewrite using `[key_mod H hu hu1 hv hv1 huv]`. Establish `hinvu` using `H.2.2.2.1 u hu`. Establish `hinvm` using `H.2.2.2.1 (u - 1) hum`. Establish `hml : mf t τinv u * lf t τinv u = τinv u * t u 0 0 - hf τinv q u`.

Rewrite using `[diagonal_entry_eq_of_modular_relation H hu hu1, ← mul_assoc, hinvu.2, one_mul]`. Normalize the expressions using the abelian group laws. Establish `qd : t u 0 0 - t u 1 0 * τinv u * t u 0 1 = q (u - 1) • τinv (u - 1)`. Establish `hm` using `H.2.1 (u - 1)`. Rewrite `hm` using `[sub_add_cancel]`.

Establish `e1 : -(t u 1 0 * t (u - 1) 0 1) + t u 0 0 * t (u - 1) 1 1 = q (u - 1) • (1 : A)`. Establish `h01` using `congrFun (congrFun hm 0) 1`. Simplify `h01` using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]`. Establish `e2 : -(t u 1 1 * t (u - 1) 0 1) + t u 0 1 * t (u - 1) 1 1 = 0`. Establish `h11` using `congrFun (congrFun hm 1) 1`.

Simplify `h11` using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J]`. Conclude with `qdet_alg e1 e2 hinvu.2 hinvm.1`. Establish `hc1 : t u 1 1 * τinv (u - 1) = τinv (u - 1) * t u 1 1` using `comm_of_inv hinvm.1 hinvm.2 (H.2.2.2.2.1 u (u - 1)).eq`. Establish `hc2 : τinv (u - 1) * τinv u = τinv u * τinv (u - 1)` using `comm_of_inv hinvu.1 hinvu.2 hc1.symm`. Establish `hfm : hf τinv q (u - 1) = q (u - 1) • (τinv u * τinv (u - 1))`.

Simplify using `only [hf]`. Rewrite using `[sub_add_cancel, hc2]`. Establish `hlm : lf t τinv u * mf t τinv u = τinv u * t u 0 0 - hf τinv q (u - 1)`. Rewrite using `[hfm, ← mul_smul_comm, ← qd]`. Simplify using `only [lf, mf, mul_sub, mul_assoc]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hml, hlm]`. Normalize the expressions using the abelian group laws.
-/
theorem yangian_relation_three_holds : Formalism.YangianSpanCharacter.Y.Y3 := by
  intro 𝕜 A _ _ _ t τinv q S H u v hu hu1 hum hv hv1 huv
  rw [key_mod H hu hu1 hv hv1 huv]
  have hinvu := H.2.2.2.1 u hu
  have hinvm := H.2.2.2.1 (u - 1) hum
  have hml : mf t τinv u * lf t τinv u = τinv u * t u 0 0 - hf τinv q u := by
    rw [diagonal_entry_eq_of_modular_relation H hu hu1, ← mul_assoc, hinvu.2, one_mul]
    abel
  have qd : t u 0 0 - t u 1 0 * τinv u * t u 0 1 = q (u - 1) • τinv (u - 1) := by
    have hm := H.2.1 (u - 1)
    rw [sub_add_cancel] at hm
    have e1 : -(t u 1 0 * t (u - 1) 0 1) + t u 0 0 * t (u - 1) 1 1 = q (u - 1) • (1 : A) := by
      have h01 := congrFun (congrFun hm 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h01
    have e2 : -(t u 1 1 * t (u - 1) 0 1) + t u 0 1 * t (u - 1) 1 1 = 0 := by
      have h11 := congrFun (congrFun hm 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] using h11
    exact qdet_alg e1 e2 hinvu.2 hinvm.1
  have hc1 : t u 1 1 * τinv (u - 1) = τinv (u - 1) * t u 1 1 :=
    comm_of_inv hinvm.1 hinvm.2 (H.2.2.2.2.1 u (u - 1)).eq
  have hc2 : τinv (u - 1) * τinv u = τinv u * τinv (u - 1) :=
    comm_of_inv hinvu.1 hinvu.2 hc1.symm
  have hfm : hf τinv q (u - 1) = q (u - 1) • (τinv u * τinv (u - 1)) := by
    simp only [hf]; rw [sub_add_cancel, hc2]
  have hlm : lf t τinv u * mf t τinv u = τinv u * t u 0 0 - hf τinv q (u - 1) := by
    rw [hfm, ← mul_smul_comm, ← qd]
    simp only [lf, mf, mul_sub, mul_assoc]
    abel
  rw [hml, hlm]
  abel

end Formalism.YangianSpanCharacter.P
