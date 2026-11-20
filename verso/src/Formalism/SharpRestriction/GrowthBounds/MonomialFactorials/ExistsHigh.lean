import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LowerBoundInitialMultiplicity

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

/- English proof (translation)
Take `⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ lo - ρ = P * q + r` from `⟨(lo - ρ) / P, (lo - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩`. Break down `Nat.eq_zero_or_pos r with h0 | hpos` into its components or cases. Use `⟨lo, le_rfl, by omega, hρ, ⟨q, by omega⟩⟩` and prove the remaining obligations. Use `⟨lo + (P - r), by omega, by omega, by omega, ⟨q + 1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Nat.mul_add, Nat.mul_one]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_low (lo ρ P : ℕ) (hP : 0 < P) (hρ : ρ ≤ lo) :
    ∃ v, lo ≤ v ∧ v + 1 ≤ lo + P ∧ ρ ≤ v ∧ P ∣ v - ρ := by
  obtain ⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ lo - ρ = P * q + r :=
    ⟨(lo - ρ) / P, (lo - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · refine ⟨lo, le_rfl, by omega, hρ, ⟨q, by omega⟩⟩
  · refine ⟨lo + (P - r), by omega, by omega, by omega, ⟨q + 1, ?_⟩⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

/- English proof (translation)
Take `⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ hi - ρ = P * q + r` from `⟨(hi - ρ) / P, (hi - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩`. Conclude with `⟨hi - r, by omega, by omega, by omega, ⟨q, by omega⟩⟩`.
-/
theorem exists_high (hi ρ P : ℕ) (hP : 0 < P) (hρ : ρ ≤ hi) :
    ∃ v, v ≤ hi ∧ hi + 1 ≤ v + P ∧ ρ ≤ v ∧ P ∣ v - ρ := by
  obtain ⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ hi - ρ = P * q + r :=
    ⟨(hi - ρ) / P, (hi - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩
  exact ⟨hi - r, by omega, by omega, by omega, ⟨q, by omega⟩⟩

section Eps

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

/- English proof (translation)
Use `set l := uTop (X.S C0 CE1 CE2) i with hl`. Use `set P := (X.S C0 CE1 CE2).P X.p l with hP`. Use `set σ := ∑ c : Fin (X.r + 1), dl.2 l c with hσ`. Use `set N := ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ with hN`. Establish `hP1 : 1 ≤ P` using `hS.P1 l`.

Establish `hdl' : dl ∈ digSet C0 CE1 CE2 X ×ˢ digSet C0 CE1 CE2 X` using `hdl`. Establish `h2 : dl.2 ∈ digSet C0 CE1 CE2 X` using `(Finset.mem_product.1 hdl').2`. Establish `hdig : ∀ c, dl.2 l c < P` using `fun c => Finset.mem_range.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 h2 l) c)`. Establish `hsum : σ < (X.r + 1) * P`. Use `Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (X.r + 1)))) Finset.univ_nonempty (fun c _ => hdig c)` as an intermediate fact.

Simplify `this` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Establish `hσA : σ ≤ X.L.a`. Establish `hkP` using `hS.kP l`. Establish `hkb` using `hS.kb`. Establish `hsR : (σ : ℝ) < ((X.r : ℝ) + 1) * (P : ℝ)` using `by exact_mod_cast hsum`.

Establish `hP1R : (1 : ℝ) ≤ (P : ℝ)` using `by exact_mod_cast hP1`. Establish `hr0 : (0 : ℝ) ≤ (X.r : ℝ)` using `Nat.cast_nonneg _`. Establish `hb0 : (0 : ℝ) ≤ X.L.b'` using `by nlinarith`. Establish `hA0 : (0 : ℝ) ≤ (X.L.a : ℝ)` using `Nat.cast_nonneg _`. Establish `: (σ : ℝ) < (X.L.a : ℝ)` using `by nlinarith`.

Conclude with `this.le` after adjusting the coercions. Take `⟨vlo, hlo1, hlo2, hlo3, hlo4⟩` from `exists_low X.L.a σ P (by omega) hσA`. Take `⟨vhi, hhi1, hhi2, hhi3, hhi4⟩` from `exists_high N σ P (by omega) (by omega)`. Establish `hWlo : vlo ∈ Wl C0 CE1 CE2 X dl l`. Simplify using `only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]`.

Conclude with `⟨⟨hlo1, by omega⟩, hlo3, hlo4⟩`. Establish `hWhi : vhi ∈ Wl C0 CE1 CE2 X dl l`. Simplify using `only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, hhi1⟩, hhi3, hhi4⟩`. Establish `hry : x.fst.ry = dl.2`.

Establish `hx'` using `(Finset.mem_sigma.1 hx).1`. Simplify using `only [Finset.mem_filter] at hx'`. Conclude with `congrArg Prod.snd hx'.2`. Establish `hall : ∀ a' ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a'` using `fun a' ha' => (hFree dl hdl a ha a' ha') ▸ hx`. Establish `hroomL : LvlRoom C0 CE1 CE2 X dl x.snd` using `lvlRoom_of ha hry hall`.

Establish `hx1 : x.2.1 i ≤ (vlo - σ) / P` using `hroomL i vlo hWlo`. Take `⟨qlo, hqlo⟩` from `hlo4`. Take `⟨qhi, hqhi⟩` from `hhi4`. Establish `hPpos : 0 < P` using `by omega`. Establish `hdlo : (vlo - σ) / P = qlo` using `by rw [hqlo]; exact Nat.mul_div_cancel_left _ hPpos`.

Establish `hdhi : (vhi - σ) / P = qhi` using `by rw [hqhi]; exact Nat.mul_div_cancel_left _ hPpos`. Establish `hmlo : cm C0 CE1 CE2 X dl x.2 i vlo ∈ Nl C0 CE1 CE2 X dl x.2 i`. Unfold `Nl`. Conclude with `Finset.mem_image_of_mem _ hWlo`. Establish `hmhi : cm C0 CE1 CE2 X dl x.2 i vhi ∈ Nl C0 CE1 CE2 X dl x.2 i`.

Unfold `Nl`. Conclude with `Finset.mem_image_of_mem _ hWhi`. Establish `hinf : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ≤ cm C0 CE1 CE2 X dl x.2 i vlo` using `Nat.sInf_le (Finset.mem_coe.2 hmlo)`. Establish `hsup : cm C0 CE1 CE2 X dl x.2 i vhi ≤ (Nl C0 CE1 CE2 X dl x.2 i).sup id` using `Finset.le_sup (f := id) hmhi`. Establish `hclo : cm C0 CE1 CE2 X dl x.2 i vlo = qlo - x.2.1 i` using `by show (vlo - σ) / P - x.2.1 i = _; rw [hdlo]`.

Establish `hchi : cm C0 CE1 CE2 X dl x.2 i vhi = qhi - x.2.1 i` using `by show (vhi - σ) / P - x.2.1 i = _; rw [hdhi]`. Establish `hY : (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i = (Nl C0 CE1 CE2 X dl x.2 i).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) + 1` using `rfl`. Rewrite `hx1` using `[hdlo]`. Establish `hvv : vlo < vhi` using `by omega`. Establish `hqq : qlo ≤ qhi`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: P * qhi < P * qlo` using `Nat.mul_lt_mul_of_pos_left hc hPpos`. Use linear arithmetic over natural numbers and integers. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hqq`.

Establish `hYd : d + 1 ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i`. Rewrite using `[hY]`. Use linear arithmetic over natural numbers and integers. Establish `hmul : (d + 1) * P ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P` using `Nat.mul_le_mul_right _ hYd`. Rewrite `hmul` using `[Nat.add_mul, one_mul, mul_comm d P]`.

Rewrite `hqhi` using `[Nat.mul_add]`. Establish `hnat : N ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P`. Generalize the expression as in `P * qlo = u at *`. Generalize the expression as in `P * d = w at *`. Generalize the expression as in `(XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P = t at *`.

Use linear arithmetic over natural numbers and integers. Establish `hR : ((N : ℕ) : ℝ) ≤ (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P : ℕ) : ℝ)`. Conclude with `hnat` after adjusting the coercions. Move the coercions through the operations in `at hR`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Yl_bound (hFree : RestFree C0 CE1 CE2 X) {dl : DCl X} (hdl : dl ∈ clSet C0 CE1 CE2 X) {a : Fin X.s → ℕ}
    (ha : a ∈ cbox C0 CE1 CE2 X dl) {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a)
    (i : Fin (X.S C0 CE1 CE2).t)
    (hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤
      ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊) :
    ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) - X.L.a -
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  set l := uTop (X.S C0 CE1 CE2) i with hl
  set P := (X.S C0 CE1 CE2).P X.p l with hP
  set σ := ∑ c : Fin (X.r + 1), dl.2 l c with hσ
  set N := ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ with hN
  have hP1 : 1 ≤ P := hS.P1 l
  have hdl' : dl ∈ digSet C0 CE1 CE2 X ×ˢ digSet C0 CE1 CE2 X := hdl
  have h2 : dl.2 ∈ digSet C0 CE1 CE2 X := (Finset.mem_product.1 hdl').2
  have hdig : ∀ c, dl.2 l c < P := fun c =>
    Finset.mem_range.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 h2 l) c)
  have hsum : σ < (X.r + 1) * P := by
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (X.r + 1))))
      Finset.univ_nonempty (fun c _ => hdig c)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this
  have hσA : σ ≤ X.L.a := by
    have hkP := hS.kP l
    have hkb := hS.kb
    have hsR : (σ : ℝ) < ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hsum
    have hP1R : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
    have hr0 : (0 : ℝ) ≤ (X.r : ℝ) := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ X.L.b' := by nlinarith
    have hA0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
    have : (σ : ℝ) < (X.L.a : ℝ) := by nlinarith
    exact_mod_cast this.le
  obtain ⟨vlo, hlo1, hlo2, hlo3, hlo4⟩ := exists_low X.L.a σ P (by omega) hσA
  obtain ⟨vhi, hhi1, hhi2, hhi3, hhi4⟩ := exists_high N σ P (by omega) (by omega)
  have hWlo : vlo ∈ Wl C0 CE1 CE2 X dl l := by
    simp only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hlo1, by omega⟩, hlo3, hlo4⟩
  have hWhi : vhi ∈ Wl C0 CE1 CE2 X dl l := by
    simp only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hhi1⟩, hhi3, hhi4⟩
  have hry : x.fst.ry = dl.2 := by
    have hx' := (Finset.mem_sigma.1 hx).1
    simp only [Finset.mem_filter] at hx'
    exact congrArg Prod.snd hx'.2
  have hall : ∀ a' ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a' := fun a' ha' =>
    (hFree dl hdl a ha a' ha') ▸ hx
  have hroomL : LvlRoom C0 CE1 CE2 X dl x.snd := lvlRoom_of ha hry hall
  have hx1 : x.2.1 i ≤ (vlo - σ) / P := hroomL i vlo hWlo
  obtain ⟨qlo, hqlo⟩ := hlo4
  obtain ⟨qhi, hqhi⟩ := hhi4
  have hPpos : 0 < P := by omega
  have hdlo : (vlo - σ) / P = qlo := by rw [hqlo]; exact Nat.mul_div_cancel_left _ hPpos
  have hdhi : (vhi - σ) / P = qhi := by rw [hqhi]; exact Nat.mul_div_cancel_left _ hPpos
  have hmlo : cm C0 CE1 CE2 X dl x.2 i vlo ∈ Nl C0 CE1 CE2 X dl x.2 i := by
    unfold Nl; exact Finset.mem_image_of_mem _ hWlo
  have hmhi : cm C0 CE1 CE2 X dl x.2 i vhi ∈ Nl C0 CE1 CE2 X dl x.2 i := by
    unfold Nl; exact Finset.mem_image_of_mem _ hWhi
  have hinf : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ≤ cm C0 CE1 CE2 X dl x.2 i vlo :=
    Nat.sInf_le (Finset.mem_coe.2 hmlo)
  have hsup : cm C0 CE1 CE2 X dl x.2 i vhi ≤ (Nl C0 CE1 CE2 X dl x.2 i).sup id :=
    Finset.le_sup (f := id) hmhi
  have hclo : cm C0 CE1 CE2 X dl x.2 i vlo = qlo - x.2.1 i := by
    show (vlo - σ) / P - x.2.1 i = _; rw [hdlo]
  have hchi : cm C0 CE1 CE2 X dl x.2 i vhi = qhi - x.2.1 i := by
    show (vhi - σ) / P - x.2.1 i = _; rw [hdhi]
  have hY : (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i =
      (Nl C0 CE1 CE2 X dl x.2 i).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) + 1 := rfl
  rw [hdlo] at hx1
  have hvv : vlo < vhi := by omega
  have hqq : qlo ≤ qhi := by
    by_contra hc
    push_neg at hc
    have : P * qhi < P * qlo := Nat.mul_lt_mul_of_pos_left hc hPpos
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqq
  have hYd : d + 1 ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i := by
    rw [hY]; omega
  have hmul : (d + 1) * P ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P := Nat.mul_le_mul_right _ hYd
  rw [Nat.add_mul, one_mul, mul_comm d P] at hmul
  rw [Nat.mul_add] at hqhi
  have hnat : N ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P := by
    generalize P * qlo = u at *
    generalize P * d = w at *
    generalize (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P = t at *
    omega
  have hR : ((N : ℕ) : ℝ) ≤ (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hR
  linarith

end Eps

end Formalism.MainNotions.G.SymmetricFormBlocks

end
