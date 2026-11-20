import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroOfTrace

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
Introduce `h`. Rewrite `hT` using `[Tz, h]`. Simplify using `at hT`.
-/
theorem herm_self_ne_zero {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  rw [Tz, h] at hT
  simp at hT

/- English proof (translation)
Rewrite using `[herm_sub_left, herm_smul_left]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_proj_zero (x z : Fin (2 * r + k + 1) → ℂ) (hc : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (x - (herm (Hpk k r) x z / herm (Hpk k r) z z) • z) z = 0 := by
  rw [herm_sub_left, herm_smul_left]
  field_simp
  ring

/- English proof (translation)
Use `set c := herm (Hpk k r) z z with hcdef`. Establish `hc0 : c ≠ 0` using `herm_self_ne_zero hT`. Establish `stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 → ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z`. Introduce `w hw hwz`. Use `set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef`.

Establish `hy : inWb k r y` using `inWb_sub (h1 w hw) (inWb_smul _ hz)`. Establish `hyz : herm (Hpk k r) y z = 0` using `herm_proj_zero _ _ hc0`. Establish `hyy : herm (Hpk k r) y y = 0`. Establish `e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0` using `h3 w y hw hy hwz hyz`. Establish `e2 : herm (Hpk k r) z y = 0` using `by rw [herm_swap, hyz, star_zero]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[herm_sub_left, herm_smul_left]`. Use `_ = 0 := by rw [e1, e2]; ring`. Establish `: y = 0` using `wb_definite hz hT hy hyz (by rw [hyy]; simp)`. Conclude with `sub_eq_zero.1 this`.

Use `set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ`. Use `set b := ξ *ᵥ z - μ • z with hbdef`. Establish `hb : inWb k r b` using `inWb_sub (h1 z hz) (inWb_smul _ hz)`. Establish `hbz : herm (Hpk k r) b z = 0` using `herm_proj_zero _ _ hc0`. Establish `hξz : ξ *ᵥ z = μ • z + b` using `by rw [hbdef]; abel`.

Establish `stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 → ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z`. Introduce `w hw hwz`. Rewrite using `[stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z` using `stepB b hb hbz`. Establish `hNz` using `h4 z hz`. Establish `hb0 : b = 0`. Assume the negation of the conclusion as `hb0`. Establish `hbb : herm (Hpk k r) b b ≠ 0`.

Introduce `h`. Conclude with `hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))`. Use `set l := -(herm (Hpk k r) b b) / c with hl`. Establish `hl0 : l ≠ 0` using `div_ne_zero (neg_ne_zero.2 hbb) hc0`. Set `f : ℕ → ℂ × ℂ` to `fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0) (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m`.

Establish `hf0 : f 0 = (1, 0)` using `rfl`. Establish `hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1)` using `fun m => rfl`. Establish `hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => rw [hf0, pow_zero, one_mulVec]`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Rewrite using `[pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]`. Use `module`.

Rewrite `hNz` using `[hpow]`. Establish `hp : (f N).1 = 0`. Use `congrArg (fun x => herm (Hpk k r) x z) hNz` as an intermediate fact. Simplify using `only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this`. Conclude with `(mul_eq_zero.1 this).resolve_right hc0`.

Establish `hq : (f N).2 = 0`. Rewrite `hNz` using `[hp, zero_smul, zero_add]`. Conclude with `(smul_eq_zero.1 hNz).resolve_right hb0`. Establish `hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => left`. Rewrite using `[hf0]`. Conclude with `one_ne_zero`. Consider the case `succ m ih`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Rewrite `hcon` using `[hfs]`. Take `⟨e1, e2⟩` from `hcon`. Simplify using `only at e1 e2`.

Rewrite `e1` using `[e2, mul_zero, zero_add]`. Establish `: (f m).2 = 0` using `(mul_eq_zero.1 e1).resolve_left hl0`. Break down `ih with h | h` into its components or cases. Conclude with `h e2`. Conclude with `h this`.

Break down `hnz N with h | h` into its components or cases. Conclude with `h hp`. Conclude with `h hq`. Establish `hξz' : ξ *ᵥ z = μ • z` using `by rw [hξz, hb0, add_zero]`. Establish `hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]`. Consider the case `succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]`. Rewrite `hNz` using `[hpow2]`.

Establish `hμ0 : μ = 0`. Use `congrArg (fun x => herm (Hpk k r) x z) hNz` as an intermediate fact. Simplify using `only [herm_smul_left, herm_zero_left] at this`. Conclude with `pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1`. Establish `hξz0 : ξ *ᵥ z = 0` using `by rw [hξz', hμ0, zero_smul]`.

Introduce `u hu`. Use `set α := herm (Hpk k r) u z / c`. Establish `hu' : inWb k r (u - α • z)` using `inWb_sub hu (inWb_smul _ hz)`. Establish `hu'z : herm (Hpk k r) (u - α • z) z = 0` using `herm_proj_zero _ _ hc0`. Establish `e : u = α • z + (u - α • z)` using `by abel`.

Rewrite using `[e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]`. Simplify using the standard rewrite rules.
-/
theorem coreW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ξ : B.Mat k r)
    (h1 : ∀ u, inWb k r u → inWb k r (ξ *ᵥ u))
    (h2 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) (ξ *ᵥ u) v = -herm (Hpk k r) u (ξ *ᵥ v))
    (h3 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
      herm (Hpk k r) (ξ *ᵥ u) v = 0)
    (N : ℕ) (h4 : ∀ u, inWb k r u → (ξ ^ N) *ᵥ u = 0) :
    ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
  set c := herm (Hpk k r) z z with hcdef
  have hc0 : c ≠ 0 := herm_self_ne_zero hT

  have stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z := by
    intro w hw hwz
    set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef
    have hy : inWb k r y := inWb_sub (h1 w hw) (inWb_smul _ hz)
    have hyz : herm (Hpk k r) y z = 0 := herm_proj_zero _ _ hc0
    have hyy : herm (Hpk k r) y y = 0 := by
      have e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0 := h3 w y hw hy hwz hyz
      have e2 : herm (Hpk k r) z y = 0 := by rw [herm_swap, hyz, star_zero]
      calc herm (Hpk k r) y y
          = herm (Hpk k r) (ξ *ᵥ w) y - (herm (Hpk k r) (ξ *ᵥ w) z / c) * herm (Hpk k r) z y := by
            conv_lhs => rw [hydef]
            rw [herm_sub_left, herm_smul_left]
        _ = 0 := by rw [e1, e2]; ring
    have : y = 0 := wb_definite hz hT hy hyz (by rw [hyy]; simp)
    exact sub_eq_zero.1 this
  set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ
  set b := ξ *ᵥ z - μ • z with hbdef
  have hb : inWb k r b := inWb_sub (h1 z hz) (inWb_smul _ hz)
  have hbz : herm (Hpk k r) b z = 0 := herm_proj_zero _ _ hc0
  have hξz : ξ *ᵥ z = μ • z + b := by rw [hbdef]; abel

  have stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z := by
    intro w hw hwz
    rw [stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]
    congr 1
    ring
  have hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z := stepB b hb hbz
  have hNz := h4 z hz

  have hb0 : b = 0 := by
    by_contra hb0
    have hbb : herm (Hpk k r) b b ≠ 0 := by
      intro h
      exact hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))
    set l := -(herm (Hpk k r) b b) / c with hl
    have hl0 : l ≠ 0 := div_ne_zero (neg_ne_zero.2 hbb) hc0
    let f : ℕ → ℂ × ℂ := fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0)
      (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m
    have hf0 : f 0 = (1, 0) := rfl
    have hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1) := fun m => rfl
    have hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b := by
      intro m
      induction m with
      | zero => rw [hf0, pow_zero, one_mulVec]; simp
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]
        module
    rw [hpow] at hNz
    have hp : (f N).1 = 0 := by
      have := congrArg (fun x => herm (Hpk k r) x z) hNz
      simp only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hc0
    have hq : (f N).2 = 0 := by
      rw [hp, zero_smul, zero_add] at hNz
      exact (smul_eq_zero.1 hNz).resolve_right hb0
    have hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0 := by
      intro m
      induction m with
      | zero => left; rw [hf0]; exact one_ne_zero
      | succ m ih =>
        by_contra hcon
        push Not at hcon
        rw [hfs] at hcon
        obtain ⟨e1, e2⟩ := hcon
        simp only at e1 e2
        rw [e2, mul_zero, zero_add] at e1
        have : (f m).2 = 0 := (mul_eq_zero.1 e1).resolve_left hl0
        rcases ih with h | h
        · exact h e2
        · exact h this
    rcases hnz N with h | h
    · exact h hp
    · exact h hq

  have hξz' : ξ *ᵥ z = μ • z := by rw [hξz, hb0, add_zero]
  have hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]
  rw [hpow2] at hNz
  have hμ0 : μ = 0 := by
    have := congrArg (fun x => herm (Hpk k r) x z) hNz
    simp only [herm_smul_left, herm_zero_left] at this
    exact pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1
  have hξz0 : ξ *ᵥ z = 0 := by rw [hξz', hμ0, zero_smul]
  intro u hu
  set α := herm (Hpk k r) u z / c
  have hu' : inWb k r (u - α • z) := inWb_sub hu (inWb_smul _ hz)
  have hu'z : herm (Hpk k r) (u - α • z) z = 0 := herm_proj_zero _ _ hc0
  have e : u = α • z + (u - α • z) := by abel
  rw [e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
