import Mathlib

namespace GroundTheory.Arith.Abelian

section Step

variable {R : Type*} [CommRing R] [IsDomain R]

/- English proof (translation)
The claim follows from `sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hM)`.
-/
private theorem eq_of_mul_sub_eq_zero {M x y : R} (hM : M ≠ 0) (h : M * (x - y) = 0) : x = y :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hM)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `eq_of_mul_sub_eq_zero (M := a1*a2^2*am1*b^4) (by simp [hb, ham1, ha1, ha2]) ?_` and prove the remaining obligations. Take the linear combination `(-a0*a1^3*a2^2*am1*am2*b^2*c + a0*a1*a2^3*am1^3*b^2*c + a1*a2^2*am1*b^3*c*e0) * hE0 + (a1*a2^2*am1*b^3*em2) * hE2 + (a0^2*a1^2*a2^2*a3*am1*b^2 - a1^2*a2^4*am1^2*b^2) * hEm2 + (-a1*a2^2*am1*b^6*om1) * hO1 + (-a0^3*a1*a2^3*am1*b^6 + a1^4*a2^2*am1^2*b^6) * hOm1 + (-a0^4*a1*a2^2*a3*a …`. Use `eq_of_mul_sub_eq_zero (M := a1*a2^17*am1*b^5*c^7) (by simp [hb, hc, ham1, ha1, ha2]) ?_` and prove the remaining obligations. Take the linear combination `(a0^2*a1^5*a2^17*am1*am2^2*b^4*c^8 - 2*a0^2*a1^3*a2^18*am1^3*am2*b^4*c^8 + a0^2*a1*a2^19*am1^5*b^4*c^8 - a0*a1^3*a2^17*am1*am2*b^5*c^8*e0 + a0*a1*a2^18*am1^3*b^5*c^8*e0 - a1*a2^17*am1*b^8*c^7*o1*om1 + a1*a2^17*am1*b^6*c^8*e0^2 - a1*a2^17*am1*b^4*c^7*d*o1*om1) * hE0 + (a1*a2^17*am …`.
-/
private theorem step_even (b c d am3 am2 am1 a0 a1 a2 a3 e0 e2 em2 o1 om1 : R)
    (hb : b ≠ 0) (hc : c ≠ 0) (ham1 : am1 ≠ 0) (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0)
    (hE0 : e0 * b = am1 ^ 2 * a0 * a2 - am2 * a0 * a1 ^ 2)
    (hE2 : e2 * b = a0 ^ 2 * a1 * a3 - am1 * a1 * a2 ^ 2)
    (hEm2 : em2 * b = am2 ^ 2 * am1 * a1 - am3 * am1 * a0 ^ 2)
    (hO1 : o1 = a2 * a0 ^ 3 - am1 * a1 ^ 3)
    (hOm1 : om1 = a1 * am1 ^ 3 - am2 * a0 ^ 3)
    (hSm1 : a1 * am3 = b ^ 2 * a0 * am2 - c * am1 ^ 2)
    (hS0 : a2 * am2 = b ^ 2 * a1 * am1 - c * a0 ^ 2)
    (hS1 : a3 * am1 = b ^ 2 * a2 * a0 - c * a1 ^ 2)
    (hI0 : c * (a2 * am1 ^ 2 + am2 * a1 ^ 2) = (b ^ 4 + d) * am1 * a0 * a1 - b ^ 2 * c * a0 ^ 3) :
    e2 * em2 = b ^ 2 * o1 * om1 - c * e0 ^ 2 ∧
      c * (e2 * om1 ^ 2 + em2 * o1 ^ 2) = (b ^ 4 + d) * om1 * e0 * o1 - b ^ 2 * c * e0 ^ 3 := by
  constructor
  · refine eq_of_mul_sub_eq_zero (M := a1*a2^2*am1*b^4) (by simp [hb, ham1, ha1, ha2]) ?_
    linear_combination (-a0*a1^3*a2^2*am1*am2*b^2*c + a0*a1*a2^3*am1^3*b^2*c + a1*a2^2*am1*b^3*c*e0) * hE0 + (a1*a2^2*am1*b^3*em2) * hE2 + (a0^2*a1^2*a2^2*a3*am1*b^2 - a1^2*a2^4*am1^2*b^2) * hEm2 + (-a1*a2^2*am1*b^6*om1) * hO1 + (-a0^3*a1*a2^3*am1*b^6 + a1^4*a2^2*am1^2*b^6) * hOm1 + (-a0^4*a1*a2^2*a3*am1^2*b^2 + a0^2*a1*a2^4*am1^3*b^2) * hSm1 + (a0^3*a1^3*a2^2*am1*am2*b^4 + a0^3*a1*a2^3*am1^3*b^4 - a0^2*a1^3*a2^2*am1^3*b^2*c - a1^4*a2^2*am1^4*b^4 - a1^3*a2^3*am1^3*am2*b^2) * hS0 + (-a0^5*a1*a2^2*am1*am2*b^4 + a0^4*a1*a2^2*am1^3*b^2*c + a0^2*a1^3*a2^2*am1*am2^2*b^2) * hS1
  · refine eq_of_mul_sub_eq_zero (M := a1*a2^17*am1*b^5*c^7) (by simp [hb, hc, ham1, ha1, ha2]) ?_
    linear_combination (a0^2*a1^5*a2^17*am1*am2^2*b^4*c^8 - 2*a0^2*a1^3*a2^18*am1^3*am2*b^4*c^8 + a0^2*a1*a2^19*am1^5*b^4*c^8 - a0*a1^3*a2^17*am1*am2*b^5*c^8*e0 + a0*a1*a2^18*am1^3*b^5*c^8*e0 - a1*a2^17*am1*b^8*c^7*o1*om1 + a1*a2^17*am1*b^6*c^8*e0^2 - a1*a2^17*am1*b^4*c^7*d*o1*om1) * hE0 + (a1*a2^17*am1*b^4*c^8*om1^2) * hE2 + (a1*a2^17*am1*b^4*c^8*o1^2) * hEm2 + (-a0^5*a1*a2^18*am1^2*am3*b^4*c^8 + a0^3*a1^2*a2^18*am1^2*am2^2*b^4*c^8 + a0^2*a1^4*a2^17*am1^3*am3*b^4*c^8 - a0^2*a1*a2^17*am1^2*am3*b^4*c^8*o1 + a0*a1^3*a2^17*am1*am2*b^8*c^7*om1 + a0*a1^3*a2^17*am1*am2*b^4*c^7*d*om1 - a0*a1*a2^18*am1^3*b^8*c^7*om1 - a0*a1*a2^18*am1^3*b^4*c^7*d*om1 - a1^5*a2^17*am1^3*am2^2*b^4*c^8 + a1^2*a2^17*am1^2*am2^2*b^4*c^8*o1) * hO1 + (-a0^5*a1^2*a2^17*a3*am1*am2*b^4*c^8 + a0^4*a1^3*a2^18*am1*am2*b^8*c^7 + a0^4*a1^3*a2^18*am1*am2*b^4*c^7*d - a0^4*a1*a2^19*am1^3*b^8*c^7 - a0^4*a1*a2^19*am1^3*b^4*c^7*d + a0^3*a1^2*a2^19*am1^2*am2*b^4*c^8 + a0^2*a1^3*a2^17*a3*am1^4*b^4*c^8 + a0^2*a1^2*a2^17*a3*am1*b^4*c^8*om1 - a0*a1^6*a2^17*am1^2*am2*b^8*c^7 - a0*a1^6*a2^17*am1^2*am2*b^4*c^7*d + a0*a1^4*a2^18*am1^4*b^8*c^7 + a0*a1^4*a2^18*am1^4*b^4*c^7*d - a1^3*a2^19*am1^5*b^4*c^8 - a1^2*a2^19*am1^2*b^4*c^8*om1) * hOm1 + (-a0^8*a2^19*am1^2*b^4*c^8 + 2*a0^5*a1^3*a2^18*am1^3*b^4*c^8 - a0^2*a1^6*a2^17*am1^4*b^4*c^8) * hSm1 + (-a0^11*a1^2*a2^16*b^6*c^9 + 2*a0^9*a1^3*a2^16*am1*b^8*c^8 + a0^9*a1^3*a2^16*am1*b^4*c^8*d + a0^9*a1^2*a2^17*am2*b^6*c^8 - a0^9*a2^18*am1^2*b^6*c^8 + a0^8*a1^5*a2^15*am1*b^6*c^9 - a0^8*a1^4*a2^16*am2*b^4*c^9 - a0^8*a1^2*a2^17*am1^2*b^4*c^9 - a0^7*a1^4*a2^16*am1^2*b^10*c^7 - a0^7*a1^4*a2^16*am1^2*b^6*c^7*d - a0^7*a1^3*a2^17*am1*am2*b^8*c^7 - a0^7*a1^3*a2^17*am1*am2*b^4*c^7*d + a0^7*a1*a2^18*am1^3*b^8*c^7 + a0^7*a1*a2^18*am1^3*b^4*c^7*d - 2*a0^6*a1^6*a2^15*am1^2*b^8*c^8 - a0^6*a1^6*a2^15*am1^2*b^4*c^8*d + a0^6*a1^3*a2^17*am1^3*b^6*c^8 + a0^5*a1^7*a2^15*am1*am2*b^4*c^9 + a0^5*a1^5*a2^16*am1^3*b^4*c^9 + a0^4*a1^7*a2^15*am1^3*b^10*c^7 + a0^4*a1^7*a2^15*am1^3*b^6*c^7*d + a0^4*a1^6*a2^16*am1^2*am2*b^8*c^7 + a0^4*a1^6*a2^16*am1^2*am2*b^4*c^7*d - a0^3*a1^8*a2^15*am1^2*am2*b^6*c^8 - a0^3*a1^7*a2^16*am1*am2^2*b^4*c^8 + a0^3*a1^5*a2^17*am1^3*am2*b^4*c^8 - 2*a0^3*a1^3*a2^18*am1^5*b^4*c^8 - a0*a1^7*a2^16*am1^5*b^8*c^7 - a0*a1^7*a2^16*am1^5*b^4*c^7*d + a1^8*a2^16*am1^4*am2*b^4*c^8 + a1^6*a2^17*am1^6*b^4*c^8) * hS0 + (a0^8*a1^2*a2^17*am2^2*b^4*c^8 - 2*a0^5*a1^3*a2^17*am1^3*am2*b^4*c^8 + a0^2*a1^4*a2^17*am1^6*b^4*c^8) * hS1 + (a0^10*a1^2*a2^16*b^4*c^9 - 2*a0^8*a1^3*a2^16*am1*b^6*c^8 + a0^8*a2^18*am1^2*b^4*c^8 - a0^7*a1^5*a2^15*am1*b^4*c^9 + a0^6*a1^4*a2^16*am1^2*b^8*c^7 - a0^6*a1*a2^18*am1^3*b^6*c^7 + 2*a0^5*a1^6*a2^15*am1^2*b^6*c^8 - a0^3*a1^7*a2^15*am1^3*b^8*c^7 + a0^3*a1*a2^19*am1^5*b^4*c^7 - a0^2*a1^6*a2^16*am1^4*b^4*c^8 + a1^7*a2^16*am1^5*b^6*c^7 - a1^4*a2^18*am1^6*b^4*c^7) * hI0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `eq_of_mul_sub_eq_zero (M := a2*am1*b^2) (by simp [hb, ham1, ha2]) ?_` and prove the remaining obligations. Take the linear combination `(-a0^2*a1*a2*a3*am1*b^2 + a1*a2^3*am1^2*b^2) * hE0 + (-a2*am1*b^3*e0) * hE2 + (a0^3*a2^2*am1*b^2*c - a1^3*a2*am1^2*b^2*c + a2*am1*b^2*c*o1) * hO1 + (-a0*a2^4*am1*b^2 + a1^3*a2*a3*am1*b^2) * hOm1 + (a2*am1*b^2*om1) * hO3 + (a0^4*a2^3*am1*b^2 - a0*a1^3*a2^2*am1^2*b^2) * hS0 + (-a0^ …`. Use `eq_of_mul_sub_eq_zero (M := a2^14*am1^2*b^4*c^6) (by simp [hb, hc, ham1, ha2]) ?_` and prove the remaining obligations. Take the linear combination `(a0^2*a1^2*a2^17*am1^2*am2*b^2*c^7 - a0^2*a1*a2^14*a3*am1^2*b^6*c^6*o1 - a0^2*a1*a2^14*a3*am1^2*b^2*c^6*d*o1 - a0^2*a2^18*am1^4*b^2*c^7 - a0*a1^5*a2^14*a3*am1^2*am2*b^2*c^7 + a0*a1^3*a2^15*a3*am1^4*b^2*c^7 - a0*a2^17*am1^2*b^3*c^7*e0 + a1^3*a2^14*a3*am1^2*b^3*c^7*e0 + a1*a2^16*am …`.
-/
private theorem step_odd (b c d am2 am1 a0 a1 a2 a3 e0 e2 o1 om1 o3 : R)
    (hb : b ≠ 0) (hc : c ≠ 0) (ham1 : am1 ≠ 0) (ha2 : a2 ≠ 0)
    (hE0 : e0 * b = am1 ^ 2 * a0 * a2 - am2 * a0 * a1 ^ 2)
    (hE2 : e2 * b = a0 ^ 2 * a1 * a3 - am1 * a1 * a2 ^ 2)
    (hO1 : o1 = a2 * a0 ^ 3 - am1 * a1 ^ 3)
    (hOm1 : om1 = a1 * am1 ^ 3 - am2 * a0 ^ 3)
    (hO3 : o3 = a3 * a1 ^ 3 - a0 * a2 ^ 3)
    (hS0 : a2 * am2 = b ^ 2 * a1 * am1 - c * a0 ^ 2)
    (hS1 : a3 * am1 = b ^ 2 * a2 * a0 - c * a1 ^ 2)
    (hI0 : c * (a2 * am1 ^ 2 + am2 * a1 ^ 2) = (b ^ 4 + d) * am1 * a0 * a1 - b ^ 2 * c * a0 ^ 3) :
    o3 * om1 = b ^ 2 * e2 * e0 - c * o1 ^ 2 ∧
      c * (o3 * e0 ^ 2 + om1 * e2 ^ 2) = (b ^ 4 + d) * e0 * o1 * e2 - b ^ 2 * c * o1 ^ 3 := by
  constructor
  · refine eq_of_mul_sub_eq_zero (M := a2*am1*b^2) (by simp [hb, ham1, ha2]) ?_
    linear_combination (-a0^2*a1*a2*a3*am1*b^2 + a1*a2^3*am1^2*b^2) * hE0 + (-a2*am1*b^3*e0) * hE2 + (a0^3*a2^2*am1*b^2*c - a1^3*a2*am1^2*b^2*c + a2*am1*b^2*c*o1) * hO1 + (-a0*a2^4*am1*b^2 + a1^3*a2*a3*am1*b^2) * hOm1 + (a2*am1*b^2*om1) * hO3 + (a0^4*a2^3*am1*b^2 - a0*a1^3*a2^2*am1^2*b^2) * hS0 + (-a0^3*a1*a2^2*am1^2*b^2 + a1^4*a2*am1^3*b^2) * hS1
  · refine eq_of_mul_sub_eq_zero (M := a2^14*am1^2*b^4*c^6) (by simp [hb, hc, ham1, ha2]) ?_
    linear_combination (a0^2*a1^2*a2^17*am1^2*am2*b^2*c^7 - a0^2*a1*a2^14*a3*am1^2*b^6*c^6*o1 - a0^2*a1*a2^14*a3*am1^2*b^2*c^6*d*o1 - a0^2*a2^18*am1^4*b^2*c^7 - a0*a1^5*a2^14*a3*am1^2*am2*b^2*c^7 + a0*a1^3*a2^15*a3*am1^4*b^2*c^7 - a0*a2^17*am1^2*b^3*c^7*e0 + a1^3*a2^14*a3*am1^2*b^3*c^7*e0 + a1*a2^16*am1^3*b^6*c^6*o1 + a1*a2^16*am1^3*b^2*c^6*d*o1) * hE0 + (a0^2*a1*a2^14*a3*am1^2*b^2*c^7*om1 - a1*a2^16*am1^3*b^2*c^7*om1 - a2^14*am1^2*b^7*c^6*e0*o1 + a2^14*am1^2*b^3*c^7*e2*om1 - a2^14*am1^2*b^3*c^6*d*e0*o1) * hE2 + (a0^6*a2^16*am1^2*b^6*c^7 - 2*a0^3*a1^3*a2^15*am1^3*b^6*c^7 + a0^3*a1^3*a2^14*a3*am1^2*am2*b^6*c^6 + a0^3*a1^3*a2^14*a3*am1^2*am2*b^2*c^6*d - a0^3*a1*a2^15*a3*am1^4*b^6*c^6 - a0^3*a1*a2^15*a3*am1^4*b^2*c^6*d + a0^3*a2^15*am1^2*b^6*c^7*o1 - a0*a1^3*a2^16*am1^3*am2*b^6*c^6 - a0*a1^3*a2^16*am1^3*am2*b^2*c^6*d + a0*a1*a2^17*am1^5*b^6*c^6 + a0*a1*a2^17*am1^5*b^2*c^6*d + a1^6*a2^14*am1^4*b^6*c^7 - a1^3*a2^14*am1^3*b^6*c^7*o1 + a2^14*am1^2*b^6*c^7*o1^2) * hO1 + (a0^4*a1^2*a2^14*a3^2*am1^2*b^2*c^7 - 2*a0^2*a1^2*a2^16*a3*am1^3*b^2*c^7 + a1^2*a2^18*am1^4*b^2*c^7) * hOm1 + (a2^14*am1^2*b^4*c^7*e0^2) * hO3 + (-a0^9*a1^2*a2^15*b^6*c^7 + a0^8*a1^4*a2^14*b^4*c^8 + a0^7*a1^3*a2^15*am1*b^8*c^6 + a0^7*a1^3*a2^15*am1*b^4*c^6*d - a0^6*a1^5*a2^14*am1*b^2*c^7*d + a0^6*a1^2*a2^16*am1^2*b^4*c^7 - a0^5*a1^7*a2^13*am1*b^4*c^8 + a0^5*a1^4*a2^15*am1^2*b^2*c^8 - a0^4*a1^6*a2^14*am1^2*b^8*c^6 - a0^4*a1^6*a2^14*am1^2*b^4*c^6*d - a0^4*a1^3*a2^16*am1^3*b^6*c^6 - a0^4*a1^3*a2^16*am1^3*b^2*c^6*d + a0^3*a1^8*a2^13*am1^2*b^6*c^7 + a0^3*a1^8*a2^13*am1^2*b^2*c^7*d + a0^3*a1^7*a2^14*am1*am2*b^4*c^7 - 3*a0^3*a1^5*a2^15*am1^3*b^4*c^7 - a0^3*a1^4*a2^16*am1^2*am2*b^2*c^7 + 2*a0^3*a1^2*a2^17*am1^4*b^2*c^7 - a0^2*a1^9*a2^13*am1*am2*b^2*c^8 + a0*a1^6*a2^15*am1^4*b^6*c^6 + a0*a1^6*a2^15*am1^4*b^2*c^6*d + a1^8*a2^14*am1^4*b^4*c^7 - a1^5*a2^16*am1^5*b^2*c^7) * hS0 + (-a0^8*a1^2*a2^15*am2*b^4*c^7 + a0^7*a1^4*a2^14*am2*b^2*c^8 - a0^7*a1^2*a2^14*a3*am1*am2*b^2*c^7 + a0^6*a1^3*a2^15*am1*am2*b^6*c^6 + a0^6*a1^3*a2^15*am1*am2*b^2*c^6*d - a0^6*a1*a2^16*am1^3*b^6*c^6 - a0^6*a1*a2^16*am1^3*b^2*c^6*d + a0^5*a1^3*a2^15*am1^3*b^4*c^7 + 2*a0^5*a1^2*a2^16*am1^2*am2*b^2*c^7 - a0^4*a1^5*a2^14*am1^3*b^2*c^8 + a0^4*a1^3*a2^14*a3*am1^4*b^2*c^7 - a0^3*a1^6*a2^14*am1^2*am2*b^6*c^6 - a0^3*a1^6*a2^14*am1^2*am2*b^2*c^6*d + a0^3*a1^4*a2^15*am1^4*b^6*c^6 + a0^3*a1^4*a2^15*am1^4*b^2*c^6*d + a0^2*a1^7*a2^14*am1*am2^2*b^2*c^7 - 2*a0^2*a1^5*a2^15*am1^3*am2*b^2*c^7 - a0^2*a1^3*a2^16*am1^5*b^2*c^7) * hS1 + (a0^8*a1^2*a2^15*b^4*c^7 - a0^7*a1^4*a2^14*b^2*c^8 - a0^6*a1^3*a2^15*am1*b^6*c^6 + a0^6*a2^17*am1^2*b^4*c^6 - 2*a0^5*a1^2*a2^16*am1^2*b^2*c^7 + a0^4*a1^7*a2^13*am1*b^2*c^8 + a0^3*a1^6*a2^14*am1^2*b^6*c^6 - a0^3*a2^18*am1^4*b^2*c^6 - a0^2*a1^8*a2^13*am1^2*b^4*c^7 + 2*a0^2*a1^5*a2^15*am1^3*b^2*c^7 - a1^6*a2^15*am1^4*b^4*c^6 + a1^3*a2^17*am1^5*b^2*c^6) * hI0

end Step

private def SomosAt {R : Type*} [CommRing R] (w : ℤ → R) (b c : R) (n : ℤ) : Prop :=
  w (n + 2) * w (n - 2) = b ^ 2 * w (n + 1) * w (n - 1) - c * w n ^ 2

private def InvAt {R : Type*} [CommRing R] (w : ℤ → R) (b c d : R) (n : ℤ) : Prop :=
  c * (w (n + 2) * w (n - 1) ^ 2 + w (n - 2) * w (n + 1) ^ 2) =
    (b ^ 4 + d) * w (n - 1) * w n * w (n + 1) - b ^ 2 * c * w n ^ 3

section Induction

variable {R : Type*} [CommRing R] [IsDomain R] (b c d : R)

/- English proof (translation)
Establish `sm1` using `hS (h - 1) le_rfl (by omega)`. Establish `s0` using `hS h (by omega) (by omega)`. Establish `s1` using `hS (h + 1) (by omega) le_rfl`. Simplify using `only [SomosAt, InvAt] at sm1 s0 s1 hI ⊢`. Rewrite `sm1` using `[show h - 1 + 2 = h + 1 by ring, show h - 1 - 2 = h - 3 by ring, show h - 1 + 1 = h by ring, show h - 1 - 1 = h - 2 by ring]`.

Rewrite `s1` using `[show h + 1 + 2 = h + 3 by ring, show h + 1 - 2 = h - 1 by ring, show h + 1 + 1 = h + 2 by ring, show h + 1 - 1 = h by ring]`. Use `set w := normEDS b c d with hw`. Establish `hE0 : w (2 * h) * b = w (h - 1) ^ 2 * w h * w (h + 2) - w (h - 2) * w h * w (h + 1) ^ 2` using `normEDS_even b c d h`. Establish `hE2 : w (2 * h + 2) * b = w h ^ 2 * w (h + 1) * w (h + 3) - w (h - 1) * w (h + 1) * w (h + 2) ^ 2`. Use `normEDS_even b c d (h + 1)` as an intermediate fact.

Rewrite `this` using `[show 2 * (h + 1) = 2 * h + 2 by ring, show h + 1 - 1 = h by ring, show h + 1 + 2 = h + 3 by ring, show h + 1 - 2 = h - 1 by ring, show h + 1 + 1 = h + 2 by ring]`. Then use the resulting hypothesis. Establish `hEm2 : w (2 * h - 2) * b = w (h - 2) ^ 2 * w (h - 1) * w (h + 1) - w (h - 3) * w (h - 1) * w h ^ 2`. Use `normEDS_even b c d (h - 1)` as an intermediate fact. Rewrite `this` using `[show 2 * (h - 1) = 2 * h - 2 by ring, show h - 1 - 1 = h - 2 by ring, show h - 1 + 2 = h + 1 by ring, show h - 1 - 2 = h - 3 by ring, show h - 1 + 1 = h by ring]`. Then use the resulting hypothesis. Establish `hO1 : w (2 * h + 1) = w (h + 2) * w h ^ 3 - w (h - 1) * w (h + 1) ^ 3` using `normEDS_odd b c d h`.

Establish `hOm1 : w (2 * h - 1) = w (h + 1) * w (h - 1) ^ 3 - w (h - 2) * w h ^ 3`. Use `normEDS_odd b c d (h - 1)` as an intermediate fact. Rewrite `this` using `[show 2 * (h - 1) + 1 = 2 * h - 1 by ring, show h - 1 + 2 = h + 1 by ring, show h - 1 - 1 = h - 2 by ring, show h - 1 + 1 = h by ring]`. Then use the resulting hypothesis. Establish `hO3 : w (2 * h + 3) = w (h + 3) * w (h + 1) ^ 3 - w h * w (h + 2) ^ 3`. Use `normEDS_odd b c d (h + 1)` as an intermediate fact.

Rewrite `this` using `[show 2 * (h + 1) + 1 = 2 * h + 3 by ring, show h + 1 + 2 = h + 3 by ring, show h + 1 - 1 = h by ring, show h + 1 + 1 = h + 2 by ring]`. Then use the resulting hypothesis. Establish `ne1` using `hne (h - 1) le_rfl (by omega)`. Establish `ne2` using `hne (h + 1) (by omega) (by omega)`. Establish `ne3` using `hne (h + 2) (by omega) le_rfl`. Take `⟨e1, e2⟩` from `step_even b c d (w (h - 3)) (w (h - 2)) (w (h - 1)) (w h) (w (h + 1)) (w (h + 2)) (w (h + 3)) (w (2 * h)) (w (2 * h + 2)) (w (2 * h - 2)) (w (2 * h + 1)) (w (2 * h - 1)) hb hc ne1 ne2 ne3 hE0 hE2 hEm2 hO1 hOm1 (by linear_combination sm1) (by linear_combination s0) (by linear_comb …`.

Take `⟨o1, o2⟩` from `step_odd b c d (w (h - 2)) (w (h - 1)) (w h) (w (h + 1)) (w (h + 2)) (w (h + 3)) (w (2 * h)) (w (2 * h + 2)) (w (2 * h + 1)) (w (2 * h - 1)) (w (2 * h + 3)) hb hc ne1 ne3 hE0 hE2 hO1 hOm1 hO3 (by linear_combination s0) (by linear_combination s1) hI`. Use `⟨⟨e1, e2⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show 2 * h + 1 + 2 = 2 * h + 3 by ring, show 2 * h + 1 - 2 = 2 * h - 1 by ring, show 2 * h + 1 + 1 = 2 * h + 2 by ring, show 2 * h + 1 - 1 = 2 * h by ring]`. Conclude with `o1`. Rewrite using `[show 2 * h + 1 + 2 = 2 * h + 3 by ring, show 2 * h + 1 - 2 = 2 * h - 1 by ring, show 2 * h + 1 + 1 = 2 * h + 2 by ring, show 2 * h + 1 - 1 = 2 * h by ring]`.

Conclude with `o2`.
-/
private theorem step_seq (hb : b ≠ 0) (hc : c ≠ 0) (h : ℤ)
    (hne : ∀ k, h - 1 ≤ k → k ≤ h + 2 → normEDS b c d k ≠ 0)
    (hS : ∀ k, h - 1 ≤ k → k ≤ h + 1 → SomosAt (normEDS b c d) b c k)
    (hI : InvAt (normEDS b c d) b c d h) :
    (SomosAt (normEDS b c d) b c (2 * h) ∧ InvAt (normEDS b c d) b c d (2 * h)) ∧
      (SomosAt (normEDS b c d) b c (2 * h + 1) ∧ InvAt (normEDS b c d) b c d (2 * h + 1)) := by
  have sm1 := hS (h - 1) le_rfl (by omega)
  have s0 := hS h (by omega) (by omega)
  have s1 := hS (h + 1) (by omega) le_rfl
  simp only [SomosAt, InvAt] at sm1 s0 s1 hI ⊢
  rw [show h - 1 + 2 = h + 1 by ring, show h - 1 - 2 = h - 3 by ring, show h - 1 + 1 = h by ring,
    show h - 1 - 1 = h - 2 by ring] at sm1
  rw [show h + 1 + 2 = h + 3 by ring, show h + 1 - 2 = h - 1 by ring,
    show h + 1 + 1 = h + 2 by ring, show h + 1 - 1 = h by ring] at s1
  set w := normEDS b c d with hw
  have hE0 : w (2 * h) * b = w (h - 1) ^ 2 * w h * w (h + 2) - w (h - 2) * w h * w (h + 1) ^ 2 :=
    normEDS_even b c d h
  have hE2 : w (2 * h + 2) * b =
      w h ^ 2 * w (h + 1) * w (h + 3) - w (h - 1) * w (h + 1) * w (h + 2) ^ 2 := by
    have := normEDS_even b c d (h + 1)
    rwa [show 2 * (h + 1) = 2 * h + 2 by ring, show h + 1 - 1 = h by ring,
      show h + 1 + 2 = h + 3 by ring, show h + 1 - 2 = h - 1 by ring,
      show h + 1 + 1 = h + 2 by ring] at this
  have hEm2 : w (2 * h - 2) * b =
      w (h - 2) ^ 2 * w (h - 1) * w (h + 1) - w (h - 3) * w (h - 1) * w h ^ 2 := by
    have := normEDS_even b c d (h - 1)
    rwa [show 2 * (h - 1) = 2 * h - 2 by ring, show h - 1 - 1 = h - 2 by ring,
      show h - 1 + 2 = h + 1 by ring, show h - 1 - 2 = h - 3 by ring,
      show h - 1 + 1 = h by ring] at this
  have hO1 : w (2 * h + 1) = w (h + 2) * w h ^ 3 - w (h - 1) * w (h + 1) ^ 3 :=
    normEDS_odd b c d h
  have hOm1 : w (2 * h - 1) = w (h + 1) * w (h - 1) ^ 3 - w (h - 2) * w h ^ 3 := by
    have := normEDS_odd b c d (h - 1)
    rwa [show 2 * (h - 1) + 1 = 2 * h - 1 by ring, show h - 1 + 2 = h + 1 by ring,
      show h - 1 - 1 = h - 2 by ring, show h - 1 + 1 = h by ring] at this
  have hO3 : w (2 * h + 3) = w (h + 3) * w (h + 1) ^ 3 - w h * w (h + 2) ^ 3 := by
    have := normEDS_odd b c d (h + 1)
    rwa [show 2 * (h + 1) + 1 = 2 * h + 3 by ring, show h + 1 + 2 = h + 3 by ring,
      show h + 1 - 1 = h by ring, show h + 1 + 1 = h + 2 by ring] at this
  have ne1 := hne (h - 1) le_rfl (by omega)
  have ne2 := hne (h + 1) (by omega) (by omega)
  have ne3 := hne (h + 2) (by omega) le_rfl
  obtain ⟨e1, e2⟩ := step_even b c d (w (h - 3)) (w (h - 2)) (w (h - 1)) (w h) (w (h + 1))
    (w (h + 2)) (w (h + 3)) (w (2 * h)) (w (2 * h + 2)) (w (2 * h - 2)) (w (2 * h + 1))
    (w (2 * h - 1)) hb hc ne1 ne2 ne3 hE0 hE2 hEm2 hO1 hOm1 (by linear_combination sm1)
    (by linear_combination s0) (by linear_combination s1) hI
  obtain ⟨o1, o2⟩ := step_odd b c d (w (h - 2)) (w (h - 1)) (w h) (w (h + 1)) (w (h + 2))
    (w (h + 3)) (w (2 * h)) (w (2 * h + 2)) (w (2 * h + 1)) (w (2 * h - 1)) (w (2 * h + 3))
    hb hc ne1 ne3 hE0 hE2 hO1 hOm1 hO3 (by linear_combination s0) (by linear_combination s1) hI
  refine ⟨⟨e1, e2⟩, ?_, ?_⟩
  · rw [show 2 * h + 1 + 2 = 2 * h + 3 by ring, show 2 * h + 1 - 2 = 2 * h - 1 by ring,
      show 2 * h + 1 + 1 = 2 * h + 2 by ring, show 2 * h + 1 - 1 = 2 * h by ring]
    exact o1
  · rw [show 2 * h + 1 + 2 = 2 * h + 3 by ring, show 2 * h + 1 - 2 = 2 * h - 1 by ring,
      show 2 * h + 1 + 1 = 2 * h + 2 by ring, show 2 * h + 1 - 1 = 2 * h by ring]
    exact o2

end Induction

section Universal

open MvPolynomial

/- English proof (translation)
Proceed by induction on `n using normEDSRec' with`. Consider the case `zero => simp [normEDS_zero]`. Consider the case `one => simp [normEDS_one]`. Consider the case `two => simp [normEDS_two]`. Consider the case `three => simp [normEDS_three]`.

Consider the case `four => norm_num [normEDS_four]`. Consider the case `even m ih`. Establish `h` using `normEDS_even (2 : ℤ) 3 2 ((m : ℤ) + 3)`. Establish `e1` using `ih (m + 2) (by omega)`. Establish `e2` using `ih (m + 3) (by omega)`.

Establish `e3` using `ih (m + 5) (by omega)`. Establish `e4` using `ih (m + 1) (by omega)`. Establish `e5` using `ih (m + 4) (by omega)`. Move the coercions through the operations in `at e1 e2 e3 e4 e5 ⊢`. Rewrite `h` using `[show (m : ℤ) + 3 - 1 = m + 2 by ring, show (m : ℤ) + 3 + 2 = m + 5 by ring, show (m : ℤ) + 3 - 2 = m + 1 by ring, show (m : ℤ) + 3 + 1 = m + 4 by ring, e1, e2, e3, e4, e5]`.

Establish `key : normEDS (2 : ℤ) 3 2 (2 * ((m : ℤ) + 3)) * 2 = 2 * (2 * ((m : ℤ) + 3))`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `odd m ih`.

Establish `h` using `normEDS_odd (2 : ℤ) 3 2 ((m : ℤ) + 2)`. Establish `e1` using `ih (m + 4) (by omega)`. Establish `e2` using `ih (m + 2) (by omega)`. Establish `e3` using `ih (m + 1) (by omega)`. Establish `e4` using `ih (m + 3) (by omega)`.

Move the coercions through the operations in `at e1 e2 e3 e4 ⊢`. Rewrite `h` using `[show (m : ℤ) + 2 + 2 = m + 4 by ring, show (m : ℤ) + 2 - 1 = m + 1 by ring, show (m : ℤ) + 2 + 1 = m + 3 by ring, e1, e2, e3, e4]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem normEDS_two_three_two_nat (n : ℕ) : normEDS (2 : ℤ) 3 2 n = n := by
  induction n using normEDSRec' with
  | zero => simp [normEDS_zero]
  | one => simp [normEDS_one]
  | two => simp [normEDS_two]
  | three => simp [normEDS_three]
  | four => norm_num [normEDS_four]
  | even m ih =>
    have h := normEDS_even (2 : ℤ) 3 2 ((m : ℤ) + 3)
    have e1 := ih (m + 2) (by omega)
    have e2 := ih (m + 3) (by omega)
    have e3 := ih (m + 5) (by omega)
    have e4 := ih (m + 1) (by omega)
    have e5 := ih (m + 4) (by omega)
    push_cast at e1 e2 e3 e4 e5 ⊢
    rw [show (m : ℤ) + 3 - 1 = m + 2 by ring, show (m : ℤ) + 3 + 2 = m + 5 by ring,
      show (m : ℤ) + 3 - 2 = m + 1 by ring, show (m : ℤ) + 3 + 1 = m + 4 by ring,
      e1, e2, e3, e4, e5] at h
    have key : normEDS (2 : ℤ) 3 2 (2 * ((m : ℤ) + 3)) * 2 = 2 * (2 * ((m : ℤ) + 3)) := by
      rw [h]; ring
    linarith
  | odd m ih =>
    have h := normEDS_odd (2 : ℤ) 3 2 ((m : ℤ) + 2)
    have e1 := ih (m + 4) (by omega)
    have e2 := ih (m + 2) (by omega)
    have e3 := ih (m + 1) (by omega)
    have e4 := ih (m + 3) (by omega)
    push_cast at e1 e2 e3 e4 ⊢
    rw [show (m : ℤ) + 2 + 2 = m + 4 by ring, show (m : ℤ) + 2 - 1 = m + 1 by ring,
      show (m : ℤ) + 2 + 1 = m + 3 by ring, e1, e2, e3, e4] at h
    rw [h]; ring

/- English proof (translation)
Break down `Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩` into its components or cases. Conclude with `normEDS_two_three_two_nat k`. Rewrite using `[normEDS_neg, normEDS_two_three_two_nat]`.
-/
private theorem normEDS_two_three_two (n : ℤ) : normEDS (2 : ℤ) 3 2 n = n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact normEDS_two_three_two_nat k
  · rw [normEDS_neg, normEDS_two_three_two_nat]

private noncomputable def uw (n : ℤ) : MvPolynomial (Fin 3) ℤ :=
  normEDS (X 0) (X 1) (X 2) n

/- English proof (translation)
Rewrite using `[uw, map_normEDS]`. Simplify using `using normEDS_two_three_two n`.
-/
private theorem eval_uw (n : ℤ) : eval ![2, 3, 2] (uw n) = n := by
  rw [uw, map_normEDS]
  simpa using normEDS_two_three_two n

/- English proof (translation)
Introduce `h`. Use `eval_uw n` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `hn this.symm`.
-/
private theorem uw_ne_zero {n : ℤ} (hn : n ≠ 0) : uw n ≠ 0 := by
  intro h
  have := eval_uw n
  rw [h, map_zero] at this
  exact hn this.symm

/- English proof (translation)
The claim follows from `X_ne_zero 0`.
-/
private theorem X0_ne_zero : (X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := X_ne_zero 0
/- English proof (translation)
The claim follows from `X_ne_zero 1`.
-/
private theorem X1_ne_zero : (X 1 : MvPolynomial (Fin 3) ℤ) ≠ 0 := X_ne_zero 1

/- English proof (translation)
Establish `w0 : uw 0 = 0` using `normEDS_zero ..`. Establish `w1 : uw 1 = 1` using `normEDS_one ..`. Establish `w2 : uw 2 = X 0` using `normEDS_two ..`. Establish `w3 : uw 3 = X 1` using `normEDS_three ..`. Establish `w4 : uw 4 = X 2 * X 0` using `normEDS_four ..`.

Establish `wm1 : uw (-1) = -1` using `by rw [uw, normEDS_neg, ← uw, w1]`. Establish `wm2 : uw (-2) = -X 0` using `by rw [uw, normEDS_neg, ← uw, w2]`. Establish `w5 : uw 5 = X 2 * X 0 ^ 4 - X 1 ^ 3`. Establish `h5 : uw (2 * 2 + 1) = uw (2 + 2) * uw 2 ^ 3 - uw (2 - 1) * uw (2 + 1) ^ 3` using `normEDS_odd _ _ _ 2`. Evaluate the numerical expressions using `at h5`.

Rewrite using `[h5, w4, w2, w1, w3]`. Expand and normalize the polynomial expressions, which then agree. Establish `w6 : uw 6 = X 0 * X 1 * (X 2 * X 0 ^ 4 - X 1 ^ 3) - X 1 * X 2 ^ 2 * X 0`. Establish `h6 : uw (2 * 3) * X 0 = uw (3 - 1) ^ 2 * uw 3 * uw (3 + 2) - uw (3 - 2) * uw 3 * uw (3 + 1) ^ 2` using `normEDS_even _ _ _ 3`. Evaluate the numerical expressions using `at h6`.

Apply `mul_right_cancel₀ X0_ne_zero` to reduce the goal to its premises. Rewrite using `[h6, w2, w3, w5, w1, w4]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `interval_cases k <;> constructor <;> simp only [SomosAt, InvAt] <;> norm_num <;>`. Apply the tactic sequence `simp only [w0, w1, w2, w3, w4, w5, w6, wm1, wm2] <;> ring`.
-/
private theorem uw_base (k : ℕ) (hk : k ≤ 4) :
    SomosAt uw (X 0) (X 1) k ∧ InvAt uw (X 0) (X 1) (X 2) k := by
  have w0 : uw 0 = 0 := normEDS_zero ..
  have w1 : uw 1 = 1 := normEDS_one ..
  have w2 : uw 2 = X 0 := normEDS_two ..
  have w3 : uw 3 = X 1 := normEDS_three ..
  have w4 : uw 4 = X 2 * X 0 := normEDS_four ..
  have wm1 : uw (-1) = -1 := by rw [uw, normEDS_neg, ← uw, w1]
  have wm2 : uw (-2) = -X 0 := by rw [uw, normEDS_neg, ← uw, w2]
  have w5 : uw 5 = X 2 * X 0 ^ 4 - X 1 ^ 3 := by
    have h5 : uw (2 * 2 + 1) = uw (2 + 2) * uw 2 ^ 3 - uw (2 - 1) * uw (2 + 1) ^ 3 :=
      normEDS_odd _ _ _ 2
    norm_num at h5
    rw [h5, w4, w2, w1, w3]; ring
  have w6 : uw 6 = X 0 * X 1 * (X 2 * X 0 ^ 4 - X 1 ^ 3) - X 1 * X 2 ^ 2 * X 0 := by
    have h6 : uw (2 * 3) * X 0 =
        uw (3 - 1) ^ 2 * uw 3 * uw (3 + 2) - uw (3 - 2) * uw 3 * uw (3 + 1) ^ 2 :=
      normEDS_even _ _ _ 3
    norm_num at h6
    apply mul_right_cancel₀ X0_ne_zero
    rw [h6, w2, w3, w5, w1, w4]; ring
  interval_cases k <;> constructor <;> simp only [SomosAt, InvAt] <;> norm_num <;>
    simp only [w0, w1, w2, w3, w4, w5, w6, wm1, wm2] <;> ring

/- English proof (translation)
Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Break down `le_or_gt N 4 with hN | hN` into its components or cases. Conclude with `uw_base N hN`. Take `⟨h, hh⟩ : ∃ h : ℕ, N = 2 * h ∨ N = 2 * h + 1` from `⟨N / 2, by omega⟩`.

Establish `key` using `step_seq (X 0 : MvPolynomial (Fin 3) ℤ) (X 1) (X 2) X0_ne_zero X1_ne_zero (h : ℤ) (fun k hk1 hk2 => uw_ne_zero (by omega)) (fun k hk1 hk2 => by`. Use `(ih k.toNat (by omega)).1` as an intermediate fact. Rewrite using `[Int.toNat_of_nonneg (by omega)] at this)` and apply the resulting hypothesis. Use the proof step `(ih h (by omega)).2`. Break down `hh with rfl | rfl` into its components or cases.

Use `push_cast`. Conclude with `key.1`. Use `push_cast`. Conclude with `key.2`.
-/
private theorem uw_rel_nat (N : ℕ) :
    SomosAt uw (X 0) (X 1) N ∧ InvAt uw (X 0) (X 1) (X 2) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases le_or_gt N 4 with hN | hN
  · exact uw_base N hN
  obtain ⟨h, hh⟩ : ∃ h : ℕ, N = 2 * h ∨ N = 2 * h + 1 := ⟨N / 2, by omega⟩
  have key := step_seq (X 0 : MvPolynomial (Fin 3) ℤ) (X 1) (X 2) X0_ne_zero X1_ne_zero (h : ℤ)
    (fun k hk1 hk2 => uw_ne_zero (by omega))
    (fun k hk1 hk2 => by
      have := (ih k.toNat (by omega)).1
      rwa [Int.toNat_of_nonneg (by omega)] at this)
    (ih h (by omega)).2
  rcases hh with rfl | rfl
  · push_cast; exact key.1
  · push_cast; exact key.2

/- English proof (translation)
Break down `Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩` into its components or cases. Conclude with `uw_rel_nat k`. Take `⟨hs, hi⟩` from `uw_rel_nat k`. Simplify using `only [SomosAt, InvAt, uw] at hs hi ⊢`. Rewrite using `[show -(k : ℤ) + 2 = -((k : ℤ) - 2) by ring, show -(k : ℤ) - 2 = -((k : ℤ) + 2) by ring, show -(k : ℤ) + 1 = -((k : ℤ) - 1) by ring, show -(k : ℤ) - 1 = -((k : ℤ) + 1) by ring]`.

Simplify using `only [normEDS_neg]`. Prove the components needed by the constructor for the conclusion. Take the linear combination `hs`. Take the linear combination `-hi`.
-/
private theorem uw_rel (n : ℤ) :
    SomosAt uw (X 0) (X 1) n ∧ InvAt uw (X 0) (X 1) (X 2) n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact uw_rel_nat k
  · obtain ⟨hs, hi⟩ := uw_rel_nat k
    simp only [SomosAt, InvAt, uw] at hs hi ⊢
    rw [show -(k : ℤ) + 2 = -((k : ℤ) - 2) by ring, show -(k : ℤ) - 2 = -((k : ℤ) + 2) by ring,
      show -(k : ℤ) + 1 = -((k : ℤ) - 1) by ring, show -(k : ℤ) - 1 = -((k : ℤ) + 1) by ring]
    simp only [normEDS_neg]
    constructor
    · linear_combination hs
    · linear_combination -hi

end Universal

variable {R : Type*} [CommRing R] (b c d : R)

/- English proof (translation)
Establish `h` using `(uw_rel n).1`. Simplify using `only [SomosAt, uw] at h`. Use `congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d]) h` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_pow, map_normEDS] at this`. Simplify using `using this`.
-/
theorem normEDS_somos (n : ℤ) :
    normEDS b c d (n + 2) * normEDS b c d (n - 2) =
      b ^ 2 * normEDS b c d (n + 1) * normEDS b c d (n - 1) - c * normEDS b c d n ^ 2 := by
  have h := (uw_rel n).1
  simp only [SomosAt, uw] at h
  have := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d]) h
  simp only [map_sub, map_mul, map_pow, map_normEDS] at this
  simpa using this

/- English proof (translation)
Establish `h` using `(uw_rel n).2`. Simplify using `only [InvAt, uw] at h`. Use `congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d]) h` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_pow, map_add, map_normEDS] at this`. Simplify using `using this`.
-/
theorem normEDS_invariant (n : ℤ) :
    c * (normEDS b c d (n + 2) * normEDS b c d (n - 1) ^ 2 +
        normEDS b c d (n - 2) * normEDS b c d (n + 1) ^ 2) =
      (b ^ 4 + d) * normEDS b c d (n - 1) * normEDS b c d n * normEDS b c d (n + 1) -
        b ^ 2 * c * normEDS b c d n ^ 3 := by
  have h := (uw_rel n).2
  simp only [InvAt, uw] at h
  have := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d]) h
  simp only [map_sub, map_mul, map_pow, map_add, map_normEDS] at this
  simpa using this

end GroundTheory.Arith.Abelian
