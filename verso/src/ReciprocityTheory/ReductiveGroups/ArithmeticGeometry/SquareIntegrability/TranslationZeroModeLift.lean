import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def Uq {dim : (E →+* ℂ) → ℕ} (q : ℕ) (a : Vsp dim) (F : Vsp dim → ℂ) : Vsp dim → ℂ :=
  fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)

def Uh (X : PT E) (q : ℕ) (a : Vsp X.dim) (F : Vsp X.dim → ℂ) : Vsp X.dim → ℂ :=
  fun v => (X.eps a : ℂ) ^ q * Uq q a F v

def F0 {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (q : ℕ)
    (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ) : Vsp dim → ℂ :=
  fun v => cexp ((q * Real.pi / 2 : ℂ) * S (IR I) v) * β (wmap (IR I) v)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Take `⟨k, hk⟩` from `X.integral a b ha hb`. Establish `hε` using `X.eps_add a ha b hb`. Rewrite `hε` using `[hk]`. Establish `hsin : Real.sin (Real.pi * k) = 0`.

Rewrite using `[mul_comm]`. Conclude with `Real.sin_int_mul_pi k`. Establish `hεC : (X.eps (a + b) : ℂ) = X.eps a * X.eps b * (Real.cos (Real.pi * k) : ℝ)`. Conclude with `hε` after adjusting the coercions. Establish `h1 : Hf v (a + b) = Hf v a + Hf v b`.

Simplify using `only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Establish `h2 : Hf (v - a) b = Hf v b - Hf a b`. Simplify using `only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]`. Establish `h3 : Hf (a + b) (a + b) = Hf a a + Hf a b + Hf b a + Hf b b`. Simplify using `only [Hf, PiLp.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : Hf b a = (starRingEnd ℂ) (Hf a b)`. Simplify using `only [Hf, map_sum, map_mul, Complex.conj_conj]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `h5 : Hf b a - Hf a b = -(2 * (k : ℂ) * Complex.I)`.

Rewrite using `[h4]`. Establish `hz` using `Complex.re_add_im (Hf a b)`. Rewrite using `[← hz, hk]`. Simplify using `only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hexp : Complex.exp (-(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q`. Establish `: -(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2 = q * (-((Real.pi * k : ℝ) : ℂ) * Complex.I)` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_nat_mul, Complex.exp_mul_I]`. Use `congr 1`.

Rewrite using `[Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin]`. Simplify using the standard rewrite rules. Establish `hAB : Complex.exp ((q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * Complex.exp ((q : ℂ) * Real.pi * (Hf v b - Hf a b) - q * Real.pi * Hf b b / 2) = Complex.exp ((q : ℂ) * Real.pi * (Hf v a + Hf v b) - q * Real.pi * (Hf a a + Hf a b + Hf b a + Hf b b) / 2) * ((Real.cos (R …`. Rewrite using `[← Complex.exp_add, ← hexp, ← Complex.exp_add]`. Use `congr 1`.

Take the linear combination `((q : ℂ) * Real.pi / 2) * h5`. Simplify using `only [Uh, Uq]`. Rewrite using `[sub_sub, hεC, h1, h2, h3]`. Take the linear combination `((X.eps a : ℂ) ^ q * (X.eps b : ℂ) ^ q * F (v - (a + b))) * hAB`.
-/
theorem Uh_add (X : PT E) (q : ℕ) {a b : Vsp X.dim} (ha : a ∈ X.L) (hb : b ∈ X.L) (F : Vsp X.dim → ℂ) :
    Uh X q a (Uh X q b F) = Uh X q (a + b) F := by
  funext v
  obtain ⟨k, hk⟩ := X.integral a b ha hb
  have hε := X.eps_add a ha b hb
  rw [hk] at hε
  have hsin : Real.sin (Real.pi * k) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi k
  have hεC : (X.eps (a + b) : ℂ) = X.eps a * X.eps b * (Real.cos (Real.pi * k) : ℝ) := by
    exact_mod_cast hε

  have h1 : Hf v (a + b) = Hf v a + Hf v b := by
    simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have h2 : Hf (v - a) b = Hf v b - Hf a b := by
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have h3 : Hf (a + b) (a + b) = Hf a a + Hf a b + Hf b a + Hf b b := by
    simp only [Hf, PiLp.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  have h4 : Hf b a = (starRingEnd ℂ) (Hf a b) := by
    simp only [Hf, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h5 : Hf b a - Hf a b = -(2 * (k : ℂ) * Complex.I) := by
    rw [h4]
    have hz := Complex.re_add_im (Hf a b)
    rw [← hz, hk]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hexp : Complex.exp (-(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2) =
      ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q := by
    have : -(q * Real.pi * (2 * (k : ℂ) * Complex.I)) / 2 = q * (-((Real.pi * k : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_nat_mul, Complex.exp_mul_I]
    congr 1
    rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin]
    simp
  have hAB : Complex.exp ((q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) *
      Complex.exp ((q : ℂ) * Real.pi * (Hf v b - Hf a b) - q * Real.pi * Hf b b / 2) =
      Complex.exp ((q : ℂ) * Real.pi * (Hf v a + Hf v b) -
        q * Real.pi * (Hf a a + Hf a b + Hf b a + Hf b b) / 2) *
        ((Real.cos (Real.pi * k) : ℝ) : ℂ) ^ q := by
    rw [← Complex.exp_add, ← hexp, ← Complex.exp_add]
    congr 1
    linear_combination ((q : ℂ) * Real.pi / 2) * h5
  simp only [Uh, Uq]
  rw [sub_sub, hεC, h1, h2, h3]
  linear_combination ((X.eps a : ℂ) ^ q * (X.eps b : ℂ) ^ q * F (v - (a + b))) * hAB

/- English proof (translation)
Establish `hH : Hf (v + a) a = Hf v a + Hf a a`. Simplify using `only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]`. Simplify using `only [Uh, Uq, add_sub_cancel_right, hH]`. Establish `he : (q : ℂ) * Real.pi * (Hf v a + Hf a a) - q * Real.pi * Hf a a / 2 = q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2` using `by ring`. Rewrite using `[he]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem Uh_shift (X : PT E) (q : ℕ) (a : Vsp X.dim) (G : Vsp X.dim → ℂ) (v : Vsp X.dim) :
    Uh X q a G (v + a) = (X.eps a : ℂ) ^ q * cexp (q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2) * G v := by
  have hH : Hf (v + a) a = Hf v a + Hf a a := by
    simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  simp only [Uh, Uq, add_sub_cancel_right, hH]
  have he : (q : ℂ) * Real.pi * (Hf v a + Hf a a) - q * Real.pi * Hf a a / 2 =
      q * Real.pi * Hf v a + q * Real.pi * Hf a a / 2 := by ring
  rw [he]; ring

section F0sec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (q : ℕ) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP q).Sec q)
include hI hβ

/- English proof (translation)
Unfold `GT.Sec at hβ`. Take `⟨-, hsec⟩` from `hβ`. Establish `hγ : wmap (IR I) x ∈ lat (YB hI hP q).b` using `by show wmap (IR I) x ∈ lat (bB hI hP)`. Rewrite using `[lat_bB]`. Conclude with `wmap_mem_GB hx`.

Establish `h1` using `hsec _ hγ (wmap (IR I) v)`. Rewrite `h1` using `[show (YB hI hP q).ka = kaB X I q from rfl, kaB_wmap hI _ hx]`. Move the coercions through the operations in `at h1`. Establish `hz : ∀ k, z (IR I) k (v + x) = z (IR I) k v + z (IR I) k x`. Introduce `k`.

Use `first`. Consider the case `(simp only [z]; rw [Hf_add_l])`. Consider the case `simp [z, Hf_add_l]`. Establish `hzr : ∀ k, (starRingEnd ℂ) (z (IR I) k x) = z (IR I) k x` using `fun k => Complex.conj_eq_iff_im.mpr (z_im_Ip hx k)`. Establish `hd1` using `Hf_decomp (K := IR I) (hK_of hI) v x`.

Establish `hd2` using `Hf_decomp (K := IR I) (hK_of hI) x x`. Unfold `F0 S`. Rewrite using `[map_add, h1, Hf_wmap (hK_of hI), Hf_wmap (hK_of hI), hd1, hd2]`. Simplify using `only [hz, hzr]`. Establish `hexp : ∀ a b c d : ℂ, a + b = c + d → cexp a * cexp b = cexp c * cexp d`.

Introduce `a b c d h`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, h]`. Establish `hs : ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2 = ∑ k, z (IR I) k v ^ 2 + 2 * ∑ k, z (IR I) k v * z (IR I) k x + ∑ k, z (IR I) k x * z (IR I) k x`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Establish `key` using `hexp ((q : ℂ) * Real.pi / 2 * ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2) ((q : ℂ) * Real.pi * Hf (p2 (IR I) v) (p2 (IR I) x) + q * Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2) ((q : ℂ) * Real.pi * (∑ k, z (IR I) k v * z (IR I) k x + Hf (p2 (IR I) v) (p2 (IR I) x)) + q * Real.pi * ( …`. Take the linear combination `((X.eps x : ℂ) ^ q * β (wmap (IR I) v)) * key`.
-/
theorem zeroModeLift_add_lattice {x : Vsp X.dim} (hx : x ∈ Ip X I) (v : Vsp X.dim) :
    F0 I q β (v + x) = (X.eps x : ℂ) ^ q * cexp (q * Real.pi * Hf v x + q * Real.pi * Hf x x / 2) * F0 I q β v := by
  unfold GT.Sec at hβ
  obtain ⟨-, hsec⟩ := hβ
  have hγ : wmap (IR I) x ∈ lat (YB hI hP q).b := by
    show wmap (IR I) x ∈ lat (bB hI hP)
    rw [lat_bB]
    exact wmap_mem_GB hx
  have h1 := hsec _ hγ (wmap (IR I) v)
  rw [show (YB hI hP q).ka = kaB X I q from rfl, kaB_wmap hI _ hx] at h1
  push_cast at h1
  have hz : ∀ k, z (IR I) k (v + x) = z (IR I) k v + z (IR I) k x := by
    intro k
    first
    | (simp only [z]; rw [Hf_add_l])
    | simp [z, Hf_add_l]
  have hzr : ∀ k, (starRingEnd ℂ) (z (IR I) k x) = z (IR I) k x := fun k =>
    Complex.conj_eq_iff_im.mpr (z_im_Ip hx k)
  have hd1 := Hf_decomp (K := IR I) (hK_of hI) v x
  have hd2 := Hf_decomp (K := IR I) (hK_of hI) x x
  unfold F0 S
  rw [map_add, h1, Hf_wmap (hK_of hI), Hf_wmap (hK_of hI), hd1, hd2]
  simp only [hz, hzr]
  have hexp : ∀ a b c d : ℂ, a + b = c + d → cexp a * cexp b = cexp c * cexp d := by
    intro a b c d h
    rw [← Complex.exp_add, ← Complex.exp_add, h]
  have hs : ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2 = ∑ k, z (IR I) k v ^ 2 +
      2 * ∑ k, z (IR I) k v * z (IR I) k x + ∑ k, z (IR I) k x * z (IR I) k x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have key := hexp ((q : ℂ) * Real.pi / 2 * ∑ k, (z (IR I) k v + z (IR I) k x) ^ 2)
    ((q : ℂ) * Real.pi * Hf (p2 (IR I) v) (p2 (IR I) x) +
      q * Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2)
    ((q : ℂ) * Real.pi * (∑ k, z (IR I) k v * z (IR I) k x + Hf (p2 (IR I) v) (p2 (IR I) x)) +
      q * Real.pi * (∑ k, z (IR I) k x * z (IR I) k x + Hf (p2 (IR I) x) (p2 (IR I) x)) / 2)
    ((q : ℂ) * Real.pi / 2 * ∑ k, z (IR I) k v ^ 2) (by rw [hs]; ring)
  linear_combination ((X.eps x : ℂ) ^ q * β (wmap (IR I) v)) * key

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `h` using `zeroModeLift_add_lattice hI hP q hβ hx (v - x)`. Rewrite `h` using `[sub_add_cancel]`. Establish `h2 : Hf (v - x) x = Hf v x - Hf x x`. Simplify using `only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]`.

Rewrite `h` using `[h2]`. Simplify using `only [Uh, Uq]`. Rewrite using `[h]`. Establish `he : (q : ℂ) * Real.pi * (Hf v x - Hf x x) + q * Real.pi * Hf x x / 2 = q * Real.pi * Hf v x - q * Real.pi * Hf x x / 2` using `by ring`. Rewrite using `[he]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem translation_zeroModeLift {x : Vsp X.dim} (hx : x ∈ Ip X I) : Uh X q x (F0 I q β) = F0 I q β := by
  funext v
  have h := zeroModeLift_add_lattice hI hP q hβ hx (v - x)
  rw [sub_add_cancel] at h
  have h2 : Hf (v - x) x = Hf v x - Hf x x := by
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [h2] at h
  simp only [Uh, Uq]
  rw [h]
  have he : (q : ℂ) * Real.pi * (Hf v x - Hf x x) + q * Real.pi * Hf x x / 2 =
      q * Real.pi * Hf v x - q * Real.pi * Hf x x / 2 := by ring
  rw [he]; ring

end F0sec

def NIp (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Submodule ℤ X.L := (Ip X I).comap X.L.subtype

abbrev Qc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) := X.L ⧸ NIp X I

def Tm (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (γ : X.L) : Vsp X.dim → ℂ :=
  Uh X q γ (F0 I q β)

def Tc (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (c : Qc X I) : Vsp X.dim → ℂ :=
  Tm X I q β (Quotient.out c)

def sP (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
    (v : Vsp X.dim) : ℂ :=
  ∑' c : Qc X I, Tc X I q β c v

section Tsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (q : ℕ) {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ}
  (hβ : β ∈ (YB hI hP q).Sec q)
include hI hβ

/- English proof (translation)
Establish `hd : ((γ - γ' : X.L) : Vsp X.dim) ∈ Ip X I` using `h`. Unfold `Tm`. Establish `e : (γ : Vsp X.dim) = (γ' : Vsp X.dim) + ((γ - γ' : X.L) : Vsp X.dim)`. Simplify using the standard rewrite rules. Rewrite using `[e, ← Uh_add X q γ'.2 (γ - γ').2, translation_zeroModeLift hI hP q hβ hd]`.
-/
theorem Tm_congr {γ γ' : X.L} (h : γ - γ' ∈ NIp X I) : Tm X I q β γ = Tm X I q β γ' := by
  have hd : ((γ - γ' : X.L) : Vsp X.dim) ∈ Ip X I := h
  unfold Tm
  have e : (γ : Vsp X.dim) = (γ' : Vsp X.dim) + ((γ - γ' : X.L) : Vsp X.dim) := by
    simp
  rw [e, ← Uh_add X q γ'.2 (γ - γ').2, translation_zeroModeLift hI hP q hβ hd]

/- English proof (translation)
Unfold `Tc`. Apply `Tm_congr hI hP q hβ` to reduce the goal to its premises. Rewrite using `[← Submodule.Quotient.eq]`. Use `first`. Consider the case `exact Quotient.out_eq _`.

Consider the case `exact Quotient.out_eq' _`. Consider the case `simp`.
-/
theorem Tc_mk (γ : X.L) : Tc X I q β (Submodule.Quotient.mk γ) = Tm X I q β γ := by
  unfold Tc
  apply Tm_congr hI hP q hβ
  rw [← Submodule.Quotient.eq]
  first
  | exact Quotient.out_eq _
  | exact Quotient.out_eq' _
  | simp

/- English proof (translation)
Establish `hc : c - Submodule.Quotient.mk γ0 = Submodule.Quotient.mk (Quotient.out c - γ0)`. Rewrite using `[Submodule.Quotient.mk_sub]`. Use `congr 1`. Conclude with `(Quotient.out_eq c).symm`. Rewrite using `[hc, Tc_mk hI hP q hβ]`.

Unfold `Tc Tm`. Establish `e : ((Quotient.out c : X.L) : Vsp X.dim) = (γ0 : Vsp X.dim) + ((Quotient.out c - γ0 : X.L) : Vsp X.dim)`. Simplify using the standard rewrite rules. Rewrite using `[e, ← Uh_add X q γ0.2 (Quotient.out c - γ0).2, Uh_shift]`.
-/
theorem Tc_shift (c : Qc X I) (γ0 : X.L) (v : Vsp X.dim) :
    Tc X I q β c (v + (γ0 : Vsp X.dim)) = (X.eps (γ0 : Vsp X.dim) : ℂ) ^ q *
      cexp (q * Real.pi * Hf v (γ0 : Vsp X.dim) + q * Real.pi * Hf (γ0 : Vsp X.dim) γ0 / 2) *
        Tc X I q β (c - Submodule.Quotient.mk γ0) v := by
  have hc : c - Submodule.Quotient.mk γ0 = Submodule.Quotient.mk (Quotient.out c - γ0) := by
    rw [Submodule.Quotient.mk_sub]
    congr 1
    exact (Quotient.out_eq c).symm
  rw [hc, Tc_mk hI hP q hβ]
  unfold Tc Tm
  have e : ((Quotient.out c : X.L) : Vsp X.dim) =
      (γ0 : Vsp X.dim) + ((Quotient.out c - γ0 : X.L) : Vsp X.dim) := by
    simp
  rw [e, ← Uh_add X q γ0.2 (Quotient.out c - γ0).2, Uh_shift]

/- English proof (translation)
Unfold `sP`. Simplify using `only [Tc_shift hI hP q hβ]`. Rewrite using `[tsum_mul_left]`. Use `congr 1`. Conclude with `(Equiv.subRight (Submodule.Quotient.mk γ0 : Qc X I)).tsum_eq (fun c => Tc X I q β c v)`.
-/
theorem sP_shift (γ0 : X.L) (v : Vsp X.dim) :
    sP X I q β (v + (γ0 : Vsp X.dim)) = (X.eps (γ0 : Vsp X.dim) : ℂ) ^ q *
      cexp (q * Real.pi * Hf v (γ0 : Vsp X.dim) + q * Real.pi * Hf (γ0 : Vsp X.dim) γ0 / 2) *
        sP X I q β v := by
  unfold sP
  simp only [Tc_shift hI hP q hβ]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight (Submodule.Quotient.mk γ0 : Qc X I)).tsum_eq (fun c => Tc X I q β c v)

end Tsec

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
