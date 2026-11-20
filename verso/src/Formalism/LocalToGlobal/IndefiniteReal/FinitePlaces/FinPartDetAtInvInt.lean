import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Mathlib.NumberTheory.NumberField.ClassNumber

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

/- English proof (translation)
It suffices to establish `H : ∀ (t : Finset ι) (q : ι → R), (∀ i ∈ t, IsIdempotentElem (q i)) → ∑ i ∈ t, q i = 0 → ∀ i ∈ t, q i = 0 from H s p hp h`. Introduce `t`. Proceed by induction on `t using Finset.strongInduction with`. Consider the case `H t ih`. Introduce `q hq hsum`.

Establish `hle : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → q j = q k * q j`. Introduce `j hj k hk hjk`. Establish `e1 : q k * q k = q k` using `(hq k hk).eq`. Establish `hid : ∀ j' ∈ t.erase k, IsIdempotentElem ((1 - q k) * q j')`. Introduce `j' hj'`.

Establish `e2 : q j' * q j' = q j'` using `(hq j' (Finset.mem_of_mem_erase hj')).eq`. Use `show ((1 - q k) * q j') * ((1 - q k) * q j') = (1 - q k) * q j'`. Take the linear combination `(1 - q k) ^ 2 * e2 + q j' * e1`. Establish `hs2 : ∑ j' ∈ t.erase k, (1 - q k) * q j' = 0`. Rewrite using `[← Finset.mul_sum]`.

Establish `h2` using `Finset.add_sum_erase t q hk`. Rewrite `h2` using `[hsum]`. Take the linear combination `(1 - q k) * h2 + e1`. Use `ih (t.erase k) (Finset.erase_ssubset hk) (fun j' => (1 - q k) * q j') hid hs2 j (Finset.mem_erase.mpr ⟨hjk, hj⟩)` as an intermediate fact. Take the linear combination `this`.

Introduce `i hi`. Establish `heq : ∀ j ∈ t, q j = q i`. Introduce `j hj`. Distinguish the cases in `hji : j = i`. Rewrite using `[hji]`.

Rewrite using `[hle j hj i hi hji, mul_comm, ← hle i hi j hj (Ne.symm hji)]`. Establish `hsum' : ∑ j ∈ t, q j = (t.card : R) * q i`. Rewrite using `[Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]`. Rewrite `hsum'` using `[hsum]`. Establish `hc : (t.card : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨i, hi⟩)`.

Establish `hu : algebraMap K R (t.card : K)⁻¹ * (t.card : R) = 1`. Rewrite using `[← map_natCast (algebraMap K R), ← map_mul, inv_mul_cancel₀ hc, map_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem idem_sum_zero {K R ι : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] (s : Finset ι) (p : ι → R)
    (hp : ∀ i ∈ s, IsIdempotentElem (p i)) (h : ∑ i ∈ s, p i = 0) : ∀ i ∈ s, p i = 0 := by
  classical
  suffices H : ∀ (t : Finset ι) (q : ι → R), (∀ i ∈ t, IsIdempotentElem (q i)) → ∑ i ∈ t, q i = 0 →
      ∀ i ∈ t, q i = 0 from H s p hp h
  intro t
  induction t using Finset.strongInduction with
  | H t ih =>
    intro q hq hsum
    have hle : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → q j = q k * q j := by
      intro j hj k hk hjk
      have e1 : q k * q k = q k := (hq k hk).eq
      have hid : ∀ j' ∈ t.erase k, IsIdempotentElem ((1 - q k) * q j') := by
        intro j' hj'
        have e2 : q j' * q j' = q j' := (hq j' (Finset.mem_of_mem_erase hj')).eq
        show ((1 - q k) * q j') * ((1 - q k) * q j') = (1 - q k) * q j'
        linear_combination (1 - q k) ^ 2 * e2 + q j' * e1
      have hs2 : ∑ j' ∈ t.erase k, (1 - q k) * q j' = 0 := by
        rw [← Finset.mul_sum]
        have h2 := Finset.add_sum_erase t q hk
        rw [hsum] at h2
        linear_combination (1 - q k) * h2 + e1
      have := ih (t.erase k) (Finset.erase_ssubset hk) (fun j' => (1 - q k) * q j') hid hs2 j
        (Finset.mem_erase.mpr ⟨hjk, hj⟩)
      linear_combination this
    intro i hi
    have heq : ∀ j ∈ t, q j = q i := by
      intro j hj
      by_cases hji : j = i
      · rw [hji]
      · rw [hle j hj i hi hji, mul_comm, ← hle i hi j hj (Ne.symm hji)]
    have hsum' : ∑ j ∈ t, q j = (t.card : R) * q i := by
      rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at hsum'
    have hc : (t.card : K) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨i, hi⟩)
    have hu : algebraMap K R (t.card : K)⁻¹ * (t.card : R) = 1 := by
      rw [← map_natCast (algebraMap K R), ← map_mul, inv_mul_cancel₀ hc, map_one]
    calc q i = algebraMap K R (t.card : K)⁻¹ * ((t.card : R) * q i) := by rw [← mul_assoc, hu, one_mul]
      _ = 0 := by rw [← hsum', mul_zero]

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def resM (s : R) (A : Matrix n n R) : Matrix n n R := 1 + s • (A - 1)

/- English proof (translation)
Simplify using `only [resM]`. Establish `key : (A - 1) + (B - 1) + (A - 1) * (B - 1) = A * B - 1` using `by noncomm_ring`. Rewrite using `[← key]`. Simplify using `only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, hs, smul_add]`. Apply the tactic sequence `try abel`.
-/
theorem resM_mul {s : R} (hs : s * s = s) (A B : Matrix n n R) : resM s A * resM s B = resM s (A * B) := by
  simp only [resM]
  have key : (A - 1) + (B - 1) + (A - 1) * (B - 1) = A * B - 1 := by noncomm_ring
  rw [← key]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, hs, smul_add]
  try abel

/- English proof (translation)
Establish `hts : t * s = 0` using `by rw [mul_comm, hst]`. Simplify using `only [resM, hts, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hst, zero_smul, add_zero]`. Apply the tactic sequence `try abel`.
-/
theorem resM_orth {s t : R} (hst : s * t = 0) (A B : Matrix n n R) :
    resM s A * resM t B = 1 + s • (A - 1) + t • (B - 1) := by
  have hts : t * s = 0 := by rw [mul_comm, hst]
  simp only [resM, hts, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hst,
    zero_smul, add_zero]
  try abel

/- English proof (translation)
Rewrite using `[resM_orth hst]`. Simplify using `only [resM, add_smul, add_assoc]`.
-/
theorem resM_add {s t : R} (hst : s * t = 0) (A : Matrix n n R) : resM s A * resM t A = resM (s + t) A := by
  rw [resM_orth hst]
  simp only [resM, add_smul, add_assoc]

/- English proof (translation)
Simplify using `[resM]`.
-/
theorem resM_one_left (A : Matrix n n R) : resM 1 A = A := by
  simp [resM]

/- English proof (translation)
Simplify using `[resM]`.
-/
theorem resM_zero_left (A : Matrix n n R) : resM 0 A = 1 := by
  simp [resM]

/- English proof (translation)
Simplify using `[resM]`.
-/
theorem resM_one_right (s : R) : resM s (1 : Matrix n n R) = 1 := by
  simp [resM]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [resM, Matrix.one_apply, h]`.
-/
theorem resM_map {R' : Type*} [CommRing R'] (f : R →+* R') (s : R) (A : Matrix n n R) :
    (resM s A).map f = resM (f s) (A.map f) := by
  ext i j
  by_cases h : i = j <;> simp [resM, Matrix.one_apply, h]

/- English proof (translation)
Simplify using `[resM, Matrix.transpose_sub]`.
-/
theorem resM_transpose (s : R) (A : Matrix n n R) : (resM s A)ᵀ = resM s Aᵀ := by
  simp [resM, Matrix.transpose_sub]

/- English proof (translation)
Simplify using `only [resM, mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hBC]`.
-/
theorem resM_conj (s : R) (A : Matrix n n R) (B C : Matrix n n R) (hBC : B * C = 1) :
    B * resM s A * C = resM s (B * A * C) := by
  simp only [resM, mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hBC]

/- English proof (translation)
Simplify using `only [resM]`. Establish `key : (A' - 1) * G + G * (A - 1) + (A' - 1) * G * (A - 1) = 0`. Establish `e : (A' - 1) * G + G * (A - 1) + (A' - 1) * G * (A - 1) = A' * G * A - G` using `by noncomm_ring`. Rewrite using `[e, h, sub_self]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, hs, smul_add]`. Normalize the expressions using the abelian group laws. Use `_ = G := by rw [key, smul_zero, add_zero]`.
-/
theorem resM_unitary {s : R} (hs : s * s = s) (A A' G : Matrix n n R) (h : A' * G * A = G) :
    resM s A' * G * resM s A = G := by
  simp only [resM]
  have key : (A' - 1) * G + G * (A - 1) + (A' - 1) * G * (A - 1) = 0 := by
    have e : (A' - 1) * G + G * (A - 1) + (A' - 1) * G * (A - 1) = A' * G * A - G := by noncomm_ring
    rw [e, h, sub_self]
  calc (1 + s • (A' - 1)) * G * (1 + s • (A - 1))
      = G + s • ((A' - 1) * G + G * (A - 1) + (A' - 1) * G * (A - 1)) := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, hs, smul_add]
        abel
    _ = G := by rw [key, smul_zero, add_zero]

end Generic

section IdemSum

variable {D : D7}

/- English proof (translation)
Rewrite using `[← map_mul, h]`.
-/
theorem isIdem_cA {a : AE D} (h : a * a = a) : cA D a * cA D a = cA D a := by
  rw [← map_mul, h]

/- English proof (translation)
Rewrite using `[← below_of_idemAt h, mul_add, h.1.1, h.1.2.1, add_zero]`.
-/
theorem idemAt_eps {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e PP) :
    e * phiE (belowPl PP) 1 = e := by
  rw [← below_of_idemAt h, mul_add, h.1.1, h.1.2.1, add_zero]

/- English proof (translation)
Establish `h1P : (1 : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun h' => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h')`. Use `not_not.1 (mt (h.2 1 one_ne_zero).2 h1P)` as an intermediate fact. Rewrite `this` using `[show ((1 : 𝓞 D.host.E) : D.host.E)⁻¹ = 1 by simp, map_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem idemAt_int {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e PP) :
    finPart D e ∈ intAE D := by
  have h1P : (1 : 𝓞 D.host.E) ∉ PP.asIdeal := fun h' => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h')
  have := not_not.1 (mt (h.2 1 one_ne_zero).2 h1P)
  rwa [show ((1 : 𝓞 D.host.E) : D.host.E)⁻¹ = 1 by simp, map_one, mul_one] at this

variable {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}

/- English proof (translation)
Introduce `PP hPP PP' hPP'`. Establish `hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0`. Rewrite using `[Finset.sum_product]`. Use `show ∑ x ∈ P, ∑ y ∈ P, es x * cA D (es y) = 0`. Rewrite using `[← Finset.sum_mul_sum, ← map_sum, ← he, hc]`.

Use `idem_sum_zero (K := D.host.F) (P ×ˢ P) (fun x => es x.1 * cA D (es x.2)) ?_ hsum (PP, PP') (Finset.mem_product.2 ⟨hPP, hPP'⟩)` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ hab`. Take `⟨ha, hb⟩` from `Finset.mem_product.1 hab`. Establish `h1` using `(hes a ha).1.1`. Establish `h2` using `isIdem_cA (hes b hb).1.1`.

Use `show (es a * cA D (es b)) * (es a * cA D (es b)) = es a * cA D (es b)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem idemSum_conj_orth (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) : ∀ PP ∈ P, ∀ PP' ∈ P, es PP * cA D (es PP') = 0 := by
  intro PP hPP PP' hPP'
  have hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0 := by
    rw [Finset.sum_product]
    show ∑ x ∈ P, ∑ y ∈ P, es x * cA D (es y) = 0
    rw [← Finset.sum_mul_sum, ← map_sum, ← he, hc]
  refine idem_sum_zero (K := D.host.F) (P ×ˢ P) (fun x => es x.1 * cA D (es x.2)) ?_ hsum (PP, PP')
    (Finset.mem_product.2 ⟨hPP, hPP'⟩)
  rintro ⟨a, b⟩ hab
  obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
  have h1 := (hes a ha).1.1
  have h2 := isIdem_cA (hes b hb).1.1
  show (es a * cA D (es b)) * (es a * cA D (es b)) = es a * cA D (es b)
  calc (es a * cA D (es b)) * (es a * cA D (es b)) = (es a * es a) * (cA D (es b) * cA D (es b)) := by ring
    _ = _ := by rw [h1, h2]

/- English proof (translation)
Establish `ho` using `idemSum_conj_orth hes he hc`. Establish `ha` using `hes PP hPP`. Establish `hb` using `hes PP' hPP'`. Establish `hsa` using `below_of_idemAt ha`. Establish `hsb` using `below_of_idemAt hb`.

Establish `h1 : es PP = es PP * es PP'`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : es PP' = es PP * es PP'`. Combine the equalities or inequalities in the displayed calculation. Establish `hab : es PP = es PP'` using `h1.trans h2.symm`.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Distinguish the cases in `hx0 : x = 0`. Substitute `hx0` using the available equality. Simplify using `only [zero_mem]`.

Rewrite using `[ha.2 x hx0, hb.2 x hx0, hab]`.
-/
theorem idemSum_below_inj (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) (hPP' : PP' ∈ P)
    (hv : belowPl PP = belowPl PP') : PP = PP' := by
  have ho := idemSum_conj_orth hes he hc
  have ha := hes PP hPP
  have hb := hes PP' hPP'
  have hsa := below_of_idemAt ha
  have hsb := below_of_idemAt hb
  have h1 : es PP = es PP * es PP' := by
    calc es PP = es PP * phiE (belowPl PP) 1 := (idemAt_eps ha).symm
      _ = es PP * (es PP' + cA D (es PP')) := by rw [hsb, hv]
      _ = es PP * es PP' := by rw [mul_add, ho PP hPP PP' hPP', add_zero]
  have h2 : es PP' = es PP * es PP' := by
    calc es PP' = es PP' * phiE (belowPl PP') 1 := (idemAt_eps hb).symm
      _ = es PP' * (es PP + cA D (es PP)) := by rw [hsa, hv]
      _ = es PP * es PP' := by rw [mul_add, ho PP' hPP' PP hPP, add_zero, mul_comm]
  have hab : es PP = es PP' := h1.trans h2.symm
  apply HeightOneSpectrum.ext
  ext x
  by_cases hx0 : x = 0
  · subst hx0; simp only [zero_mem]
  rw [ha.2 x hx0, hb.2 x hx0, hab]

/- English proof (translation)
Establish `hv : belowPl PP ≠ belowPl PP'` using `fun hv => hne (idemSum_below_inj hes he hc hPP hPP' hv)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[idemAt_eps (hes PP hPP), idemAt_eps (hes PP' hPP')]`. Use `_ = es PP * es PP' * (phiE (belowPl PP) 1 * phiE (belowPl PP') 1) := by ring`. Use `_ = 0 := by rw [phiE_orth hv, mul_zero]`.
-/
theorem idemSum_orth (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) (hPP' : PP' ∈ P) (hne : PP ≠ PP') :
    es PP * es PP' = 0 := by
  have hv : belowPl PP ≠ belowPl PP' := fun hv => hne (idemSum_below_inj hes he hc hPP hPP' hv)
  calc es PP * es PP' = (es PP * phiE (belowPl PP) 1) * (es PP' * phiE (belowPl PP') 1) := by
        rw [idemAt_eps (hes PP hPP), idemAt_eps (hes PP' hPP')]
    _ = es PP * es PP' * (phiE (belowPl PP) 1 * phiE (belowPl PP') 1) := by ring
    _ = 0 := by rw [phiE_orth hv, mul_zero]

/- English proof (translation)
Rewrite using `[he, Finset.mul_sum, Finset.sum_eq_single PP]`. Conclude with `(hes PP hPP).1.1`. Introduce `PP' hPP' hne`. Conclude with `idemSum_orth hes he hc hPP hPP' (Ne.symm hne)`. Introduce `h`.

Conclude with `absurd hPP h`.
-/
theorem idemSum_mul_mem (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) : es PP * e = es PP := by
  rw [he, Finset.mul_sum, Finset.sum_eq_single PP]
  · exact (hes PP hPP).1.1
  · intro PP' hPP' hne
    exact idemSum_orth hes he hc hPP hPP' (Ne.symm hne)
  · intro h
    exact absurd hPP h

/- English proof (translation)
Take `⟨⟨es, hes, he⟩, hc⟩` from `h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem idemSum_sq (h : IsIdemSum e P) : e * e = e := by
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  calc e * e = (∑ PP ∈ P, es PP) * e := by rw [← he]
    _ = ∑ PP ∈ P, es PP * e := by rw [Finset.sum_mul]
    _ = ∑ PP ∈ P, es PP := Finset.sum_congr rfl (fun PP hPP => idemSum_mul_mem hes he hc hPP)
    _ = e := he.symm

/- English proof (translation)
Establish `hsq` using `idemSum_sq h`. Take `⟨⟨es, hes, he⟩, hc⟩` from `h`. Establish `hinj : Function.Injective (algebraMap (AF D.host.F) (AE D))`. Establish `h0` using `Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := AF D.host.F) (A := AF D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective`. Introduce `a b hab`.

Apply `h0` to reduce the goal to its premises. Simplify `hab` using `[Algebra.TensorProduct.algebraMap_apply]`. Use `choose! v ε hpl hε using fun PP (hPP : PP ∈ P) => (hes PP hPP).1.2.2`. Establish `hsum : algebraMap (AF D.host.F) (AE D) (∑ PP ∈ P, ε PP) = e + cA D e`. Rewrite using `[map_sum, he, map_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl (fun PP hPP => (hε PP hPP).symm)`. Use `⟨∑ PP ∈ P, ε PP, ?_, hsum⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hsum]`. Establish `h3 : cA D e * cA D e = cA D e` using `isIdem_cA hsq`.

Take the linear combination `hsq + 2 * hc + h3`.
-/
theorem idemSum_eps (h : IsIdemSum e P) :
    ∃ εP : AF D.host.F, IsIdempotentElem εP ∧ algebraMap (AF D.host.F) (AE D) εP = e + cA D e := by
  have hsq := idemSum_sq h
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) := by
    have h0 := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := AF D.host.F)
      (A := AF D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    intro a b hab
    apply h0
    simpa [Algebra.TensorProduct.algebraMap_apply] using hab
  choose! v ε hpl hε using fun PP (hPP : PP ∈ P) => (hes PP hPP).1.2.2
  have hsum : algebraMap (AF D.host.F) (AE D) (∑ PP ∈ P, ε PP) = e + cA D e := by
    rw [map_sum, he, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun PP hPP => (hε PP hPP).symm)
  refine ⟨∑ PP ∈ P, ε PP, ?_, hsum⟩
  apply hinj
  rw [map_mul, hsum]
  have h3 : cA D e * cA D e = cA D e := isIdem_cA hsq
  linear_combination hsq + 2 * hc + h3

end IdemSum

section Res

variable {D : D7}

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`. Simplify using `[cA, sigR]`.
-/
theorem cA_alg (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [cA, sigR]

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem mtG_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul]
  rfl

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem mtG_one (V : HSp D) : mt V (1 : GA D V) = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one]
  rfl

/- English proof (translation)
Rewrite using `[← mtG_mul, mul_inv_cancel, mtG_one]`.
-/
theorem mtG_inv (V : HSp D) (a : GA D V) : mt V a * mt V a⁻¹ = 1 := by
  rw [← mtG_mul, mul_inv_cancel, mtG_one]

/- English proof (translation)
Rewrite using `[← mtG_mul, inv_mul_cancel, mtG_one]`.
-/
theorem mtG_inv' (V : HSp D) (a : GA D V) : mt V a⁻¹ * mt V a = 1 := by
  rw [← mtG_mul, inv_mul_cancel, mtG_one]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Units.ext h`.
-/
theorem gaExt {V : HSp D} {a b : GA D V} (h : mt V a = mt V b) : a = b := by
  apply Subtype.ext
  exact Units.ext h

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem mtG_unitary (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2

def mkRes (V : HSp D) (ε : AF D.host.F) (hε : IsIdempotentElem ε) (g : GA D V) : GA D V :=
    have hs : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε =
        algebraMap (AF D.host.F) (AE D) ε := by rw [← map_mul, hε.eq]
    let g' : HR (AF D.host.F) D.sp.cm.sig V.gram :=
      ⟨⟨resM (algebraMap (AF D.host.F) (AE D) ε) (mt V g), resM (algebraMap (AF D.host.F) (AE D) ε) (mt V g⁻¹),
        by rw [resM_mul hs, mtG_inv, resM_one_right], by rw [resM_mul hs, mtG_inv', resM_one_right]⟩, by
        show ((resM (algebraMap (AF D.host.F) (AE D) ε) (mt V g)).map (cA D))ᵀ * V.gram.map (incA D) *
          resM (algebraMap (AF D.host.F) (AE D) ε) (mt V g) = V.gram.map (incA D)
        rw [resM_map, resM_transpose, cA_alg]
        exact resM_unitary hs _ _ _ (mtG_unitary V g)⟩
    g'

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mkRes (V : HSp D) (ε : AF D.host.F) (hε : IsIdempotentElem ε) (g : GA D V) :
    mt V (mkRes V ε hε g) = resM (algebraMap (AF D.host.F) (AE D) ε) (mt V g) := rfl

open Classical in

def resG (V : HSp D) (ε : AF D.host.F) (g : GA D V) : GA D V :=
  if hε : IsIdempotentElem ε then mkRes V ε hε g else g

variable (V : HSp D) {ε ε' : AF D.host.F}

/- English proof (translation)
Simplify using `only [resG, dif_pos hε]`. Conclude with `mt_mkRes V ε hε g`.
-/
theorem mt_resG (hε : IsIdempotentElem ε) (g : GA D V) :
    mt V (resG V ε g) = resM (algebraMap (AF D.host.F) (AE D) ε) (mt V g) := by
  simp only [resG, dif_pos hε]
  exact mt_mkRes V ε hε g

/- English proof (translation)
Rewrite using `[← map_mul, hε.eq]`.
-/
theorem algIdem (hε : IsIdempotentElem ε) :
    algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
  rw [← map_mul, hε.eq]

/- English proof (translation)
Apply `gaExt` to reduce the goal to its premises. Simplify using `only [mt_resG V hε, mtG_mul, resM_mul (algIdem hε)]`.
-/
theorem resG_mul (hε : IsIdempotentElem ε) (g g' : GA D V) : resG V ε (g * g') = resG V ε g * resG V ε g' := by
  apply gaExt
  simp only [mt_resG V hε, mtG_mul, resM_mul (algIdem hε)]

/- English proof (translation)
Apply `gaExt` to reduce the goal to its premises. Rewrite using `[mt_resG V IsIdempotentElem.one, map_one, resM_one_left]`.
-/
theorem resG_one_eps (g : GA D V) : resG V 1 g = g := by
  apply gaExt
  rw [mt_resG V IsIdempotentElem.one, map_one, resM_one_left]

/- English proof (translation)
Apply `gaExt` to reduce the goal to its premises. Rewrite using `[mt_resG V IsIdempotentElem.zero, map_zero, resM_zero_left, mtG_one]`.
-/
theorem resG_zero_eps (g : GA D V) : resG V 0 g = 1 := by
  apply gaExt
  rw [mt_resG V IsIdempotentElem.zero, map_zero, resM_zero_left, mtG_one]

/- English proof (translation)
Apply `gaExt` to reduce the goal to its premises. Rewrite using `[mt_resG V hε, mtG_one, resM_one_right]`.
-/
theorem resG_one (hε : IsIdempotentElem ε) : resG V ε 1 = 1 := by
  apply gaExt
  rw [mt_resG V hε, mtG_one, resM_one_right]

/- English proof (translation)
Use `show (ε + ε') * (ε + ε') = ε + ε'`. Establish `h1` using `hε.eq`. Establish `h2` using `hε'.eq`. Take the linear combination `h1 + h2 + 2 * h`.
-/
theorem isIdem_add_orth (hε : IsIdempotentElem ε) (hε' : IsIdempotentElem ε') (h : ε * ε' = 0) :
    IsIdempotentElem (ε + ε') := by
  show (ε + ε') * (ε + ε') = ε + ε'
  have h1 := hε.eq
  have h2 := hε'.eq
  linear_combination h1 + h2 + 2 * h

/- English proof (translation)
Apply `gaExt` to reduce the goal to its premises. Establish `hst : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε' = 0`. Rewrite using `[← map_mul, h, map_zero]`. Rewrite using `[mtG_mul, mt_resG V hε, mt_resG V hε', mt_resG V (isIdem_add_orth hε hε' h), map_add, resM_add hst]`.
-/
theorem resG_orth (hε : IsIdempotentElem ε) (hε' : IsIdempotentElem ε') (h : ε * ε' = 0) (g : GA D V) :
    resG V ε g * resG V ε' g = resG V (ε + ε') g := by
  apply gaExt
  have hst : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε' = 0 := by
    rw [← map_mul, h, map_zero]
  rw [mtG_mul, mt_resG V hε, mt_resG V hε', mt_resG V (isIdem_add_orth hε hε' h), map_add, resM_add hst]

/- English proof (translation)
Apply `gaExt` to reduce the goal to its premises. Establish `hst : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε' = 0`. Rewrite using `[← map_mul, h, map_zero]`. Establish `hts : algebraMap (AF D.host.F) (AE D) ε' * algebraMap (AF D.host.F) (AE D) ε = 0`. Rewrite using `[mul_comm, hst]`.

Rewrite using `[mtG_mul, mtG_mul]`. Simplify using `only [mt_resG V hε, mt_resG V hε']`. Rewrite using `[resM_orth hst, resM_orth hts]`. Normalize the expressions using the abelian group laws.
-/
theorem resG_comm (hε : IsIdempotentElem ε) (hε' : IsIdempotentElem ε') (h : ε * ε' = 0) (g g' : GA D V) :
    resG V ε g * resG V ε' g' = resG V ε' g' * resG V ε g := by
  apply gaExt
  have hst : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε' = 0 := by
    rw [← map_mul, h, map_zero]
  have hts : algebraMap (AF D.host.F) (AE D) ε' * algebraMap (AF D.host.F) (AE D) ε = 0 := by
    rw [mul_comm, hst]
  rw [mtG_mul, mtG_mul]
  simp only [mt_resG V hε, mt_resG V hε']
  rw [resM_orth hst, resM_orth hts]
  abel

/- English proof (translation)
Establish `h0 : ε * (1 - ε) = 0` using `by rw [mul_sub, mul_one, hε.eq, sub_self]`. Establish `h1 : ε + (1 - ε) = 1` using `by ring`. Rewrite using `[resG_orth V hε hε.one_sub h0 g, h1, resG_one_eps]`.
-/
theorem resG_compl (hε : IsIdempotentElem ε) (g : GA D V) : resG V ε g * resG V (1 - ε) g = g := by
  have h0 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε.eq, sub_self]
  have h1 : ε + (1 - ε) = 1 := by ring
  rw [resG_orth V hε hε.one_sub h0 g, h1, resG_one_eps]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Unfold `GfC at hg ⊢`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`. Establish `key : ∀ x : GA D V, ((infHom V x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) = (mt V x).map (infPart D)` using `fun x => rfl`. Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : (mt V g).map (infPart D) = 1` using `by rw [← key, hg, Units.val_one]`.

Rewrite using `[key, Units.val_one, mt_resG V hε, resM_map, h1, resM_one_right]`.
-/
theorem resG_mem_GfC (hε : IsIdempotentElem ε) {g : GA D V} (hg : g ∈ GfC V) : resG V ε g ∈ GfC V := by
  unfold GfC at hg ⊢
  rw [MonoidHom.mem_ker] at hg ⊢
  have key : ∀ x : GA D V, ((infHom V x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) = (mt V x).map (infPart D) :=
    fun x => rfl
  apply Units.ext
  have h1 : (mt V g).map (infPart D) = 1 := by rw [← key, hg, Units.val_one]
  rw [key, Units.val_one, mt_resG V hε, resM_map, h1, resM_one_right]

/- English proof (translation)
Introduce `i j`. Rewrite using `[he, mt_resG V hε, resM, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, algIdem hε]`.
-/
theorem suppAt_resG (hε : IsIdempotentElem ε) (g : GA D V) {e : AE D}
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SuppAt e V (resG V ε g) := by
  intro i j
  rw [he, mt_resG V hε, resM, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, algIdem hε]

end Res

section Fin

variable {D : D7} (V : HSp D) {ε : AF D.host.F}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finE_val (g : GA D V) :
    ((Lev.finE V g : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) =
      (mt V g).map (toEAf D) := rfl

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`. Simplify using `[toEAf, finPart]`.
-/
theorem toEAf_alg (a : AF D.host.F) :
    toEAf D (algebraMap (AF D.host.F) (AE D) a) = (1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F a := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [toEAf, finPart]

/- English proof (translation)
Introduce `v`. Establish `h : IsIdempotentElem (evalV D.host.F v (sndA D.host.F ε))` using `by show _ * _ = _`. Rewrite using `[← map_mul, ← map_mul, hε.eq]`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 h with h0 | h1` into its components or cases. Use `show evalV D.host.F v (sndA D.host.F ε) ∈ _`.

Rewrite using `[h0]`. Conclude with `zero_mem _`. Use `show evalV D.host.F v (sndA D.host.F ε) ∈ _`. Rewrite using `[h1]`. Conclude with `one_mem _`.
-/
theorem sndA_idem_int (hε : IsIdempotentElem ε) : sndA D.host.F ε ∈ Formalism.UG.intAd D.host.F := by
  intro v
  have h : IsIdempotentElem (evalV D.host.F v (sndA D.host.F ε)) := by
    show _ * _ = _
    rw [← map_mul, ← map_mul, hε.eq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 h with h0 | h1
  · show evalV D.host.F v (sndA D.host.F ε) ∈ _
    rw [h0]; exact zero_mem _
  · show evalV D.host.F v (sndA D.host.F ε) ∈ _
    rw [h1]; exact one_mem _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frGL_val' {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    ((Formalism.L2.DIV.frGL β y : GL (Fin n) (Lev.EAf D)) : Matrix (Fin n) (Fin n) (Lev.EAf D)) =
      (β : Matrix (Fin n) (Fin n) (Lev.EAf D)) *
        (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map
          (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
        ((β⁻¹ : GL (Fin n) (Lev.EAf D)) : Matrix (Fin n) (Fin n) (Lev.EAf D)) := rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨y, hy⟩` from `hg`. Take `⟨α, hαv⟩ : ∃ α : Formalism.L2.Herm.intAf D.host.F D.host.E, (α : Lev.EAf D) = (1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε` from `⟨Formalism.L2.DIV.adS D.host.F D.host.E ⟨sndA D.host.F ε, sndA_idem_int hε⟩, rfl⟩`. Establish `hα : α * α = α` using `Subtype.ext (by show (α : Lev.EAf D) * α = α`. Rewrite using `[hαv, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul, hε.eq])`. Use `⟨⟨resM α (y : Matrix _ _ _), resM α ((y⁻¹ : GL _ _) : Matrix _ _ _), by rw [resM_mul hα, Units.mul_inv, resM_one_right], by rw [resM_mul hα, Units.inv_mul, resM_one_right]⟩, ?_⟩` and prove the remaining obligations.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[frGL_val']`. Establish `hsub : (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype α = (1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε` using `hαv`. Establish `hy' : (β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf …`. Rewrite using `[← frGL_val', hy, finE_val]`.

Establish `hββ : (β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[resM_map, resM_conj _ _ _ _ hββ, hy', hsub, finE_val, mt_resG V hε, resM_map, toEAf_alg]`.
-/
theorem finE_resG_mem_St (hε : IsIdempotentElem ε) {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) : Lev.finE V (resG V ε g) ∈ Formalism.L2.DIV.St β := by
  obtain ⟨y, hy⟩ := hg
  obtain ⟨α, hαv⟩ : ∃ α : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (α : Lev.EAf D) = (1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε :=
    ⟨Formalism.L2.DIV.adS D.host.F D.host.E ⟨sndA D.host.F ε, sndA_idem_int hε⟩, rfl⟩
  have hα : α * α = α := Subtype.ext (by
    show (α : Lev.EAf D) * α = α
    rw [hαv, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul, hε.eq])
  refine ⟨⟨resM α (y : Matrix _ _ _), resM α ((y⁻¹ : GL _ _) : Matrix _ _ _),
    by rw [resM_mul hα, Units.mul_inv, resM_one_right], by rw [resM_mul hα, Units.inv_mul, resM_one_right]⟩, ?_⟩
  apply Units.ext
  rw [frGL_val']
  have hsub : (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype α = (1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε := hαv
  have hy' : (β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) *
      (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
      ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) = (mt V g).map (toEAf D) := by
    rw [← frGL_val', hy, finE_val]
  have hββ : (β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) *
      ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [resM_map, resM_conj _ _ _ _ hββ, hy', hsub, finE_val, mt_resG V hε, resM_map, toEAf_alg]

/- English proof (translation)
Use `Formalism.L2.DIV.reduction_local D.host.F D.host.E V.rank β PP v hv _ (finE_resG_mem_St V hε hg) ?_` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `show ((Lev.finE V (resG V ε g) : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)).map (Formalism.UG.prV (E := D.host.E) v) = 1`. Rewrite using `[finE_val, mt_resG V hε, resM_map, resM_map, toEAf_alg]`. Establish `hp : Formalism.UG.prV (E` using `D.host.E) v ((1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε) = 0 := by show (Algebra.TensorProduct.map (AlgHom.id D.host.F D.host.E) (Formalism.UG.evalV D.host.F v)) ((1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε) = 0`.

Rewrite using `[Algebra.TensorProduct.map_tmul]`. Establish `: Formalism.UG.evalV D.host.F v (sndA D.host.F ε) = 0` using `h0`. Rewrite using `[this, TensorProduct.tmul_zero]`. Rewrite using `[hp, resM_zero_left]`.
-/
theorem redFn_resG_zero (hε : IsIdempotentElem ε) {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) {PP : Formalism.L2.DIV.Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)))
    (h0 : evalV D.host.F v (sndA D.host.F ε) = 0) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V ε g)) = 1 := by
  refine Formalism.L2.DIV.reduction_local D.host.F D.host.E V.rank β PP v hv _ (finE_resG_mem_St V hε hg) ?_
  apply Units.ext
  show ((Lev.finE V (resG V ε g) : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)).map
    (Formalism.UG.prV (E := D.host.E) v) = 1
  rw [finE_val, mt_resG V hε, resM_map, resM_map, toEAf_alg]
  have hp : Formalism.UG.prV (E := D.host.E) v ((1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε) = 0 := by
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F D.host.E) (Formalism.UG.evalV D.host.F v))
      ((1 : D.host.E) ⊗ₜ[D.host.F] sndA D.host.F ε) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : Formalism.UG.evalV D.host.F v (sndA D.host.F ε) = 0 := h0
    rw [this, TensorProduct.tmul_zero]
  rw [hp, resM_zero_left]

/- English proof (translation)
Establish `h1' : evalV D.host.F v (sndA D.host.F (1 - ε)) = 0` using `by rw [map_sub, map_one, map_sub, map_one, h1, sub_self]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[redFn_resG_zero V hε.one_sub hg hv h1', mul_one]`. Use `_ = Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V ε g) * Lev.finE V (resG V (1 - ε) g)) := (Formalism.L2.DIV.redFn_mul (finE_resG_mem_St V hε hg) (finE_resG_mem_St V hε.one_sub hg) PP).symm`. Use `_ = Formalism.L2.DIV.redFn β PP (Lev.finE V g) := by rw [← map_mul, resG_compl V hε]`.
-/
theorem redFn_resG_one (hε : IsIdempotentElem ε) {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) {PP : Formalism.L2.DIV.Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)))
    (h1 : evalV D.host.F v (sndA D.host.F ε) = 1) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V ε g)) = Formalism.L2.DIV.redFn β PP (Lev.finE V g) := by
  have h1' : evalV D.host.F v (sndA D.host.F (1 - ε)) = 0 := by rw [map_sub, map_one, map_sub, map_one, h1, sub_self]
  calc Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V ε g))
        = Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V ε g)) *
          Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V (1 - ε) g)) := by
        rw [redFn_resG_zero V hε.one_sub hg hv h1', mul_one]
    _ = Formalism.L2.DIV.redFn β PP (Lev.finE V (resG V ε g) * Lev.finE V (resG V (1 - ε) g)) :=
        (Formalism.L2.DIV.redFn_mul (finE_resG_mem_St V hε hg) (finE_resG_mem_St V hε.one_sub hg) PP).symm
    _ = Formalism.L2.DIV.redFn β PP (Lev.finE V g) := by rw [← map_mul, resG_compl V hε]

end Fin

section Det

variable {D : D7}

open Classical in

def detAt (e : AE D) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  if he : e * e = e then
    ⟨e * (mt V g).det + (1 - e), e * (mt V g⁻¹).det + (1 - e),
      by
        have hd : (mt V g).det * (mt V g⁻¹).det = 1 := by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]
        linear_combination (e * e) * hd + (2 - (mt V g).det - (mt V g⁻¹).det) * he,
      by
        have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by rw [← Matrix.det_mul, mtG_inv', Matrix.det_one]
        linear_combination (e * e) * hd + (2 - (mt V g).det - (mt V g⁻¹).det) * he⟩
  else 1

/- English proof (translation)
Rewrite using `[detAt, dif_pos he]`.
-/
theorem detAt_val {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detAt e V g : (AE D)ˣ) : AE D) = e * (mt V g).det + (1 - e) := by
  rw [detAt, dif_pos he]

/- English proof (translation)
Unfold `IsDetAt`. Conclude with `detAt_val he V g`.
-/
theorem isDetAt_detAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : IsDetAt e V g (detAt e V g) := by
  unfold IsDetAt
  exact detAt_val he V g

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`. Rewrite using `[Algebra.TensorProduct.comm_tmul]`. Establish `hx : (x : D.host.E) ⊗ₜ[D.host.F] a = ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[hx]`. Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`.
-/
theorem comm_mem_intAf {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [Algebra.TensorProduct.comm_tmul]
    have hx : (x : D.host.E) ⊗ₜ[D.host.F] a =
        ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hx]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/- English proof (translation)
The claim follows from `comm_mem_intAf hz`.
-/
theorem toEAf_mem_intAf {z : AE D} (hz : finPart D z ∈ intAE D) : toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  comm_mem_intAf hz

/- English proof (translation)
Establish `hs' : s ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪ Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F)))` using `hs`. Use `clear hs`. Establish `hone : (1 : Af D.host.F) ∈ intAf D.host.F` using `fun v => by rw [map_one]; exact one_mem _`. Proceed by induction on `hs' using Subring.closure_induction with`. Consider the case `mem x hx`.

Break down `hx with ⟨⟨x, y, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩` into its components or cases. Rewrite using `[Algebra.TensorProduct.comm_tmul]`. Conclude with `AddSubgroup.subset_closure ⟨1, hone, y, rfl⟩`. Rewrite using `[Algebra.TensorProduct.comm_tmul]`. Conclude with `AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, by simp⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `one`. Rewrite using `[map_one, Algebra.TensorProduct.one_def]`. Conclude with `AddSubgroup.subset_closure ⟨1, hone, 1, by simp⟩`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `intAE_mul hx hy`.
-/
theorem comm_mem_intAE {s : D.host.E ⊗[D.host.F] Af D.host.F} (hs : s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) s ∈ intAE D := by
  have hs' : s ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
      Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))) := hs
  clear hs
  have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by rw [map_one]; exact one_mem _
  induction hs' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, y, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · rw [Algebra.TensorProduct.comm_tmul]
      exact AddSubgroup.subset_closure ⟨1, hone, y, rfl⟩
    · rw [Algebra.TensorProduct.comm_tmul]
      exact AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, by simp⟩
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [map_one, Algebra.TensorProduct.one_def]
    exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp⟩
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact intAE_mul hx hy

/- English proof (translation)
Establish `hne : PP.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 D.host.E))` using `mem_nonZeroDivisors_of_ne_zero PP.ne_bot`. Set `I : nonZeroDivisors (Ideal (𝓞 D.host.E))` to `⟨PP.asIdeal, hne⟩`. Establish `hn : 0 < Fintype.card (ClassGroup (𝓞 D.host.E))` using `Fintype.card_pos`. Establish `h1 : ClassGroup.mk0 (I ^ Fintype.card (ClassGroup (𝓞 D.host.E))) = 1`. Rewrite using `[map_pow, pow_card_eq_one]`.

Rewrite `h1` using `[ClassGroup.mk0_eq_one_iff]`. Take `⟨⟨π, hπ⟩⟩` from `h1`. Establish `hπ' : PP.asIdeal ^ Fintype.card (ClassGroup (𝓞 D.host.E)) = Ideal.span {π}` using `by first`. Consider the case `exact hπ`. Consider the case `simpa [Ideal.span] using hπ`.

Establish `hpow0 : PP.asIdeal ^ Fintype.card (ClassGroup (𝓞 D.host.E)) ≠ ⊥` using `pow_ne_zero _ PP.ne_bot`. Use `⟨π, ?_, ?_, Fintype.card (ClassGroup (𝓞 D.host.E)) - 1, ?_⟩` and prove the remaining obligations. Apply `Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn)` to reduce the goal to its premises. Rewrite using `[hπ']`. Conclude with `Ideal.subset_span (Set.mem_singleton π)`.

Introduce and unpack `rfl`. Apply `hpow0` to reduce the goal to its premises. Rewrite using `[hπ', Ideal.span_singleton_eq_bot]`. Rewrite using `[Nat.sub_add_cancel hn, hπ']`.
-/
theorem exists_principal_pow (PP : Formalism.L2.DIV.Pl D.host.E) :
    ∃ π : 𝓞 D.host.E, π ∈ PP.asIdeal ∧ π ≠ 0 ∧ ∃ m : ℕ, PP.asIdeal ^ (m + 1) = Ideal.span {π} := by
  classical
  have hne : PP.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 D.host.E)) := mem_nonZeroDivisors_of_ne_zero PP.ne_bot
  let I : nonZeroDivisors (Ideal (𝓞 D.host.E)) := ⟨PP.asIdeal, hne⟩
  have hn : 0 < Fintype.card (ClassGroup (𝓞 D.host.E)) := Fintype.card_pos
  have h1 : ClassGroup.mk0 (I ^ Fintype.card (ClassGroup (𝓞 D.host.E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  rw [ClassGroup.mk0_eq_one_iff] at h1
  obtain ⟨⟨π, hπ⟩⟩ := h1
  have hπ' : PP.asIdeal ^ Fintype.card (ClassGroup (𝓞 D.host.E)) = Ideal.span {π} := by
    first
      | exact hπ
      | simpa [Ideal.span] using hπ
  have hpow0 : PP.asIdeal ^ Fintype.card (ClassGroup (𝓞 D.host.E)) ≠ ⊥ := pow_ne_zero _ PP.ne_bot
  refine ⟨π, ?_, ?_, Fintype.card (ClassGroup (𝓞 D.host.E)) - 1, ?_⟩
  · apply Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn)
    rw [hπ']
    exact Ideal.subset_span (Set.mem_singleton π)
  · rintro rfl
    apply hpow0
    rw [hπ', Ideal.span_singleton_eq_bot]
  · rw [Nat.sub_add_cancel hn, hπ']

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem comm_comm (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F))
      ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hidem : e' * e' = e'` using `Subtype.ext (by show (e' : Lev.EAf D) * e' = e'`. Rewrite using `[he', ← map_mul, hPP.1.1])`. Use `haveI : PP.asIdeal.IsPrime := PP.isPrime`. Establish `hI : IsIdempotentElem (Formalism.L2.DIV.resS D.host.F PP e')` using `by show _ * _ = _`. Rewrite using `[← map_mul, hidem]`.

Break down `IsIdempotentElem.iff_eq_zero_or_one.1 hI with h0 | h1` into its components or cases. It suffices to derive a contradiction. Take `⟨π, hπPP, hπ0, m, hπ⟩` from `exists_principal_pow PP`. Establish `hmem : e' ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal` using `(Formalism.L2.DIV.resS_eq_zero_iff PP e').1 h0`. Establish `hpow : e' ∈ Ideal.span {Formalism.L2.DIV.oToS D.host.F D.host.E π}`.

Establish `h2 : e' ^ (m + 1) ∈ (Formalism.L2.DIV.idS D.host.F PP.asIdeal) ^ (m + 1)` using `Ideal.pow_mem_pow hmem (m + 1)`. Establish `h3 : e' ^ (m + 1) = e'` using `IsIdempotentElem.pow_succ_eq m hidem`. Rewrite `h2` using `[h3]`. Unfold `Formalism.L2.DIV.idS at h2`. Rewrite `h2` using `[← Ideal.map_pow, hπ, Ideal.map_span, Set.image_singleton]`. Then use the resulting hypothesis.

Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 hpow`. Apply `(hPP.2 π hπ0).1 hπPP` to reduce the goal to its premises. Establish `hsv : (s : D.host.E ⊗[D.host.F] Af D.host.F) * ((π : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) = toEAf D e`. Use `congrArg (fun x : Formalism.L2.Herm.intAf D.host.F D.host.E => (x : D.host.E ⊗[D.host.F] Af D.host.F)) hs` as an intermediate fact. Rewrite using `[← he']`.

Conclude with `this`. Establish `hπE : (π : D.host.E) ≠ 0`. Introduce `h; apply hπ0; exact FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by rw [map_zero]; exact h)`. Establish `hfe : finPart D e = (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (toEAf D e)` using `(comm_comm _).symm`. Establish `key : finPart D (e * incA D ((π : D.host.E)⁻¹)) = (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (s : D.host.E ⊗[D.host.F] Af D.host.F)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, Algebra.TensorProduct.comm_tmul, mul_assoc]`. Use `_ = _ := by`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hπE, ← Algebra.TensorProduct.one_def, mul_one]`. Rewrite using `[key]`.

Conclude with `comm_mem_intAE s.2`. Conclude with `h1`.
-/
theorem resS_idemAt' {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : Formalism.L2.NTheta.IsIdemAt e PP)
    (e' : Formalism.L2.Herm.intAf D.host.F D.host.E) (he' : (e' : Lev.EAf D) = toEAf D e) :
    Formalism.L2.DIV.resS D.host.F PP e' = 1 := by
  classical
  have hidem : e' * e' = e' := Subtype.ext (by
    show (e' : Lev.EAf D) * e' = e'
    rw [he', ← map_mul, hPP.1.1])
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have hI : IsIdempotentElem (Formalism.L2.DIV.resS D.host.F PP e') := by
    show _ * _ = _
    rw [← map_mul, hidem]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hI with h0 | h1
  · exfalso
    obtain ⟨π, hπPP, hπ0, m, hπ⟩ := exists_principal_pow PP
    have hmem : e' ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := (Formalism.L2.DIV.resS_eq_zero_iff PP e').1 h0
    have hpow : e' ∈ Ideal.span {Formalism.L2.DIV.oToS D.host.F D.host.E π} := by
      have h2 : e' ^ (m + 1) ∈ (Formalism.L2.DIV.idS D.host.F PP.asIdeal) ^ (m + 1) := Ideal.pow_mem_pow hmem (m + 1)
      have h3 : e' ^ (m + 1) = e' := IsIdempotentElem.pow_succ_eq m hidem
      rw [h3] at h2
      unfold Formalism.L2.DIV.idS at h2
      rwa [← Ideal.map_pow, hπ, Ideal.map_span, Set.image_singleton] at h2
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hpow
    apply (hPP.2 π hπ0).1 hπPP
    have hsv : (s : D.host.E ⊗[D.host.F] Af D.host.F) * ((π : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) =
        toEAf D e := by
      have := congrArg (fun x : Formalism.L2.Herm.intAf D.host.F D.host.E => (x : D.host.E ⊗[D.host.F] Af D.host.F)) hs
      rw [← he']
      exact this
    have hπE : (π : D.host.E) ≠ 0 := by
      intro h; apply hπ0; exact FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E (by rw [map_zero]; exact h)
    have hfe : finPart D e = (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (toEAf D e) :=
      (comm_comm _).symm
    have key : finPart D (e * incA D ((π : D.host.E)⁻¹)) =
        (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (s : D.host.E ⊗[D.host.F] Af D.host.F) := by
      calc finPart D (e * incA D ((π : D.host.E)⁻¹))
          = finPart D e * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (π : D.host.E)⁻¹) := by rw [map_mul, finPart_incA]
        _ = (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F))
              ((s : D.host.E ⊗[D.host.F] Af D.host.F) * ((π : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) *
            ((1 : Af D.host.F) ⊗ₜ[D.host.F] (π : D.host.E)⁻¹) := by rw [hfe, hsv]
        _ = (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (s : D.host.E ⊗[D.host.F] Af D.host.F) *
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (π : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (π : D.host.E)⁻¹)) := by
            rw [map_mul, Algebra.TensorProduct.comm_tmul, mul_assoc]
        _ = _ := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hπE, ← Algebra.TensorProduct.one_def,
              mul_one]
    rw [key]
    exact comm_mem_intAE s.2
  · exact h1

/- English proof (translation)
The claim follows from `resS_idemAt' hPP _ rfl`.
-/
theorem resS_idemAt {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : Formalism.L2.NTheta.IsIdemAt e PP) :
    Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, toEAf_mem_intAf (idemAt_int hPP)⟩ = 1 :=
  resS_idemAt' hPP _ rfl

/- English proof (translation)
Use `⟨⟨e' * d + (1 - e'), e' * ((d⁻¹ : Rˣ) : R) + (1 - e'), ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hd : (d : R) * ((d⁻¹ : Rˣ) : R) = 1` using `Units.mul_inv d`. Take the linear combination `(e' * e') * hd + (2 - (d : R) - ((d⁻¹ : Rˣ) : R)) * he`. Establish `hd : ((d⁻¹ : Rˣ) : R) * (d : R) = 1` using `Units.inv_mul d`. Take the linear combination `(e' * e') * hd + (2 - (d : R) - ((d⁻¹ : Rˣ) : R)) * he`.
-/
theorem idemUnit_exists {R : Type*} [CommRing R] (e' : R) (he : e' * e' = e') (d : Rˣ) :
    ∃ u : Rˣ, (u : R) = e' * d + (1 - e') := by
  refine ⟨⟨e' * d + (1 - e'), e' * ((d⁻¹ : Rˣ) : R) + (1 - e'), ?_, ?_⟩, rfl⟩
  · have hd : (d : R) * ((d⁻¹ : Rˣ) : R) = 1 := Units.mul_inv d
    linear_combination (e' * e') * hd + (2 - (d : R) - ((d⁻¹ : Rˣ) : R)) * he
  · have hd : ((d⁻¹ : Rˣ) : R) * (d : R) = 1 := Units.inv_mul d
    linear_combination (e' * e') * hd + (2 - (d : R) - ((d⁻¹ : Rˣ) : R)) * he

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨y, hy⟩` from `hg`. Establish `he` using `hPP.1.1`. Take `⟨e', he'⟩ : ∃ e' : Formalism.L2.Herm.intAf D.host.F D.host.E, (e' : Lev.EAf D) = toEAf D e` from `⟨⟨toEAf D e, toEAf_mem_intAf (idemAt_int hPP)⟩, rfl⟩`. Establish `hidem : e' * e' = e'` using `Subtype.ext (by show (e' : Lev.EAf D) * e' = e'`. Rewrite using `[he', ← map_mul, he])`.

Take `⟨d, hd⟩ : ∃ d : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ, d = Matrix.GeneralLinearGroup.det y` from `⟨_, rfl⟩`. Take `⟨u, hu⟩` from `idemUnit_exists e' hidem d`. Establish `hx1 : (1 - e) * ((detAt e V g : (AE D)ˣ) : AE D) = 1 - e`. Rewrite using `[detAt_val he]`. Take the linear combination `(1 - (mt V g).det) * he`.

Establish `hdet : toEAf D (mt V g).det = ((d : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)`. Establish `h1 : toEAf D (mt V g).det = ((Lev.finE V g : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)).det`. Rewrite using `[finE_val, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[h1, ← hy]`.

Use `show ((β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf …`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul, hd]`. Conclude with `(RingHom.map_det (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype _).symm`. Establish `hxu : toEAf D ((detAt e V g : (AE D)ˣ) : AE D) = (((u : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)`. Rewrite using `[detAt_val he, map_add, map_mul, map_sub, map_one, hdet, ← he', hu]`.

Both sides reduce to the same expression. Establish `hU : Units.map (Formalism.L2.DIV.resS D.host.F PP).toMonoidHom u = Matrix.GeneralLinearGroup.det (Formalism.L2.DIV.redFn β PP (Lev.finE V g))`. Apply `Units.ext` to reduce the goal to its premises. Use `show Formalism.L2.DIV.resS D.host.F PP (u : Formalism.L2.Herm.intAf D.host.F D.host.E) = _`. Rewrite using `[hu]`.

Use `show Formalism.L2.DIV.resS D.host.F PP (e' * d + (1 - e')) = (Formalism.L2.DIV.redFn β PP (Lev.finE V g) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)).det`. Rewrite using `[map_add, map_mul, map_sub, map_one, resS_idemAt' hPP e' he', one_mul, sub_self, add_zero, ← hy, Formalism.L2.DIV.redFn_frGL, hd]`. Conclude with `RingHom.map_det (Formalism.L2.DIV.resS D.host.F PP) _`. Rewrite using `[hT (detAt e V g) u hx1 hxu, hU]`.
-/
theorem tame_detAt {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : Formalism.L2.NTheta.IsIdemAt e PP) (V : HSp D)
    {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)} (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) {χ : (AE D)ˣ →* Circle}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {k : ℤ} (hT : TameAt e PP χ c k) :
    ((χ (detAt e V g) : Circle) : ℂ) =
      ((c (Matrix.GeneralLinearGroup.det (Formalism.L2.DIV.redFn β PP (Lev.finE V g))) : ℂˣ) : ℂ) ^ k := by
  obtain ⟨y, hy⟩ := hg
  have he := hPP.1.1
  obtain ⟨e', he'⟩ : ∃ e' : Formalism.L2.Herm.intAf D.host.F D.host.E, (e' : Lev.EAf D) = toEAf D e :=
    ⟨⟨toEAf D e, toEAf_mem_intAf (idemAt_int hPP)⟩, rfl⟩
  have hidem : e' * e' = e' := Subtype.ext (by
    show (e' : Lev.EAf D) * e' = e'
    rw [he', ← map_mul, he])
  obtain ⟨d, hd⟩ : ∃ d : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ, d = Matrix.GeneralLinearGroup.det y := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := idemUnit_exists e' hidem d
  have hx1 : (1 - e) * ((detAt e V g : (AE D)ˣ) : AE D) = 1 - e := by
    rw [detAt_val he]; linear_combination (1 - (mt V g).det) * he

  have hdet : toEAf D (mt V g).det = ((d : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
    have h1 : toEAf D (mt V g).det =
        ((Lev.finE V g : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)).det := by
      rw [finE_val, RingHom.map_det]; rfl
    rw [h1, ← hy]
    show ((β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) *
      (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
      ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D))).det = _
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.det_one, one_mul, hd]
    exact (RingHom.map_det (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype _).symm
  have hxu : toEAf D ((detAt e V g : (AE D)ˣ) : AE D) =
      (((u : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D) := by
    rw [detAt_val he, map_add, map_mul, map_sub, map_one, hdet, ← he', hu]
    rfl
  have hU : Units.map (Formalism.L2.DIV.resS D.host.F PP).toMonoidHom u =
      Matrix.GeneralLinearGroup.det (Formalism.L2.DIV.redFn β PP (Lev.finE V g)) := by
    apply Units.ext
    show Formalism.L2.DIV.resS D.host.F PP (u : Formalism.L2.Herm.intAf D.host.F D.host.E) = _
    rw [hu]
    show Formalism.L2.DIV.resS D.host.F PP (e' * d + (1 - e')) = (Formalism.L2.DIV.redFn β PP (Lev.finE V g) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)).det
    rw [map_add, map_mul, map_sub, map_one, resS_idemAt' hPP e' he', one_mul,
      sub_self, add_zero, ← hy,
      Formalism.L2.DIV.redFn_frGL, hd]
    exact RingHom.map_det (Formalism.L2.DIV.resS D.host.F PP) _
  rw [hT (detAt e V g) u hx1 hxu, hU]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨d, hd⟩ : ∃ d : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ, d = Matrix.GeneralLinearGroup.det y` from `⟨_, rfl⟩`. Rewrite using `[← hd]`. Establish `h1 : toEAf D (mt V g).det = ((Lev.finE V g : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)).det`. Rewrite using `[finE_val, RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[h1, ← hy]`. Use `show ((β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf …`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul, hd]`. Conclude with `(RingHom.map_det (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype _).symm`.
-/
theorem toEAf_det {V : HSp D} {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)} (hy : Formalism.L2.DIV.frGL β y = Lev.finE V g) :
    toEAf D (mt V g).det =
      (((Matrix.GeneralLinearGroup.det y : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
  obtain ⟨d, hd⟩ : ∃ d : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ, d = Matrix.GeneralLinearGroup.det y := ⟨_, rfl⟩
  rw [← hd]
  have h1 : toEAf D (mt V g).det =
      ((Lev.finE V g : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)).det := by
    rw [finE_val, RingHom.map_det]; rfl
  rw [h1, ← hy]
  show ((β : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) *
    (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map
      (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
    ((β⁻¹ : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D))).det = _
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.det_one, one_mul, hd]
  exact (RingHom.map_det (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype _).symm

/- English proof (translation)
Take `⟨y, hy⟩` from `hg`. Rewrite using `[← comm_comm (finPart D (mt V g).det)]`. Establish `h : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D (mt V g).det) = (((Matrix.GeneralLinearGroup.det y : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)` using `toEAf_det hy`. Rewrite using `[h]`. Conclude with `comm_mem_intAE (((Matrix.GeneralLinearGroup.det y : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : Formalism.L2.Herm.intAf D.host.F D.host.E)).2`.
-/
theorem finPart_det_int {V : HSp D} {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) : finPart D (mt V g).det ∈ intAE D := by
  obtain ⟨y, hy⟩ := hg
  rw [← comm_comm (finPart D (mt V g).det)]
  have h : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D (mt V g).det) =
      (((Matrix.GeneralLinearGroup.det y : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := toEAf_det hy
  rw [h]
  exact comm_mem_intAE (((Matrix.GeneralLinearGroup.det y : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
    Formalism.L2.Herm.intAf D.host.F D.host.E)).2

/- English proof (translation)
Unfold `intAE`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Apply the tactic sequence `exact ⟨1, by first | simp [Formalism.MainNotions.StandardLattice.intAf] | exact Subring.one_mem _, 1, by rw [Algebra.TensorProduct.one_def]; simp⟩`.
-/
theorem one_mem_intAE : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  unfold intAE
  apply AddSubgroup.subset_closure
  exact ⟨1, by first | simp [Formalism.MainNotions.StandardLattice.intAf] | exact Subring.one_mem _, 1, by rw [Algebra.TensorProduct.one_def]; simp⟩

/- English proof (translation)
Take `⟨⟨h1, h2, v, ε, ⟨α, hεα, -, -⟩, h3⟩, -⟩` from `hPP`. Establish `hx : infPart D e * infPart D (cA D e) = 0` using `by rw [← map_mul, h2, map_zero]`. Establish `hy : infPart D e + infPart D (cA D e) = 0`. Rewrite using `[← map_add, h3, hεα, Algebra.TensorProduct.algebraMap_apply]`. Simplify using `only [infPart, pairA, fstA]`.

Use `first`. Consider the case `(erw [Algebra.TensorProduct.map_tmul]; exact TensorProduct.zero_tmul _ _)`. Consider the case `(erw [Algebra.TensorProduct.map_tmul]; show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0; simp)`. Consider the case `exact TensorProduct.zero_tmul _ _`. Consider the case `rfl`.

Establish `hz : infPart D e * infPart D e = infPart D e` using `by rw [← map_mul, h1]`. Take the linear combination `-hz + (infPart D e) * hy - hx`.
-/
theorem infPart_idemAt {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : Formalism.L2.NTheta.IsIdemAt e PP) :
    infPart D e = 0 := by
  obtain ⟨⟨h1, h2, v, ε, ⟨α, hεα, -, -⟩, h3⟩, -⟩ := hPP
  have hx : infPart D e * infPart D (cA D e) = 0 := by rw [← map_mul, h2, map_zero]
  have hy : infPart D e + infPart D (cA D e) = 0 := by
    rw [← map_add, h3, hεα, Algebra.TensorProduct.algebraMap_apply]
    simp only [infPart, pairA, fstA]
    first
      | (erw [Algebra.TensorProduct.map_tmul]; exact TensorProduct.zero_tmul _ _)
      | (erw [Algebra.TensorProduct.map_tmul]; show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0; simp)
      | exact TensorProduct.zero_tmul _ _
      | rfl
  have hz : infPart D e * infPart D e = infPart D e := by rw [← map_mul, h1]
  linear_combination -hz + (infPart D e) * hy - hx

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `he₁` using `hPP₁.1.1`. Establish `hinf` using `infPart_idemAt hPP₁`. Establish `hint` using `idemAt_int hPP₁`. Establish `hginv : Lev.finE V g⁻¹ ∈ Formalism.L2.DIV.St β` using `by rw [map_inv]; exact inv_mem hg`. Establish `hx : ((detAt e₁ V g : (AE D)ˣ) : AE D) = e₁ * (mt V g).det + (1 - e₁)` using `detAt_val he₁ V g`.

Establish `hxi : (((detAt e₁ V g)⁻¹ : (AE D)ˣ) : AE D) = e₁ * (mt V g⁻¹).det + (1 - e₁)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Establish `hd : (mt V g).det * (mt V g⁻¹).det = 1` using `by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]`. Rewrite using `[hx]`. Take the linear combination `(e₁ * e₁) * hd + (2 - (mt V g).det - (mt V g⁻¹).det) * he₁`.

Use `hU _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hx, map_add, map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]`. Rewrite using `[hx, map_add, map_mul, map_sub, map_one]`. Conclude with `add_mem (intAE_mul hint (finPart_det_int hg)) (sub_mem one_mem_intAE hint)`. Rewrite using `[hxi, map_add, map_mul, map_sub, map_one]`.

Conclude with `add_mem (intAE_mul hint (finPart_det_int hginv)) (sub_mem one_mem_intAE hint)`. Rewrite using `[hx]`. Take the linear combination `((mt V g).det - 1) * horth`.
-/
theorem unrOff_detAt {e e₁ : AE D} {PP₁ : Formalism.L2.DIV.Pl D.host.E} (hPP₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP₁)
    (horth : (e + cA D e) * e₁ = 0) (V : HSp D) {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) {χ : (AE D)ˣ →* Circle} (hU : UnrOff e χ) : χ (detAt e₁ V g) = 1 := by
  have he₁ := hPP₁.1.1
  have hinf := infPart_idemAt hPP₁
  have hint := idemAt_int hPP₁
  have hginv : Lev.finE V g⁻¹ ∈ Formalism.L2.DIV.St β := by rw [map_inv]; exact inv_mem hg
  have hx : ((detAt e₁ V g : (AE D)ˣ) : AE D) = e₁ * (mt V g).det + (1 - e₁) := detAt_val he₁ V g
  have hxi : (((detAt e₁ V g)⁻¹ : (AE D)ˣ) : AE D) = e₁ * (mt V g⁻¹).det + (1 - e₁) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have hd : (mt V g).det * (mt V g⁻¹).det = 1 := by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]
    rw [hx]
    linear_combination (e₁ * e₁) * hd + (2 - (mt V g).det - (mt V g⁻¹).det) * he₁
  refine hU _ ?_ ?_ ?_ ?_
  · rw [hx, map_add, map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · rw [hx, map_add, map_mul, map_sub, map_one]
    exact add_mem (intAE_mul hint (finPart_det_int hg)) (sub_mem one_mem_intAE hint)
  · rw [hxi, map_add, map_mul, map_sub, map_one]
    exact add_mem (intAE_mul hint (finPart_det_int hginv)) (sub_mem one_mem_intAE hint)
  · rw [hx]
    linear_combination ((mt V g).det - 1) * horth

end Det

section DetInt

variable {D : D7}

/- English proof (translation)
Rewrite using `[detAt_val he, map_add, map_mul, map_sub, map_one]`. Conclude with `add_mem (intAE_mul hint (finPart_det_int hg)) (sub_mem one_mem_intAE hint)`.
-/
theorem finPart_detAt_int {e : AE D} (he : e * e = e) (hint : finPart D e ∈ intAE D) (V : HSp D) {g : GA D V}
    {β : GL (Fin V.rank) (Lev.EAf D)} (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) :
    finPart D ((detAt e V g : (AE D)ˣ) : AE D) ∈ intAE D := by
  rw [detAt_val he, map_add, map_mul, map_sub, map_one]
  exact add_mem (intAE_mul hint (finPart_det_int hg)) (sub_mem one_mem_intAE hint)

/- English proof (translation)
Establish `hginv : Lev.finE V g⁻¹ ∈ Formalism.L2.DIV.St β` using `by rw [map_inv]; exact inv_mem hg`. Establish `hx : ((detAt e V g : (AE D)ˣ) : AE D) = e * (mt V g).det + (1 - e)` using `detAt_val he V g`. Establish `hxi : (((detAt e V g)⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Establish `hd : (mt V g).det * (mt V g⁻¹).det = 1` using `by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]`.

Rewrite using `[hx]`. Take the linear combination `(e * e) * hd + (2 - (mt V g).det - (mt V g⁻¹).det) * he`. Rewrite using `[hxi, map_add, map_mul, map_sub, map_one]`. Conclude with `add_mem (intAE_mul hint (finPart_det_int hginv)) (sub_mem one_mem_intAE hint)`.
-/
theorem finPart_detAt_inv_int {e : AE D} (he : e * e = e) (hint : finPart D e ∈ intAE D) (V : HSp D) {g : GA D V}
    {β : GL (Fin V.rank) (Lev.EAf D)} (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) :
    finPart D (((detAt e V g)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  have hginv : Lev.finE V g⁻¹ ∈ Formalism.L2.DIV.St β := by rw [map_inv]; exact inv_mem hg
  have hx : ((detAt e V g : (AE D)ˣ) : AE D) = e * (mt V g).det + (1 - e) := detAt_val he V g
  have hxi : (((detAt e V g)⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have hd : (mt V g).det * (mt V g⁻¹).det = 1 := by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]
    rw [hx]
    linear_combination (e * e) * hd + (2 - (mt V g).det - (mt V g⁻¹).det) * he
  rw [hxi, map_add, map_mul, map_sub, map_one]
  exact add_mem (intAE_mul hint (finPart_det_int hginv)) (sub_mem one_mem_intAE hint)

end DetInt

section Conj

variable {D : D7}

/- English proof (translation)
Take `⟨⟨h1, h2, v, ε, hv, hs⟩, hcl⟩` from `h`. Use `⟨⟨isIdem_cA h1, ?_, v, ε, hv, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[cA_cA, mul_comm]`. Conclude with `h2`. Rewrite using `[cA_cA, add_comm]`.

Conclude with `hs`. Introduce `x hx0`. Establish `hs0 : Formalism.L2.DIV.starO x ≠ 0`. Introduce `h0`. Apply `hx0` to reduce the goal to its premises.

Rewrite using `[← Formalism.L2.DIV.starO_starO x, h0]`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.DIV.starO_coe]`. Simplify using the standard rewrite rules. Establish `hmem : x ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ Formalism.L2.DIV.starO x ∈ PP.asIdeal` using `Iff.rfl`.

Rewrite using `[hmem, hcl _ hs0]`. Establish `hf : finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) = cF D (finPart D (e * incA D ((Formalism.L2.DIV.starO x : D.host.E)⁻¹)))`. Rewrite using `[← finPart_cA, cA_mul_incA, Formalism.L2.DIV.starO_coe, star_inv₀, star_star]`. Rewrite using `[hf]`. Prove the components needed by the constructor for the conclusion.

Introduce `hn hm; exact hn (by have h3 := cF_int hm; rwa [cF_cF] at h3)`. Introduce `hn hm`. Conclude with `hn (cF_int hm)`.
-/
theorem isIdemAt_conj {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e PP) :
    Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.L2.DIV.conjPl PP) := by
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, hcl⟩ := h
  refine ⟨⟨isIdem_cA h1, ?_, v, ε, hv, ?_⟩, ?_⟩
  · rw [cA_cA, mul_comm]; exact h2
  · rw [cA_cA, add_comm]; exact hs
  · intro x hx0
    have hs0 : Formalism.L2.DIV.starO x ≠ 0 := by
      intro h0; apply hx0
      rw [← Formalism.L2.DIV.starO_starO x, h0]
      apply RingOfIntegers.ext
      rw [Formalism.L2.DIV.starO_coe]
      simp
    have hmem : x ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ Formalism.L2.DIV.starO x ∈ PP.asIdeal := Iff.rfl
    rw [hmem, hcl _ hs0]
    have hf : finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) =
        cF D (finPart D (e * incA D ((Formalism.L2.DIV.starO x : D.host.E)⁻¹))) := by
      rw [← finPart_cA, cA_mul_incA, Formalism.L2.DIV.starO_coe, star_inv₀, star_star]
    rw [hf]
    constructor
    · intro hn hm; exact hn (by have h3 := cF_int hm; rwa [cF_cF] at h3)
    · intro hn hm; exact hn (cF_int hm)

open Classical in

/- English proof (translation)
Take `⟨⟨es, hes, he⟩, hc⟩` from `h`. Use `⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `Q hQ`. Take `⟨PP, hPP, rfl⟩` from `Finset.mem_image.1 hQ`. Use `show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)`.

Rewrite using `[Formalism.L2.DIV.conjPl_conjPl]`. Conclude with `isIdemAt_conj (hes PP hPP)`. Rewrite using `[Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by`. Rewrite using `[← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl])]`. Simplify using `only [Formalism.L2.DIV.conjPl_conjPl]`.

Rewrite using `[he, map_sum]`. Rewrite using `[cA_cA, mul_comm]`. Conclude with `hc`.
-/
theorem isIdemSum_conj {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsIdemSum (cA D e) (P.image Formalism.L2.DIV.conjPl) := by
  classical
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact isIdemAt_conj (hes PP hPP)
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    rw [he, map_sum]
  · rw [cA_cA, mul_comm]; exact hc

/- English proof (translation)
Establish `hx : ∃ x : D.host.E, star x ≠ x`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `hsurj : Function.Surjective (Algebra.linearMap D.host.F D.host.E)`. Introduce `a`.

Take `⟨f, hf⟩` from `(D.sp.cm.fixed a).1 (hno a)`. Conclude with `⟨f, hf⟩`. Establish `hinj : Function.Injective (Algebra.linearMap D.host.F D.host.E)` using `(algebraMap D.host.F D.host.E).injective`. Establish `h1` using `(LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E) ⟨hinj, hsurj⟩).finrank_eq`. Rewrite `h1` using `[Module.finrank_self, D.sp.cm.deg2]`.

Conclude with `absurd h1 (by norm_num)`. Take `⟨x, hx⟩` from `hx`. Use `⟨x - star x, sub_ne_zero.2 (Ne.symm hx), by rw [star_sub, star_star, neg_sub], ?_⟩` and prove the remaining obligations. Establish `hfix : star ((x - star x) * (x - star x)) = (x - star x) * (x - star x)`. Rewrite using `[star_mul, star_sub, star_star]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨d, hd⟩` from `(D.sp.cm.fixed _).1 hfix`. Conclude with `⟨d, hd⟩`.
-/
theorem exists_anti :
    ∃ ω : D.host.E, ω ≠ 0 ∧ star ω = -ω ∧ ∃ d : D.host.F, algebraMap D.host.F D.host.E d = ω * ω := by
  have hx : ∃ x : D.host.E, star x ≠ x := by
    by_contra hno
    push Not at hno
    have hsurj : Function.Surjective (Algebra.linearMap D.host.F D.host.E) := by
      intro a
      obtain ⟨f, hf⟩ := (D.sp.cm.fixed a).1 (hno a)
      exact ⟨f, hf⟩
    have hinj : Function.Injective (Algebra.linearMap D.host.F D.host.E) := (algebraMap D.host.F D.host.E).injective
    have h1 := (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E) ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_self, D.sp.cm.deg2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - star x, sub_ne_zero.2 (Ne.symm hx), by rw [star_sub, star_star, neg_sub], ?_⟩
  have hfix : star ((x - star x) * (x - star x)) = (x - star x) * (x - star x) := by
    rw [star_mul, star_sub, star_star]; ring
  obtain ⟨d, hd⟩ := (D.sp.cm.fixed _).1 hfix
  exact ⟨d, hd⟩

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨ω, hω0, hωs, d, hd⟩` from `exists_anti (D := D)`. Establish `hli : LinearIndependent D.host.F ![(1 : D.host.E), ω]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`.

Establish `hs' : star (algebraMap D.host.F D.host.E s) = algebraMap D.host.F D.host.E s` using `(D.sp.cm.fixed _).2 ⟨s, rfl⟩`. Establish `ht' : star (algebraMap D.host.F D.host.E t) = algebraMap D.host.F D.host.E t` using `(D.sp.cm.fixed _).2 ⟨t, rfl⟩`. Establish `hst2 : algebraMap D.host.F D.host.E s - algebraMap D.host.F D.host.E t * ω = 0`. Establish `h3` using `congrArg star hst`. Rewrite `h3` using `[star_add, star_mul, hs', ht', hωs, star_zero]`.

Take the linear combination `h3`. Establish `hsum : (2 : D.host.E) * algebraMap D.host.F D.host.E s = 0` using `by linear_combination hst + hst2`. Establish `hdif : (2 : D.host.E) * algebraMap D.host.F D.host.E t * ω = 0` using `by linear_combination hst - hst2`. Establish `h2 : (2 : D.host.E) ≠ 0` using `two_ne_zero`. Prove the components needed by the constructor for the conclusion.

Establish `h4` using `(mul_eq_zero.1 hsum).resolve_left h2`. Conclude with `(algebraMap D.host.F D.host.E).injective (by rw [h4, map_zero])`. Establish `h4` using `(mul_eq_zero.1 hdif).resolve_right hω0`. Establish `h5` using `(mul_eq_zero.1 h4).resolve_left h2`. Conclude with `(algebraMap D.host.F D.host.E).injective (by rw [h5, map_zero])`.

Set `B : Module.Basis (Fin 2) D.host.F D.host.E` to `basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, D.sp.cm.deg2])`. Establish `hB0 : B 0 = 1` using `by simp [B]`. Establish `hB1 : B 1 = ω` using `by simp [B]`. Set `b` to `Algebra.TensorProduct.basis (AF D.host.F) B`. Establish `hb0 : b 0 = 1` using `by show Algebra.TensorProduct.basis (AF D.host.F) B 0 = 1`.

Rewrite using `[Algebra.TensorProduct.basis_apply, hB0]`. Both sides reduce to the same expression. Establish `hb1 : b 1 = incA D ω` using `by show Algebra.TensorProduct.basis (AF D.host.F) B 1 = incA D ω`. Rewrite using `[Algebra.TensorProduct.basis_apply, hB1]`. Both sides reduce to the same expression.

Establish `hWW : incA D ω * incA D ω = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) d)`. Rewrite using `[← map_mul, ← hd, incA_alg, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]`. Establish `hcW : cA D (incA D ω) = - incA D ω` using `by rw [cA_incA, hωs, map_neg]`. Establish `hy : y = algebraMap (AF D.host.F) (AE D) (b.repr y 0) + algebraMap (AF D.host.F) (AE D) (b.repr y 1) * incA D ω`. Establish `h3` using `b.sum_repr y`.

Rewrite `h3` using `[Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Conclude with `h3.symm`. Establish `hrepr : ∀ α β : AF D.host.F, b.repr (algebraMap (AF D.host.F) (AE D) α + algebraMap (AF D.host.F) (AE D) β * incA D ω) = Finsupp.single 0 α + Finsupp.single 1 β`. Introduce `α β`. Establish `h3 : algebraMap (AF D.host.F) (AE D) α + algebraMap (AF D.host.F) (AE D) β * incA D ω = α • b 0 + β • b 1`.

Rewrite using `[hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[h3, map_add, map_smul, map_smul, b.repr_self, b.repr_self, Finsupp.smul_single_one, Finsupp.smul_single_one]`. Establish `hy1 : y * b 1 = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) d * b.repr y 1) + algebraMap (AF D.host.F) (AE D) (b.repr y 0) * incA D ω`. Rewrite using `[hb1, map_mul]`. Use `conv_lhs => rw [hy]`.

Take the linear combination `(algebraMap (AF D.host.F) (AE D) (b.repr y 1)) * hWW`. Establish `e00 : Algebra.leftMulMatrix b y 0 0 = b.repr y 0` using `by rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]`. Establish `e10 : Algebra.leftMulMatrix b y 1 0 = b.repr y 1` using `by rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]`. Establish `e01 : Algebra.leftMulMatrix b y 0 1 = algebraMap D.host.F (AF D.host.F) d * b.repr y 1`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hy1, hrepr]`.

Simplify using the standard rewrite rules. Establish `e11 : Algebra.leftMulMatrix b y 1 1 = b.repr y 0`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hy1, hrepr]`. Simplify using the standard rewrite rules. Rewrite using `[Algebra.norm_eq_matrix_det b, Matrix.det_fin_two, e00, e11, e01, e10]`.

Use `conv_rhs => rw [hy]`. Rewrite using `[map_add, map_mul, cA_alg, cA_alg, hcW, map_sub, map_mul, map_mul, map_mul]`. Take the linear combination `(algebraMap (AF D.host.F) (AE D) (b.repr y 1) * algebraMap (AF D.host.F) (AE D) (b.repr y 1)) * hWW`.
-/
theorem norm_eq_mul_cA (y : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) y) = y * cA D y := by
  classical
  obtain ⟨ω, hω0, hωs, d, hd⟩ := exists_anti (D := D)
  have hli : LinearIndependent D.host.F ![(1 : D.host.E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hs' : star (algebraMap D.host.F D.host.E s) = algebraMap D.host.F D.host.E s :=
      (D.sp.cm.fixed _).2 ⟨s, rfl⟩
    have ht' : star (algebraMap D.host.F D.host.E t) = algebraMap D.host.F D.host.E t :=
      (D.sp.cm.fixed _).2 ⟨t, rfl⟩
    have hst2 : algebraMap D.host.F D.host.E s - algebraMap D.host.F D.host.E t * ω = 0 := by
      have h3 := congrArg star hst
      rw [star_add, star_mul, hs', ht', hωs, star_zero] at h3
      linear_combination h3
    have hsum : (2 : D.host.E) * algebraMap D.host.F D.host.E s = 0 := by linear_combination hst + hst2
    have hdif : (2 : D.host.E) * algebraMap D.host.F D.host.E t * ω = 0 := by linear_combination hst - hst2
    have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
    constructor
    · have h4 := (mul_eq_zero.1 hsum).resolve_left h2
      exact (algebraMap D.host.F D.host.E).injective (by rw [h4, map_zero])
    · have h4 := (mul_eq_zero.1 hdif).resolve_right hω0
      have h5 := (mul_eq_zero.1 h4).resolve_left h2
      exact (algebraMap D.host.F D.host.E).injective (by rw [h5, map_zero])
  let B : Module.Basis (Fin 2) D.host.F D.host.E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, D.sp.cm.deg2])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = ω := by simp [B]
  let b := Algebra.TensorProduct.basis (AF D.host.F) B
  have hb0 : b 0 = 1 := by
    show Algebra.TensorProduct.basis (AF D.host.F) B 0 = 1
    rw [Algebra.TensorProduct.basis_apply, hB0]; rfl
  have hb1 : b 1 = incA D ω := by
    show Algebra.TensorProduct.basis (AF D.host.F) B 1 = incA D ω
    rw [Algebra.TensorProduct.basis_apply, hB1]; rfl
  have hWW : incA D ω * incA D ω =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) d) := by
    rw [← map_mul, ← hd, incA_alg, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  have hcW : cA D (incA D ω) = - incA D ω := by rw [cA_incA, hωs, map_neg]
  have hy : y = algebraMap (AF D.host.F) (AE D) (b.repr y 0) + algebraMap (AF D.host.F) (AE D) (b.repr y 1) * incA D ω := by
    have h3 := b.sum_repr y
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at h3
    exact h3.symm
  have hrepr : ∀ α β : AF D.host.F, b.repr (algebraMap (AF D.host.F) (AE D) α +
      algebraMap (AF D.host.F) (AE D) β * incA D ω) = Finsupp.single 0 α + Finsupp.single 1 β := by
    intro α β
    have h3 : algebraMap (AF D.host.F) (AE D) α + algebraMap (AF D.host.F) (AE D) β * incA D ω = α • b 0 + β • b 1 := by
      rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [h3, map_add, map_smul, map_smul, b.repr_self, b.repr_self, Finsupp.smul_single_one, Finsupp.smul_single_one]
  have hy1 : y * b 1 = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) d * b.repr y 1) +
      algebraMap (AF D.host.F) (AE D) (b.repr y 0) * incA D ω := by
    rw [hb1, map_mul]
    conv_lhs => rw [hy]
    linear_combination (algebraMap (AF D.host.F) (AE D) (b.repr y 1)) * hWW
  have e00 : Algebra.leftMulMatrix b y 0 0 = b.repr y 0 := by rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]
  have e10 : Algebra.leftMulMatrix b y 1 0 = b.repr y 1 := by rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]
  have e01 : Algebra.leftMulMatrix b y 0 1 = algebraMap D.host.F (AF D.host.F) d * b.repr y 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hy1, hrepr]; simp
  have e11 : Algebra.leftMulMatrix b y 1 1 = b.repr y 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hy1, hrepr]; simp
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two, e00, e11, e01, e10]
  conv_rhs => rw [hy]
  rw [map_add, map_mul, cA_alg, cA_alg, hcW, map_sub, map_mul, map_mul, map_mul]
  linear_combination (algebraMap (AF D.host.F) (AE D) (b.repr y 1) * algebraMap (AF D.host.F) (AE D) (b.repr y 1)) * hWW

/- English proof (translation)
Take `⟨⟨η, hη⟩, hall⟩` from `hR`. Establish `hprod : y * Units.map (cA D).toMonoidHom y = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y)`. Apply `Units.ext` to reduce the goal to its premises. Use `show (y : AE D) * cA D y = algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) (y : AE D))`. Rewrite using `[norm_eq_mul_cA]`.

Establish `h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1`. Rewrite using `[← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]`. Conclude with `eq_inv_of_mul_eq_one_right h1`.
-/
theorem chi_cA {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    show (y : AE D) * cA D y = algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) (y : AE D))
    rw [norm_eq_mul_cA]
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[detAt_val (isIdem_cA he)]`. Use `show _ = cA D ((detAt e V g⁻¹ : (AE D)ˣ) : AE D)`. Rewrite using `[detAt_val he, map_add, map_mul, map_sub, map_one]`. Establish `h1` using `det_conj_mul V g⁻¹`.

Establish `h2 : (mt V g).det * (mt V g⁻¹).det = 1` using `by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]`. Establish `h3 : cA D (mt V g⁻¹).det = (mt V g).det`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3]`.
-/
theorem detAt_cA {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    detAt (cA D e) V g = Units.map (cA D).toMonoidHom (detAt e V g⁻¹) := by
  apply Units.ext
  rw [detAt_val (isIdem_cA he)]
  show _ = cA D ((detAt e V g⁻¹ : (AE D)ˣ) : AE D)
  rw [detAt_val he, map_add, map_mul, map_sub, map_one]
  have h1 := det_conj_mul V g⁻¹
  have h2 : (mt V g).det * (mt V g⁻¹).det = 1 := by rw [← Matrix.det_mul, mtG_inv, Matrix.det_one]
  have h3 : cA D (mt V g⁻¹).det = (mt V g).det := by
    calc cA D (mt V g⁻¹).det = cA D (mt V g⁻¹).det * ((mt V g).det * (mt V g⁻¹).det) := by rw [h2, mul_one]
      _ = (mt V g).det * (cA D (mt V g⁻¹).det * (mt V g⁻¹).det) := by ring
      _ = (mt V g).det := by rw [h1, mul_one]
  rw [h3]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hginv : Lev.finE V g⁻¹ ∈ Formalism.L2.DIV.St β` using `by rw [map_inv]; exact inv_mem hg`. Rewrite using `[detAt_cA hPP.1.1, chi_cA hR, Circle.coe_inv, tame_detAt hPP V hginv hT, map_inv, Formalism.L2.DIV.redFn_inv hg PP, map_inv, map_inv, Units.val_inv_eq_inv_val, _root_.inv_zpow, inv_inv]`.
-/
theorem tame_detAt_cA {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : Formalism.L2.NTheta.IsIdemAt e PP) (V : HSp D)
    {g : GA D V} {β : GL (Fin V.rank) (Lev.EAf D)} (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) {χ : (AE D)ˣ →* Circle}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {k : ℤ} {n : ℕ} (hT : TameAt e PP χ c k) (hR : ResEta D χ n) :
    ((χ (detAt (cA D e) V g) : Circle) : ℂ) =
      ((c (Matrix.GeneralLinearGroup.det (Formalism.L2.DIV.redFn β PP (Lev.finE V g))) : ℂˣ) : ℂ) ^ k := by
  have hginv : Lev.finE V g⁻¹ ∈ Formalism.L2.DIV.St β := by rw [map_inv]; exact inv_mem hg
  rw [detAt_cA hPP.1.1, chi_cA hR, Circle.coe_inv, tame_detAt hPP V hginv hT, map_inv,
    Formalism.L2.DIV.redFn_inv hg PP, map_inv, map_inv, Units.val_inv_eq_inv_val, _root_.inv_zpow, inv_inv]

end Conj

end Formalism.IndefR.Fin.LevelGroupLemmas

end
