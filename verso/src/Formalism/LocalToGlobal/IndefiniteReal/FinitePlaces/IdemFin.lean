import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish `h : P.asIdeal = Q.asIdeal`. Use extensionality with `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Conclude with `⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩`.

Rewrite using `[hP.2 x hx, hQ.2 x hx]`. Conclude with `HeightOneSpectrum.ext h`.
-/
theorem pin_eq {P Q : HeightOneSpectrum (𝓞 D.host.E)} {x : AE D} (hP : Formalism.L2.NTheta.IsIdemAt x P)
    (hQ : Formalism.L2.NTheta.IsIdemAt x Q) : P = Q := by
  have h : P.asIdeal = Q.asIdeal := by
    ext x
    by_cases hx : x = 0
    · subst hx
      exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
    · rw [hP.2 x hx, hQ.2 x hx]
  exact HeightOneSpectrum.ext h

/- English proof (translation)
Establish `hsp` using `idemAt_split hx`. Take `⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩` from `idem_data P hsp (belowPl P) rfl`. Establish `hx0 : x = e₀` using `idemAt_eq_split hsp hx he₀`. Establish `hle : (belowPl P).asIdeal ≤ (belowPl Q).asIdeal`. Introduce `f hf`.

Take `⟨c, hc', hce⟩` from `hc _ hf`. Establish `: c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f`. Apply `FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E` to reduce the goal to its premises. Use `show (c : D.host.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[hce, algebraMap_O]`.

Conclude with `(D.sp.cm.fixed _).2 ⟨_, rfl⟩`. Use `show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f ∈ Q.asIdeal`. Rewrite using `[← this]`. Conclude with `hc'`. Establish `hbel : belowPl Q = belowPl P` using `(HeightOneSpectrum.ext ((belowPl P).isMaximal.eq_of_le (belowPl Q).isPrime.ne_top hle)).symm`.

Establish `hs'` using `below_of_idemAt hy`. Rewrite `hs'` using `[hbel]`. Break down `idem_class P hsp e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 y hy.1.1 hy.1.2.1 hs' with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `h` using `[← hx0]`.

Establish `hPQ : P = Q` using `pin_eq hx (h ▸ hy)`. Substitute `hPQ` using the available equality. Conclude with `hsp hc`. Rewrite using `[h, hx0]`.
-/
theorem conj_idem_eq {P Q : HeightOneSpectrum (𝓞 D.host.E)} {x y : AE D} (hx : Formalism.L2.NTheta.IsIdemAt x P)
    (hy : Formalism.L2.NTheta.IsIdemAt y Q) (hc : Lev.IsConjPl (D := D) P Q) : y = cA D x := by
  have hsp := idemAt_split hx
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hsp (belowPl P) rfl
  have hx0 : x = e₀ := idemAt_eq_split hsp hx he₀
  have hle : (belowPl P).asIdeal ≤ (belowPl Q).asIdeal := by
    intro f hf
    obtain ⟨c, hc', hce⟩ := hc _ hf
    have : c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f := by
      apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
      show (c : D.host.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E)
      rw [hce, algebraMap_O]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f ∈ Q.asIdeal
    rw [← this]; exact hc'
  have hbel : belowPl Q = belowPl P :=
    (HeightOneSpectrum.ext ((belowPl P).isMaximal.eq_of_le (belowPl Q).isPrime.ne_top hle)).symm
  have hs' := below_of_idemAt hy
  rw [hbel] at hs'
  rcases idem_class P hsp e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 y hy.1.1 hy.1.2.1 hs' with h | h
  · exfalso
    rw [← hx0] at h
    have hPQ : P = Q := pin_eq hx (h ▸ hy)
    subst hPQ
    exact hsp hc
  · rw [h, hx0]

/- English proof (translation)
Introduce `h0`. Take `⟨c, hcP, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Establish `h` using `(he.2 c hc0).1 hcP`. Rewrite `h` using `[h0, zero_mul]`. Use `first`.

Consider the case `exact h (by simp)`. Consider the case `simp at h`. Consider the case `exact h (map_zero (finPart D) ▸ (intAE D).zero_mem)`.
-/
private theorem ne_zero_of_isIdemAt' {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  intro h0
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have h := (he.2 c hc0).1 hcP
  rw [h0, zero_mul] at h
  first
  | exact h (by simp)
  | simp at h
  | exact h (map_zero (finPart D) ▸ (intAE D).zero_mem)

/- English proof (translation)
Introduce `hc`. Establish `h1 : e = cA D e` using `conj_idem_eq he he hc`. Establish `h2 : e * cA D e = 0` using `he.1.2.1`. Rewrite `h2` using `[← h1, he.1.1]`. Conclude with `ne_zero_of_isIdemAt' he h2`.
-/
private theorem not_isConjPl_of_isIdemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : ¬ Lev.IsConjPl (D := D) P P := by
  intro hc
  have h1 : e = cA D e := conj_idem_eq he he hc
  have h2 : e * cA D e = 0 := he.1.2.1
  rw [← h1, he.1.1] at h2
  exact ne_zero_of_isIdemAt' he h2

/- English proof (translation)
Take `⟨⟨es, hes, hsum⟩, hc⟩` from `he`. Use `⟨es, fun PP hPP => (hes PP hPP).1, hsum, fun PP hPP PP' hPP' hne => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hne`. Distinguish the cases in `hcj : Lev.IsConjPl (D := D) PP PP'`. It suffices to derive a contradiction.

Establish `hy : es PP' = cA D (es PP)` using `conj_idem_eq (hes PP hPP) (hes PP' hPP') hcj`. Establish `hL : es PP * e = es PP`. Rewrite using `[hsum, Finset.mul_sum, Finset.sum_eq_single PP]`. Conclude with `(hes PP hPP).1.1`. Introduce `b hb hbne`.

Conclude with `idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (Ne.symm hbne)`. Introduce `h`. Conclude with `absurd hPP h`. Establish `hR : es PP * cA D e = es PP`. Rewrite using `[hsum, map_sum, Finset.mul_sum, Finset.sum_eq_single PP']`.

Rewrite using `[hy, cA_cA]`. Conclude with `(hes PP hPP).1.1`. Introduce `b hb hbne`. Distinguish the cases in `hb0 : b = PP`. Rewrite using `[hb0]`.

Conclude with `(hes PP hPP).1.2.1`. Use `idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (fun hcb => hbne ?_)` and prove the remaining obligations. Establish `hyb : es b = cA D (es PP)` using `conj_idem_eq (hes PP hPP) (hes b hb) hcb`. Rewrite `hyb` using `[← hy]`. Establish `hb'` using `hes b hb`.

Rewrite `hb'` using `[hyb]`. Conclude with `pin_eq hb' (hes PP' hPP')`. Introduce `h`. Conclude with `absurd hPP' h`. Establish `h0 : es PP * (e * cA D e) = 0` using `by rw [hc, mul_zero]`.

Rewrite `h0` using `[← mul_assoc, hL, hR]`. Conclude with `ne_zero_of_isIdemAt' (hes PP hPP) h0`. Conclude with `idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hcj`.
-/
theorem idemSum_orth (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : Formalism.IndefR.Datum.IsIdemSum e P) :
    ∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, IsSplitIdem D (es PP)) ∧ e = ∑ PP ∈ P, es PP ∧
      ∀ PP ∈ P, ∀ PP' ∈ P, PP ≠ PP' → es PP * es PP' = 0 ∧ es PP * cA D (es PP') = 0 := by
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  refine ⟨es, fun PP hPP => (hes PP hPP).1, hsum, fun PP hPP PP' hPP' hne => ⟨?_, ?_⟩⟩
  · exact idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hne
  · by_cases hcj : Lev.IsConjPl (D := D) PP PP'
    · exfalso
      have hy : es PP' = cA D (es PP) := conj_idem_eq (hes PP hPP) (hes PP' hPP') hcj
      have hL : es PP * e = es PP := by
        rw [hsum, Finset.mul_sum, Finset.sum_eq_single PP]
        · exact (hes PP hPP).1.1
        · intro b hb hbne
          exact idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (Ne.symm hbne)
        · intro h; exact absurd hPP h
      have hR : es PP * cA D e = es PP := by
        rw [hsum, map_sum, Finset.mul_sum, Finset.sum_eq_single PP']
        · rw [hy, cA_cA]; exact (hes PP hPP).1.1
        · intro b hb hbne
          by_cases hb0 : b = PP
          · rw [hb0]; exact (hes PP hPP).1.2.1
          · refine idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (fun hcb => hbne ?_)
            have hyb : es b = cA D (es PP) := conj_idem_eq (hes PP hPP) (hes b hb) hcb
            rw [← hy] at hyb
            have hb' := hes b hb
            rw [hyb] at hb'
            exact pin_eq hb' (hes PP' hPP')
        · intro h; exact absurd hPP' h
      have h0 : es PP * (e * cA D e) = 0 := by rw [hc, mul_zero]
      rw [← mul_assoc, hL, hR] at h0
      exact ne_zero_of_isIdemAt' (hes PP hPP) h0
    · exact idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hcj

end Formalism.IndefR.Fin

end
