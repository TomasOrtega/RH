import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Use `⟨0, fun _ => zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `[Sys.r, Sys.mu, mul_comm]`. Take `⟨t, rfl⟩` from `Fin.exists_succAbove_eq h`.

Use `⟨Pi.single t 1, fun l => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : l = t`. Substitute `hl` using the available equality. Simplify using `using R.one_mem`. Simplify `R.zero_mem` using `[Pi.single_eq_of_ne hl]`.

Rewrite using `[Finset.sum_eq_single t]`. Simplify using `only [Pi.single_eq_same, one_mul]`. Both sides reduce to the same expression. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`.

Introduce `hb`. Conclude with `absurd (Finset.mem_univ t) hb`.
-/
private lemma muSpan_base {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (R : Subalgebra ℂ S) (i j a : Fin (d + 1)) :
    InSp R (fun t => T.r n11 T.mu i j (dj j t)) (T.r n11 T.mu i j (toLex (a, j))) := by
  by_cases h : a = j
  · subst h
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    simp [Sys.r, Sys.mu, mul_comm]
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq h
    refine ⟨Pi.single t 1, fun l => ?_, ?_⟩
    · by_cases hl : l = t
      · subst hl
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hl] using R.zero_mem
    · rw [Finset.sum_eq_single t]
      · simp only [Pi.single_eq_same, one_mul]
        rfl
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro hb
        exact absurd (Finset.mem_univ t) hb

/- English proof (translation)
Establish `hv : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1` using `Units.mul_inv _`. Establish `hu : ∀ l' : Mi d, T.u n11 i j l' = T.X i * T.Y j` using `fun _ => by simp [Sys.u, n11]`. Simplify using `only [Sys.r, Sys.mu, ofLex_toLex, Units.val_mul, hu]`. Take the linear combination `(-((T.X (ofLex l).1 : S) * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1) * ((T.X i * T.Y j)⁻¹ : Sˣ)) * hv`.
-/
private lemma muSpan_rel {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (i j : Fin (d + 1)) (l : Mi d) :
    T.r n11 T.mu i j l =
      ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).1, j)) -
      ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).2, j)) := by
  have hv : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hu : ∀ l' : Mi d, T.u n11 i j l' = T.X i * T.Y j := fun _ => by simp [Sys.u, n11]
  simp only [Sys.r, Sys.mu, ofLex_toLex, Units.val_mul, hu]
  linear_combination (-((T.X (ofLex l).1 : S) * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1) *
    ((T.X i * T.Y j)⁻¹ : Sˣ)) * hv

/- English proof (translation)
Introduce `d S E _ _ _ _ T hT I J i hi j hj l`. Establish `hI : I.Nonempty` using `⟨i, hi⟩`. Take `⟨p, hp, hp'⟩` from `muSpan_base T (T.R I J) i j (ofLex l).1`. Take `⟨q, hq, hq'⟩` from `muSpan_base T (T.R I J) i j (ofLex l).2`. Establish `hb` using `hT.memY I J hI j hj (ofLex l).2`.

Establish `ha` using `hT.memY I J hI j hj (ofLex l).1`. Use `⟨fun t => ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * p t - ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * q t, fun t => ?_, ?_⟩` and prove the remaining obligations. Conclude with `sub_mem (mul_mem hb (hp t)) (mul_mem ha (hq t))`. Rewrite using `[muSpan_rel T i j l, hp', hq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.productCup_of_system.muSpan_of :
    MuSpan := by
  intro d S E _ _ _ _ T hT I J i hi j hj l
  have hI : I.Nonempty := ⟨i, hi⟩
  obtain ⟨p, hp, hp'⟩ := muSpan_base T (T.R I J) i j (ofLex l).1
  obtain ⟨q, hq, hq'⟩ := muSpan_base T (T.R I J) i j (ofLex l).2
  have hb := hT.memY I J hI j hj (ofLex l).2
  have ha := hT.memY I J hI j hj (ofLex l).1
  refine ⟨fun t => ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * p t -
    ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * q t, fun t => ?_, ?_⟩
  · exact sub_mem (mul_mem hb (hp t)) (mul_mem ha (hq t))
  · rw [muSpan_rel T i j l, hp', hq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
