import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Formalism.FrobeniusOrbits.HostCorollaries

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.Proof.LetterConjugation

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

/- English proof (translation)
Take `⟨τ, i⟩` from `x`. Take `⟨a, rfl⟩` from `(Fintype.equivFin (E →+* ℂ)).symm.surjective τ`. Conclude with `List.mem_flatMap.2 ⟨a, List.mem_finRange a, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩⟩`.
-/
theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange a, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩⟩

/- English proof (translation)
Use `List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(List.nodup_finRange _).map fun i i' h => eq_of_heq (Sigma.mk.inj h).2`. Use `(List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_` and prove the remaining obligations. Introduce `x hx hy`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hx`.

Take `⟨i', -, h⟩` from `List.mem_map.1 hy`. Conclude with `hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (Sigma.mk.inj h).1).symm`.
-/
theorem nodup_letters : (letters Dw).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · exact (List.nodup_finRange _).map fun i i' h => eq_of_heq (Sigma.mk.inj h).2
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (Sigma.mk.inj h).1).symm

/- English proof (translation)
Introduce `h2`. Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.1 h2`. Establish `h3` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Simplify using `[pow_two, him] at h3`.

Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.
-/
theorem rt0_conj_neg_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, him] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

/- English proof (translation)
Introduce `h1`. Conclude with `rt0_conj_neg_ne_zero (H := H) (by simpa [conjEmb, h] using h1)`.
-/
theorem conj_ne {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h1
  exact rt0_conj_neg_ne_zero (H := H) (by simpa [conjEmb, h] using h1)

/- English proof (translation)
Establish `h0 : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, h0, H.sqrt_neg_disc_sq]`.

Simplify using the standard rewrite rules. Establish `h2 : τ (H.rt : E) = -H.rt0` using `(sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left h`. Establish `h3 : starRingEnd ℂ H.rt0 ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, H.sqrt_neg_disc_sq]`. Simplify using the standard rewrite rules.

Establish `h4 : starRingEnd ℂ H.rt0 = -H.rt0` using `(sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left rt0_conj_neg_ne_zero`. Simplify using `[conjEmb, h2, h4]`.
-/
theorem conj_eq {τ : E →+* ℂ} (h : τ (H.rt : E) ≠ H.rt0) : conjEmb τ (H.rt : E) = H.rt0 := by
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
  have h2 : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left h
  have h3 : starRingEnd ℂ H.rt0 ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  have h4 : starRingEnd ℂ H.rt0 = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left rt0_conj_neg_ne_zero
  simp [conjEmb, h2, h4]

/- English proof (translation)
Unfold `Datum.mult`. Distinguish the cases in `h : τ (H.rt : E) = H.rt0`. Rewrite using `[if_pos h, if_neg (conj_ne h)]`. Rewrite using `[if_neg h, if_pos (conj_eq h), add_comm]`.
-/
theorem mult_add (τ : E →+* ℂ) : Dw.mult τ + Dw.mult (conjEmb τ) = Dw.p + Dw.q := by
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (conj_ne h)]
  · rw [if_neg h, if_pos (conj_eq h), add_comm]

/- English proof (translation)
Establish `h1 : (letters Dw).length = ∑ τ, Dw.mult τ`. Rewrite using `[← List.toFinset_card_of_nodup (nodup_letters Dw), Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_letters Dw x), Finset.card_univ, Fintype.card_sigma]`. Simplify using the standard rewrite rules. Establish `hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ))` using `fun τ => by`. Use extensionality with `x`.

Simplify using `[conjEmb]`. Establish `h2 : ∑ τ, Dw.mult (conjEmb τ) = ∑ τ, Dw.mult τ` using `hinv.bijective.sum_comp Dw.mult`. Rewrite using `[h1, two_mul]`. Use `nth_rewrite 2 [← h2]`. Rewrite using `[← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => mult_add Dw τ, Finset.sum_const, Finset.card_univ, Embeddings.card, smul_eq_mul]`.
-/
theorem two_mul_length : 2 * (letters Dw).length = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  classical
  have h1 : (letters Dw).length = ∑ τ, Dw.mult τ := by
    rw [← List.toFinset_card_of_nodup (nodup_letters Dw),
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_letters Dw x), Finset.card_univ, Fintype.card_sigma]
    simp
  have hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := fun τ => by
    ext x; simp [conjEmb]
  have h2 : ∑ τ, Dw.mult (conjEmb τ) = ∑ τ, Dw.mult τ := hinv.bijective.sum_comp Dw.mult
  rw [h1, two_mul]
  nth_rewrite 2 [← h2]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => mult_add Dw τ, Finset.sum_const, Finset.card_univ,
    Embeddings.card, smul_eq_mul]

end Free

/- English proof (translation)
The claim follows from `D.host.finrank_E'`.
-/
theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

/- English proof (translation)
Introduce `D A N j S _ _`. Use `⟨?_, nodup_letters _, mem_letters _, fun t => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `two_mul_length S.Dw`. Rewrite `h` using `[finrank_host, S.rank_eq, mul_assoc]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Datum.mult, if_pos (A.cm t), S.p_eq]`. Rewrite using `[Datum.mult, if_neg (conj_ne (A.cm t))]`. Use `S.p_eq` as an intermediate fact. Use `S.rank_eq` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem letters_spec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ), (letters S.Dw).length = D.R.f * N ∧ (letters S.Dw).Nodup ∧ (∀ x, x ∈ letters S.Dw) ∧ ∀ t : D.what₂.Tau, S.Dw.mult (DV.tauEmb D t) = j ∧ S.Dw.mult (conjEmb (DV.tauEmb D t)) = N - j := by
  intro D A N j S _ _
  refine ⟨?_, nodup_letters _, mem_letters _, fun t => ⟨?_, ?_⟩⟩
  · have h := two_mul_length S.Dw
    rw [finrank_host, S.rank_eq, mul_assoc] at h
    omega
  · rw [Datum.mult, if_pos (A.cm t), S.p_eq]
  · rw [Datum.mult, if_neg (conj_ne (A.cm t))]
    have := S.p_eq
    have := S.rank_eq
    omega

end GlobalTheory.Proof.LetterConjugation
