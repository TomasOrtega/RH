import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

def AdjKlt (c : k →+* K) (n : ℕ) (T : Subring K) (S : Place c) (η : Forms c n) (φ : K →₀ ℚ) :
    Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧
  ∀ (Q : Subring K) (hQ : IsLocModel c Q) (t u : Q) (E : Place c), T ≤ Q →
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : K) = 1 → E.ord (u : K) = 1 →
    (∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) →
    -1 < E.disc η φ

namespace AdjKlt

variable {c : k →+* K} {n : ℕ} {T T' : Subring K} {S : Place c} {η : Forms c n} {φ : K →₀ ℚ}

/- English proof (translation)
The claim follows from `h.1`.
-/
theorem form_ne_zero (h : AdjKlt c n T S η φ) : η ≠ 0 := h.1

/- English proof (translation)
The claim follows from `h.2.1`.
-/
theorem apply_zero (h : AdjKlt c n T S η φ) : φ 0 = 0 := h.2.1

/- English proof (translation)
The claim follows from `h.2.2 Q hQ t u E hT hm hd hS hE ht hu h0`.
-/
theorem lt_disc (h : AdjKlt c n T S η φ) {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q}
    {E : Place c} (hT : T ≤ Q)
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (hE : E.IsPrimeOf Q)
    (ht : S.ord (t : K) = 1) (hu : E.ord (u : K) = 1)
    (h0 : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) :
    -1 < E.disc η φ :=
  h.2.2 Q hQ t u E hT hm hd hS hE ht hu h0

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, fun Q hQ t u E hQ' => h.2.2 Q hQ t u E (hT.trans hQ')⟩`.
-/
theorem mono (h : AdjKlt c n T S η φ) (hT : T ≤ T') : AdjKlt c n T' S η φ :=
  ⟨h.1, h.2.1, fun Q hQ t u E hQ' => h.2.2 Q hQ t u E (hT.trans hQ')⟩

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

/- English proof (translation)
Use `⟨fun h h0 => h ?_, fun h hu => h (P.ord_eq_zero hu)⟩` and prove the remaining obligations. Establish `h1 : (b : K)⁻¹ ∈ P.ring` using `(P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h0]; rfl)`. Conclude with `IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))`.
-/
theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 := by
  refine ⟨fun h h0 => h ?_, fun h hu => h (P.ord_eq_zero hu)⟩
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h0]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

/- English proof (translation)
Introduce and unpack `rfl`. Use `haveI := hQ.isLocalRing`. Establish `h0 : E.ord (0 : K) = 0` using `by simp [Place.ord]`. Establish `hle : IsLocalRing.maximalIdeal Q ≤ (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1)`. Rewrite using `[← hm, Ideal.span_le]`.

Apply the tactic sequence `rintro _ (h | h) <;> rw [h]`. Conclude with `(mem_maximalIdeal_iff E _ fun h => by`. Express the relevant statement in the definitionally equal form `(t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)`. Conclude with `(mem_maximalIdeal_iff E _ fun h => by`. Express the relevant statement in the definitionally equal form `(u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)`.

Establish `hb : Function.Bijective (incl hS.1)`. Use `⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, hb0, hbo, e⟩` from `hS.2 f f.2`. Establish `hu : IsUnit (⟨b, hb⟩ : Q)`. Assume the negation of the conclusion as `hn`.

Conclude with `(mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo`. Take `⟨g, hg⟩` from `hu.exists_right_inv`. Establish `hg' : b * (g : K) = 1` using `congrArg Subtype.val hg`. Use `⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a * (g : K) = f`.

Rewrite using `[← e, mul_assoc, hg', mul_one]`. Use `ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)` as an intermediate fact. Rewrite `this` using `[hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)]`. Conclude with `absurd this (by decide)`.
-/
theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)

end AdjKlt

variable {c : k →+* K} {n : ℕ} {T : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hη, hφ, fun _ hQ _ _ E hT hm hd hS hE ht hu _ => h E (hE.1.mono hT) fun e => AdjKlt.neighbour_ne hQ hm hd hS ht hu (Place.ext e)⟩`.
-/
theorem adjKlt_of_lt_disc (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0)
    (h : ∀ E : Place c, E.Contains T → E.ring ≠ S.ring → -1 < E.disc η φ) :
    AdjKlt c n T S η φ :=
  ⟨hη, hφ, fun _ hQ _ _ E hT hm hd hS hE ht hu _ =>
    h E (hE.1.mono hT) fun e => AdjKlt.neighbour_ne hQ hm hd hS ht hu (Place.ext e)⟩

/- English proof (translation)
Introduce `h` and use `h.form_ne_zero rfl`.
-/
example (S : Place c) : ¬ AdjKlt c n T S 0 φ := fun h => h.form_ne_zero rfl

/- English proof (translation)
Introduce `h` and use `by simpa using h.apply_zero`.
-/
example (S : Place c) : ¬ AdjKlt c n T S η (Finsupp.single 0 1) := fun h => by
  simpa using h.apply_zero

/- English proof (translation)
The claim follows from `adjKlt_of_lt_disc S hη hφ fun E hE _ => (hT E hE).elim`.
-/
example (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0) (hT : ∀ E : Place c, ¬ E.Contains T) :
    AdjKlt c n T S η φ :=
  adjKlt_of_lt_disc S hη hφ fun E hE _ => (hT E hE).elim

end GlobalTheory.FieldPair
