import Mathlib

namespace KStar.Schema

variable {A B G : Type*} [CommRing A] [CommRing B]

def IsCost (ℓ : A) (E : G → A) : Prop :=
  ∀ I : Ideal A, (∀ g, E g - 1 ∈ I) → ℓ ∈ I

def IsCost' (ℓ : A) (E : G → A) : Prop :=
  ℓ ∈ Ideal.span (Set.range fun g => E g - 1)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem IsCost.of_dvd {ℓ ℓ' : A} {E : G → A} (h : IsCost ℓ E) (hd : ℓ ∣ ℓ') : IsCost ℓ' E :=
  fun I hI => I.mem_of_dvd hd (h I hI)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem IsCost.map {ℓ : A} {E : G → A} (h : IsCost ℓ E) (φ : A →+* B) :
    IsCost (φ ℓ) (fun g => φ (E g)) := by
  intro I hI
  exact h (I.comap φ) fun g => by simpa [Ideal.mem_comap] using hI g

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isCost_of_dvd {ℓ : A} {E : G → A} (g : G) (h : E g - 1 ∣ ℓ) : IsCost ℓ E :=
  fun I hI => I.mem_of_dvd h (hI g)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsCost.dvd_of_forall {ℓ a : A} {E : G → A} (h : IsCost ℓ E) (ha : ∀ g, a ∣ E g - 1) :
    a ∣ ℓ :=
  Ideal.mem_span_singleton.mp (h _ fun g => Ideal.mem_span_singleton.mpr (ha g))

/- English proof (translation)
A detailed English derivation is pending.
-/
example : IsCost (2 : ℤ) (fun _ : Unit => (3 : ℤ)) := isCost_of_dvd () (by norm_num)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
example : ¬ IsCost (1 : ℤ) (fun _ : Unit => (3 : ℤ)) := fun h => by
  have := h.dvd_of_forall (a := 2) fun _ => by norm_num
  norm_num at this

end KStar.Schema
