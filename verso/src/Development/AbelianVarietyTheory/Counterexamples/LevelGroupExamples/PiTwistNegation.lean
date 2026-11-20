import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

noncomputable section
namespace GlobalTheory.Survey.PiTwistNegation
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

def withPi (X : ErrX D) (p : Fin 2 → 𝓞 D.host.E) (hK : ∀ i, ((p i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K)
    (hn : ∀ i, p i * barE D (p i) = (D.host.g i : 𝓞 D.host.E)) : ErrX D :=
  { X with
    piG := p
    piG_K := hK
    piG_norm := fun i => by
      rw [← barE_eq_conj]
      have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) (hn i)
      rw [map_mul, map_natCast] at this
      exact this }

def swapX (X : ErrX D) : ErrX D :=
  withPi X (fun i => barE D (X.piG i)) (barE_piG_mem X) fun i => by
    rw [barE_barE, mul_comm]; exact piG_mul_barE X i

def negX (X : ErrX D) : ErrX D :=
  withPi X (fun i => -X.piG i) (fun i => by
    have := neg_mem (X.piG_K i)
    simpa using this) fun i => by
    rw [map_neg, neg_mul_neg]; exact piG_mul_barE X i

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem halfI_ne_top (T : Core D) (i : Fin 2) : halfI T i ≠ ⊤ := by
  intro h
  have hc : ((T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).comap
      (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊤ := by
    rw [show (T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊤ from h, Ideal.comap_top]
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hc
  exact (T.pb i).isPrime.ne_top hc

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bar_piOf_mem_K (T : Core D) (X : ErrX D) (i : Fin 2) :
    ((barE D (piOf T X i) : 𝓞 D.host.E) : D.host.E) ∈ D.host.K := by
  classical
  unfold piOf
  split_ifs
  · rw [barE_barE]; exact X.piG_K i
  · exact barE_piG_mem X i

def orientX (T : Core D) (X : ErrX D) : ErrX D :=
  withPi X (fun i => barE D (piOf T X i)) (bar_piOf_mem_K T X) fun i => by
    rw [barE_barE, mul_comm]; exact piOf_mul_barE T X i

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfEX_iff_le (T : Core D) (h : LawsM T) (X : ErrX D) :
    HalfEX T X ↔ ∀ i, T.Q.l.Mb ≤ Ideal.span {barE D (X.piG i)} := by
  have hle : ∀ i, T.Q.l.Mb ≤ halfI T i := by
    intro i
    rw [Mb_eq T h]
    fin_cases i
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_right
  refine forall_congr' fun i => ⟨fun hb => ?_, fun hM => ?_⟩
  · rw [← (piOf_eq_bar_iff T h X i).2 hb, span_piOf T h]; exact hle i
  · by_contra hb
    have hp : piOf T X i = X.piG i := by
      classical
      unfold piOf; rw [if_neg hb]

    have h1 : T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {barE D (X.piG i)} := by
      rw [← hp, ← bar_core T, span_bar_piOf T h]; exact Ideal.map_mono (hle i)
    have ht : Ideal.span {barE D (X.piG i)} = ⊤ := by
      rw [eq_top_iff, ← T.Q.l.coprime]; exact sup_le hM h1
    have hu : IsUnit (X.piG i) := by
      have := (Ideal.span_singleton_eq_top.1 ht).map (barE D)
      rwa [barE_barE] at this
    apply halfI_ne_top T i
    rw [← span_piOf T h X i, hp, Ideal.span_singleton_eq_top]; exact hu

end GlobalTheory.Survey.PiTwistNegation
