import Mathlib
import ReciprocityTheory.GaloisValuations.ArithOfA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GenOfTwo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective

noncomputable section

namespace MassDataIdxEmb

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `p.isMaximal` as an intermediate fact. Establish `: Fintype (p.asIdeal.primesOver (𝓞 E))` using `Fintype.ofFinite _`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 E)`. Establish `hrk : Module.finrank (𝓞 F) (𝓞 E) = 2` using `(IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm.trans h2`. Rewrite `hsum` using `[hrk]`.

Establish `hterm : ∀ q : p.asIdeal.primesOver (𝓞 E), (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) ≤ 1`. Introduce `q`. Establish `hqp : (q : Ideal (𝓞 E)).IsPrime` using `q.2.1`. Establish `hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal` using `q.2.2`. Establish `hq0 : (q : Ideal (𝓞 E)) ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _`.

Set `w : HeightOneSpectrum (𝓞 E)` to `⟨q, hqp, hq0⟩`. Establish `hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal`. Use `(Ideal.mem_of_liesOver (q : Ideal (𝓞 E)) p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp` as an intermediate fact. Simplify using `using this`. Take `⟨he, hf⟩` from `MassDataIdxRes.locDeg_one l hsplit w hw`.

Express the relevant statement in the definitionally equal form `(q : Ideal (𝓞 E)).ramificationIdx ℤ = 1 at he`. Express the relevant statement in the definitionally equal form `(q : Ideal (𝓞 E)).inertiaDeg ℤ = 1 at hf`. Establish `h1` using `Ideal.ramificationIdx_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))`. Establish `h2` using `Ideal.inertiaDeg_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))`. Rewrite `h1` using `[he]`.

Rewrite `h2` using `[hf]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcard : 2 ≤ Fintype.card (p.asIdeal.primesOver (𝓞 E))`. Combine the equalities or inequalities in the displayed calculation. Take `⟨q, q', hqq⟩` from `Fintype.one_lt_card_iff.1 (show 1 < Fintype.card (p.asIdeal.primesOver (𝓞 E)) by omega)`.

Establish `hqp : (q : Ideal (𝓞 E)).IsPrime` using `q.2.1`. Establish `hqp' : (q' : Ideal (𝓞 E)).IsPrime` using `q'.2.1`. Establish `hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal` using `q.2.2`. Establish `hqo' : (q' : Ideal (𝓞 E)).LiesOver p.asIdeal` using `q'.2.2`. Use `⟨q, q', hqp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _), hqp'.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _), fun h => hqq (Subtype.ext h), hqo, hqo'⟩` and prove the remaining obligations.
-/
theorem two_primes (h2 : Module.finrank F E = 2) (l : ℕ) [hl : Fact l.Prime]
    (hsplit : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    ∃ Q Q' : Ideal (𝓞 E), Q.IsMaximal ∧ Q'.IsMaximal ∧ Q ≠ Q' ∧ Q.LiesOver p.asIdeal ∧
      Q'.LiesOver p.asIdeal := by
  have := p.isMaximal
  have : Fintype (p.asIdeal.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 E)
  have hrk : Module.finrank (𝓞 F) (𝓞 E) = 2 := (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm.trans h2
  rw [hrk] at hsum
  have hterm : ∀ q : p.asIdeal.primesOver (𝓞 E),
      (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) ≤ 1 := by
    intro q
    have hqp : (q : Ideal (𝓞 E)).IsPrime := q.2.1
    have hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal := q.2.2
    have hq0 : (q : Ideal (𝓞 E)) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _
    let w : HeightOneSpectrum (𝓞 E) := ⟨q, hqp, hq0⟩
    have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
      have := (Ideal.mem_of_liesOver (q : Ideal (𝓞 E)) p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
      simpa using this
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one l hsplit w hw
    change (q : Ideal (𝓞 E)).ramificationIdx ℤ = 1 at he
    change (q : Ideal (𝓞 E)).inertiaDeg ℤ = 1 at hf
    have h1 := Ideal.ramificationIdx_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))
    have h2 := Ideal.inertiaDeg_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))
    rw [he] at h1
    rw [hf] at h2
    calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
      _ = 1 := rfl
  have hcard : 2 ≤ Fintype.card (p.asIdeal.primesOver (𝓞 E)) := by
    calc 2 = ∑ q : p.asIdeal.primesOver (𝓞 E),
          (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) := hsum.symm
      _ ≤ ∑ _q : p.asIdeal.primesOver (𝓞 E), 1 := Finset.sum_le_sum fun q _ => hterm q
      _ = _ := by simp
  obtain ⟨q, q', hqq⟩ := Fintype.one_lt_card_iff.1
    (show 1 < Fintype.card (p.asIdeal.primesOver (𝓞 E)) by omega)
  have hqp : (q : Ideal (𝓞 E)).IsPrime := q.2.1
  have hqp' : (q' : Ideal (𝓞 E)).IsPrime := q'.2.1
  have hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal := q.2.2
  have hqo' : (q' : Ideal (𝓞 E)).LiesOver p.asIdeal := q'.2.2
  refine ⟨q, q', hqp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _),
    hqp'.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _), fun h => hqq (Subtype.ext h), hqo, hqo'⟩

end MassDataIdxEmb

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

/- English proof (translation)
Establish `hgp : Fact (gOf p).Prime` using `⟨gOf_prime X p⟩`. Establish `hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal` using `(resArith_holds X p).2.1`. Establish `hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) | ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E`. Unfold `gOf`. Use `split_ifs`.

Conclude with `MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)`. Conclude with `MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)`. Take `⟨Q, Q', hQ, hQ', hne, hQo, hQ'o⟩` from `MassDataIdxEmb.two_primes (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.deg2 (gOf p) hsplit p.1 hmem`. Conclude with `MassDataIdxEmb.emb_of_two X.B.I.cm.deg2 p.1 Q Q' hne`.
-/
theorem embP_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : EmbP X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := (resArith_holds X p).2.1
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨Q, Q', hQ, hQ', hne, hQo, hQ'o⟩ :=
    MassDataIdxEmb.two_primes (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.deg2 (gOf p) hsplit p.1 hmem
  exact MassDataIdxEmb.emb_of_two X.B.I.cm.deg2 p.1 Q Q' hne

end MassDataIdxSteps
