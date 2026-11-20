import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.CombinationEquivInvMemUnipotentFlagGroup

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Establish `hq0` using `qE_ne_zero P hp`. Use `⟨Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j, Nat.findGreatest_le j, Nat.findGreatest_spec (P := fun k => I (qE P ^ k)⁻¹) (Nat.zero_le j) (by simpa using hI1), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hxK`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hxK (by simpa using intAt_zero P)`.

Establish `hex : ∃ k, IntAt P (qE P ^ k * x)` using `⟨j, hIb x hx⟩`. Establish `hk0 : IntAt P (qE P ^ Nat.find hex * x)` using `Nat.find_spec hex`. Establish `hk0j : Nat.find hex ≤ j` using `Nat.find_min' hex (hIb x hx)`. Establish `hKk0 : Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j < Nat.find hex`. Assume the negation of the conclusion as `hle`.

Rewrite `hle` using `[not_lt]`. Apply `hxK` to reduce the goal to its premises. Establish `: qE P ^ Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j * x = qE P ^ (Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j - Nat.find hex) * (qE P ^ Nat.find hex * x)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`. Rewrite using `[this]`.

Conclude with `intAt_mul P (intAt_pow P (intAt_natCast P _) _) hk0`. Take `⟨k1, hk1⟩ : ∃ k1, Nat.find hex = k1 + 1` from `⟨Nat.find hex - 1, by omega⟩`. Establish `hnot : ¬ IntAt P (qE P ^ Nat.find hex * x / qE P)`. Establish `: qE P ^ Nat.find hex * x / qE P = qE P ^ k1 * x` using `by rw [hk1, pow_succ]; field_simp`. Rewrite using `[this]; exact Nat.find_min hex (by omega)`.

Establish `hu` using `unit_of_not_div P hp hq hk0 hnot`. Establish `hI` using `hIm _ _ hu hx`. Establish `e : (qE P ^ Nat.find hex * x)⁻¹ * x = (qE P ^ Nat.find hex)⁻¹`. Rewrite using `[mul_inv, mul_assoc, inv_mul_cancel₀ hx0, mul_one]`. Rewrite `hI` using `[e]`.

Conclude with `Nat.findGreatest_is_greatest hKk0 hk0j hI`.
-/
theorem ideal_form (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ) (I : E → Prop) (hI1 : I 1)
    (hIm : ∀ t x, IntAt P t → I x → I (t * x)) (hIb : ∀ x, I x → IntAt P (qE P ^ j * x)) :
    ∃ K, K ≤ j ∧ I (qE P ^ K)⁻¹ ∧ ∀ x, I x → IntAt P (qE P ^ K * x) := by
  classical
  have hq0 := qE_ne_zero P hp
  refine ⟨Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j, Nat.findGreatest_le j,
    Nat.findGreatest_spec (P := fun k => I (qE P ^ k)⁻¹) (Nat.zero_le j) (by simpa using hI1), ?_⟩
  intro x hx
  by_contra hxK
  have hx0 : x ≠ 0 := by rintro rfl; exact hxK (by simpa using intAt_zero P)
  have hex : ∃ k, IntAt P (qE P ^ k * x) := ⟨j, hIb x hx⟩
  have hk0 : IntAt P (qE P ^ Nat.find hex * x) := Nat.find_spec hex
  have hk0j : Nat.find hex ≤ j := Nat.find_min' hex (hIb x hx)
  have hKk0 : Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j < Nat.find hex := by
    by_contra hle; rw [not_lt] at hle
    apply hxK
    have : qE P ^ Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j * x =
        qE P ^ (Nat.findGreatest (fun k => I (qE P ^ k)⁻¹) j - Nat.find hex) * (qE P ^ Nat.find hex * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]; exact intAt_mul P (intAt_pow P (intAt_natCast P _) _) hk0
  obtain ⟨k1, hk1⟩ : ∃ k1, Nat.find hex = k1 + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnot : ¬ IntAt P (qE P ^ Nat.find hex * x / qE P) := by
    have : qE P ^ Nat.find hex * x / qE P = qE P ^ k1 * x := by rw [hk1, pow_succ]; field_simp
    rw [this]; exact Nat.find_min hex (by omega)
  have hu := unit_of_not_div P hp hq hk0 hnot
  have hI := hIm _ _ hu hx
  have e : (qE P ^ Nat.find hex * x)⁻¹ * x = (qE P ^ Nat.find hex)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  rw [e] at hI
  exact Nat.findGreatest_is_greatest hKk0 hk0j hI

section M

variable {n : ℕ} (Mm : (Fin n → E) → Prop) (Madd : ∀ u v, Mm u → Mm v → Mm (u + v))
  (Msmul : ∀ t v, IntAt P t → Mm v → Mm (t • v)) (Mlam : ∀ v, (∀ l, IntAt P (v l)) → Mm v)

include Madd Msmul Mlam in
/- English proof (translation)
Establish `h0 : Mm 0` using `Mlam 0 (fun l => by first`. Consider the case `exact ⟨0, 1, (fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)), by simp⟩`. Consider the case `(unfold IntAt; done))`. Conclude with `Finset.sum_induction _ Mm (fun a b ha hb => Madd a b ha hb) h0 (fun l _ => Msmul _ _ (hw l) (hbM l))`.
-/
theorem comb_mem (b : Fin n → Fin n → E) (hbM : ∀ l, Mm (b l)) (w : Fin n → E) (hw : ∀ l, IntAt P (w l)) :
    Mm (∑ l, w l • b l) := by
  classical
  have h0 : Mm 0 := Mlam 0 (fun l => by
    first
    | exact ⟨0, 1, (fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)), by simp⟩
    | (unfold IntAt; done))
  exact Finset.sum_induction _ Mm (fun a b ha hb => Madd a b ha hb) h0
    (fun l _ => Msmul _ _ (hw l) (hbM l))

include Madd Msmul Mlam in

/- English proof (translation)
Establish `hIl : ∀ l : Fin n, ∃ K, K ≤ j ∧ (∃ v, Mm v ∧ v l = (qE P ^ K)⁻¹ ∧ ∀ k, l < k → v k = 0) ∧ ∀ x, (∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0) → IntAt P (qE P ^ K * x)`. Introduce `l`. Apply `ideal_form P hp hq j (fun x => ∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0)` to reduce the goal to its premises. Use `⟨Pi.single l 1, Mlam _ fun k => ?_, by simp, fun k hk => by simp [Pi.single_apply, hk.ne']⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = l`.

Rewrite using `[hk]`. Simplify using `using intAt_one P`. Simplify `intAt_zero P` using `[Pi.single_apply, hk]`. Introduce and unpack `t x ht ⟨v, hv, rfl, hz⟩`. Conclude with `⟨t • v, Msmul t v ht hv, by simp, fun k hk => by simp [hz k hk]⟩`.

Introduce and unpack `x ⟨v, hv, rfl, -⟩`. Conclude with `Mbd v hv l`. Use `choose K hKj hKb hKall using hIl`. Use `choose b hbM hbl hbz using hKb`. Use `⟨K, b, hKj, hbM, hbl, fun l k hlk => hbz l k hlk, ?_⟩` and prove the remaining obligations.

Establish `hq0` using `qE_ne_zero P hp`. Establish `main : ∀ k, k ≤ n → ∀ v, Mm v → Zab k v → ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `_ v _ hz`. Use `⟨0, fun _ => intAt_zero P, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using `[hz l (Nat.zero_le _)]`. Consider the case `succ k ih`.

Introduce `hk v hv hz`. Establish `ht : IntAt P (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)` using `hKall ⟨k, by omega⟩ _ ⟨v, hv, rfl, fun k' hk' => hz k' (by rw [Fin.lt_def] at hk'; simp at hk'; omega)⟩`. Establish `hv'` using `Madd _ _ hv (Msmul _ _ (intAt_neg P ht) (hbM ⟨k, by omega⟩))`. Establish `hz' : Zab k (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩)`. Introduce `l hl`.

Break down `Nat.lt_or_eq_of_le hl with hlt | heq` into its components or cases. Rewrite using `[Pi.add_apply, hz l hlt, Pi.smul_apply, hbz _ l (by rw [Fin.lt_def]; simpa using hlt)]; simp`. Establish `: l = ⟨k, by omega⟩` using `Fin.ext heq.symm`. Rewrite using `[this, Pi.add_apply, Pi.smul_apply, hbl, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨w', hw', e'⟩` from `ih (by omega) _ hv' hz'`. Use `⟨w' + Pi.single ⟨k, by omega⟩ (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩), fun l => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply]`. Use `intAt_add P (hw' l) ?_` and prove the remaining obligations.

Distinguish the cases in `hl : l = ⟨k, by omega⟩`. Rewrite using `[hl]`. Simplify using `using ht`. Simplify `intAt_zero P` using `[Pi.single_apply, hl]`. Establish `: v = (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) + (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) • b ⟨k, by omega⟩` using `by rw [neg_smul]; abel conv_lhs => rw [this]`.

Rewrite using `[e']`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single ⟨k, by omega⟩]`. Simplify using the standard rewrite rules.

Introduce `i _ hi`. Simplify using `[Pi.single_apply, hi]`. Simplify using the standard rewrite rules. Conclude with `fun v hv => main n le_rfl v hv (fun l hl => absurd l.2 (by omega))`.
-/
theorem herm (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ)
    (Mbd : ∀ v, Mm v → ∀ l, IntAt P (qE P ^ j * v l)) :
    ∃ (K : Fin n → ℕ) (b : Fin n → Fin n → E), (∀ l, K l ≤ j) ∧ (∀ l, Mm (b l)) ∧
      (∀ l, b l l = (qE P ^ K l)⁻¹) ∧ UT b ∧
      ∀ v, Mm v → ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by
  classical
  have hIl : ∀ l : Fin n, ∃ K, K ≤ j ∧ (∃ v, Mm v ∧ v l = (qE P ^ K)⁻¹ ∧ ∀ k, l < k → v k = 0) ∧
      ∀ x, (∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0) → IntAt P (qE P ^ K * x) := by
    intro l
    apply ideal_form P hp hq j (fun x => ∃ v, Mm v ∧ v l = x ∧ ∀ k, l < k → v k = 0)
    · refine ⟨Pi.single l 1, Mlam _ fun k => ?_, by simp, fun k hk => by simp [Pi.single_apply, hk.ne']⟩
      by_cases hk : k = l
      · rw [hk]; simpa using intAt_one P
      · simpa [Pi.single_apply, hk] using intAt_zero P
    · rintro t x ht ⟨v, hv, rfl, hz⟩
      exact ⟨t • v, Msmul t v ht hv, by simp, fun k hk => by simp [hz k hk]⟩
    · rintro x ⟨v, hv, rfl, -⟩; exact Mbd v hv l
  choose K hKj hKb hKall using hIl
  choose b hbM hbl hbz using hKb
  refine ⟨K, b, hKj, hbM, hbl, fun l k hlk => hbz l k hlk, ?_⟩
  have hq0 := qE_ne_zero P hp
  have main : ∀ k, k ≤ n → ∀ v, Mm v → Zab k v →
      ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by
    intro k
    induction k with
    | zero =>
      intro _ v _ hz
      refine ⟨0, fun _ => intAt_zero P, ?_⟩
      funext l; simp [hz l (Nat.zero_le _)]
    | succ k ih =>
      intro hk v hv hz
      have ht : IntAt P (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) :=
        hKall ⟨k, by omega⟩ _ ⟨v, hv, rfl, fun k' hk' => hz k' (by rw [Fin.lt_def] at hk'; simp at hk'; omega)⟩
      have hv' := Madd _ _ hv (Msmul _ _ (intAt_neg P ht) (hbM ⟨k, by omega⟩))
      have hz' : Zab k (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) := by
        intro l hl
        rcases Nat.lt_or_eq_of_le hl with hlt | heq
        · rw [Pi.add_apply, hz l hlt, Pi.smul_apply, hbz _ l (by rw [Fin.lt_def]; simpa using hlt)]; simp
        · have : l = ⟨k, by omega⟩ := Fin.ext heq.symm
          rw [this, Pi.add_apply, Pi.smul_apply, hbl, smul_eq_mul]
          field_simp; ring
      obtain ⟨w', hw', e'⟩ := ih (by omega) _ hv' hz'
      refine ⟨w' + Pi.single ⟨k, by omega⟩ (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩), fun l => ?_, ?_⟩
      · rw [Pi.add_apply]
        refine intAt_add P (hw' l) ?_
        by_cases hl : l = ⟨k, by omega⟩
        · rw [hl]; simpa using ht
        · simpa [Pi.single_apply, hl] using intAt_zero P
      · have : v = (v + (-(qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩)) • b ⟨k, by omega⟩) +
            (qE P ^ K ⟨k, by omega⟩ * v ⟨k, by omega⟩) • b ⟨k, by omega⟩ := by rw [neg_smul]; abel
        conv_lhs => rw [this]
        rw [e']
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single ⟨k, by omega⟩]
        · simp
        · intro i _ hi; simp [Pi.single_apply, hi]
        · simp
  exact fun v hv => main n le_rfl v hv (fun l hl => absurd l.2 (by omega))

end M

end PI.TwNormLat.W
