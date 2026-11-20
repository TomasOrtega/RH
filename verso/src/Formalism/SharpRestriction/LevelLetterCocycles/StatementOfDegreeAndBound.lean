import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
import Formalism.PadicSubsetSums.StableGradedCounts.FrobeniusDifferenceDividedPower
import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens

noncomputable section

namespace Formalism.MainNotions.EmbeddingTypeJumps

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

variable (D : D7)

section Sqrt

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨z, hz⟩` from `Formalism.IrreducibleCountingLemmas.WindowSums.sqrt_neg_in_cyclotomic_field p hp hp4 ↥M ⟨ζ, hM⟩ (IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ)`. Establish `hz' : -(p : Om l) = (z : Om l) * z`. Use `congrArg (Subtype.val : ↥M → Om l) hz` as an intermediate fact. Simplify using `using this`. Establish `h0 : (y - z) * (y + z) = 0` using `by linear_combination hy + hz'`.

Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Rewrite using `[sub_eq_zero.mp h]`. Conclude with `z.2`. Rewrite using `[eq_neg_of_add_eq_zero_left h]`. Conclude with `M.neg_mem z.2`.
-/
theorem sqrt_neg_mem (M : IntermediateField ℚ_[l] (Om l)) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3)
    (ζ : Om l) (hζ : IsPrimitiveRoot ζ p) (hM : ζ ∈ M) (y : Om l) (hy : y ^ 2 = -(p : Om l)) :
    y ∈ M := by
  obtain ⟨z, hz⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.sqrt_neg_in_cyclotomic_field p hp hp4 ↥M ⟨ζ, hM⟩
    (IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ)
  have hz' : -(p : Om l) = (z : Om l) * z := by
    have := congrArg (Subtype.val : ↥M → Om l) hz
    simpa using this
  have h0 : (y - z) * (y + z) = 0 := by linear_combination hy + hz'
  rcases mul_eq_zero.mp h0 with h | h
  · rw [sub_eq_zero.mp h]; exact z.2
  · rw [eq_neg_of_add_eq_zero_left h]; exact M.neg_mem z.2

/- English proof (translation)
Establish `: NeZero (p : Om l)` using `⟨by exact_mod_cast hp.ne_zero⟩`. Conclude with `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) p`.
-/
theorem exists_prim (p : ℕ) (hp : p.Prime) : ∃ ζ : Om l, IsPrimitiveRoot ζ p := by
  have : NeZero (p : Om l) := ⟨by exact_mod_cast hp.ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) p

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `exists_prim (l := l) p hp`. Use `sqrt_neg_mem (MaximalUnramifiedExtension l) p hp hp4 ζ hζ (IntermediateField.subset_adjoin _ _ ?_) y hy` and prove the remaining obligations. Use `⟨p, hp.pos, ?_, hζ.pow_eq_one⟩` and prove the remaining obligations. Introduce `h`. Conclude with `hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hp).mp h).symm`.
-/
theorem sqrt_mem_Kur (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hpl : p ≠ l) (y : Om l)
    (hy : y ^ 2 = -(p : Om l)) : y ∈ MaximalUnramifiedExtension l := by
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) p hp
  refine sqrt_neg_mem (MaximalUnramifiedExtension l) p hp hp4 ζ hζ (IntermediateField.subset_adjoin _ _ ?_) y hy
  refine ⟨p, hp.pos, ?_, hζ.pow_eq_one⟩
  intro h
  exact hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hp).mp h).symm

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `exists_prim (l := l) l Fact.out`. Use `sqrt_neg_mem (Ks K 1) l Fact.out hl4 ζ hζ ?_ y hy` and prove the remaining obligations. Apply `(le_sup_right : _ ≤ Ks K 1)` to reduce the goal to its premises. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Use `show ζ ^ (l ^ 1) = 1`.

Rewrite using `[pow_one]`. Conclude with `hζ.pow_eq_one`.
-/
theorem sqrt_mem_Ks (hl4 : l % 4 = 3) (K : FinExt l) (y : Om l) (hy : y ^ 2 = -(l : Om l)) :
    y ∈ Ks K 1 := by
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) l Fact.out
  refine sqrt_neg_mem (Ks K 1) l Fact.out hl4 ζ hζ ?_ y hy
  apply (le_sup_right : _ ≤ Ks K 1)
  apply IntermediateField.subset_adjoin
  show ζ ^ (l ^ 1) = 1
  rw [pow_one]; exact hζ.pow_eq_one

end Sqrt

section Local

open Formalism.BasicNotions.Loc Polynomial UpperTheory.InertGen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

/- English proof (translation)
Take `⟨z, hz, hθ⟩` from `image_inertField H.toHostRaw J (l := l)`. Establish `hN` using `H.toHostRaw.condN_ne_zero`. Establish `hzK : z ∈ (MaximalUnramifiedExtension l).toSubfield` using `IntermediateField.subset_adjoin _ _ ⟨_, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl Fact.out hN, hz⟩`. Conclude with `(Subfield.closure_le.2 (Set.singleton_subset_iff.2 hzK) : Subfield.closure {z} ≤ (MaximalUnramifiedExtension l).toSubfield) (hθ _ (thetaAt_mem _ l))`.
-/
theorem theta_mem_Kur : J (thetaAt H.toHostRaw l) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨z, hz, hθ⟩ := image_inertField H.toHostRaw J (l := l)
  have hN := H.toHostRaw.condN_ne_zero
  have hzK : z ∈ (MaximalUnramifiedExtension l).toSubfield := IntermediateField.subset_adjoin _ _
    ⟨_, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl Fact.out hN, hz⟩
  exact (Subfield.closure_le.2 (Set.singleton_subset_iff.2 hzK) : Subfield.closure {z} ≤ (MaximalUnramifiedExtension l).toSubfield)
    (hθ _ (thetaAt_mem _ l))

/- English proof (translation)
The claim follows from `adjoin_thetaAt_top H hp hpS`.
-/
theorem adjoin_gen_top {p : ℕ} (hp : p.Prime) (hpS : ¬ p ∣ H.QS) :
    IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw p, H.sqq, H.sqd} : Set H.E) = ⊤ :=
  adjoin_thetaAt_top H hp hpS

/- English proof (translation)
Establish `hx : x ∈ IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw l, H.sqq, H.sqd} : Set H.E)`. Rewrite using `[adjoin_gen_top H Fact.out hlS]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem y hy`.

Break down `hy with rfl | rfl | rfl` into its components or cases. Use `exacts [h1, h2, h3]`. Consider the case `algebraMap r`. Rewrite using `[eq_ratCast, map_ratCast]`. Conclude with `SubfieldClass.ratCast_mem M r`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `M.add_mem ha hb`. Consider the case `inv a _ ha => rw [map_inv₀]`. Conclude with `M.inv_mem ha`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`.

Conclude with `M.mul_mem ha hb`.
-/
theorem image_le (hlS : ¬ l ∣ H.QS) (M : IntermediateField ℚ_[l] (Om l)) (h1 : J (thetaAt H.toHostRaw l) ∈ M)
    (h2 : J (H.sqq) ∈ M) (h3 : J (H.sqd) ∈ M) (x : H.E) : J x ∈ M := by
  have hx : x ∈ IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw l, H.sqq, H.sqd} : Set H.E) := by
    rw [adjoin_gen_top H Fact.out hlS]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    exacts [h1, h2, h3]
  | algebraMap r =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem M r
  | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact M.inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact M.mul_mem ha hb

/- English proof (translation)
Establish `hh` using `H.hyp`. Establish `hqd` using `H.hypOdd`. Establish `ha : (J (H.sqq)) ^ 2 = -(H.q : Om l)`. Rewrite using `[← map_pow, H.sqq_sq]`. Simplify using the standard rewrite rules.

Establish `hb : (J (H.sqd)) ^ 2 = -(H.d : Om l)`. Rewrite using `[← map_pow, H.sqd_sq]`. Simplify using the standard rewrite rules. Apply the tactic sequence `have hlS : ¬ l ∣ H.QS := by rcases hl with h | h <;> rw [h]; exacts [H.q_not_dvd_QS, H.d_not_dvd_QS]`. Establish `hl4 : l % 4 = 3`.

Establish `h1` using `hh.2.2.1`. Establish `h2` using `hh.2.2.2.1`. Apply the tactic sequence `rcases hl with h | h <;> rw [h] <;> omega`. Establish `hθ` using `theta_mem_Kur H J`. Establish `key : ∀ y z : Om l, J (thetaAt H.toHostRaw l) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} → J (H.sqq) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} → J (H.sqd) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} → y ∈ Kw.1 → z = y → Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}`.

Introduce `y z h1 h2 h3 hy _`. Establish `hle : K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} ≤ Kw.1` using `sup_le inf_le_left (IntermediateField.adjoin_le_iff.mpr (by simpa using hy))`. Establish `: FiniteDimensional ℚ_[l] ↥Kw.1` using `Kw.2`. Establish `hfd : FiniteDimensional ℚ_[l] ↥(K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y})` using `FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective`. Establish `hcl : IsClosed ((K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} : IntermediateField ℚ_[l] (Om l)) : Set (Om l))` using `Submodule.closed_of_finiteDimensional (K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}).toSubalgebra.toSubmodule`.

Use `le_antisymm (fun x hx => ?_) hle` and prove the remaining obligations. Use `closure_minimal ?_ hcl (hdense hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `image_le H J hlS _ h1 h2 h3 x`. Establish `hK0 : ∀ x : H.E, J x ∈ MaximalUnramifiedExtension l → ∀ y : Om l, J x ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}` using `fun x hx y => (le_sup_left : K0 Kw ≤ _) ⟨hE x, hx⟩`.

Establish `hself : ∀ y : Om l, y ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}` using `fun y => (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _) (IntermediateField.mem_adjoin_simple_self _ _)`. Establish `main : ∃ y : Om l, y ^ 2 = -(l : Om l) ∧ Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}`. Break down `hl with h | h` into its components or cases. Use `⟨J (H.sqq), by rw [ha]; exact congrArg (fun n : ℕ => -(n : Om l)) h.symm, key _ _ (hK0 _ hθ _) (hself _) (hK0 _ ?_ _) (hE _) rfl⟩` and prove the remaining obligations. Conclude with `sqrt_mem_Kur H.d hh.2.1 (by have := hh.2.2.2.1; omega) (by rw [h]; exact hqd.2.2.1.symm) _ hb`.

Use `⟨J (H.sqd), by rw [hb]; exact congrArg (fun n : ℕ => -(n : Om l)) h.symm, key _ _ (hK0 _ hθ _) (hK0 _ ?_ _) (hself _) (hE _) rfl⟩` and prove the remaining obligations. Conclude with `sqrt_mem_Kur H.q hh.1 (by have := hh.2.2.1; omega) (by rw [h]; exact hqd.2.2.1) _ ha`. Use `⟨main, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hK⟩` from `main`. Rewrite using `[hK]`.

Conclude with `sup_le le_sup_left (IntermediateField.adjoin_le_iff.mpr (by simpa using sqrt_mem_Ks hl4 Kw y hy))`.
-/
theorem local_pre (hl : l = H.q ∨ l = H.d) (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) :
    (∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}) ∧ Kw.1 ≤ Ks Kw 1 := by
  have hh := H.hyp
  have hqd := H.hypOdd
  have ha : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
    rw [← map_pow, H.sqq_sq]; simp
  have hb : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
    rw [← map_pow, H.sqd_sq]; simp
  have hlS : ¬ l ∣ H.QS := by rcases hl with h | h <;> rw [h]; exacts [H.q_not_dvd_QS, H.d_not_dvd_QS]
  have hl4 : l % 4 = 3 := by
    have h1 := hh.2.2.1
    have h2 := hh.2.2.2.1
    rcases hl with h | h <;> rw [h] <;> omega
  have hθ := theta_mem_Kur H J

  have key : ∀ y z : Om l, J (thetaAt H.toHostRaw l) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} →
      J (H.sqq) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} →
      J (H.sqd) ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} → y ∈ Kw.1 → z = y →
      Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
    intro y z h1 h2 h3 hy _
    have hle : K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} ≤ Kw.1 :=
      sup_le inf_le_left (IntermediateField.adjoin_le_iff.mpr (by simpa using hy))
    have : FiniteDimensional ℚ_[l] ↥Kw.1 := Kw.2
    have hfd : FiniteDimensional ℚ_[l] ↥(K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion hle).injective
    have hcl : IsClosed ((K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} :
        IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
      Submodule.closed_of_finiteDimensional
        (K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y}).toSubalgebra.toSubmodule
    refine le_antisymm (fun x hx => ?_) hle
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨x, rfl⟩
    exact image_le H J hlS _ h1 h2 h3 x
  have hK0 : ∀ x : H.E, J x ∈ MaximalUnramifiedExtension l → ∀ y : Om l,
      J x ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    fun x hx y => (le_sup_left : K0 Kw ≤ _) ⟨hE x, hx⟩
  have hself : ∀ y : Om l, y ∈ K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    fun y => (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have main : ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = K0 Kw ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
    rcases hl with h | h
    · refine ⟨J (H.sqq), by rw [ha]; exact congrArg (fun n : ℕ => -(n : Om l)) h.symm, key _ _ (hK0 _ hθ _) (hself _) (hK0 _ ?_ _) (hE _) rfl⟩
      exact sqrt_mem_Kur H.d hh.2.1 (by have := hh.2.2.2.1; omega) (by rw [h]; exact hqd.2.2.1.symm) _ hb
    · refine ⟨J (H.sqd), by rw [hb]; exact congrArg (fun n : ℕ => -(n : Om l)) h.symm, key _ _ (hK0 _ hθ _) (hK0 _ ?_ _) (hself _) (hE _) rfl⟩
      exact sqrt_mem_Kur H.q hh.1 (by have := hh.2.2.1; omega) (by rw [h]; exact hqd.2.2.1) _ ha
  refine ⟨main, ?_⟩
  obtain ⟨y, hy, hK⟩ := main
  rw [hK]
  exact sup_le le_sup_left (IntermediateField.adjoin_le_iff.mpr
    (by simpa using sqrt_mem_Ks hl4 Kw y hy))

end Local

/- English proof (translation)
The claim follows from `local_pre D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) hl (D.nbr i w hw).Kw (D.nbr i w hw).j_E (D.nbr i w hw).j_dense`.
-/
theorem preamble_first_clauses (D : D7) (i : D.nd.Loc) (hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (∃ y : Formalism.BasicNotions.Loc.Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ∧
      (D.nbr i w hw).Kw.1 = Formalism.BasicNotions.Loc.K0 (D.nbr i w hw).Kw ⊔
        IntermediateField.adjoin ℚ_[D.nd.l i] {y}) ∧
    (D.nbr i w hw).Kw.1 ≤ Formalism.BasicNotions.Loc.Ks (D.nbr i w hw).Kw 1 :=
  local_pre D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) hl (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense

def DegreeClauses (D : D7) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      Module.finrank ↥(Formalism.BasicNotions.Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 = 2 ∧
      Module.finrank ℚ_[D.nd.l i] ↥(Formalism.BasicNotions.Loc.Ks (D.nbr i w hw).Kw 1) =
        (D.nd.l i - 1) / 2 * Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1

/- English proof (translation)
Introduce `i hl w hw` and use `⟨(preamble_first_clauses D i hl w hw).1, (preamble_first_clauses D i hl w hw).2, (h i hl w hw).1, (h i hl w hw).2⟩`.
-/
theorem preamble_of_degree_clauses (D : D7) (h : DegreeClauses D) : Conclusion0 D :=
  fun i hl w hw => ⟨(preamble_first_clauses D i hl w hw).1, (preamble_first_clauses D i hl w hw).2, (h i hl w hw).1, (h i hl w hw).2⟩

section Proviso

open Ideal

end Proviso

section Kill

open Formalism.MainNotions.N

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.EmbeddingTypeJumps

end
