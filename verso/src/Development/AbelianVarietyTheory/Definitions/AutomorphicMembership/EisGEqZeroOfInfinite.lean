import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

namespace GlobalTheory.Mem.Per.Model

/- English proof (translation)
Unfold `eisG`. Rewrite using `[← tsum_mul_left]`. Set `f : {w : ℂ // w ∈ Λ ∧ w ≠ 0} → {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0}` to `fun w => ⟨δ * w.1, ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hδ w.2.2⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion.

Introduce `a b h`. Conclude with `Subtype.ext (mul_left_cancel₀ hδ (congrArg Subtype.val h))`. Introduce and unpack `⟨w, ⟨v, hv, rfl⟩, h0⟩`. Use `⟨⟨v, hv, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Simplify using `at h0`. Rewrite using `[← (Equiv.ofBijective f hf).tsum_eq]`. Use `tsum_congr fun w => ?_` and prove the remaining obligations. Simplify using `[f, mul_pow, mul_comm]`.
-/
theorem eisG_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (k : ℕ) :
    eisG (Λ.map (AddMonoidHom.mulLeft δ)) k = (δ ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [← tsum_mul_left]
  let f : {w : ℂ // w ∈ Λ ∧ w ≠ 0} → {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0} :=
    fun w => ⟨δ * w.1, ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hδ w.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (mul_left_cancel₀ hδ (congrArg Subtype.val h))
    · rintro ⟨w, ⟨v, hv, rfl⟩, h0⟩
      refine ⟨⟨v, hv, ?_⟩, rfl⟩
      rintro rfl
      simp at h0
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  refine tsum_congr fun w => ?_
  simp [f, mul_pow, mul_comm]

/- English proof (translation)
Unfold `TaylorLogMetric.discr g2 g3`. Rewrite using `[eisG_map _ _ hδ, eisG_map _ _ hδ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem discr_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 12)⁻¹ * TaylorLogMetric.discr Λ := by
  unfold TaylorLogMetric.discr g2 g3
  rw [eisG_map _ _ hδ, eisG_map _ _ hδ]
  field_simp
  ring

/- English proof (translation)
Unfold `jLat`. Rewrite using `[discr_map _ _ hδ]`. Unfold `g2`. Rewrite using `[eisG_map _ _ hδ]`. Distinguish the cases in `h : TaylorLogMetric.discr Λ = 0`.

Simplify using `[h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jLat_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    jLat (Λ.map (AddMonoidHom.mulLeft δ)) = jLat Λ := by
  unfold jLat
  rw [discr_map _ _ hδ]
  unfold g2
  rw [eisG_map _ _ hδ]
  by_cases h : TaylorLogMetric.discr Λ = 0
  · simp [h]
  · field_simp
    ring

variable {LL : Type} [Field LL] [NumberField LL]

/- English proof (translation)
Take `⟨δ, hδ⟩` from `IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr Λ) (n := 12) (by norm_num)`. Establish `h0 : δ ≠ 0` using `by rintro rfl; apply h; rw [← hδ]; simp`. Take `⟨a, ha⟩` from `ha`. Use `⟨Λ.map (AddMonoidHom.mulLeft δ), ?_, a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[discr_map _ _ h0, hδ, inv_mul_cancel₀ h]`.

Rewrite using `[jLat_map _ _ h0, ha]`.
-/
theorem exists_isConjLat_self (emb : LL →+* ℂ) (Λ : AddSubgroup ℂ) (h : TaylorLogMetric.discr Λ ≠ 0)
    (ha : ∃ a : LL, emb a = jLat Λ) : ∃ Λ', IsConjLat emb emb Λ Λ' := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr Λ) (n := 12) (by norm_num)
  have h0 : δ ≠ 0 := by rintro rfl; apply h; rw [← hδ]; simp
  obtain ⟨a, ha⟩ := ha
  refine ⟨Λ.map (AddMonoidHom.mulLeft δ), ?_, a, ha, ?_⟩
  · rw [discr_map _ _ h0, hδ, inv_mul_cancel₀ h]
  · rw [jLat_map _ _ h0, ha]

/- English proof (translation)
Unfold `eisG`. Apply `tsum_eq_zero_of_not_summable` to reduce the goal to its premises. Introduce `hs`. Establish `ht` using `hs.tendsto_cofinite_zero`. Establish `he` using `(Metric.tendsto_nhds.1 ht) 1 one_pos`.

Rewrite `he` using `[Filter.eventually_cofinite]`. Apply `h` to reduce the goal to its premises. Use `(he.image Subtype.val).subset ?_` and prove the remaining obligations. Introduce and unpack `w ⟨h1, h2, h3⟩`. Use `⟨⟨w, h1, h2⟩, ?_, rfl⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, dist_zero_right, not_lt, norm_div, norm_one, norm_pow]`. Establish `hp : 0 < ‖w‖ ^ (2 * k)` using `pow_pos (norm_pos_iff.2 h2) _`. Rewrite using `[le_div_iff₀ hp, one_mul]`. Conclude with `pow_le_one₀ (norm_nonneg _) h3`.
-/
theorem eisG_eq_zero_of_infinite (Λ : AddSubgroup ℂ) (h : {w : ℂ | w ∈ Λ ∧ w ≠ 0 ∧ ‖w‖ ≤ 1}.Infinite) (k : ℕ) :
    eisG Λ k = 0 := by
  unfold eisG
  apply tsum_eq_zero_of_not_summable
  intro hs
  have ht := hs.tendsto_cofinite_zero
  have he := (Metric.tendsto_nhds.1 ht) 1 one_pos
  rw [Filter.eventually_cofinite] at he
  apply h
  refine (he.image Subtype.val).subset ?_
  rintro w ⟨h1, h2, h3⟩
  refine ⟨⟨w, h1, h2⟩, ?_, rfl⟩
  simp only [Set.mem_setOf_eq, dist_zero_right, not_lt, norm_div, norm_one, norm_pow]
  have hp : 0 < ‖w‖ ^ (2 * k) := pow_pos (norm_pos_iff.2 h2) _
  rw [le_div_iff₀ hp, one_mul]
  exact pow_le_one₀ (norm_nonneg _) h3

/- English proof (translation)
Assume the negation of the conclusion as `hi`. Use `h.1` as an intermediate fact. Unfold `TaylorLogMetric.discr g2 g3 at this`. Rewrite `this` using `[eisG_eq_zero_of_infinite _ hi, eisG_eq_zero_of_infinite _ hi]`. Evaluate the numerical expressions using `at this`.
-/
theorem finite_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    {w : ℂ | w ∈ Λ' ∧ w ≠ 0 ∧ ‖w‖ ≤ 1}.Finite := by
  by_contra hi
  have := h.1
  unfold TaylorLogMetric.discr g2 g3 at this
  rw [eisG_eq_zero_of_infinite _ hi, eisG_eq_zero_of_infinite _ hi] at this
  norm_num at this

/- English proof (translation)
Introduce and unpack `rfl`. Use `h.1` as an intermediate fact. Use `haveI : IsEmpty {w : ℂ // w ∈ (⊥ : AddSubgroup ℂ) ∧ w ≠ 0} := ⟨fun w => w.2.2 (AddSubgroup.mem_bot.1 w.2.1)⟩`. Unfold `TaylorLogMetric.discr g2 g3 eisG at *`. Rewrite `*` using `[tsum_empty, tsum_empty]`.

Evaluate the numerical expressions using `at *`.
-/
theorem ne_bot_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') : Λ' ≠ ⊥ := by
  rintro rfl
  have := h.1
  haveI : IsEmpty {w : ℂ // w ∈ (⊥ : AddSubgroup ℂ) ∧ w ≠ 0} := ⟨fun w => w.2.2 (AddSubgroup.mem_bot.1 w.2.1)⟩
  unfold TaylorLogMetric.discr g2 g3 eisG at *
  rw [tsum_empty, tsum_empty] at *
  norm_num at *

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Establish `hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hb : H.𝔟 ≠ ⊥`. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Use `H.𝔟_spec.1` as an intermediate fact.

Rewrite `this` using `[h0, Ideal.bot_mul]`. Conclude with `this`. Establish `hA : H.AA0 ≠ 0`. Unfold `Host.AA0`. Conclude with `inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)`.

Take `⟨a, ha0, ha⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger hA |>.imp fun a h => h`. Take `⟨b, hb1, hb0⟩` from `(Submodule.ne_bot_iff _).1 hd`. Introduce `h`. Establish `: embE (H.sigmaOf g ((a : H.E) * (b : H.E))) ∈ ellLat H embE g` using `Submodule.subset_span ⟨_, ha, b, hb1, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Simplify using `[ha0, hb0] at this`.
-/
theorem ellLat_ne_bot (embE : H.E →+* LL) (g : R.GG) : ellLat H embE g ≠ ⊥ := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    have := H.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at this
    exact this
  have hA : H.AA0 ≠ 0 := by
    unfold Host.AA0
    exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hA |>.imp fun a h => h
  obtain ⟨b, hb1, hb0⟩ := (Submodule.ne_bot_iff _).1 hd
  intro h
  have : embE (H.sigmaOf g ((a : H.E) * (b : H.E))) ∈ ellLat H embE g :=
    Submodule.subset_span ⟨_, ha, b, hb1, rfl⟩
  rw [h, Submodule.mem_bot] at this
  simp [ha0, hb0] at this

/- English proof (translation)
Introduce and unpack `rfl`. Apply `ellLat_ne_bot H embE g` to reduce the goal to its premises. Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
theorem ne_zero_of_isGen {embE : H.E →+* LL} {g : R.GG} {x : LL} (h : IsGen H embE g x) : x ≠ 0 := by
  rintro rfl
  apply ellLat_ne_bot H embE g
  rw [← h]; simp

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (h.2 g)`.
-/
theorem gen_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (g) :
    IsGen H embE g (gen H embE g) := Classical.epsilon_spec (h.2 g)

/- English proof (translation)
Establish `h : Submodule.span (𝓞 LL) {x} = Submodule.span (𝓞 LL) {y}` using `hx.trans hy.symm`. Take `⟨u, hu⟩` from `Submodule.span_singleton_eq_span_singleton.1 h`. Establish `hu1 : ∏ s : LL →+* ℂ, ‖s ((u : 𝓞 LL) : LL)‖ = 1`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom LL ℂ) (fun f => ‖f ((u : 𝓞 LL) : LL)‖) (fun φ => ‖φ ((u : 𝓞 LL) : LL)‖) (fun _ => rfl), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]`. Use `NumberField.Units.norm LL u` as an intermediate fact.

Simplify using `only [eq_ratCast, Complex.norm_ratCast]`. Conclude with `this` after adjusting the coercions. Rewrite using `[← hu]`. Simplify using `only [Units.smul_def, Algebra.smul_def, map_mul, norm_mul, Finset.prod_mul_distrib]`. Rewrite using `[show (∏ s : LL →+* ℂ, ‖s (algebraMap (𝓞 LL) LL u)‖) = 1 from hu1, one_mul]`.
-/
theorem prod_norm_eq_of_isGen {embE : H.E →+* LL} {g : R.GG} {x y : LL}
    (hx : IsGen H embE g x) (hy : IsGen H embE g y) :
    ∏ s : LL →+* ℂ, ‖s x‖ = ∏ s : LL →+* ℂ, ‖s y‖ := by
  have h : Submodule.span (𝓞 LL) {x} = Submodule.span (𝓞 LL) {y} := hx.trans hy.symm
  obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.1 h
  have hu1 : ∏ s : LL →+* ℂ, ‖s ((u : 𝓞 LL) : LL)‖ = 1 := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom LL ℂ) (fun f => ‖f ((u : 𝓞 LL) : LL)‖)
      (fun φ => ‖φ ((u : 𝓞 LL) : LL)‖) (fun _ => rfl), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]
    have := NumberField.Units.norm LL u
    simp only [eq_ratCast, Complex.norm_ratCast]
    exact_mod_cast this
  rw [← hu]
  simp only [Units.smul_def, Algebra.smul_def, map_mul, norm_mul, Finset.prod_mul_distrib]
  rw [show (∏ s : LL →+* ℂ, ‖s (algebraMap (𝓞 LL) LL u)‖) = 1 from hu1, one_mul]

/- English proof (translation)
Take `⟨L, hL⟩` from `GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ') (by rw [h.1]; exact one_ne_zero)`. Conclude with `⟨⟨L, hL⟩, (GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ' hL).1⟩`.
-/
theorem area_pos_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    (∃ L : PeriodPair, ∀ z, z ∈ Λ' ↔ z ∈ L.lattice) ∧ 0 < area Λ' := by
  obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ') (by rw [h.1]; exact one_ne_zero)
  exact ⟨⟨L, hL⟩, (GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ' hL).1⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `ha`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq (s a / 1728) (n := 3) (by norm_num)`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq ((s a / 1728 - 1) / 27) (n := 2) (by norm_num)`. Establish `h1 : x ^ 3 - 27 * y ^ 2 = 1` using `by rw [hx, hy]; ring`. Take `⟨L, h2, h3⟩` from `GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := x) (b := y) (by rw [h1]; exact one_ne_zero)`.

Establish `hd` using `GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)`. Establish `hD : TaylorLogMetric.discr L.lattice.toAddSubgroup = 1`. Unfold `TaylorLogMetric.discr`. Rewrite using `[hd.1, hd.2.1, h2, h3, h1]`. Use `⟨L.lattice.toAddSubgroup, hD, a, ha, ?_⟩` and prove the remaining obligations.

Unfold `jLat`. Rewrite using `[hD, hd.1, h2, hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isConjLat (emb s : LL →+* ℂ) (Λ : AddSubgroup ℂ) (ha : ∃ a : LL, emb a = jLat Λ) :
    ∃ Λ', IsConjLat emb s Λ Λ' := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (s a / 1728) (n := 3) (by norm_num)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((s a / 1728 - 1) / 27) (n := 2) (by norm_num)
  have h1 : x ^ 3 - 27 * y ^ 2 = 1 := by rw [hx, hy]; ring
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := x) (b := y)
    (by rw [h1]; exact one_ne_zero)
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hD : TaylorLogMetric.discr L.lattice.toAddSubgroup = 1 := by
    unfold TaylorLogMetric.discr; rw [hd.1, hd.2.1, h2, h3, h1]
  refine ⟨L.lattice.toAddSubgroup, hD, a, ha, ?_⟩
  unfold jLat
  rw [hD, hd.1, h2, hx]; ring

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (exists_isConjLat emb s _ h.1)`.
-/
theorem conjLat_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (s : LL →+* ℂ) :
    IsConjLat emb s (baseLat H) (conjLat H emb s) :=
  Classical.epsilon_spec (exists_isConjLat emb s _ h.1)

/- English proof (translation)
Establish `h1` using `(area_pos_of_isConjLat (conjLat_spec H h s)).2`. Establish `h2 : s (gen H embE (e τ).1) ≠ 0` using `(map_ne_zero s).2 (ne_zero_of_isGen H (gen_spec H h _))`. Establish `h3 : 0 < omAt H emb s (gen H embE (e τ).1)`. Unfold `omAt`. Use `norm_pos_iff.2 h2` as an intermediate fact.

Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression. Use `show posOr1 _ = _`. Unfold `posOr1`. Rewrite using `[if_pos h3]`.

Both sides reduce to the same expression.
-/
theorem om_eq {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) {I : Type}
    (e : I ≃ R.Psi) (τ : I) (s : LL →+* ℂ) :
    (trueGx H emb embE e).Om τ s = area (conjLat H emb s) / (Real.pi * ‖s (gen H embE (e τ).1)‖ ^ 2) := by
  have h1 := (area_pos_of_isConjLat (conjLat_spec H h s)).2
  have h2 : s (gen H embE (e τ).1) ≠ 0 := (map_ne_zero s).2 (ne_zero_of_isGen H (gen_spec H h _))
  have h3 : 0 < omAt H emb s (gen H embE (e τ).1) := by
    unfold omAt
    have := norm_pos_iff.2 h2
    have := Real.pi_pos
    positivity
  show posOr1 _ = _
  unfold posOr1
  rw [if_pos h3]; rfl

end GlobalTheory.Mem.Per.Model
