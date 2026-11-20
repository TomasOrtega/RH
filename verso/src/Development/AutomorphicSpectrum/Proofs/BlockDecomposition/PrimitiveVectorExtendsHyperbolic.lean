import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GermConstantsEqAlongAffineSpaceSquare
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans

open GlobalTheory.CompanionTheory.SW.QuasiRefl Matrix

/- English proof (translation)
Take `⟨ci, hci⟩` from `hu.exists_right_inv`. Use `set p := hform σ J y' y with hp`. Establish `hyy' : hform σ J y y' = σ p` using `by rw [hp, hform_conj_symm hσ hJ]`. Establish `hsc : σ p * σ ci = 1` using `by rw [← map_mul, hci, map_one]`. Use `set d : n → A := y - (1 : A) • y' with hd`.

Establish `hdy : hform σ J d y = -p`. Rewrite using `[hd, hform_sub_left, hy, map_one, one_mul, ← hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdy' : hform σ J d y' = σ p`. Rewrite using `[hd, hform_sub_left, hyy', hy']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdd : hform σ J d d = -p - σ p` using `by conv_lhs => rw [hd, hform_sub_right]`. Rewrite using `[← hd, hdy, hdy']`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (-ci) + σ (-ci) = (-ci) * σ (-ci) * hform σ J d d`.

Rewrite using `[map_neg, hdd]`. Take the linear combination `(σ ci) * hci + ci * hsc`. Use `⟨((qr hσ hJ d (-ci) hc : UJ σ J) : GL n A), SetLike.coe_mem _, ?_⟩` and prove the remaining obligations. Use `show qrMat σ J d (-ci) *ᵥ y = y'`. Rewrite using `[qrMat_mulVec, hdy]`.

Use function extensionality and compare the values at `i`. Simplify using `only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]`. Take the linear combination `(-(y i - y' i)) * hci`.
-/
theorem carry {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
    {J : Matrix n n A} (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (y y' : n → A)
    (hy : hform σ J y y = 0) (hy' : hform σ J y' y' = 0) (hu : IsUnit (hform σ J y' y)) :
    ∃ g ∈ UJ σ J, (g : Matrix n n A) *ᵥ y = y' := by
  obtain ⟨ci, hci⟩ := hu.exists_right_inv
  set p := hform σ J y' y with hp
  have hyy' : hform σ J y y' = σ p := by rw [hp, hform_conj_symm hσ hJ]
  have hsc : σ p * σ ci = 1 := by rw [← map_mul, hci, map_one]
  set d : n → A := y - (1 : A) • y' with hd
  have hdy : hform σ J d y = -p := by
    rw [hd, hform_sub_left, hy, map_one, one_mul, ← hp]
    ring
  have hdy' : hform σ J d y' = σ p := by
    rw [hd, hform_sub_left, hyy', hy']
    ring
  have hdd : hform σ J d d = -p - σ p := by
    conv_lhs => rw [hd, hform_sub_right]
    rw [← hd, hdy, hdy']
    ring
  have hc : (-ci) + σ (-ci) = (-ci) * σ (-ci) * hform σ J d d := by
    rw [map_neg, hdd]
    linear_combination (σ ci) * hci + ci * hsc
  refine ⟨((qr hσ hJ d (-ci) hc : UJ σ J) : GL n A), SetLike.coe_mem _, ?_⟩
  show qrMat σ J d (-ci) *ᵥ y = y'
  rw [qrMat_mulVec, hdy]
  funext i
  simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  linear_combination (-(y i - y' i)) * hci

/- English proof (translation)
Simplify using `only [hform, Fin.sum_univ_succ, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_hyp {A : Type} [CommRing A] (σ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin (M + 2) → A) :
    hform σ (hypOne J) x y = σ (x 0) * y 1 + σ (x 1) * y 0 +
      hform σ J (fun i => x i.succ.succ) (fun i => y i.succ.succ) := by
  simp only [hform, Fin.sum_univ_succ, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one,
    hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero,
    hypOne_rest_one, hypOne_rest_rest]
  simp
  ring

/- English proof (translation)
Distinguish the cases in `h1 : x 1 ∈ P`. Use `swap`. Conclude with `⟨0, Or.inl h1⟩`. Distinguish the cases in `h0 : x 0 ∈ P`. Use `swap`.

Conclude with `⟨0, Or.inr (by simpa [hform] using h0)⟩`. Take `⟨i, hi⟩` from `hprim`. Choose the witnesses or unpack the hypotheses as in `⟨j, rfl⟩ : ∃ j : Fin M, i = j.succ.succ := by`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => exact absurd h0 hi`.

Consider the case `succ i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => exact absurd h1 hi`. Consider the case `succ j => exact ⟨j, rfl⟩`. Use `set w : Fin M → A := fun i => x i.succ.succ with hw`.

Establish `hex : ∃ k, (J *ᵥ w) k ∉ P`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `e : w = Ji *ᵥ (J *ᵥ w)`. Rewrite using `[Matrix.mulVec_mulVec, mul_eq_one_comm.1 hJi, one_mulVec]`.

Apply `hi` to reduce the goal to its premises. Use `show w j ∈ P`. Rewrite using `[e]`. Simplify using `only [mulVec, dotProduct]`. Conclude with `P.sum_mem fun k _ => P.mul_mem_left _ (hc k)`.

Take `⟨k, hk⟩` from `hex`. Use `⟨Pi.single k 1, Or.inr fun hmem => hk ?_⟩` and prove the remaining obligations. Establish `e : hform σ J (Pi.single k 1) w = (J *ᵥ w) k`. Establish `: σ ∘ (Pi.single k 1 : Fin M → A) = Pi.single k 1`. Use function extensionality and compare the values at `l`.

Apply the tactic sequence `by_cases h : l = k <;> simp [h]`. Rewrite using `[hform_eq_dot, this]`. Simplify using the standard rewrite rules. Rewrite `hmem` using `[e]`. Conclude with `(Ideal.add_mem_iff_right P h0).1 hmem`.
-/
theorem exists_u_local {A : Type} [CommRing A] (σ : A →+* A) {M : ℕ}
    (J Ji : Matrix (Fin M) (Fin M) A) (hJi : J * Ji = 1) (x : Fin (M + 2) → A) (P : Ideal A)
    (hprim : ∃ i, x i ∉ P) :
    ∃ u : Fin M → A, x 1 ∉ P ∨ x 0 + hform σ J u (fun i => x i.succ.succ) ∉ P := by
  by_cases h1 : x 1 ∈ P
  swap
  · exact ⟨0, Or.inl h1⟩
  by_cases h0 : x 0 ∈ P
  swap
  · exact ⟨0, Or.inr (by simpa [hform] using h0)⟩
  obtain ⟨i, hi⟩ := hprim
  obtain ⟨j, rfl⟩ : ∃ j : Fin M, i = j.succ.succ := by
    induction i using Fin.cases with
    | zero => exact absurd h0 hi
    | succ i =>
      induction i using Fin.cases with
      | zero => exact absurd h1 hi
      | succ j => exact ⟨j, rfl⟩
  set w : Fin M → A := fun i => x i.succ.succ with hw
  have hex : ∃ k, (J *ᵥ w) k ∉ P := by
    by_contra hc
    push_neg at hc
    have e : w = Ji *ᵥ (J *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hJi, one_mulVec]
    apply hi
    show w j ∈ P
    rw [e]
    simp only [mulVec, dotProduct]
    exact P.sum_mem fun k _ => P.mul_mem_left _ (hc k)
  obtain ⟨k, hk⟩ := hex
  refine ⟨Pi.single k 1, Or.inr fun hmem => hk ?_⟩
  have e : hform σ J (Pi.single k 1) w = (J *ᵥ w) k := by
    have : σ ∘ (Pi.single k 1 : Fin M → A) = Pi.single k 1 := by
      funext l
      by_cases h : l = k <;> simp [h]
    rw [hform_eq_dot, this]
    simp
  rw [e] at hmem
  exact (Ideal.add_mem_iff_right P h0).1 hmem

/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]`.
-/
theorem hform_comb {A : Type} [CommRing A] (σ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (c c' : A) (u v w : Fin M → A) :
    hform σ J (c • u + c' • v) w = σ c * hform σ J u w + σ c' * hform σ J v w := by
  simp [hform, Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]

/- English proof (translation)
Distinguish the cases in `hdist : ∃ P Q : Ideal A, P.IsMaximal ∧ Q.IsMaximal ∧ P ≠ Q`. Take `⟨P, Q, hP, hQ, hne⟩` from `hdist`. Establish `hall : ∀ R : Ideal A, R.IsMaximal → R = P ∨ R = Q`. Introduce `R hR`. Apply the tactic sequence `rcases hmax R hR with h | h <;> rcases hmax P hP with h' | h' <;>`.

Apply the tactic sequence `rcases hmax Q hQ with h'' | h'' <;> simp_all`. Establish `h1 : (1 : A) ∈ P ⊔ Q`. Rewrite using `[Ideal.IsMaximal.coprime_of_ne hP hQ hne]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨p, hp, q, hq, hpq⟩` from `Submodule.mem_sup.1 h1`.

Take `⟨uP, huP⟩` from `hloc P hP`. Take `⟨uQ, huQ⟩` from `hloc Q hQ`. Establish `hval : a + hform σ J (σ q • uP + σ p • uQ) w = q * (a + hform σ J uP w) + p * (a + hform σ J uQ w)`. Rewrite using `[hform_comb, hσ, hσ]`. Take the linear combination `(-a) * hpq`.

Use `⟨σ q • uP + σ p • uQ, fun R hR => ?_⟩` and prove the remaining obligations. Establish `hq1 : q ∉ P` using `fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ P.add_mem hp h))`. Establish `hp1 : p ∉ Q` using `fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ Q.add_mem h hq))`. Break down `hall R hR with rfl | rfl` into its components or cases. Break down `huP with h | h` into its components or cases.

Conclude with `Or.inl h`. Use `Or.inr fun hm => ?_` and prove the remaining obligations. Rewrite `hm` using `[hval]`. Establish `h3` using `(Ideal.add_mem_iff_left R (R.mul_mem_right _ hp)).1 hm`. Break down `hP.isPrime.mem_or_mem h3 with h4 | h4` into its components or cases.

Conclude with `hq1 h4`. Conclude with `h h4`. Break down `huQ with h | h` into its components or cases. Conclude with `Or.inl h`. Use `Or.inr fun hm => ?_` and prove the remaining obligations.

Rewrite `hm` using `[hval]`. Establish `h3` using `(Ideal.add_mem_iff_right R (R.mul_mem_right _ hq)).1 hm`. Break down `hQ.isPrime.mem_or_mem h3 with h4 | h4` into its components or cases. Conclude with `hp1 h4`. Conclude with `h h4`.

Use `push_neg at hdist`. Distinguish the cases in `hex : ∃ P : Ideal A, P.IsMaximal`. Take `⟨P, hP⟩` from `hex`. Take `⟨u, hu⟩` from `hloc P hP`. Conclude with `⟨u, fun R hR => by rw [hdist R P hR hP]; exact hu⟩`.

Conclude with `⟨0, fun P hP => absurd ⟨P, hP⟩ hex⟩`.
-/
theorem exists_u {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P₁ P₂ : Ideal A)
    (hmax : ∀ P : Ideal A, P.IsMaximal → P = P₁ ∨ P = P₂) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) A) (w : Fin M → A) (b a : A)
    (hloc : ∀ P : Ideal A, P.IsMaximal → ∃ u : Fin M → A, b ∉ P ∨ a + hform σ J u w ∉ P) :
    ∃ u : Fin M → A, ∀ P : Ideal A, P.IsMaximal → b ∉ P ∨ a + hform σ J u w ∉ P := by
  by_cases hdist : ∃ P Q : Ideal A, P.IsMaximal ∧ Q.IsMaximal ∧ P ≠ Q
  · obtain ⟨P, Q, hP, hQ, hne⟩ := hdist
    have hall : ∀ R : Ideal A, R.IsMaximal → R = P ∨ R = Q := by
      intro R hR
      rcases hmax R hR with h | h <;> rcases hmax P hP with h' | h' <;>
        rcases hmax Q hQ with h'' | h'' <;> simp_all
    have h1 : (1 : A) ∈ P ⊔ Q := by
      rw [Ideal.IsMaximal.coprime_of_ne hP hQ hne]
      trivial
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 h1
    obtain ⟨uP, huP⟩ := hloc P hP
    obtain ⟨uQ, huQ⟩ := hloc Q hQ
    have hval : a + hform σ J (σ q • uP + σ p • uQ) w =
        q * (a + hform σ J uP w) + p * (a + hform σ J uQ w) := by
      rw [hform_comb, hσ, hσ]
      linear_combination (-a) * hpq
    refine ⟨σ q • uP + σ p • uQ, fun R hR => ?_⟩
    have hq1 : q ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ P.add_mem hp h))
    have hp1 : p ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ Q.add_mem h hq))
    rcases hall R hR with rfl | rfl
    · rcases huP with h | h
      · exact Or.inl h
      · refine Or.inr fun hm => ?_
        rw [hval] at hm
        have h3 := (Ideal.add_mem_iff_left R (R.mul_mem_right _ hp)).1 hm
        rcases hP.isPrime.mem_or_mem h3 with h4 | h4
        · exact hq1 h4
        · exact h h4
    · rcases huQ with h | h
      · exact Or.inl h
      · refine Or.inr fun hm => ?_
        rw [hval] at hm
        have h3 := (Ideal.add_mem_iff_right R (R.mul_mem_right _ hq)).1 hm
        rcases hQ.isPrime.mem_or_mem h3 with h4 | h4
        · exact hp1 h4
        · exact h h4
  · push_neg at hdist
    by_cases hex : ∃ P : Ideal A, P.IsMaximal
    · obtain ⟨P, hP⟩ := hex
      obtain ⟨u, hu⟩ := hloc P hP
      exact ⟨u, fun R hR => by rw [hdist R P hR hP]; exact hu⟩
    · exact ⟨0, fun P hP => absurd ⟨P, hP⟩ hex⟩

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `pair : ∀ P : Ideal A, P.IsMaximal → ∀ m n : ℤ, IsUnit ((n : A) - m) → a - (m : A) * b ∈ P → a - (n : A) * b ∈ P → False`. Introduce `P hP m n hu h1 h3`. Take `⟨v, hv⟩` from `hu.exists_left_inv`.

Establish `hb : b ∈ P`. Establish `e : b = v * ((a - (m : A) * b) - (a - (n : A) * b))`. Take the linear combination `(-b) * hv`. Rewrite using `[e]`. Conclude with `P.mul_mem_left _ (P.sub_mem h1 h3)`.

Establish `ha : a ∈ P`. Establish `e : a = (a - (m : A) * b) + (m : A) * b` using `by ring`. Rewrite using `[e]`. Conclude with `P.add_mem h1 (P.mul_mem_left _ hb)`. Break down `hab P hP with h | h` into its components or cases.

Conclude with `h hb`. Conclude with `h ha`. Take `⟨Pa, ha, ha'⟩` from `exists_max_ideal_of_mem_nonunits (show a - ((0 : ℤ) : A) * b ∈ nonunits A from hc 0)`. Take `⟨Pb, hb, hb'⟩` from `exists_max_ideal_of_mem_nonunits (show a - ((1 : ℤ) : A) * b ∈ nonunits A from hc 1)`. Take `⟨Pc, hc₁, hc'⟩` from `exists_max_ideal_of_mem_nonunits (show a - ((-1 : ℤ) : A) * b ∈ nonunits A from hc (-1))`.

Establish `u01 : IsUnit (((1 : ℤ) : A) - ((0 : ℤ) : A))` using `by simp`. Establish `u0m : IsUnit (((-1 : ℤ) : A) - ((0 : ℤ) : A))` using `by simp`. Establish `u1m : IsUnit (((1 : ℤ) : A) - ((-1 : ℤ) : A))`. Establish `: ((1 : ℤ) : A) - ((-1 : ℤ) : A) = 2` using `by push_cast; ring`. Rewrite using `[this]`.

Conclude with `h2`. Establish `hpig : Pa = Pb ∨ Pa = Pc ∨ Pb = Pc`. Apply the tactic sequence `rcases hmax Pa ha with h | h <;> rcases hmax Pb hb with h' | h' <;>`. Apply the tactic sequence `rcases hmax Pc hc₁ with h'' | h'' <;> simp_all`. Break down `hpig with h | h | h` into its components or cases.

Substitute `h` using the available equality. Conclude with `pair Pa ha 0 1 u01 ha' hb'`. Substitute `h` using the available equality. Conclude with `pair Pa ha 0 (-1) u0m ha' hc'`. Substitute `h` using the available equality.

Conclude with `pair Pb hb (-1) 1 u1m hc' hb'`.
-/
theorem exists_mu {A : Type} [CommRing A] (P₁ P₂ : Ideal A)
    (hmax : ∀ P : Ideal A, P.IsMaximal → P = P₁ ∨ P = P₂) (h2 : IsUnit (2 : A)) (a b : A)
    (hab : ∀ P : Ideal A, P.IsMaximal → b ∉ P ∨ a ∉ P) : ∃ μ : ℤ, IsUnit (a - (μ : A) * b) := by
  by_contra hc
  push_neg at hc
  have pair : ∀ P : Ideal A, P.IsMaximal → ∀ m n : ℤ, IsUnit ((n : A) - m) →
      a - (m : A) * b ∈ P → a - (n : A) * b ∈ P → False := by
    intro P hP m n hu h1 h3
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have hb : b ∈ P := by
      have e : b = v * ((a - (m : A) * b) - (a - (n : A) * b)) := by
        linear_combination (-b) * hv
      rw [e]
      exact P.mul_mem_left _ (P.sub_mem h1 h3)
    have ha : a ∈ P := by
      have e : a = (a - (m : A) * b) + (m : A) * b := by ring
      rw [e]
      exact P.add_mem h1 (P.mul_mem_left _ hb)
    rcases hab P hP with h | h
    · exact h hb
    · exact h ha
  obtain ⟨Pa, ha, ha'⟩ := exists_max_ideal_of_mem_nonunits (show a - ((0 : ℤ) : A) * b ∈ nonunits A from hc 0)
  obtain ⟨Pb, hb, hb'⟩ := exists_max_ideal_of_mem_nonunits (show a - ((1 : ℤ) : A) * b ∈ nonunits A from hc 1)
  obtain ⟨Pc, hc₁, hc'⟩ := exists_max_ideal_of_mem_nonunits (show a - ((-1 : ℤ) : A) * b ∈ nonunits A from hc (-1))
  have u01 : IsUnit (((1 : ℤ) : A) - ((0 : ℤ) : A)) := by simp
  have u0m : IsUnit (((-1 : ℤ) : A) - ((0 : ℤ) : A)) := by simp
  have u1m : IsUnit (((1 : ℤ) : A) - ((-1 : ℤ) : A)) := by
    have : ((1 : ℤ) : A) - ((-1 : ℤ) : A) = 2 := by push_cast; ring
    rw [this]
    exact h2
  have hpig : Pa = Pb ∨ Pa = Pc ∨ Pb = Pc := by
    rcases hmax Pa ha with h | h <;> rcases hmax Pb hb with h' | h' <;>
      rcases hmax Pc hc₁ with h'' | h'' <;> simp_all
  rcases hpig with h | h | h
  · subst h
    exact pair Pa ha 0 1 u01 ha' hb'
  · subst h
    exact pair Pa ha 0 (-1) u0m ha' hc'
  · subst h
    exact pair Pb hb (-1) 1 u1m hc' hb'

/- English proof (translation)
Establish `hH : ∀ i j, σ (hypOne J j i) = hypOne J i j`. Introduce `i j`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`.

Consider the case `zero => simp [hypOne_zero_zero]`. Consider the case `succ j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact (map_one σ).trans rfl`. Consider the case `succ j => exact (map_zero σ).trans rfl`.

Consider the case `succ i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact (map_one σ).trans rfl`.

Consider the case `succ j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact (map_zero σ).trans rfl`. Consider the case `succ j => exact (map_zero σ).trans rfl`. Consider the case `succ i`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact (map_zero σ).trans rfl`. Consider the case `succ j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact (map_zero σ).trans rfl`.

Consider the case `succ j => exact hJ i j`. Use `set w : Fin M → A := fun i => x i.succ.succ with hw`. Take `⟨u, hu⟩` from `exists_u σ hσ P₁ P₂ hmax J w (x 1) (x 0) (fun P hP => exists_u_local σ J Ji hJi x P (hprim P hP))`. Take `⟨i2, hi2⟩` from `h2.exists_right_inv`. Establish `hsi2 : σ i2 = i2`.

Establish `h : 2 * σ i2 = 1`. Use `congrArg σ hi2` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, map_ofNat]`. Then use the resulting hypothesis. Take the linear combination `i2 * h - σ i2 * hi2`. Use `set q := hform σ J u u with hq`.

Establish `hsq : σ q = q` using `hform_conj_symm hσ hJ u u`. Use `set a := x 0 + hform σ J u w - q * i2 * x 1 with ha`. Take `⟨di, hdi⟩` from `hδ.exists_left_inv`. Establish `hab : ∀ P : Ideal A, P.IsMaximal → δ * x 1 ∉ P ∨ a ∉ P`. Introduce `P hP`.

Distinguish the cases in `h1 : x 1 ∈ P`. Use `right`. Introduce `hm`. Break down `hu P hP with h | h` into its components or cases. Conclude with `h h1`.

Apply `h` to reduce the goal to its premises. Establish `e : x 0 + hform σ J u w = a + q * i2 * x 1` using `by rw [ha]; ring`. Rewrite using `[e]`. Conclude with `P.add_mem hm (P.mul_mem_left _ h1)`. Use `left`.

Introduce `hm`. Apply `h1` to reduce the goal to its premises. Establish `e : x 1 = di * (δ * x 1)` using `by linear_combination (-x 1) * hdi`. Rewrite using `[e]`. Conclude with `P.mul_mem_left _ hm`.

Take `⟨μ, hμ⟩` from `exists_mu P₁ P₂ hmax h2 a (δ * x 1) hab`. Use `set t : A := -(q * i2) + (μ : A) * δ with ht`. Establish `hst : σ t = -(q * i2) - (μ : A) * δ`. Rewrite using `[ht, map_add, map_neg, map_mul, map_mul, hsq, hsi2, hδs, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.

Set `z : Fin (M + 2) → A` to `Fin.cons t (Fin.cons 1 u)`. Set `e : Fin (M + 2) → A` to `Fin.cons 1 fun _ => 0`. Establish `z0 : z 0 = t` using `rfl`. Establish `z1 : z 1 = 1` using `rfl`. Establish `zt : (fun i : Fin M => z i.succ.succ) = u` using `rfl`.

Establish `e0' : e 0 = 1` using `rfl`. Establish `e1' : e 1 = 0` using `rfl`. Establish `et : (fun i : Fin M => e i.succ.succ) = 0` using `rfl`. Establish `hzz : hform σ (hypOne J) z z = 0`. Rewrite using `[hform_hyp, z0, z1, zt, hst, map_one, ← hq, ht]`.

Take the linear combination `(-q) * hi2`. Establish `hee : hform σ (hypOne J) e e = 0`. Rewrite using `[hform_hyp, e0', e1', et]`. Simplify using `[hform]`. Establish `hze : hform σ (hypOne J) z e = 1`.

Rewrite using `[hform_hyp, z1, e0', e1', zt, et]`. Simplify using `[hform]`. Establish `hzx : hform σ (hypOne J) z x = a - (μ : A) * (δ * x 1)`. Rewrite using `[hform_hyp, z0, z1, zt, hst, map_one, ← hw, ha]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hxz : IsUnit (hform σ (hypOne J) x z)`. Rewrite using `[← hform_conj_symm hσ hH z x, hzx]`. Conclude with `hμ.map σ`. Take `⟨g₁, hg₁, h₁⟩` from `carry hσ hH e z hee hzz (by rw [hze]; exact isUnit_one)`. Take `⟨g₂, hg₂, h₂⟩` from `carry hσ hH z x hzz hiso hxz`.

Use `⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩` and prove the remaining obligations. Use `show ((g₂ * g₁ : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) *ᵥ e = x`. Rewrite using `[Units.val_mul, ← mulVec_mulVec, h₁, h₂]`.
-/
theorem orbit_ring {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a)
    (h2 : IsUnit (2 : A)) (δ : A) (hδ : IsUnit δ) (hδs : σ δ = -δ) (P₁ P₂ : Ideal A)
    (hmax : ∀ P : Ideal A, P.IsMaximal → P = P₁ ∨ P = P₂) {M : ℕ}
    (J Ji : Matrix (Fin M) (Fin M) A) (hJi : J * Ji = 1) (hJ : ∀ i j, σ (J j i) = J i j)
    (x : Fin (M + 2) → A) (hprim : ∀ P : Ideal A, P.IsMaximal → ∃ i, x i ∉ P)
    (hiso : hform σ (hypOne J) x x = 0) :
    ∃ g ∈ UJ σ (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A) *ᵥ
      (Fin.cons 1 fun _ => 0 : Fin (M + 2) → A) = x := by
  have hH : ∀ i j, σ (hypOne J j i) = hypOne J i j := by
    intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [hypOne_zero_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => exact (map_one σ).trans rfl
        | succ j => exact (map_zero σ).trans rfl
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (map_one σ).trans rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => exact (map_zero σ).trans rfl
          | succ j => exact (map_zero σ).trans rfl
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (map_zero σ).trans rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => exact (map_zero σ).trans rfl
          | succ j => exact hJ i j
  set w : Fin M → A := fun i => x i.succ.succ with hw
  obtain ⟨u, hu⟩ := exists_u σ hσ P₁ P₂ hmax J w (x 1) (x 0)
    (fun P hP => exists_u_local σ J Ji hJi x P (hprim P hP))
  obtain ⟨i2, hi2⟩ := h2.exists_right_inv
  have hsi2 : σ i2 = i2 := by
    have h : 2 * σ i2 = 1 := by
      have := congrArg σ hi2
      rwa [map_mul, map_one, map_ofNat] at this
    linear_combination i2 * h - σ i2 * hi2
  set q := hform σ J u u with hq
  have hsq : σ q = q := hform_conj_symm hσ hJ u u
  set a := x 0 + hform σ J u w - q * i2 * x 1 with ha
  obtain ⟨di, hdi⟩ := hδ.exists_left_inv
  have hab : ∀ P : Ideal A, P.IsMaximal → δ * x 1 ∉ P ∨ a ∉ P := by
    intro P hP
    by_cases h1 : x 1 ∈ P
    · right
      intro hm
      rcases hu P hP with h | h
      · exact h h1
      · apply h
        have e : x 0 + hform σ J u w = a + q * i2 * x 1 := by rw [ha]; ring
        rw [e]
        exact P.add_mem hm (P.mul_mem_left _ h1)
    · left
      intro hm
      apply h1
      have e : x 1 = di * (δ * x 1) := by linear_combination (-x 1) * hdi
      rw [e]
      exact P.mul_mem_left _ hm
  obtain ⟨μ, hμ⟩ := exists_mu P₁ P₂ hmax h2 a (δ * x 1) hab
  set t : A := -(q * i2) + (μ : A) * δ with ht
  have hst : σ t = -(q * i2) - (μ : A) * δ := by
    rw [ht, map_add, map_neg, map_mul, map_mul, hsq, hsi2, hδs, map_intCast]
    ring
  let z : Fin (M + 2) → A := Fin.cons t (Fin.cons 1 u)
  let e : Fin (M + 2) → A := Fin.cons 1 fun _ => 0
  have z0 : z 0 = t := rfl
  have z1 : z 1 = 1 := rfl
  have zt : (fun i : Fin M => z i.succ.succ) = u := rfl
  have e0' : e 0 = 1 := rfl
  have e1' : e 1 = 0 := rfl
  have et : (fun i : Fin M => e i.succ.succ) = 0 := rfl
  have hzz : hform σ (hypOne J) z z = 0 := by
    rw [hform_hyp, z0, z1, zt, hst, map_one, ← hq, ht]
    linear_combination (-q) * hi2
  have hee : hform σ (hypOne J) e e = 0 := by
    rw [hform_hyp, e0', e1', et]
    simp [hform]
  have hze : hform σ (hypOne J) z e = 1 := by
    rw [hform_hyp, z1, e0', e1', zt, et]
    simp [hform]
  have hzx : hform σ (hypOne J) z x = a - (μ : A) * (δ * x 1) := by
    rw [hform_hyp, z0, z1, zt, hst, map_one, ← hw, ha]
    ring
  have hxz : IsUnit (hform σ (hypOne J) x z) := by
    rw [← hform_conj_symm hσ hH z x, hzx]
    exact hμ.map σ
  obtain ⟨g₁, hg₁, h₁⟩ := carry hσ hH e z hee hzz (by rw [hze]; exact isUnit_one)
  obtain ⟨g₂, hg₂, h₂⟩ := carry hσ hH z x hzz hiso hxz
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  show ((g₂ * g₁ : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) *ᵥ e = x
  rw [Units.val_mul, ← mulVec_mulVec, h₁, h₂]

/- English proof (translation)
Introduce `T _ O s hs hss h2 ⟨δ, hδ, hδs⟩ π₁ π₂ hmax M J Ji hJO hJiO hJJ hJ x hprim hiso`. Set `τ : O →+* O` to `s.restrict O O hs`. Establish `hτ : ∀ a : O, ((τ a : O) : T) = s a` using `fun a => rfl`. Set `JO : Matrix (Fin M) (Fin M) O` to `fun i j => ⟨J i j, hJO i j⟩`. Set `JiO : Matrix (Fin M) (Fin M) O` to `fun i j => ⟨Ji i j, hJiO i j⟩`.

Establish `hmapJ : (hypOne JO).map O.subtype = hypOne J`. Use extensionality with `i j`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`.

Consider the case `zero => rfl`. Consider the case `succ j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rfl`. Consider the case `succ j => rfl`.

Consider the case `succ i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rfl`.

Consider the case `succ j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rfl`. Consider the case `succ j => rfl`. Consider the case `succ i`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rfl`. Consider the case `succ j`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rfl`.

Consider the case `succ j => rfl`. Establish `hmul : JO * JiO = 1`. Apply `Matrix.map_injective (f := O.subtype) Subtype.val_injective` to reduce the goal to its premises. Use `show (JO * JiO).map O.subtype = (1 : Matrix (Fin M) (Fin M) O).map O.subtype`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `hJJ`. Establish `hiso0 : hform τ (hypOne JO) x x = 0`. Establish `h3 : ((hform τ (hypOne JO) x x : O) : T) = hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T))`. Rewrite using `[← hmapJ]`. Simplify using `[hform, hτ]`.

Conclude with `Subtype.ext (h3.trans hiso)`. Take `⟨g0, hg0, hgx⟩` from `orbit_ring τ (fun a => Subtype.ext (hss a)) h2 δ hδ (Subtype.ext hδs) (Ideal.span {π₁}) (Ideal.span {π₂}) hmax JO JiO hmul (fun i j => Subtype.ext (hJ i j)) x hprim hiso0`. Establish `hval : ∀ g : GL (Fin (M + 2)) O, ((Matrix.GeneralLinearGroup.map O.subtype g : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) = (g : Matrix (Fin (M + 2)) (Fin (M + 2)) O).map O.subtype` using `fun g => rfl`. Use `⟨Matrix.GeneralLinearGroup.map O.subtype g0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) * hypOne JO * (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) = hypOne JO` using `hg0`.

Establish `h1` using `congrArg (RingHom.mapMatrix O.subtype) h0`. Rewrite `h1` using `[map_mul, map_mul]`. Use `show cT s ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) * hypOne J * ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) = hypOne J`. Establish `e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O)) = cT s ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `e2 : RingHom.mapMatrix O.subtype (hypOne JO) = hypOne J` using `hmapJ`. Establish `e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) = ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T)` using `rfl`. Rewrite `h1` using `[e1, e2, e3]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `i`.

Establish `h3` using `congrArg Subtype.val (congrFun hgx i)`. Rewrite using `[← h3, hval]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Subring.coe_subtype]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rfl`. Consider the case `succ j => rfl`. Introduce `i j`. Rewrite using `[hval]`.

Conclude with `((g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) i j).2`. Introduce `i j`. Rewrite using `[← map_inv, hval]`. Conclude with `(((g0⁻¹ : GL (Fin (M + 2)) O) : Matrix (Fin (M + 2)) (Fin (M + 2)) O) i j).2`.
-/
theorem trans_orbit : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  intro T _ O s hs hss h2 ⟨δ, hδ, hδs⟩ π₁ π₂ hmax M J Ji hJO hJiO hJJ hJ x hprim hiso
  let τ : O →+* O := s.restrict O O hs
  have hτ : ∀ a : O, ((τ a : O) : T) = s a := fun a => rfl
  let JO : Matrix (Fin M) (Fin M) O := fun i j => ⟨J i j, hJO i j⟩
  let JiO : Matrix (Fin M) (Fin M) O := fun i j => ⟨Ji i j, hJiO i j⟩
  have hmapJ : (hypOne JO).map O.subtype = hypOne J := by
    ext i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => rfl
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => rfl
          | succ j => rfl
      | succ i =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => rfl
          | succ j => rfl
  have hmul : JO * JiO = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    show (JO * JiO).map O.subtype = (1 : Matrix (Fin M) (Fin M) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hJJ
  have hiso0 : hform τ (hypOne JO) x x = 0 := by
    have h3 : ((hform τ (hypOne JO) x x : O) : T) =
        hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) := by
      rw [← hmapJ]
      simp [hform, hτ]
    exact Subtype.ext (h3.trans hiso)
  obtain ⟨g0, hg0, hgx⟩ := orbit_ring τ (fun a => Subtype.ext (hss a)) h2 δ hδ
    (Subtype.ext hδs) (Ideal.span {π₁}) (Ideal.span {π₂}) hmax JO JiO hmul
    (fun i j => Subtype.ext (hJ i j)) x hprim hiso0
  have hval : ∀ g : GL (Fin (M + 2)) O,
      ((Matrix.GeneralLinearGroup.map O.subtype g : GL (Fin (M + 2)) T) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) T) =
      (g : Matrix (Fin (M + 2)) (Fin (M + 2)) O).map O.subtype := fun g => rfl
  refine ⟨Matrix.GeneralLinearGroup.map O.subtype g0, ?_, ?_, ?_, ?_⟩
  · have h0 : cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) * hypOne JO *
        (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) = hypOne JO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) T) * hypOne J *
      ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) T) = hypOne J
    have e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O)) =
        cT s ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) T) := by
      ext i j
      rfl
    have e2 : RingHom.mapMatrix O.subtype (hypOne JO) = hypOne J := hmapJ
    have e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) =
        ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) T) := rfl
    rwa [e1, e2, e3] at h1
  · funext i
    have h3 := congrArg Subtype.val (congrFun hgx i)
    rw [← h3, hval]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Subring.coe_subtype]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    induction j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  · intro i j
    rw [hval]
    exact ((g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) i j).2
  · intro i j
    rw [← map_inv, hval]
    exact (((g0⁻¹ : GL (Fin (M + 2)) O) : Matrix (Fin (M + 2)) (Fin (M + 2)) O) i j).2

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans
