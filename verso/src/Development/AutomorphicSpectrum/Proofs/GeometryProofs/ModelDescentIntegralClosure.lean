import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverRamifiedExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverDvrExtensionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

noncomputable section

open GroundTheory.Heights₂.Heights.NumbersDVR (classList classNum cycEval ratDiv IsVerticalDivisor pairNum psumExpansion isHomogeneous_psumExpansion)

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
  {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)]

def Scales (P : Ideal (MvPolynomial (Σ k, J k) O)) (P' : Ideal (MvPolynomial (Σ k, J k) O')) (d e : ℕ) : Prop :=
  ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P →
    ∀ l : List (K → ℤ), l.length = d →
      cycList (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) l

/- English proof (translation)
Use `(Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_` and prove the remaining obligations. Introduce `W hW`. Assume the negation of the conclusion as `h`. Apply `hW` to reduce the goal to its premises. Simplify using `[GroundTheory.Heights₂.Heights.NumbersDVR.divCycle, h]`.
-/
theorem support_divCycle_finite {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (P : Ideal (MvPolynomial (Σ k, J k) R))
    (f : MvPolynomial (Σ k, J k) R) : (Function.support (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [GroundTheory.Heights₂.Heights.NumbersDVR.divCycle, h]

/- English proof (translation)
Establish `h` using `hH (mem_support_iff.mp hμ)`. Simplify using `only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]`. Rewrite using `[← h]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum]`.
-/
theorem length_classList {σ : Type} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) {m : ℕ} {H : MvPolynomial σ ℝ}
    (hH : H.IsHomogeneous m) (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

/- English proof (translation)
Unfold `cycNum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[hs a f hf hfP _ (by rw [List.length_append, length_classList cls μ hH hμ, hQ])]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cycNum_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {a : K → ℕ} {f : MvPolynomial (Σ k, J k) O} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a) (hfP : f ∉ P)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ} (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) cls H Q =
      e * cycNum (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) cls H Q := by
  unfold cycNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [hs a f hf hfP _ (by rw [List.length_append, length_classList cls μ hH hμ, hQ])]
  push_cast
  ring

/- English proof (translation)
Establish `h1` using `(cycNum_int_and_comb O K J σ cls Q).1 (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) (support_divCycle_finite P f) H`. Establish `h2` using `(cycNum_int_and_comb O' K J σ cls Q).1 _ (support_divCycle_finite P' (MvPolynomial.map (algebraMap O O') f)) H`. Establish `hH' : (MvPolynomial.map (Int.castRingHom ℝ) H).IsHomogeneous m` using `hH.map _`. Establish `h3` using `cycNum_scale hs hf hfP cls hH' Q hQ`. Rewrite `h3` using `[h1, h2]`.

Conclude with `h3` after adjusting the coercions.
-/
theorem cycEval_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {a : K → ℕ} {f : MvPolynomial (Σ k, J k) O} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a) (hfP : f ∉ P)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {m : ℕ} (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycEval (fun W => classNum cls H Q W) (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) =
      e * cycEval (fun W => classNum cls H Q W) (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) := by
  have h1 := (cycNum_int_and_comb O K J σ cls Q).1 (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) (support_divCycle_finite P f) H
  have h2 := (cycNum_int_and_comb O' K J σ cls Q).1 _
    (support_divCycle_finite P' (MvPolynomial.map (algebraMap O O') f)) H
  have hH' : (MvPolynomial.map (Int.castRingHom ℝ) H).IsHomogeneous m := hH.map _
  have h3 := cycNum_scale hs hf hfP cls hH' Q hQ
  rw [h1, h2] at h3
  exact_mod_cast h3

/- English proof (translation)
Unfold `cycEval ratDiv`. Simplify using `only [sub_mul]`. Use `finsum_sub_distrib ?_ ?_` and prove the remaining obligations. Conclude with `(support_divCycle_finite P f).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f W = 0 from h])`. Conclude with `(support_divCycle_finite P g).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g W = 0 from h])`.
-/
theorem cycEval_ratDiv {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : Ideal (MvPolynomial (Σ k, J k) R) → ℤ) (P : Ideal (MvPolynomial (Σ k, J k) R)) (f g : MvPolynomial (Σ k, J k) R) :
    cycEval n (ratDiv P f g) = cycEval n (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) - cycEval n (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g) := by
  unfold cycEval ratDiv
  simp only [sub_mul]
  refine finsum_sub_distrib ?_ ?_
  · exact (support_divCycle_finite P f).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f W = 0 from h])
  · exact (support_divCycle_finite P g).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g W = 0 from h])

/- English proof (translation)
Unfold `LocPair.ck pairNum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -, -⟩` from `hT i`. Establish `hm : k - 1 + Q.length = d` using `by omega`.

Establish `hH` using `isHomogeneous_psumExpansion r k i`. Use `show cycEval _ (ratDiv P' (MvPolynomial.map (algebraMap O O') (T.f i)) (MvPolynomial.map (algebraMap O O') (T.g i))) = _`. Rewrite using `[cycEval_ratDiv, cycEval_ratDiv, mul_sub]`. Conclude with `congrArg₂ _ (cycEval_scale hs hf hfP _ hH Q hm) (cycEval_scale hs hg hgP _ hH Q hm)`.
-/
theorem ck_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e) {ϖ : O}
    {r : ℕ} (T : LocPair J O (Fin r)) (hT : T.IsVert P ϖ) {k : ℕ} (hk : 1 ≤ k) (Q : List (K → ℤ))
    (hQ : Q.length + k = d + 1) :
    (T.map (algebraMap O O')).ck P' k Q = e * T.ck P k Q := by
  unfold LocPair.ck pairNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -, -⟩ := hT i
  have hm : k - 1 + Q.length = d := by omega
  have hH := isHomogeneous_psumExpansion r k i
  show cycEval _ (ratDiv P' (MvPolynomial.map (algebraMap O O') (T.f i))
    (MvPolynomial.map (algebraMap O O') (T.g i))) = _
  rw [cycEval_ratDiv, cycEval_ratDiv, mul_sub]
  exact congrArg₂ _ (cycEval_scale hs hf hfP _ hH Q hm) (cycEval_scale hs hg hgP _ hH Q hm)

/- English proof (translation)
Unfold `laNum`. Establish `hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O))` using `by simp`. Establish `hH : (MvPolynomial.psum (Fin r) ℤ (k - 1)).IsHomogeneous (k - 1)`. Unfold `MvPolynomial.psum`. Conclude with `IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℤ i).pow (k - 1)`.

Establish `hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ)` using `isWeightedHomogeneous_C _ _`. Rewrite using `[hc, cycEval_scale hs hC hp x hH Q (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem laNum_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {p : ℕ} (hp : (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P) {r : ℕ} (x : Fin r → K → ℤ) {k : ℕ} (hk : 1 ≤ k)
    (Q : List (K → ℤ)) (hQ : Q.length + k = d + 1) :
    laNum P' (p : O') x k Q = e * laNum P (p : O) x k Q := by
  unfold laNum
  have hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O)) := by simp
  have hH : (MvPolynomial.psum (Fin r) ℤ (k - 1)).IsHomogeneous (k - 1) := by
    unfold MvPolynomial.psum
    exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℤ i).pow (k - 1)
  have hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
    isWeightedHomogeneous_C _ _
  rw [hc, cycEval_scale hs hC hp x hH Q (by omega)]
  ring

/- English proof (translation)
Break down `τ with τ | τ` into its components or cases. Conclude with `IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℝ (τ, i)).pow m`. Conclude with `IsHomogeneous.sum _ _ _ fun i _ => by simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m`.
-/
theorem isHomogeneous_liePs {Ψ : Type} {N : ℕ} (j m : ℕ) (τ : Ψ ⊕ Ψ) :
    (liePs (N := N) j m τ : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous m := by
  rcases τ with τ | τ
  · exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℝ (τ, i)).pow m
  · exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m

/- English proof (translation)
Unfold `bracket`. Establish `h : (∑ τ', C (GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (Sum.inl τ) τ') * (liePs (N` using `N) j (k - 1) τ' : MvPolynomial (Ψ × Fin N) ℝ)).IsHomogeneous (k - 1) := IsHomogeneous.sum _ _ _ fun τ' _ => by`. Simplify using `using (isHomogeneous_C _ _).mul (isHomogeneous_liePs j (k - 1) τ')`. Establish `h2` using `(isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul h`. Rewrite `h2` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_bracket {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (p k : ℕ) (τ : Ψ) : (bracket (N := N) j φ p k τ).IsHomogeneous (k - 1) := by
  unfold bracket
  have h : (∑ τ', C (GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (Sum.inl τ) τ') *
      (liePs (N := N) j (k - 1) τ' : MvPolynomial (Ψ × Fin N) ℝ)).IsHomogeneous (k - 1) :=
    IsHomogeneous.sum _ _ _ fun τ' _ => by
      simpa using (isHomogeneous_C _ _).mul (isHomogeneous_liePs j (k - 1) τ')
  have h2 := (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul h
  rwa [zero_add] at h2

end

end GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

namespace GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

noncomputable section

open GroundTheory.Heights₂.Heights.NumbersDVR (classList classNum cycEval ratDiv IsVerticalDivisor pairNum psumExpansion isHomogeneous_psumExpansion)

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
  {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)]

/- English proof (translation)
Introduce `τ k hk Q hQ`. Establish `h0` using `h τ k hk Q hQ`. Establish `e1 : ((T.map (algebraMap O O')).comp fun i : Fin N => (τ, i)) = (T.comp fun i : Fin N => (τ, i)).map (algebraMap O O')` using `rfl`. Establish `hTc : (T.comp fun i : Fin N => (τ, i)).IsVert P ϖ` using `fun i => hT (τ, i)`. Establish `hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O))` using `by simp`.

Establish `hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ)` using `isWeightedHomogeneous_C _ _`. Rewrite `h0` using `[e1, ck_scale hs _ hTc hk Q hQ, show (T.map (algebraMap O O')).x = T.x from rfl, hc, cycNum_scale hs hC hp T.x (isHomogeneous_bracket j φ p k τ) Q (by omega)]`. Establish `he' : (e : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 he.ne'`. Move the coercions through the operations in `at h0`. Conclude with `mul_left_cancel₀ he' h0`.
-/
theorem flag_descends {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ}
    (hs : Scales P P' d e) (he : 0 < e) {ϖ : O} {p : ℕ} (hp : (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (T : LocPair J O (Ψ × Fin N)) (hT : T.IsVert P ϖ)
    (h : FlagChernComparison P' d p j φ (T.map (algebraMap O O'))) : FlagChernComparison P d p j φ T := by
  intro τ k hk Q hQ
  have h0 := h τ k hk Q hQ
  have e1 : ((T.map (algebraMap O O')).comp fun i : Fin N => (τ, i)) =
      (T.comp fun i : Fin N => (τ, i)).map (algebraMap O O') := rfl
  have hTc : (T.comp fun i : Fin N => (τ, i)).IsVert P ϖ := fun i => hT (τ, i)
  have hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O)) := by simp
  have hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
    isWeightedHomogeneous_C _ _
  rw [e1, ck_scale hs _ hTc hk Q hQ, show (T.map (algebraMap O O')).x = T.x from rfl, hc,
    cycNum_scale hs hC hp T.x (isHomogeneous_bracket j φ p k τ) Q (by omega)] at h0
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  push_cast at h0
  exact mul_left_cancel₀ he' h0

/- English proof (translation)
Introduce `k hk Q hQ`. Establish `h0` using `h k hk Q hQ`. Establish `he' : (e : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 he.ne'`. Rewrite `h0` using `[ck_scale hs _ hl hk Q hQ, ck_scale hs _ ho hk Q hQ]`. Distinguish the cases in `hp0 : p = 0`.

Substitute `hp0` using the available equality. Establish `hz : (1 / (((0 : ℕ) : ℝ) ^ k - 1) - 1 / (((0 : ℕ) : ℝ) - 1)) = 0`. Establish `: k ≠ 0` using `by omega`. Simplify using `[this]`. Rewrite `h0`, the goal using `[hz, zero_mul]`.

Move the coercions through the operations in `at h0`. Establish `h1 : (e : ℝ) * (((lie.ck P k Q : ℤ) : ℝ) + ((om.ck P k Q : ℤ) : ℝ)) = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 h1).resolve_left he'`. Rewrite `h0` using `[show (lie.map (algebraMap O O')).x = lie.x from rfl, laNum_scale hs (hp hp0) lie.x hk Q hQ]`. Move the coercions through the operations in `at h0`.

Use `mul_left_cancel₀ he' ?_` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem whole_descends {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ}
    (hs : Scales P P' d e) (he : 0 < e) {ϖ : O} {p : ℕ}
    (hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P) {r s : ℕ}
    (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)) (hl : lie.IsVert P ϖ) (ho : om.IsVert P ϖ)
    (h : BundleChernComparison P' d p (lie.map (algebraMap O O')) (om.map (algebraMap O O'))) : BundleChernComparison P d p lie om := by
  intro k hk Q hQ
  have h0 := h k hk Q hQ
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  rw [ck_scale hs _ hl hk Q hQ, ck_scale hs _ ho hk Q hQ] at h0
  by_cases hp0 : p = 0
  · subst hp0
    have hz : (1 / (((0 : ℕ) : ℝ) ^ k - 1) - 1 / (((0 : ℕ) : ℝ) - 1)) = 0 := by
      have : k ≠ 0 := by omega
      simp [this]
    rw [hz, zero_mul] at h0 ⊢
    push_cast at h0
    have h1 : (e : ℝ) * (((lie.ck P k Q : ℤ) : ℝ) + ((om.ck P k Q : ℤ) : ℝ)) = 0 := by linarith
    exact (mul_eq_zero.1 h1).resolve_left he'
  · rw [show (lie.map (algebraMap O O')).x = lie.x from rfl, laNum_scale hs (hp hp0) lie.x hk Q hQ] at h0
    push_cast at h0
    refine mul_left_cancel₀ he' ?_
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

namespace GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ _ K _ _ J _ y d hM hI O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ hinj ϖ hϖ p`. Take `⟨hEq, hM'⟩` from `GlobalTheory.T.model_over_dvr_extension O Ω K J y d hM hI O' Ω' hinj`. Establish `hCmem : ∀ a : O, (C a : MvPolynomial (Σ k, J k) O) ∈ pointIdeal O y → a = 0` using `fun a ha => by`. Establish `h' : a ∈ (pointIdeal O y).comap (C : O →+* MvPolynomial (Σ k, J k) O)` using `ha`. Rewrite `h'` using `[hM.noTorsion]`.

Simplify using `using h'`. Establish `hΩ : Function.Injective (algebraMap O Ω)`. Use `(injective_iff_map_eq_zero _).2 fun a ha => hCmem a ?_` and prove the remaining obligations. Use `show GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap O y (C a) = 0`. Simplify using `[GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, ha]`.

Establish `hOO : Function.Injective (algebraMap O O')`. Establish `h2 : Function.Injective (algebraMap O' Ω' ∘ algebraMap O O')`. Establish `e : (algebraMap O' Ω' ∘ algebraMap O O' : O → Ω') = algebraMap Ω Ω' ∘ algebraMap O Ω`. Use function extensionality and compare the values at `a`. Simplify using `only [Function.comp]`.

Rewrite using `[← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']`. Rewrite using `[e]`. Conclude with `(algebraMap Ω Ω').injective.comp hΩ`. Conclude with `h2.of_comp`. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible O'`.

Establish `hne : algebraMap O O' ϖ ≠ 0` using `fun h0 => hϖ.ne_zero (hOO (by simpa using h0))`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hne hϖ'`. Establish `hrel : algebraMap O O' ϖ = ((u⁻¹ : O'ˣ) : O') * ϖ' ^ e`. Rewrite using `[← hu]`. Simplify using `[mul_comm]`.

Establish `he : 0 < e`. Break down `Nat.eq_zero_or_pos e with rfl | h` into its components or cases. It suffices to derive a contradiction. Establish `hU : IsUnit (algebraMap O O' ϖ)`. Rewrite using `[hrel]`.

Simplify using the standard rewrite rules. Conclude with `hϖ.not_isUnit ((isUnit_map_iff (algebraMap O O') ϖ).1 hU)`. Conclude with `h`. Establish `hs : ModelDescentAlt.Scales (pointIdeal O y) ((pointIdeal O y).map (MvPolynomial.map (algebraMap O O'))) d e` using `fun a f hf hfP l hl => GlobalTheory.T.model_over_ramified_extension O O' ϖ ϖ' u⁻¹ e hϖ hϖ' he hrel K J (pointIdeal O y) d hM (hEq ▸ hM') a f hf hfP l hl`. Establish `hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ pointIdeal O y` using `fun h0 hmem => by`.

Establish `h1` using `hCmem _ hmem`. Establish `h2 : ((p : ℕ) : Ω) = 0`. Use `congrArg (algebraMap O Ω) h1` as an intermediate fact. Simplify using `using this`. Conclude with `h0 (by exact_mod_cast h2)`.

Rewrite using `[hEq]`. Conclude with `⟨fun h0 Ψ _ _ N j φ T hT h => ModelDescentAlt.flag_descends hs he (hp h0) j φ T hT h, fun r s lie om hl ho h => ModelDescentAlt.whole_descends hs he hp lie om hl ho h⟩`.
-/
theorem model_descends_from_dvr_ext : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O), Irreducible ϖ → ∀ p : ℕ, (p ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair J O (Ψ × Fin N)), T.IsVert (pointIdeal O y) ϖ → FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p j φ (T.map (algebraMap O O')) → FlagChernComparison (pointIdeal O y) d p j φ T) ∧ ∀ (r s : ℕ) (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)), lie.IsVert (pointIdeal O y) ϖ → om.IsVert (pointIdeal O y) ϖ → BundleChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (lie.map (algebraMap O O')) (om.map (algebraMap O O')) → BundleChernComparison (pointIdeal O y) d p lie om := by
  intro O _ _ _ Ω _ _ _ K _ _ J _ y d hM hI O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ hinj ϖ hϖ p
  obtain ⟨hEq, hM'⟩ := GlobalTheory.T.model_over_dvr_extension O Ω K J y d hM hI O' Ω' hinj
  have hCmem : ∀ a : O, (C a : MvPolynomial (Σ k, J k) O) ∈ pointIdeal O y → a = 0 := fun a ha => by
    have h' : a ∈ (pointIdeal O y).comap (C : O →+* MvPolynomial (Σ k, J k) O) := ha
    rw [hM.noTorsion] at h'
    simpa using h'
  have hΩ : Function.Injective (algebraMap O Ω) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => hCmem a ?_
    show GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap O y (C a) = 0
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, ha]
  have hOO : Function.Injective (algebraMap O O') := by
    have h2 : Function.Injective (algebraMap O' Ω' ∘ algebraMap O O') := by
      have e : (algebraMap O' Ω' ∘ algebraMap O O' : O → Ω') = algebraMap Ω Ω' ∘ algebraMap O Ω := by
        funext a
        simp only [Function.comp]
        rw [← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']
      rw [e]
      exact (algebraMap Ω Ω').injective.comp hΩ
    exact h2.of_comp
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hne : algebraMap O O' ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hOO (by simpa using h0))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ'
  have hrel : algebraMap O O' ϖ = ((u⁻¹ : O'ˣ) : O') * ϖ' ^ e := by
    rw [← hu]
    simp [mul_comm]
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      have hU : IsUnit (algebraMap O O' ϖ) := by
        rw [hrel]
        simp
      exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap O O') ϖ).1 hU)
    · exact h
  have hs : ModelDescentAlt.Scales (pointIdeal O y) ((pointIdeal O y).map (MvPolynomial.map (algebraMap O O'))) d e :=
    fun a f hf hfP l hl => GlobalTheory.T.model_over_ramified_extension O O' ϖ ϖ' u⁻¹ e hϖ hϖ' he hrel K J (pointIdeal O y) d hM (hEq ▸ hM') a f hf hfP l hl
  have hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ pointIdeal O y := fun h0 hmem => by
    have h1 := hCmem _ hmem
    have h2 : ((p : ℕ) : Ω) = 0 := by
      have := congrArg (algebraMap O Ω) h1
      simpa using this
    exact h0 (by exact_mod_cast h2)
  rw [hEq]
  exact ⟨fun h0 Ψ _ _ N j φ T hT h => ModelDescentAlt.flag_descends hs he (hp h0) j φ T hT h,
    fun r s lie om hl ho h => ModelDescentAlt.whole_descends hs he hp lie om hl ho h⟩

end GlobalTheory.CompanionTheory.Ar.Num
