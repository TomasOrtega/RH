import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Mathlib.Topology.Algebra.ClopenNhdofOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

namespace UpperTheory.V.Chr.DecompositionCyclotomic

variable (l : ℕ) [hl : Fact l.Prime]

/- English proof (translation)
Establish `h` using `Nat.prime_iff_prime_int.mp hl.out`. Establish `he : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ)` using `by simp`. Rewrite using `[he, MulEquiv.prime_iff]`. Conclude with `h`.
-/
private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h := Nat.prime_iff_prime_int.mp hl.out
  have he : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [he, MulEquiv.prime_iff]
  exact h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

/- English proof (translation)
Use `haveI : NeZero l := ⟨hl.out.ne_zero⟩`. Unfold `normV`. Establish `hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (vQ l).asIdeal` using `by show _ = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)})`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `e : (𝓞 ℚ ⧸ (vQ l).asIdeal) ≃+* ZMod l` using `(Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)`.

Rewrite using `[Nat.card_congr e.toEquiv, Nat.card_zmod]`.
-/
private theorem normV_vQ : normV (vQ l) = l := by
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  unfold normV
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (vQ l).asIdeal := by
    show _ = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)})
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have e : (𝓞 ℚ ⧸ (vQ l).asIdeal) ≃+* ZMod l :=
    (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

/- English proof (translation)
Use `show _ ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _`. Rewrite using `[Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_intCast]`. Simplify using the standard rewrite rules.
-/
private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show _ ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_intCast]
  simp

/- English proof (translation)
Establish `h` using `A.valuation_le_one (n : A)`. Simplify using `using h`.
-/
private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  have h := A.valuation_le_one (n : A)
  simpa using h

/- English proof (translation)
Establish `hlp : Prime ((l : ℕ) : ℤ)` using `Nat.prime_iff_prime_int.mp hl.out`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hnd`. Take `⟨a, b, hab⟩` from `(Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd`.

Establish `h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1`. Use `push_cast`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h`. Rewrite `h1` using `[hab]`. Simplify using `at h1`. Introduce and unpack `⟨k, rfl⟩`.

Use `push_cast`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA`.
-/
private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  have hlp : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  constructor
  · intro h
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd
    have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    rw [hab] at h1
    simp at h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

/- English proof (translation)
Introduce `x`. Take `⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x` from `⟨Rat.ringOfIntegersEquiv x, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans (Rat.ringOfIntegersEquiv.symm_apply_apply x)⟩`. Rewrite using `[intCast_mem_vQ, ← val_intCast_lt_one_iff A hA m]`. Simplify using the standard rewrite rules.
-/
private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x,
      (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply x)⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA m]
  simp

end UpperTheory.V.Chr.DecompositionCyclotomic

/- English proof (translation)
Introduce `hx`. Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`. Use `open scoped Pointwise in (have h1 := MulAction.mem_stabilizer_iff.mp hτ`. Rewrite using `[← h1, ← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul]`. Conclude with `Set.smul_mem_smul_set hx)`.
-/
private theorem decomposition_cyclotomic_of_mem_dec {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation x ≤ 1 → A.valuation (τ x) ≤ 1 := by
  intro hx
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  open scoped Pointwise in
    (have h1 := MulAction.mem_stabilizer_iff.mp hτ
     rw [← h1, ← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul]
     exact Set.smul_mem_smul_set hx)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `decomposition_cyclotomic_of_mem_dec A τ⁻¹ ((Dec (F := ℚ) A).inv_mem hτ) _ h`. Simplify `h'` using `[AlgEquiv.aut_inv]`. Conclude with `decomposition_cyclotomic_of_mem_dec A τ hτ x`.
-/
private theorem decomposition_cyclotomic_of_mem_dec_second {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation (τ x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  constructor
  · intro h
    have h' := decomposition_cyclotomic_of_mem_dec A τ⁻¹ ((Dec (F := ℚ) A).inv_mem hτ) _ h
    simpa [AlgEquiv.aut_inv] using h'
  · exact decomposition_cyclotomic_of_mem_dec A τ hτ x

/- English proof (translation)
Establish `key : ∀ z : Ω, A.valuation z < 1 ↔ z = 0 ∨ (A.valuation z ≤ 1 ∧ ¬ A.valuation z⁻¹ ≤ 1)`. Introduce `z`. Distinguish the cases in `hz : z = 0`. Simplify using `[hz]`. Establish `hv0 : A.valuation z ≠ 0` using `by simpa using hz`.

Rewrite using `[map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← lt_iff_le_not_ge]`. Simplify using `[hz]`. Rewrite using `[key, key, ← map_inv₀ τ x, decomposition_cyclotomic_of_mem_dec_second A τ hτ, decomposition_cyclotomic_of_mem_dec_second A τ hτ, EmbeddingLike.map_eq_zero_iff]`.
-/
private theorem decomposition_cyclotomic_of_mem_dec_third {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation (τ x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ z : Ω, A.valuation z < 1 ↔ z = 0 ∨ (A.valuation z ≤ 1 ∧ ¬ A.valuation z⁻¹ ≤ 1) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hv0 : A.valuation z ≠ 0 := by simpa using hz
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← lt_iff_le_not_ge]
      simp [hz]
  rw [key, key, ← map_inv₀ τ x, decomposition_cyclotomic_of_mem_dec_second A τ hτ, decomposition_cyclotomic_of_mem_dec_second A τ hτ, EmbeddingLike.map_eq_zero_iff]

open UpperTheory.V.Chr.DecompositionCyclotomic in
/- English proof (translation)
Introduce `Ω _ _ _ p A hp hA`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hPO` using `isPlaceOver_vQ (l := p) A hA`. Take `⟨σ, hσ⟩` from `exists_isFrob hPO`. Establish `hσD : σ ∈ Dec (F` using `ℚ) A := hσ.1`.

Use `⟨?_, Ine_le_Dec A, σ, hσD, ?_, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hiD⟩ hi ⟨τ, hτ⟩`. Rewrite `hi`, the goal using `[Subgroup.mem_subgroupOf]`. Establish `hi2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (i x - x) < 1` using `hi.2`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `⟨(Dec (F := ℚ) A).mul_mem ((Dec (F := ℚ) A).mul_mem hτ hiD) ((Dec (F := ℚ) A).inv_mem hτ), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hτi : τ⁻¹ ∈ Dec (F` using `ℚ) A := (Dec (F := ℚ) A).inv_mem hτ`. Establish `hy : A.valuation (τ⁻¹ x) ≤ 1` using `decomposition_cyclotomic_of_mem_dec A τ⁻¹ hτi x hx`.

Establish `h3` using `hi2 _ hy`. Establish `heq : (τ * i * τ⁻¹) x - x = τ (i (τ⁻¹ x) - τ⁻¹ x)`. Simplify using `[AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv]`. Rewrite using `[heq, decomposition_cyclotomic_of_mem_dec_third A τ hτ]`. Conclude with `h3`.

Use `set K := (Subgroup.zpowers σ ⊔ Ine (F := ℚ) A).topologicalClosure with hK`. Establish `hKc : IsClosed (K : Set (G ℚ Ω))` using `Subgroup.isClosed_topologicalClosure _`. Establish `hcs` using `ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K, hKc⟩`. Use `le_trans ?_ hcs.ge` and prove the remaining obligations. Use `le_sInf fun N hN => ?_` and prove the remaining obligations.

Establish `hKN : K ≤ N` using `hN.2`. Conclude with `Kum.decGen ℚ Ω A (vQ p) σ N hPO hσ hN.1 (le_trans (le_sup_right.trans (Subgroup.le_topologicalClosure _)) hKN) (hKN (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))))`. Introduce `l _ hlp`. Establish `hnot : ((l : ℕ) : 𝓞 ℚ) ∉ (vQ p).asIdeal`. Introduce `h`.

Establish `h'` using `(intCast_mem_vQ (l := p) (l : ℤ)).mp (by simpa using h)`. Rewrite `h'` using `[Int.natCast_dvd_natCast]`. Conclude with `hlp ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp h').symm`. Rewrite using `[cycZ_of_isFrob hnot hPO hσ, normV_vQ]`.
-/
theorem UpperTheory.V.Chr.decCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 →
          ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ Ine (F := ℚ) A ≤ Dec (F := ℚ) A ∧
          ∃ γ ∈ Dec (F := ℚ) A, Dec (F := ℚ) A ≤ (Subgroup.zpowers γ ⊔ Ine (F := ℚ) A).topologicalClosure ∧
            ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) := by
  intro Ω _ _ _ p A hp hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hPO := isPlaceOver_vQ (l := p) A hA
  obtain ⟨σ, hσ⟩ := exists_isFrob hPO
  have hσD : σ ∈ Dec (F := ℚ) A := hσ.1
  refine ⟨?_, Ine_le_Dec A, σ, hσD, ?_, ?_⟩
  · constructor
    rintro ⟨i, hiD⟩ hi ⟨τ, hτ⟩
    rw [Subgroup.mem_subgroupOf] at hi ⊢
    have hi2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (i x - x) < 1 := hi.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(Dec (F := ℚ) A).mul_mem ((Dec (F := ℚ) A).mul_mem hτ hiD) ((Dec (F := ℚ) A).inv_mem hτ), ?_⟩
    intro x hx
    have hτi : τ⁻¹ ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).inv_mem hτ
    have hy : A.valuation (τ⁻¹ x) ≤ 1 := decomposition_cyclotomic_of_mem_dec A τ⁻¹ hτi x hx
    have h3 := hi2 _ hy
    have heq : (τ * i * τ⁻¹) x - x = τ (i (τ⁻¹ x) - τ⁻¹ x) := by
      simp [AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv]
    rw [heq, decomposition_cyclotomic_of_mem_dec_third A τ hτ]
    exact h3
  · set K := (Subgroup.zpowers σ ⊔ Ine (F := ℚ) A).topologicalClosure with hK
    have hKc : IsClosed (K : Set (G ℚ Ω)) := Subgroup.isClosed_topologicalClosure _
    have hcs := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K, hKc⟩
    refine le_trans ?_ hcs.ge
    refine le_sInf fun N hN => ?_
    have hKN : K ≤ N := hN.2
    exact Kum.decGen ℚ Ω A (vQ p) σ N hPO hσ hN.1
      (le_trans (le_sup_right.trans (Subgroup.le_topologicalClosure _)) hKN)
      (hKN (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))))
  · intro l _ hlp
    have hnot : ((l : ℕ) : 𝓞 ℚ) ∉ (vQ p).asIdeal := by
      intro h
      have h' := (intCast_mem_vQ (l := p) (l : ℤ)).mp (by simpa using h)
      rw [Int.natCast_dvd_natCast] at h'
      exact hlp ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp h').symm
    rw [cycZ_of_isFrob hnot hPO hσ, normV_vQ]
