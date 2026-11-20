import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex

open NumberField IsDedekindDomain Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.DegOneRay

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) fun σ τ h => by ext x exact Complex.ofReal_injective (congrArg (fun f : F →+* ℂ => f x) h)`.
-/
theorem finite_realEmb : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) fun σ τ h => by
    ext x
    exact Complex.ofReal_injective (congrArg (fun f : F →+* ℂ => f x) h)

/- English proof (translation)
Take `⟨i, hi, j, hj, hij⟩` from `Ideal.isCoprime_iff_exists.1 hu`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hi`. Establish `hc : c * u - 1 ∈ 𝔣`. Establish `: c * u - 1 = -j` using `by rw [← hij]; ring`. Rewrite using `[this]`.

Conclude with `𝔣.neg_mem hj`. Use `set N : ℕ := Ideal.absNorm 𝔣 with hN`. Establish `hN0 : 0 < N` using `Nat.pos_of_ne_zero (by simpa [hN, Ideal.absNorm_eq_zero_iff] using hf)`. Establish `hNm : ((N : ℕ) : 𝓞 F) ∈ 𝔣` using `Ideal.absNorm_mem 𝔣`. Establish `: Finite (F →+* ℝ)` using `finite_realEmb`.

Take `⟨b, hb⟩` from `(Set.finite_range fun σ : F →+* ℝ => -σ (c : F)).bddAbove`. Take `⟨M, hM⟩` from `exists_nat_gt b`. Establish `key : ∀ m : ℕ, M ≤ m → ((c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 ∈ 𝔣 ∧ ∀ σ : F →+* ℝ, 0 < σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F))`. Introduce `m hm`. Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations.

Establish `: (c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 = (c * u - 1) + (N : 𝓞 F) * ((m : 𝓞 F) * u)` using `by ring`. Rewrite using `[this]`. Conclude with `𝔣.add_mem hc (𝔣.mul_mem_right _ hNm)`. Establish `h1 : -σ (c : F) ≤ b` using `hb ⟨σ, rfl⟩`. Establish `h2 : (M : ℝ) ≤ m` using `by exact_mod_cast hm`.

Establish `h3 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN0`. Establish `h4 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `e : σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F) = σ (c : F) + (m : ℝ) * (N : ℝ)`. Use `push_cast`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `h0 : c + (M : 𝓞 F) * (N : 𝓞 F) = 0`. Use `⟨c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F), ?_, (key _ (Nat.le_succ M)).1, (key _ (Nat.le_succ M)).2⟩` and prove the remaining obligations. Establish `: c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F) = (N : 𝓞 F)`.

Use `push_cast`. Take the linear combination `h0`. Rewrite using `[this]`. Conclude with `hN0.ne'` after adjusting the coercions. Conclude with `⟨_, h0, (key M le_rfl).1, (key M le_rfl).2⟩`.
-/
theorem exists_totPos_inv {𝔣 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {u : 𝓞 F} (hu : IsCoprime (Ideal.span {u}) 𝔣) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ d * u - 1 ∈ 𝔣 ∧ ∀ σ : F →+* ℝ, 0 < σ (d : F) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hu
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have hc : c * u - 1 ∈ 𝔣 := by
    have : c * u - 1 = -j := by rw [← hij]; ring
    rw [this]; exact 𝔣.neg_mem hj
  set N : ℕ := Ideal.absNorm 𝔣 with hN
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by simpa [hN, Ideal.absNorm_eq_zero_iff] using hf)
  have hNm : ((N : ℕ) : 𝓞 F) ∈ 𝔣 := Ideal.absNorm_mem 𝔣
  have : Finite (F →+* ℝ) := finite_realEmb
  obtain ⟨b, hb⟩ := (Set.finite_range fun σ : F →+* ℝ => -σ (c : F)).bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt b
  have key : ∀ m : ℕ, M ≤ m → ((c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 ∈ 𝔣 ∧
      ∀ σ : F →+* ℝ, 0 < σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F)) := by
    intro m hm
    refine ⟨?_, fun σ => ?_⟩
    · have : (c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 = (c * u - 1) + (N : 𝓞 F) * ((m : 𝓞 F) * u) := by ring
      rw [this]
      exact 𝔣.add_mem hc (𝔣.mul_mem_right _ hNm)
    · have h1 : -σ (c : F) ≤ b := hb ⟨σ, rfl⟩
      have h2 : (M : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e : σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F) = σ (c : F) + (m : ℝ) * (N : ℝ) := by
        push_cast
        simp
      rw [e]
      nlinarith
  by_cases h0 : c + (M : 𝓞 F) * (N : 𝓞 F) = 0
  · refine ⟨c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F), ?_, (key _ (Nat.le_succ M)).1, (key _ (Nat.le_succ M)).2⟩
    have : c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F) = (N : 𝓞 F) := by
      push_cast
      linear_combination h0
    rw [this]
    exact_mod_cast hN0.ne'
  · exact ⟨_, h0, (key M le_rfl).1, (key M le_rfl).2⟩

/- English proof (translation)
Take `⟨ha, hb, ha', hb', hab, hpos⟩` from `hr`. Establish `hb2 : IsCoprime (Ideal.span {β * β}) 𝔣`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton]`. Conclude with `hb'.mul_left hb'`. Take `⟨d, hd0, hd, hdp⟩` from `exists_totPos_inv hf hb2`.

Use `⟨d * (β * β), d * (α * β), mul_ne_zero hd0 (mul_ne_zero hb hb), mul_ne_zero hd0 (mul_ne_zero ha hb), hd, ?_, fun σ => ?_, ?_⟩` and prove the remaining obligations. Establish `: d * (α * β) - 1 = (d * β) * (α - β) + (d * (β * β) - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `𝔣.add_mem (𝔣.mul_mem_left _ hab) hd`. Establish `hbK : (β : F) ≠ 0` using `by exact_mod_cast hb`.

Establish `hσb : σ (β : F) ≠ 0` using `(map_ne_zero σ).2 hbK`. Establish `e1 : σ ((d * (β * β) : 𝓞 F) : F) = σ (d : F) * (σ (β : F) * σ (β : F))` using `by push_cast; simp`. Establish `e2 : σ ((d * (α * β) : 𝓞 F) : F) = σ (d : F) * (σ (α : F) * σ (β : F))` using `by push_cast; simp`. Rewrite using `[e1, e2]`. Conclude with `⟨mul_pos (hdp σ) (mul_self_pos.2 hσb), mul_pos (hdp σ) (hpos σ)⟩`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton, mul_assoc d]`. Use `_ = Ideal.span {d * β} * (Ideal.span {α} * 𝔞) := by rw [h]`. Use `_ = Ideal.span {d * (α * β)} * 𝔞 := by`. Rewrite using `[← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton, show d * β * α = d * (α * β) by ring]`.
-/
theorem rayRel_of_rayPair {𝔣 𝔠 𝔞 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {α β : 𝓞 F} (hr : GlobalTheory.NT.RayPair 𝔣 α β)
    (h : Ideal.span {β} * 𝔠 = Ideal.span {α} * 𝔞) : RayRel F 𝔣 𝔠 𝔞 := by
  obtain ⟨ha, hb, ha', hb', hab, hpos⟩ := hr
  have hb2 : IsCoprime (Ideal.span {β * β}) 𝔣 := by
    rw [← Ideal.span_singleton_mul_span_singleton]; exact hb'.mul_left hb'
  obtain ⟨d, hd0, hd, hdp⟩ := exists_totPos_inv hf hb2
  refine ⟨d * (β * β), d * (α * β), mul_ne_zero hd0 (mul_ne_zero hb hb),
    mul_ne_zero hd0 (mul_ne_zero ha hb), hd, ?_, fun σ => ?_, ?_⟩
  · have : d * (α * β) - 1 = (d * β) * (α - β) + (d * (β * β) - 1) := by ring
    rw [this]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ hab) hd
  · have hbK : (β : F) ≠ 0 := by exact_mod_cast hb
    have hσb : σ (β : F) ≠ 0 := (map_ne_zero σ).2 hbK
    have e1 : σ ((d * (β * β) : 𝓞 F) : F) = σ (d : F) * (σ (β : F) * σ (β : F)) := by
      push_cast; simp
    have e2 : σ ((d * (α * β) : 𝓞 F) : F) = σ (d : F) * (σ (α : F) * σ (β : F)) := by
      push_cast; simp
    rw [e1, e2]
    exact ⟨mul_pos (hdp σ) (mul_self_pos.2 hσb), mul_pos (hdp σ) (hpos σ)⟩
  · calc Ideal.span {d * (β * β)} * 𝔠 = Ideal.span {d * β} * (Ideal.span {β} * 𝔠) := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton, mul_assoc d]
      _ = Ideal.span {d * β} * (Ideal.span {α} * 𝔞) := by rw [h]
      _ = Ideal.span {d * (α * β)} * 𝔞 := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton,
            show d * β * α = d * (α * β) by ring]

/- English proof (translation)
Establish `h1 : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣}.Finite` using `Ideal.finite_factors hf`. Establish `h2 : {v : HeightOneSpectrum (𝓞 F) | Ideal.absNorm v.asIdeal ≤ B}.Finite`. Establish `h : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B}.Finite`. Establish `: {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B} = ⋃ n ∈ Finset.range (B + 1), {I : Ideal (𝓞 F) | Ideal.absNorm I = n}`. Use extensionality with `I`.

Simplify using `[Nat.lt_succ_iff]`. Rewrite using `[this]`. Conclude with `Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Ideal.finite_setOfPred_absNorm_eq n`. Conclude with `(h.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun v _ w _ e => HeightOneSpectrum.ext e))`. Establish `h3 : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal}.Finite`.

Establish `: {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal} = ⋃ x ∈ W, {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {x}}`. Use extensionality with `v`. Simplify using `[Ideal.dvd_span_singleton]`. Rewrite using `[this]`. Use `Set.Finite.biUnion W.finite_toSet fun x hx => Ideal.finite_factors ?_` and prove the remaining obligations.

Simplify using `using hW x hx`. Conclude with `(h1.union (h2.union h3)).subset fun v hv => by`. Break down `hv with h | h | h` into its components or cases. Use `exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]`.
-/
theorem finite_excluded (𝔣 : Ideal (𝓞 F)) (hf : 𝔣 ≠ ⊥) (W : Finset (𝓞 F)) (B : ℕ) (hW : ∀ x ∈ W, x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣 ∨ Ideal.absNorm v.asIdeal ≤ B ∨ ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
  have h1 : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hf
  have h2 : {v : HeightOneSpectrum (𝓞 F) | Ideal.absNorm v.asIdeal ≤ B}.Finite := by
    have h : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B}.Finite := by
      have : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B} =
          ⋃ n ∈ Finset.range (B + 1), {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
        ext I; simp [Nat.lt_succ_iff]
      rw [this]
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Ideal.finite_setOfPred_absNorm_eq n
    exact (h.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun v _ w _ e => HeightOneSpectrum.ext e))
  have h3 : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
    have : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal} =
        ⋃ x ∈ W, {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {x}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [this]
    refine Set.Finite.biUnion W.finite_toSet fun x hx => Ideal.finite_factors ?_
    simpa using hW x hx
  exact (h1.union (h2.union h3)).subset fun v hv => by
    rcases hv with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

/- English proof (translation)
Take `⟨v, hv, hd, A, hA, -, σ, hσ, hg⟩` from `GlobalTheory.Published.chebotarevDegreeOne' F Ω L g S hS`. Use `⟨v, hv, hd, ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.RayFromArtin.isFrob_restrict (K := F) (Ω := Ω) L hA hσ`. Rewrite `h` using `[hg]`. Then use the resulting hypothesis.
-/
theorem exists_degree_one_frobenius_prime {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω)
    [FiniteDimensional F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  obtain ⟨v, hv, hd, A, hA, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' F Ω L g S hS
  refine ⟨v, hv, hd, ?_⟩
  have h := GlobalTheory.RayFromArtin.isFrob_restrict (K := F) (Ω := Ω) L hA hσ
  rwa [hg] at h

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: FiniteDimensional F L` using `Module.Finite.of_restrictScalars_finite ℚ F L`. Set `i : L →ₐ[F] Ω` to `IsAlgClosed.lift`. Set `e : L ≃ₐ[F] i.fieldRange` to `AlgEquiv.ofInjectiveField i`. Establish `: IsGalois F i.fieldRange` using `IsGalois.of_algEquiv e`.

Establish `: FiniteDimensional F i.fieldRange` using `e.toLinearEquiv.finiteDimensional`. Take `⟨v, hv, hd, h⟩` from `exists_degree_one_frobenius_prime i.fieldRange (e.autCongr g) S hS`. Conclude with `⟨v, hv, hd, (GlobalTheory.Mem.Fld.isFrob_congr e v g).1 h⟩`.
-/
theorem exists_degOne_isFrob_of_closure (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {L : Type} [Field L]
    [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  let i : L →ₐ[F] Ω := IsAlgClosed.lift
  let e : L ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  have : IsGalois F i.fieldRange := IsGalois.of_algEquiv e
  have : FiniteDimensional F i.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨v, hv, hd, h⟩ := exists_degree_one_frobenius_prime i.fieldRange (e.autCongr g) S hS
  exact ⟨v, hv, hd, (GlobalTheory.Mem.Fld.isFrob_congr e v g).1 h⟩

/- English proof (translation)
The claim follows from `exists_degOne_isFrob_of_closure (AlgebraicClosure F) g S hS`.
-/
theorem exists_degOne_isFrob {L : Type} [Field L] [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g :=
  exists_degOne_isFrob_of_closure (AlgebraicClosure F) g S hS

/- English proof (translation)
Introduce `F _ _ 𝔣 𝔞 hf ha W B hW`. Take `⟨ha0, hac⟩` from `ha`. Take `⟨L, _, _, _, hab, Art, hArt⟩` from `(GlobalTheory.Published.rayClassFieldSt_iff_artinIso.1 (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt GlobalTheory.CompanionTheory.Hypotheses₂.globalArtinReciprocity)) F 𝔣 hf`. Establish `hc : IsCoprime 𝔞 𝔣` using `Ideal.isCoprime_iff_sup_eq.2 hac`. Take `⟨J, hJ⟩` from `GlobalTheory.RayFieldCompare.exists_integral 𝔣 𝔞 ha0 hc`.

Take `⟨v, hv, hd, hfr⟩` from `exists_degOne_isFrob (Art (QuotientGroup.mk J)) _ (finite_excluded 𝔣 hf W B hW)`. Simplify using `only [Set.mem_setOf_eq, not_or, not_exists, not_and] at hv`. Take `⟨hv1, hv2, hv3⟩` from `hv`. Establish `heq : (QuotientGroup.mk J : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔣) = GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔣 v hv1` using `Art.injective (GlobalTheory.RayFieldCompare.isFrob_unique L (hArt v hv1).1 hfr (hArt v hv1).2)`. Take `⟨x, ⟨α, β, hr, hx⟩, hxJ⟩` from `Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 heq)`.

Establish `e1 : J.1 * toPrincipalIdeal (𝓞 F) F x = (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeElt 𝔣 v hv1).1`. Rewrite using `[hxJ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]`. Establish `e2 : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) = (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)`. Establish `h` using `congrArg Units.val e1`. Rewrite `h` using `[Units.val_mul, hJ, coe_toPrincipalIdeal]`.

Conclude with `h`. Establish `hα : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F)`. Rewrite using `[FractionalIdeal.spanSingleton_mul_spanSingleton, hx]`. Establish `e3 : Ideal.span {β} * v.asIdeal = Ideal.span {α} * 𝔞`. Use `FractionalIdeal.coeIdeal_injective (K := F) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((Ideal.span {β} * v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = ((Ideal.span {α} * 𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)`. Rewrite using `[FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton, ← e2]`. Express the relevant statement in the definitionally equal form `FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) * _ = FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) * _`. Rewrite using `[hα]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨v.asIdeal, v.isPrime, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd, not_le.1 hv2, ⟨v.ne_bot, ?_⟩, rayRel_of_rayPair hf hr e3, fun y hy hy' => hv3 y hy hy'⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hv1 (Ideal.dvd_iff_le.2 ((v.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right))`.
-/
theorem exists_degOne_prime_in_rayClass : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧
      RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 𝔞 hf ha W B hW
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨L, _, _, _, hab, Art, hArt⟩ := (GlobalTheory.Published.rayClassFieldSt_iff_artinIso.1
    (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt GlobalTheory.CompanionTheory.Hypotheses₂.globalArtinReciprocity)) F 𝔣 hf
  have hc : IsCoprime 𝔞 𝔣 := Ideal.isCoprime_iff_sup_eq.2 hac
  obtain ⟨J, hJ⟩ := GlobalTheory.RayFieldCompare.exists_integral 𝔣 𝔞 ha0 hc
  obtain ⟨v, hv, hd, hfr⟩ := exists_degOne_isFrob (Art (QuotientGroup.mk J)) _ (finite_excluded 𝔣 hf W B hW)
  simp only [Set.mem_setOf_eq, not_or, not_exists, not_and] at hv
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have heq : (QuotientGroup.mk J : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔣) = GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔣 v hv1 :=
    Art.injective (GlobalTheory.RayFieldCompare.isFrob_unique L (hArt v hv1).1 hfr (hArt v hv1).2)
  obtain ⟨x, ⟨α, β, hr, hx⟩, hxJ⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 heq)
  have e1 : J.1 * toPrincipalIdeal (𝓞 F) F x = (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeElt 𝔣 v hv1).1 := by
    rw [hxJ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have e2 : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) := by
    have h := congrArg Units.val e1
    rw [Units.val_mul, hJ, coe_toPrincipalIdeal] at h
    exact h
  have hα : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hx]
  have e3 : Ideal.span {β} * v.asIdeal = Ideal.span {α} * 𝔞 := by
    refine FractionalIdeal.coeIdeal_injective (K := F) ?_
    change ((Ideal.span {β} * v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      ((Ideal.span {α} * 𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, ← e2]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) * _ =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) * _
    rw [hα]
    ring
  refine ⟨v.asIdeal, v.isPrime, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd,
    not_le.1 hv2, ⟨v.ne_bot, ?_⟩, rayRel_of_rayPair hf hr e3, fun y hy hy' => hv3 y hy hy'⟩
  by_contra hne
  exact hv1 (Ideal.dvd_iff_le.2 ((v.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right))

end GlobalTheory.CompanionTheory.DegOneRay
