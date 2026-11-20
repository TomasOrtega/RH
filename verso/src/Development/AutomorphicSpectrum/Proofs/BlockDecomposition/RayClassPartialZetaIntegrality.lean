import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationAlt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBoundStatement

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality

/- English proof (translation)
Apply the tactic sequence `have hconn : IsPreconnected ({1}ᶜ : Set ℂ) := (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; first | exact Cardinal.one_lt_two | norm_num | exact_mod_cast (show (1:ℕ) < 2 by norm_num)) 1).isPreconnected`. Establish `hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)`. Rewrite using `[Set.mem_compl_singleton_iff]`. Evaluate the numerical expressions. Establish `hopen : IsOpen {s : ℂ | 1 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`.

Establish `hnhds : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ)` using `hopen.mem_nhds (by norm_num)`. Conclude with `(hH.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd isOpen_compl_singleton) hconn hmem (Filter.eventually_of_mem hnhds fun s hs => h s hs)`.
-/
theorem eqOn_compl_one {H R : ℂ → ℂ} (hH : DifferentiableOn ℂ H {1}ᶜ) (hR : DifferentiableOn ℂ R {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → H s = R s) : Set.EqOn H R {1}ᶜ := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; first | exact Cardinal.one_lt_two | norm_num | exact_mod_cast (show (1:ℕ) < 2 by norm_num)) 1).isPreconnected
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff]; norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by norm_num)
  exact (hH.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd isOpen_compl_singleton) hconn hmem (Filter.eventually_of_mem hnhds fun s hs => h s hs)

/- English proof (translation)
Unfold `coneWeight`. Use `split_ifs`. Conclude with `⟨(l : ℤ) - 1, by push_cast; ring⟩`. Conclude with `⟨-1, by push_cast; ring⟩`.
-/
theorem coneWeight_int {F : Type} [Field F] [NumberField F] {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F)
    (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ∃ z : ℤ, coneWeight l A y v m = z := by
  unfold coneWeight
  split_ifs
  · exact ⟨(l : ℤ) - 1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩

/- English proof (translation)
Use `⟨∑ j ∈ S, K j, ∑ j ∈ S, (l : ℤ) ^ (∑ i ∈ S, K i - K j) * z j, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Establish `hle : K j ≤ ∑ i ∈ S, K i` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj`.

Rewrite using `[← h j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`.
-/
theorem exists_pow_mul_sum {J : Type} (S : Finset J) (l : ℕ) (q : J → ℚ) (K : J → ℕ) (z : J → ℤ)
    (h : ∀ j, (l : ℚ) ^ K j * q j = z j) : ∃ (K' : ℕ) (Z : ℤ), (l : ℚ) ^ K' * ∑ j ∈ S, q j = Z := by
  refine ⟨∑ j ∈ S, K j, ∑ j ∈ S, (l : ℤ) ^ (∑ i ∈ S, K i - K j) * z j, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hle : K j ≤ ∑ i ∈ S, K i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← h j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

/- English proof (translation)
Break down `eq_or_ne Z 0 with rfl | hZ` into its components or cases. Simplify using the standard rewrite rules. Establish `hZ' : (Z : ℚ) ≠ 0` using `Int.cast_ne_zero.mpr hZ`. Establish `hD' : (D : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hD`. Rewrite using `[padicValRat.div hZ' hD', padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]`.

Simplify using the standard rewrite rules.
-/
theorem padicValRat_int_div_nonneg (l : ℕ) [Fact l.Prime] (Z : ℤ) (D : ℕ) (hD : D ≠ 0) (h : ¬ l ∣ D) :
    0 ≤ padicValRat l ((Z : ℚ) / (D : ℚ)) := by
  rcases eq_or_ne Z 0 with rfl | hZ
  · simp
  have hZ' : (Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hZ
  have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  rw [padicValRat.div hZ' hD', padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

/- English proof (translation)
Introduce `F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP h𝔠 hN hv T hT hS k hk`. Take `⟨hb, hy, hvv, hr, e, he⟩` from `hP`. Use `letI : Fintype (F →+* ℝ) := Fintype.ofEquiv (F →+* ℂ) (realEmbeddingsEquiv F).symm`. Use `set l := Ideal.absNorm 𝔠 with hl_def`. Establish `hl0 : 0 < l` using `hN.pos`.

Establish `hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F`. Rewrite using `[Fintype.card_congr (realEmbeddingsEquiv F)]`. Use `NumberField.Embeddings.card F ℂ` and compare the differences between its conclusion and the goal. Establish `hNb : Ideal.absNorm 𝔟 ≠ 0` using `fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hNbC : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hNb`.

Establish `hw : ∀ j, GoodWeight l (coneWeight l (𝔠 * 𝔟) (y j) (v j))` using `fun j => goodWeight_coneWeight hb hN (hy j).1 (fun i => (hvv j i).1) (hv j)`. Establish `hcont : ∀ j, ∃ Tj : ℂ → ℂ, Differentiable ℂ Tj ∧ (∀ s : ℂ, 1 < s.re → HasSum (fun m => (coneWeight l (𝔠 * 𝔟) (y j) (v j) m : ℂ) * coneTerm (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) s m) (Tj s))`. Introduce `j`. Take `⟨Tj, hd, hs, -⟩` from `abelContinuation (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) (hw j)`. Conclude with `⟨Tj, hd, hs⟩`.

Use `choose Tc hTcd hTcs using hcont`. Establish `key : ∀ (s : ℂ) (p : (j : J) × (Fin (r j) → ℕ)), (classWeight l 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) * coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+ …`. Introduce and unpack `s ⟨j, m⟩`. Simplify using `only`. Establish `hx : (e ⟨j, m⟩).1 * 𝔟 = Ideal.span {conePt (y j) (v j) m}` using `he ⟨j, m⟩`.

Establish `hwt : classWeight l 𝔠 (e ⟨j, m⟩).1 = coneWeight l (𝔠 * 𝔟) (y j) (v j) m`. Unfold `classWeight coneWeight`. Rewrite using `[le_iff_mem_mul_of_span (𝔠 := 𝔠) hb hx]`. Establish `hnorm : Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) = Ideal.absNorm (e ⟨j, m⟩).1 * Ideal.absNorm 𝔟` using `by rw [← hx, map_mul]`. Rewrite using `[hwt, coneTerm_eq_absNorm_cpow (hy j).2 (fun i => (hvv j i).2) s m, hnorm, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), ← Complex.cpow_add _ _ hNbC, add_neg_cancel, Complex.cpow_z …`.

Establish `hRs : ∀ s : ℂ, 1 < s.re → T s = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s`. Introduce `s hs`. Establish `h1` using `(e.hasSum_iff.mpr (hS s hs))`. Establish `h2 : HasSum (fun p : (j : J) × (Fin (r j) → ℕ) => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) * coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2)) (T s)`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `p`. Conclude with `(key s p).symm`. Establish `h3` using `h2.sigma (fun j => (hTcs j s hs).mul_left (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s))`. Rewrite using `[Finset.mul_sum]`. Conclude with `h3.unique (hasSum_fintype _)`.

Establish `hRd : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s) {1}ᶜ`. Introduce `s _`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Apply `DifferentiableAt.mul` to reduce the goal to its premises. Conclude with `differentiableAt_id.const_cpow (Or.inl hNbC)`.

Establish `hsd` using `DifferentiableAt.sum (u := Finset.univ) (fun j _ => hTcd j s)`. Establish `hfun : (fun t => ∑ j, Tc j t) = ∑ j, Tc j`. Use function extensionality and compare the values at `t`. Simplify using `[Finset.sum_apply]`. Rewrite using `[hfun]`.

Conclude with `hsd`. Establish `heq` using `eqOn_compl_one hT hRd (fun s hs => hRs s hs)`. Establish `hint : ∀ j, ∃ (qj : ℚ) (K : ℕ) (z : ℤ), Tc j (-((k - 1 : ℕ) : ℂ)) = qj ∧ (l : ℚ) ^ K * qj = z`. Introduce `j`. Use `GlobalTheory.T.cone_zeta_special_value_denominator_bound (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) …` and prove the remaining obligations.

Establish `h1 : ∏ σ : F →+* ℝ, (σ ((y j : 𝓞 F) : F) + ∑ i, σ ((v j i : 𝓞 F) : F) * (m i : ℝ)) = ((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℝ)`. Rewrite using `[← prod_real_embeddings_eq_absNorm _ (totPos_conePt (hy j).2 (fun i => (hvv j i).2) m)]`. Conclude with `Finset.prod_congr rfl fun σ _ => (embedding_conePt σ (y j) (v j) m).symm`. Use `⟨(Ideal.absNorm (Ideal.span {conePt (y j) (v j) m})) ^ (k - 1), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `try beta_reduce`.

Rewrite using `[Finset.prod_pow, h1]`. Apply the tactic sequence `first | norm_cast | (push_cast; ring) | simp`. Use `choose qj Kj zj hqj hzj using hint`. Take `⟨K', Z, hZ⟩` from `exists_pow_mul_sum Finset.univ l qj Kj zj hzj`. Establish `hs0 : (1 - (k : ℂ)) = -(((k - 1 : ℕ)) : ℂ)` using `by rw [Nat.cast_sub hk]; push_cast; ring`.

Establish `hmem : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ)`. Rewrite using `[Set.mem_compl_singleton_iff, Ne, sub_eq_self]; exact_mod_cast (by omega : k ≠ 0)`. Establish `hval : T (1 - (k : ℂ)) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ (1 - (k : ℂ)) * ∑ j, (qj j : ℂ)`. Rewrite using `[heq hmem]`. Simplify using `only`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hs0]`. Conclude with `hqj j`. Establish `hlK : (l : ℚ) ^ K' ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hl0.ne')`.

Establish `hsum : ∑ j, qj j = (Z : ℚ) / (l : ℚ) ^ K'`. Rewrite using `[eq_div_iff hlK, mul_comm]`. Conclude with `hZ`. Establish `hD : l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hl0.ne') (pow_ne_zero _ hNb)`. Use `⟨(Z : ℚ) / ((l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) : ℕ) : ℚ), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hval, hs0, Complex.cpow_neg, Complex.cpow_natCast, ← Rat.cast_sum, hsum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `l' hl' hne hndvd haveI := Fact.mk hl'`. Apply `padicValRat_int_div_nonneg l' Z _ hD` to reduce the goal to its premises.

Introduce `hdvd`. Break down `(Nat.Prime.dvd_mul hl').mp hdvd with h | h` into its components or cases. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq hl' hN).mp (hl'.dvd_of_dvd_pow h))`. Conclude with `hndvd (hl'.dvd_of_dvd_pow h)`.
-/
theorem classTwist_value_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP h𝔠 hN hv T hT hS k hk
  obtain ⟨hb, hy, hvv, hr, e, he⟩ := hP
  letI : Fintype (F →+* ℝ) := Fintype.ofEquiv (F →+* ℂ) (realEmbeddingsEquiv F).symm
  set l := Ideal.absNorm 𝔠 with hl_def
  have hl0 : 0 < l := hN.pos
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F)]
    convert NumberField.Embeddings.card F ℂ
  have hNb : Ideal.absNorm 𝔟 ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hNbC : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNb
  have hw : ∀ j, GoodWeight l (coneWeight l (𝔠 * 𝔟) (y j) (v j)) := fun j =>
    goodWeight_coneWeight hb hN (hy j).1 (fun i => (hvv j i).1) (hv j)
  have hcont : ∀ j, ∃ Tj : ℂ → ℂ, Differentiable ℂ Tj ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun m => (coneWeight l (𝔠 * 𝔟) (y j) (v j) m : ℂ) *
        coneTerm (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) s m) (Tj s)) := by
    intro j
    obtain ⟨Tj, hd, hs, -⟩ := abelContinuation (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F))
      (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0
      (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) (hw j)
    exact ⟨Tj, hd, hs⟩
  choose Tc hTcd hTcs using hcont
  have key : ∀ (s : ℂ) (p : (j : J) × (Fin (r j) → ℕ)),
      (classWeight l 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2) := by
    rintro s ⟨j, m⟩
    dsimp only
    have hx : (e ⟨j, m⟩).1 * 𝔟 = Ideal.span {conePt (y j) (v j) m} := he ⟨j, m⟩
    have hwt : classWeight l 𝔠 (e ⟨j, m⟩).1 = coneWeight l (𝔠 * 𝔟) (y j) (v j) m := by
      unfold classWeight coneWeight
      rw [le_iff_mem_mul_of_span (𝔠 := 𝔠) hb hx]
    have hnorm : Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) =
        Ideal.absNorm (e ⟨j, m⟩).1 * Ideal.absNorm 𝔟 := by rw [← hx, map_mul]
    rw [hwt, coneTerm_eq_absNorm_cpow (hy j).2 (fun i => (hvv j i).2) s m, hnorm, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s),
      mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), ← Complex.cpow_add _ _ hNbC, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have hRs : ∀ s : ℂ, 1 < s.re → T s = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s := by
    intro s hs
    have h1 := (e.hasSum_iff.mpr (hS s hs))
    have h2 : HasSum (fun p : (j : J) × (Fin (r j) → ℕ) => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s *
        ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2)) (T s) := by
      convert h1 using 1
      funext p
      exact (key s p).symm
    have h3 := h2.sigma (fun j => (hTcs j s hs).mul_left (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s))
    rw [Finset.mul_sum]
    exact h3.unique (hasSum_fintype _)
  have hRd : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s) {1}ᶜ := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact differentiableAt_id.const_cpow (Or.inl hNbC)
    · have hsd := DifferentiableAt.sum (u := Finset.univ) (fun j _ => hTcd j s)
      have hfun : (fun t => ∑ j, Tc j t) = ∑ j, Tc j := by
        funext t
        simp [Finset.sum_apply]
      rw [hfun]
      exact hsd
  have heq := eqOn_compl_one hT hRd (fun s hs => hRs s hs)
  have hint : ∀ j, ∃ (qj : ℚ) (K : ℕ) (z : ℤ), Tc j (-((k - 1 : ℕ) : ℂ)) = qj ∧ (l : ℚ) ^ K * qj = z := by
    intro j
    refine GlobalTheory.T.cone_zeta_special_value_denominator_bound (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F))
      (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ)
      (fun σ => (hy j).2 σ) (hw j) (fun m => coneWeight_int l _ _ _ m) (Tc j) (hTcd j).differentiableOn
      (hTcs j) (k - 1) (fun m => ?_)
    have h1 : ∏ σ : F →+* ℝ, (σ ((y j : 𝓞 F) : F) + ∑ i, σ ((v j i : 𝓞 F) : F) * (m i : ℝ)) =
        ((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℝ) := by
      rw [← prod_real_embeddings_eq_absNorm _ (totPos_conePt (hy j).2 (fun i => (hvv j i).2) m)]
      exact Finset.prod_congr rfl fun σ _ => (embedding_conePt σ (y j) (v j) m).symm
    refine ⟨(Ideal.absNorm (Ideal.span {conePt (y j) (v j) m})) ^ (k - 1), ?_⟩
    try beta_reduce
    rw [Finset.prod_pow, h1]
    first | norm_cast | (push_cast; ring) | simp
  choose qj Kj zj hqj hzj using hint
  obtain ⟨K', Z, hZ⟩ := exists_pow_mul_sum Finset.univ l qj Kj zj hzj
  have hs0 : (1 - (k : ℂ)) = -(((k - 1 : ℕ)) : ℂ) := by rw [Nat.cast_sub hk]; push_cast; ring
  have hmem : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff, Ne, sub_eq_self]; exact_mod_cast (by omega : k ≠ 0)
  have hval : T (1 - (k : ℂ)) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ (1 - (k : ℂ)) * ∑ j, (qj j : ℂ) := by
    rw [heq hmem]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs0]; exact hqj j
  have hlK : (l : ℚ) ^ K' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl0.ne')
  have hsum : ∑ j, qj j = (Z : ℚ) / (l : ℚ) ^ K' := by
    rw [eq_div_iff hlK, mul_comm]; exact hZ
  have hD : l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0.ne') (pow_ne_zero _ hNb)
  refine ⟨(Z : ℚ) / ((l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) : ℕ) : ℚ), ?_, ?_⟩
  · rw [hval, hs0, Complex.cpow_neg, Complex.cpow_natCast, ← Rat.cast_sum, hsum]
    push_cast
    ring
  · intro l' hl' hne hndvd
    haveI := Fact.mk hl'
    apply padicValRat_int_div_nonneg l' Z _ hD
    intro hdvd
    rcases (Nat.Prime.dvd_mul hl').mp hdvd with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hl' hN).mp (hl'.dvd_of_dvd_pow h))
    · exact hndvd (hl'.dvd_of_dvd_pow h)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality
