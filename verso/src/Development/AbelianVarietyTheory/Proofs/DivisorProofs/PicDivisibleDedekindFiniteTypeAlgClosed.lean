import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletionEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeCountGenerates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupNthPowerOfCodimOneMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalBoundedIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetsMemSubalgebraOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CcSubst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseDerivativePowerSeriesMulSubstLeibnizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseJetVanishingMemPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinrankQuotientSpanModEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableNormalisationReducedFibresStatement

open Polynomial

namespace GlobalTheory.PicDiv.FormalDeformHasse

/- English proof (translation)
Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' ha`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hs, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]`.
-/
theorem constantCoeff_subst_eq {k : Type} [Field k] (a φ : PowerSeries k)
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hs,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]

/- English proof (translation)
Introduce `hmem`. Establish `hQne : Q i ≠ ⊥`. Introduce `h`. Rewrite `hmem` using `[h, Ideal.bot_pow (Nat.succ_ne_zero N), Ideal.mem_bot]`. Conclude with `hf₀ hmem`.

Establish `hp : Prime (Q i)` using `Ideal.prime_of_isPrime hQne (hQmax i).isPrime`. Establish `hdvd : Q i ^ (N + 1) ∣ Ideal.span {f₀}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)`. Establish `hsplit : Ideal.span {f₀} = Q i ^ N * (P₀ * D * ∏ j ∈ Finset.univ.erase i, Q j ^ N)`. Rewrite using `[hspan, ← Finset.mul_prod_erase Finset.univ (fun j => Q j ^ N) (Finset.mem_univ i)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hdvd` using `[hsplit, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero N hQne)]`. Break down `hp.dvd_or_dvd hdvd with h | h` into its components or cases. Break down `hp.dvd_or_dvd h with h | h` into its components or cases. Conclude with `hQP i (hP₀.eq_of_le (hQmax i).ne_top (Ideal.le_of_dvd h)).symm`. Conclude with `hDQ i (Ideal.le_of_dvd h)`.

Take `⟨j, hj, hji⟩` from `(hp.dvd_finset_prod_iff _).mp h`. Establish `hle : Q j ≤ Q i` using `Ideal.le_of_dvd (hp.dvd_of_dvd_pow hji)`. Conclude with `(Finset.mem_erase.mp hj).1 (hQinj ((hQmax j).eq_of_le (hQmax i).ne_top hle))`.
-/
theorem not_mem_pow_succ {A : Type} [CommRing A] [IsDedekindDomain A] {N : ℕ} {I : Type}
    [Fintype I] {D P₀ : Ideal A} {Q : I → Ideal A} {f₀ : A} (hP₀ : P₀.IsMaximal)
    (hQmax : ∀ i, (Q i).IsMaximal) (hQinj : Function.Injective Q) (hQP : ∀ i, Q i ≠ P₀)
    (hDQ : ∀ i, ¬ D ≤ Q i) (hf₀ : f₀ ≠ 0)
    (hspan : Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N) (i : I) : f₀ ∉ Q i ^ (N + 1) := by
  classical
  intro hmem
  have hQne : Q i ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_pow (Nat.succ_ne_zero N), Ideal.mem_bot] at hmem
    exact hf₀ hmem
  have hp : Prime (Q i) := Ideal.prime_of_isPrime hQne (hQmax i).isPrime
  have hdvd : Q i ^ (N + 1) ∣ Ideal.span {f₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hsplit : Ideal.span {f₀} = Q i ^ N * (P₀ * D * ∏ j ∈ Finset.univ.erase i, Q j ^ N) := by
    rw [hspan, ← Finset.mul_prod_erase Finset.univ (fun j => Q j ^ N) (Finset.mem_univ i)]
    ring
  rw [hsplit, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero N hQne)] at hdvd
  rcases hp.dvd_or_dvd hdvd with h | h
  · rcases hp.dvd_or_dvd h with h | h
    · exact hQP i (hP₀.eq_of_le (hQmax i).ne_top (Ideal.le_of_dvd h)).symm
    · exact hDQ i (Ideal.le_of_dvd h)
  · obtain ⟨j, hj, hji⟩ := (hp.dvd_finset_prod_iff _).mp h
    have hle : Q j ≤ Q i := Ideal.le_of_dvd (hp.dvd_of_dvd_pow hji)
    exact (Finset.mem_erase.mp hj).1 (hQinj ((hQmax j).eq_of_le (hQmax i).ne_top hle))

/- English proof (translation)
Simplify using `[map_sum, map_smul]`.
-/
theorem coeff_map_sum {k A : Type} [Field k] [CommRing A] [Algebra k A] {m : ℕ}
    (σ : A →ₐ[k] PowerSeries k) (v : Fin m → A) (c : Fin m → k) (l : ℕ) :
    ∑ j, c j * PowerSeries.coeff l (σ (v j)) = PowerSeries.coeff l (σ (∑ j, c j • v j)) := by
  simp [map_sum, map_smul]

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ N I _ V D P₀ Q f₀ hN hNk hP₀ hyp`. Take `⟨hVfin, hVD, hQmax, hQinj, hQP, hDQ, hDP, hf₀V, hf₀, hspan, hsurj⟩` from `hyp`. Establish `hne : Ideal.span {f₀} ≠ ⊥` using `by simpa [Ideal.span_singleton_eq_bot] using hf₀`. Establish `hf₀P : f₀ ∈ P₀`. Establish `: Ideal.span {f₀} ≤ P₀` using `hspan ▸ le_trans Ideal.mul_le_left Ideal.mul_le_left`.

Conclude with `this (Ideal.mem_span_singleton_self f₀)`. Establish `hf₀Q : ∀ i, f₀ ∈ Q i ^ N`. Introduce `i`. Establish `h1 : Ideal.span {f₀} ≤ ∏ i, Q i ^ N` using `hspan ▸ Ideal.mul_le_right`. Establish `h2 : (∏ i, Q i ^ N) ≤ Q i ^ N` using `Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ N) (Finset.mem_univ i))`.

Conclude with `h2 (h1 (Ideal.mem_span_singleton_self f₀))`. Establish `hP₀ne : P₀ ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hf₀ ((Ideal.mem_bot).mp hf₀P)`. Establish `hQne : ∀ i, Q i ≠ ⊥`.

Introduce `i h`. Use `hf₀Q i` as an intermediate fact. Rewrite `this` using `[h, Ideal.bot_pow (by omega), Ideal.mem_bot]`. Conclude with `hf₀ this`. Take `⟨σ₀, π₀, -, hσ₀inj, hσ₀pow, hσ₀surj⟩` from `GlobalTheory.CurveCompletionG.exists_completion_embedding k A P₀ hP₀ hP₀ne`.

Establish `hcomp` using `fun i => GlobalTheory.CurveCompletionG.exists_completion_embedding k A (Q i) (hQmax i) (hQne i)`. Use `choose σ π hσπ hσinj hσpow hσsurj using hcomp`. Establish `hzero : ∀ (τ : A →ₐ[k] PowerSeries k) (R : Ideal A), (∀ (m : ℕ) (u : A), u ∈ R ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ τ u) → ∀ u, u ∈ R ↔ PowerSeries.constantCoeff (τ u) = 0`. Introduce `τ R h u`. Rewrite using `[← PowerSeries.X_dvd_iff, ← pow_one (PowerSeries.X : PowerSeries k), ← h 1 u, pow_one]`.

Use `set b := Module.finBasis k V with hb`. Use `set m := Module.finrank k V with hm`. Set `v : Fin m → A` to `fun j => (b j : A)`. Establish `hrepr : ∀ x : V, ∑ j, b.repr x j • v j = (x : A)`. Introduce `x`.

Establish `h` using `congrArg Subtype.val (b.sum_repr x)`. Rewrite `h` using `[Submodule.coe_sum]`. Simplify `h` using `[v]`. Set `y₀ : Fin m → k` to `fun j => b.repr ⟨f₀, hf₀V⟩ j`. Establish `hy₀ : ∑ j, y₀ j • v j = f₀` using `hrepr ⟨f₀, hf₀V⟩`.

Establish `hlin : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k) (l : ℕ), ∑ j, c j * PowerSeries.coeff l (τ (v j)) = PowerSeries.coeff l (τ (∑ j, c j • v j))` using `fun τ c l => coeff_map_sum τ v c l`. Establish `hlin0 : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k), ∑ j, c j * PowerSeries.constantCoeff (τ (v j)) = PowerSeries.constantCoeff (τ (∑ j, c j • v j))`. Introduce `τ c`. Simplify `hlin τ c 0` using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Establish `h1 : ∑ j, y₀ j * PowerSeries.constantCoeff (σ₀ (v j)) = 0`.

Rewrite using `[hlin0, hy₀]`. Conclude with `(hzero σ₀ P₀ hσ₀pow f₀).mp hf₀P`. Establish `h2 : ∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (σ i (v j)) = 0`. Introduce `i l hl`. Rewrite using `[hlin, hy₀]`.

Conclude with `PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl`. Establish `h3 : ∀ i, ∑ j, y₀ j * PowerSeries.coeff N (σ i (v j)) ≠ 0`. Introduce `i hc`. Rewrite `hc` using `[hlin, hy₀]`. Apply `not_mem_pow_succ hP₀ hQmax hQinj hQP hDQ hf₀ hspan i` to reduce the goal to its premises.

Rewrite using `[hσpow i (N + 1) f₀, PowerSeries.X_pow_dvd_iff]`. Introduce `l hl`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl` into its components or cases. Conclude with `PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl`. Conclude with `hc`.

Establish `h4 : ∀ (e₀ : k) (e : I → ℕ → k), ∃ h : Fin m → k, ∑ j, h j * PowerSeries.constantCoeff (σ₀ (v j)) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (σ i (v j)) = e i l`. Introduce `e₀ e`. Take `⟨u₀, hu₀⟩` from `hσ₀surj 1 (PowerSeries.C e₀)`. Use `choose u hu using fun i => hσsurj i (N - 1) (PowerSeries.mk (e i))`. Set `P : Option I → Ideal A` to `fun o => o.elim P₀ Q`.

Set `ex : Option I → ℕ` to `fun o => o.elim 1 (fun _ => N - 1)`. Take `⟨w, hw⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) P ex (by`. Introduce and unpack `(_ | i) -`. Use `exacts [Ideal.prime_of_isPrime hP₀ne hP₀.isPrime, Ideal.prime_of_isPrime (hQne i) (hQmax i).isPrime])`. Use the proof step `(by`.

Introduce and unpack `(_ | i) - (_ | j) - hij`. Conclude with `absurd rfl hij`. Conclude with `(hQP j).symm`. Conclude with `hQP i`. Conclude with `hQinj.ne (fun h => hij (by rw [h])))`.

Use the proof step `(fun o => o.1.elim u₀ u)`. Establish `hw₀ : w - u₀ ∈ P₀` using `by simpa [P, ex] using hw none (Finset.mem_univ _)`. Establish `hwi : ∀ i, w - u i ∈ Q i ^ (N - 1)` using `fun i => by`. Simplify `hw (some i) (Finset.mem_univ _)` using `[P, ex]`. Take `⟨v', hv'V, hv'⟩` from `hsurj w`.

Establish `hv'P : v' - u₀ ∈ P₀`. Establish `: w - v' ∈ P₀` using `Ideal.mul_le_left hv'`. Establish `e1 : v' - u₀ = (w - u₀) - (w - v')` using `by ring`. Rewrite using `[e1]`. Conclude with `P₀.sub_mem hw₀ this`.

Establish `hv'Q : ∀ i, v' - u i ∈ Q i ^ (N - 1)`. Introduce `i`. Establish `h5 : (∏ i, Q i ^ (N - 1)) ≤ Q i ^ (N - 1)` using `Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ (N - 1)) (Finset.mem_univ i))`. Establish `: w - v' ∈ Q i ^ (N - 1)` using `h5 (Ideal.mul_le_right hv')`. Establish `e1 : v' - u i = (w - u i) - (w - v')` using `by ring`.

Rewrite using `[e1]`. Conclude with `Ideal.sub_mem _ (hwi i) this`. Use `⟨fun j => b.repr ⟨v', hv'V⟩ j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlin0, hrepr ⟨v', hv'V⟩]`. Establish `h6 : (PowerSeries.X : PowerSeries k) ^ 1 ∣ σ₀ v' - σ₀ u₀`.

Rewrite using `[← map_sub, ← hσ₀pow 1, pow_one]`. Conclude with `hv'P`. Establish `h7 : (PowerSeries.X : PowerSeries k) ∣ PowerSeries.C e₀ - σ₀ v'`. Use `dvd_sub hu₀ h6` as an intermediate fact. Rewrite `this` using `[pow_one]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite `h7` using `[PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero]`. Conclude with `h7.symm`. Introduce `i l hl`.

Rewrite using `[hlin, hrepr ⟨v', hv'V⟩]`. Establish `h6 : (PowerSeries.X : PowerSeries k) ^ (N - 1) ∣ σ i v' - σ i (u i)`. Rewrite using `[← map_sub, ← hσpow i]`. Conclude with `hv'Q i`. Establish `h7` using `PowerSeries.X_pow_dvd_iff.mp (dvd_sub (hu i) h6) l (by omega)`.

Rewrite `h7` using `[show PowerSeries.mk (e i) - σ i (u i) - (σ i v' - σ i (u i)) = PowerSeries.mk (e i) - σ i v' by ring, map_sub, PowerSeries.coeff_mk, sub_eq_zero]`. Conclude with `h7.symm`. Take `⟨y, a, hy0, ha0, hyξ, hyΔ⟩` from `GlobalTheory.PicDiv.DeformZerosHasse.deform k (Fin m) I N (fun j => σ₀ (v j)) (fun i j => σ i (v j)) y₀ (by omega) hNk h1 h2 h3 h4`. Establish `hsub : ∀ i, PowerSeries.HasSubst (a i)` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (ha0 i)`. Set `Δ : I → ℕ → A →ₗ[k] PowerSeries k` to `fun i l => (PowerSeries.substAlgHom (R := k) (hsub i)).toLinearMap ∘ₗ (GlobalTheory.PicDiv.hasse l) ∘ₗ (σ i).toLinearMap`.

Establish `hΔ : ∀ i l u, Δ i l u = ((GlobalTheory.PicDiv.hasse l (σ i u)).subst (a i) : PowerSeries k)`. Introduce `i l u`. Simplify using `only [Δ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, PowerSeries.coe_substAlgHom]`. Establish `hcc : ∀ i u, PowerSeries.constantCoeff (Δ i 0 u) = PowerSeries.constantCoeff (σ i u)`. Introduce `i u`.

Rewrite using `[hΔ, GlobalTheory.PicDiv.hasse_zero]`. Conclude with `constantCoeff_subst_eq _ _ (ha0 i)`. Establish `hunit : ∀ φ : PowerSeries k, IsUnit φ ↔ PowerSeries.constantCoeff φ ≠ 0`. Introduce `φ`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]`.

Establish `hQσ : ∀ i u, u ∈ Q i ↔ PowerSeries.constantCoeff (σ i u) = 0` using `fun i => hzero (σ i) (Q i) (hσpow i)`. Establish `hPσ : ∀ u, u ∈ P₀ ↔ PowerSeries.constantCoeff (σ₀ u) = 0` using `hzero σ₀ P₀ hσ₀pow`. Use `⟨σ₀, Δ, m, v, y, hσ₀inj, ?_, ?_, ?_, ?_, ?_, ?_, hyξ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hΔ, GlobalTheory.PicDiv.hasse_zero, map_one, ← PowerSeries.coe_substAlgHom (hsub i), map_one]`.

Introduce `i l u w`. Simplify using `only [hΔ, map_mul]`. Conclude with `GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz k (a i) _ _ l (ha0 i)`. Introduce `i`. Use `⟨π i, ?_⟩` and prove the remaining obligations.

Establish `hX : GlobalTheory.PicDiv.hasse 1 (PowerSeries.X : PowerSeries k) = 1`. Apply the tactic sequence `ext n; rw [GlobalTheory.PicDiv.coeff_hasse, PowerSeries.coeff_X, PowerSeries.coeff_one]; rcases n with _ | n <;> simp`. Rewrite using `[hΔ, hσπ, hX, ← PowerSeries.coe_substAlgHom (hsub i), map_one]`. Introduce `j`. Conclude with `(b j).2`.

Conclude with `b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)`. Assume the negation of the conclusion as `hcon push_neg at hcon`. Establish `hz : ∀ j, y₀ j = 0`. Introduce `j`. Use `hcon j` as an intermediate fact.

Rewrite `this` using `[hunit, hy0, not_not]`. Then use the resulting hypothesis. Apply `hf₀` to reduce the goal to its premises. Rewrite using `[← hy₀]`. Simplify using `[hz]`. Introduce `i l hl`.

Simplify `hyΔ i l hl` using `only [hΔ]`. Introduce `i i' hii'`. Establish `hle : ¬ Q i' ≤ Q i` using `fun h => hii' (hQinj ((hQmax i').eq_of_le (hQmax i).ne_top h)).symm`. Take `⟨u, hu', hu⟩` from `SetLike.not_le_iff_exists.mp hle`. Use `⟨u, ?_⟩` and prove the remaining obligations.

Rewrite using `[hunit, map_sub, hcc, hcc, (hQσ i' u).mp hu', sub_zero]`. Conclude with `fun h => hu ((hQσ i u).mpr h)`. Introduce `i`. Establish `hle : ¬ P₀ ≤ Q i` using `fun h => hQP i (hP₀.eq_of_le (hQmax i).ne_top h).symm`. Take `⟨u, hu', hu⟩` from `SetLike.not_le_iff_exists.mp hle`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[hunit, map_sub, hcc, (hPσ u).mp hu', sub_zero]`. Conclude with `fun h => hu ((hQσ i u).mpr h)`. Introduce `i`. Take `⟨u, hu', hu⟩` from `SetLike.not_le_iff_exists.mp (hDQ i)`.

Use `⟨u, hu', ?_⟩` and prove the remaining obligations. Rewrite using `[hunit, hcc]`. Conclude with `fun h => hu ((hQσ i u).mpr h)`. Take `⟨u, hu', hu⟩` from `SetLike.not_le_iff_exists.mp hDP`. Use `⟨u, hu', ?_⟩` and prove the remaining obligations.

Rewrite using `[hunit]`. Conclude with `fun h => hu ((hPσ u).mpr h)`.
-/
theorem formal_deformation : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → (N : k) ≠ 0 → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ i p u * Δ i (l - p) w)) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  intro k A _ _ _ _ _ _ N I _ V D P₀ Q f₀ hN hNk hP₀ hyp
  obtain ⟨hVfin, hVD, hQmax, hQinj, hQP, hDQ, hDP, hf₀V, hf₀, hspan, hsurj⟩ := hyp
  classical
  have hne : Ideal.span {f₀} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf₀
  have hf₀P : f₀ ∈ P₀ := by
    have : Ideal.span {f₀} ≤ P₀ := hspan ▸ le_trans Ideal.mul_le_left Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self f₀)
  have hf₀Q : ∀ i, f₀ ∈ Q i ^ N := by
    intro i
    have h1 : Ideal.span {f₀} ≤ ∏ i, Q i ^ N := hspan ▸ Ideal.mul_le_right
    have h2 : (∏ i, Q i ^ N) ≤ Q i ^ N :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ N) (Finset.mem_univ i))
    exact h2 (h1 (Ideal.mem_span_singleton_self f₀))
  have hP₀ne : P₀ ≠ ⊥ := by
    rintro rfl; exact hf₀ ((Ideal.mem_bot).mp hf₀P)
  have hQne : ∀ i, Q i ≠ ⊥ := by
    intro i h
    have := hf₀Q i
    rw [h, Ideal.bot_pow (by omega), Ideal.mem_bot] at this
    exact hf₀ this

  obtain ⟨σ₀, π₀, -, hσ₀inj, hσ₀pow, hσ₀surj⟩ := GlobalTheory.CurveCompletionG.exists_completion_embedding k A P₀ hP₀ hP₀ne
  have hcomp := fun i => GlobalTheory.CurveCompletionG.exists_completion_embedding k A (Q i) (hQmax i) (hQne i)
  choose σ π hσπ hσinj hσpow hσsurj using hcomp
  have hzero : ∀ (τ : A →ₐ[k] PowerSeries k) (R : Ideal A),
      (∀ (m : ℕ) (u : A), u ∈ R ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ τ u) →
      ∀ u, u ∈ R ↔ PowerSeries.constantCoeff (τ u) = 0 := by
    intro τ R h u
    rw [← PowerSeries.X_dvd_iff, ← pow_one (PowerSeries.X : PowerSeries k), ← h 1 u, pow_one]

  set b := Module.finBasis k V with hb
  set m := Module.finrank k V with hm
  let v : Fin m → A := fun j => (b j : A)
  have hrepr : ∀ x : V, ∑ j, b.repr x j • v j = (x : A) := by
    intro x
    have h := congrArg Subtype.val (b.sum_repr x)
    rw [Submodule.coe_sum] at h
    simpa [v] using h
  let y₀ : Fin m → k := fun j => b.repr ⟨f₀, hf₀V⟩ j
  have hy₀ : ∑ j, y₀ j • v j = f₀ := hrepr ⟨f₀, hf₀V⟩
  have hlin : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k) (l : ℕ),
      ∑ j, c j * PowerSeries.coeff l (τ (v j)) = PowerSeries.coeff l (τ (∑ j, c j • v j)) :=
    fun τ c l => coeff_map_sum τ v c l
  have hlin0 : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k),
      ∑ j, c j * PowerSeries.constantCoeff (τ (v j)) =
        PowerSeries.constantCoeff (τ (∑ j, c j • v j)) := by
    intro τ c
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hlin τ c 0
  have h1 : ∑ j, y₀ j * PowerSeries.constantCoeff (σ₀ (v j)) = 0 := by
    rw [hlin0, hy₀]; exact (hzero σ₀ P₀ hσ₀pow f₀).mp hf₀P
  have h2 : ∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (σ i (v j)) = 0 := by
    intro i l hl
    rw [hlin, hy₀]
    exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
  have h3 : ∀ i, ∑ j, y₀ j * PowerSeries.coeff N (σ i (v j)) ≠ 0 := by
    intro i hc
    rw [hlin, hy₀] at hc
    apply not_mem_pow_succ hP₀ hQmax hQinj hQP hDQ hf₀ hspan i
    rw [hσpow i (N + 1) f₀, PowerSeries.X_pow_dvd_iff]
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
    · exact hc
  have h4 : ∀ (e₀ : k) (e : I → ℕ → k), ∃ h : Fin m → k,
      ∑ j, h j * PowerSeries.constantCoeff (σ₀ (v j)) = e₀ ∧
        ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (σ i (v j)) = e i l := by
    intro e₀ e
    obtain ⟨u₀, hu₀⟩ := hσ₀surj 1 (PowerSeries.C e₀)
    choose u hu using fun i => hσsurj i (N - 1) (PowerSeries.mk (e i))
    let P : Option I → Ideal A := fun o => o.elim P₀ Q
    let ex : Option I → ℕ := fun o => o.elim 1 (fun _ => N - 1)
    obtain ⟨w, hw⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) P ex
      (by
        rintro (_ | i) -
        exacts [Ideal.prime_of_isPrime hP₀ne hP₀.isPrime,
          Ideal.prime_of_isPrime (hQne i) (hQmax i).isPrime])
      (by
        rintro (_ | i) - (_ | j) - hij
        · exact absurd rfl hij
        · exact (hQP j).symm
        · exact hQP i
        · exact hQinj.ne (fun h => hij (by rw [h])))
      (fun o => o.1.elim u₀ u)
    have hw₀ : w - u₀ ∈ P₀ := by simpa [P, ex] using hw none (Finset.mem_univ _)
    have hwi : ∀ i, w - u i ∈ Q i ^ (N - 1) := fun i => by
      simpa [P, ex] using hw (some i) (Finset.mem_univ _)
    obtain ⟨v', hv'V, hv'⟩ := hsurj w
    have hv'P : v' - u₀ ∈ P₀ := by
      have : w - v' ∈ P₀ := Ideal.mul_le_left hv'
      have e1 : v' - u₀ = (w - u₀) - (w - v') := by ring
      rw [e1]; exact P₀.sub_mem hw₀ this
    have hv'Q : ∀ i, v' - u i ∈ Q i ^ (N - 1) := by
      intro i
      have h5 : (∏ i, Q i ^ (N - 1)) ≤ Q i ^ (N - 1) :=
        Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ (N - 1)) (Finset.mem_univ i))
      have : w - v' ∈ Q i ^ (N - 1) := h5 (Ideal.mul_le_right hv')
      have e1 : v' - u i = (w - u i) - (w - v') := by ring
      rw [e1]; exact Ideal.sub_mem _ (hwi i) this
    refine ⟨fun j => b.repr ⟨v', hv'V⟩ j, ?_, ?_⟩
    · rw [hlin0, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ 1 ∣ σ₀ v' - σ₀ u₀ := by
        rw [← map_sub, ← hσ₀pow 1, pow_one]; exact hv'P
      have h7 : (PowerSeries.X : PowerSeries k) ∣ PowerSeries.C e₀ - σ₀ v' := by
        have := dvd_sub hu₀ h6
        rw [pow_one] at this
        convert this using 1; ring
      rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h7
      exact h7.symm
    · intro i l hl
      rw [hlin, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ (N - 1) ∣ σ i v' - σ i (u i) := by
        rw [← map_sub, ← hσpow i]; exact hv'Q i
      have h7 := PowerSeries.X_pow_dvd_iff.mp (dvd_sub (hu i) h6) l (by omega)
      rw [show PowerSeries.mk (e i) - σ i (u i) - (σ i v' - σ i (u i)) =
        PowerSeries.mk (e i) - σ i v' by ring, map_sub, PowerSeries.coeff_mk, sub_eq_zero] at h7
      exact h7.symm
  obtain ⟨y, a, hy0, ha0, hyξ, hyΔ⟩ := GlobalTheory.PicDiv.DeformZerosHasse.deform k (Fin m) I N (fun j => σ₀ (v j))
    (fun i j => σ i (v j)) y₀ (by omega) hNk h1 h2 h3 h4
  have hsub : ∀ i, PowerSeries.HasSubst (a i) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (ha0 i)
  let Δ : I → ℕ → A →ₗ[k] PowerSeries k := fun i l =>
    (PowerSeries.substAlgHom (R := k) (hsub i)).toLinearMap ∘ₗ
      (GlobalTheory.PicDiv.hasse l) ∘ₗ (σ i).toLinearMap
  have hΔ : ∀ i l u, Δ i l u =
      ((GlobalTheory.PicDiv.hasse l (σ i u)).subst (a i) : PowerSeries k) := by
    intro i l u
    simp only [Δ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      PowerSeries.coe_substAlgHom]
  have hcc : ∀ i u, PowerSeries.constantCoeff (Δ i 0 u) = PowerSeries.constantCoeff (σ i u) := by
    intro i u
    rw [hΔ, GlobalTheory.PicDiv.hasse_zero]
    exact constantCoeff_subst_eq _ _ (ha0 i)
  have hunit : ∀ φ : PowerSeries k, IsUnit φ ↔ PowerSeries.constantCoeff φ ≠ 0 := by
    intro φ; rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hQσ : ∀ i u, u ∈ Q i ↔ PowerSeries.constantCoeff (σ i u) = 0 :=
    fun i => hzero (σ i) (Q i) (hσpow i)
  have hPσ : ∀ u, u ∈ P₀ ↔ PowerSeries.constantCoeff (σ₀ u) = 0 := hzero σ₀ P₀ hσ₀pow
  refine ⟨σ₀, Δ, m, v, y, hσ₀inj, ?_, ?_, ?_, ?_, ?_, ?_, hyξ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hΔ, GlobalTheory.PicDiv.hasse_zero, map_one, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro i l u w
    simp only [hΔ, map_mul]
    exact GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz k (a i) _ _ l (ha0 i)
  · intro i
    refine ⟨π i, ?_⟩
    have hX : GlobalTheory.PicDiv.hasse 1 (PowerSeries.X : PowerSeries k) = 1 := by
      ext n; rw [GlobalTheory.PicDiv.coeff_hasse, PowerSeries.coeff_X, PowerSeries.coeff_one]; rcases n with _ | n <;> simp
    rw [hΔ, hσπ, hX, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro j; exact (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · by_contra hcon
    push_neg at hcon
    have hz : ∀ j, y₀ j = 0 := by
      intro j
      have := hcon j
      rwa [hunit, hy0, not_not] at this
    apply hf₀
    rw [← hy₀]
    simp [hz]
  · intro i l hl
    simpa only [hΔ] using hyΔ i l hl
  · intro i i' hii'
    have hle : ¬ Q i' ≤ Q i := fun h =>
      hii' (hQinj ((hQmax i').eq_of_le (hQmax i).ne_top h)).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, hcc, (hQσ i' u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    have hle : ¬ P₀ ≤ Q i := fun h => hQP i (hP₀.eq_of_le (hQmax i).ne_top h).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, (hPσ u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp (hDQ i)
    refine ⟨u, hu', ?_⟩
    rw [hunit, hcc]
    exact fun h => hu ((hQσ i u).mpr h)
  · obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hDP
    refine ⟨u, hu', ?_⟩
    rw [hunit]
    exact fun h => hu ((hPσ u).mpr h)

end GlobalTheory.PicDiv.FormalDeformHasse

namespace GlobalTheory.PicDiv
namespace GenericSpecialHasse

/- English proof (translation)
Introduce `h`. Establish `e` using `hmul x hx _ hi`. Rewrite `e` using `[Ring.mul_inverse_cancel x hu, hone, h, zero_mul]`. Conclude with `one_ne_zero e`.
-/
theorem ext_unit_ne {k R : Type} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (S : Subalgebra k R) (L : R →ₗ[k] k) (hone : L 1 = 1)
    (hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z) (x : R) (hx : x ∈ S) (hu : IsUnit x)
    (hi : Ring.inverse x ∈ S) : L x ≠ 0 := by
  intro h
  have e := hmul x hx _ hi
  rw [Ring.mul_inverse_cancel x hu, hone, h, zero_mul] at e
  exact one_ne_zero e

/- English proof (translation)
Establish `h1 : g (u - g u • 1) = 0` using `by simp [hg]`. Establish `h2` using `(hk _).1 h1`. Rewrite `h2` using `[map_sub, map_smul, hh, smul_eq_mul, mul_one, sub_eq_zero]`. Conclude with `h2.symm`.
-/
theorem lin_eq_of_zero_iff {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (g h : A →ₗ[k] k) (hg : g 1 = 1) (hh : h 1 = 1) (hk : ∀ u, g u = 0 ↔ h u = 0) (u : A) :
    g u = h u := by
  have h1 : g (u - g u • 1) = 0 := by simp [hg]
  have h2 := (hk _).1 h1
  rw [map_sub, map_smul, hh, smul_eq_mul, mul_one, sub_eq_zero] at h2
  exact h2.symm

end GenericSpecialHasse

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ R _ _ _ N I _ V D hN hex`. Take `⟨ξ, Δ, m, v, y, hinj, h01, hleib, hπ, hvV, hli, ⟨j0, hj0⟩, heq0, heqΔ, hsep, hsepξ, hD, hDξ⟩` from `hex`. Establish `hsep' : ∀ p : I × I, ∃ u : A, p.1 ≠ p.2 → IsUnit (Δ p.1 0 u - Δ p.2 0 u)`. Introduce `p`. Distinguish the cases in `hp : p.1 = p.2`.

Conclude with `⟨0, fun h => absurd hp h⟩`. Take `⟨u, hu⟩` from `hsep p.1 p.2 hp`. Conclude with `⟨u, fun _ => hu⟩`. Use `choose us hus using hsep'`. Use `choose uξ huξ using hsepξ`.

Use `choose uD huDmem huD using hD`. Take `⟨u0, hu0D, hu0⟩` from `hDξ`. Use `choose TJ hTJ using fun i => GlobalTheory.PicDiv.jets_mem_subalgebra_of_finiteType k A R N (Δ i) (h01 i) (hleib i)`. Set `T : Finset R` to `Finset.univ.biUnion TJ ∪ Finset.univ.image y ∪ Finset.univ.image (fun p : I × I => Ring.inverse (Δ p.1 0 (us p) - Δ p.2 0 (us p))) ∪ Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uξ i) - ξ (uξ i))) ∪ Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uD i))) ∪ {Ring.inverse (ξ u …`. Take `⟨a, S, hξS, ha0, hTS, hspec⟩` from `GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k A R ξ hinj T`.

Use `⟨a, ha0, ?_⟩` and prove the remaining obligations. Introduce `P hPmax haP`. Take `⟨-, φ, hφ⟩` from `(GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P hPmax`. Take `⟨ψ, hψ⟩` from `hspec φ (fun h => haP ((hφ a).2 h))`. Take `⟨L, hL⟩` from `LinearMap.exists_extend (ψ.toLinearMap.comp (LinearEquiv.refl k (Subalgebra.toSubmodule S)).toLinearMap)`.

Establish `hLS : ∀ x (hx : x ∈ S), L x = ψ ⟨x, hx⟩`. Introduce `x hx`. Conclude with `LinearMap.congr_fun hL ⟨x, hx⟩`. Establish `hone : L 1 = 1` using `by rw [hLS 1 S.one_mem]; exact map_one ψ`. Establish `hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z`.

Introduce `x hx z hz`. Rewrite using `[hLS _ (S.mul_mem hx hz), hLS x hx, hLS z hz, ← map_mul]`. Both sides reduce to the same expression. Establish `hLξ : ∀ u, L (ξ u) = φ u` using `fun u => by rw [hLS _ (hξS u), hψ]`. Establish `hSΔ : ∀ i l, l < N → ∀ u, Δ i l u ∈ S` using `fun i => hTJ i S (fun t ht => hTS t (by simp only [T, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, Finset.mem_univ _, ht⟩))))))`.

Establish `hy : ∀ j, y j ∈ S` using `fun j => hTS _ (by simp [T])`. Establish `hN0 : 0 < N` using `by omega`. Establish `hN1 : 1 < N` using `by omega`. Set `Δ' : I → ℕ → A →ₗ[k] k` to `fun i l => if l < N then L ∘ₗ Δ i l else 0`. Establish `hΔ' : ∀ i l, l < N → ∀ u, Δ' i l u = L (Δ i l u)`.

Introduce `i l h u`. Simplify using `[Δ', h]`. Establish `hjet : ∀ i, ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ' i 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ' i l f = 0) → f ∈ Q ^ N`. Introduce `i`. Apply `GlobalTheory.T.exists_maximal_mem_pow_of_hasse_vanishing k A N (Δ' i) hN` to reduce the goal to its premises.

Rewrite using `[hΔ' i 0 hN0, h01 i, hone]`. Introduce `l hl u w`. Rewrite using `[hΔ' i l hl, hleib i l u w, map_sum]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p < l + 1` using `Finset.mem_range.1 hp`.

Rewrite using `[hmul _ (hSΔ i p (by omega) u) _ (hSΔ i (l - p) (by omega) w), hΔ' i p (by omega), hΔ' i (l - p) (by omega)]`. Take `⟨π, hπ'⟩` from `hπ i`. Conclude with `⟨π, by rw [hΔ' i 1 hN1, hπ', hone]⟩`. Use `choose Q' hQmax hQmem hQpow using hjet`. Establish `hunit : ∀ x ∈ S, IsUnit x → Ring.inverse x ∈ S → L x ≠ 0` using `fun x hx hu hi => GenericSpecialHasse.ext_unit_ne S L hone hmul x hx hu hi`.

Set `f : A` to `∑ j, L (y j) • v j`. Use `⟨Q', f, hQmax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i i' hii'`. Assume the negation of the conclusion as `hne`. Establish `hu` using `hus (i, i') hne`.

Use `set u := us (i, i')`. Establish `heqv` using `GenericSpecialHasse.lin_eq_of_zero_iff (Δ' i 0) (Δ' i' 0) (by rw [hΔ' i 0 hN0, h01 i, hone]) (by rw [hΔ' i' 0 hN0, h01 i', hone]) (fun w => by rw [← hQmem, ← hQmem, hii']) u`. Rewrite `heqv` using `[hΔ' i 0 hN0, hΔ' i' 0 hN0]`. Use `hunit _ (S.sub_mem (hSΔ i 0 hN0 u) (hSΔ i' 0 hN0 u)) hu (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i'), Finset.mem_univ _, rfl⟩))))) ?_` and prove the remaining obligations. Rewrite using `[map_sub, heqv, sub_self]`.

Introduce `i hiP`. Establish `hu` using `huξ i`. Establish `heqv` using `GenericSpecialHasse.lin_eq_of_zero_iff (Δ' i 0) φ.toLinearMap (by rw [hΔ' i 0 hN0, h01 i, hone]) (map_one φ) (fun w => by rw [← hQmem, hiP, hφ]; rfl) (uξ i)`. Rewrite `heqv` using `[hΔ' i 0 hN0, AlgHom.toLinearMap_apply, ← hLξ]`. Use `hunit _ (S.sub_mem (hSΔ i 0 hN0 _) (hξS _)) hu (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩)))) ?_` and prove the remaining obligations.

Rewrite using `[map_sub, heqv, sub_self]`. Introduce `i hDQ`. Establish `h0 : Δ' i 0 (uD i) = 0` using `(hQmem i _).1 (hDQ (huDmem i))`. Rewrite `h0` using `[hΔ' i 0 hN0]`. Conclude with `hunit _ (hSΔ i 0 hN0 _) (huD i) (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩))) h0`.

Introduce `hDP`. Establish `h0 : φ u0 = 0` using `(hφ u0).1 (hDP hu0D)`. Rewrite `h0` using `[← hLξ]`. Conclude with `hunit _ (hξS _) hu0 (hTS _ (by simp [T])) h0`. Conclude with `Submodule.sum_mem _ fun j _ => V.smul_mem _ (hvV j)`.

Introduce `hf`. Use `(Fintype.linearIndependent_iff.1 hli) (fun j => L (y j)) hf j0` as an intermediate fact. Conclude with `hunit _ (hy j0) hj0 (hTS _ (by simp [T])) this`. Apply `(hφ f).2` to reduce the goal to its premises. Establish `: φ f = L (∑ j, y j * ξ (v j))`.

Simplify using `only [f, map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hmul _ (hy j) _ (hξS _), hLξ]`. Rewrite using `[this, heq0, map_zero]`. Introduce `i`.

Apply `hQpow i` to reduce the goal to its premises. Introduce `l hl`. Establish `: Δ' i l f = L (∑ j, y j * Δ i l (v j))`. Simplify using `only [f, map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hmul _ (hy j) _ (hSΔ i l hl _), hΔ' i l hl]`. Rewrite using `[this, heqΔ i l hl, map_zero]`.
-/
theorem specialise_generic_solution_hasse : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (R : Type) [CommRing R] [IsDomain R] [Algebra k R] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D : Ideal A), 2 ≤ N → (∃ (ξ : A →ₐ[k] R) (Δ : I → ℕ → A →ₗ[k] R) (m : ℕ) (v : Fin m → A) (y : Fin m → R),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ i p u * Δ i (l - p) w)) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u))) → ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∃ (Q' : I → Ideal A) (f : A), (∀ i, (Q' i).IsMaximal) ∧ Function.Injective Q' ∧ (∀ i, Q' i ≠ P) ∧ (∀ i, ¬ D ≤ Q' i) ∧ ¬ D ≤ P ∧ f ∈ V ∧ f ≠ 0 ∧ f ∈ P ∧ ∀ i, f ∈ Q' i ^ N := by
  intro k A _ _ _ _ _ _ R _ _ _ N I _ V D hN hex
  classical
  obtain ⟨ξ, Δ, m, v, y, hinj, h01, hleib, hπ, hvV, hli, ⟨j0, hj0⟩, heq0, heqΔ, hsep, hsepξ,
    hD, hDξ⟩ := hex
  have hsep' : ∀ p : I × I, ∃ u : A, p.1 ≠ p.2 → IsUnit (Δ p.1 0 u - Δ p.2 0 u) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨0, fun h => absurd hp h⟩
    · obtain ⟨u, hu⟩ := hsep p.1 p.2 hp
      exact ⟨u, fun _ => hu⟩
  choose us hus using hsep'
  choose uξ huξ using hsepξ
  choose uD huDmem huD using hD
  obtain ⟨u0, hu0D, hu0⟩ := hDξ
  choose TJ hTJ using fun i => GlobalTheory.PicDiv.jets_mem_subalgebra_of_finiteType k A R N (Δ i) (h01 i) (hleib i)
  let T : Finset R := Finset.univ.biUnion TJ ∪ Finset.univ.image y ∪
    Finset.univ.image (fun p : I × I => Ring.inverse (Δ p.1 0 (us p) - Δ p.2 0 (us p))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uξ i) - ξ (uξ i))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uD i))) ∪
    {Ring.inverse (ξ u0), Ring.inverse (y j0)}
  obtain ⟨a, S, hξS, ha0, hTS, hspec⟩ := GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k A R ξ hinj T
  refine ⟨a, ha0, ?_⟩
  intro P hPmax haP
  obtain ⟨-, φ, hφ⟩ := (GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P hPmax
  obtain ⟨ψ, hψ⟩ := hspec φ (fun h => haP ((hφ a).2 h))
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (ψ.toLinearMap.comp
    (LinearEquiv.refl k (Subalgebra.toSubmodule S)).toLinearMap)
  have hLS : ∀ x (hx : x ∈ S), L x = ψ ⟨x, hx⟩ := by
    intro x hx
    exact LinearMap.congr_fun hL ⟨x, hx⟩
  have hone : L 1 = 1 := by rw [hLS 1 S.one_mem]; exact map_one ψ
  have hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z := by
    intro x hx z hz
    rw [hLS _ (S.mul_mem hx hz), hLS x hx, hLS z hz, ← map_mul]; rfl
  have hLξ : ∀ u, L (ξ u) = φ u := fun u => by rw [hLS _ (hξS u), hψ]
  have hSΔ : ∀ i l, l < N → ∀ u, Δ i l u ∈ S := fun i =>
    hTJ i S (fun t ht => hTS t (by simp only [T, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, Finset.mem_univ _, ht⟩))))))
  have hy : ∀ j, y j ∈ S := fun j => hTS _ (by simp [T])
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  let Δ' : I → ℕ → A →ₗ[k] k := fun i l => if l < N then L ∘ₗ Δ i l else 0
  have hΔ' : ∀ i l, l < N → ∀ u, Δ' i l u = L (Δ i l u) := by
    intro i l h u; simp [Δ', h]
  have hjet : ∀ i, ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ' i 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ' i l f = 0) → f ∈ Q ^ N := by
    intro i
    apply GlobalTheory.T.exists_maximal_mem_pow_of_hasse_vanishing k A N (Δ' i) hN
    · rw [hΔ' i 0 hN0, h01 i, hone]
    · intro l hl u w
      rw [hΔ' i l hl, hleib i l u w, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < l + 1 := Finset.mem_range.1 hp
      rw [hmul _ (hSΔ i p (by omega) u) _ (hSΔ i (l - p) (by omega) w),
        hΔ' i p (by omega), hΔ' i (l - p) (by omega)]
    · obtain ⟨π, hπ'⟩ := hπ i
      exact ⟨π, by rw [hΔ' i 1 hN1, hπ', hone]⟩
  choose Q' hQmax hQmem hQpow using hjet
  have hunit : ∀ x ∈ S, IsUnit x → Ring.inverse x ∈ S → L x ≠ 0 :=
    fun x hx hu hi => GenericSpecialHasse.ext_unit_ne S L hone hmul x hx hu hi
  let f : A := ∑ j, L (y j) • v j
  refine ⟨Q', f, hQmax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i i' hii'
    by_contra hne
    have hu := hus (i, i') hne
    set u := us (i, i')
    have heqv := GenericSpecialHasse.lin_eq_of_zero_iff (Δ' i 0) (Δ' i' 0)
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (by rw [hΔ' i' 0 hN0, h01 i', hone])
      (fun w => by rw [← hQmem, ← hQmem, hii']) u
    rw [hΔ' i 0 hN0, hΔ' i' 0 hN0] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 u) (hSΔ i' 0 hN0 u)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i'), Finset.mem_univ _, rfl⟩))))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hiP
    have hu := huξ i
    have heqv := GenericSpecialHasse.lin_eq_of_zero_iff (Δ' i 0) φ.toLinearMap
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (map_one φ)
      (fun w => by rw [← hQmem, hiP, hφ]; rfl) (uξ i)
    rw [hΔ' i 0 hN0, AlgHom.toLinearMap_apply, ← hLξ] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 _) (hξS _)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩)))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hDQ
    have h0 : Δ' i 0 (uD i) = 0 := (hQmem i _).1 (hDQ (huDmem i))
    rw [hΔ' i 0 hN0] at h0
    exact hunit _ (hSΔ i 0 hN0 _) (huD i)
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩))) h0
  · intro hDP
    have h0 : φ u0 = 0 := (hφ u0).1 (hDP hu0D)
    rw [← hLξ] at h0
    exact hunit _ (hξS _) hu0 (hTS _ (by simp [T])) h0
  · exact Submodule.sum_mem _ fun j _ => V.smul_mem _ (hvV j)
  · intro hf
    have := (Fintype.linearIndependent_iff.1 hli) (fun j => L (y j)) hf j0
    exact hunit _ (hy j0) hj0 (hTS _ (by simp [T])) this
  · apply (hφ f).2
    have : φ f = L (∑ j, y j * ξ (v j)) := by
      simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hξS _), hLξ]
    rw [this, heq0, map_zero]
  · intro i
    apply hQpow i
    intro l hl
    have : Δ' i l f = L (∑ j, y j * Δ i l (v j)) := by
      simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hSΔ i l hl _), hΔ' i l hl]
    rw [this, heqΔ i l hl, map_zero]

end GlobalTheory.PicDiv

namespace GlobalTheory.PicDiv

/- English proof (translation)
Rewrite using `[← map_pow, ← map_mul, ← map_mul]`. Establish `hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A)` using `mul_mem (mul_mem hP hD) (pow_mem hC N)`. Establish `e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩` using `Subtype.ext (by simp)`. Rewrite using `[e, ClassGroup.mk0_eq_one_iff, ← h]`. Conclude with `⟨⟨f, rfl⟩⟩`.
-/
theorem classGroup_mk0_mul_mul_pow_eq_one_of_span_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (N : ℕ) (P D C : Ideal A) (f : A) (hP : P ∈ nonZeroDivisors (Ideal A))
    (hD : D ∈ nonZeroDivisors (Ideal A)) (hC : C ∈ nonZeroDivisors (Ideal A))
    (h : Ideal.span {f} = P * D * C ^ N) :
    ClassGroup.mk0 ⟨P, hP⟩ * ClassGroup.mk0 ⟨D, hD⟩ * ClassGroup.mk0 ⟨C, hC⟩ ^ N = 1 := by
  rw [← map_pow, ← map_mul, ← map_mul]
  have hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A) :=
    mul_mem (mul_mem hP hD) (pow_mem hC N)
  have e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩ :=
    Subtype.ext (by simp)
  rw [e, ClassGroup.mk0_eq_one_iff, ← h]
  exact ⟨⟨f, rfl⟩⟩

/- English proof (translation)
Use `prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Introduce `hi`. Establish `hb : (⊥ : Ideal A).IsMaximal`. Use `hQ i` as an intermediate fact. Rewrite `this` using `[hi]`. Then use the resulting hypothesis.

Conclude with `h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm`.
-/
theorem prod_maximal_mem_nonZeroDivisors {A : Type} [CommRing A] [IsDedekindDomain A]
    {I : Type} [Fintype I] (Q : I → Ideal A) (hQ : ∀ i, (Q i).IsMaximal)
    (P₀ : Ideal A) (hP₀ : P₀.IsMaximal) (h₀ : P₀ ≠ ⊥) :
    (∏ i, Q i) ∈ nonZeroDivisors (Ideal A) := by
  refine prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_
  intro hi
  have hb : (⊥ : Ideal A).IsMaximal := by
    have := hQ i
    rwa [hi] at this
  exact h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ _ _ _ hred N hN hNk P₀ hP₀ h₀`. Use `haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance`. Take `⟨r, V, D, Q, f₀, hset, hdeg⟩` from `GlobalTheory.PicDiv.linear_system_setup k A hred N P₀ (by omega) hP₀`. Establish `hform` using `GlobalTheory.PicDiv.FormalDeformHasse.formal_deformation k A N (Fin r) V D P₀ Q f₀ hN hNk hP₀ hset`. Take `⟨a, ha, hall⟩` from `GlobalTheory.PicDiv.specialise_generic_solution_hasse k A (PowerSeries k) N (Fin r) V D hN hform`.

Take `⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩` from `hset`. Use `⟨a, ha, fun P hP haP h => ?_⟩` and prove the remaining obligations. Take `⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩` from `hall P hP haP`. Establish `hspan` using `GlobalTheory.PicDiv.degree_count_generates k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)`. Establish `hP₀ne : P₀ ≠ ⊥` using `nonZeroDivisors.ne_zero h₀`.

Establish `hD : D ∈ nonZeroDivisors (Ideal A)`. Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Introduce `hD0`. Apply `hDP` to reduce the goal to its premises. Rewrite using `[hD0]`.

Conclude with `bot_le`. Establish `hC` using `prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne`. Establish `hC'` using `prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne`. Rewrite `hspan`, `hspan₀` using `[Finset.prod_pow]`. Establish `e` using `classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan`.

Establish `e₀` using `classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀`. Use `⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩` and prove the remaining obligations. Generalize the expression as in `ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢`. Generalize the expression as in `ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢`. Generalize the expression as in `ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀`.

Generalize the expression as in `ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢`. Generalize the expression as in `ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢`. Establish `e' : p * c' ^ N = p₀ * c ^ N`. Apply `mul_right_cancel (b := d)` to reduce the goal to its premises. Rewrite using `[mul_right_comm p, mul_right_comm p₀, e, e₀]`.

Rewrite using `[div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]`.
-/
theorem exists_classGroup_mk0_eq_mul_pow_reduced :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (N : ℕ), 2 ≤ N → (N : k) ≠ 0 → ∀ P₀ : Ideal A, P₀.IsMaximal →
      ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal →
        a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A,
          ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  intro k A _ _ _ _ _ _ _ _ _ hred N hN hNk P₀ hP₀ h₀
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨r, V, D, Q, f₀, hset, hdeg⟩ := GlobalTheory.PicDiv.linear_system_setup k A hred N P₀ (by omega) hP₀
  have hform := GlobalTheory.PicDiv.FormalDeformHasse.formal_deformation k A N (Fin r) V D P₀ Q f₀ hN hNk hP₀ hset
  obtain ⟨a, ha, hall⟩ := GlobalTheory.PicDiv.specialise_generic_solution_hasse k A (PowerSeries k) N (Fin r) V D hN hform
  obtain ⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩ := hset
  refine ⟨a, ha, fun P hP haP h => ?_⟩
  obtain ⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩ := hall P hP haP
  have hspan := GlobalTheory.PicDiv.degree_count_generates k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP
    hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)
  have hP₀ne : P₀ ≠ ⊥ := nonZeroDivisors.ne_zero h₀
  have hD : D ∈ nonZeroDivisors (Ideal A) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hD0
    apply hDP
    rw [hD0]
    exact bot_le
  have hC := prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne
  have hC' := prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne
  rw [Finset.prod_pow] at hspan hspan₀
  have e := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan
  have e₀ := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀
  refine ⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩
  generalize ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢
  generalize ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢
  generalize ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀
  generalize ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢
  generalize ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢
  have e' : p * c' ^ N = p₀ * c ^ N := by
    apply mul_right_cancel (b := d)
    rw [mul_right_comm p, mul_right_comm p₀, e, e₀]
  rw [div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]

end GlobalTheory.PicDiv

namespace GlobalTheory.PicDiv

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Assume the negation of the conclusion as `hp0`. Establish `hint : IsIntegral k y` using `(isAlgebraic_iff_isIntegral).mp ⟨p, hp0, hp⟩`. Establish `hdeg : (minpoly k y).natDegree = 1`.

Use `IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)` as an intermediate fact. Conclude with `Polynomial.natDegree_eq_of_degree_eq_some this`. Take `⟨r, hr⟩` from `(minpoly.natDegree_eq_one_iff).mp hdeg`. Use `letI : Algebra k[X] B := (Polynomial.aeval y).toRingHom.toAlgebra`. Use `haveI : Module.Finite k[X] B := hfin`.

Establish `hsmul : ∀ (q : k[X]) (b : B), q • b = (q.eval r) • b`. Introduce `q b`. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `Polynomial.aeval y q * b = _`. Rewrite using `[← hr, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def]`.

Both sides reduce to the same expression. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := k[X]) (M := B)`. Establish `hk : Submodule.span k (s : Set B) = ⊤`. Establish `key : ∀ b ∈ Submodule.span k[X] (s : Set B), b ∈ Submodule.span k (s : Set B)`. Introduce `b hb`.

Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact zero_mem _`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`. Consider the case `smul q x _ hx => rw [hsmul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[eq_top_iff]`. Introduce `b _`. Conclude with `key b (by rw [hs]; trivial)`. Use `haveI : Module.Finite k B := ⟨⟨s, hk⟩⟩`.

Conclude with `hB ((Algebra.IsIntegral.isField_iff_isField (algebraMap k B).injective).mp (Field.toIsField k))`.
-/
theorem injective_of_finite_not_field (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] (y : B) (hfin : (Polynomial.aeval (R := k) y).Finite) (hB : ¬ IsField B) :
    Function.Injective (Polynomial.aeval (R := k) y) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have hint : IsIntegral k y := (isAlgebraic_iff_isIntegral).mp ⟨p, hp0, hp⟩
  have hdeg : (minpoly k y).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨r, hr⟩ := (minpoly.natDegree_eq_one_iff).mp hdeg
  letI : Algebra k[X] B := (Polynomial.aeval y).toRingHom.toAlgebra
  haveI : Module.Finite k[X] B := hfin
  have hsmul : ∀ (q : k[X]) (b : B), q • b = (q.eval r) • b := by
    intro q b
    rw [Algebra.smul_def, Algebra.smul_def]
    change Polynomial.aeval y q * b = _
    rw [← hr, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def]
    rfl
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k[X]) (M := B)
  have hk : Submodule.span k (s : Set B) = ⊤ := by
    have key : ∀ b ∈ Submodule.span k[X] (s : Set B), b ∈ Submodule.span k (s : Set B) := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem _
      | add x z _ _ hx hz => exact add_mem hx hz
      | smul q x _ hx => rw [hsmul]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro b _
    exact key b (by rw [hs]; trivial)
  haveI : Module.Finite k B := ⟨⟨s, hk⟩⟩
  exact hB ((Algebra.IsIntegral.isField_iff_isField (algebraMap k B).injective).mp (Field.toIsField k))

end GlobalTheory.PicDiv

namespace GlobalTheory.PicDiv

/- English proof (translation)
Introduce `k B _ _ _ _ _ _ _ q hq c`. It suffices to establish `h : ∀ c : ClassGroup B, ∃ d, d ^ q = c by`. Take `⟨d, hd⟩` from `h ((ClassGroup.equivPic B).symm c)`. Conclude with `⟨ClassGroup.equivPic B d, by rw [← map_pow, hd, MulEquiv.apply_symm_apply]⟩`. Introduce `c`.

Establish `hNk : (q : k) ≠ 0` using `hq.ne_zero`. Establish `hq0 : q ≠ 0` using `by rintro rfl; exact hNk (by simp)`. Distinguish the cases in `hfield : IsField B`. Use `⟨1, ?_⟩` and prove the remaining obligations. Take `⟨⟨I, hI⟩, rfl⟩` from `ClassGroup.mk0_surjective c`.

Rewrite using `[one_pow, eq_comm, ClassGroup.mk0_eq_one_iff]`. Establish `hI0 : I ≠ ⊥` using `nonZeroDivisors.ne_zero hI`. Take `⟨x, hxI, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI0`. Establish `hu : IsUnit x`. Take `⟨z, hz⟩` from `hfield.mul_inv_cancel hx0`.

Conclude with `isUnit_iff_exists_inv.mpr ⟨z, hz⟩`. Rewrite using `[Ideal.eq_top_of_isUnit_mem I hxI hu]`. Conclude with `⟨⟨1, by simp⟩⟩`. Break down `Nat.lt_or_ge q 2 with h1 | h2` into its components or cases. Establish `: q = 1` using `by omega`.

Substitute `this` using the available equality. Conclude with `⟨c, pow_one c⟩`. Take `⟨y, hfin, hred⟩` from `GlobalTheory.T.exists_separable_normalization_reduced_fibers k B hfield`. Use `letI : Algebra k[X] B := (Polynomial.aeval y).toRingHom.toAlgebra`. Establish `hmap : ∀ p : k[X], algebraMap k[X] B p = Polynomial.aeval y p` using `fun p => rfl`.

Use `haveI : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq (fun c => by`. Rewrite using `[hmap, Polynomial.algebraMap_eq, Polynomial.aeval_C])`. Use `haveI : Module.Finite k[X] B := hfin`. Establish `hinj : Function.Injective (algebraMap k[X] B)` using `injective_of_finite_not_field k B y hfin hfield`. Use `haveI : Module.IsTorsionFree k[X] B := (NoZeroSMulDivisors.iff_algebraMap_injective).mpr hinj`.

Use `haveI : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'`. Establish `hred' : (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal B, Q.IsMaximal → algebraMap k[X] B (X - C α) ∉ Q ^ 2)`. Take `⟨δ, hδ0, hδ⟩` from `hred`. Use `⟨δ, hδ0, fun α hα Q hQ => ?_⟩` and prove the remaining obligations. Rewrite using `[hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]`.

Conclude with `hδ α hα Q hQ`. Establish `key` using `exists_classGroup_mk0_eq_mul_pow_reduced k B hred' q h2 hNk`. Take `⟨f, hf0, hfmod⟩` from `GlobalTheory.T.exists_finrank_quotient_span_mod_eq_one' k B q (by omega)`. Take `⟨d, hd⟩` from `classGroup_nthPower_of_codim_one_mod k B q (by omega) key ⟨f, hf0, hfmod⟩ c`. Conclude with `⟨d, hd.symm⟩`.
-/
theorem pic_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  suffices h : ∀ c : ClassGroup B, ∃ d, d ^ q = c by
    obtain ⟨d, hd⟩ := h ((ClassGroup.equivPic B).symm c)
    exact ⟨ClassGroup.equivPic B d, by rw [← map_pow, hd, MulEquiv.apply_symm_apply]⟩
  intro c
  have hNk : (q : k) ≠ 0 := hq.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; exact hNk (by simp)
  by_cases hfield : IsField B
  · refine ⟨1, ?_⟩
    obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
    rw [one_pow, eq_comm, ClassGroup.mk0_eq_one_iff]
    have hI0 : I ≠ ⊥ := nonZeroDivisors.ne_zero hI
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    have hu : IsUnit x := by
      obtain ⟨z, hz⟩ := hfield.mul_inv_cancel hx0
      exact isUnit_iff_exists_inv.mpr ⟨z, hz⟩
    rw [Ideal.eq_top_of_isUnit_mem I hxI hu]
    exact ⟨⟨1, by simp⟩⟩
  rcases Nat.lt_or_ge q 2 with h1 | h2
  · have : q = 1 := by omega
    subst this; exact ⟨c, pow_one c⟩
  obtain ⟨y, hfin, hred⟩ := GlobalTheory.T.exists_separable_normalization_reduced_fibers k B hfield
  letI : Algebra k[X] B := (Polynomial.aeval y).toRingHom.toAlgebra
  have hmap : ∀ p : k[X], algebraMap k[X] B p = Polynomial.aeval y p := fun p => rfl
  haveI : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [hmap, Polynomial.algebraMap_eq, Polynomial.aeval_C])
  haveI : Module.Finite k[X] B := hfin
  have hinj : Function.Injective (algebraMap k[X] B) := injective_of_finite_not_field k B y hfin hfield
  haveI : Module.IsTorsionFree k[X] B := (NoZeroSMulDivisors.iff_algebraMap_injective).mpr hinj
  haveI : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'
  have hred' : (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal B, Q.IsMaximal → algebraMap k[X] B (X - C α) ∉ Q ^ 2) := by
    obtain ⟨δ, hδ0, hδ⟩ := hred
    refine ⟨δ, hδ0, fun α hα Q hQ => ?_⟩
    rw [hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hδ α hα Q hQ
  have key := exists_classGroup_mk0_eq_mul_pow_reduced k B hred' q h2 hNk
  obtain ⟨f, hf0, hfmod⟩ := GlobalTheory.T.exists_finrank_quotient_span_mod_eq_one' k B q (by omega)
  obtain ⟨d, hd⟩ := classGroup_nthPower_of_codim_one_mod k B q (by omega) key ⟨f, hf0, hfmod⟩ c
  exact ⟨d, hd.symm⟩

end GlobalTheory.PicDiv
