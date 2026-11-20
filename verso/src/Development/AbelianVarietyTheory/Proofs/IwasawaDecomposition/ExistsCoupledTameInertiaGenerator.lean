import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubOneLtOfRed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharactersStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
noncomputable section

open GlobalTheory.TameCoupledEx in
/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A v hA g _ hg hg2 ζ hζ`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Use `haveI : IsGalois E Ω := {}`. Establish `hgp : g.Prime` using `Fact.out`.

Establish `hgv : A.valuation ((g : ℕ) : Ω) < 1` using `val_g_lt A v hA hg`. Establish `hg0 : ((g : ℕ) : Ω) ≠ 0` using `Nat.cast_ne_zero.2 hgp.ne_zero`. Take `⟨κ⟩` from `hK E Ω A v hA g hg`. Set `D : ℕ → ℕ` to `fun n => (n + 1).factorial`. Establish `hDpos : ∀ n, 0 < D n` using `fun n => Nat.factorial_pos _`.

Establish `hNpos : ∀ d, 0 < d → 0 < g ^ d - 1` using `fun d hd => pow_sub_one_pos hgp hd`. Establish `hgN : ∀ d, 0 < d → ¬ g ∣ g ^ d - 1` using `fun d hd => not_dvd_pow_sub_one hgp hd`. Establish `hroot : ∀ n, ∃ r : Ω, r ^ (g ^ D n - 1) = ((g : ℕ) : Ω)` using `fun n => IsAlgClosed.exists_pow_nat_eq _ (hNpos _ (hDpos n))`. Use `choose r hr using hroot`. Establish `hDdvd : ∀ n, D n ∣ D (n + 1)` using `fun n => Nat.factorial_dvd_factorial (by omega)`.

Establish `hdD : ∀ d, 0 < d → d ∣ D d` using `fun d hd => Nat.dvd_factorial hd (by omega)`. Establish `hmem : ∀ (σ : G E Ω) {N : ℕ} {y : Ω}, 0 < N → y ^ N = ((g : ℕ) : Ω) → σ y / y ∈ A` using `fun σ N y hN hy => tameQuot_mem A σ hN hg0 hy`. Establish `hcl : ∀ (x : Ω) (P : Ω → Prop), IsClosed {τ : G E Ω | P (τ x)}` using `fun x P => ReciprocityTheory.Gal.isClosed_setOf_apply x P`. Set `T : ℕ → Set (G E Ω)` to `fun n => (Ine (F := E) A : Set (G E Ω)) ∩ {σ | redThrough A κ (σ (r n) / r n) = ζ (D n)}`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ⟩ : (⋂ n, T n).Nonempty := by`.

Use `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `n σ ⟨hI, hv⟩`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Use `show redThrough A κ (σ (r n) / r n) = ζ (D n)`. Establish `hv' : redThrough A κ (σ (r (n + 1)) / r (n + 1)) = ζ (D (n + 1))` using `hv`.

Rewrite using `[ratio_descent hgp hgv hI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)), redThrough_pow A κ (hmem σ (hNpos _ (hDpos _)) (hr (n + 1))), hv']`. Conclude with `(hζ (D n) (hDpos n)).2 (D (n + 1)) (hDdvd n) (hDpos (n + 1))`. Introduce `n`. Establish `hc : ζ (D n) ^ (g ^ D n - 1) = 1`. Rewrite using `[← (hζ _ (hDpos n)).1]`.

Conclude with `pow_orderOf_eq_one _`. Take `⟨μ, hμ, hμc⟩` from `hL E Ω A v hA g hg κ _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) _ hc`. Take `⟨σ, hσI, hσr⟩` from `hS E Ω A v hA g hg hg2 _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) (r n) μ (hr n) hμ`. Use `⟨σ, hσI, ?_⟩` and prove the remaining obligations. Use `show redThrough A κ (σ (r n) / r n) = ζ (D n)`.

Establish `hr0 : r n ≠ 0` using `ne_zero_of_pow_eq hgp (hNpos _ (hDpos n)) (hr n)`. Rewrite using `[hσr, mul_div_cancel_right₀ _ hr0, hμc]`. Conclude with `((ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r 0) (fun t => redThrough A κ (t / r 0) = ζ (D 0)))).isCompact`. Introduce `n`. Conclude with `(ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r n) (fun t => redThrough A κ (t / r n) = ζ (D n)))`.

Simplify using `only [Set.mem_iInter] at hσ`. Establish `hσI : σ ∈ Ine (F` using `E) A := (hσ 0).1`. Establish `hσv : ∀ n, redThrough A κ (σ (r n) / r n) = ζ (D n)` using `fun n => (hσ n).2`. Use `⟨κ, σ, hσI, ⟨hσI, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `τ hτ`.

Establish `hτI : τ ∈ Ine (F` using `E) A := hτ`. Set `Z : Set (G E Ω)` to `closure (Subgroup.zpowers σ : Set (G E Ω))`. Establish `hZI : Z ⊆ Ine (F` using `E) A := closure_minimal (fun x hx => by`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hx`. Conclude with `zpow_mem hσI k) (ReciprocityTheory.Gal.isClosed_Ine A)`.

Set `U : ℕ → Set (G E Ω)` to `fun n => Z ∩ {h | redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n)}`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : (⋂ n, U n).Nonempty := by`. Use `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed U ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `n x ⟨hxZ, hx⟩`. Use `⟨hxZ, ?_⟩` and prove the remaining obligations.

Use `show redThrough A κ (x (r n) / r n) = redThrough A κ (τ (r n) / r n)`. Establish `hx' : redThrough A κ (x (r (n + 1)) / r (n + 1)) = redThrough A κ (τ (r (n + 1)) / r (n + 1))` using `hx`. Rewrite using `[ratio_descent hgp hgv (hZI hxZ) (hDpos n) (hDdvd n) (hr n) (hr (n + 1)), ratio_descent hgp hgv hτI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)), redThrough_pow A κ (hmem x (hNpos _ (hDpos _)) (hr (n + 1))), redThrough_pow A κ (hmem τ (hNpos _ (hDpos _)) (hr (n + 1))), hx']`. Introduce `n`. Establish `hN` using `hNpos _ (hDpos n)`.

Use `haveI : NeZero (g ^ D n - 1) := ⟨hN.ne'⟩`. Establish `hprim : IsPrimitiveRoot (ζ (D n)) (g ^ D n - 1)` using `(hζ _ (hDpos n)).1 ▸ IsPrimitiveRoot.orderOf _`. Establish `hc : (redThrough A κ (τ (r n) / r n)) ^ (g ^ D n - 1) = 1`. Rewrite using `[← redThrough_pow A κ (hmem τ hN (hr n)), tameQuot_pow τ hg0 (hr n), redThrough_one]`. Take `⟨j, -, hj⟩` from `hprim.eq_pow_of_pow_eq_one hc`.

Use `⟨σ ^ j, subset_closure (Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), by simp⟩), ?_⟩` and prove the remaining obligations. Use `show redThrough A κ ((σ ^ j) (r n) / r n) = _`. Rewrite using `[ratio_pow hgp hgv hσI hN (hgN _ (hDpos n)) (hr n), redThrough_pow A κ (hmem σ hN (hr n)), hσv n, hj]`. Conclude with `(isClosed_closure.inter (hcl (r 0) (fun t => redThrough A κ (t / r 0) = redThrough A κ (τ (r 0) / r 0)))).isCompact`. Introduce `n`.

Conclude with `isClosed_closure.inter (hcl (r n) (fun t => redThrough A κ (t / r n) = redThrough A κ (τ (r n) / r n)))`. Simplify using `only [Set.mem_iInter] at hh`. Establish `hhZ : h ∈ Z` using `(hh 0).1`. Establish `hhI` using `hZI hhZ`. Establish `hhv : ∀ n, redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n)` using `fun n => (hh n).2`.

Establish `hρI : h⁻¹ * τ ∈ Ine (F` using `E) A := mul_mem (inv_mem hhI) hτI`. Establish `hρW : ∀ y : Ω, y ≠ 0 → A.valuation ((h⁻¹ * τ) y / y - 1) < 1`. Use `hW E Ω A v hA g hg _ hρI ?_` and prove the remaining obligations. Introduce `d hd`. Establish `hN` using `hNpos _ (hDpos d)`.

Use `⟨r d ^ ((g ^ D d - 1) / (g ^ d - 1)), root_down (hdD d hd) (hr d), ?_⟩` and prove the remaining obligations. Apply `val_sub_one_lt_of_red κ (hmem _ (hNpos _ hd) (root_down (hdD d hd) (hr d)))` to reduce the goal to its premises. Rewrite using `[ratio_descent hgp hgv hρI hd (hdD d hd) (root_down (hdD d hd) (hr d)) (hr d), redThrough_pow A κ (hmem _ hN (hr d))]`. Establish `e1 : (h * (h⁻¹ * τ)) (r d) / r d = (h (r d) / r d) * ((h⁻¹ * τ) (r d) / r d)` using `ratio_mul hgp hgv hhI _ hN (hgN _ (hDpos d)) (hr d)`. Rewrite `e1` using `[mul_inv_cancel_left]`.

Establish `e2` using `congrArg (redThrough A κ) e1`. Rewrite `e2` using `[redThrough_mul A κ (hmem h hN (hr d)) (hmem _ hN (hr d)), ← hhv d]`. Establish `hne : redThrough A κ (h (r d) / r d) ≠ 0`. Introduce `h0`. Establish `: (redThrough A κ (h (r d) / r d)) ^ (g ^ D d - 1) = 1`.

Rewrite using `[← redThrough_pow A κ (hmem h hN (hr d)), tameQuot_pow h hg0 (hr d), redThrough_one]`. Rewrite `this` using `[h0, zero_pow hN.ne']`. Conclude with `zero_ne_one this`. Establish `e3 : redThrough A κ ((h⁻¹ * τ) (r d) / r d) = 1` using `(mul_eq_left₀ hne).1 e2.symm`. Rewrite using `[e3, one_pow]`.

Use `set C : Subgroup (G E Ω) := Subgroup.closure (insert σ {σ' : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ' y / y - 1) < 1}) with hC`. Establish `h1 : h ∈ C.topologicalClosure`. Use `closure_mono ?_ hhZ` and prove the remaining obligations. Introduce `x hx`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hx`.

Conclude with `zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : σ ∈ C) k`. Establish `h2 : h⁻¹ * τ ∈ C` using `Subgroup.subset_closure (Set.mem_insert_of_mem _ hρW)`. Establish `h3` using `C.topologicalClosure.mul_mem h1 (C.le_topologicalClosure h2)`. Rewrite `h3` using `[mul_inv_cancel_left]`. Conclude with `h3`.

Introduce `d hd y hy`. Rewrite using `[ratio_descent hgp hgv hσI hd (hdD d hd) hy (hr d), redThrough_pow A κ (hmem σ (hNpos _ (hDpos d)) (hr d)), hσv d]`. Conclude with `(hζ d hd).2 (D d) (hdD d hd) (hDpos d)`.
-/
theorem GlobalTheory.TameCoupledEx.exists_coupled_of (hK : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g)) (hL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c) (hS : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y) (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  intro E Ω _ _ _ _ _ A v hA g _ hg hg2 ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsGalois E Ω := {}
  have hgp : g.Prime := Fact.out
  have hgv : A.valuation ((g : ℕ) : Ω) < 1 := val_g_lt A v hA hg
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  obtain ⟨κ⟩ := hK E Ω A v hA g hg
  let D : ℕ → ℕ := fun n => (n + 1).factorial
  have hDpos : ∀ n, 0 < D n := fun n => Nat.factorial_pos _
  have hNpos : ∀ d, 0 < d → 0 < g ^ d - 1 := fun d hd => pow_sub_one_pos hgp hd
  have hgN : ∀ d, 0 < d → ¬ g ∣ g ^ d - 1 := fun d hd => not_dvd_pow_sub_one hgp hd
  have hroot : ∀ n, ∃ r : Ω, r ^ (g ^ D n - 1) = ((g : ℕ) : Ω) := fun n =>
    IsAlgClosed.exists_pow_nat_eq _ (hNpos _ (hDpos n))
  choose r hr using hroot
  have hDdvd : ∀ n, D n ∣ D (n + 1) := fun n => Nat.factorial_dvd_factorial (by omega)
  have hdD : ∀ d, 0 < d → d ∣ D d := fun d hd => Nat.dvd_factorial hd (by omega)
  have hmem : ∀ (σ : G E Ω) {N : ℕ} {y : Ω}, 0 < N → y ^ N = ((g : ℕ) : Ω) → σ y / y ∈ A :=
    fun σ N y hN hy => tameQuot_mem A σ hN hg0 hy
  have hcl : ∀ (x : Ω) (P : Ω → Prop), IsClosed {τ : G E Ω | P (τ x)} := fun x P =>
    ReciprocityTheory.Gal.isClosed_setOf_apply x P
  let T : ℕ → Set (G E Ω) := fun n =>
    (Ine (F := E) A : Set (G E Ω)) ∩ {σ | redThrough A κ (σ (r n) / r n) = ζ (D n)}
  obtain ⟨σ, hσ⟩ : (⋂ n, T n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_ ?_ ?_
    · rintro n σ ⟨hI, hv⟩
      refine ⟨hI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hv' : redThrough A κ (σ (r (n + 1)) / r (n + 1)) = ζ (D (n + 1)) := hv
      rw [ratio_descent hgp hgv hI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
        redThrough_pow A κ (hmem σ (hNpos _ (hDpos _)) (hr (n + 1))), hv']
      exact (hζ (D n) (hDpos n)).2 (D (n + 1)) (hDdvd n) (hDpos (n + 1))
    · intro n
      have hc : ζ (D n) ^ (g ^ D n - 1) = 1 := by
        rw [← (hζ _ (hDpos n)).1]; exact pow_orderOf_eq_one _
      obtain ⟨μ, hμ, hμc⟩ := hL E Ω A v hA g hg κ _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) _ hc
      obtain ⟨σ, hσI, hσr⟩ := hS E Ω A v hA g hg hg2 _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) (r n) μ (hr n) hμ
      refine ⟨σ, hσI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hr0 : r n ≠ 0 := ne_zero_of_pow_eq hgp (hNpos _ (hDpos n)) (hr n)
      rw [hσr, mul_div_cancel_right₀ _ hr0, hμc]
    · exact ((ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r 0) (fun t => redThrough A κ (t / r 0) = ζ (D 0)))).isCompact
    · intro n
      exact (ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r n) (fun t => redThrough A κ (t / r n) = ζ (D n)))
  simp only [Set.mem_iInter] at hσ
  have hσI : σ ∈ Ine (F := E) A := (hσ 0).1
  have hσv : ∀ n, redThrough A κ (σ (r n) / r n) = ζ (D n) := fun n => (hσ n).2
  refine ⟨κ, σ, hσI, ⟨hσI, ?_⟩, ?_⟩
  · intro τ hτ
    have hτI : τ ∈ Ine (F := E) A := hτ
    let Z : Set (G E Ω) := closure (Subgroup.zpowers σ : Set (G E Ω))
    have hZI : Z ⊆ Ine (F := E) A := closure_minimal (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx; exact zpow_mem hσI k) (ReciprocityTheory.Gal.isClosed_Ine A)
    let U : ℕ → Set (G E Ω) := fun n =>
      Z ∩ {h | redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n)}
    obtain ⟨h, hh⟩ : (⋂ n, U n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed U ?_ ?_ ?_ ?_
      · rintro n x ⟨hxZ, hx⟩
        refine ⟨hxZ, ?_⟩
        show redThrough A κ (x (r n) / r n) = redThrough A κ (τ (r n) / r n)
        have hx' : redThrough A κ (x (r (n + 1)) / r (n + 1)) = redThrough A κ (τ (r (n + 1)) / r (n + 1)) := hx
        rw [ratio_descent hgp hgv (hZI hxZ) (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          ratio_descent hgp hgv hτI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          redThrough_pow A κ (hmem x (hNpos _ (hDpos _)) (hr (n + 1))),
          redThrough_pow A κ (hmem τ (hNpos _ (hDpos _)) (hr (n + 1))), hx']
      · intro n
        have hN := hNpos _ (hDpos n)
        haveI : NeZero (g ^ D n - 1) := ⟨hN.ne'⟩
        have hprim : IsPrimitiveRoot (ζ (D n)) (g ^ D n - 1) := (hζ _ (hDpos n)).1 ▸ IsPrimitiveRoot.orderOf _
        have hc : (redThrough A κ (τ (r n) / r n)) ^ (g ^ D n - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem τ hN (hr n)), tameQuot_pow τ hg0 (hr n), redThrough_one]
        obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hc
        refine ⟨σ ^ j, subset_closure (Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), by simp⟩), ?_⟩
        show redThrough A κ ((σ ^ j) (r n) / r n) = _
        rw [ratio_pow hgp hgv hσI hN (hgN _ (hDpos n)) (hr n), redThrough_pow A κ (hmem σ hN (hr n)), hσv n, hj]
      · exact (isClosed_closure.inter (hcl (r 0)
          (fun t => redThrough A κ (t / r 0) = redThrough A κ (τ (r 0) / r 0)))).isCompact
      · intro n
        exact isClosed_closure.inter (hcl (r n)
          (fun t => redThrough A κ (t / r n) = redThrough A κ (τ (r n) / r n)))
    simp only [Set.mem_iInter] at hh
    have hhZ : h ∈ Z := (hh 0).1
    have hhI := hZI hhZ
    have hhv : ∀ n, redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n) := fun n => (hh n).2
    have hρI : h⁻¹ * τ ∈ Ine (F := E) A := mul_mem (inv_mem hhI) hτI
    have hρW : ∀ y : Ω, y ≠ 0 → A.valuation ((h⁻¹ * τ) y / y - 1) < 1 := by
      refine hW E Ω A v hA g hg _ hρI ?_
      intro d hd
      have hN := hNpos _ (hDpos d)
      refine ⟨r d ^ ((g ^ D d - 1) / (g ^ d - 1)), root_down (hdD d hd) (hr d), ?_⟩
      apply val_sub_one_lt_of_red κ (hmem _ (hNpos _ hd) (root_down (hdD d hd) (hr d)))
      rw [ratio_descent hgp hgv hρI hd (hdD d hd) (root_down (hdD d hd) (hr d)) (hr d),
        redThrough_pow A κ (hmem _ hN (hr d))]
      have e1 : (h * (h⁻¹ * τ)) (r d) / r d = (h (r d) / r d) * ((h⁻¹ * τ) (r d) / r d) :=
        ratio_mul hgp hgv hhI _ hN (hgN _ (hDpos d)) (hr d)
      rw [mul_inv_cancel_left] at e1
      have e2 := congrArg (redThrough A κ) e1
      rw [redThrough_mul A κ (hmem h hN (hr d)) (hmem _ hN (hr d)), ← hhv d] at e2
      have hne : redThrough A κ (h (r d) / r d) ≠ 0 := by
        intro h0
        have : (redThrough A κ (h (r d) / r d)) ^ (g ^ D d - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem h hN (hr d)), tameQuot_pow h hg0 (hr d), redThrough_one]
        rw [h0, zero_pow hN.ne'] at this
        exact zero_ne_one this
      have e3 : redThrough A κ ((h⁻¹ * τ) (r d) / r d) = 1 :=
        (mul_eq_left₀ hne).1 e2.symm
      rw [e3, one_pow]
    set C : Subgroup (G E Ω) :=
      Subgroup.closure (insert σ {σ' : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ' y / y - 1) < 1}) with hC
    have h1 : h ∈ C.topologicalClosure := by
      refine closure_mono ?_ hhZ
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : σ ∈ C) k
    have h2 : h⁻¹ * τ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ hρW)
    have h3 := C.topologicalClosure.mul_mem h1 (C.le_topologicalClosure h2)
    rw [mul_inv_cancel_left] at h3
    exact h3
  · intro d hd y hy
    rw [ratio_descent hgp hgv hσI hd (hdD d hd) hy (hr d),
      redThrough_pow A κ (hmem σ (hNpos _ (hDpos d)) (hr d)), hσv d]
    exact (hζ d hd).2 (D d) (hdD d hd) (hDpos d)

/- English proof (translation)
The claim follows from `GlobalTheory.TameCoupledEx.exists_coupled_of GlobalTheory.T.residue_field_over_place_alg_closure GlobalTheory.T.exists_rootOfUnity_lift_from_residueField GlobalTheory.T.tame_kummer_inertia_surjective GlobalTheory.T.inertia_wild_of_trivial_tame_characters`.
-/
theorem GlobalTheory.TameCoupledEx.exists_coupled_tame_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ :=
  GlobalTheory.TameCoupledEx.exists_coupled_of GlobalTheory.T.residue_field_over_place_alg_closure GlobalTheory.T.exists_rootOfUnity_lift_from_residueField GlobalTheory.T.tame_kummer_inertia_surjective GlobalTheory.T.inertia_wild_of_trivial_tame_characters
