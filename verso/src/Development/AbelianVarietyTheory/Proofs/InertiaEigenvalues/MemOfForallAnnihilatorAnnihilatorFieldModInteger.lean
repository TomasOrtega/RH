import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DoubleAnnihilator

section
variable {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]

local notation "QE" => LL ⧸ LinearMap.range (Algebra.linearMap O LL)

/- English proof (translation)
Rewrite using `[Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]`. Simplify using `[Algebra.linearMap_apply]`.
-/
theorem mk_eq_zero_iff (z : LL) :
    (Submodule.Quotient.mk z : QE) = 0 ↔ ∃ b : O, algebraMap O LL b = z := by
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  simp [Algebra.linearMap_apply]

/- English proof (translation)
Introduce `I g`. Take `⟨a, rfl⟩` from `(IsPrincipalIdealRing.principal I).principal`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Use `⟨0, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hx0 : x = 0` using `by simpa using hx`. Substitute `hx0` using the available equality. Establish `: (⟨0, hx⟩ : Ideal.span ({0} : Set O)) = 0` using `rfl`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `haL : algebraMap O LL a ≠ 0`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[h, map_zero]`.

Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ (g ⟨a, Ideal.mem_span_singleton_self a⟩)`. Use `⟨LinearMap.toSpanSingleton O _ (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ * z)), fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Establish `: (⟨r * a, hx⟩ : Ideal.span ({a} : Set O)) = r • ⟨a, Ideal.mem_span_singleton_self a⟩` using `rfl`. Rewrite using `[this, map_smul, ← hz, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]`.

Use `congr 1`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem baer [IsDomain O] [IsPrincipalIdealRing O] (hinj : Function.Injective (algebraMap O LL)) :
    Module.Baer O QE := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    have : (⟨0, hx⟩ : Ideal.span ({0} : Set O)) = 0 := rfl
    rw [this]; simp
  · have haL : algebraMap O LL a ≠ 0 := by
      intro h; apply ha; apply hinj; rw [h, map_zero]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (g ⟨a, Ideal.mem_span_singleton_self a⟩)
    refine ⟨LinearMap.toSpanSingleton O _ (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ * z)),
      fun x hx => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have : (⟨r * a, hx⟩ : Ideal.span ({a} : Set O)) = r • ⟨a, Ideal.mem_span_singleton_self a⟩ := rfl
    rw [this, map_smul, ← hz, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    field_simp

/- English proof (translation)
Use `set w : LL := (algebraMap O LL ℓ ^ n)⁻¹ with hw_def`. Establish `hw : algebraMap O LL ℓ ^ n * w = 1` using `mul_inv_cancel₀ (pow_ne_zero _ hℓ)`. Use `set u : QE := Submodule.Quotient.mk w with hu_def`. Establish `key : ∀ e : QE, ℓ ^ n • e = 0 → ∃ b : O, e = b • u`. Introduce `e he`.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ e`. Rewrite `he` using `[← Submodule.Quotient.mk_smul, mk_eq_zero_iff]`. Take `⟨b, hb⟩` from `he`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hu_def, ← Submodule.Quotient.mk_smul]`.

Use `congr 1`. Rewrite using `[Algebra.smul_def, hb, Algebra.smul_def, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hu : ℓ ^ n • u = 0`. Rewrite using `[hu_def, ← Submodule.Quotient.mk_smul, mk_eq_zero_iff]`.

Conclude with `⟨1, by rw [map_one, Algebra.smul_def, map_pow, hw]⟩`. Take `⟨c, hc⟩` from `key (h u) (by rw [← map_smul, hu, map_zero])`. Use `⟨c, fun e he => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `key e he`. Rewrite using `[map_smul, hc, smul_comm]`.
-/
theorem endo_on_torsion (ℓ : O) (hℓ : algebraMap O LL ℓ ≠ 0) (h : QE →ₗ[O] QE) (n : ℕ) :
    ∃ c : O, ∀ e : QE, ℓ ^ n • e = 0 → h e = c • e := by
  set w : LL := (algebraMap O LL ℓ ^ n)⁻¹ with hw_def
  have hw : algebraMap O LL ℓ ^ n * w = 1 := mul_inv_cancel₀ (pow_ne_zero _ hℓ)
  set u : QE := Submodule.Quotient.mk w with hu_def
  have key : ∀ e : QE, ℓ ^ n • e = 0 → ∃ b : O, e = b • u := by
    intro e he
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ e
    rw [← Submodule.Quotient.mk_smul, mk_eq_zero_iff] at he
    obtain ⟨b, hb⟩ := he
    refine ⟨b, ?_⟩
    rw [hu_def, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, hb, Algebra.smul_def, map_pow]
    calc z = (algebraMap O LL ℓ ^ n * w) * z := by rw [hw, one_mul]
      _ = _ := by ring
  have hu : ℓ ^ n • u = 0 := by
    rw [hu_def, ← Submodule.Quotient.mk_smul, mk_eq_zero_iff]
    exact ⟨1, by rw [map_one, Algebra.smul_def, map_pow, hw]⟩
  obtain ⟨c, hc⟩ := key (h u) (by rw [← map_smul, hu, map_zero])
  refine ⟨c, fun e he => ?_⟩
  obtain ⟨b, rfl⟩ := key e he
  rw [map_smul, hc, smul_comm]

/- English proof (translation)
Take `⟨⟨x, y⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors O) z`. Establish `hy : (y : O) ≠ 0` using `nonZeroDivisors.ne_zero y.2`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Take `⟨e, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ`.

Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Apply `hℓ` to reduce the goal to its premises. Rewrite using `[hv, pow_zero, mul_one]`. Conclude with `v.isUnit`.

Establish `hdvd : (y : O) ∣ ℓ ^ n`. Rewrite using `[hu, hv, mul_pow, Units.mul_left_dvd]`. Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Rewrite using `[← pow_mul]`. Conclude with `pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))`.

Take `⟨t, ht⟩` from `hdvd`. Use `⟨n, t * x, ?_⟩` and prove the remaining obligations. Establish `hspec` using `IsLocalization.mk'_spec LL x y`. Rewrite using `[← map_pow, ht, map_mul, map_mul, ← hspec]`. Simplify using `only`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pow_mul_mem [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (ℓ : O) (hℓ0 : ℓ ≠ 0) (hℓ : ¬ IsUnit ℓ) (z : LL) :
    ∃ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap O LL ℓ ^ k * z := by
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) z
  have hy : (y : O) ≠ 0 := nonZeroDivisors.ne_zero y.2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
  have he : e ≠ 0 := by
    rintro rfl; apply hℓ; rw [hv, pow_zero, mul_one]; exact v.isUnit
  have hdvd : (y : O) ∣ ℓ ^ n := by
    rw [hu, hv, mul_pow, Units.mul_left_dvd]
    apply Dvd.dvd.mul_left
    rw [← pow_mul]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨n, t * x, ?_⟩
  have hspec := IsLocalization.mk'_spec LL x y
  rw [← map_pow, ht, map_mul, map_mul, ← hspec]
  simp only
  ring

/- English proof (translation)
Introduce `hu`. Establish `htop : Ideal.span {ℓ} = ⊤` using `Ideal.span_singleton_eq_top.mpr hu`. Rewrite `h` using `[htop]`. Use `h.toIsHausdorff.haus (1 : O) (fun n => by` as an intermediate fact. Rewrite using `[Ideal.top_pow, Submodule.top_smul]`.

Conclude with `SModEq.top)`. Conclude with `one_ne_zero this`.
-/
theorem not_isUnit_of_adicComplete [Nontrivial O] (ℓ : O) (h : IsAdicComplete (Ideal.span {ℓ}) O) :
    ¬ IsUnit ℓ := by
  intro hu
  have htop : Ideal.span {ℓ} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
  rw [htop] at h
  have := h.toIsHausdorff.haus (1 : O) (fun n => by
    rw [Ideal.top_pow, Submodule.top_smul]; exact SModEq.top)
  exact one_ne_zero this

end

end GlobalTheory.DoubleAnnihilator

namespace GlobalTheory

open GlobalTheory.DoubleAnnihilator in

/- English proof (translation)
Introduce `l _ LL _ _ _ O _ _ hO M N _ _ _ _ _ β S hker c hc`. Take `⟨-, hRc, -, hAd⟩` from `GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO`. Take `⟨⟨hD, hDVR, hFr⟩, -, -, hTR, hOpen⟩` from `hO`. Use `haveI := hD`. Use `haveI := hDVR`.

Use `haveI := hFr`. Use `haveI := hTR`. Establish `hinj : Function.Injective (algebraMap O LL)` using `IsFractionRing.injective O LL`. Use `set ℓ : O := ((l : ℕ) : O) with hℓ_def`. Establish `hℓLL : algebraMap O LL ℓ ≠ 0`.

Rewrite using `[hℓ_def, map_natCast]`. Introduce `h`. Establish `h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0` using `by rw [map_natCast]; exact h`. Rewrite `h'` using `[map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective]`. Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast h')`.

Establish `hℓ0 : ℓ ≠ 0` using `fun h => hℓLL (by rw [h, map_zero])`. Establish `hℓu : ¬ IsUnit ℓ` using `not_isUnit_of_adicComplete ℓ hAd`. Use `set R : Set LL := Set.range (algebraMap O LL) with hR_def`. Establish `hRcl : IsClosed R`. Establish `h1` using `AddSubgroup.isClosed_of_isOpen ((algebraMap O LL).toAddMonoidHom.range) (by simpa using hOpen)`.

Simplify using `using h1`. Take `⟨r, v, hv⟩` from `Module.Finite.exists_fin (R := O) (M := M)`. Establish `hspan : ∀ d : M, ∃ a : Fin r → O, ∑ i, a i • v i = d` using `fun d => (Submodule.mem_span_range_iff_exists_fun O).mp (hv ▸ Submodule.mem_top)`. Establish `hlift : ∀ (s : N) (i : Fin r), ∃ z : LL, (Submodule.Quotient.mk z : LL ⧸ LinearMap.range (Algebra.linearMap O LL)) = β (v i) s` using `fun s i => Submodule.Quotient.mk_surjective _ _`. Use `choose y hy using hlift`.

Establish `hexp : ∀ (a : Fin r → O) (s : N), β (∑ i, a i • v i) s = Submodule.Quotient.mk (∑ i, algebraMap O LL (a i) * y s i)`. Introduce `a s`. Rewrite using `[← Submodule.mkQ_apply, map_sum, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, ← hy, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def]`.

Set `L : N → (Fin r → LL) → LL` to `fun s x => ∑ i, x i * y s i`. Establish `hLc : ∀ s, Continuous (L s)` using `fun s => by`. Simplify using `only [L]`. Use `fun_prop`. Set `K : Set (Fin r → LL)` to `Set.univ.pi (fun _ => R)`.

Establish `hKc : IsCompact K` using `isCompact_univ_pi (fun _ => hRc)`. Set `U : Set (Fin r → LL)` to `{x | L c x ∈ R}`. Establish `hUo : IsOpen U` using `hOpen.preimage (hLc c)`. Set `T : S → Set (Fin r → LL)` to `fun s => {x | L s.1 x ∈ R}`. Establish `hTcl : ∀ s, IsClosed (T s)` using `fun s => hRcl.preimage (hLc s.1)`.

Establish `hempty : (K \ U) ∩ ⋂ s, T s = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_diff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨⟨hK, hU⟩, hT⟩`. Establish `hK' : ∀ i, ∃ a : O, algebraMap O LL a = x i` using `fun i => hK i (Set.mem_univ i)`.

Use `choose a ha using hK'`. Establish `hx : x = fun i => algebraMap O LL (a i)` using `funext fun i => (ha i).symm`. Substitute `hx` using the available equality. Apply `hU` to reduce the goal to its premises. Establish `h1` using `hc (∑ i, a i • v i) (fun s hs => by`.

Rewrite using `[hexp, mk_eq_zero_iff]`. Conclude with `hT ⟨s, hs⟩)`. Rewrite `h1` using `[hexp, mk_eq_zero_iff]`. Conclude with `h1`. Take `⟨F, hF⟩` from `(hKc.diff hUo).elim_finite_subfamily_closed T hTcl hempty`.

Establish `hfin : ∀ d : M, (∀ s ∈ F, β d s.1 = 0) → β d c = 0`. Introduce `d hd`. Take `⟨a, rfl⟩` from `hspan d`. Assume the negation of the conclusion as `hne`. Establish `hx : (fun i => algebraMap O LL (a i)) ∈ (K \ U) ∩ ⋂ s ∈ F, T s`.

Use `⟨⟨fun i _ => ⟨a i, rfl⟩, fun hU => hne ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hexp, mk_eq_zero_iff]`. Conclude with `hU`. Simplify using `only [Set.mem_iInter]`. Introduce `s hs`.

Establish `h2` using `hd s hs`. Rewrite `h2` using `[hexp, mk_eq_zero_iff]`. Conclude with `h2`. Rewrite `hx` using `[hF]`. Conclude with `hx`.

Set `τ : M →ₗ[O] (F → LL ⧸ LinearMap.range (Algebra.linearMap O LL))` to `LinearMap.pi (fun s : F => β.flip s.1.1)`. Establish `hτ : ∀ d (s : F), τ d s = β d s.1.1` using `fun d s => rfl`. Establish `hker' : LinearMap.ker τ ≤ LinearMap.ker (β.flip c)`. Introduce `d hd`. Rewrite `hd`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[LinearMap.flip_apply]`. Apply `hfin d` to reduce the goal to its premises. Introduce `s hs`. Establish `h3` using `congr_fun hd ⟨s, hs⟩`. Rewrite `h3` using `[hτ]`.

Conclude with `h3`. Take `⟨G, hG⟩` from `(baer hinj).extension_property ((LinearMap.ker τ).liftQ τ le_rfl) (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)) ((LinearMap.ker τ).liftQ (β.flip c) hker')`. Establish `hφG : ∀ d, β d c = G (τ d)` using `fun d => by`. Establish `h4` using `LinearMap.congr_fun hG (Submodule.Quotient.mk d)`. Simplify using `only [LinearMap.comp_apply, Submodule.liftQ_apply, LinearMap.flip_apply] at h4`.

Conclude with `h4.symm`. Establish `htor : ∀ s : N, ∃ n : ℕ, ∀ d : M, ℓ ^ n • β d s = 0`. Introduce `s`. Establish `h5 : ∀ i : Fin r, ∃ k : ℕ, ∀ m, k ≤ m → ℓ ^ m • β (v i) s = 0`. Introduce `i`.

Take `⟨k, b, hb⟩` from `exists_pow_mul_mem ℓ hℓ0 hℓu (y s i)`. Use `⟨k, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, ← Submodule.Quotient.mk_smul, mk_eq_zero_iff]`. Use `⟨ℓ ^ (m - k) * b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hb, Algebra.smul_def, map_pow, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]`.

Use `choose k hk using h5`. Use `⟨Finset.univ.sup k, fun d => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hspan d`. Rewrite using `[map_sum, LinearMap.sum_apply, Finset.smul_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, LinearMap.smul_apply, smul_comm, hk i _ (Finset.le_sup (Finset.mem_univ i)), smul_zero]`. Use `choose n hn using htor`. Establish `hcoef : ∀ s : F, ∃ cs : O, ∀ e : LL ⧸ LinearMap.range (Algebra.linearMap O LL), ℓ ^ (n s.1.1) • e = 0 → G (Pi.single s e) = cs • e` using `fun s => by`. Take `⟨cs, hcs⟩` from `endo_on_torsion ℓ hℓLL (G ∘ₗ LinearMap.single O (fun _ : F => LL ⧸ LinearMap.range (Algebra.linearMap O LL)) s) (n s.1.1)`. Conclude with `⟨cs, fun e he => by simpa using hcs e he⟩`.

Use `choose cs hcs using hcoef`. Establish `hkey : ∀ d, β d c = β d (∑ s : F, cs s • s.1.1)`. Introduce `d`. Rewrite using `[hφG d, ← Finset.univ_sum_single (τ d), map_sum, map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hτ, hcs s _ (hn _ d), map_smul]`. Establish `hdiff : c - ∑ s : F, cs s • s.1.1 ∈ S` using `hker _ (fun d => by rw [map_sub, sub_eq_zero]; exact hkey d)`. Establish `hsum : ∑ s : F, cs s • s.1.1 ∈ S` using `Submodule.sum_mem _ fun s _ => S.smul_mem _ s.1.2`. Simplify using `using S.add_mem hdiff hsum`.
-/
theorem mem_of_forall_annihilator_annihilator :
    ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
      (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
      ∀ (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O M]
        (β : M →ₗ[O] N →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL))) (S : Submodule O N),
        (∀ c, (∀ d, β d c = 0) → c ∈ S) →
          ∀ c, (∀ d, (∀ s ∈ S, β d s = 0) → β d c = 0) → c ∈ S := by
  intro l _ LL _ _ _ O _ _ hO M N _ _ _ _ _ β S hker c hc
  classical
  obtain ⟨-, hRc, -, hAd⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, hTR, hOpen⟩ := hO
  haveI := hD; haveI := hDVR; haveI := hFr; haveI := hTR
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  set ℓ : O := ((l : ℕ) : O) with hℓ_def
  have hℓLL : algebraMap O LL ℓ ≠ 0 := by
    rw [hℓ_def, map_natCast]
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have hℓ0 : ℓ ≠ 0 := fun h => hℓLL (by rw [h, map_zero])
  have hℓu : ¬ IsUnit ℓ := not_isUnit_of_adicComplete ℓ hAd
  set R : Set LL := Set.range (algebraMap O LL) with hR_def
  have hRcl : IsClosed R := by
    have h1 := AddSubgroup.isClosed_of_isOpen ((algebraMap O LL).toAddMonoidHom.range)
      (by simpa using hOpen)
    simpa using h1
  obtain ⟨r, v, hv⟩ := Module.Finite.exists_fin (R := O) (M := M)
  have hspan : ∀ d : M, ∃ a : Fin r → O, ∑ i, a i • v i = d := fun d =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hv ▸ Submodule.mem_top)
  have hlift : ∀ (s : N) (i : Fin r), ∃ z : LL,
      (Submodule.Quotient.mk z : LL ⧸ LinearMap.range (Algebra.linearMap O LL)) = β (v i) s :=
    fun s i => Submodule.Quotient.mk_surjective _ _
  choose y hy using hlift
  have hexp : ∀ (a : Fin r → O) (s : N), β (∑ i, a i • v i) s =
      Submodule.Quotient.mk (∑ i, algebraMap O LL (a i) * y s i) := by
    intro a s
    rw [← Submodule.mkQ_apply, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, ← hy, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Algebra.smul_def]

  let L : N → (Fin r → LL) → LL := fun s x => ∑ i, x i * y s i
  have hLc : ∀ s, Continuous (L s) := fun s => by
    simp only [L]; fun_prop
  let K : Set (Fin r → LL) := Set.univ.pi (fun _ => R)
  have hKc : IsCompact K := isCompact_univ_pi (fun _ => hRc)
  let U : Set (Fin r → LL) := {x | L c x ∈ R}
  have hUo : IsOpen U := hOpen.preimage (hLc c)
  let T : S → Set (Fin r → LL) := fun s => {x | L s.1 x ∈ R}
  have hTcl : ∀ s, IsClosed (T s) := fun s => hRcl.preimage (hLc s.1)
  have hempty : (K \ U) ∩ ⋂ s, T s = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hK, hU⟩, hT⟩
    have hK' : ∀ i, ∃ a : O, algebraMap O LL a = x i := fun i => hK i (Set.mem_univ i)
    choose a ha using hK'
    have hx : x = fun i => algebraMap O LL (a i) := funext fun i => (ha i).symm
    subst hx
    apply hU
    have h1 := hc (∑ i, a i • v i) (fun s hs => by
      rw [hexp, mk_eq_zero_iff]; exact hT ⟨s, hs⟩)
    rw [hexp, mk_eq_zero_iff] at h1
    exact h1
  obtain ⟨F, hF⟩ := (hKc.diff hUo).elim_finite_subfamily_closed T hTcl hempty
  have hfin : ∀ d : M, (∀ s ∈ F, β d s.1 = 0) → β d c = 0 := by
    intro d hd
    obtain ⟨a, rfl⟩ := hspan d
    by_contra hne
    have hx : (fun i => algebraMap O LL (a i)) ∈ (K \ U) ∩ ⋂ s ∈ F, T s := by
      refine ⟨⟨fun i _ => ⟨a i, rfl⟩, fun hU => hne ?_⟩, ?_⟩
      · rw [hexp, mk_eq_zero_iff]; exact hU
      · simp only [Set.mem_iInter]
        intro s hs
        have h2 := hd s hs
        rw [hexp, mk_eq_zero_iff] at h2
        exact h2
    rw [hF] at hx
    exact hx

  let τ : M →ₗ[O] (F → LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    LinearMap.pi (fun s : F => β.flip s.1.1)
  have hτ : ∀ d (s : F), τ d s = β d s.1.1 := fun d s => rfl
  have hker' : LinearMap.ker τ ≤ LinearMap.ker (β.flip c) := by
    intro d hd
    rw [LinearMap.mem_ker] at hd ⊢
    rw [LinearMap.flip_apply]
    apply hfin d
    intro s hs
    have h3 := congr_fun hd ⟨s, hs⟩
    rw [hτ] at h3
    exact h3
  obtain ⟨G, hG⟩ := (baer hinj).extension_property ((LinearMap.ker τ).liftQ τ le_rfl)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
    ((LinearMap.ker τ).liftQ (β.flip c) hker')
  have hφG : ∀ d, β d c = G (τ d) := fun d => by
    have h4 := LinearMap.congr_fun hG (Submodule.Quotient.mk d)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, LinearMap.flip_apply] at h4
    exact h4.symm

  have htor : ∀ s : N, ∃ n : ℕ, ∀ d : M, ℓ ^ n • β d s = 0 := by
    intro s
    have h5 : ∀ i : Fin r, ∃ k : ℕ, ∀ m, k ≤ m → ℓ ^ m • β (v i) s = 0 := by
      intro i
      obtain ⟨k, b, hb⟩ := exists_pow_mul_mem ℓ hℓ0 hℓu (y s i)
      refine ⟨k, fun m hm => ?_⟩
      rw [← hy, ← Submodule.Quotient.mk_smul, mk_eq_zero_iff]
      refine ⟨ℓ ^ (m - k) * b, ?_⟩
      rw [map_mul, hb, Algebra.smul_def, map_pow, map_pow, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel hm]
    choose k hk using h5
    refine ⟨Finset.univ.sup k, fun d => ?_⟩
    obtain ⟨a, rfl⟩ := hspan d
    rw [map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_comm, hk i _ (Finset.le_sup (Finset.mem_univ i)),
      smul_zero]
  choose n hn using htor
  have hcoef : ∀ s : F, ∃ cs : O, ∀ e : LL ⧸ LinearMap.range (Algebra.linearMap O LL),
      ℓ ^ (n s.1.1) • e = 0 → G (Pi.single s e) = cs • e := fun s => by
    obtain ⟨cs, hcs⟩ := endo_on_torsion ℓ hℓLL
      (G ∘ₗ LinearMap.single O (fun _ : F => LL ⧸ LinearMap.range (Algebra.linearMap O LL)) s)
      (n s.1.1)
    exact ⟨cs, fun e he => by simpa using hcs e he⟩
  choose cs hcs using hcoef
  have hkey : ∀ d, β d c = β d (∑ s : F, cs s • s.1.1) := by
    intro d
    rw [hφG d, ← Finset.univ_sum_single (τ d), map_sum, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hτ, hcs s _ (hn _ d), map_smul]
  have hdiff : c - ∑ s : F, cs s • s.1.1 ∈ S :=
    hker _ (fun d => by rw [map_sub, sub_eq_zero]; exact hkey d)
  have hsum : ∑ s : F, cs s • s.1.1 ∈ S := Submodule.sum_mem _ fun s _ => S.smul_mem _ s.1.2
  simpa using S.add_mem hdiff hsum

end GlobalTheory
