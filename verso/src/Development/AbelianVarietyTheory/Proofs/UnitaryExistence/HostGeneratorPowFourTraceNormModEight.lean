import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open NumberField Matrix in
open scoped nonZeroDivisors in

/- English proof (translation)
Set `K` to `FractionRing O`. Set `N` to `LocalizedModule O⁰ M`. Set `f : M →ₗ[O] N` to `LocalizedModule.mkLinearMap O⁰ M`. Set `T` to `Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)`. Establish `hdvd : ∀ s ∈ O⁰, ∃ n : ℤ, n ≠ 0 ∧ s ∣ (n : O)` using `fun s hs => by`.

Take `⟨r, hr, hd⟩` from `IsAlgebraic.exists_nonzero_dvd (R := ℤ) (Algebra.IsIntegral.isIntegral (R := ℤ) s).isAlgebraic hs`. Conclude with `⟨r, hr, by simpa using hd⟩`. Establish `hT : ∀ t ∈ T, t ≠ 0`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Simplify using `using nonZeroDivisors.ne_zero hn`.

Use `haveI hTK : IsLocalization T K := { map_units := fun t => IsLocalization.map_units K (M := O⁰) ⟨t, mem_nonZeroDivisors_of_ne_zero (hT t t.2)⟩ surj := fun z => by`. Take `⟨⟨a, s⟩, hz⟩` from `IsLocalization.surj O⁰ z`. Take `⟨n, hn, t, ht⟩` from `hdvd s s.2`. Use `⟨⟨a * t, ⟨(n : O), n, mem_nonZeroDivisors_of_ne_zero hn, by simp⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [ht, map_mul] at hz ⊢`.

Rewrite using `[← hz]`. Expand and normalize the polynomial expressions, which then agree. Use `exists_of_eq := fun {x y} h => ⟨1, by simpa using IsFractionRing.injective O K h⟩ }`. Use `haveI : IsLocalizedModule T f := by`. Rewrite using `[isLocalizedModule_iff_isBaseChange T K, ← isLocalizedModule_iff_isBaseChange O⁰ K]`.

Use `infer_instance`. Use `haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f`. Establish `h1 : Module.finrank ℤ N = Module.finrank ℤ M` using `IsLocalizedModule.finrank_eq _ (f.restrictScalars ℤ) le_rfl`. Establish `h2 : Module.finrank O N = Module.finrank O M` using `IsLocalizedModule.finrank_eq O⁰ f le_rfl`. Establish `h3 : Module.finrank K N = Module.finrank O N` using `IsLocalization.finrank_eq K O⁰ le_rfl`.

Use `letI : Module ℚ N := Module.compHom N (algebraMap ℚ K)`. Use `haveI : IsScalarTower ℚ K N := ⟨fun q k n => by`. Express the relevant statement in the definitionally equal form `(q • k) • n = (algebraMap ℚ K q) • (k • n)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Establish `h4 : Module.finrank ℚ N = Module.finrank ℤ N` using `IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl`.

Establish `h5 : Module.finrank ℚ K * Module.finrank K N = Module.finrank ℚ N` using `Module.finrank_mul_finrank ℚ K N`. Establish `h6 : Module.finrank ℚ K = Module.finrank ℤ K` using `IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl`. Establish `h7 : Module.finrank ℤ O * Module.finrank O K = Module.finrank ℤ K`. Use `Module.finrank_mul_finrank' (R := ℤ) (S := O) K using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | exact Subsingleton.elim _ _`.

Establish `h8 : Module.finrank K K = Module.finrank O K` using `IsLocalization.finrank_eq K O⁰ le_rfl`. Rewrite `h8` using `[Module.finrank_self]`. Rewrite using `[← h1, ← h4, ← h5, h6, ← h7, ← h8, h3, h2, mul_one]`.
-/
theorem _root_.GlobalTheory.finrank_int_eq_mul_of_finite {O M : Type*} [CommRing O] [IsDomain O] [CharZero O]
    [Module.Free ℤ O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  classical
  let K := FractionRing O
  let N := LocalizedModule O⁰ M
  let f : M →ₗ[O] N := LocalizedModule.mkLinearMap O⁰ M
  let T := Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)
  have hdvd : ∀ s ∈ O⁰, ∃ n : ℤ, n ≠ 0 ∧ s ∣ (n : O) := fun s hs => by
    obtain ⟨r, hr, hd⟩ := IsAlgebraic.exists_nonzero_dvd (R := ℤ)
      (Algebra.IsIntegral.isIntegral (R := ℤ) s).isAlgebraic hs
    exact ⟨r, hr, by simpa using hd⟩
  have hT : ∀ t ∈ T, t ≠ 0 := by
    rintro _ ⟨n, hn, rfl⟩
    simpa using nonZeroDivisors.ne_zero hn
  haveI hTK : IsLocalization T K :=
    { map_units := fun t => IsLocalization.map_units K (M := O⁰)
        ⟨t, mem_nonZeroDivisors_of_ne_zero (hT t t.2)⟩
      surj := fun z => by
        obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj O⁰ z
        obtain ⟨n, hn, t, ht⟩ := hdvd s s.2
        refine ⟨⟨a * t, ⟨(n : O), n, mem_nonZeroDivisors_of_ne_zero hn, by simp⟩⟩, ?_⟩
        simp only [ht, map_mul] at hz ⊢
        rw [← hz]; ring
      exists_of_eq := fun {x y} h => ⟨1, by simpa using IsFractionRing.injective O K h⟩ }
  haveI : IsLocalizedModule T f := by
    rw [isLocalizedModule_iff_isBaseChange T K, ← isLocalizedModule_iff_isBaseChange O⁰ K]
    infer_instance
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars _ f
  have h1 : Module.finrank ℤ N = Module.finrank ℤ M :=
    IsLocalizedModule.finrank_eq _ (f.restrictScalars ℤ) le_rfl
  have h2 : Module.finrank O N = Module.finrank O M := IsLocalizedModule.finrank_eq O⁰ f le_rfl
  have h3 : Module.finrank K N = Module.finrank O N := IsLocalization.finrank_eq K O⁰ le_rfl
  letI : Module ℚ N := Module.compHom N (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K N := ⟨fun q k n => by
    change (q • k) • n = (algebraMap ℚ K q) • (k • n)
    rw [Algebra.smul_def, mul_smul]⟩
  have h4 : Module.finrank ℚ N = Module.finrank ℤ N :=
    IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h5 : Module.finrank ℚ K * Module.finrank K N = Module.finrank ℚ N :=
    Module.finrank_mul_finrank ℚ K N
  have h6 : Module.finrank ℚ K = Module.finrank ℤ K :=
    IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h7 : Module.finrank ℤ O * Module.finrank O K = Module.finrank ℤ K := by
    convert Module.finrank_mul_finrank' (R := ℤ) (S := O) K using 2
    all_goals first | rfl | exact Subsingleton.elim _ _
  have h8 : Module.finrank K K = Module.finrank O K := IsLocalization.finrank_eq K O⁰ le_rfl
  rw [Module.finrank_self] at h8
  rw [← h1, ← h4, ← h5, h6, ← h7, ← h8, h3, h2, mul_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Use `haveI := D.fin`. Use `haveI := D.proj`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.IsTorsionFree (𝓞 E) D.La := inferInstance`. Use `haveI : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans (𝓞 E)`.

Conclude with `Module.free_of_finite_type_torsion_free'`.
-/
theorem _root_.GlobalTheory.datum_free_int {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) : Module.Free ℤ D.La := by
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree (𝓞 E) D.La := inferInstance
  haveI : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans (𝓞 E)
  exact Module.free_of_finite_type_torsion_free'

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Use `haveI := D.fin`. Rewrite using `[_root_.GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]`. Establish `h1` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `h2 : NumberField.InfinitePlace.nrRealPlaces E = 0` using `nrRealPlaces_eq_zero_iff.mpr inferInstance`. Rewrite `h1` using `[h2, zero_add]`.

Rewrite using `[← h1]`. Establish `h3 : 2 * NumberField.InfinitePlace.nrComplexPlaces E / 2 = NumberField.InfinitePlace.nrComplexPlaces E` using `by omega`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.datum_finrank_int {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) :
    Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  haveI := D.fin
  rw [_root_.GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  have h2 : NumberField.InfinitePlace.nrRealPlaces E = 0 :=
    nrRealPlaces_eq_zero_iff.mpr inferInstance
  rw [h2, zero_add] at h1
  rw [← h1]
  have h3 : 2 * NumberField.InfinitePlace.nrComplexPlaces E / 2 =
      NumberField.InfinitePlace.nrComplexPlaces E := by omega
  rw [h3]; ring

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hd : (H.d : 𝓞 E) = 16 * ((H.d / 16 : ℕ) : 𝓞 E) + 7`. Use `Nat.div_add_mod H.d 16` as an intermediate fact. Rewrite `this` using `[H.d_mod]`. Conclude with `this.symm` after adjusting the coercions. Establish `h4 : (4 : 𝓞 E) * (H.w0 ^ 2 - (H.w0 - 2 * ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E))) = 0`.

Use `push_cast`. Take the linear combination `(2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hd`. Break down `mul_eq_zero.mp h4 with h | h` into its components or cases. Conclude with `absurd h (by norm_num)`. Conclude with `sub_eq_zero.mp h`.
-/
private lemma w0_sq_eq_w0_sub_two_mul (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 ^ 2 = H.w0 - 2 * ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E) := by
  have hd : (H.d : 𝓞 E) = 16 * ((H.d / 16 : ℕ) : 𝓞 E) + 7 := by
    have := Nat.div_add_mod H.d 16
    rw [H.d_mod] at this
    exact_mod_cast this.symm
  have h4 : (4 : 𝓞 E) * (H.w0 ^ 2 - (H.w0 - 2 * ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E))) = 0 := by
    push_cast
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hd
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · exact sub_eq_zero.mp h

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hsq : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Simplify using `using congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hconj : (starRingEnd ℂ) (φ (H.rt : E)) = -φ (H.rt : E)` using `by set z := φ (H.rt : E) with hz`.

Establish `hre` using `congrArg Complex.re hsq`. Establish `him` using `congrArg Complex.im hsq`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`. Establish `hre0 : z.re = 0`. Break down `mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h` into its components or cases.

Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `h`. Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[sq_nonneg z.re]`. Evaluate the numerical expressions using `at h`.

Apply the tactic sequence `apply Complex.ext <;> simp [hre0]`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[H.bar_eq, NumberField.IsCMField.complexEmbedding_complexConj, hconj]`. Simplify using the standard rewrite rules.
-/
private lemma host_bar_rt_eq_neg (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    simpa using congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hconj : (starRingEnd ℂ) (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E) with hz
    have hre := congrArg Complex.re hsq
    have him := congrArg Complex.im hsq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
    have hre0 : z.re = 0 := by
      rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · rw [h] at hre; nlinarith [sq_nonneg z.re]
      · norm_num at h
    apply Complex.ext <;> simp [hre0]
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, NumberField.IsCMField.complexEmbedding_complexConj, hconj]
  simp

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `h` using `congrArg H.bar H.two_weight_eq_one_add_root`. Rewrite `h` using `[map_mul, map_add, map_one, host_bar_rt_eq_neg, map_ofNat]`. Establish `h2 : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0`. Take the linear combination `h + H.two_weight_eq_one_add_root`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `absurd h3 two_ne_zero`. Conclude with `sub_eq_zero.mp h3`.
-/
private lemma host_bar_w0 (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, host_bar_rt_eq_neg, map_ofNat] at h
  have h2 : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0 := by
    linear_combination h + H.two_weight_eq_one_add_root
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact sub_eq_zero.mp h3

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `E _ _ _ H D g hg`. Use `haveI := D.fin`. Use `haveI : Module.Free ℤ D.La := _root_.GlobalTheory.datum_free_int D`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `set w := H.w0 with hw`.

Use `set m : 𝓞 E := ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E) with hm`. Establish `hsq : w ^ 2 = w - 2 * m` using `w0_sq_eq_w0_sub_two_mul H`. Establish `hA : w ^ 4 + (1 - w) ^ 4 = 1 + 8 * (m ^ 2 - m)`. Take the linear combination `(2 * w ^ 2 - 2 * w + 4 - 4 * m) * hsq`. Establish `hB : w ^ 4 * (1 - w) ^ 4 = 8 * (2 * m ^ 4)`.

Establish `h : w * (1 - w) = 2 * m` using `by linear_combination -hsq`. Rewrite using `[← mul_pow, h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : w ^ 4 * w ^ 4 = w ^ 4 + 8 * ((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4)`. Take the linear combination `w ^ 4 * hA - hB`.

Establish `hbar4 : H.bar (w ^ 4) = (1 - w) ^ 4` using `by rw [map_pow, hw, host_bar_w0]`. Establish `hbar4' : H.bar ((1 - w) ^ 4) = w ^ 4`. Rewrite using `[map_pow, map_sub, map_one, hw, host_bar_w0]`. Expand and normalize the polynomial expressions, which then agree. Establish `h8 : ∀ u : D.La, (8 : 𝓞 E) • u = (8 : ℤ) • u` using `fun u => by`.

Simplify using `using Int.cast_smul_eq_zsmul (𝓞 E) (8 : ℤ) u`. Establish `hn8 : ∀ u : D.La, (8 : ℕ) • u = (8 : 𝓞 E) • u` using `fun u => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Evaluate the numerical expressions. Establish `hE8 : ∀ u v : D.La, D.EF ((8 : 𝓞 E) • u) v = 8 * D.EF u v` using `fun u v => by`.

Rewrite using `[h8, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Establish `hE8' : ∀ u v : D.La, D.EF u ((8 : 𝓞 E) • v) = 8 * D.EF u v` using `fun u v => by`. Rewrite using `[h8, map_smul, smul_eq_mul]`. Set `P : Submodule ℤ D.La` to `{ carrier := {x | ∃ e, w ^ 4 • x = x + (8 : 𝓞 E) • e} add_mem' := by`. Introduce and unpack `x y ⟨a, ha⟩ ⟨b, hb⟩`.

Conclude with `⟨a + b, by rw [smul_add, ha, hb, smul_add]; abel⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨a, ha⟩`. Conclude with `⟨c • a, by rw [smul_comm (w ^ 4) c x, ha, smul_add, smul_comm c (8 : 𝓞 E) a]⟩ }`.

Set `Q : Submodule ℤ D.La` to `{ carrier := {x | ∃ e, w ^ 4 • x = (8 : 𝓞 E) • e} add_mem' := by`. Introduce and unpack `x y ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨a + b, by rw [smul_add, ha, hb, smul_add]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c x ⟨a, ha⟩`. Conclude with `⟨c • a, by rw [smul_comm (w ^ 4) c x, ha, smul_comm c (8 : 𝓞 E) a]⟩ }`. Establish `hP8 : ∀ x : D.La, ((8 : ℕ) : ℤ) • x ∈ P` using `fun x => ⟨w ^ 4 • x - x, by`. Rewrite using `[show ((8 : ℕ) : ℤ) = 8 by norm_num, ← h8, smul_comm (w ^ 4) (8 : 𝓞 E) x, smul_sub]`. Use the proof step `abel⟩`.

Establish `hQ8 : ∀ x : D.La, ((8 : ℕ) : ℤ) • x ∈ Q` using `fun x => ⟨w ^ 4 • x, by rw [show ((8 : ℕ) : ℤ) = 8 by norm_num, ← h8, smul_comm (w ^ 4) (8 : 𝓞 E) x]⟩`. Establish `hPiso : ∀ x ∈ P, ∀ y ∈ P, (8 : ℤ) ∣ D.EF x y`. Introduce and unpack `x ⟨a, ha⟩ y ⟨b, hb⟩`. Establish `hy : (1 - w) ^ 4 • y = (8 : 𝓞 E) • ((2 * m ^ 4) • y - (1 - w) ^ 4 • b)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hb, add_sub_cancel_right]`. Use `_ = ((1 - w) ^ 4 * w ^ 4) • y - ((1 - w) ^ 4 * 8) • b := by`. Rewrite using `[smul_sub, smul_smul, smul_smul]`. Use `_ = (8 * (2 * m ^ 4)) • y - (8 * (1 - w) ^ 4) • b := by`. Rewrite using `[mul_comm ((1 - w) ^ 4) (w ^ 4), hB, mul_comm ((1 - w) ^ 4) 8]`.

Use `_ = (8 : 𝓞 E) • ((2 * m ^ 4) • y - (1 - w) ^ 4 • b) := by`. Simplify using `only [smul_sub, mul_smul]`. Establish `hx : D.EF x y = D.EF (w ^ 4 • x) y - 8 * D.EF a y`. Rewrite using `[ha, map_add, LinearMap.add_apply, hE8]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hx, D.adj, hbar4, hy, hE8']`. Conclude with `(dvd_mul_right _ _).sub (dvd_mul_right _ _)`. Establish `hQiso : ∀ x ∈ Q, ∀ y ∈ Q, (8 : ℤ) ∣ D.EF x y`. Introduce and unpack `x ⟨a, ha⟩ y ⟨b, hb⟩`. Establish `hx : x = (8 : 𝓞 E) • (a - (m ^ 2 - m) • x) + (1 - w) ^ 4 • x`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Take the linear combination `-hA`. Use `_ = w ^ 4 • x + (1 - w) ^ 4 • x - (8 * (m ^ 2 - m)) • x := by`. Rewrite using `[sub_smul, add_smul]`.

Use `_ = (8 : 𝓞 E) • (a - (m ^ 2 - m) • x) + (1 - w) ^ 4 • x := by`. Rewrite using `[ha, mul_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hxy : D.EF x y = 8 * D.EF (a - (m ^ 2 - m) • x) y + D.EF ((1 - w) ^ 4 • x) y` using `by conv_lhs => rw [hx]`. Rewrite using `[map_add, LinearMap.add_apply, hE8]`.

Rewrite using `[hxy, D.adj, hbar4', hb, hE8']`. Conclude with `(dvd_mul_right _ _).add (dvd_mul_right _ _)`. Establish `hsup : P ⊔ Q = ⊤`. Use `eq_top_iff.mpr fun x _ => Submodule.mem_sup.mpr ⟨w ^ 4 • x, ?_, x - w ^ 4 • x, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) • x, by`.

Rewrite using `[smul_smul, hC, add_smul, mul_smul]⟩`. Conclude with `⟨-(((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) • x), by`. Rewrite using `[smul_sub, smul_smul, hC, add_smul, mul_smul, smul_neg]`. Use the proof step `abel⟩`. Normalize the expressions using the abelian group laws.

Establish `halt : (-D.EF).IsAlt` using `fun x => by simp [D.alt]`. Establish `hfin : Module.finrank ℤ D.La = 2 * g`. Rewrite using `[hg]`. Conclude with `_root_.GlobalTheory.datum_finrank_int D`. Take `⟨c, hc, hcP, hcQ⟩` from `_root_.GlobalTheory.exists_isSymplecticBasis_adapted_dvd halt (_root_.GlobalTheory.bijective_neg_bilinForm D.unimod) hfin (N := 8) (by norm_num) hP8 hQ8 (fun x hx y hy => by simpa using hPiso x hx y hy) (fun x hx y hy => by simpa using hQiso x hx y hy) hsup`.

Establish `hrepr : ∀ a j, c.repr (c.equivFun.symm a) j = a j` using `fun a j => by`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `hsingle : ∀ i, c.equivFun.symm (Pi.single i 1) = c i` using `fun i => by simp`. Use `⟨c.equivFun.symm, fun a b => ?_, fun k => ?_, fun k => ?_⟩` and prove the remaining obligations. Establish `h` using `hc.apply_eq_sum halt (c.equivFun.symm a) (c.equivFun.symm b)`.

Simplify using `only [hrepr, LinearMap.neg_apply] at h`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd`. Rewrite using `[← h, neg_neg]`. Rewrite using `[hsingle]`. Take `⟨e, he⟩` from `(hcP (c (Sum.inl k))).mpr fun i => by simp`.

Conclude with `⟨e, by rw [he, hn8]⟩`. Rewrite using `[hsingle]`. Take `⟨e, he⟩` from `(hcQ (c (Sum.inr k))).mpr fun i => by simp`. Conclude with `⟨e, by rw [he, hn8]⟩`.
-/
theorem _root_.GlobalTheory.exists_symplectic_basis_adapted_mod_eight :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ),
      g = Module.finrank ℚ E / 2 * (D.p + D.q) → ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La),
        (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
        (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧
        (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) := by
  intro E _ _ _ H D g hg
  haveI := D.fin
  haveI : Module.Free ℤ D.La := _root_.GlobalTheory.datum_free_int D
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  set w := H.w0 with hw
  set m : 𝓞 E := ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E) with hm
  have hsq : w ^ 2 = w - 2 * m := w0_sq_eq_w0_sub_two_mul H
  have hA : w ^ 4 + (1 - w) ^ 4 = 1 + 8 * (m ^ 2 - m) := by
    linear_combination (2 * w ^ 2 - 2 * w + 4 - 4 * m) * hsq
  have hB : w ^ 4 * (1 - w) ^ 4 = 8 * (2 * m ^ 4) := by
    have h : w * (1 - w) = 2 * m := by linear_combination -hsq
    rw [← mul_pow, h]; ring
  have hC : w ^ 4 * w ^ 4 = w ^ 4 + 8 * ((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) := by
    linear_combination w ^ 4 * hA - hB
  have hbar4 : H.bar (w ^ 4) = (1 - w) ^ 4 := by rw [map_pow, hw, host_bar_w0]
  have hbar4' : H.bar ((1 - w) ^ 4) = w ^ 4 := by
    rw [map_pow, map_sub, map_one, hw, host_bar_w0]; ring
  have h8 : ∀ u : D.La, (8 : 𝓞 E) • u = (8 : ℤ) • u := fun u => by
    simpa using Int.cast_smul_eq_zsmul (𝓞 E) (8 : ℤ) u
  have hn8 : ∀ u : D.La, (8 : ℕ) • u = (8 : 𝓞 E) • u := fun u => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; norm_num
  have hE8 : ∀ u v : D.La, D.EF ((8 : 𝓞 E) • u) v = 8 * D.EF u v := fun u v => by
    rw [h8, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hE8' : ∀ u v : D.La, D.EF u ((8 : 𝓞 E) • v) = 8 * D.EF u v := fun u v => by
    rw [h8, map_smul, smul_eq_mul]
  let P : Submodule ℤ D.La :=
    { carrier := {x | ∃ e, w ^ 4 • x = x + (8 : 𝓞 E) • e}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [smul_add, ha, hb, smul_add]; abel⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨c • a, by rw [smul_comm (w ^ 4) c x, ha, smul_add, smul_comm c (8 : 𝓞 E) a]⟩ }
  let Q : Submodule ℤ D.La :=
    { carrier := {x | ∃ e, w ^ 4 • x = (8 : 𝓞 E) • e}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [smul_add, ha, hb, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨c • a, by rw [smul_comm (w ^ 4) c x, ha, smul_comm c (8 : 𝓞 E) a]⟩ }
  have hP8 : ∀ x : D.La, ((8 : ℕ) : ℤ) • x ∈ P := fun x =>
    ⟨w ^ 4 • x - x, by
      rw [show ((8 : ℕ) : ℤ) = 8 by norm_num, ← h8, smul_comm (w ^ 4) (8 : 𝓞 E) x, smul_sub]
      abel⟩
  have hQ8 : ∀ x : D.La, ((8 : ℕ) : ℤ) • x ∈ Q := fun x =>
    ⟨w ^ 4 • x, by rw [show ((8 : ℕ) : ℤ) = 8 by norm_num, ← h8, smul_comm (w ^ 4) (8 : 𝓞 E) x]⟩
  have hPiso : ∀ x ∈ P, ∀ y ∈ P, (8 : ℤ) ∣ D.EF x y := by
    rintro x ⟨a, ha⟩ y ⟨b, hb⟩
    have hy : (1 - w) ^ 4 • y = (8 : 𝓞 E) • ((2 * m ^ 4) • y - (1 - w) ^ 4 • b) := by
      calc (1 - w) ^ 4 • y = (1 - w) ^ 4 • (w ^ 4 • y - (8 : 𝓞 E) • b) := by
            rw [hb, add_sub_cancel_right]
        _ = ((1 - w) ^ 4 * w ^ 4) • y - ((1 - w) ^ 4 * 8) • b := by
            rw [smul_sub, smul_smul, smul_smul]
        _ = (8 * (2 * m ^ 4)) • y - (8 * (1 - w) ^ 4) • b := by
            rw [mul_comm ((1 - w) ^ 4) (w ^ 4), hB, mul_comm ((1 - w) ^ 4) 8]
        _ = (8 : 𝓞 E) • ((2 * m ^ 4) • y - (1 - w) ^ 4 • b) := by
            simp only [smul_sub, mul_smul]
    have hx : D.EF x y = D.EF (w ^ 4 • x) y - 8 * D.EF a y := by
      rw [ha, map_add, LinearMap.add_apply, hE8]; ring
    rw [hx, D.adj, hbar4, hy, hE8']
    exact (dvd_mul_right _ _).sub (dvd_mul_right _ _)
  have hQiso : ∀ x ∈ Q, ∀ y ∈ Q, (8 : ℤ) ∣ D.EF x y := by
    rintro x ⟨a, ha⟩ y ⟨b, hb⟩
    have hx : x = (8 : 𝓞 E) • (a - (m ^ 2 - m) • x) + (1 - w) ^ 4 • x := by
      calc x = (1 : 𝓞 E) • x := (one_smul _ _).symm
        _ = (w ^ 4 + (1 - w) ^ 4 - 8 * (m ^ 2 - m)) • x := by
            congr 1; linear_combination -hA
        _ = w ^ 4 • x + (1 - w) ^ 4 • x - (8 * (m ^ 2 - m)) • x := by
            rw [sub_smul, add_smul]
        _ = (8 : 𝓞 E) • (a - (m ^ 2 - m) • x) + (1 - w) ^ 4 • x := by
            rw [ha, mul_smul, smul_sub]; abel
    have hxy : D.EF x y = 8 * D.EF (a - (m ^ 2 - m) • x) y + D.EF ((1 - w) ^ 4 • x) y := by
      conv_lhs => rw [hx]
      rw [map_add, LinearMap.add_apply, hE8]
    rw [hxy, D.adj, hbar4', hb, hE8']
    exact (dvd_mul_right _ _).add (dvd_mul_right _ _)
  have hsup : P ⊔ Q = ⊤ := by
    refine eq_top_iff.mpr fun x _ => Submodule.mem_sup.mpr ⟨w ^ 4 • x, ?_, x - w ^ 4 • x, ?_, ?_⟩
    · exact ⟨((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) • x, by
        rw [smul_smul, hC, add_smul, mul_smul]⟩
    · exact ⟨-(((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) • x), by
        rw [smul_sub, smul_smul, hC, add_smul, mul_smul, smul_neg]; abel⟩
    · abel
  have halt : (-D.EF).IsAlt := fun x => by simp [D.alt]
  have hfin : Module.finrank ℤ D.La = 2 * g := by
    rw [hg]; exact _root_.GlobalTheory.datum_finrank_int D
  obtain ⟨c, hc, hcP, hcQ⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_adapted_dvd halt
    (_root_.GlobalTheory.bijective_neg_bilinForm D.unimod) hfin (N := 8) (by norm_num) hP8 hQ8
    (fun x hx y hy => by simpa using hPiso x hx y hy)
    (fun x hx y hy => by simpa using hQiso x hx y hy) hsup
  have hrepr : ∀ a j, c.repr (c.equivFun.symm a) j = a j := fun a j => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hsingle : ∀ i, c.equivFun.symm (Pi.single i 1) = c i := fun i => by simp
  refine ⟨c.equivFun.symm, fun a b => ?_, fun k => ?_, fun k => ?_⟩
  · have h := hc.apply_eq_sum halt (c.equivFun.symm a) (c.equivFun.symm b)
    simp only [hrepr, LinearMap.neg_apply] at h
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
    rw [← h, neg_neg]
  · rw [hsingle]
    obtain ⟨e, he⟩ := (hcP (c (Sum.inl k))).mpr fun i => by simp
    exact ⟨e, by rw [he, hn8]⟩
  · rw [hsingle]
    obtain ⟨e, he⟩ := (hcQ (c (Sum.inr k))).mpr fun i => by simp
    exact ⟨e, by rw [he, hn8]⟩

end GlobalTheory
