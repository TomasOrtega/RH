import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ

namespace UpperTheory.V.Z.Inf

namespace ArchimedeanTermRegrouping

/- English proof (translation)
Use `haveI := v.isMaximal`. Use `haveI : v.asIdeal.LiesOver (v.under (𝓞 K)).asIdeal := ⟨rfl⟩`. Use `haveI := (v.under (𝓞 K)).isMaximal`. Establish `h1` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal (v.under (𝓞 K)).ne_bot`. Establish `h2` using `Ideal.inertiaDeg'_pos (p := (v.under (𝓞 K)).asIdeal) (P := v.asIdeal)`.

Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1 h2.ne')`.
-/
private theorem term_pos (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (v : HeightOneSpectrum (𝓞 E)) :
    1 ≤ (v.under (𝓞 K)).asIdeal.ramificationIdx' v.asIdeal * (v.under (𝓞 K)).asIdeal.inertiaDeg' v.asIdeal := by
  haveI := v.isMaximal
  haveI : v.asIdeal.LiesOver (v.under (𝓞 K)).asIdeal := ⟨rfl⟩
  haveI := (v.under (𝓞 K)).isMaximal
  have h1 := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal (v.under (𝓞 K)).ne_bot
  have h2 := Ideal.inertiaDeg'_pos (p := (v.under (𝓞 K)).asIdeal) (P := v.asIdeal)
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1 h2.ne')

/- English proof (translation)
Use `haveI := (v.under (𝓞 K)).isMaximal`. Rewrite using `[IsDedekindDomain.mem_primesOverFinset_iff (v.under (𝓞 K)).ne_bot]`. Conclude with `⟨v.isPrime, ⟨rfl⟩⟩`.
-/
private theorem mem_fin (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (v : HeightOneSpectrum (𝓞 E)) :
    v.asIdeal ∈ IsDedekindDomain.primesOverFinset (v.under (𝓞 K)).asIdeal (𝓞 E) := by
  haveI := (v.under (𝓞 K)).isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff (v.under (𝓞 K)).ne_bot]
  exact ⟨v.isPrime, ⟨rfl⟩⟩

/- English proof (translation)
Use `haveI := p.isMaximal`. Rewrite using `[Ideal.sum_ramification_inertia (𝓞 E) K E p.ne_bot, hE]`.
-/
private theorem sum_eq (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (hE : Module.finrank K E = 2) (p : HeightOneSpectrum (𝓞 K)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E), p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P = 2 := by
  haveI := p.isMaximal
  rw [Ideal.sum_ramification_inertia (𝓞 E) K E p.ne_bot, hE]

/- English proof (translation)
Use `haveI := v.isMaximal`. Take `⟨P, hPm, hP⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hP.over, h]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 E))`. Use `⟨⟨P, hPm.isPrime, hne⟩, ?_⟩` and prove the remaining obligations. Use `ext1`. Rewrite using `[HeightOneSpectrum.under_asIdeal]`.

Conclude with `hP.over.symm`.
-/
private theorem exists_above (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 E))
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hP.over.symm

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hvw : v.asIdeal ≠ w.asIdeal` using `fun e => h.1 (HeightOneSpectrum.ext e)`. Establish `hvw' : v.asIdeal ≠ w'.asIdeal` using `fun e => h.2 (HeightOneSpectrum.ext e)`. Establish `hww' : w'.asIdeal ≠ w.asIdeal` using `fun e => hne (HeightOneSpectrum.ext e)`.

Use `set p := w.under (𝓞 K)`. Establish `hsub : ({v.asIdeal, w'.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 E))) ⊆ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E)`. Introduce `P hP`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hP`. Break down `hP with rfl | rfl | rfl` into its components or cases.

Use `mem_fin K E v` as an intermediate fact. Rewrite `this` using `[hv]`. Then use the resulting hypothesis. Use `mem_fin K E w'` as an intermediate fact. Rewrite `this` using `[hw']`. Then use the resulting hypothesis. Conclude with `mem_fin K E w`.

Establish `hle` using `Finset.sum_le_sum_of_subset (f := fun P => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub`. Rewrite `hle` using `[sum_eq K E hE p]`. Rewrite `hle` using `[Finset.sum_insert (by simp [hvw, hvw']), Finset.sum_insert (by simp [hww']), Finset.sum_singleton]`. Establish `a` using `term_pos K E v`. Establish `b` using `term_pos K E w'`.

Establish `c : 1 ≤ p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal` using `term_pos K E w`. Rewrite `a` using `[hv]`. Rewrite `b` using `[hw']`. Use linear arithmetic over natural numbers and integers.
-/
private theorem fiber_split (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (hE : Module.finrank K E = 2)
    (w w' v : HeightOneSpectrum (𝓞 E)) (hw' : w'.under (𝓞 K) = w.under (𝓞 K))
    (hv : v.under (𝓞 K) = w.under (𝓞 K)) (hne : w' ≠ w) : v = w ∨ v = w' := by
  by_contra h
  push_neg at h
  have hvw : v.asIdeal ≠ w.asIdeal := fun e => h.1 (HeightOneSpectrum.ext e)
  have hvw' : v.asIdeal ≠ w'.asIdeal := fun e => h.2 (HeightOneSpectrum.ext e)
  have hww' : w'.asIdeal ≠ w.asIdeal := fun e => hne (HeightOneSpectrum.ext e)
  set p := w.under (𝓞 K)
  have hsub : ({v.asIdeal, w'.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 E))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · have := mem_fin K E v; rwa [hv] at this
    · have := mem_fin K E w'; rwa [hw'] at this
    · exact mem_fin K E w
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub
  rw [sum_eq K E hE p] at hle
  rw [Finset.sum_insert (by simp [hvw, hvw']), Finset.sum_insert (by simp [hww']), Finset.sum_singleton] at hle
  have a := term_pos K E v
  have b := term_pos K E w'
  have c : 1 ≤ p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal := term_pos K E w
  rw [hv] at a
  rw [hw'] at b
  omega

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hvw : v.asIdeal ≠ w.asIdeal` using `fun e => h (HeightOneSpectrum.ext e)`. Use `set p := w.under (𝓞 K)`. Use `haveI := w.isMaximal`. Use `haveI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩`.

Establish `hf` using `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot`. Rewrite `hf` using `[hN]`. Establish `hf2 : p.asIdeal.inertiaDeg' w.asIdeal = 2` using `(Nat.pow_right_injective (GlobalTheory.HenQ.Regroup.two_le_absNorm p) hf).symm`. Establish `hsub : ({v.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 E))) ⊆ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E)`. Introduce `P hP`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hP`. Break down `hP with rfl | rfl` into its components or cases. Use `mem_fin K E v` as an intermediate fact. Rewrite `this` using `[hv]`. Then use the resulting hypothesis. Conclude with `mem_fin K E w`.

Establish `hle` using `Finset.sum_le_sum_of_subset (f := fun P => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub`. Rewrite `hle` using `[sum_eq K E hE p]`. Rewrite `hle` using `[Finset.sum_insert (by simp [hvw]), Finset.sum_singleton, hf2]`. Establish `a` using `term_pos K E v`. Rewrite `a` using `[hv]`.

Establish `he` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal p.ne_bot`. Establish `: 1 ≤ p.asIdeal.ramificationIdx' w.asIdeal` using `Nat.one_le_iff_ne_zero.mpr he`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem fiber_inert (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (hE : Module.finrank K E = 2)
    (w v : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2)
    (hv : v.under (𝓞 K) = w.under (𝓞 K)) : v = w := by
  by_contra h
  have hvw : v.asIdeal ≠ w.asIdeal := fun e => h (HeightOneSpectrum.ext e)
  set p := w.under (𝓞 K)
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot
  rw [hN] at hf
  have hf2 : p.asIdeal.inertiaDeg' w.asIdeal = 2 :=
    (Nat.pow_right_injective (GlobalTheory.HenQ.Regroup.two_le_absNorm p) hf).symm
  have hsub : ({v.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 E))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · have := mem_fin K E v; rwa [hv] at this
    · exact mem_fin K E w
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub
  rw [sum_eq K E hE p] at hle
  rw [Finset.sum_insert (by simp [hvw]), Finset.sum_singleton, hf2] at hle
  have a := term_pos K E v
  rw [hv] at a
  have he := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal p.ne_bot
  have : 1 ≤ p.asIdeal.ramificationIdx' w.asIdeal := Nat.one_le_iff_ne_zero.mpr he
  nlinarith

/- English proof (translation)
Establish `hE'` using `(GlobalTheory.HenQ.Regroup.multipliable_E E SE BE c₀ r hBE s hs).hasProd`. Set `e : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 K) = p.1}) ≃ {w : HeightOneSpectrum (𝓞 E) // w ∉ SE}` to `{ toFun := fun x => ⟨x.2.1, by rw [hSE, x.2.2]; exact x.1.2⟩ invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hSE w.1).not.mp w.2⟩, ⟨w.1, rfl⟩⟩ left_inv := by rintro ⟨⟨p, hp⟩, ⟨w, hw⟩⟩; simp only at hw; subst hw; rfl right_inv := by intro w; rfl }`. Establish `h2` using `(e.hasProd_iff).mpr hE'`. Use `(h2.sigma (g := fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} => ((BK p.1).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) ?_).tprod_eq` and prove the remaining obligations. Introduce and unpack `⟨p, hp⟩`.

Take `⟨w, rfl⟩` from `exists_above K E p`. Establish `hwS : w ∉ SE` using `by rw [hSE]; exact hp`. Break down `hloc w hwS with ⟨hN, w', hne, hw', hBK⟩ | ⟨hN, B', hBE', hBK⟩` into its components or cases. Establish `hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal`. Break down `hloc w' (by rw [hSE, hw']; exact hp) with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases.

Rewrite using `[h, hw']`. Conclude with `absurd (fiber_inert K E hE w' w h hw'.symm) (Ne.symm hne)`. Set `a : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}` to `⟨w, rfl⟩`. Set `a' : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}` to `⟨w', hw'⟩`. Establish `hall : ∀ c : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}, c ∈ ({a, a'} : Finset _)`.

Introduce `c`. Break down `fiber_split K E hE w w' c.1 hw' c.2 hne with h | h` into its components or cases. Simplify using `[Subtype.ext_iff, h, a]`. Simplify using `[Subtype.ext_iff, h, a']`. Establish `hne' : a ≠ a'` using `fun h => hne (congrArg Subtype.val h).symm`.

Use `hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := ({a, a'} : Finset _)) (fun c hc => absurd (hall c) hc) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.prod_pair hne']`. Simplify using `only [e, Equiv.coe_fn_mk, a, a', Function.comp_apply]`. Rewrite using `[hBK, Multiset.map_add, Multiset.prod_add, hN, hN']`. Set `a : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}` to `⟨w, rfl⟩`.

Establish `hall : ∀ c : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}, c ∈ ({a} : Finset _)`. Introduce `c`. Use `fiber_inert K E hE w c.1 hN c.2` as an intermediate fact. Simplify using `[Subtype.ext_iff, this, a]`. Use `hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := ({a} : Finset _)) (fun c hc => absurd (hall c) hc) using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Finset.prod_singleton]`. Simplify using `only [e, Equiv.coe_fn_mk, a, Function.comp_apply]`. Establish `hX : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) = (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℂ) ^ (-s)) ^ 2`. Rewrite using `[hN, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, pow_two]`. Rewrite using `[hX, hBE', hBK, GlobalTheory.HenQ.Regroup.fac_inert]`.
-/
private theorem core (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (hE : Module.finrank K E = 2)
    (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SE : Set (HeightOneSpectrum (𝓞 E)))
    (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (BE : HeightOneSpectrum (𝓞 E) → Multiset ℂ) (c₀ : ℝ) (r : ℕ)
    (hSE : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 K) ∈ MainNotions)
    (hBE : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE → Multiset.card (BE w) ≤ r ∧
      ∀ b ∈ BE w, ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 E), w' ≠ w ∧
        w'.under (𝓞 K) = w.under (𝓞 K) ∧ BK (w.under (𝓞 K)) = BE w + BE w') ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧ ∃ B' : Multiset ℂ,
        BE w = B'.map (· ^ 2) ∧ BK (w.under (𝓞 K)) = B' + B'.map Neg.neg))
    (s : ℂ) (hs : c₀ + 1 < s.re) : eulerL K BK MainNotions s = eulerL E BE SE s := by
  classical
  have hE' := (GlobalTheory.HenQ.Regroup.multipliable_E E SE BE c₀ r hBE s hs).hasProd
  let e : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions},
      {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 K) = p.1}) ≃ {w : HeightOneSpectrum (𝓞 E) // w ∉ SE} :=
    { toFun := fun x => ⟨x.2.1, by rw [hSE, x.2.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hSE w.1).not.mp w.2⟩, ⟨w.1, rfl⟩⟩
      left_inv := by rintro ⟨⟨p, hp⟩, ⟨w, hw⟩⟩; simp only at hw; subst hw; rfl
      right_inv := by intro w; rfl }
  have h2 := (e.hasProd_iff).mpr hE'
  refine (h2.sigma (g := fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} =>
    ((BK p.1).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w, rfl⟩ := exists_above K E p
  have hwS : w ∉ SE := by rw [hSE]; exact hp
  rcases hloc w hwS with ⟨hN, w', hne, hw', hBK⟩ | ⟨hN, B', hBE', hBK⟩
  · have hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal := by
      rcases hloc w' (by rw [hSE, hw']; exact hp) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h, hw']
      · exact absurd (fiber_inert K E hE w' w h hw'.symm) (Ne.symm hne)
    let a : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)} := ⟨w, rfl⟩
    let a' : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)} := ⟨w', hw'⟩
    have hall : ∀ c : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}, c ∈ ({a, a'} : Finset _) := by
      intro c
      rcases fiber_split K E hE w w' c.1 hw' c.2 hne with h | h
      · simp [Subtype.ext_iff, h, a]
      · simp [Subtype.ext_iff, h, a']
    have hne' : a ≠ a' := fun h => hne (congrArg Subtype.val h).symm
    convert hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := ({a, a'} : Finset _)) (fun c hc => absurd (hall c) hc) using 1
    rw [Finset.prod_pair hne']
    dsimp only [e, Equiv.coe_fn_mk, a, a', Function.comp_apply]
    rw [hBK, Multiset.map_add, Multiset.prod_add, hN, hN']
  · let a : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)} := ⟨w, rfl⟩
    have hall : ∀ c : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 K) = w.under (𝓞 K)}, c ∈ ({a} : Finset _) := by
      intro c
      have := fiber_inert K E hE w c.1 hN c.2
      simp [Subtype.ext_iff, this, a]
    convert hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := ({a} : Finset _)) (fun c hc => absurd (hall c) hc) using 1
    rw [Finset.prod_singleton]
    dsimp only [e, Equiv.coe_fn_mk, a, Function.comp_apply]
    have hX : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) =
        (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℂ) ^ (-s)) ^ 2 := by
      rw [hN, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, pow_two]
    rw [hX, hBE', hBK, GlobalTheory.HenQ.Regroup.fac_inert]

end ArchimedeanTermRegrouping

open ArchimedeanTermRegrouping in
/- English proof (translation)
Introduce `K E _ _ _ _ _ hE MainNotions SE BK BE c₀ r hSE _hBK hBE hloc`. Use `⟨c₀ + 1, fun s => ⟨fun hs => core K E hE MainNotions SE BK BE c₀ r hSE (fun w hw => ⟨(hBE w hw).1, fun b hb => ((hBE w hw).2 b hb).1⟩) hloc s hs, fun hs => ?_⟩⟩` and prove the remaining obligations. Unfold `eulerLd`. Apply `core K E hE MainNotions SE (fun p => (BK p).map (·⁻¹)) (fun w => (BE w).map (·⁻¹)) c₀ r hSE` to reduce the goal to its premises. Introduce `w hw`.

Use `⟨by rw [Multiset.card_map]; exact (hBE w hw).1, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hb`. Conclude with `((hBE w hw).2 a ha).2`. Introduce `w hw`. Break down `hloc w hw with ⟨hN, w', hne, hw', hBK⟩ | ⟨hN, B', hBE', hBK⟩` into its components or cases.

Conclude with `Or.inl ⟨hN, w', hne, hw', by simp only [hBK, Multiset.map_add]⟩`. Use `Or.inr ⟨hN, B'.map (·⁻¹), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hBE', Multiset.map_map]`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `b _`.

Simplify using `[inv_pow]`. Simplify using `only [hBK, Multiset.map_add, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `b _`.

Simplify using `[inv_neg]`. Simplify using `only [Complex.sub_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem regroup : Regroup := by
  intro K E _ _ _ _ _ hE MainNotions SE BK BE c₀ r hSE _hBK hBE hloc
  refine ⟨c₀ + 1, fun s => ⟨fun hs => core K E hE MainNotions SE BK BE c₀ r hSE
    (fun w hw => ⟨(hBE w hw).1, fun b hb => ((hBE w hw).2 b hb).1⟩) hloc s hs, fun hs => ?_⟩⟩
  unfold eulerLd
  apply core K E hE MainNotions SE (fun p => (BK p).map (·⁻¹)) (fun w => (BE w).map (·⁻¹)) c₀ r hSE
  · intro w hw
    refine ⟨by rw [Multiset.card_map]; exact (hBE w hw).1, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    exact ((hBE w hw).2 a ha).2
  · intro w hw
    rcases hloc w hw with ⟨hN, w', hne, hw', hBK⟩ | ⟨hN, B', hBE', hBK⟩
    · exact Or.inl ⟨hN, w', hne, hw', by simp only [hBK, Multiset.map_add]⟩
    · refine Or.inr ⟨hN, B'.map (·⁻¹), ?_, ?_⟩
      · simp only [hBE', Multiset.map_map]
        apply Multiset.map_congr rfl
        intro b _
        simp [inv_pow]
      · simp only [hBK, Multiset.map_add, Multiset.map_map]
        congr 1
        apply Multiset.map_congr rfl
        intro b _
        simp [inv_neg]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith

end UpperTheory.V.Z.Inf
