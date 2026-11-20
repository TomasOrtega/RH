import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ
open GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.Gam

namespace BaseChangeLocalFactorRegrouping

/- English proof (translation)
Establish `h1` using `congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod h hf (rfl : y ^ f = y ^ f))`. Rewrite `h1` using `[Polynomial.eval_prod]`. Simplify using `using h1.symm`.
-/
private theorem one_period {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) :
    ∏ j ∈ Finset.range f, (1 - ζ ^ j * y) = 1 - y ^ f := by
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod h hf (rfl : y ^ f = y ^ f))
  rw [Polynomial.eval_prod] at h1
  simpa using h1.symm

/- English proof (translation)
Proceed by induction on `g with`. Consider the case `zero => simp`. Consider the case `succ g ih`. Rewrite using `[Nat.succ_mul, Finset.prod_range_add, ih, pow_succ, ← one_period h hf y]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_add, mul_comm g f, pow_mul, h.pow_eq_one, one_pow, one_mul]`.
-/
private theorem periods {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) (g : ℕ) :
    ∏ j ∈ Finset.range (g * f), (1 - ζ ^ j * y) = (1 - y ^ f) ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ, ← one_period h hf y]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pow_add, mul_comm g f, pow_mul, h.pow_eq_one, one_pow, one_mul]

/- English proof (translation)
Proceed by induction on `B using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a B ih`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons]`. Rewrite using `[Finset.prod_mul_distrib, ih, mul_pow, Finset.prod_inv_distrib, ← mul_pow a x, inv_pow, ← periods h hf]`.

Use `congr 2`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fac_eq {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (g : ℕ) (B : Multiset ℂ) (x : ℂ) :
    ∏ j ∈ Finset.range (g * f), ((B.map (· * ζ ^ j)).map fun b => (1 - b * x)⁻¹).prod =
      (((B.map (· ^ f)).map fun b => (1 - b * x ^ f)⁻¹).prod) ^ g := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a B ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Finset.prod_mul_distrib, ih, mul_pow, Finset.prod_inv_distrib, ← mul_pow a x, inv_pow, ← periods h hf]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Proceed by induction on `f with`. Consider the case `zero => simp`. Consider the case `succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]`.
-/
private theorem cast_pow_cpow (N f : ℕ) (z : ℂ) : (((N ^ f : ℕ)) : ℂ) ^ z = (((N : ℕ) : ℂ) ^ z) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
The claim follows from `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal p.asIdeal p.isPrime p.ne_bot`.
-/
private theorem norm_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm p.asIdeal ^ fdeg w :=
  Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal p.asIdeal p.isPrime p.ne_bot

/- English proof (translation)
Use `ext1`. Rewrite using `[HeightOneSpectrum.under_asIdeal]`. Conclude with `w.2.over.symm`.
-/
private theorem under_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) : w.1.under (𝓞 K) = p := by
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact w.2.over.symm

/- English proof (translation)
Use `haveI := p.isMaximal`. Take `⟨P, hPm, hP⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal`. Conclude with `⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩, hP⟩⟩`.
-/
private theorem nonempty_over (p : HeightOneSpectrum (𝓞 K)) : Nonempty (PlacesOver L p) := by
  haveI := p.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  exact ⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩, hP⟩⟩

/- English proof (translation)
Establish `hf : ∀ p ∉ MainNotions, ∀ w : PlacesOver L p, 0 < fdeg w`. Introduce `p hp w`. Use `((h p hp).2.2 w).2.1` as an intermediate fact. Break down `Nat.eq_zero_or_pos (fdeg w) with h0 | h0` into its components or cases. Rewrite `this` using `[h0]`.

Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `hL` using `(GlobalTheory.HenQ.Regroup.multipliable_E L SL BL c₀ r (by`. Introduce `w hw`. Establish `hp : w.under (𝓞 K) ∉ MainNotions` using `(hS w).not.mp hw`.

Set `w' : PlacesOver L (w.under (𝓞 K))` to `⟨w, ⟨rfl⟩⟩`. Take `⟨h1, h2, h3⟩` from `h _ hp`. Establish `hB : BL w = _` using `(h3 w').2.2`. Establish `hN : Ideal.absNorm w.asIdeal = _` using `norm_eq w'`. Use `⟨by rw [hB, Multiset.card_map]; exact h1, fun b hb => ?_⟩` and prove the remaining obligations.

Rewrite `hb` using `[hB]`. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hb`. Rewrite using `[hN, norm_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (h2 a ha) _) s hs).hasProd`. Establish `hK : ∀ j ∈ Finset.range d, Multipliable (fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} => (((BK p.1).map (· * e p.1 ^ j)).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod)`.

Introduce `j _`. Use `GlobalTheory.HenQ.Regroup.multipliable_E K MainNotions (fun p => (BK p).map (· * e p ^ j)) c₀ r ?_ s hs` and prove the remaining obligations. Introduce `p hp`. Take `⟨h1, h2, h3⟩` from `h _ hp`. Take `⟨w⟩` from `nonempty_over (L := L) p`.

Establish `he : ‖e p‖ = 1` using `(h3 w).1.norm'_eq_one (hf p hp w).ne'`. Use `⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hb`. Rewrite using `[norm_mul, norm_pow, he, one_pow, mul_one]`. Conclude with `h2 a ha`.

Set `E : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, PlacesOver L p.1) ≃ {w : HeightOneSpectrum (𝓞 L) // w ∉ SL}` to `{ toFun := fun x => ⟨x.2.1, by rw [hS, under_eq x.2]; exact x.1.2⟩ invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hS w.1).not.mp w.2⟩, ⟨w.1, ⟨rfl⟩⟩⟩ left_inv := by`. Introduce and unpack `⟨⟨p, hp⟩, w⟩`. Establish `hw` using `under_eq w`. Take `⟨w, hw'⟩` from `w`. Simplify using `only at hw`.

Substitute `hw` using the available equality. Both sides reduce to the same expression. Use `right_inv := by intro w; rfl }`. Establish `h2` using `(E.hasProd_iff).mpr hL`. Unfold `eulerL`.

Rewrite using `[← Multipliable.tprod_finsetProd hK]`. Use `(h2.sigma ?_).tprod_eq` and prove the remaining obligations. Introduce and unpack `⟨p, hp⟩`. Take `⟨w₀⟩` from `nonempty_over (L := L) p`. Take `⟨-, -, h3⟩` from `h p hp`.

Establish `hcard : 0 < Fintype.card (PlacesOver L p)` using `Fintype.card_pos_iff.mpr ⟨w₀⟩`. Establish `hff : ∀ w : PlacesOver L p, fdeg w = fdeg w₀` using `fun w => Nat.eq_of_mul_eq_mul_left hcard ((h3 w).2.1.trans (h3 w₀).2.1.symm)`. Use `hasProd_fintype _ using 1` and compare the differences between its conclusion and the goal. Simplify using `only [E, Equiv.coe_fn_mk, Function.comp_apply]`. Rewrite using `[← (h3 w₀).2.1, fac_eq (h3 w₀).1 (hf p hp w₀), ← Finset.card_univ, ← Finset.prod_const]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[(h3 w).2.2, norm_eq w, cast_pow_cpow, hff w]`.
-/
private theorem core (d : ℕ) (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L)))
    (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (BL : HeightOneSpectrum (𝓞 L) → Multiset ℂ)
    (e : HeightOneSpectrum (𝓞 K) → ℂ) (c₀ : ℝ) (r : ℕ) (hd : 0 < d)
    (hS : ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ MainNotions)
    (h : ∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ (∀ b ∈ BK p, ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) ∧
      ∀ w : PlacesOver L p, IsPrimitiveRoot (e p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = d ∧
        BL w.1 = (BK p).map (· ^ fdeg w))
    (s : ℂ) (hs : c₀ + 1 < s.re) :
    ∏ j ∈ Finset.range d, eulerL K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerL L BL SL s := by
  have hf : ∀ p ∉ MainNotions, ∀ w : PlacesOver L p, 0 < fdeg w := by
    intro p hp w
    have := ((h p hp).2.2 w).2.1
    rcases Nat.eq_zero_or_pos (fdeg w) with h0 | h0
    · rw [h0] at this; omega
    · exact h0
  have hL := (GlobalTheory.HenQ.Regroup.multipliable_E L SL BL c₀ r (by
    intro w hw
    have hp : w.under (𝓞 K) ∉ MainNotions := (hS w).not.mp hw
    let w' : PlacesOver L (w.under (𝓞 K)) := ⟨w, ⟨rfl⟩⟩
    obtain ⟨h1, h2, h3⟩ := h _ hp
    have hB : BL w = _ := (h3 w').2.2
    have hN : Ideal.absNorm w.asIdeal = _ := norm_eq w'
    refine ⟨by rw [hB, Multiset.card_map]; exact h1, fun b hb => ?_⟩
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [hN, norm_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 a ha) _) s hs).hasProd
  have hK : ∀ j ∈ Finset.range d, Multipliable (fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} =>
      (((BK p.1).map (· * e p.1 ^ j)).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) := by
    intro j _
    refine GlobalTheory.HenQ.Regroup.multipliable_E K MainNotions (fun p => (BK p).map (· * e p ^ j)) c₀ r ?_ s hs
    intro p hp
    obtain ⟨h1, h2, h3⟩ := h _ hp
    obtain ⟨w⟩ := nonempty_over (L := L) p
    have he : ‖e p‖ = 1 := (h3 w).1.norm'_eq_one (hf p hp w).ne'
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [norm_mul, norm_pow, he, one_pow, mul_one]
    exact h2 a ha
  let E : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, PlacesOver L p.1) ≃
      {w : HeightOneSpectrum (𝓞 L) // w ∉ SL} :=
    { toFun := fun x => ⟨x.2.1, by rw [hS, under_eq x.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hS w.1).not.mp w.2⟩, ⟨w.1, ⟨rfl⟩⟩⟩
      left_inv := by
        rintro ⟨⟨p, hp⟩, w⟩
        have hw := under_eq w
        obtain ⟨w, hw'⟩ := w
        simp only at hw
        subst hw
        rfl
      right_inv := by intro w; rfl }
  have h2 := (E.hasProd_iff).mpr hL
  unfold eulerL
  rw [← Multipliable.tprod_finsetProd hK]
  refine (h2.sigma ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w₀⟩ := nonempty_over (L := L) p
  obtain ⟨-, -, h3⟩ := h p hp
  have hcard : 0 < Fintype.card (PlacesOver L p) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  have hff : ∀ w : PlacesOver L p, fdeg w = fdeg w₀ := fun w =>
    Nat.eq_of_mul_eq_mul_left hcard ((h3 w).2.1.trans (h3 w₀).2.1.symm)
  convert hasProd_fintype _ using 1
  · dsimp only [E, Equiv.coe_fn_mk, Function.comp_apply]
    rw [← (h3 w₀).2.1, fac_eq (h3 w₀).1 (hf p hp w₀), ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(h3 w).2.2, norm_eq w, cast_pow_cpow, hff w]

end BaseChangeLocalFactorRegrouping

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam.BaseChangeLocalFactorRegrouping in
/- English proof (translation)
Introduce `K L _ _ _ _ _ d MainNotions SL BK BL e c₀ r hd hS h`. Use `⟨c₀ + 1, fun s => ⟨fun hs => core d MainNotions SL BK BL e c₀ r hd.pos hS (fun p hp => ⟨(h p hp).1, fun b hb => ((h p hp).2.1 b hb).1, (h p hp).2.2⟩) s hs, fun hs => ?_⟩⟩` and prove the remaining obligations. Unfold `eulerLd`. Rewrite using `[← core d MainNotions SL (fun p => (BK p).map (·⁻¹)) (fun w => (BL w).map (·⁻¹)) (fun p => (e p)⁻¹) c₀ r hd.pos hS ?_ (1 - s) ?_]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `only [Multiset.map_map]`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, mul_inv, inv_pow]`.

Introduce `p hp`. Take `⟨h1, h2, h3⟩` from `h p hp`. Use `⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_, fun w => ⟨(h3 w).1.inv, (h3 w).2.1, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hb`. Conclude with `(h2 a ha).2`.

Simplify using `only [(h3 w).2.2, Multiset.map_map]`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, inv_pow]`. Simplify using `only [Complex.sub_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Z.Gam.regroupBC :
    UpperTheory.V.Z.Gam.RegroupBC := by
  intro K L _ _ _ _ _ d MainNotions SL BK BL e c₀ r hd hS h
  refine ⟨c₀ + 1, fun s => ⟨fun hs => core d MainNotions SL BK BL e c₀ r hd.pos hS
    (fun p hp => ⟨(h p hp).1, fun b hb => ((h p hp).2.1 b hb).1, (h p hp).2.2⟩) s hs, fun hs => ?_⟩⟩
  unfold eulerLd
  rw [← core d MainNotions SL (fun p => (BK p).map (·⁻¹)) (fun w => (BL w).map (·⁻¹)) (fun p => (e p)⁻¹) c₀ r hd.pos hS
    ?_ (1 - s) ?_]
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    funext p
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_pow]
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h p hp
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_, fun w => ⟨(h3 w).1.inv, (h3 w).2.1, ?_⟩⟩
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact (h2 a ha).2
    · simp only [(h3 w).2.2, Multiset.map_map]
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp_apply, inv_pow]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
