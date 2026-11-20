import Formalism.LocalToGlobal.Columns.XtLamGvSCongr

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc1

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Substitute `hc'` using the available equality. Establish `hf : ∀ m s, LocE.fIdx k₀ 0 m s = s`. Introduce `m s`. Unfold `LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.

Simplify using `[LocE.entB, hf, LocE.scE, Loc.atN, hp, hp']`.
-/
theorem xtEntB {q k₀ c' n' n : ℕ} (hc' : c' = 0) (x : HomE E (n' + c') (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' = x (Loc.eN E (n' + c') p') ⟨p, by omega⟩ := by
  subst hc'
  have hf : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, hf, LocE.scE, Loc.atN, hp, hp']

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]`.
-/
theorem xtRes {c' n' p' : ℕ} (hp' : p' < n') :
    LinearMap.funLeft E E (Fin.castAdd c') (Loc.eN E (n' + c') p') = (Pi.single (⟨p', hp'⟩ : Fin n') (1 : E) : Sp E n') := by
  funext l
  simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]

/- English proof (translation)
Use `⟨(q : 𝓞 E) ^ k, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem xtIntAt_qpow (q k : ℕ) : IntAt P ((q : E) ^ k) := by
  refine ⟨(q : 𝓞 E) ^ k, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp

open Classical in

/- English proof (translation)
Substitute `hc'` using the available equality. Establish `hone : IntAt P (-1 : E)` using `⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩`. Establish `hneg : ∀ z : E, IntAt P z → IntAt P (-z)` using `fun z hz => by`. Rewrite using `[← neg_one_mul]`. Conclude with `hone.mul hz`.

Establish `hqI : IntAt P (q : E)` using `by simpa using xtIntAt_qpow (P := P) q 1`. Establish `hεI : IntAt P (ε : E)` using `⟨ε, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩`. Establish `hq0 : (q : E) ≠ 0`. Introduce `h0`. Apply `hu` to reduce the goal to its premises.

Establish `h1 : ((q : ℕ) : 𝓞 E) = 0`. Apply `IsFractionRing.injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[map_natCast, h0, map_zero]`. Rewrite using `[h1]`. Conclude with `Submodule.zero_mem _`.

Establish `diff : ∀ a b : E, IntAt P a → IntAt P b → redP P b = redP P a → IntAt P ((b - a) / (q : E))`. Introduce `a b ha hb hab`. Establish `hba : IntAt P (b - a)`. Rewrite using `[sub_eq_add_neg]`. Conclude with `hb.add (hneg a ha)`.

Establish `hr0 : redP P (b - a) = 0`. Establish `h1` using `reduction_add hba ha`. Rewrite `h1` using `[sub_add_cancel, hab]`. Conclude with `(add_eq_right.1 h1.symm)`. Conclude with `ciIntAt_div hq hu hba hr0`.

Establish `eX : ∀ p p' (hp : p < n) (hp' : p' < n'), LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' = prX (zA (Pi.single ⟨p', hp'⟩ 1)) ⟨p, by omega⟩`. Introduce `p p' hp hp'`. Rewrite using `[xtEntB rfl _ hp hp']`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[xtRes hp']`.

Establish `eY : ∀ p p' (hp : p < n) (hp' : p' < n'), LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' = zB (Pi.single ⟨p', hp'⟩ 1) ⟨p, by omega⟩`. Introduce `p p' hp hp'`. Rewrite using `[xtEntB rfl _ hp hp']`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[xtRes hp']`.

Establish `hexp : ∀ L : Sp E n' →ₗ[E] E, L y' = ∑ j, y' j * L (Pi.single j 1)`. Introduce `L`. Use `conv_lhs => rw [show y' = ∑ j, y' j • (Pi.single j (1 : E) : Sp E n') by`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]]`.

Simplify using `[map_sum, map_smul, smul_eq_mul]`. Distinguish the cases in `hall : ∀ j : Fin n', ∀ i, IntAt P (zA (Pi.single j 1) i)`. Establish `hB` using `fun j => (H j).1.1 (hall j)`. Establish `hl` using `fun j => ((hsplit _).1 (hall j)).2`. Establish `hpr` using `fun j => ((hsplit _).1 (hall j)).1`.

Establish `hres` using `fun j => (H j).2 (hall j)`. Rewrite using `[if_pos (show ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) from fun i => hl i), if_pos (show ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) from fun i => (hB i).2)]`. Establish `hΦ : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0))`. Apply `hcongr` to reduce the goal to its premises. Introduce `p p' hp hp'`.

Establish `hpn : p < n` using `by omega`. Rewrite using `[eX p p' hpn hp', eY p p' hpn hp']`. Use `⟨_, diff _ _ ((hB ⟨p', hp'⟩).1 ⟨p, by omega⟩) (hpr ⟨p', hp'⟩ ⟨p, by omega⟩) ((hres ⟨p', hp'⟩).1 ⟨p, by omega⟩), ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Rewrite using `[hΦ]`. Use `congr 1`. Establish `hΔ : IntAt P ((lastN ∘ₗ zA) y' - ηB y')`. Rewrite using `[hexp (lastN ∘ₗ zA), hexp ηB, ← Finset.sum_sub_distrib]`. Use `ciIntAt_sum _ _ fun j _ => ?_` and prove the remaining obligations.

Establish `e : y' j * (lastN ∘ₗ zA) (Pi.single j 1) - y' j * ηB (Pi.single j 1) = ((q : E) * y' j) * (((lastN ∘ₗ zA) (Pi.single j 1) - ηB (Pi.single j 1)) / (q : E))`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[e]`. Conclude with `(hy j).mul (diff _ _ (hB j).2 (hl j) (hres j).2)`.

Establish `hqη : IntAt P ((q : E) * ηB y')`. Rewrite using `[hexp ηB, Finset.mul_sum]`. Use `ciIntAt_sum _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `(hy j).mul (hB j).2`.

Establish `hD' : D = (D - 1) + 1` using `by omega`. Establish `h1 : IntAt P ((q : E) ^ D * ((ε : E) * ηB y'))`. Establish `e : (q : E) ^ D * ((ε : E) * ηB y') = (ε : E) * (q : E) ^ (D - 1) * ((q : E) * ηB y')` using `by conv_lhs => rw [hD', pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `(hεI.mul (xtIntAt_qpow q (D - 1))).mul hqη`. Establish `h2 : IntAt P ((q : E) ^ D * ((ε : E) * ((lastN ∘ₗ zA) y' - ηB y')))`. Rewrite using `[← mul_assoc, mul_comm ((q : E) ^ D), mul_assoc]`. Conclude with `hεI.mul ((xtIntAt_qpow q D).mul hΔ)`. Establish `e : (ε : E) * (lastN ∘ₗ zA) y' = (ε : E) * ηB y' + (ε : E) * ((lastN ∘ₗ zA) y' - ηB y')`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, psi_add _ _ h1 h2, psi_int _ (hεI.mul hΔ), mul_one]`. Use `push_neg at hall`. Take `⟨j, i, hji⟩` from `hall`. Establish `hnA : ¬ ∀ i, IntAt P (zA (Pi.single j 1) i)` using `fun h => hji (h i)`.

Establish `hnB : ¬ ((∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1)))` using `fun h => hnA ((H j).1.2 h)`. Establish `hnS : ¬ ((∀ i, IntAt P (prX (zA (Pi.single j 1)) i)) ∧ IntAt P (lastN (zA (Pi.single j 1))))` using `fun h => hnA ((hsplit _).2 h)`. Establish `L0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) * (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) = 0`. Distinguish the cases in `hl : IntAt P (lastN (zA (Pi.single j 1)))`. Establish `hpx : ¬ ∀ i, IntAt P (prX (zA (Pi.single j 1)) i)` using `fun h => hnS ⟨h, hl⟩ push_neg at hpx`.

Take `⟨p, hp⟩` from `hpx`. Establish `h0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0`. Assume the negation of the conclusion as `h0`. Establish `h3` using `hint _ h0 p.1 j.1 p.2 j.2`. Rewrite `h3` using `[eX p.1 j.1 (by omega) j.2]`.

Conclude with `hp h3`. Rewrite using `[h0, zero_mul]`. Rewrite using `[if_neg (fun h => hl (h j)), mul_zero]`. Establish `R0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) * (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) = 0`. Distinguish the cases in `hl : IntAt P (ηB (Pi.single j 1))`.

Establish `hpx : ¬ ∀ i, IntAt P (zB (Pi.single j 1) i)` using `fun h => hnB ⟨h, hl⟩ push_neg at hpx`. Take `⟨p, hp⟩` from `hpx`. Establish `h0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0`. Assume the negation of the conclusion as `h0`. Establish `h3` using `hint _ h0 p.1 j.1 p.2 j.2`.

Rewrite `h3` using `[eY p.1 j.1 (by omega) j.2]`. Conclude with `hp h3`. Rewrite using `[h0, zero_mul]`. Rewrite using `[if_neg (fun h => hl (h j)), mul_zero]`. Rewrite using `[L0, R0]`.
-/
theorem xtLocal {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ c' n' n N : ℕ} (hc' : c' = 0)
    (Φ : Loc.SF E K (n' + c') (n + 0))
    (hcongr : ∀ x x' : HomE E (n' + c') (n + 0), (∀ p p', p < n + 0 → p' < n' → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) → Φ x' = Φ x)
    (hint : ∀ x : HomE E (n' + c') (n + 0), Φ x ≠ 0 → ∀ p p', p < n + 0 → p' < n' →
      IntAt P (LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p'))
    (ψ : E → K) (D : ℕ) (hD : 1 ≤ D)
    (psi_add : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → ψ (x + y) = ψ x * ψ y)
    (psi_int : ∀ x : E, IntAt P x → ψ x = 1) (ε : ℤ)
    (prX : Sp E N →ₗ[E] Sp E (n + 0)) (lastN : Sp E N →ₗ[E] E)
    (hsplit : ∀ a : Sp E N, (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prX a i)) ∧ IntAt P (lastN a))
    (zA : HomE E n' N) (zB : HomE E n' (n + 0)) (ηB : Sp E n' →ₗ[E] E)
    (H : ∀ j : Fin n', ((∀ i, IntAt P (zA (Pi.single j 1) i)) ↔ (∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) ∧
      ((∀ i, IntAt P (zA (Pi.single j 1) i)) → (∀ i, redP P (prX (zA (Pi.single j 1)) i) = redP P (zB (Pi.single j 1) i)) ∧
        redP P (lastN (zA (Pi.single j 1))) = redP P (ηB (Pi.single j 1))))
    (y' : Sp E n') (hy : ∀ j, IntAt P ((q : E) * y' j)) :
    Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) =
      Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) := by
  subst hc'
  have hone : IntAt P (-1 : E) :=
    ⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hneg : ∀ z : E, IntAt P z → IntAt P (-z) := fun z hz => by
    rw [← neg_one_mul]
    exact hone.mul hz
  have hqI : IntAt P (q : E) := by simpa using xtIntAt_qpow (P := P) q 1
  have hεI : IntAt P (ε : E) :=
    ⟨ε, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hq0 : (q : E) ≠ 0 := by
    intro h0
    apply hu
    have h1 : ((q : ℕ) : 𝓞 E) = 0 := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_natCast, h0, map_zero]
    rw [h1]
    exact Submodule.zero_mem _
  have diff : ∀ a b : E, IntAt P a → IntAt P b → redP P b = redP P a →
      IntAt P ((b - a) / (q : E)) := by
    intro a b ha hb hab
    have hba : IntAt P (b - a) := by
      rw [sub_eq_add_neg]
      exact hb.add (hneg a ha)
    have hr0 : redP P (b - a) = 0 := by
      have h1 := reduction_add hba ha
      rw [sub_add_cancel, hab] at h1
      exact (add_eq_right.1 h1.symm)
    exact ciIntAt_div hq hu hba hr0
  have eX : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        prX (zA (Pi.single ⟨p', hp'⟩ 1)) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have eY : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        zB (Pi.single ⟨p', hp'⟩ 1) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have hexp : ∀ L : Sp E n' →ₗ[E] E, L y' = ∑ j, y' j * L (Pi.single j 1) := by
    intro L
    conv_lhs => rw [show y' = ∑ j, y' j • (Pi.single j (1 : E) : Sp E n') by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul, smul_eq_mul]
  by_cases hall : ∀ j : Fin n', ∀ i, IntAt P (zA (Pi.single j 1) i)
  · have hB := fun j => (H j).1.1 (hall j)
    have hl := fun j => ((hsplit _).1 (hall j)).2
    have hpr := fun j => ((hsplit _).1 (hall j)).1
    have hres := fun j => (H j).2 (hall j)
    rw [if_pos (show ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) from fun i => hl i),
      if_pos (show ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) from fun i => (hB i).2)]
    have hΦ : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) =
        Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) := by
      apply hcongr
      intro p p' hp hp'
      have hpn : p < n := by omega
      rw [eX p p' hpn hp', eY p p' hpn hp']
      refine ⟨_, diff _ _ ((hB ⟨p', hp'⟩).1 ⟨p, by omega⟩) (hpr ⟨p', hp'⟩ ⟨p, by omega⟩)
        ((hres ⟨p', hp'⟩).1 ⟨p, by omega⟩), ?_⟩
      field_simp
      try ring
    rw [hΦ]
    congr 1
    have hΔ : IntAt P ((lastN ∘ₗ zA) y' - ηB y') := by
      rw [hexp (lastN ∘ₗ zA), hexp ηB, ← Finset.sum_sub_distrib]
      refine ciIntAt_sum _ _ fun j _ => ?_
      have e : y' j * (lastN ∘ₗ zA) (Pi.single j 1) - y' j * ηB (Pi.single j 1) =
          ((q : E) * y' j) * (((lastN ∘ₗ zA) (Pi.single j 1) - ηB (Pi.single j 1)) / (q : E)) := by
        field_simp
        try ring
      rw [e]
      exact (hy j).mul (diff _ _ (hB j).2 (hl j) (hres j).2)
    have hqη : IntAt P ((q : E) * ηB y') := by
      rw [hexp ηB, Finset.mul_sum]
      refine ciIntAt_sum _ _ fun j _ => ?_
      rw [← mul_assoc]
      exact (hy j).mul (hB j).2
    have hD' : D = (D - 1) + 1 := by omega
    have h1 : IntAt P ((q : E) ^ D * ((ε : E) * ηB y')) := by
      have e : (q : E) ^ D * ((ε : E) * ηB y') = (ε : E) * (q : E) ^ (D - 1) * ((q : E) * ηB y') := by
        conv_lhs => rw [hD', pow_succ]
        ring
      rw [e]
      exact (hεI.mul (xtIntAt_qpow q (D - 1))).mul hqη
    have h2 : IntAt P ((q : E) ^ D * ((ε : E) * ((lastN ∘ₗ zA) y' - ηB y'))) := by
      rw [← mul_assoc, mul_comm ((q : E) ^ D), mul_assoc]
      exact hεI.mul ((xtIntAt_qpow q D).mul hΔ)
    have e : (ε : E) * (lastN ∘ₗ zA) y' = (ε : E) * ηB y' + (ε : E) * ((lastN ∘ₗ zA) y' - ηB y') := by
      ring
    rw [e, psi_add _ _ h1 h2, psi_int _ (hεI.mul hΔ), mul_one]
  · push_neg at hall
    obtain ⟨j, i, hji⟩ := hall
    have hnA : ¬ ∀ i, IntAt P (zA (Pi.single j 1) i) := fun h => hji (h i)
    have hnB : ¬ ((∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) :=
      fun h => hnA ((H j).1.2 h)
    have hnS : ¬ ((∀ i, IntAt P (prX (zA (Pi.single j 1)) i)) ∧ IntAt P (lastN (zA (Pi.single j 1)))) :=
      fun h => hnA ((hsplit _).2 h)
    have L0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then
          ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) = 0 := by
      by_cases hl : IntAt P (lastN (zA (Pi.single j 1)))
      · have hpx : ¬ ∀ i, IntAt P (prX (zA (Pi.single j 1)) i) := fun h => hnS ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eX p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    have R0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) = 0 := by
      by_cases hl : IntAt P (ηB (Pi.single j 1))
      · have hpx : ¬ ∀ i, IntAt P (zB (Pi.single j 1) i) := fun h => hnB ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eY p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    rw [L0, R0]

end Loc1

end Formalism.L2.Col
