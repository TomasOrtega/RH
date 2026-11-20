import Formalism.LocalToGlobal.Columns.OcbBEntEntB

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

/- English proof (translation)
Establish `hdiv : p ≤ p' → (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t` using `fun h => Nat.div_le_div_right (by omega)`. Unfold `ocbAllow symIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem ocbPhi_forb_iff {k₀ m t a p p' : ℕ} (hk : 1 ≤ k₀) (hm : 4 ≤ m) (hra : k₀ + m - 1 ≤ a) (hne : p ≠ p') (hp' : p' < a) :
    (a ≤ p ∨ (p' < k₀ + m - 1 ∧ p < a ∧ (k₀ + m - 1 ≤ p ∨ symIdx k₀ (m / 2 - 1) p' < symIdx k₀ (m / 2 - 1) p ∨
        (p' = k₀ + (m / 2 - 1) ∧ p < k₀))) ∨
      (k₀ + m - 1 ≤ p' ∧ p < a ∧ (p' - (k₀ + m - 1)) / t < (p - (k₀ + m - 1)) / t)) ↔ ¬ ocbAllow k₀ m t a p p' := by
  have hdiv : p ≤ p' → (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t :=
    fun h => Nat.div_le_div_right (by omega)
  unfold ocbAllow symIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `LocE.fPos LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem ocbPhi_fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l := by
  unfold LocE.fPos LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `LocE.fPos`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem ocbPhi_fPos_lt {k₀ c n l : ℕ} (_hk : k₀ ≤ n) (hl : l < n + c) : LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fPos
  split_ifs <;> omega

/- English proof (translation)
Unfold `LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem ocbPhi_fIdx_lt {k₀ c n p : ℕ} (_hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Take `⟨h1, -, h4, hj, hjm, hc, hn', hn⟩` from `hr`. Establish `hjt : (j - 1) * t ≤ j * t` using `Nat.mul_le_mul_right t (Nat.sub_le j 1)`. Use `⟨by omega, by omega, by omega, by omega, h1, h4⟩` and prove the remaining obligations.
-/
theorem ocbPhi_ranks {k₀ m t j n' c n : ℕ} (hr : ocbRanks k₀ m t j n' c n) :
    k₀ ≤ n' ∧ k₀ ≤ n ∧ k₀ + m - 1 + (j - 1) * t ≤ n + c ∧ k₀ + m - 1 + (j - 1) * t = n' + (c + 1) ∧ 1 ≤ k₀ ∧ 4 ≤ m := by
  obtain ⟨h1, -, h4, hj, hjm, hc, hn', hn⟩ := hr
  have hjt : (j - 1) * t ≤ j * t := Nat.mul_le_mul_right t (Nat.sub_le j 1)
  refine ⟨by omega, by omega, by omega, by omega, h1, h4⟩

/- English proof (translation)
Take `⟨a, rfl⟩ : ∃ a, k₀ = a + 1` from `⟨k₀ - 1, by omega⟩`. Establish `hs : r - 1 = (a + 1) + (r - (a + 1) - 1)` using `by omega`. Rewrite using `[hs, Finset.sum_range_add, Finset.sum_range_succ]`. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ocbPhi_sum_split {R : Type} [CommRing R] (k₀ r : ℕ) (hk : 1 ≤ k₀) (hr : k₀ + 1 ≤ r) (M : ℕ → ℕ → R) :
    ∑ i ∈ Finset.range (r - 1), M i (i + 1) =
      (∑ i ∈ Finset.range (k₀ - 1), M i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), M (k₀ + i) (k₀ + i + 1)) + M (k₀ - 1) k₀ := by
  obtain ⟨a, rfl⟩ : ∃ a, k₀ = a + 1 := ⟨k₀ - 1, by omega⟩
  have hs : r - 1 = (a + 1) + (r - (a + 1) - 1) := by omega
  rw [hs, Finset.sum_range_add, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  ring

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Use `letI := resField P`. Unfold `LocE.unitV ocbChiV`. Distinguish the cases in `hx : redP P a = 0`. Establish `hnu : ¬ IsUnit (redP P a)`. Rewrite using `[hx]`.

Conclude with `not_isUnit_zero`. Rewrite using `[dif_neg hnu, dif_pos hx, map_zero]`. Establish `hu : IsUnit (redP P a)` using `isUnit_iff_ne_zero.mpr hx`. Rewrite using `[dif_pos hu, dif_neg hx]`. Rewrite using `[show hu.unit = Units.mk0 _ hx from Units.ext rfl]`.

Both sides reduce to the same expression.
-/
theorem ocbPhi_unitV (σ : K →+* ℂ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    σ (LocE.unitV χ a) = @ocbChiV (𝓞 E ⧸ P.asIdeal) (resField P) ((Units.map (σ : K →* ℂ)).comp χ) (redP P a) := by
  letI := resField P
  unfold LocE.unitV ocbChiV
  by_cases hx : redP P a = 0
  · have hnu : ¬ IsUnit (redP P a) := by
      rw [hx]
      exact not_isUnit_zero
    rw [dif_neg hnu, dif_pos hx, map_zero]
  · have hu : IsUnit (redP P a) := isUnit_iff_ne_zero.mpr hx
    rw [dif_pos hu, dif_neg hx]
    rw [show hu.unit = Units.mk0 _ hx from Units.ext rfl]
    rfl

/- English proof (translation)
Introduce `l s hl hs`. Take `⟨hk', hk, -, hsrc, -, -⟩` from `ocbPhi_ranks hr`. Substitute `hc'` using the available equality. Unfold `LocE.PhiGS at h`. Simplify using `only at h`.

Use `split_ifs at h with hc`. Establish `hp` using `ocbPhi_fPos_lt hk hl`. Establish `hp'` using `ocbPhi_fPos_lt hk' hs`. Establish `e` using `hc.1 (LocE.fPos k₀ c n l) (LocE.fPos k₀ (c + 1) n' s) hp (by omega)`. Rewrite `e` using `[ocbBEnt_entB, ocbPhi_fIdx_fPos hk hl, ocbPhi_fIdx_fPos hk' hs]`.

Conclude with `e`. Conclude with `absurd rfl h`.
-/
theorem ocbPhiGS_supp (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ m t j n' c' c n : ℕ}
    (hr : ocbRanks k₀ m t j n' c n) (hc' : c' = c + 1) (y : HomE E (n' + c') (n + c))
    (h : LocE.PhiGS q ψ₀ χ k₀ (m / 2 - 1) (k₀ + m - 1) t j c' n' c n y ≠ 0) :
    ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s) := by
  intro l s hl hs
  obtain ⟨hk', hk, -, hsrc, -, -⟩ := ocbPhi_ranks hr
  subst hc'
  unfold LocE.PhiGS at h
  dsimp only at h
  split_ifs at h with hc
  · have hp := ocbPhi_fPos_lt hk hl
    have hp' := ocbPhi_fPos_lt hk' hs
    have e := hc.1 (LocE.fPos k₀ c n l) (LocE.fPos k₀ (c + 1) n' s) hp (by omega)
    rw [ocbBEnt_entB, ocbPhi_fIdx_fPos hk hl, ocbPhi_fIdx_fPos hk' hs] at e
    exact e
  · exact absurd rfl h

/- English proof (translation)
Establish `h` using `redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by`. Introduce `i _`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb)`.

Simplify `h` using `[Fin.prod_univ_two]`.
-/
private theorem redP_mul_of_intAt_of_intAt {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a * b) = redP Q a * redP Q b := by
  have h := redP_prod (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.prod_univ_two] using h

/- English proof (translation)
Establish `h` using `redP_sum (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by`. Introduce `i _`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb)`.

Simplify `h` using `[Fin.sum_univ_two]`.
-/
private theorem redP_add_of_intAt {F : Type} [Field F] [NumberField F] {Q : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : IntAt Q a) (hb : IntAt Q b) : redP Q (a + b) = redP Q a + redP Q b := by
  have h := redP_sum (P := Q) (Finset.univ : Finset (Fin 2)) ![a, b] (by
    intro i _
    fin_cases i
    · exact ha
    · exact hb)
  simpa [Fin.sum_univ_two] using h

/- English proof (translation)
Take `⟨hk', hk, haN, hsrc, hk1, hm4⟩` from `ocbPhi_ranks hr`. Substitute `hc'` using the available equality. Use `letI := resField P`. Establish `hqn : q ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hu (by simp)`. Establish `hq0 : ((q : ℕ) : E) ≠ 0` using `Nat.cast_ne_zero.mpr hqn`. Establish `hF : ∀ p p', p < n + c → p' < n' + (c + 1) → ocbEnt k₀ (c + 1) n' c n ybar p p' = redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y p p')`. Introduce `p p' hp hp'`. Rewrite using `[ocbBEnt_entB]`.

Conclude with `hred _ _ (ocbPhi_fIdx_lt hk hp) (ocbPhi_fIdx_lt hk' hp')`. Establish `hI : ∀ p p', p < n + c → p' < n' + (c + 1) → IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y p p')`. Introduce `p p' hp hp'`. Rewrite using `[ocbBEnt_entB]`. Conclude with `hint _ _ (ocbPhi_fIdx_lt hk hp) (ocbPhi_fIdx_lt hk' hp')`.

Establish `hz : ∀ x : E, IntAt P x → (redP P x = 0 ↔ IntAt P (x / (q : E)))`. Introduce `x hx`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Conclude with `ciIntAt_div hq hu hx h0`.

Introduce `hb`. Establish `e : x = (q : E) * (x / (q : E))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, redP_mul_of_intAt_of_intAt ciIntAt_q hb, redP_natCast_eq_zero hq, zero_mul]`. Unfold `LocE.PhiGS ocbPhiS`.

Simplify using `only`. Use `split_ifs with h1 h2 h2`. Rewrite using `[map_mul, map_inv₀, ocbPhi_unitV]`. Unfold `LocE.lamGvS`. Rewrite using `[map_mul, map_prod]`.

Repeatedly rewrite using `[ocbPhi_unitV]`. Establish `h0 : ocbEnt k₀ (c + 1) n' c n ybar (k₀ - 1) k₀ = 0`. Assume the negation of the conclusion as `hnz`. Establish `ha` using `h2.2 (k₀ - 1) k₀ (by omega) (by omega) (by omega) hnz`. Unfold `ocbAllow at ha`.

Apply the tactic sequence `split_ifs at ha <;> omega`. Establish `e1 : ∑ i ∈ Finset.range (k₀ - 1), redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1)) = ∑ i ∈ Finset.range (k₀ - 1), ocbEnt k₀ (c + 1) n' c n ybar i (i + 1)`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Use `Finset.mem_range.mp hi` as an intermediate fact. Conclude with `(hF _ _ (by omega) (by omega)).symm`.

Establish `e2 : ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1), redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) = ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1), ocbEnt k₀ (c + 1) n' c n ybar (k₀ + i) (k₀ + i + 1)`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Use `Finset.mem_range.mp hi` as an intermediate fact. Conclude with `(hF _ _ (by omega) (by omega)).symm`. Establish `hS : redP P (∑ i ∈ Finset.range (k₀ - 1), LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1) + ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1), LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) = ∑ i ∈ Finset.range (k₀ + m …`.

Establish `i1 : ∀ i ∈ Finset.range (k₀ - 1), IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1))`. Introduce `i hi`. Use `Finset.mem_range.mp hi` as an intermediate fact. Conclude with `hI _ _ (by omega) (by omega)`. Establish `i2 : ∀ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1), IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1))`.

Introduce `i hi`. Use `Finset.mem_range.mp hi` as an intermediate fact. Conclude with `hI _ _ (by omega) (by omega)`. Rewrite using `[redP_add_of_intAt (ciIntAt_sum _ _ i1) (ciIntAt_sum _ _ i2), redP_sum _ _ i1, redP_sum _ _ i2, e1, e2, ocbPhi_sum_split k₀ (k₀ + m - 1) hk1 (by omega), h0, add_zero]`. Establish `hB : ∀ i ∈ Finset.range (j - 1), redP P (Matrix.of fun (s s' : Fin t) => LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')).det = (Matrix.of fun (s s' : Fin t) => ocbEnt k₀ (c + 1) n' c n ybar (k₀ + m - 1 + i * …`.

Introduce `i hi`. Establish `hi'` using `Finset.mem_range.mp hi`. Establish `hmul : (i + 1) * t ≤ (j - 1) * t` using `Nat.mul_le_mul_right t hi'`. Rewrite `hmul` using `[Nat.add_mul, one_mul]`. Establish `hlt : ∀ s : Fin t, k₀ + m - 1 + i * t + ↑s < k₀ + m - 1 + (j - 1) * t` using `fun s => by`.

Use `s.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[redP_det (Matrix.of fun (s s' : Fin t) => LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')) (fun (s s' : Fin t) => hI (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s') (by have := hlt s; omega) (by have := …`. Use `congr 1`. Use extensionality with `s s'`.

Simplify using `only [Matrix.map_apply, Matrix.of_apply]`. Conclude with `(hF _ _ (by have := hlt s; omega) (by have := hlt s'; omega)).symm`. Establish `hT : redP P (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y ↑s ↑s').det = (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => ocbEnt k₀ (c + 1) n' c n ybar ↑s ↑s').det`. Rewrite using `[redP_det (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y ↑s ↑s') (fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => hI (↑s) (↑s') (by have := s.isLt; omega) (by have := s'.isLt; omega))]`. Use `congr 1`.

Use extensionality with `s s'`. Simplify using `only [Matrix.map_apply, Matrix.of_apply]`. Conclude with `(hF _ _ (by have := s.isLt; omega) (by have := s'.isLt; omega)).symm`. Rewrite using `[hS, hT, Finset.prod_congr rfl (fun i hi => by rw [hB i hi])]`. Both sides reduce to the same expression.

It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `p' hp'`. Rewrite using `[hF p' p' (by omega) (by omega)]`.

Conclude with `(h1.2.2.1 p' hp').1`. Introduce `p p' hp hp' hne hnz`. Assume the negation of the conclusion as `hna`. Apply `hnz` to reduce the goal to its premises. Rewrite using `[hF p p' hp (by omega)]`.

Establish `hd` using `(ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne hp').mpr hna`. Break down `hd with hd | ⟨h3, h4, h5⟩ | ⟨h3, h4, h5⟩` into its components or cases. Conclude with `(hz _ (hI p p' hp (by omega))).mpr (h1.2.1 p p' hd hp hp')`. Conclude with `(h1.2.2.1 p' h3).2 p h4 hne h5`. Conclude with `h1.2.2.2 p p' h3 hp' h4 h5`.

It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises. Use `⟨fun p p' hp hp' => hI p p' hp (by omega), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p p' hap hp hp'`. Apply `(hz _ (hI p p' hp (by omega))).mp` to reduce the goal to its premises.

Rewrite using `[← hF p p' hp (by omega)]`. Assume the negation of the conclusion as `hnz`. Conclude with `(ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) (by omega) hp').mp (Or.inl hap) (h2.2 p p' hp hp' (by omega) hnz)`. Introduce `p' hp'`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hF p' p' (by omega) (by omega)]`. Conclude with `h2.1 p' hp'`. Introduce `p hp hne h5`. Rewrite using `[← hF p p' (by omega) (by omega)]`. Assume the negation of the conclusion as `hnz`.

Conclude with `(ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne (by omega)).mp (Or.inr (Or.inl ⟨hp', hp, h5⟩)) (h2.2 p p' (by omega) (by omega) hne hnz)`. Introduce `p p' h3 hp' hp h5`. Rewrite using `[← hF p p' (by omega) (by omega)]`. Assume the negation of the conclusion as `hnz`. Establish `hne : p ≠ p'`.

Introduce and unpack `rfl`. Conclude with `lt_irrefl _ h5`. Conclude with `(ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne hp').mp (Or.inr (Or.inr ⟨h3, hp, h5⟩)) (h2.2 p p' (by omega) hp' hne hnz)`. Conclude with `map_zero σ`.
-/
theorem ocbPhiGS_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (σ : K →+* ℂ)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ m t j n' c' c n : ℕ}
    (hr : ocbRanks k₀ m t j n' c n) (hc' : c' = c + 1) (y : HomE E (n' + c') (n + c))
    (ybar : (Fin (n' + (c + 1)) → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal))
    (hint : ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) :
    σ (LocE.PhiGS q ψ₀ χ k₀ (m / 2 - 1) (k₀ + m - 1) t j c' n' c n y) =
      @ocbPhiS (𝓞 E ⧸ P.asIdeal) (resField P) ((σ : K →* ℂ).compAddChar ψ₀) (fun i => (Units.map (σ : K →* ℂ)).comp (χ i))
        k₀ m t j n' c n ybar := by
  obtain ⟨hk', hk, haN, hsrc, hk1, hm4⟩ := ocbPhi_ranks hr
  subst hc'
  letI := resField P
  have hqn : q ≠ 0 := by
    rintro rfl
    exact hu (by simp)
  have hq0 : ((q : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr hqn
  have hF : ∀ p p', p < n + c → p' < n' + (c + 1) →
      ocbEnt k₀ (c + 1) n' c n ybar p p' =
        redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y p p') := by
    intro p p' hp hp'
    rw [ocbBEnt_entB]
    exact hred _ _ (ocbPhi_fIdx_lt hk hp) (ocbPhi_fIdx_lt hk' hp')
  have hI : ∀ p p', p < n + c → p' < n' + (c + 1) →
      IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y p p') := by
    intro p p' hp hp'
    rw [ocbBEnt_entB]
    exact hint _ _ (ocbPhi_fIdx_lt hk hp) (ocbPhi_fIdx_lt hk' hp')
  have hz : ∀ x : E, IntAt P x → (redP P x = 0 ↔ IntAt P (x / (q : E))) := by
    intro x hx
    constructor
    · intro h0
      exact ciIntAt_div hq hu hx h0
    · intro hb
      have e : x = (q : E) * (x / (q : E)) := by
        field_simp
      rw [e, redP_mul_of_intAt_of_intAt ciIntAt_q hb, redP_natCast_eq_zero hq, zero_mul]
  unfold LocE.PhiGS ocbPhiS
  dsimp only
  split_ifs with h1 h2 h2
  · rw [map_mul, map_inv₀, ocbPhi_unitV]
    unfold LocE.lamGvS
    rw [map_mul, map_prod]
    simp_rw [ocbPhi_unitV]
    have h0 : ocbEnt k₀ (c + 1) n' c n ybar (k₀ - 1) k₀ = 0 := by
      by_contra hnz
      have ha := h2.2 (k₀ - 1) k₀ (by omega) (by omega) (by omega) hnz
      unfold ocbAllow at ha
      split_ifs at ha <;> omega
    have e1 : ∑ i ∈ Finset.range (k₀ - 1),
        redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1)) =
        ∑ i ∈ Finset.range (k₀ - 1), ocbEnt k₀ (c + 1) n' c n ybar i (i + 1) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have := Finset.mem_range.mp hi
      exact (hF _ _ (by omega) (by omega)).symm
    have e2 : ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1),
        redP P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) =
        ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1), ocbEnt k₀ (c + 1) n' c n ybar (k₀ + i) (k₀ + i + 1) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have := Finset.mem_range.mp hi
      exact (hF _ _ (by omega) (by omega)).symm
    have hS : redP P (∑ i ∈ Finset.range (k₀ - 1),
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1) +
        ∑ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1),
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) =
        ∑ i ∈ Finset.range (k₀ + m - 1 - 1), ocbEnt k₀ (c + 1) n' c n ybar i (i + 1) := by
      have i1 : ∀ i ∈ Finset.range (k₀ - 1),
          IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y i (i + 1)) := by
        intro i hi
        have := Finset.mem_range.mp hi
        exact hI _ _ (by omega) (by omega)
      have i2 : ∀ i ∈ Finset.range (k₀ + m - 1 - k₀ - 1),
          IntAt P (LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y (k₀ + i) (k₀ + i + 1)) := by
        intro i hi
        have := Finset.mem_range.mp hi
        exact hI _ _ (by omega) (by omega)
      rw [redP_add_of_intAt (ciIntAt_sum _ _ i1) (ciIntAt_sum _ _ i2), redP_sum _ _ i1, redP_sum _ _ i2, e1, e2,
        ocbPhi_sum_split k₀ (k₀ + m - 1) hk1 (by omega), h0, add_zero]
    have hB : ∀ i ∈ Finset.range (j - 1),
        redP P (Matrix.of fun (s s' : Fin t) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y
            (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')).det =
        (Matrix.of fun (s s' : Fin t) =>
          ocbEnt k₀ (c + 1) n' c n ybar (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')).det := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hmul : (i + 1) * t ≤ (j - 1) * t := Nat.mul_le_mul_right t hi'
      rw [Nat.add_mul, one_mul] at hmul
      have hlt : ∀ s : Fin t, k₀ + m - 1 + i * t + ↑s < k₀ + m - 1 + (j - 1) * t := fun s => by
        have := s.isLt
        omega
      rw [redP_det (Matrix.of fun (s s' : Fin t) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y
            (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s'))
        (fun (s s' : Fin t) => hI (k₀ + m - 1 + i * t + ↑s) (k₀ + m - 1 + i * t + ↑s')
          (by have := hlt s; omega) (by have := hlt s'; omega))]
      congr 1
      ext s s'
      simp only [Matrix.map_apply, Matrix.of_apply]
      exact (hF _ _ (by have := hlt s; omega) (by have := hlt s'; omega)).symm
    have hT : redP P (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y ↑s ↑s').det =
        (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => ocbEnt k₀ (c + 1) n' c n ybar ↑s ↑s').det := by
      rw [redP_det (Matrix.of fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) =>
          LocE.entB q k₀ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) y ↑s ↑s')
        (fun (s s' : Fin (k₀ + m - 1 + (j - 1) * t)) => hI (↑s) (↑s')
          (by have := s.isLt; omega) (by have := s'.isLt; omega))]
      congr 1
      ext s s'
      simp only [Matrix.map_apply, Matrix.of_apply]
      exact (hF _ _ (by have := s.isLt; omega) (by have := s'.isLt; omega)).symm
    rw [hS, hT, Finset.prod_congr rfl (fun i hi => by rw [hB i hi])]
    rfl
  · exfalso
    apply h2
    constructor
    · intro p' hp'
      rw [hF p' p' (by omega) (by omega)]
      exact (h1.2.2.1 p' hp').1
    · intro p p' hp hp' hne hnz
      by_contra hna
      apply hnz
      rw [hF p p' hp (by omega)]
      have hd := (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne hp').mpr hna
      rcases hd with hd | ⟨h3, h4, h5⟩ | ⟨h3, h4, h5⟩
      · exact (hz _ (hI p p' hp (by omega))).mpr (h1.2.1 p p' hd hp hp')
      · exact (h1.2.2.1 p' h3).2 p h4 hne h5
      · exact h1.2.2.2 p p' h3 hp' h4 h5
  · exfalso
    apply h1
    refine ⟨fun p p' hp hp' => hI p p' hp (by omega), ?_, ?_, ?_⟩
    · intro p p' hap hp hp'
      apply (hz _ (hI p p' hp (by omega))).mp
      rw [← hF p p' hp (by omega)]
      by_contra hnz
      exact (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) (by omega) hp').mp
        (Or.inl hap) (h2.2 p p' hp hp' (by omega) hnz)
    · intro p' hp'
      refine ⟨?_, ?_⟩
      · rw [← hF p' p' (by omega) (by omega)]
        exact h2.1 p' hp'
      · intro p hp hne h5
        rw [← hF p p' (by omega) (by omega)]
        by_contra hnz
        exact (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne (by omega)).mp
          (Or.inr (Or.inl ⟨hp', hp, h5⟩)) (h2.2 p p' (by omega) (by omega) hne hnz)
    · intro p p' h3 hp' hp h5
      rw [← hF p p' (by omega) (by omega)]
      by_contra hnz
      have hne : p ≠ p' := by
        rintro rfl
        exact lt_irrefl _ h5
      exact (ocbPhi_forb_iff (a := k₀ + m - 1 + (j - 1) * t) (t := t) hk1 hm4 (by omega) hne hp').mp
        (Or.inr (Or.inr ⟨h3, hp, h5⟩)) (h2.2 p p' (by omega) hp' hne hnz)
  · exact map_zero σ

end Loc

end Formalism.L2.Col
