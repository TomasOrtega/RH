import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory

namespace SymLevelDatum

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

omit [StarRing E] in
/- English proof (translation)
The claim follows from `(intRing P).sum_mem hf`.
-/
theorem intAt_sum' {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) :=
  (intRing P).sum_mem hf

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[← Finset.sum_coe_sort s f, ← Finset.sum_coe_sort s (fun i => redP P (f i))]`. Conclude with `reduction_sum₂ P _ _ fun i => hf i.1 i.2`.
-/
theorem redP_sum' {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  rw [← Finset.sum_coe_sort s f, ← Finset.sum_coe_sort s (fun i => redP P (f i))]
  exact reduction_sum₂ P _ _ fun i => hf i.1 i.2

/- English proof (translation)
Establish `hq' : (q : E) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Prove the components needed by the constructor for the conclusion. Introduce `h l l'`. Establish `h1 : ((q : E) ^ e' l'.1) • eN E N' l'.1 ∈ sclLat P q N' e'`. Rewrite using `[mem_sclLat]`.

Introduce `i`. Distinguish the cases in `hi : i.1 = l'.1`. Simplify using `only [Pi.smul_apply, eN, hi, if_true, smul_eq_mul, mul_one]`. Rewrite using `[inv_mul_cancel₀ (zpow_ne_zero _ hq')]`. Conclude with `intAt_one P`.

Simplify using `only [Pi.smul_apply, eN, hi, if_false, smul_eq_mul, mul_zero]`. Conclude with `intAt_zero P`. Establish `h2` using `(mem_sclLat P q _ _ _).1 (h _ h1) l`. Rewrite `h2` using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[zpow_sub₀ hq']`. Clear the denominators using the available nonvanishing facts. Introduce `h y hy`. Rewrite `hy`, the goal using `[mem_sclLat]`. Introduce `l`.

Establish `h1 : y = ∑ l' : Fin N', y l' • eN E N' l'.1`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, eN, Fin.val_inj]`. Rewrite using `[h1, map_sum, Finset.sum_apply, Finset.mul_sum]`. Use `intAt_sum' P _ _ fun l' _ => ?_` and prove the remaining obligations.

Use `(hy l').mul (h l l') using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, zpow_sub₀ hq']`. Clear the denominators using the available nonvanishing facts.
-/
theorem maps_iff (hq : q ≠ 0) {N' N : ℕ} (e' e : ℕ → ℤ) (x : HomE E N' N) :
    (∀ y ∈ sclLat P q N' e', x y ∈ sclLat P q N e) ↔
      ∀ (l : Fin N) (l' : Fin N'), IntAt P (x (eN E N' l'.1) l * (q : E) ^ (e' l'.1 - e l.1)) := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  constructor
  · intro h l l'
    have h1 : ((q : E) ^ e' l'.1) • eN E N' l'.1 ∈ sclLat P q N' e' := by
      rw [mem_sclLat]
      intro i
      by_cases hi : i.1 = l'.1
      · simp only [Pi.smul_apply, eN, hi, if_true, smul_eq_mul, mul_one]
        rw [inv_mul_cancel₀ (zpow_ne_zero _ hq')]
        exact intAt_one P
      · simp only [Pi.smul_apply, eN, hi, if_false, smul_eq_mul, mul_zero]
        exact intAt_zero P
    have h2 := (mem_sclLat P q _ _ _).1 (h _ h1) l
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    convert h2 using 1
    rw [zpow_sub₀ hq']
    field_simp
  · intro h y hy
    rw [mem_sclLat] at hy ⊢
    intro l
    have h1 : y = ∑ l' : Fin N', y l' • eN E N' l'.1 := by
      funext i
      simp [Finset.sum_apply, eN, Fin.val_inj]
    rw [h1, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine intAt_sum' P _ _ fun l' _ => ?_
    convert (hy l').mul (h l l') using 1
    rw [map_smul, Pi.smul_apply, smul_eq_mul, zpow_sub₀ hq']
    field_simp

/- English proof (translation)
Unfold `fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem fIdx_lt {k c n s : ℕ} (hk : k ≤ n) (hs : s < n + c) : fIdx k c n s < n + c := by
  unfold fIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `fIdx fPos`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem fIdx_fPos {k c n l : ℕ} (hk : k ≤ n) (hl : l < n + c) : fPos k c n l < n + c ∧ fIdx k c n (fPos k c n l) = l := by
  unfold fIdx fPos
  split_ifs <;> omega

/- English proof (translation)
Unfold `lamY`. Rewrite using `[maps_iff P q hq]`. Prove the components needed by the constructor for the conclusion. Introduce `h p p' hp hp'`. Use `h ⟨_, fIdx_lt hk hp⟩ ⟨_, fIdx_lt hk' hp'⟩` as an intermediate fact.

Unfold `entB atN`. Rewrite using `[dif_pos (fIdx_lt hk hp)]`. Conclude with `this`. Introduce `h l l'`. Use `h _ _ (fIdx_fPos hk l.2).1 (fIdx_fPos hk' l'.2).1` as an intermediate fact.

Unfold `entB atN at this`. Rewrite `this` using `[(fIdx_fPos hk l.2).2, (fIdx_fPos hk' l'.2).2, dif_pos l.2]`. Conclude with `this`.
-/
theorem maps_lamY_iff (hq : q ≠ 0) {k c' n' c n : ℕ} (hk' : k ≤ n') (hk : k ≤ n) (ex' ex : ℕ → ℕ)
    (x : HomE E (n' + c') (n + c)) :
    (∀ y ∈ lamY P q n' c' ex', x y ∈ lamY P q n c ex) ↔
      ∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k c' n' c n ex' ex x p p') := by
  unfold lamY
  rw [maps_iff P q hq]
  constructor
  · intro h p p' hp hp'
    have := h ⟨_, fIdx_lt hk hp⟩ ⟨_, fIdx_lt hk' hp'⟩
    unfold entB atN
    rw [dif_pos (fIdx_lt hk hp)]
    exact this
  · intro h l l'
    have := h _ _ (fIdx_fPos hk l.2).1 (fIdx_fPos hk' l'.2).1
    unfold entB atN at this
    rw [(fIdx_fPos hk l.2).2, (fIdx_fPos hk' l'.2).2, dif_pos l.2] at this
    exact this

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Unfold `entB atN`. Use `split_ifs`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem entB_add_smul {N' N : ℕ} (k c' n' c n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E N' N) (u : E) (p p' : ℕ) :
    entB q k c' n' c n ex' ex (x + u • z) p p' =
      entB q k c' n' c n ex' ex x p p' + u * entB q k c' n' c n ex' ex z p p' := by
  unfold entB atN
  split_ifs
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

omit [StarRing E] in
/- English proof (translation)
The claim follows from `(intRing P).toAddSubgroup.add_mem_cancel_right (x := b) (y := a) hb`.
-/
theorem intAt_add_iff {a b : E} (hb : IntAt P b) : IntAt P (a + b) ↔ IntAt P a :=
  (intRing P).toAddSubgroup.add_mem_cancel_right (x := b) (y := a) hb

omit [StarRing E] in
/- English proof (translation)
Simplify using `using IntAt.coe P (q : 𝓞 E)`.
-/
theorem intAt_natCast : IntAt P (q : E) := by simpa using IntAt.coe P (q : 𝓞 E)

omit [StarRing E] in
/- English proof (translation)
Establish `hqb` using `(intAt_natCast P q).mul hb`. Distinguish the cases in `ha : IntAt P a`. Establish `: redP P (q : E) = 0`. Use `reduction_coe P (q : 𝓞 E)` as an intermediate fact. Rewrite `this` using `[map_natCast (algebraMap (𝓞 E) E)]`.

Rewrite using `[this, Ideal.Quotient.eq_zero_iff_mem.2 hP]`. Rewrite using `[reduction_add ha hqb, reduction_mul (intAt_natCast P q) hb, this, zero_mul, add_zero]`. Rewrite using `[reduction_eq_zero_of_not_integral P ha, reduction_eq_zero_of_not_integral P (by rwa [intAt_add_iff P hqb])]`.
-/
theorem redP_add_mul (hP : (q : 𝓞 E) ∈ P.asIdeal) (a : E) {b : E} (hb : IntAt P b) :
    redP P (a + q * b) = redP P a := by
  have hqb := (intAt_natCast P q).mul hb
  by_cases ha : IntAt P a
  · have : redP P (q : E) = 0 := by
      have := reduction_coe P (q : 𝓞 E)
      rw [map_natCast (algebraMap (𝓞 E) E)] at this
      rw [this, Ideal.Quotient.eq_zero_iff_mem.2 hP]
    rw [reduction_add ha hqb, reduction_mul (intAt_natCast P q) hb, this, zero_mul, add_zero]
  · rw [reduction_eq_zero_of_not_integral P ha, reduction_eq_zero_of_not_integral P (by rwa [intAt_add_iff P hqb])]

variable {K : Type} [Field K]

omit [StarRing E] in
/- English proof (translation)
Unfold `unitV`. Generalize the expression as in `redP P a = u at h`. Generalize the expression as in `redP P b = v at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem unitV_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) : unitV χ a = unitV χ b := by
  unfold unitV
  generalize redP P a = u at h
  generalize redP P b = v at h
  subst h
  rfl

omit [StarRing E] in
/- English proof (translation)
Apply `unitV_congr` to reduce the goal to its premises. Rewrite using `[reduction_det P A hA, reduction_det P B hB]`. Simplify using `only [h]`.
-/
theorem unitV_det_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} {A B : Matrix (Fin t) (Fin t) E}
    (hA : ∀ i j, IntAt P (A i j)) (hB : ∀ i j, IntAt P (B i j)) (h : ∀ i j, redP P (A i j) = redP P (B i j)) :
    unitV χ A.det = unitV χ B.det := by
  apply unitV_congr
  rw [reduction_det P A hA, reduction_det P B hB]
  simp only [h]

omit [StarRing E] in
/- English proof (translation)
Unfold `lamGvS`. Establish `key : ∀ A : ℕ → ℕ → E, (∀ p p', p < r + j * t → p' < r + j * t → IntAt P (A p p')) → redP P (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) = ∑ i ∈ Finset.range (k - 1), redP P (A i (i + 1)) + ∑ i ∈ Finset.range (r - k - 1), redP …`. Introduce `A hA`. Establish `h1 : ∀ i ∈ Finset.range (k - 1), IntAt P (A i (i + 1))` using `fun i hi => by`. Rewrite `hi` using `[Finset.mem_range]`.

Conclude with `hA _ _ (by omega) (by omega)`. Establish `h2 : ∀ i ∈ Finset.range (r - k - 1), IntAt P (A (k + i) (k + i + 1))` using `fun i hi => by`. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `hA _ _ (by omega) (by omega)`. Rewrite using `[reduction_add (intAt_sum' P _ _ h1) (intAt_sum' P _ _ h2), redP_sum' P _ _ h1, redP_sum' P _ _ h2]`.

Use `congr 1`. Rewrite using `[key M hM, key M' hM']`. Use `congr 2`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`.

Conclude with `h _ _ (by omega) (by omega)`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `h _ _ (by omega) (by omega)`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_range]`. Establish `hb : ∀ s : Fin t, r + i * t + s.1 < r + j * t` using `fun s => by`. Establish `h1` using `s.2`. Establish `h2 : (i + 1) * t ≤ j * t` using `Nat.mul_le_mul_right t hi`. Rewrite `h2` using `[Nat.add_mul, one_mul]`.

Use linear arithmetic over natural numbers and integers. Conclude with `unitV_det_congr P _ (fun s s' => hM _ _ (hb s) (hb s')) (fun s s' => hM' _ _ (hb s) (hb s')) (fun s s' => h _ _ (hb s) (hb s'))`.
-/
theorem lamGvS_congr (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k r t j : ℕ} (hk : k ≤ r)
    {M M' : ℕ → ℕ → E} (hM : ∀ p p', p < r + j * t → p' < r + j * t → IntAt P (M p p'))
    (hM' : ∀ p p', p < r + j * t → p' < r + j * t → IntAt P (M' p p'))
    (h : ∀ p p', p < r + j * t → p' < r + j * t → redP P (M p p') = redP P (M' p p')) :
    lamGvS ψ χ k r t j M = lamGvS ψ χ k r t j M' := by
  unfold lamGvS
  have key : ∀ A : ℕ → ℕ → E, (∀ p p', p < r + j * t → p' < r + j * t → IntAt P (A p p')) →
      redP P (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) =
        ∑ i ∈ Finset.range (k - 1), redP P (A i (i + 1)) +
          ∑ i ∈ Finset.range (r - k - 1), redP P (A (k + i) (k + i + 1)) := by
    intro A hA
    have h1 : ∀ i ∈ Finset.range (k - 1), IntAt P (A i (i + 1)) := fun i hi => by
      rw [Finset.mem_range] at hi
      exact hA _ _ (by omega) (by omega)
    have h2 : ∀ i ∈ Finset.range (r - k - 1), IntAt P (A (k + i) (k + i + 1)) := fun i hi => by
      rw [Finset.mem_range] at hi
      exact hA _ _ (by omega) (by omega)
    rw [reduction_add (intAt_sum' P _ _ h1) (intAt_sum' P _ _ h2), redP_sum' P _ _ h1, redP_sum' P _ _ h2]
  congr 1
  · rw [key M hM, key M' hM']
    congr 2
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact h _ _ (by omega) (by omega)
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact h _ _ (by omega) (by omega)
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hb : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
      have h1 := s.2
      have h2 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi
      rw [Nat.add_mul, one_mul] at h2
      omega
    exact unitV_det_congr P _ (fun s s' => hM _ _ (hb s) (hb s')) (fun s s' => hM' _ _ (hb s) (hb s'))
      (fun s s' => h _ _ (hb s) (hb s'))

/- English proof (translation)
Establish `h` using `isOfFinOrder_of_finite g`. Take `⟨m, hm, h1⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `: ‖f g‖ ^ m = 1` using `by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this`.
-/
theorem norm_eq_one_of_finite {G : Type*} [Group G] [Finite G] (f : G →* ℂ) (g : G) : ‖f g‖ = 1 := by
  have h := isOfFinOrder_of_finite g
  obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have : ‖f g‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

omit [StarRing E] in
/- English proof (translation)
The claim follows from `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`.
-/
theorem finite_res : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot

omit [StarRing E] in
/- English proof (translation)
Use `finite_res P` as an intermediate fact. Unfold `unitV`. Use `split_ifs with h`. Conclude with `Or.inr (norm_eq_one_of_finite (σ.toMonoidHom.comp ((Units.coeHom K).comp χ)) h.unit)`. Simplify using the standard rewrite rules.
-/
theorem norm_unitV (σ : K →+* ℂ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    ‖σ (unitV χ a)‖ = 0 ∨ ‖σ (unitV χ a)‖ = 1 := by
  have := finite_res P
  unfold unitV
  split_ifs with h
  · exact Or.inr (norm_eq_one_of_finite (σ.toMonoidHom.comp ((Units.coeHom K).comp χ)) h.unit)
  · simp

omit [StarRing E] in
/- English proof (translation)
Use `finite_res P` as an intermediate fact. Conclude with `norm_eq_one_of_finite (σ.toMonoidHom.comp ψ.toMonoidHom) (Multiplicative.ofAdd a)`.
-/
theorem norm_addChar (σ : K →+* ℂ) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (a : 𝓞 E ⧸ P.asIdeal) : ‖σ (ψ a)‖ = 1 := by
  have := finite_res P
  exact norm_eq_one_of_finite (σ.toMonoidHom.comp ψ.toMonoidHom) (Multiplicative.ofAdd a)

end

/- English proof (translation)
Establish `hq' : (q : E) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Use `⟨fun x hx => ?_, fun x z hz => ?_, fun σ x => ?_⟩` and prove the remaining obligations. Rewrite using `[maps_lamY_iff P q hq hk' hk]`. Unfold `PhiGS at hx`. Simplify using `only at hx`.

Use `split_ifs at hx with h`. Introduce `p p' hp hp'`. Conclude with `h.1 p p' hp (ha ▸ hp')`. Conclude with `absurd rfl hx`. Rewrite `hz` using `[maps_lamY_iff P q hq hk' hk]`.

Unfold `PhiGS`. Establish `e` using `entB_add_smul q k c' n' c n (fun i => i + 1) (fun i => i + 1) x z (q : E)`. Generalize the expression as in `entB q k c' n' c n (fun i => i + 1) (fun i => i + 1) (x + (q : E) • z) = M' at e`. Generalize the expression as in `entB q k c' n' c n (fun i => i + 1) (fun i => i + 1) x = M at e`. Generalize the expression as in `entB q k c' n' c n (fun i => i + 1) (fun i => i + 1) z = Z at e hz`.

Rewrite `hz`, `hle` using `[ha]`. Establish `hI : ∀ p p', p < n + c → p' < r + (j - 1) * t → (IntAt P (M' p p') ↔ IntAt P (M p p'))` using `fun p p' hp hp' => by`. Rewrite using `[e, intAt_add_iff P ((intAt_natCast P q).mul (hz p p' hp hp'))]`. Establish `hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q))` using `fun p p' hp hp' => by`. Rewrite using `[e, add_div, mul_div_cancel_left₀ _ hq', intAt_add_iff P (hz p p' hp hp')]`.

Establish `hR : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t → redP P (M' p p') = redP P (M p p')` using `fun p p' hp hp' => by`. Rewrite using `[e, redP_add_mul P q hP _ (hz p p' (by omega) hp')]`. Simplify using `only`. Use `@if_ctx_congr _ _ _ (_) (_) _ _ _ _ ?_ (fun h => ?_) (fun _ => rfl)` and prove the remaining obligations. Use `and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))` and prove the remaining obligations.

Conclude with `forall₂_congr fun p p' => forall₂_congr fun hp hp' => hI p p' hp hp'`. Conclude with `forall₂_congr fun p p' => forall₃_congr fun _ hp hp' => hD p p' hp hp'`. Use `forall₂_congr fun p' hp' => and_congr ?_ (forall₄_congr fun p hp _ _ => ?_)` and prove the remaining obligations. Rewrite using `[hR _ _ (by omega) (by omega)]`. Rewrite using `[hR _ _ hp (by omega)]`.

Use `forall₂_congr fun p p' => forall₄_congr fun _ hp' hp _ => ?_` and prove the remaining obligations. Rewrite using `[hR _ _ hp hp']`. Establish `hM : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t → IntAt P (M p p')` using `fun p p' hp hp' => h.1 p p' (by omega) hp'`. Establish `hM' : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t → IntAt P (M' p p')` using `fun p p' hp hp' => (hI p p' (by omega) hp').2 (hM p p' hp hp')`. Rewrite using `[lamGvS_congr P ψ χ hr hM' hM hR]`.

Use `congr 2`. Conclude with `unitV_det_congr P _ (fun s s' => hM' _ _ s.2 s'.2) (fun s s' => hM _ _ s.2 s'.2) (fun s s' => hR _ _ s.2 s'.2)`. Unfold `PhiGS`. Simplify using `only`. Use `split_ifs`.

Unfold `lamGvS`. Rewrite using `[map_mul, map_mul, norm_mul, norm_mul, norm_addChar, one_mul, map_inv₀, norm_inv, map_prod, norm_prod]`. Use `mul_le_one₀ (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_) (by positivity) ?_` and prove the remaining obligations. Apply the tactic sequence `rcases norm_unitV P σ (χ i) _ with h | h <;> rw [h] <;> norm_num`. Apply the tactic sequence `rcases norm_unitV P σ (χ (j - 1)) _ with h | h <;> rw [h] <;> norm_num`.

Simplify using the standard rewrite rules.
-/
theorem locSmall_phiGS (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)
    (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k rS r t j c' n' c n : ℕ) (hq : q ≠ 0)
    (hP : (q : 𝓞 E) ∈ P.asIdeal) (ha : n' + c' = r + (j - 1) * t) (hle : n' + c' ≤ n + c) (hk' : k ≤ n') (hk : k ≤ n)
    (hr : k ≤ r) :
    LocSmall q (LocE.lamY P q n' c' fun i => i + 1) (LocE.lamY P q n c fun i => i + 1)
      (LocE.PhiGS q ψ χ k rS r t j c' n' c n) 1 := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  refine ⟨fun x hx => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · rw [maps_lamY_iff P q hq hk' hk]
    unfold PhiGS at hx
    simp only at hx
    split_ifs at hx with h
    · intro p p' hp hp'
      exact h.1 p p' hp (ha ▸ hp')
    · exact absurd rfl hx
  · rw [maps_lamY_iff P q hq hk' hk] at hz
    unfold PhiGS
    have e := entB_add_smul q k c' n' c n (fun i => i + 1) (fun i => i + 1) x z (q : E)
    generalize entB q k c' n' c n (fun i => i + 1) (fun i => i + 1) (x + (q : E) • z) = M' at e
    generalize entB q k c' n' c n (fun i => i + 1) (fun i => i + 1) x = M at e
    generalize entB q k c' n' c n (fun i => i + 1) (fun i => i + 1) z = Z at e hz
    rw [ha] at hz hle
    have hI : ∀ p p', p < n + c → p' < r + (j - 1) * t → (IntAt P (M' p p') ↔ IntAt P (M p p')) := fun p p' hp hp' => by
      rw [e, intAt_add_iff P ((intAt_natCast P q).mul (hz p p' hp hp'))]
    have hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) :=
      fun p p' hp hp' => by
        rw [e, add_div, mul_div_cancel_left₀ _ hq', intAt_add_iff P (hz p p' hp hp')]
    have hR : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t → redP P (M' p p') = redP P (M p p') :=
      fun p p' hp hp' => by
        rw [e, redP_add_mul P q hP _ (hz p p' (by omega) hp')]
    simp only
    refine @if_ctx_congr _ _ _ (_) (_) _ _ _ _ ?_ (fun h => ?_) (fun _ => rfl)
    · refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
      · exact forall₂_congr fun p p' => forall₂_congr fun hp hp' => hI p p' hp hp'
      · exact forall₂_congr fun p p' => forall₃_congr fun _ hp hp' => hD p p' hp hp'
      · refine forall₂_congr fun p' hp' => and_congr ?_ (forall₄_congr fun p hp _ _ => ?_)
        · rw [hR _ _ (by omega) (by omega)]
        · rw [hR _ _ hp (by omega)]
      · refine forall₂_congr fun p p' => forall₄_congr fun _ hp' hp _ => ?_
        rw [hR _ _ hp hp']
    · have hM : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t → IntAt P (M p p') :=
        fun p p' hp hp' => h.1 p p' (by omega) hp'
      have hM' : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t → IntAt P (M' p p') :=
        fun p p' hp hp' => (hI p p' (by omega) hp').2 (hM p p' hp hp')
      rw [lamGvS_congr P ψ χ hr hM' hM hR]
      congr 2
      exact unitV_det_congr P _ (fun s s' => hM' _ _ s.2 s'.2) (fun s s' => hM _ _ s.2 s'.2)
        (fun s s' => hR _ _ s.2 s'.2)
  · unfold PhiGS
    simp only
    split_ifs
    · unfold lamGvS
      rw [map_mul, map_mul, norm_mul, norm_mul, norm_addChar, one_mul, map_inv₀, norm_inv, map_prod, norm_prod]
      refine mul_le_one₀ (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_) (by positivity) ?_
      · rcases norm_unitV P σ (χ i) _ with h | h <;> rw [h] <;> norm_num
      · rcases norm_unitV P σ (χ (j - 1)) _ with h | h <;> rw [h] <;> norm_num
    · simp

end SymLevelDatum

end GlobalTheory
