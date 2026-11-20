import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/- English proof (translation)
Establish `: (x + y) w = x w + y w` using `rfl`. Simplify using `only [re, this, map_add, Complex.add_re]`.
-/
theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  have : (x + y) w = x w + y w := rfl
  simp only [re, this, map_add, Complex.add_re]

/- English proof (translation)
Establish `: (-x) w = -x w` using `rfl`. Simplify using `only [re, this, map_neg, Complex.neg_re]`.
-/
theorem re_neg (x : Ainf F) (w : InfinitePlace F) : re (-x) w = -re x w := by
  have : (-x) w = -x w := rfl
  simp only [re, this, map_neg, Complex.neg_re]

/- English proof (translation)
Establish `hw : w.IsReal` using `IsTotallyReal.isReal w`. Establish `: (x * y) w = x w * y w` using `rfl`. Simplify using `only [re, this, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, map_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]`.
-/
theorem re_mul [IsTotallyReal F] (x y : Ainf F) (w : InfinitePlace F) :
    re (x * y) w = re x w * re y w := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have : (x * y) w = x w * y w := rfl
  simp only [re, this, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, map_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `: (0 : Ainf F) w = 0` using `rfl`. Simplify using `[re, this]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, re_add, ih]`.
-/
theorem re_sum [IsTotallyReal F] {ι : Type} (s : Finset ι) (f : ι → Ainf F) (w : InfinitePlace F) :
    re (∑ i ∈ s, f i) w = ∑ i ∈ s, re (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (0 : Ainf F) w = 0 := rfl
    simp [re, this]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, re_add, ih]

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`.
-/
theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[inf, map_add]`.
-/
theorem inf_add (u v : Fin N → AF F) : inf (u + v) = inf u + inf v := by
  funext l; simp [inf, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[inf, map_neg]`.
-/
theorem inf_neg (u : Fin N → AF F) : inf (-u) = -inf u := by
  funext l; simp [inf, map_neg]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[fin, map_add]`.
-/
theorem fin_add (u v : Fin N → AF F) : fin (u + v) = fin u + fin v := by
  funext l; simp [fin, map_add]

/- English proof (translation)
Unfold `sz`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[inf_add, Pi.add_apply, re_add]`. Conclude with `abs_add_le _ _`.
-/
theorem sz_add_le (u v : Fin N → AF F) : sz (u + v) ≤ sz u + sz v := by
  unfold sz
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [inf_add, Pi.add_apply, re_add]
  exact abs_add_le _ _

/- English proof (translation)
Unfold `sz`. Simplify using `only [inf_neg, Pi.neg_apply, re_neg, abs_neg]`.
-/
theorem sz_neg (u : Fin N → AF F) : sz (-u) = sz u := by
  unfold sz
  simp only [inf_neg, Pi.neg_apply, re_neg, abs_neg]

/- English proof (translation)
Simplify using `only [inf, Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem inf_mulVec (M : Matrix (Fin N) (Fin N) (AF F)) (u : Fin N → AF F) (l : Fin N) :
    inf (M.mulVec u) l = ∑ m, fstA F (M l m) * inf u m := by
  simp only [inf, Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Use `set D : ℝ := ∑ l, ∑ m, ∑ w : InfinitePlace F, |re (fstA F (M l m)) w| with hD`. Establish `hD0 : 0 ≤ D` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hle : ∀ l m w, |re (fstA F (M l m)) w| ≤ D`. Introduce `l m w`. Establish `h1 : |re (fstA F (M l m)) w| ≤ ∑ w' : InfinitePlace F, |re (fstA F (M l m)) w'|` using `Finset.single_le_sum (f := fun w' => |re (fstA F (M l m)) w'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)`.

Establish `h2 : ∑ w' : InfinitePlace F, |re (fstA F (M l m)) w'| ≤ ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'|` using `Finset.single_le_sum (f := fun m' => ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)`. Establish `h3 : ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'| ≤ D` using `Finset.single_le_sum (f := fun l' => ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l' m')) w'|) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : ∀ (u : Fin N → AF F) m w, |re (inf u m) w| ≤ sz u`. Introduce `u m w`.

Establish `h1 : |re (inf u m) w| ≤ ∑ w' : InfinitePlace F, |re (inf u m) w'|` using `Finset.single_le_sum (f := fun w' => |re (inf u m) w'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)`. Establish `h2 : ∑ w' : InfinitePlace F, |re (inf u m) w'| ≤ sz u` using `Finset.single_le_sum (f := fun m' => ∑ w' : InfinitePlace F, |re (inf u m') w'|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨(N : ℝ) * (Fintype.card (InfinitePlace F) : ℝ) * ((N : ℝ) * D), by positivity, fun u => ?_⟩` and prove the remaining obligations. Establish `key : ∀ l w, |re (inf (M.mulVec u) l) w| ≤ (N : ℝ) * D * sz u`.

Introduce `l w`. Rewrite using `[inf_mulVec, re_sum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun m _ => ?_` and prove the remaining obligations. Rewrite using `[re_mul, abs_mul]`.

Conclude with `mul_le_mul (hle l m w) (hs u m w) (abs_nonneg _) hD0`. Use `_ = (N : ℝ) * D * sz u := by simp [Finset.sum_const, Finset.card_univ]; ring`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Finset.sum_const, Finset.card_univ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sz_mulVec_le [IsTotallyReal F] (M : Matrix (Fin N) (Fin N) (AF F)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u, sz (M.mulVec u) ≤ A * sz u := by
  set D : ℝ := ∑ l, ∑ m, ∑ w : InfinitePlace F, |re (fstA F (M l m)) w| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∀ l m w, |re (fstA F (M l m)) w| ≤ D := by
    intro l m w
    have h1 : |re (fstA F (M l m)) w| ≤ ∑ w' : InfinitePlace F, |re (fstA F (M l m)) w'| :=
      Finset.single_le_sum (f := fun w' => |re (fstA F (M l m)) w'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ w)
    have h2 : ∑ w' : InfinitePlace F, |re (fstA F (M l m)) w'| ≤
        ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'| :=
      Finset.single_le_sum (f := fun m' => ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    have h3 : ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'| ≤ D :=
      Finset.single_le_sum (f := fun l' => ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l' m')) w'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    linarith
  have hs : ∀ (u : Fin N → AF F) m w, |re (inf u m) w| ≤ sz u := by
    intro u m w
    have h1 : |re (inf u m) w| ≤ ∑ w' : InfinitePlace F, |re (inf u m) w'| :=
      Finset.single_le_sum (f := fun w' => |re (inf u m) w'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ w)
    have h2 : ∑ w' : InfinitePlace F, |re (inf u m) w'| ≤ sz u :=
      Finset.single_le_sum (f := fun m' => ∑ w' : InfinitePlace F, |re (inf u m') w'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    linarith
  refine ⟨(N : ℝ) * (Fintype.card (InfinitePlace F) : ℝ) * ((N : ℝ) * D), by positivity, fun u => ?_⟩
  have key : ∀ l w, |re (inf (M.mulVec u) l) w| ≤ (N : ℝ) * D * sz u := by
    intro l w
    rw [inf_mulVec, re_sum]
    calc |∑ m, re (fstA F (M l m) * inf u m) w| ≤ ∑ m, |re (fstA F (M l m) * inf u m) w| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin N, D * sz u := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [re_mul, abs_mul]
          exact mul_le_mul (hle l m w) (hs u m w) (abs_nonneg _) hD0
      _ = (N : ℝ) * D * sz u := by simp [Finset.sum_const, Finset.card_univ]; ring
  calc sz (M.mulVec u) = ∑ l, ∑ w : InfinitePlace F, |re (inf (M.mulVec u) l) w| := rfl
    _ ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, (N : ℝ) * D * sz u :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ => key l w
    _ = (N : ℝ) * (Fintype.card (InfinitePlace F) : ℝ) * ((N : ℝ) * D) * sz u := by
        simp [Finset.sum_const, Finset.card_univ]; ring

/- English proof (translation)
Take `⟨hc, ⟨K, hKc, hK0⟩, hd⟩` from `hΦ`. Use `⟨hm.mul (hc.comp hf), ?_, fun k => ?_⟩` and prove the remaining obligations. Take `⟨K', hK'c, hK'⟩` from `hK K hKc`. Use `⟨K', hK'c, fun u hu => ?_⟩` and prove the remaining obligations. Establish `: fin (f u) ∉ K` using `fun h => hu (hK' u h)`.

Use `show m u * Φ (f u) = 0`. Rewrite using `[hK0 _ this, mul_zero]`. Take `⟨D, hD⟩` from `hd k`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB 0)`. Use `⟨B * (1 + A + C) ^ k * D, fun u => ?_⟩` and prove the remaining obligations.

Establish `h1 : 1 + sz u ≤ (1 + A + C) * (1 + sz (f u))`. Use `hsz u` as an intermediate fact. Use `sz_nonneg (f u)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (1 + sz u) ^ k ≤ (1 + A + C) ^ k * (1 + sz (f u)) ^ k`.

Rewrite using `[← mul_pow]; exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k`. Establish `h3` using `hD (f u)`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_right (hB u) (norm_nonneg _)) h2 (pow_nonneg (by linarith [sz_nonneg u]) _) (mul_nonneg hB0 (norm_nonneg _))` to reduce the goal to its premises.

Use `_ = B * (1 + A + C) ^ k * (‖Φ (f u)‖ * (1 + sz (f u)) ^ k) := by ring`. Use `_ ≤ B * (1 + A + C) ^ k * D := mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (pow_nonneg (by linarith) _))`.
-/
theorem decay_of_comp {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (f : (Fin N → AF F) → (Fin N → AF F))
    (hf : Continuous f) (m : (Fin N → AF F) → ℂ) (hm : Continuous m) (B : ℝ) (hB : ∀ u, ‖m u‖ ≤ B)
    (hK : ∀ K : Set (Fin N → Af F), IsCompact K →
      ∃ K' : Set (Fin N → Af F), IsCompact K' ∧ ∀ u, fin (f u) ∈ K → fin u ∈ K')
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hsz : ∀ u, sz u ≤ A * sz (f u) + C) :
    Decay fun u => m u * Φ (f u) := by
  obtain ⟨hc, ⟨K, hKc, hK0⟩, hd⟩ := hΦ
  refine ⟨hm.mul (hc.comp hf), ?_, fun k => ?_⟩
  · obtain ⟨K', hK'c, hK'⟩ := hK K hKc
    refine ⟨K', hK'c, fun u hu => ?_⟩
    have : fin (f u) ∉ K := fun h => hu (hK' u h)
    show m u * Φ (f u) = 0
    rw [hK0 _ this, mul_zero]
  · obtain ⟨D, hD⟩ := hd k
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨B * (1 + A + C) ^ k * D, fun u => ?_⟩
    have h1 : 1 + sz u ≤ (1 + A + C) * (1 + sz (f u)) := by
      have := hsz u; have := sz_nonneg (f u); nlinarith
    have h2 : (1 + sz u) ^ k ≤ (1 + A + C) ^ k * (1 + sz (f u)) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have h3 := hD (f u)
    rw [norm_mul]
    calc ‖m u‖ * ‖Φ (f u)‖ * (1 + sz u) ^ k
        ≤ B * ‖Φ (f u)‖ * ((1 + A + C) ^ k * (1 + sz (f u)) ^ k) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hB u) (norm_nonneg _)) h2
            (pow_nonneg (by linarith [sz_nonneg u]) _) (mul_nonneg hB0 (norm_nonneg _))
      _ = B * (1 + A + C) ^ k * (‖Φ (f u)‖ * (1 + sz (f u)) ^ k) := by ring
      _ ≤ B * (1 + A + C) ^ k * D :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (pow_nonneg (by linarith) _))

end GlobalTheory.SWQ

noncomputable section

namespace GlobalTheory.SWQ

/- English proof (translation)
Unfold `qd`. Use `fun_prop`.
-/
theorem continuous_qd' {F : Type} [Field F] [NumberField F] {N : ℕ} (a : Fin N → F) :
    Continuous (qd (AF F) a) := by
  unfold qd; fun_prop

/- English proof (translation)
Unfold `Bd`. Use `fun_prop`.
-/
theorem continuous_Bd_gen {F : Type} [Field F] {N : ℕ} (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] (a : Fin N → F) (y : Fin N → R) :
    Continuous fun x => Bd R a x y := by
  unfold Bd; fun_prop

/- English proof (translation)
The claim follows from `continuous_Bd_gen (AF F) a y`.
-/
theorem continuous_Bd' {F : Type} [Field F] [NumberField F] {N : ℕ} (a : Fin N → F)
    (y : Fin N → AF F) : Continuous fun x => Bd (AF F) a x y :=
  continuous_Bd_gen (AF F) a y

/- English proof (translation)
Use function extensionality and compare the values at `l`. Conclude with `RingHom.map_mulVec (sndA F).toRingHom M v l`.
-/
theorem fin_mulVec {F : Type} [Field F] [NumberField F] {N : ℕ} (M : Matrix (Fin N) (Fin N) (AF F))
    (v : Fin N → AF F) : fin (M.mulVec v) = (M.map (sndA F).toRingHom).mulVec (fin v) := by
  funext l
  exact RingHom.map_mulVec (sndA F).toRingHom M v l

/- English proof (translation)
Introduce `F _ _ N ψ lam ν a hc Φ hΦ`. Use `haveI : IsTotallyReal F := hc.1`. Establish `hψc : Continuous ψ` using `hc.2.1.1`. Establish `hψ1 : ∀ x, ‖ψ x‖ = 1` using `hc.2.1.2.1`. Establish `hGL : ∀ g : GL (Fin N) (AF F), Decay fun u => Φ ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u)`.

Introduce `g`. Establish `hinv : ((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F)) * (g : Matrix _ _ _) = 1` using `Units.inv_mul g`. Take `⟨A, hA, hAle⟩` from `sz_mulVec_le ((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F))`. Establish `h` using `decay_of_comp hΦ (fun u => (g : Matrix (Fin N) (Fin N) (AF F)).mulVec u) (continuous_const.matrix_mulVec continuous_id) (fun _ => (1 : ℂ)) continuous_const 1 (by simp) ?_ A 0 hA le_rfl ?_`. Simplify using `using h`.

Introduce `K hK`. Use `⟨(fun z => (((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F)).map (sndA F).toRingHom).mulVec z) '' K, hK.image (continuous_const.matrix_mulVec continuous_id), fun u hu => ⟨_, hu, ?_⟩⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[fin_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Introduce `u`.

Establish `h` using `hAle ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u)`. Rewrite `h` using `[Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun b => ?_, fun x y => ?_, fun t ht => ?_, fun c => ?_, hGL⟩` and prove the remaining obligations. Conclude with `decay_of_comp hΦ id continuous_id (fun u => ψ (b * qd (AF F) a u)) (hψc.comp (continuous_const.mul (continuous_qd' a))) 1 (fun u => (hψ1 _).le) (fun K hK => ⟨K, hK, fun u h => h⟩) 1 0 zero_le_one le_rfl (fun u => by simp)`.

Conclude with `decay_of_comp hΦ (fun u => u + x) (continuous_id.add continuous_const) (fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y)) (hψc.comp ((continuous_Bd' a y).add continuous_const)) 1 (fun u => (hψ1 _).le) (fun K hK => ⟨(fun z => z - fin x) '' K, hK.image ( …`. Establish `h1` using `sz_add_le (u + x) (-x)`. Rewrite `h1` using `[sz_neg, add_neg_cancel_right]`. Use the proof step `linarith)`. Set `g : GL (Fin N) (AF F)` to `Units.map (Matrix.scalar (Fin N) : AF F →+* Matrix (Fin N) (Fin N) (AF F)).toMonoidHom ht.unit`.

Establish `h` using `hGL g`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using `only [Da]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Simplify using `[g, Matrix.mulVec_diagonal]`. Establish `h` using `decay_of_comp hΦ id continuous_id (fun _ => c) continuous_const ‖c‖ (fun _ => le_rfl) (fun K hK => ⟨K, hK, fun u h => h⟩) 1 0 zero_le_one le_rfl (fun u => by simp)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`.

Simplify using the standard rewrite rules.
-/
theorem decay_ops : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → (∀ b, Decay (Ub ψ a b Φ)) ∧ (∀ x y, Decay (rho ψ a x y Φ)) ∧
      (∀ t : AF F, IsUnit t → Decay (Da t Φ)) ∧ (∀ c : ℂ, Decay (c • Φ)) ∧
      ∀ g : GL (Fin N) (AF F), Decay fun u => Φ ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u) := by
  intro F _ _ N ψ lam ν a hc Φ hΦ
  haveI : IsTotallyReal F := hc.1
  have hψc : Continuous ψ := hc.2.1.1
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hc.2.1.2.1
  have hGL : ∀ g : GL (Fin N) (AF F), Decay fun u => Φ ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u) := by
    intro g
    have hinv : ((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F)) * (g : Matrix _ _ _) = 1 :=
      Units.inv_mul g
    obtain ⟨A, hA, hAle⟩ := sz_mulVec_le ((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F))
    have h := decay_of_comp hΦ (fun u => (g : Matrix (Fin N) (Fin N) (AF F)).mulVec u)
      (continuous_const.matrix_mulVec continuous_id) (fun _ => (1 : ℂ)) continuous_const 1 (by simp) ?_
      A 0 hA le_rfl ?_
    · simpa using h
    · intro K hK
      refine ⟨(fun z => (((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F)).map
          (sndA F).toRingHom).mulVec z) '' K,
        hK.image (continuous_const.matrix_mulVec continuous_id), fun u hu => ⟨_, hu, ?_⟩⟩
      simp only
      rw [fin_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    · intro u
      have h := hAle ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u)
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h
      linarith
  refine ⟨fun b => ?_, fun x y => ?_, fun t ht => ?_, fun c => ?_, hGL⟩
  · exact decay_of_comp hΦ id continuous_id (fun u => ψ (b * qd (AF F) a u))
      (hψc.comp (continuous_const.mul (continuous_qd' a))) 1 (fun u => (hψ1 _).le)
      (fun K hK => ⟨K, hK, fun u h => h⟩) 1 0 zero_le_one le_rfl (fun u => by simp)
  · exact decay_of_comp hΦ (fun u => u + x) (continuous_id.add continuous_const)
      (fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y))
      (hψc.comp ((continuous_Bd' a y).add continuous_const)) 1 (fun u => (hψ1 _).le)
      (fun K hK => ⟨(fun z => z - fin x) '' K, hK.image (continuous_sub_right _),
        fun u hu => ⟨_, hu, by simp only [fin_add, add_sub_cancel_right]⟩⟩)
      1 (sz x) zero_le_one (sz_nonneg x) (fun u => by
        have h1 := sz_add_le (u + x) (-x)
        rw [sz_neg, add_neg_cancel_right] at h1
        linarith)
  · let g : GL (Fin N) (AF F) := Units.map (Matrix.scalar (Fin N) : AF F →+* Matrix (Fin N) (Fin N) (AF F)).toMonoidHom ht.unit
    have h := hGL g
    convert h using 1
    funext u
    simp only [Da]
    congr 1
    funext l
    simp [g, Matrix.mulVec_diagonal]
  · have h := decay_of_comp hΦ id continuous_id (fun _ => c) continuous_const ‖c‖ (fun _ => le_rfl)
      (fun K hK => ⟨K, hK, fun u h => h⟩) 1 0 zero_le_one le_rfl (fun u => by simp)
    convert h using 1
    funext u
    simp

end GlobalTheory.SWQ
