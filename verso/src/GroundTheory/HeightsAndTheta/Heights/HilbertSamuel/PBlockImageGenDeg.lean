import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenFibreHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHeightsirationalHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolySandwich
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff diffStep eventualValue intNum)
open fwdDiff

/- English proof (translation)
Proceed by induction on `D generalizing t with`. Consider the case `zero => simp [mixedDiff]`. Consider the case `succ D ih`. Establish `hs : mixedDiff (fun _ : Fin (D + 1) => b) h = diffStep b (mixedDiff (fun _ : Fin D => b) h)`. Simplify using `[mixedDiff, List.ofFn_succ]`.

Establish `h1 : m₀ + t • b - b = m₀ + (t - 1) • b` using `by rw [sub_smul, one_smul, add_sub_assoc]`. Establish `e1 : t - ((D + 1 : ℕ) : ℤ) + 1 = t - D` using `by push_cast; ring`. Establish `e2 : t - ((D + 1 : ℕ) : ℤ) = t - 1 - D` using `by push_cast; ring`. Rewrite using `[hs, diffStep, h1, ih, ih, Function.iterate_succ_apply', fwdDiff, e1, e2]`.
-/
theorem mixedDiff_line {K : Type*} (b m₀ : K → ℤ) (h : (K → ℤ) → ℤ) (D : ℕ) (t : ℤ) :
    mixedDiff (fun _ : Fin D => b) h (m₀ + t • b) = ((fwdDiff 1)^[D] fun s : ℤ => h (m₀ + s • b)) (t - D) := by
  induction D generalizing t with
  | zero => simp [mixedDiff]
  | succ D ih =>
    have hs : mixedDiff (fun _ : Fin (D + 1) => b) h = diffStep b (mixedDiff (fun _ : Fin D => b) h) := by
      simp [mixedDiff, List.ofFn_succ]
    have h1 : m₀ + t • b - b = m₀ + (t - 1) • b := by rw [sub_smul, one_smul, add_sub_assoc]
    have e1 : t - ((D + 1 : ℕ) : ℤ) + 1 = t - D := by push_cast; ring
    have e2 : t - ((D + 1 : ℕ) : ℤ) = t - 1 - D := by push_cast; ring
    rw [hs, diffStep, h1, ih, ih, Function.iterate_succ_apply', fwdDiff, e1, e2]

/- English proof (translation)
Rewrite using `[fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]`. Use `push_cast`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j ≤ D` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Simplify using `only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]`.

Rewrite using `[h j hj']`.
-/
theorem fwdDiff_iter_eq_poly (φ : ℤ → ℤ) (q : Polynomial ℚ) (D : ℕ) (s : ℤ)
    (h : ∀ j ≤ D, (φ (s + j) : ℚ) = q.eval ((s : ℚ) + j)) :
    (((fwdDiff 1)^[D] φ) s : ℚ) = ((fwdDiff 1)^[D] q.eval) (s : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  rw [h j hj']

/- English proof (translation)
Break down `hq.lt_or_eq with h | h` into its components or cases. Rewrite using `[Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]`. Simplify using the standard rewrite rules. Substitute `h` using the available equality. Rewrite using `[q.fwdDiff_iter_degree_eq_factorial]`.

Rewrite using `[Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem fwdDiff_iter_poly (q : Polynomial ℚ) {D : ℕ} (hq : q.natDegree ≤ D) (x : ℚ) :
    ((fwdDiff 1)^[D] q.eval) x = q.coeff D * D.factorial := by
  rcases hq.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [q.fwdDiff_iter_degree_eq_factorial]
    rw [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rfl

def lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => if k = k₀ then Polynomial.X else Polynomial.C (m k)) p

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [lineRestr]`. Consider the case `add p q hp hq => simp only [lineRestr, map_add, Polynomial.eval_add] at *`. Rewrite using `[hp, hq]`. Consider the case `mul_X p k hp`.

Simplify using `only [lineRestr, map_mul, Polynomial.eval_mul] at *`. Rewrite using `[hp]`. Apply the tactic sequence `by_cases hk : k = k₀ <;> simp [hk]`.
-/
theorem eval_lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) (t : ℚ) :
    (lineRestr p k₀ m).eval t = MvPolynomial.eval (fun k => if k = k₀ then t else m k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add, Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    by_cases hk : k = k₀ <;> simp [hk]

/- English proof (translation)
Rewrite using `[lineRestr]`. Use `conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]`.

Use `(Polynomial.natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations. Use `(Polynomial.natDegree_prod_le _ _).trans ?_` and prove the remaining obligations. Use `le_trans ?_ (MvPolynomial.le_totalDegree hs)` and prove the remaining obligations. Use `Finset.sum_le_sum fun k _ => (Polynomial.natDegree_pow_le).trans ?_` and prove the remaining obligations. Apply the tactic sequence `have : (if k = k₀ then (Polynomial.X : Polynomial ℚ) else Polynomial.C (m k)).natDegree ≤ 1 := by split_ifs <;> simp`.

Simplify using `using Nat.mul_le_mul_left (s k) this`.
-/
theorem natDegree_lineRestr_le {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) :
    (lineRestr p k₀ m).natDegree ≤ p.totalDegree := by
  rw [lineRestr]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum fun k _ => (Polynomial.natDegree_pow_le).trans ?_
  have : (if k = k₀ then (Polynomial.X : Polynomial ℚ) else Polynomial.C (m k)).natDegree ≤ 1 := by
    split_ifs <;> simp
  simpa using Nat.mul_le_mul_left (s k) this

/- English proof (translation)
Establish `hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c`. Take `⟨m, hm⟩` from `h.exists`. Conclude with `⟨f m, h.mono fun m' hm' => by exact_mod_cast hm'.trans hm.symm⟩`. Unfold `eventualValue`. Rewrite using `[dif_pos hex]`.

Take `⟨m, hm1, hm2⟩` from `(hex.choose_spec.and h).exists`. Rewrite using `[← hm1]`. Conclude with `hm2`.
-/
theorem eventualValue_eq {K : Type*} (f : (K → ℤ) → ℤ) (e : ℚ) (h : ∀ᶠ m in Filter.atTop, (f m : ℚ) = e) :
    (eventualValue f : ℚ) = e := by
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := by
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨f m, h.mono fun m' hm' => by exact_mod_cast hm'.trans hm.symm⟩
  unfold eventualValue
  rw [dif_pos hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  rw [← hm1]
  exact hm2

end BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff eventualValue) in
open BlockImageGenDeg in

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hA hB hI`. Use `set PY := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPY`. Use `set PX := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPX`. Take `⟨⟨hprime, -, hrel⟩, hdim⟩` from `hGFV K ι Ω y D hA`. Take `⟨pY, a₀, hdeg, hpY⟩` from `hMHP ℚ K ι PY D ⟨hprime, hHom K ι Ω y, hrel⟩ hdim`.

Establish `hXhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal (ι` using `GlobalTheory κ) PX := by`. Rewrite using `[hPX, coordIdeal_eq_mCoordIdeal]`. Conclude with `hHom Unit (GlobalTheory κ) Ω x`. Take `⟨pX, hpX⟩` from `hHEP ℚ Unit (GlobalTheory κ) PX hXhom`. Take `⟨aX, haX⟩` from `Filter.eventually_atTop.mp hpX`.

Use `set p₁ := lineRestr pX () 0 with hp₁`. Establish `hX1 : ∀ n : ℕ, (aX ()).toNat ≤ n → (hilbFn PX (fun _ => (n : ℤ)) : ℚ) = p₁.eval (n : ℚ)`. Introduce `n hn`. Rewrite using `[haX (fun _ => (n : ℤ)) (fun u => by cases u; show aX () ≤ (n : ℤ); omega), hp₁, eval_lineRestr]`. Simplify using the standard rewrite rules.

Establish `hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hA.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `show mConeMap y (X ⟨k, i⟩) = 0`.

Simplify using `[mConeMap, h0]`. Establish `hY1 : ∀ (m : K → ℕ) (s : ℕ), (∀ k, k ≠ k₀ → a₀ ≤ m k) → a₀ ≤ s → (hilbFn PY (fun k => if k = k₀ then (s : ℤ) else m k) : ℚ) = (lineRestr pY k₀ fun k => (m k : ℚ)).eval (s : ℚ)`. Introduce `m s hm hs`. Use `hpY (fun k => if k = k₀ then s else m k) fun k => by` as an intermediate fact. Apply the tactic sequence `by_cases hk : k = k₀ <;> simp [hk, hs, hm k]`.

Rewrite using `[eval_lineRestr]`. Apply the tactic sequence `convert this using 3 <;> (funext k; by_cases hk : k = k₀ <;> simp [hk])`. Establish `hsand : ∀ m : K → ℕ, (∀ k, k ≠ k₀ → a₀ ≤ m k) → p₁.natDegree ≤ D ∧ p₁.coeff D = (lineRestr pY k₀ fun k => (m k : ℚ)).coeff D`. Introduce `m hm`. Take `⟨c, hc⟩` from `hBir K ι Ω y k₀ hnz hB m`.

Use `hSand D c _ _ ((natDegree_lineRestr_le _ _ _).trans hdeg) ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop (max a₀ (aX ()).toNat)] with n hn`. Establish `h1` using `hX1 n (le_of_max_le_right hn)`. Establish `h2` using `hX1 (n + c) ((le_of_max_le_right hn).trans (Nat.le_add_right _ _))`. Rewrite `h1`, `h2` using `[hImg K ι Ω κ y k₀ M N x hI]`.

Rewrite using `[← hY1 m n hm (le_of_max_le_left hn)]`. Move the coercions through the operations in `at h2`. Rewrite using `[← h1, ← h2]`. Conclude with `⟨by exact_mod_cast (hc n).1, by exact_mod_cast (hc n).2⟩`. Establish `hdegX : p₁.natDegree ≤ D` using `(hsand (fun _ => a₀) fun _ _ => le_rfl).1`.

Establish `key : (eventualValue (mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (hilbFn PX)) : ℚ) = eventualValue (mixedDiff (fun _ : Fin D => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) (hilbFn PY))`. Rewrite using `[eventualValue_eq (e := p₁.coeff D * D.factorial), eventualValue_eq (e := p₁.coeff D * D.factorial)]`. Rewrite using `[Filter.eventually_atTop]`. Use `⟨fun _ => ((a₀ : ℤ) + D), fun m hm => ?_⟩` and prove the remaining obligations. Establish `hm' : ∀ k, (a₀ : ℤ) + D ≤ m k` using `hm`.

Establish `hline : m = (fun k => if k = k₀ then 0 else m k) + m k₀ • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀`. Apply the tactic sequence `funext k; by_cases hk : k = k₀ <;> simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]`. Rewrite using `[hline, mixedDiff_line, fwdDiff_iter_eq_poly _ (lineRestr pY k₀ fun k => ((m k).toNat : ℚ)) D, fwdDiff_iter_poly _ ((natDegree_lineRestr_le _ _ _).trans hdeg), (hsand (fun k => (m k).toNat) fun k _ => by have := hm' k; omega).2]`. Introduce `j hj`. Establish `hs : 0 ≤ m k₀ - D + j` using `by have := hm' k₀; omega`.

Establish `hkey : (fun k => if k = k₀ then 0 else m k) + (m k₀ - D + j) • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ = fun k => if k = k₀ then (((m k₀ - D + j).toNat : ℕ) : ℤ) else (((m k).toNat : ℕ) : ℤ)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = k₀`. Simplify using `[hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Int.toNat_of_nonneg hs]`. Use `hm' k` as an intermediate fact.

Simplify using `[hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hkey, hY1 (fun k => (m k).toNat) _ (fun k _ => by have := hm' k; omega) (by have := hm' k₀; omega)]`. Use `congr 1`. Rewrite using `[show (((m k₀ - D + j).toNat : ℕ) : ℚ) = ((m k₀ - D + j : ℤ) : ℚ) by`.

Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hs]]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Filter.eventually_atTop]`. Use `⟨fun _ => ((aX ()).toNat + D : ℤ), fun m hm => ?_⟩` and prove the remaining obligations.

Establish `hm' : ((aX ()).toNat + D : ℤ) ≤ m ()` using `hm ()`. Establish `hline : m = 0 + m () • (1 : Unit → ℤ)` using `by funext u; cases u; simp`. Rewrite using `[hline, mixedDiff_line, fwdDiff_iter_eq_poly _ p₁ D, fwdDiff_iter_poly _ hdegX]`. Introduce `j hj`. Establish `hs : 0 ≤ m () - D + j` using `by omega`.

Establish `hkey : (0 : Unit → ℤ) + (m () - D + j) • (1 : Unit → ℤ) = fun _ => (((m () - D + j).toNat : ℕ) : ℤ)`. Use function extensionality and compare the values at `u`. Simplify using `[Int.toNat_of_nonneg hs]`. Rewrite using `[hkey, hX1 _ (by omega)]`. Use `congr 1`.

Rewrite using `[show (((m () - D + j).toNat : ℕ) : ℚ) = ((m () - D + j : ℤ) : ℚ) by`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hs]]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises.

Unfold `genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum`. Apply the tactic sequence `convert key using 6 <;> rfl`.
-/
theorem BlockImageGenDeg.proof (hMHP : MultigradedHilbertPolynomial.Statement.{0})
    (hGFV : GenericFibreVar.Statement) (hHEP : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement.{0})
    (hHom : GenFibreHomog.Statement) (hImg : BlockImageHilb.Statement) (hBir : BlockBirationalHilbert.Statement)
    (hSand : PolySandwich.Statement) : BlockImageGenDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hA hB hI
  set PY := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPY
  set PX := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPX

  obtain ⟨⟨hprime, -, hrel⟩, hdim⟩ := hGFV K ι Ω y D hA
  obtain ⟨pY, a₀, hdeg, hpY⟩ := hMHP ℚ K ι PY D ⟨hprime, hHom K ι Ω y, hrel⟩ hdim

  have hXhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal (ι := GlobalTheory κ) PX := by
    rw [hPX, coordIdeal_eq_mCoordIdeal]; exact hHom Unit (GlobalTheory κ) Ω x
  obtain ⟨pX, hpX⟩ := hHEP ℚ Unit (GlobalTheory κ) PX hXhom
  obtain ⟨aX, haX⟩ := Filter.eventually_atTop.mp hpX
  set p₁ := lineRestr pX () 0 with hp₁
  have hX1 : ∀ n : ℕ, (aX ()).toNat ≤ n → (hilbFn PX (fun _ => (n : ℤ)) : ℚ) = p₁.eval (n : ℚ) := by
    intro n hn
    rw [haX (fun _ => (n : ℤ)) (fun u => by cases u; show aX () ≤ (n : ℤ); omega), hp₁, eval_lineRestr]
    simp

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]

  have hY1 : ∀ (m : K → ℕ) (s : ℕ), (∀ k, k ≠ k₀ → a₀ ≤ m k) → a₀ ≤ s →
      (hilbFn PY (fun k => if k = k₀ then (s : ℤ) else m k) : ℚ) =
        (lineRestr pY k₀ fun k => (m k : ℚ)).eval (s : ℚ) := by
    intro m s hm hs
    have := hpY (fun k => if k = k₀ then s else m k) fun k => by
      by_cases hk : k = k₀ <;> simp [hk, hs, hm k]
    rw [eval_lineRestr]
    convert this using 3 <;> (funext k; by_cases hk : k = k₀ <;> simp [hk])

  have hsand : ∀ m : K → ℕ, (∀ k, k ≠ k₀ → a₀ ≤ m k) →
      p₁.natDegree ≤ D ∧ p₁.coeff D = (lineRestr pY k₀ fun k => (m k : ℚ)).coeff D := by
    intro m hm
    obtain ⟨c, hc⟩ := hBir K ι Ω y k₀ hnz hB m
    refine hSand D c _ _ ((natDegree_lineRestr_le _ _ _).trans hdeg) ?_
    filter_upwards [Filter.eventually_ge_atTop (max a₀ (aX ()).toNat)] with n hn
    have h1 := hX1 n (le_of_max_le_right hn)
    have h2 := hX1 (n + c) ((le_of_max_le_right hn).trans (Nat.le_add_right _ _))
    rw [hImg K ι Ω κ y k₀ M N x hI] at h1 h2
    rw [← hY1 m n hm (le_of_max_le_left hn)]
    push_cast at h2
    rw [← h1, ← h2]
    exact ⟨by exact_mod_cast (hc n).1, by exact_mod_cast (hc n).2⟩
  have hdegX : p₁.natDegree ≤ D := (hsand (fun _ => a₀) fun _ _ => le_rfl).1

  have key : (eventualValue (mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (hilbFn PX)) : ℚ) =
      eventualValue (mixedDiff (fun _ : Fin D => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) (hilbFn PY)) := by
    rw [eventualValue_eq (e := p₁.coeff D * D.factorial), eventualValue_eq (e := p₁.coeff D * D.factorial)]
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((a₀ : ℤ) + D), fun m hm => ?_⟩
      have hm' : ∀ k, (a₀ : ℤ) + D ≤ m k := hm
      have hline : m = (fun k => if k = k₀ then 0 else m k) + m k₀ • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ := by
        funext k; by_cases hk : k = k₀ <;> simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ (lineRestr pY k₀ fun k => ((m k).toNat : ℚ)) D,
        fwdDiff_iter_poly _ ((natDegree_lineRestr_le _ _ _).trans hdeg),
        (hsand (fun k => (m k).toNat) fun k _ => by have := hm' k; omega).2]
      intro j hj
      have hs : 0 ≤ m k₀ - D + j := by have := hm' k₀; omega
      have hkey : (fun k => if k = k₀ then 0 else m k) + (m k₀ - D + j) • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ =
          fun k => if k = k₀ then (((m k₀ - D + j).toNat : ℕ) : ℤ) else (((m k).toNat : ℕ) : ℤ) := by
        funext k
        by_cases hk : k = k₀
        · simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Int.toNat_of_nonneg hs]
        · have := hm' k
          simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
          omega
      rw [hkey, hY1 (fun k => (m k).toNat) _ (fun k _ => by have := hm' k; omega) (by have := hm' k₀; omega)]
      congr 1
      rw [show (((m k₀ - D + j).toNat : ℕ) : ℚ) = ((m k₀ - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((aX ()).toNat + D : ℤ), fun m hm => ?_⟩
      have hm' : ((aX ()).toNat + D : ℤ) ≤ m () := hm ()
      have hline : m = 0 + m () • (1 : Unit → ℤ) := by funext u; cases u; simp
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ p₁ D, fwdDiff_iter_poly _ hdegX]
      intro j hj
      have hs : 0 ≤ m () - D + j := by omega
      have hkey : (0 : Unit → ℤ) + (m () - D + j) • (1 : Unit → ℤ) = fun _ => (((m () - D + j).toNat : ℕ) : ℤ) := by
        funext u; simp [Int.toNat_of_nonneg hs]
      rw [hkey, hX1 _ (by omega)]
      congr 1
      rw [show (((m () - D + j).toNat : ℕ) : ℚ) = ((m () - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring

  apply Int.cast_injective (α := ℚ)
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  convert key using 6 <;> rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
