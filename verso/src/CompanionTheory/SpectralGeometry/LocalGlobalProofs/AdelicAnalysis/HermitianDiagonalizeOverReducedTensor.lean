import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.QuadFiniteDimensional

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HermDiagonal

open HeckeCharacterZeroLocus.SiegelWeilU Matrix
open scoped TensorProduct

section SemiLocal

variable {B : Type} [CommRing B]

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Take `⟨M, hM, ha⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)`. Conclude with `h ⟨M, hM⟩ ha`.
-/
theorem isUnit_of_forall_notMem {a : B} (h : ∀ m : MaximalSpectrum B, a ∉ m.asIdeal) : IsUnit a := by
  by_contra hu
  obtain ⟨M, hM, ha⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
  exact h ⟨M, hM⟩ ha

/- English proof (translation)
Establish `hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum B => m.asIdeal)`. Introduce `m m' hne`. Use `Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne m.isMaximal m'.isMaximal ?_)` and prove the remaining obligations. Conclude with `fun h => hne (MaximalSpectrum.ext h)`. Take `⟨c, hc⟩` from `Ideal.pi_quotient_surjective hcop fun m => Ideal.Quotient.mk m.asIdeal (y m)`.

Conclude with `⟨c, fun m => Ideal.Quotient.eq.1 (hc m)⟩`.
-/
theorem exists_crt [Finite (MaximalSpectrum B)] (y : MaximalSpectrum B → B) :
    ∃ c : B, ∀ m : MaximalSpectrum B, c - y m ∈ m.asIdeal := by
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum B => m.asIdeal) := by
    intro m m' hne
    refine Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne m.isMaximal m'.isMaximal ?_)
    exact fun h => hne (MaximalSpectrum.ext h)
  obtain ⟨c, hc⟩ := Ideal.pi_quotient_surjective hcop fun m => Ideal.Quotient.mk m.asIdeal (y m)
  exact ⟨c, fun m => Ideal.Quotient.eq.1 (hc m)⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `choose C hC using fun i : ι => exists_crt (B := B) fun m => if x i0 ∈ m.asIdeal then l i else 0`. Use `⟨Function.update C i0 1, by simp, isUnit_of_forall_notMem fun m hm => ?_⟩` and prove the remaining obligations. Establish `hsplit : ∑ i, Function.update C i0 1 i * x i = x i0 + ∑ i ∈ Finset.univ.erase i0, C i * x i`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]`. Simplify using `only [Function.update_self, one_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hi)]`. Rewrite `hm` using `[hsplit]`. Distinguish the cases in `hx : x i0 ∈ m.asIdeal`.

Establish `h1 : ∀ i, C i - l i ∈ m.asIdeal` using `fun i => by simpa [hx] using hC i m`. Establish `h2 : ∑ i ∈ Finset.univ.erase i0, (C i - l i) * x i ∈ m.asIdeal` using `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (h1 i)`. Establish `h3 : (1 : B) = (x i0 + ∑ i ∈ Finset.univ.erase i0, C i * x i) + l i0 * x i0 - x i0 - ∑ i ∈ Finset.univ.erase i0, (C i - l i) * x i`. Rewrite using `[← h, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: (1 : B) ∈ m.asIdeal`. Rewrite using `[h3]`. Conclude with `Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.add_mem _ hm (Ideal.mul_mem_left _ _ hx)) hx) h2`. Conclude with `m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 this)`.

Establish `h1 : ∀ i, C i ∈ m.asIdeal` using `fun i => by simpa [hx] using hC i m`. Establish `h2 : ∑ i ∈ Finset.univ.erase i0, C i * x i ∈ m.asIdeal` using `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (h1 i)`. Conclude with `hx ((Ideal.add_mem_iff_left _ h2).1 hm)`.
-/
theorem exists_unit_comb [Finite (MaximalSpectrum B)] (i0 : ι) (x l : ι → B)
    (h : ∑ i, l i * x i = 1) : ∃ c : ι → B, c i0 = 1 ∧ IsUnit (∑ i, c i * x i) := by
  classical
  choose C hC using fun i : ι =>
    exists_crt (B := B) fun m => if x i0 ∈ m.asIdeal then l i else 0
  refine ⟨Function.update C i0 1, by simp, isUnit_of_forall_notMem fun m hm => ?_⟩
  have hsplit : ∑ i, Function.update C i0 1 i * x i
      = x i0 + ∑ i ∈ Finset.univ.erase i0, C i * x i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    simp only [Function.update_self, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hsplit] at hm
  by_cases hx : x i0 ∈ m.asIdeal
  · have h1 : ∀ i, C i - l i ∈ m.asIdeal := fun i => by simpa [hx] using hC i m
    have h2 : ∑ i ∈ Finset.univ.erase i0, (C i - l i) * x i ∈ m.asIdeal :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (h1 i)
    have h3 : (1 : B) = (x i0 + ∑ i ∈ Finset.univ.erase i0, C i * x i) + l i0 * x i0 - x i0
        - ∑ i ∈ Finset.univ.erase i0, (C i - l i) * x i := by
      rw [← h, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have : (1 : B) ∈ m.asIdeal := by
      rw [h3]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.add_mem _ hm (Ideal.mul_mem_left _ _ hx)) hx) h2
    exact m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · have h1 : ∀ i, C i ∈ m.asIdeal := fun i => by simpa [hx] using hC i m
    have h2 : ∑ i ∈ Finset.univ.erase i0, C i * x i ∈ m.asIdeal :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (h1 i)
    exact hx ((Ideal.add_mem_iff_left _ h2).1 hm)

/- English proof (translation)
Take `⟨c, hc, hu⟩` from `exists_unit_comb i0 x l h`. Use `set p : Matrix ι ι B := (1 : Matrix ι ι B).updateRow i0 c with hp`. Establish `hdp : p.det = 1`. Use `Matrix.det_updateRow_sum (1 : Matrix ι ι B) i0 c` as an intermediate fact. Establish `hc' : ∑ k, c k • (1 : Matrix ι ι B) k = c`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Matrix.one_apply]`. Rewrite `this` using `[hc']`. Simplify `this` using `[hc]`. Use `set y := p *ᵥ x with hy`.

Establish `hy0 : y i0 = ∑ i, c i * x i`. Simplify using `[hy, hp, Matrix.mulVec, dotProduct, Matrix.updateRow_self]`. Use `set q : Matrix ι ι B := (1 : Matrix ι ι B).updateCol i0 y with hq`. Establish `hdq : q.det = y i0`. Use `Matrix.det_updateCol_sum (1 : Matrix ι ι B) i0 y` as an intermediate fact.

Establish `hc' : (fun k => ∑ i, y i • (1 : Matrix ι ι B) k i) = y`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.one_apply]`. Rewrite `this` using `[hc']`. Simplify using `using this`.

Establish `hpu : IsUnit p.det` using `by rw [hdp]; exact isUnit_one`. Use `⟨p⁻¹ * q, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, hdq, hy0]`. Conclude with `((Matrix.isUnit_nonsing_inv_det_iff).2 hpu).mul hu`. Establish `h1 : ∀ j, q j i0 = y j` using `fun j => by simp [hq, Matrix.updateCol_self]`.

Establish `h2 : (p⁻¹ * q) i i0 = (p⁻¹ *ᵥ y) i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, h1]`. Rewrite using `[h2, hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hpu, Matrix.one_mulVec]`.
-/
theorem exists_col [Finite (MaximalSpectrum B)] (i0 : ι) (x l : ι → B)
    (h : ∑ i, l i * x i = 1) : ∃ g : Matrix ι ι B, IsUnit g.det ∧ ∀ i, g i i0 = x i := by
  obtain ⟨c, hc, hu⟩ := exists_unit_comb i0 x l h
  set p : Matrix ι ι B := (1 : Matrix ι ι B).updateRow i0 c with hp
  have hdp : p.det = 1 := by
    have := Matrix.det_updateRow_sum (1 : Matrix ι ι B) i0 c
    have hc' : ∑ k, c k • (1 : Matrix ι ι B) k = c := by
      funext j
      simp [Finset.sum_apply, Matrix.one_apply]
    rw [hc'] at this
    simpa [hc] using this
  set y := p *ᵥ x with hy
  have hy0 : y i0 = ∑ i, c i * x i := by
    simp [hy, hp, Matrix.mulVec, dotProduct, Matrix.updateRow_self]
  set q : Matrix ι ι B := (1 : Matrix ι ι B).updateCol i0 y with hq
  have hdq : q.det = y i0 := by
    have := Matrix.det_updateCol_sum (1 : Matrix ι ι B) i0 y
    have hc' : (fun k => ∑ i, y i • (1 : Matrix ι ι B) k i) = y := by
      funext j
      simp [Matrix.one_apply]
    rw [hc'] at this
    simpa using this
  have hpu : IsUnit p.det := by rw [hdp]; exact isUnit_one
  refine ⟨p⁻¹ * q, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul, hdq, hy0]
    exact ((Matrix.isUnit_nonsing_inv_det_iff).2 hpu).mul hu
  · have h1 : ∀ j, q j i0 = y j := fun j => by simp [hq, Matrix.updateCol_self]
    have h2 : (p⁻¹ * q) i i0 = (p⁻¹ *ᵥ y) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, h1]
    rw [h2, hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hpu, Matrix.one_mulVec]

end SemiLocal

section Form

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (s : A →+* A)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def bf (S : Matrix ι ι A) (x y : ι → A) : A := (fun i => s (x i)) ⬝ᵥ (S *ᵥ y)

variable {s}

/- English proof (translation)
Simplify using `only [bf, Pi.add_apply, map_add]`. Conclude with `add_dotProduct _ _ _`.
-/
theorem bf_add_left (S : Matrix ι ι A) (x x' y : ι → A) :
    bf s S (x + x') y = bf s S x y + bf s S x' y := by
  simp only [bf, Pi.add_apply, map_add]
  exact add_dotProduct _ _ _

/- English proof (translation)
Simplify using `only [bf, mulVec_add, dotProduct_add]`.
-/
theorem bf_add_right (S : Matrix ι ι A) (x y y' : ι → A) :
    bf s S x (y + y') = bf s S x y + bf s S x y' := by
  simp only [bf, mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [bf, Pi.smul_apply, smul_eq_mul, map_mul, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
theorem bf_smul_left (S : Matrix ι ι A) (a : A) (x y : ι → A) :
    bf s S (a • x) y = s a * bf s S x y := by
  simp only [bf, Pi.smul_apply, smul_eq_mul, map_mul, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [bf, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem bf_smul_right (S : Matrix ι ι A) (a : A) (x y : ι → A) :
    bf s S x (a • y) = a * bf s S x y := by
  simp only [bf, mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp [bf]`. Consider the case `insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_left, ih]`.
-/
theorem bf_sum_left {κ : Type} (T : Finset κ) (S : Matrix ι ι A) (f : κ → ι → A) (y : ι → A) :
    bf s S (∑ k ∈ T, f k) y = ∑ k ∈ T, bf s S (f k) y := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [bf]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_left, ih]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp [bf]`. Consider the case `insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_right, ih]`.
-/
theorem bf_sum_right {κ : Type} (T : Finset κ) (S : Matrix ι ι A) (x : ι → A) (f : κ → ι → A) :
    bf s S x (∑ k ∈ T, f k) = ∑ k ∈ T, bf s S x (f k) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [bf]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_right, ih]

/- English proof (translation)
Establish `h : (fun k => s ((Pi.single i (1 : A) : ι → A) k)) = Pi.single i 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hk]`. Simplify using `only [bf, h, mulVec_single_one, single_one_dotProduct, col_apply]`.
-/
theorem bf_single (S : Matrix ι ι A) (i j : ι) :
    bf s S (Pi.single i 1) (Pi.single j 1) = S i j := by
  have h : (fun k => s ((Pi.single i (1 : A) : ι → A) k)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  simp only [bf, h, mulVec_single_one, single_one_dotProduct, col_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cT_apply {l m : Type} (S : Matrix l m A) (i : m) (j : l) : cT s S i j = s (S j i) := rfl

/- English proof (translation)
Establish `hS' : ∀ i j, s (S i j) = S j i` using `fun i j => by rw [← cT_apply, hS]`. Simplify using `only [bf, dotProduct, mulVec, map_sum, map_mul, hs, hS', Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem bf_conj (hs : ∀ z, s (s z) = z) {S : Matrix ι ι A} (hS : cT s S = S) (x y : ι → A) :
    s (bf s S x y) = bf s S y x := by
  have hS' : ∀ i j, s (S i j) = S j i := fun i j => by rw [← cT_apply, hS]
  simp only [bf, dotProduct, mulVec, map_sum, map_mul, hs, hS', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `pol : ∀ x y, bf s S x y + bf s S y x ∈ I` using `fun x y => by`. Establish `h` using `I.sub_mem (I.sub_mem (hv (x + y)) (hv x)) (hv y)`. Establish `e : bf s S (x + y) (x + y) - bf s S x x - bf s S y y = bf s S x y + bf s S y x`. Simplify using `only [bf_add_left, bf_add_right]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `h1` using `pol (Pi.single i 1) (Pi.single j 1)`. Establish `h3` using `pol (Pi.single i 1) (θ • Pi.single j 1)`. Rewrite `h1` using `[bf_single, bf_single]`. Rewrite `h3` using `[bf_smul_right, bf_smul_left, hsθ, bf_single, bf_single]`.

Establish `h4 : θ * (S i j - S j i) ∈ I`. Establish `e : θ * (S i j - S j i) = θ * S i j + -θ * S j i` using `by ring`. Rewrite using `[e]` and apply the resulting hypothesis. Establish `h5 : S i j - S j i ∈ I` using `(Ideal.unit_mul_mem_iff_mem I hθ).1 h4`. Establish `h6 : 2 * S i j ∈ I`.

Establish `e : 2 * S i j = (S i j + S j i) + (S i j - S j i)` using `by ring`. Rewrite using `[e]`. Conclude with `I.add_mem h1 h5`. Conclude with `(Ideal.unit_mul_mem_iff_mem I h2).1 h6`.
-/
theorem entry_mem (I : Ideal A) {θ : A} (hθ : IsUnit θ) (hsθ : s θ = -θ) (h2 : IsUnit (2 : A))
    (S : Matrix ι ι A) (hv : ∀ x, bf s S x x ∈ I) (i j : ι) : S i j ∈ I := by
  have pol : ∀ x y, bf s S x y + bf s S y x ∈ I := fun x y => by
    have h := I.sub_mem (I.sub_mem (hv (x + y)) (hv x)) (hv y)
    have e : bf s S (x + y) (x + y) - bf s S x x - bf s S y y = bf s S x y + bf s S y x := by
      simp only [bf_add_left, bf_add_right]
      ring
    rwa [e] at h
  have h1 := pol (Pi.single i 1) (Pi.single j 1)
  have h3 := pol (Pi.single i 1) (θ • Pi.single j 1)
  rw [bf_single, bf_single] at h1
  rw [bf_smul_right, bf_smul_left, hsθ, bf_single, bf_single] at h3
  have h4 : θ * (S i j - S j i) ∈ I := by
    have e : θ * (S i j - S j i) = θ * S i j + -θ * S j i := by ring
    rwa [e]
  have h5 : S i j - S j i ∈ I := (Ideal.unit_mul_mem_iff_mem I hθ).1 h4
  have h6 : 2 * S i j ∈ I := by
    have e : 2 * S i j = (S i j + S j i) + (S i j - S j i) := by ring
    rw [e]
    exact I.add_mem h1 h5
  exact (Ideal.unit_mul_mem_iff_mem I h2).1 h6

/- English proof (translation)
Rewrite using `[cT, Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_cT (S : Matrix ι ι A) : (cT s S).det = s S.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.det_mul, Matrix.det_mul, det_cT]`. Conclude with `((hg.map s).mul hS).mul hg`.
-/
theorem isUnit_det_congr (S g : Matrix ι ι A) (hS : IsUnit S.det) (hg : IsUnit g.det) :
    IsUnit (cT s g * S * g).det := by
  rw [Matrix.det_mul, Matrix.det_mul, det_cT]
  exact ((hg.map s).mul hS).mul hg

/- English proof (translation)
Establish `h : cT s (cT s g) = g`. Use extensionality with `i j`. Simplify using `[cT_apply, hs]`. Rewrite using `[cT_mul, cT_mul, h, hS, Matrix.mul_assoc]`.
-/
theorem cT_congr (hs : ∀ z, s (s z) = z) {S : Matrix ι ι A} (hS : cT s S = S) (g : Matrix ι ι A) :
    cT s (cT s g * S * g) = cT s g * S * g := by
  have h : cT s (cT s g) = g := by
    ext i j
    simp [cT_apply, hs]
  rw [cT_mul, cT_mul, h, hS, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem congr_mul (S g g' : Matrix ι ι A) :
    cT s (g * g') * S * (g * g') = cT s g' * (cT s g * S * g) * g' := by
  rw [cT_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [bf, dotProduct, mulVec, Matrix.mul_apply, cT_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem congr_apply (S g : Matrix ι ι A) (i : ι) :
    (cT s g * S * g) i i = bf s S (fun k => g k i) (fun k => g k i) := by
  simp only [bf, dotProduct, mulVec, Matrix.mul_apply, cT_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

variable (hs : ∀ z, s (s z) = z) (hR : ∀ r, s (algebraMap R A r) = algebraMap R A r)
  (t : A →ₗ[R] R) (ht : ∀ r, t (algebraMap R A r) = r) (hfix : ∀ z, s z = z → algebraMap R A (t z) = z)
  {θ : A} (hθ : IsUnit θ) (hsθ : s θ = -θ) (h2 : IsUnit (2 : A))

include hs ht hfix hθ hsθ h2 in

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `set I : Ideal A := m.asIdeal.map (algebraMap R A) with hI`. Establish `hv : ∀ x, bf s S x x ∈ I` using `fun x => by`. Rewrite using `[← hfix _ (bf_conj hs hS x x)]`.

Conclude with `Ideal.mem_map_of_mem _ (hcon x)`. Establish `hent` using `entry_mem I hθ hsθ h2 S hv`. Establish `hzero : S.map (Ideal.Quotient.mk I) = 0`. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hent i j)`.

Establish `hu : IsUnit (Ideal.Quotient.mk I S.det)` using `hdet.map _`. Rewrite `hu` using `[RingHom.map_det, RingHom.mapMatrix_apply, hzero, Matrix.det_zero, isUnit_zero_iff]`. Establish `htop : I = ⊤` using `(Ideal.eq_top_iff_one I).2 (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact hu.symm))`. Establish `h1 : (1 : A) ∈ (m.asIdeal • ⊤ : Submodule R A)`. Rewrite using `[Ideal.smul_top_eq_map, ← hI, htop]`.

Discharge the goal by the elementary cases of `trivial`. Establish `h3 : ∀ z ∈ (m.asIdeal • ⊤ : Submodule R A), t z ∈ m.asIdeal` using `fun z hz => by`. Use `Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ hr`.

Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ ha hb`. Establish `h4` using `h3 1 h1`. Rewrite `h4` using `[← map_one (algebraMap R A), ht]`. Conclude with `m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h4)`.
-/
theorem exists_value_notMem [Nonempty ι] {S : Matrix ι ι A} (hS : cT s S = S) (hdet : IsUnit S.det)
    (m : MaximalSpectrum R) : ∃ x, t (bf s S x x) ∉ m.asIdeal := by
  by_contra hcon
  push_neg at hcon
  set I : Ideal A := m.asIdeal.map (algebraMap R A) with hI
  have hv : ∀ x, bf s S x x ∈ I := fun x => by
    rw [← hfix _ (bf_conj hs hS x x)]
    exact Ideal.mem_map_of_mem _ (hcon x)
  have hent := entry_mem I hθ hsθ h2 S hv
  have hzero : S.map (Ideal.Quotient.mk I) = 0 := by
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hent i j)
  have hu : IsUnit (Ideal.Quotient.mk I S.det) := hdet.map _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hzero, Matrix.det_zero, isUnit_zero_iff] at hu
  have htop : I = ⊤ :=
    (Ideal.eq_top_iff_one I).2 (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact hu.symm))
  have h1 : (1 : A) ∈ (m.asIdeal • ⊤ : Submodule R A) := by
    rw [Ideal.smul_top_eq_map, ← hI, htop]
    trivial
  have h3 : ∀ z ∈ (m.asIdeal • ⊤ : Submodule R A), t z ∈ m.asIdeal := fun z hz => by
    refine Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    · rw [map_add]
      exact Ideal.add_mem _ ha hb
  have h4 := h3 1 h1
  rw [← map_one (algebraMap R A), ht] at h4
  exact m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h4)

include hs hR ht hfix hθ hsθ h2 in

/- English proof (translation)
Use `haveI := Fintype.ofFinite (MaximalSpectrum R)`. Use `choose xm hxm using exists_value_notMem hs t ht hfix hθ hsθ h2 hS hdet`. Use `choose c hc using fun k : MaximalSpectrum R => exists_crt (B := R) fun m => if m = k then 1 else 0`. Use `set x : ι → A := ∑ k, algebraMap R A (c k) • xm k with hx`. Establish `hval : t (bf s S x x) = ∑ k, ∑ l, c k * c l * t (bf s S (xm k) (xm l))`.

Rewrite using `[hx, bf_sum_left, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[bf_sum_right, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[bf_smul_left, bf_smul_right, hR, ← mul_assoc, ← map_mul, ← Algebra.smul_def, map_smul, smul_eq_mul]`.

Establish `hunit : IsUnit (t (bf s S x x))` using `isUnit_of_forall_notMem fun m hm => by`. Establish `hπ : ∀ k, Ideal.Quotient.mk m.asIdeal (c k) = if m = k then 1 else 0` using `fun k => by`. Use `Ideal.Quotient.eq.2 (hc k m)` as an intermediate fact. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h1 : Ideal.Quotient.mk m.asIdeal (t (bf s S x x)) = Ideal.Quotient.mk m.asIdeal (t (bf s S (xm m) (xm m)))`. Rewrite using `[hval]`. Simplify using `only [map_sum, map_mul, hπ]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[Ideal.Quotient.eq_zero_iff_mem.2 hm]`.

Conclude with `hxm m (Ideal.Quotient.eq_zero_iff_mem.1 h1.symm)`. Conclude with `⟨x, hunit.unit, by rw [IsUnit.unit_spec]; exact (hfix _ (bf_conj hs hS x x)).symm⟩`.
-/
theorem exists_value_unit [Nonempty ι] [Finite (MaximalSpectrum R)] {S : Matrix ι ι A}
    (hS : cT s S = S) (hdet : IsUnit S.det) : ∃ (x : ι → A) (r : Rˣ), bf s S x x = algebraMap R A r := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum R)
  choose xm hxm using exists_value_notMem hs t ht hfix hθ hsθ h2 hS hdet
  choose c hc using fun k : MaximalSpectrum R =>
    exists_crt (B := R) fun m => if m = k then 1 else 0
  set x : ι → A := ∑ k, algebraMap R A (c k) • xm k with hx
  have hval : t (bf s S x x) = ∑ k, ∑ l, c k * c l * t (bf s S (xm k) (xm l)) := by
    rw [hx, bf_sum_left, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bf_sum_right, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [bf_smul_left, bf_smul_right, hR, ← mul_assoc, ← map_mul, ← Algebra.smul_def, map_smul,
      smul_eq_mul]
  have hunit : IsUnit (t (bf s S x x)) := isUnit_of_forall_notMem fun m hm => by
    have hπ : ∀ k, Ideal.Quotient.mk m.asIdeal (c k) = if m = k then 1 else 0 := fun k => by
      have := Ideal.Quotient.eq.2 (hc k m)
      rw [this]
      split_ifs <;> simp
    have h1 : Ideal.Quotient.mk m.asIdeal (t (bf s S x x))
        = Ideal.Quotient.mk m.asIdeal (t (bf s S (xm m) (xm m))) := by
      rw [hval]
      simp only [map_sum, map_mul, hπ]
      simp
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm] at h1
    exact hxm m (Ideal.Quotient.eq_zero_iff_mem.1 h1.symm)
  exact ⟨x, hunit.unit, by rw [IsUnit.unit_spec]; exact (hfix _ (bf_conj hs hS x x)).symm⟩

/- English proof (translation)
Rewrite using `[cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]`. Both sides reduce to the same expression.
-/
theorem cT_fromBlocks {l m : Type} (a : Matrix l l A) (b : Matrix l m A) (c : Matrix m l A)
    (d : Matrix m m A) : cT s (fromBlocks a b c d) = fromBlocks (cT s a) (cT s c) (cT s b) (cT s d) := by
  rw [cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  rfl

variable (s R) in

def DiagProp (A : Type) [CommRing A] [Algebra R A] (s : A →+* A) (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ S : Matrix ι ι A, cT s S = S → IsUnit S.det →
    ∃ (g : Matrix ι ι A) (D : ι → Rˣ), IsUnit g.det ∧
      cT s g * S * g = diagonal fun i => algebraMap R A (D i : R)

/- English proof (translation)
Introduce `S hS hdet`. Establish `hS' : cT s (S.submatrix e e) = S.submatrix e e`. Use extensionality with `i j`. Simplify using `only [cT_apply, submatrix_apply]`. Rewrite using `[← cT_apply, hS]`.

Take `⟨g, D, hg, hgS⟩` from `h (S.submatrix e e) hS' (by rwa [Matrix.det_submatrix_equiv_self])`. Use `⟨g.submatrix e.symm e.symm, fun k => D (e.symm k), by rwa [Matrix.det_submatrix_equiv_self], ?_⟩` and prove the remaining obligations. Establish `h1 : (cT s g * S.submatrix e e * g).submatrix e.symm e.symm = (diagonal fun i => algebraMap R A (D i : R)).submatrix e.symm e.symm` using `by rw [hgS]`. Establish `hc : cT s (g.submatrix e.symm e.symm) = (cT s g).submatrix e.symm e.symm` using `rfl`. Establish `hS2 : S = (S.submatrix e e).submatrix e.symm e.symm`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hc]`. Rewrite using `[hS2, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]`. Use extensionality with `i j`.

Simplify using `[Matrix.diagonal_apply]`.
-/
theorem DiagProp.of_equiv {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (h : DiagProp (R := R) A s ι) : DiagProp (R := R) A s κ := by
  intro S hS hdet
  have hS' : cT s (S.submatrix e e) = S.submatrix e e := by
    ext i j
    simp only [cT_apply, submatrix_apply]
    rw [← cT_apply, hS]
  obtain ⟨g, D, hg, hgS⟩ := h (S.submatrix e e) hS' (by rwa [Matrix.det_submatrix_equiv_self])
  refine ⟨g.submatrix e.symm e.symm, fun k => D (e.symm k), by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  have h1 : (cT s g * S.submatrix e e * g).submatrix e.symm e.symm
      = (diagonal fun i => algebraMap R A (D i : R)).submatrix e.symm e.symm := by rw [hgS]
  have hc : cT s (g.submatrix e.symm e.symm) = (cT s g).submatrix e.symm e.symm := rfl
  have hS2 : S = (S.submatrix e e).submatrix e.symm e.symm := by
    ext i j
    simp
  rw [hc]
  rw [hS2, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]
  ext i j
  simp [Matrix.diagonal_apply]

include hs hR in

/- English proof (translation)
Take `⟨a, b, c, d, rfl⟩ : ∃ a b c d, S = fromBlocks a b c d` from `⟨_, _, _, _, (fromBlocks_toBlocks S).symm⟩`. Use `set u := algebraMap R A (r : R) with hu`. Use `set v := algebraMap R A ((r⁻¹ : Rˣ) : R) with hv`. Establish `huv : u * v = 1`. Rewrite using `[hu, hv, ← map_mul, Units.mul_inv, map_one]`.

Establish `hsv : s v = v` using `hR _`. Rewrite `hS` using `[cT_fromBlocks]`. Take `⟨-, hcb, hbc, hd⟩` from `Matrix.fromBlocks_inj.1 hS`. Establish `ha : a = u • (1 : Matrix Unit Unit A)`. Use extensionality with `i j`.

Consider the cases of `i`. Consider the cases of `j`. Simplify using `using h0`. Substitute `ha` using the available equality. Use `set P : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A := fromBlocks 1 (-(v • b)) 0 1 with hP`.

Establish `hPdet : P.det = 1`. Rewrite using `[hP, Matrix.det_fromBlocks_zero₂₁]`. Simplify using the standard rewrite rules. Establish `hcP : cT s P = fromBlocks 1 0 (-(v • c)) 1`. Establish `z1 : cT s (0 : Matrix ι Unit A) = 0`.

Use extensionality with `i j`. Simplify using `[cT_apply]`. Establish `z2 : cT s (-(v • b)) = -(v • c)`. Rewrite using `[← hbc]`. Use extensionality with `i j`.

Simplify using `[cT_apply, hsv]`. Rewrite using `[hP, cT_fromBlocks, cT_one, cT_one, z1, z2]`. Use `set d' : Matrix ι ι A := d - v • (c * b) with hd'`. Establish `huv' : v * u = 1` using `by rw [mul_comm, huv]`. Establish `hcong : cT s P * fromBlocks (u • 1) b c d * P = fromBlocks (u • 1) 0 0 d'`.

Rewrite using `[hcP, hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Establish `e1 : (u • (1 : Matrix Unit Unit A)) * (-(v • b)) + b = 0`. Simplify using `[smul_smul, huv']`. Establish `e2 : -(v • c) * (u • (1 : Matrix Unit Unit A)) + c = 0`. Simplify using `[smul_smul, huv, huv']`.

Simplify using `only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, e2, e1]`. Use `congr 1`. Rewrite using `[hd']`. Simplify using `only [Matrix.neg_mul, Matrix.smul_mul]`. Normalize the expressions using the abelian group laws.

Establish `hcb' : cT s (c * b) = c * b` using `by rw [cT_mul, hbc, hcb]`. Establish `hherm : cT s d' = d'`. Use extensionality with `i j`. Simplify using `only [hd', cT_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, hsv]`. Rewrite using `[← cT_apply, ← cT_apply, hd, hcb']`.

Establish `hdet' : IsUnit d'.det`. Establish `h1` using `isUnit_det_congr (s := s) _ P hdet (by rw [hPdet]; exact isUnit_one)`. Rewrite `h1` using `[hcong, Matrix.det_fromBlocks_zero₂₁]`. Conclude with `isUnit_of_mul_isUnit_right h1`. Take `⟨g', D', hg', hgd⟩` from `ih d' hherm hdet'`.

Use `set g3 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A := fromBlocks 1 0 0 g' with hg3`. Establish `hc3 : cT s g3 = fromBlocks 1 0 0 (cT s g')`. Establish `z1 : cT s (0 : Matrix Unit ι A) = 0`. Use extensionality with `i j`. Simplify using `[cT_apply]`.

Establish `z2 : cT s (0 : Matrix ι Unit A) = 0`. Use extensionality with `i j`. Simplify using `[cT_apply]`. Rewrite using `[hg3, cT_fromBlocks, cT_one, z1, z2]`. Use `⟨P * g3, Sum.elim (fun _ => r) D', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_mul, hPdet, one_mul, hg3, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `using hg'`. Rewrite using `[congr_mul, hcong, hc3, hg3, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, hgd]`. Establish `hdiag : u • (1 : Matrix Unit Unit A) = diagonal fun _ => u`.

Use extensionality with `i j`. Consider the cases of `i`. Consider the cases of `j`. Simplify using the standard rewrite rules. Rewrite using `[hdiag, Matrix.fromBlocks_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> rfl`.
-/
theorem split_step (ih : DiagProp (R := R) A s ι) {S : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A} (hS : cT s S = S)
    (hdet : IsUnit S.det) (r : Rˣ) (h0 : S (Sum.inl ()) (Sum.inl ()) = algebraMap R A r) :
    ∃ (g : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A) (D : Unit ⊕ ι → Rˣ), IsUnit g.det ∧
      cT s g * S * g = diagonal fun i => algebraMap R A (D i : R) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, S = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks S).symm⟩
  set u := algebraMap R A (r : R) with hu
  set v := algebraMap R A ((r⁻¹ : Rˣ) : R) with hv
  have huv : u * v = 1 := by
    rw [hu, hv, ← map_mul, Units.mul_inv, map_one]
  have hsv : s v = v := hR _
  rw [cT_fromBlocks] at hS
  obtain ⟨-, hcb, hbc, hd⟩ := Matrix.fromBlocks_inj.1 hS
  have ha : a = u • (1 : Matrix Unit Unit A) := by
    ext i j
    cases i; cases j
    simpa using h0
  subst ha
  set P : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A := fromBlocks 1 (-(v • b)) 0 1 with hP
  have hPdet : P.det = 1 := by
    rw [hP, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hcP : cT s P = fromBlocks 1 0 (-(v • c)) 1 := by
    have z1 : cT s (0 : Matrix ι Unit A) = 0 := by
      ext i j
      simp [cT_apply]
    have z2 : cT s (-(v • b)) = -(v • c) := by
      rw [← hbc]
      ext i j
      simp [cT_apply, hsv]
    rw [hP, cT_fromBlocks, cT_one, cT_one, z1, z2]
  set d' : Matrix ι ι A := d - v • (c * b) with hd'
  have huv' : v * u = 1 := by rw [mul_comm, huv]
  have hcong : cT s P * fromBlocks (u • 1) b c d * P = fromBlocks (u • 1) 0 0 d' := by
    rw [hcP, hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have e1 : (u • (1 : Matrix Unit Unit A)) * (-(v • b)) + b = 0 := by
      simp [smul_smul, huv']
    have e2 : -(v • c) * (u • (1 : Matrix Unit Unit A)) + c = 0 := by
      simp [smul_smul, huv, huv']
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, e2, e1]
    congr 1
    rw [hd']
    simp only [Matrix.neg_mul, Matrix.smul_mul]
    abel
  have hcb' : cT s (c * b) = c * b := by rw [cT_mul, hbc, hcb]
  have hherm : cT s d' = d' := by
    ext i j
    simp only [hd', cT_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, hsv]
    rw [← cT_apply, ← cT_apply, hd, hcb']
  have hdet' : IsUnit d'.det := by
    have h1 := isUnit_det_congr (s := s) _ P hdet (by rw [hPdet]; exact isUnit_one)
    rw [hcong, Matrix.det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨g', D', hg', hgd⟩ := ih d' hherm hdet'
  set g3 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A := fromBlocks 1 0 0 g' with hg3
  have hc3 : cT s g3 = fromBlocks 1 0 0 (cT s g') := by
    have z1 : cT s (0 : Matrix Unit ι A) = 0 := by
      ext i j
      simp [cT_apply]
    have z2 : cT s (0 : Matrix ι Unit A) = 0 := by
      ext i j
      simp [cT_apply]
    rw [hg3, cT_fromBlocks, cT_one, z1, z2]
  refine ⟨P * g3, Sum.elim (fun _ => r) D', ?_, ?_⟩
  · rw [Matrix.det_mul, hPdet, one_mul, hg3, Matrix.det_fromBlocks_zero₂₁]
    simpa using hg'
  · rw [congr_mul, hcong, hc3, hg3, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, hgd]
    have hdiag : u • (1 : Matrix Unit Unit A) = diagonal fun _ => u := by
      ext i j
      cases i; cases j
      simp
    rw [hdiag, Matrix.fromBlocks_diagonal]
    congr 1
    funext i
    cases i <;> rfl

include hs hR ht hfix hθ hsθ h2 in

/- English proof (translation)
Introduce `S hS hdet`. Take `⟨x, r, hx⟩` from `exists_value_unit hs hR t ht hfix hθ hsθ h2 hS hdet`. Use `set v := algebraMap R A ((r⁻¹ : Rˣ) : R) with hv`. Establish `hvr : v * algebraMap R A (r : R) = 1`. Rewrite using `[hv, ← map_mul, Units.inv_mul, map_one]`.

Establish `hl : ∑ j, (v * ∑ i, s (x i) * S i j) * x j = 1`. Rewrite using `[← hvr, ← hx]`. Simplify using `only [bf, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.

Take `⟨g1, hg1, hcol⟩` from `exists_col (Sum.inl ()) x _ hl`. Establish `h00 : (cT s g1 * S * g1) (Sum.inl ()) (Sum.inl ()) = algebraMap R A (r : R)`. Rewrite using `[congr_apply, ← hx]`. Simplify using `only [hcol]`. Take `⟨g2, D, hg2, h⟩` from `split_step hs hR ih (cT_congr hs hS g1) (isUnit_det_congr S g1 hdet hg1) r h00`.

Use `⟨g1 * g2, D, by rw [Matrix.det_mul]; exact hg1.mul hg2, ?_⟩` and prove the remaining obligations. Rewrite using `[congr_mul]`. Conclude with `h`.
-/
theorem diagProp_succ [Finite (MaximalSpectrum R)] [Finite (MaximalSpectrum A)]
    (ih : DiagProp (R := R) A s ι) : DiagProp (R := R) A s (Unit ⊕ ι) := by
  intro S hS hdet
  obtain ⟨x, r, hx⟩ := exists_value_unit hs hR t ht hfix hθ hsθ h2 hS hdet
  set v := algebraMap R A ((r⁻¹ : Rˣ) : R) with hv
  have hvr : v * algebraMap R A (r : R) = 1 := by
    rw [hv, ← map_mul, Units.inv_mul, map_one]
  have hl : ∑ j, (v * ∑ i, s (x i) * S i j) * x j = 1 := by
    rw [← hvr, ← hx]
    simp only [bf, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨g1, hg1, hcol⟩ := exists_col (Sum.inl ()) x _ hl
  have h00 : (cT s g1 * S * g1) (Sum.inl ()) (Sum.inl ()) = algebraMap R A (r : R) := by
    rw [congr_apply, ← hx]
    simp only [hcol]
  obtain ⟨g2, D, hg2, h⟩ := split_step hs hR ih (cT_congr hs hS g1) (isUnit_det_congr S g1 hdet hg1) r h00
  refine ⟨g1 * g2, D, by rw [Matrix.det_mul]; exact hg1.mul hg2, ?_⟩
  rw [congr_mul]
  exact h

include hs hR ht hfix hθ hsθ h2 in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `S _ _`. Conclude with `⟨1, fun i => i.elim0, by simp, by ext i; exact i.elim0⟩`. Consider the case `succ n ih`.

Conclude with `(diagProp_succ hs hR t ht hfix hθ hsθ h2 ih).of_equiv (Fintype.equivOfCardEq (by simp; omega))`.
-/
theorem diagProp_fin [Finite (MaximalSpectrum R)] [Finite (MaximalSpectrum A)] (n : ℕ) :
    DiagProp (R := R) A s (Fin n) := by
  induction n with
  | zero =>
    intro S _ _
    exact ⟨1, fun i => i.elim0, by simp, by ext i; exact i.elim0⟩
  | succ n ih =>
    exact (diagProp_succ hs hR t ht hfix hθ hsθ h2 ih).of_equiv
      (Fintype.equivOfCardEq (by simp; omega))

end Form

end GlobalTheory.CompanionTheory.SW.HermDiagonal

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h R _ _ _ _ n S hS hdet`. Establish `h2 : Module.finrank F E = 2` using `h.2.2.1`. Establish `h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ` using `h`. Establish `hσ` using `GlobalTheory.GaussMean.OneVec.sigma_sigma h'`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`.

Establish `hs : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hR : ∀ r : R, sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r` using `fun r => by`. Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`. Establish `hhalf : algebraMap F R (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F R) 2, ← map_mul]`. Simplify using the standard rewrite rules.

Set `t : (R ⊗[F] E) →ₗ[R] R` to `algebraMap F R (1 / 2) • Algebra.trace R (R ⊗[F] E)`. Establish `ht : ∀ r, t (algebraMap R (R ⊗[F] E) r) = r` using `fun r => by`. Use `Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)) r` as an intermediate fact. Simplify using `only [t, LinearMap.smul_apply, this, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]`. Rewrite using `[← mul_assoc]`.

Evaluate the numerical expressions using `[hhalf]`. Establish `hfix : ∀ z, sigR R σ z = z → algebraMap R (R ⊗[F] E) (t z) = z` using `fun z hz => by`. Establish `h1 : z + z = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z)`. Use `GlobalTheory.GaussMean.OneVec.add_sigR R h' z` as an intermediate fact. Rewrite using `[← this]`.

Conclude with `congrArg (z + ·) hz.symm`. Establish `h3 : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, hhalf, map_one]`. Simplify using `only [t, LinearMap.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[← h1]`.

Take the linear combination `z * h3`. Establish `hfixE : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range` using `fun a => by`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `h1` using `GlobalTheory.GaussMean.OneVec.add_sigma h' a`.

Rewrite `h1` using `[ha]`. Use `⟨(1 / 2) * Algebra.trace F E a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← h1]`. Simplify using `only [one_div, map_inv₀, map_ofNat]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨b, rfl⟩`. Conclude with `σ.commutes b`. Take `⟨θ, hθ0, hσθ, -, -⟩` from `PIW.AdelicOrbitU.quad_exists_theta σ h2 hfixE`. Establish `hθ : IsUnit ((1 : R) ⊗ₜ[F] θ)` using `(IsUnit.mk0 θ hθ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)`.

Establish `hsθ : sigR R σ ((1 : R) ⊗ₜ[F] θ) = -((1 : R) ⊗ₜ[F] θ)`. Simplify using `[sigR, hσθ, TensorProduct.tmul_neg]`. Establish `h2u : IsUnit (2 : R ⊗[F] E)`. Use `(IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (R ⊗[F] E))` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Use `haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.base_change F R E`. Use `haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _`. Take `⟨g, D, hg, hgS⟩` from `HermDiagonal.diagProp_fin hs hR t ht hfix hθ hsθ h2u n S hS hdet`. Conclude with `⟨Matrix.GeneralLinearGroup.mk'' g hg, D, hgS⟩`.
-/
theorem exists_diagonal_congr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) S = S → IsUnit S.det → ∃ (g : GL (Fin n) (R ⊗[F] E)) (D : Fin n → Rˣ), cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Matrix.diagonal fun i => algebraMap R (R ⊗[F] E) (D i : R) := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ n S hS hdet
  have h2 : Module.finrank F E = 2 := h.2.2.1
  have h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ := h
  have hσ := GlobalTheory.GaussMean.OneVec.sigma_sigma h'
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hs : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hR : ∀ r : R, sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := fun r => by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  have hhalf : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    simp
  let t : (R ⊗[F] E) →ₗ[R] R := algebraMap F R (1 / 2) • Algebra.trace R (R ⊗[F] E)
  have ht : ∀ r, t (algebraMap R (R ⊗[F] E) r) = r := fun r => by
    have := Algebra.trace_algebraMap_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)) r
    simp only [t, LinearMap.smul_apply, this, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc]
    norm_num [hhalf]
  have hfix : ∀ z, sigR R σ z = z → algebraMap R (R ⊗[F] E) (t z) = z := fun z hz => by
    have h1 : z + z = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) := by
      have := GlobalTheory.GaussMean.OneVec.add_sigR R h' z
      rw [← this]
      exact congrArg (z + ·) hz.symm
    have h3 : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
      rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, hhalf, map_one]
    simp only [t, LinearMap.smul_apply, smul_eq_mul, map_mul]
    rw [← h1]
    linear_combination z * h3
  have hfixE : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range := fun a => by
    constructor
    · intro ha
      have h1 := GlobalTheory.GaussMean.OneVec.add_sigma h' a
      rw [ha] at h1
      refine ⟨(1 / 2) * Algebra.trace F E a, ?_⟩
      rw [map_mul, ← h1]
      simp only [one_div, map_inv₀, map_ofNat]
      field_simp
      ring
    · rintro ⟨b, rfl⟩
      exact σ.commutes b
  obtain ⟨θ, hθ0, hσθ, -, -⟩ := PIW.AdelicOrbitU.quad_exists_theta σ h2 hfixE
  have hθ : IsUnit ((1 : R) ⊗ₜ[F] θ) :=
    (IsUnit.mk0 θ hθ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)
  have hsθ : sigR R σ ((1 : R) ⊗ₜ[F] θ) = -((1 : R) ⊗ₜ[F] θ) := by
    simp [sigR, hσθ, TensorProduct.tmul_neg]
  have h2u : IsUnit (2 : R ⊗[F] E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (R ⊗[F] E))
    rwa [map_ofNat] at this
  haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.base_change F R E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  obtain ⟨g, D, hg, hgS⟩ := HermDiagonal.diagProp_fin hs hR t ht hfix hθ hsθ h2u n S hS hdet
  exact ⟨Matrix.GeneralLinearGroup.mk'' g hg, D, hgS⟩

end GlobalTheory.CompanionTheory.SW
