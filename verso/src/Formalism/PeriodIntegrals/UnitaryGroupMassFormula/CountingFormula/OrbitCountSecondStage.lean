import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DsumCancel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IsIntIntCast

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hermP (D : Formalism.BasicNotions.D7) (Z : MatZ D) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  (alM D x).conjTranspose * betaZ D Z + (betaZ D Z).conjTranspose * alM D x

/- English proof (translation)
Establish `hE : ∀ c, (VS D).hT (D.sp.hypE c) (fr D x b - fr D y b) = 0`. Introduce `c`. Establish `h1` using `hx.2.1 (Fin.castSucc c) b`. Establish `h2` using `hy.2.1 (Fin.castSucc c) b`. Simplify using `only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1 h2`.

Rewrite using `[map_sub, h1, h2, sub_self]`. Establish `hZ : (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0`. Take `⟨c0, hc0, hz⟩` from `hF.2.2.2.2`. Establish `h1` using `hx.2.1 (Fin.last _) b`. Establish `h2` using `hy.2.1 (Fin.last _) b`.

Simplify using `only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1 h2`. Establish `h3 : (starRingEnd D.host.E) c0 * (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0`. Rewrite using `[map_sub, mul_sub, h1, h2, sub_self]`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Conclude with `absurd ((map_eq_zero _).1 h) hc0`.

Conclude with `h`. Establish `hP : pW D (fr D x b - fr D y b) = 0`. Establish `h` using `congrFun hw b`. Simplify using `only [pWf] at h`. Rewrite using `[pW_eq, map_sub, ← pW_eq, ← pW_eq, h, sub_self]`.

Establish `h` using `hP`. Simplify using `only [pW, hE, hZ, zero_smul, Finset.sum_const_zero, sub_zero, zero_div, add_zero] at h`. Conclude with `sub_eq_zero.1 h`.
-/
private theorem fr_sub_eq_sum_hypE_of_good_of_pWf_eq (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    {x y : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (hy : Good D T' F0 Λ Z y)
    (hw : pWf D x = pWf D y) (b : Fin (D.R.rS + 1)) :
    fr D x b - fr D y b = ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) • D.sp.hypE c := by
  have hE : ∀ c, (VS D).hT (D.sp.hypE c) (fr D x b - fr D y b) = 0 := by
    intro c
    have h1 := hx.2.1 (Fin.castSucc c) b
    have h2 := hy.2.1 (Fin.castSucc c) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZ : (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0 := by
    obtain ⟨c0, hc0, hz⟩ := hF.2.2.2.2
    have h1 := hx.2.1 (Fin.last _) b
    have h2 := hy.2.1 (Fin.last _) b
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul] at h1 h2
    have h3 : (starRingEnd D.host.E) c0 * (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0 := by
      rw [map_sub, mul_sub, h1, h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd ((map_eq_zero _).1 h) hc0
    · exact h
  have hP : pW D (fr D x b - fr D y b) = 0 := by
    have h := congrFun hw b
    simp only [pWf] at h
    rw [pW_eq, map_sub, ← pW_eq, ← pW_eq, h, sub_self]
  have h := hP
  simp only [pW, hE, hZ, zero_smul, Finset.sum_const_zero, sub_zero, zero_div, add_zero] at h
  exact sub_eq_zero.1 h

/- English proof (translation)
Establish `hd` using `fun b => fr_sub_eq_sum_hypE_of_good_of_pWf_eq D T' F0 Λ hF Z hx hy hw b`. Establish `hβ : ∀ c b, (VS D).hT (D.sp.hypE c) (fr D y b) = betaZ D Z c b`. Introduce `c b`. Establish `h2` using `hy.2.1 (Fin.castSucc c) b`. Simplify using `only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h2`.

Simplify using `only [betaZ, Matrix.submatrix_apply, id, h2]`. Establish `hβ' : ∀ c a, (VS D).hT (fr D y a) (D.sp.hypE c) = star (betaZ D Z c a)`. Introduce `c a`. Rewrite using `[← hβ, hT_star]`. Establish `hα : ∀ c b, alM D x c b = alM D y c b + (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b)`.

Introduce `c b`. Simplify using `only [alM, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hee : ∀ i j, (VS D).hT (D.sp.hypE i) (D.sp.hypE j) = 0` using `fun i j => D.sp.hyp_ee i j`. Establish `key : ∀ a b, ∑ c, star ((VS D).hT (D.sp.hypF c) (fr D x a - fr D y a)) * betaZ D Z c b + ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) = 0`.

Introduce `a b`. Establish `hxx` using `hx.2.2 a b`. Rewrite `hxx` using `[← hy.2.2 a b]`. Establish `ex : ∀ a, fr D x a = fr D y a + ∑ c, (VS D).hT (D.sp.hypF c) (fr D x a - fr D y a) • D.sp.hypE c`. Introduce `a`.

Rewrite using `[← hd a]`. Normalize the expressions using the abelian group laws. Rewrite `hxx` using `[ex a, ex b]`. Simplify using `only [map_add, map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, hee, mul_zero, Finset.sum_const_zero, add_zero, hβ, hβ', starRingEnd_apply] at hxx`. Take the linear combination `hxx`.

Use extensionality with `a b`. Simplify using `only [hermP, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hα, star_add, add_mul, mul_add, Finset.sum_add_distrib]`. Establish `k2 : ∑ c, star (betaZ D Z c a) * (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) = ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a)` using `Finset.sum_congr rfl (fun _ _ => mul_comm _ _)`. Take the linear combination `key a b + k2`.
-/
theorem hermitianDivisible_eq_smul (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    {x y : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (hy : Good D T' F0 Λ Z y)
    (hw : pWf D x = pWf D y) : hermP D Z x = hermP D Z y := by
  have hd := fun b => fr_sub_eq_sum_hypE_of_good_of_pWf_eq D T' F0 Λ hF Z hx hy hw b
  have hβ : ∀ c b, (VS D).hT (D.sp.hypE c) (fr D y b) = betaZ D Z c b := by
    intro c b
    have h2 := hy.2.1 (Fin.castSucc c) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h2
    simp only [betaZ, Matrix.submatrix_apply, id, h2]
  have hβ' : ∀ c a, (VS D).hT (fr D y a) (D.sp.hypE c) = star (betaZ D Z c a) := by
    intro c a
    rw [← hβ, hT_star]
  have hα : ∀ c b, alM D x c b = alM D y c b + (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) := by
    intro c b
    simp only [alM, map_sub]
    ring
  have hee : ∀ i j, (VS D).hT (D.sp.hypE i) (D.sp.hypE j) = 0 := fun i j => D.sp.hyp_ee i j
  have key : ∀ a b, ∑ c, star ((VS D).hT (D.sp.hypF c) (fr D x a - fr D y a)) * betaZ D Z c b +
      ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) = 0 := by
    intro a b
    have hxx := hx.2.2 a b
    rw [← hy.2.2 a b] at hxx
    have ex : ∀ a, fr D x a = fr D y a + ∑ c, (VS D).hT (D.sp.hypF c) (fr D x a - fr D y a) • D.sp.hypE c := by
      intro a
      rw [← hd a]
      abel
    rw [ex a, ex b] at hxx
    simp only [map_add, map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, hee, mul_zero,
      Finset.sum_const_zero, add_zero, hβ, hβ', starRingEnd_apply] at hxx
    linear_combination hxx
  ext a b
  simp only [hermP, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hα, star_add,
    add_mul, mul_add, Finset.sum_add_distrib]
  have k2 : ∑ c, star (betaZ D Z c a) * (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) =
      ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  linear_combination key a b + k2

/- English proof (translation)
Take `⟨g, hg⟩` from `hF.1.fg`. Take `⟨N1, hN1, h1⟩` from `commonDen (K := D.host.E) (Finset.image (fun p : Fin D.R.rS × (VS D).V => (VS D).hT (D.sp.hypF p.1) p.2) (Finset.univ ×ˢ g) ∪ Finset.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) Finset.univ)`. Establish `hv : ∀ v ∈ Λ, ∀ c, IsIntegral ℤ ((N1 : D.host.E) * (VS D).hT (D.sp.hypF c) v)`. Introduce `v hv c`. Rewrite `hv` using `[← hg]`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`. Conclude with `h1 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(c, y), Finset.mem_product.2 ⟨Finset.mem_univ _, by exact_mod_cast hy⟩, rfl⟩))`. Consider the case `zero`. Rewrite using `[map_zero, mul_zero]`.

Conclude with `isIntegral_zero`. Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add, mul_add]`. Conclude with `hy.add hz`. Consider the case `smul o y _ hy`.

Rewrite using `[← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, mul_left_comm]`. Conclude with `(isInt_O o).mul hy`. Use `⟨N1 * N1, Nat.mul_pos hN1 hN1, fun x hx i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Nat.cast_mul, Finset.mul_sum]`. Use `IsIntegral.sum _ (fun b _ => ?_)` and prove the remaining obligations.

Establish `e : (N1 : D.host.E) * N1 * (alM D x i b * R b j) = ((N1 : D.host.E) * alM D x i b) * ((N1 : D.host.E) * R b j)` using `by ring`. Rewrite using `[e]`. Conclude with `(hv _ (hx b) i).mul (h1 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(b, j), Finset.mem_univ _, rfl⟩)))`.
-/
private theorem exists_nat_mul_alM_mul_isIntegral_of_fr_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : (Fin D.R.rS → (VS D).V) × (VS D).V, (∀ b, fr D x b ∈ Λ) →
      ∀ i j, IsIntegral ℤ ((N : D.host.E) * (alM D x * R) i j) := by
  obtain ⟨g, hg⟩ := hF.1.fg
  obtain ⟨N1, hN1, h1⟩ := commonDen (K := D.host.E)
    (Finset.image (fun p : Fin D.R.rS × (VS D).V => (VS D).hT (D.sp.hypF p.1) p.2)
      (Finset.univ ×ˢ g) ∪
     Finset.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) Finset.univ)
  have hv : ∀ v ∈ Λ, ∀ c, IsIntegral ℤ ((N1 : D.host.E) * (VS D).hT (D.sp.hypF c) v) := by
    intro v hv c
    rw [← hg] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      exact h1 _ (Finset.mem_union_left _ (Finset.mem_image.2
        ⟨(c, y), Finset.mem_product.2 ⟨Finset.mem_univ _, by exact_mod_cast hy⟩, rfl⟩))
    | zero =>
      rw [map_zero, mul_zero]
      exact isIntegral_zero
    | add y z _ _ hy hz =>
      rw [map_add, mul_add]
      exact hy.add hz
    | smul o y _ hy =>
      rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, mul_left_comm]
      exact (isInt_O o).mul hy
  refine ⟨N1 * N1, Nat.mul_pos hN1 hN1, fun x hx i j => ?_⟩
  rw [Matrix.mul_apply, Nat.cast_mul, Finset.mul_sum]
  refine IsIntegral.sum _ (fun b _ => ?_)
  have e : (N1 : D.host.E) * N1 * (alM D x i b * R b j) =
      ((N1 : D.host.E) * alM D x i b) * ((N1 : D.host.E) * R b j) := by ring
  rw [e]
  exact (hv _ (hx b) i).mul (h1 _ (Finset.mem_union_right _ (Finset.mem_image.2
    ⟨(b, j), Finset.mem_univ _, rfl⟩)))

/- English proof (translation)
Introduce `D T T' F0 Λ hF Z R hR Wf hWf`. Take `⟨N, hN, hden⟩` from `exists_nat_mul_alM_mul_isIntegral_of_fr_mem D F0 Λ hF R`. Take `⟨Rep, hRepF, hRepI, hrep⟩` from `reduceRep (K := D.host.E) (4 * N) (by omega)`. Set `hfun : (Fin (D.R.rS + 1) → (VS D).V) → Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E` to `fun w => if h : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = w then R.conjTranspose * hermP D Z h.choose * R else 0`. Use `⟨(fun q : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E × (Fin D.R.rS → Fin D.R.rS → D.host.E) => Matrix.of fun i j => q.1 i j / 2 + (q.2 i j - star (q.2 j i)) / 4) '' ((hfun '' Wf) ×ˢ Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (fun ρ => ρ / (N : D.host.E)) '' Rep))), ?_, ?_ …` and prove the remaining obligations.

Conclude with `((hWf.image _).prod (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hRepF.image _)).image _`. Introduce `x hx hxw`. Establish `hN0 : (N : D.host.E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hint : ∀ i j, IsIntegral ℤ ((N : D.host.E) * ((alM D x * R) i j - star ((alM D x * R) j i)))`. Introduce `i j`.

Rewrite using `[mul_sub]`. Use `(hden x hx.1 i j).sub ?_` and prove the remaining obligations. Establish `h` using `isInt_star (hden x hx.1 j i)`. Rewrite `h` using `[star_mul', star_natCast]`. Conclude with `h`.

Use `choose t ρ ht hρ heq using fun i j => hrep _ (hint i j)`. Establish `hrel : ∀ i j, (alM D x * R) i j - star ((alM D x * R) j i) = 4 * t i j + ρ i j / N`. Introduce `i j`. Establish `h` using `heq i j`. Move the coercions through the operations in `at h`.

Establish `h' : (alM D x * R) i j - star ((alM D x * R) j i) - 4 * t i j = ρ i j / N`. Rewrite using `[eq_div_iff hN0]`. Take the linear combination `h`. Take the linear combination `h'`. Set `S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E` to `Matrix.of fun i j => star (t j i) - t i j`.

Establish `hSskew : ∀ i j, star (S j i) = -S i j`. Introduce `i j`. Simplify using `only [S, Matrix.of_apply, star_sub, star_star, neg_sub]`. Establish `hSint : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j` using `fun i j => O_of_isInt ((isInt_star (ht j i)).sub (ht i j))`. Use `⟨skE D S, skE_mem D F0 Λ hF S hSskew hSint, pWf_skE D S x, ?_⟩` and prove the remaining obligations.

Rewrite using `[alM_skE D T' F0 Λ hF Z S hx, Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one]`. Establish `e1 : R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = (alM D x * R).conjTranspose`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (alM D x * R).conjTranspose := by rw [hR, Matrix.mul_one, Matrix.conjTranspose_mul]`.

Establish `e2 : R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = alM D x * R`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = alM D x * R := by`. Rewrite using `[← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one, Matrix.one_mul]`.

Establish `hH : R.conjTranspose * hermP D Z x * R = alM D x * R + (alM D x * R).conjTranspose`. Rewrite using `[hermP, Matrix.mul_add, Matrix.add_mul, e1, e2, add_comm]`. Establish `hfx : hfun (pWf D x) = alM D x * R + (alM D x * R).conjTranspose`. Establish `hex : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = pWf D x` using `⟨x, hx, rfl⟩`. Simplify using `only [hfun, dif_pos hex]`.

Rewrite using `[hermitianDivisible_eq_smul D T' F0 Λ hF Z hex.choose_spec.1 hx hex.choose_spec.2, hH]`. Use `⟨(alM D x * R + (alM D x * R).conjTranspose, fun i j => ρ i j / N), ⟨⟨pWf D x, hxw, hfx⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Introduce `i j`. Conclude with `⟨ρ i j, hρ i j, rfl⟩`.

Use extensionality with `i j`. Establish `h1` using `hrel i j`. Establish `h2` using `congrArg star (hrel j i)`. Simplify using `only [star_sub, star_add, star_mul', star_star, star_div₀, star_natCast, star_ofNat] at h2`. Simplify using `only [S, Matrix.of_apply, Matrix.add_apply, Matrix.conjTranspose_apply, star_div₀, star_natCast]`.

Take the linear combination `(-1 / 4 : D.host.E) * h1 + (1 / 4 : D.host.E) * h2`.
-/
theorem orbit_count_second_stage : Stage2 := by
  intro D T T' F0 Λ hF Z R hR Wf hWf
  obtain ⟨N, hN, hden⟩ := exists_nat_mul_alM_mul_isIntegral_of_fr_mem D F0 Λ hF R
  obtain ⟨Rep, hRepF, hRepI, hrep⟩ := reduceRep (K := D.host.E) (4 * N) (by omega)
  let hfun : (Fin (D.R.rS + 1) → (VS D).V) → Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun w =>
    if h : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = w then R.conjTranspose * hermP D Z h.choose * R else 0
  refine ⟨(fun q : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E × (Fin D.R.rS → Fin D.R.rS → D.host.E) =>
      Matrix.of fun i j => q.1 i j / 2 + (q.2 i j - star (q.2 j i)) / 4) ''
      ((hfun '' Wf) ×ˢ Set.pi Set.univ
        (fun _ => Set.pi Set.univ (fun _ => (fun ρ => ρ / (N : D.host.E)) '' Rep))), ?_, ?_⟩
  · exact ((hWf.image _).prod (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hRepF.image _)).image _
  intro x hx hxw
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∀ i j, IsIntegral ℤ ((N : D.host.E) *
      ((alM D x * R) i j - star ((alM D x * R) j i))) := by
    intro i j
    rw [mul_sub]
    refine (hden x hx.1 i j).sub ?_
    have h := isInt_star (hden x hx.1 j i)
    rw [star_mul', star_natCast] at h
    exact h
  choose t ρ ht hρ heq using fun i j => hrep _ (hint i j)
  have hrel : ∀ i j, (alM D x * R) i j - star ((alM D x * R) j i) = 4 * t i j + ρ i j / N := by
    intro i j
    have h := heq i j
    push_cast at h
    have h' : (alM D x * R) i j - star ((alM D x * R) j i) - 4 * t i j = ρ i j / N := by
      rw [eq_div_iff hN0]
      linear_combination h
    linear_combination h'
  let S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := Matrix.of fun i j => star (t j i) - t i j
  have hSskew : ∀ i j, star (S j i) = -S i j := by
    intro i j
    simp only [S, Matrix.of_apply, star_sub, star_star, neg_sub]
  have hSint : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j :=
    fun i j => O_of_isInt ((isInt_star (ht j i)).sub (ht i j))
  refine ⟨skE D S, skE_mem D F0 Λ hF S hSskew hSint, pWf_skE D S x, ?_⟩
  rw [alM_skE D T' F0 Λ hF Z S hx, Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one]
  have e1 : R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = (alM D x * R).conjTranspose := by
    calc R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = R.conjTranspose * (alM D x).conjTranspose * (betaZ D Z * R) := by
          simp only [Matrix.mul_assoc]
      _ = (alM D x * R).conjTranspose := by rw [hR, Matrix.mul_one, Matrix.conjTranspose_mul]
  have e2 : R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = alM D x * R := by
    calc R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = (R.conjTranspose * (betaZ D Z).conjTranspose) * (alM D x * R) := by
          simp only [Matrix.mul_assoc]
      _ = alM D x * R := by
          rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one, Matrix.one_mul]
  have hH : R.conjTranspose * hermP D Z x * R = alM D x * R + (alM D x * R).conjTranspose := by
    rw [hermP, Matrix.mul_add, Matrix.add_mul, e1, e2, add_comm]
  have hfx : hfun (pWf D x) = alM D x * R + (alM D x * R).conjTranspose := by
    have hex : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = pWf D x := ⟨x, hx, rfl⟩
    simp only [hfun, dif_pos hex]
    rw [hermitianDivisible_eq_smul D T' F0 Λ hF Z hex.choose_spec.1 hx hex.choose_spec.2, hH]
  refine ⟨(alM D x * R + (alM D x * R).conjTranspose, fun i j => ρ i j / N),
    ⟨⟨pWf D x, hxw, hfx⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i j
    exact ⟨ρ i j, hρ i j, rfl⟩
  · ext i j
    have h1 := hrel i j
    have h2 := congrArg star (hrel j i)
    simp only [star_sub, star_add, star_mul', star_star, star_div₀, star_natCast, star_ofNat] at h2
    simp only [S, Matrix.of_apply, Matrix.add_apply, Matrix.conjTranspose_apply, star_div₀,
      star_natCast]
    linear_combination (-1 / 4 : D.host.E) * h1 + (1 / 4 : D.host.E) * h2

end PI.UnitaryGroupMassFormula.CntFormula
