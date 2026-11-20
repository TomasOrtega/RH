import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.CharacteristicIdentity

open Finset Polynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.TensStep

open GlobalTheory.CompanionTheory.Inh.CharId Formalism.REAL CompanionTheory.RgExh

section Abstract

variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨ℓ, hℓ, hker⟩` from `Submodule.exists_le_ker_of_notMem h`. Set `q : ℂ[X]` to `∑ j ∈ G.support, monomial j (ℓ (G.coeff j))`. Establish `hq : q = 0`. Apply `Polynomial.funext` to reduce the goal to its premises.

Introduce `u`. Establish `h0 : ℓ (G.eval (algebraMap ℂ B u)) = 0` using `hker (Submodule.subset_span ⟨u, rfl⟩)`. Rewrite `h0` using `[eval_eq_sum, Polynomial.sum, map_sum]`. Rewrite using `[eval_zero, ← h0, eval_finsetSum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, eval_monomial, smul_eq_mul, mul_comm]`. Establish `hk` using `congrArg (fun r => r.coeff i) hq`. Simplify using `only [q, finsetSum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq'] at hk`. Distinguish the cases in `hs : i ∈ G.support`. Simplify using `only [hs, if_true] at hk`.

Conclude with `hℓ hk`. Conclude with `hℓ (by simp [notMem_support_iff.mp hs])`.
-/
theorem coeff_mem_span (G : B[X]) (i : ℕ) :
    G.coeff i ∈ Submodule.span ℂ (Set.range fun u : ℂ => G.eval (algebraMap ℂ B u)) := by
  by_contra h
  obtain ⟨ℓ, hℓ, hker⟩ := Submodule.exists_le_ker_of_notMem h
  let q : ℂ[X] := ∑ j ∈ G.support, monomial j (ℓ (G.coeff j))
  have hq : q = 0 := by
    apply Polynomial.funext
    intro u
    have h0 : ℓ (G.eval (algebraMap ℂ B u)) = 0 := hker (Submodule.subset_span ⟨u, rfl⟩)
    rw [eval_eq_sum, Polynomial.sum, map_sum] at h0
    rw [eval_zero, ← h0, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, eval_monomial, smul_eq_mul,
      mul_comm]
  have hk := congrArg (fun r => r.coeff i) hq
  simp only [q, finsetSum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq'] at hk
  by_cases hs : i ∈ G.support
  · simp only [hs, if_true] at hk
    exact hℓ hk
  · exact hℓ (by simp [notMem_support_iff.mp hs])

/- English proof (translation)
Take `⟨P, hP⟩` from `hp`. Take `⟨G, hG⟩` from `hf`. Establish `key : P * (X - C Y) - G = 0`. Apply `eq_zero_of_eval` to reduce the goal to its premises. Introduce `u`.

Rewrite using `[eval_sub, eval_mul_scalar, ← hP, eval_sub, eval_X, eval_C, h, ← hG, sub_self]`. Establish `hGY : G.eval Y = 0`. Use `Polynomial.eval_mul_X_sub_C (p := P) Y` as an intermediate fact. Rewrite `this` using `[sub_eq_zero.mp key]`. Then use the resulting hypothesis. Set `g : ℂ → B` to `fun u => f u - algebraMap ℂ B (c.eval u)`.

Set `R : B[X]` to `G - c.map (algebraMap ℂ B)`. Establish `hRu : (fun u : ℂ => R.eval (algebraMap ℂ B u)) = g`. Use function extensionality and compare the values at `u`. Simplify using `only [R, g, eval_sub, ← hG, eval_map_apply]`. Establish `gg : ∀ u v, Commute (g u) (g v)` using `fun u v => ((hcomm u v).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commute_algebraMap_left _ _))`.

Establish `gY : ∀ u, Commute (g u) Y` using `fun u => (hY u).sub_left (Algebra.commute_algebraMap_left _ _)`. Set `S` to `Submodule.span ℂ (Set.range g)`. Establish `c1 : ∀ x ∈ S, Commute x Y` using `fun x hx => Submodule.span_induction (p := fun x _ => Commute x Y) (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact gY u) (Commute.zero_left _) (fun _ _ _ _ h1 h2 => h1.add_left h2) (fun a _ _ h1 => h1.smul_left a) hx`. Establish `c2 : ∀ x ∈ S, ∀ v, Commute x (g v)` using `fun x hx v => Submodule.span_induction (p := fun x _ => Commute x (g v)) (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact gg u v) (Commute.zero_left _) (fun _ _ _ _ h1 h2 => h1.add_left h2) (fun a _ _ h1 => h1.smul_left a) hx`. Establish `c3 : ∀ x ∈ S, ∀ y ∈ S, Commute x y` using `fun x hx y hy => Submodule.span_induction (p := fun y _ => Commute x y) (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact c2 x hx u) (Commute.zero_right _) (fun _ _ _ _ h1 h2 => h1.add_right h2) (fun a _ _ h1 => h1.smul_right a) hy`.

Establish `c4 : ∀ x ∈ S, IsNilpotent x` using `fun x hx => Submodule.span_induction (p := fun x _ => IsNilpotent x) (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact hnil u) IsNilpotent.zero (fun x y hx hy h1 h2 => (c3 x hx y hy).isNilpotent_add h1 h2) (fun a _ _ h1 => h1.smul a) hx`. Establish `hcoef : ∀ i, R.coeff i ∈ S` using `fun i => by`. Use `coeff_mem_span R i` as an intermediate fact. Rewrite `this` using `[hRu]`. Then use the resulting hypothesis. Establish `hsum : IsNilpotent (R.eval Y)`.

Rewrite using `[eval_eq_sum, Polynomial.sum]`. Use `Commute.isNilpotent_sum (fun i _ => ?_) (fun i j _ _ => ?_)` and prove the remaining obligations. Conclude with `((c1 _ (hcoef i)).pow_right i).isNilpotent_mul_right (c4 _ (hcoef i))`. Conclude with `(((c3 _ (hcoef i) _ (hcoef j)).mul_right ((c1 _ (hcoef i)).pow_right j))).mul_left ((((c1 _ (hcoef j)).pow_right i).symm.mul_right ((Commute.refl Y).pow_pow i j)))`. Establish `e : aeval Y c = - R.eval Y`.

Simplify using `only [R, eval_sub, hGY, zero_sub, neg_neg, eval_map, aeval_def]`. Rewrite using `[e]`. Conclude with `hsum.neg`.
-/
theorem isNilpotent_aeval_of_resolvent {p f : ℂ → B} (hp : IsPolyFun p) (hf : IsPolyFun f) (Y : B)
    (c : ℂ[X]) (h : ∀ u, p u * (algebraMap ℂ B u - Y) = f u)
    (hnil : ∀ u, IsNilpotent (f u - algebraMap ℂ B (c.eval u)))
    (hcomm : ∀ u v, Commute (f u) (f v)) (hY : ∀ u, Commute (f u) Y) :
    IsNilpotent (aeval Y c) := by
  obtain ⟨P, hP⟩ := hp
  obtain ⟨G, hG⟩ := hf
  have key : P * (X - C Y) - G = 0 := by
    apply eq_zero_of_eval
    intro u
    rw [eval_sub, eval_mul_scalar, ← hP, eval_sub, eval_X, eval_C, h, ← hG, sub_self]
  have hGY : G.eval Y = 0 := by
    have := Polynomial.eval_mul_X_sub_C (p := P) Y
    rwa [sub_eq_zero.mp key] at this
  let g : ℂ → B := fun u => f u - algebraMap ℂ B (c.eval u)
  let R : B[X] := G - c.map (algebraMap ℂ B)
  have hRu : (fun u : ℂ => R.eval (algebraMap ℂ B u)) = g := by
    funext u
    simp only [R, g, eval_sub, ← hG, eval_map_apply]
  have gg : ∀ u v, Commute (g u) (g v) := fun u v =>
    ((hcomm u v).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commute_algebraMap_left _ _))
  have gY : ∀ u, Commute (g u) Y := fun u =>
    (hY u).sub_left (Algebra.commute_algebraMap_left _ _)
  let S := Submodule.span ℂ (Set.range g)
  have c1 : ∀ x ∈ S, Commute x Y := fun x hx =>
    Submodule.span_induction (p := fun x _ => Commute x Y)
      (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact gY u) (Commute.zero_left _)
      (fun _ _ _ _ h1 h2 => h1.add_left h2) (fun a _ _ h1 => h1.smul_left a) hx
  have c2 : ∀ x ∈ S, ∀ v, Commute x (g v) := fun x hx v =>
    Submodule.span_induction (p := fun x _ => Commute x (g v))
      (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact gg u v) (Commute.zero_left _)
      (fun _ _ _ _ h1 h2 => h1.add_left h2) (fun a _ _ h1 => h1.smul_left a) hx
  have c3 : ∀ x ∈ S, ∀ y ∈ S, Commute x y := fun x hx y hy =>
    Submodule.span_induction (p := fun y _ => Commute x y)
      (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact c2 x hx u) (Commute.zero_right _)
      (fun _ _ _ _ h1 h2 => h1.add_right h2) (fun a _ _ h1 => h1.smul_right a) hy
  have c4 : ∀ x ∈ S, IsNilpotent x := fun x hx =>
    Submodule.span_induction (p := fun x _ => IsNilpotent x)
      (fun _ hy => by obtain ⟨u, rfl⟩ := hy; exact hnil u) IsNilpotent.zero
      (fun x y hx hy h1 h2 => (c3 x hx y hy).isNilpotent_add h1 h2)
      (fun a _ _ h1 => h1.smul a) hx
  have hcoef : ∀ i, R.coeff i ∈ S := fun i => by
    have := coeff_mem_span R i
    rwa [hRu] at this
  have hsum : IsNilpotent (R.eval Y) := by
    rw [eval_eq_sum, Polynomial.sum]
    refine Commute.isNilpotent_sum (fun i _ => ?_) (fun i j _ _ => ?_)
    · exact ((c1 _ (hcoef i)).pow_right i).isNilpotent_mul_right (c4 _ (hcoef i))
    · exact (((c3 _ (hcoef i) _ (hcoef j)).mul_right
        ((c1 _ (hcoef i)).pow_right j))).mul_left
        ((((c1 _ (hcoef j)).pow_right i).symm.mul_right ((Commute.refl Y).pow_pow i j)))
  have e : aeval Y c = - R.eval Y := by
    simp only [R, eval_sub, hGY, zero_sub, neg_neg, eval_map, aeval_def]
  rw [e]
  exact hsum.neg

end Abstract

section Split

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, map_one]`. Introduce `v hv`. Establish `: v = 0` using `hv`.

Simplify using `[this]`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime, Finset.iSup_insert]`. Use `sup_le_sup ?_ ih` and prove the remaining obligations. Introduce `v hv`.

Rewrite using `[Module.End.mem_maxGenEigenspace]`. Use `⟨L, ?_⟩` and prove the remaining obligations. Establish `e : aeval T ((X - C a) ^ L) = (T - a • (1 : Module.End ℂ W)) ^ L`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Rewrite `hv` using `[LinearMap.mem_ker, e]`. Then use the resulting hypothesis.

Use `IsCoprime.prod_right fun z hz => IsCoprime.pow ?_` and prove the remaining obligations. Conclude with `pairwise_coprime_X_sub_C (s := id) Function.injective_id (fun e : a = z => ha (e ▸ hz))`.
-/
theorem ker_aeval_prod_le (T : Module.End ℂ W) (S : Finset ℂ) (L : ℕ) :
    LinearMap.ker (aeval T (∏ z ∈ S, (X - C z) ^ L)) ≤ ⨆ z ∈ S, T.maxGenEigenspace z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, map_one]
    intro v hv
    have : v = 0 := hv
    simp [this]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime,
      Finset.iSup_insert]
    · refine sup_le_sup ?_ ih
      intro v hv
      rw [Module.End.mem_maxGenEigenspace]
      refine ⟨L, ?_⟩
      have e : aeval T ((X - C a) ^ L) = (T - a • (1 : Module.End ℂ W)) ^ L := by
        simp [Algebra.algebraMap_eq_smul_one]
      rwa [LinearMap.mem_ker, e] at hv
    · refine IsCoprime.prod_right fun z hz => IsCoprime.pow ?_
      exact pairwise_coprime_X_sub_C (s := id) Function.injective_id
        (fun e : a = z => ha (e ▸ hz))

/- English proof (translation)
Set `q : ℂ[X]` to `∏ z ∈ univ.image a, (X - C z)`. Establish `hd : (∏ s, (X - C (a s)) : ℂ[X]) ∣ q ^ (Fintype.card ι)`. Rewrite using `[← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Finset.prod_dvd_prod_of_dvd _ _ fun s _ => Finset.dvd_prod_of_mem (fun z => X - C z) (mem_image_of_mem a (mem_univ s))`. Take `⟨r, hr⟩` from `pow_dvd_pow_of_dvd hd K`.

Establish `h0 : aeval T (∏ z ∈ univ.image a, (X - C z) ^ (Fintype.card ι * K)) = 0`. Rewrite using `[Finset.prod_pow, pow_mul]`. Express the relevant statement in the definitionally equal form `aeval T ((q ^ Fintype.card ι) ^ K) = 0`. Rewrite using `[hr, map_mul, map_pow, h, zero_mul]`. Establish `hk` using `ker_aeval_prod_le T (univ.image a) (Fintype.card ι * K)`.

Rewrite `hk` using `[h0, LinearMap.ker_zero]`. Rewrite using `[eq_top_iff]`. Use `hk.trans (iSup₂_le fun z hz => ?_)` and prove the remaining obligations. Take `⟨s, _, rfl⟩` from `mem_image.mp hz`. Conclude with `le_iSup (fun s => T.maxGenEigenspace (a s)) s`.
-/
theorem iSup_maxGen_eq_top {ι : Type*} [Fintype ι] (T : Module.End ℂ W) (a : ι → ℂ) (K : ℕ)
    (h : (aeval T (∏ s, (X - C (a s)))) ^ K = 0) : ⨆ s, T.maxGenEigenspace (a s) = ⊤ := by
  classical
  let q : ℂ[X] := ∏ z ∈ univ.image a, (X - C z)
  have hd : (∏ s, (X - C (a s)) : ℂ[X]) ∣ q ^ (Fintype.card ι) := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun s _ =>
      Finset.dvd_prod_of_mem (fun z => X - C z) (mem_image_of_mem a (mem_univ s))
  obtain ⟨r, hr⟩ := pow_dvd_pow_of_dvd hd K
  have h0 : aeval T (∏ z ∈ univ.image a, (X - C z) ^ (Fintype.card ι * K)) = 0 := by
    rw [Finset.prod_pow, pow_mul]
    change aeval T ((q ^ Fintype.card ι) ^ K) = 0
    rw [hr, map_mul, map_pow, h, zero_mul]
  have hk := ker_aeval_prod_le T (univ.image a) (Fintype.card ι * K)
  rw [h0, LinearMap.ker_zero] at hk
  rw [eq_top_iff]
  refine hk.trans (iSup₂_le fun z hz => ?_)
  obtain ⟨s, _, rfl⟩ := mem_image.mp hz
  exact le_iSup (fun s => T.maxGenEigenspace (a s)) s

end Split

section Concrete

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def colOp (M : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Fin n → V) where
  toFun w := fun i => ∑ j, M i j (w j)
  map_add' u v := by funext i; simp [sum_add_distrib]
  map_smul' c u := by funext i; simp [smul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colOp_apply (M : Fin n → Fin n → Module.End ℂ V) (w : Fin n → V) (i : Fin n) :
    colOp M w i = ∑ j, M i j (w j) := rfl

/- English proof (translation)
Use `LinearMap.ext fun w => funext fun i => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, colOp_apply, map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_comm`.
-/
theorem colOp_mul (M N : Fin n → Fin n → Module.End ℂ V) :
    colOp M * colOp N = colOp (fun a d => ∑ b, M a b * N b d) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  simp only [Module.End.mul_apply, colOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

def diagHom : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Fin n → V) where
  toFun T := T.compLeft (Fin n)
  map_one' := LinearMap.ext fun w => funext fun i => rfl
  map_mul' S T := LinearMap.ext fun w => funext fun i => rfl
  map_zero' := LinearMap.ext fun w => funext fun i => rfl
  map_add' S T := LinearMap.ext fun w => funext fun i => rfl
  commutes' c := LinearMap.ext fun w => funext fun i => by
    show (algebraMap ℂ (Module.End ℂ V) c) (w i) = (algebraMap ℂ (Module.End ℂ (Fin n → V)) c) w i
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagHom_apply (T : Module.End ℂ V) (w : Fin n → V) (i : Fin n) :
    diagHom T w i = T (w i) := rfl

/- English proof (translation)
Use `LinearMap.ext fun w => funext fun i => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, diagHom_apply, colOp_apply]`. Use `symm`. Rewrite using `[Finset.sum_eq_single i]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[eOp]`. Introduce `a _ ha`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Simplify using `[eOp, Ne.symm ha]`. Simplify using the standard rewrite rules.
-/
theorem colOp_eq_sum (M : Fin n → Fin n → Module.End ℂ V) :
    colOp M = ∑ a, ∑ b, diagHom (M a b) * eOp V a b := by
  refine LinearMap.ext fun w => funext fun i => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, diagHom_apply, colOp_apply]
  symm
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [eOp]
  · intro a _ ha
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [eOp, Ne.symm ha]
  · simp

/- English proof (translation)
Simplify using `only [colOp_eq_sum]`. Conclude with `IsPolyFun.sum _ _ fun a => IsPolyFun.sum _ _ fun b => ((h a b).map diagHom).mul (IsPolyFun.const _)`.
-/
theorem isPoly_colOp (M : ℂ → Fin n → Fin n → Module.End ℂ V)
    (h : ∀ a b, IsPolyFun fun u => M u a b) : IsPolyFun fun u => colOp (M u) := by
  simp only [colOp_eq_sum]
  exact IsPolyFun.sum _ _ fun a => IsPolyFun.sum _ _ fun b =>
    ((h a b).map diagHom).mul (IsPolyFun.const _)

/- English proof (translation)
Use `LinearMap.ext fun w => funext fun i => ?_` and prove the remaining obligations. Apply the tactic sequence `have e : ∀ j, (if i = j then T else 0) (w j) = if i = j then T (w j) else 0 := fun j => by split_ifs <;> simp`. Simplify using `only [colOp_apply, diagHom_apply, e, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem colOp_diag (T : Module.End ℂ V) :
    colOp (fun i l : Fin n => if i = l then T else 0) = diagHom T := by
  refine LinearMap.ext fun w => funext fun i => ?_
  have e : ∀ j, (if i = j then T else 0) (w j) = if i = j then T (w j) else 0 := fun j => by
    split_ifs <;> simp
  simp only [colOp_apply, diagHom_apply, e, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Concrete

/- English proof (translation)
Introduce `a b c d`. Establish `h` using `hE d c b a`. Simplify using `only [neg_mul_neg]`. Establish `h0 : E b a * E d c - E d c * E b a = -(E d c * E b a - E b a * E d c)` using `by abel`. Rewrite using `[h0, h]`.

Simplify using `only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]`. Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem glRel_negT {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel (fun a b => -E b a) := by
  intro a b c d
  have h := hE d c b a
  simp only [neg_mul_neg]
  have h0 : E b a * E d c - E d c * E b a = -(E d c * E b a - E b a * E d c) := by abel
  rw [h0, h]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]
  split_ifs <;> abel

/- English proof (translation)
Unfold `qdet qminor`. Use `Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_` and prove the remaining obligations. Use `Commute.list_prod_right _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hy`. Use `Commute.add_right ?_ (h _ _)` and prove the remaining obligations.

Use `split_ifs`. Conclude with `Algebra.commute_algebraMap_right _ _`. Conclude with `Commute.zero_right _`.
-/
theorem commute_qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {z : A}
    (h : ∀ a b, Commute z (E a b)) (u : ℂ) : Commute z (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

section Main

variable {n : ℕ}

def negT (M : GMod n) : Fin n → Fin n → Module.End ℂ M.V := fun a b => -M.E b a

/- English proof (translation)
Use `LinearMap.ext fun w => funext fun i => ?_` and prove the remaining obligations. Apply the tactic sequence `have e : ∀ j, (if i = j then algebraMap ℂ (Module.End ℂ M.V) v else 0) (w j) = if i = j then v • w j else 0 := fun j => by split_ifs <;> simp`. Simplify using `only [colOp_apply, Tm, negT, LinearMap.add_apply, LinearMap.neg_apply, sum_add_distrib, sum_neg_distrib, om_apply, e, Finset.sum_ite_eq, Finset.mem_univ, if_true, Module.algebraMap_end_apply, Pi.smul_apply, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply]`.
-/
theorem colOp_Tm (M : GMod n) (v : ℂ) :
    colOp (Tm (negT M) v) = algebraMap ℂ _ v - om M := by
  refine LinearMap.ext fun w => funext fun i => ?_
  have e : ∀ j, (if i = j then algebraMap ℂ (Module.End ℂ M.V) v else 0) (w j) =
      if i = j then v • w j else 0 := fun j => by
    split_ifs <;> simp
  simp only [colOp_apply, Tm, negT, LinearMap.add_apply, LinearMap.neg_apply, sum_add_distrib,
    sum_neg_distrib, om_apply, e, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Module.algebraMap_end_apply, Pi.smul_apply, sub_eq_add_neg,
    Pi.add_apply, Pi.neg_apply]

def coM {m : ℕ} (M : GMod (m + 1)) (u : ℂ) (i j : Fin (m + 1)) : Module.End ℂ M.V :=
  (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ M.V) *
    qminor (negT M) (Fin.succAbove j) (Fin.succAbove i) u

/- English proof (translation)
Establish `e : algebraMap ℂ (Module.End ℂ (Fin (m + 1) → M.V)) u - om M = colOp (Tm (negT M) (u + m - m))`. Rewrite using `[colOp_Tm, add_sub_cancel_right]`. Rewrite using `[e, colOp_mul, ← colOp_diag]`. Use `congr 1`. Use function extensionality and compare the values at `i l`.

Conclude with `qComatrix _ m (negT M) (glRel_negT M.gl) (u + m) i l`.
-/
theorem resolvent {m : ℕ} (M : GMod (m + 1)) (u : ℂ) :
    colOp (coM M (u + m)) * (algebraMap ℂ _ u - om M) = diagHom (qdet (negT M) (u + m)) := by
  have e : algebraMap ℂ (Module.End ℂ (Fin (m + 1) → M.V)) u - om M =
      colOp (Tm (negT M) (u + m - m)) := by
    rw [colOp_Tm, add_sub_cancel_right]
  rw [e, colOp_mul, ← colOp_diag]
  congr 1
  funext i l
  exact qComatrix _ m (negT M) (glRel_negT M.gl) (u + m) i l

/- English proof (translation)
Use `LinearMap.ext fun w => funext fun b => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, diagHom_apply, om_apply, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `LinearMap.congr_fun (h a b).eq (w a)`.
-/
theorem commute_diag_om (M : GMod n) (T : Module.End ℂ M.V) (h : ∀ a b, Commute T (M.E a b)) :
    Commute (diagHom T) (om M) := by
  refine LinearMap.ext fun w => funext fun b => ?_
  simp only [Module.End.mul_apply, diagHom_apply, om_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact LinearMap.congr_fun (h a b).eq (w a)

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Establish `hF` using `glRel_negT M.gl`. Establish `hcen : ∀ u c d, Commute (qdet (negT M) u) (negT M c d)` using `fun u c d => qDetCentral _ _ _ hF u c d`. Use `isNilpotent_aeval_of_resolvent (p := fun u => colOp (coM M (u + m))) (f := fun u => diagHom (qdet (negT M) (u + m))) ?_ ?_ (om M) _ (fun u => resolvent M u) ?_ ?_ ?_` and prove the remaining obligations. Conclude with `isPoly_colOp _ fun i j => (IsPolyFun.const _).mul (isPoly_qminor _ _ _ _)`.

Conclude with `(isPoly_qminor (negT M) id id _).map diagHom`. Introduce `u`. Establish `e1 : qdet (negT M) (u + m) = ((-1 : ℂ) ^ (m + 1)) • qdet M.E (((m + 1 : ℕ) : ℂ) - 1 - (u + m))` using `Formalism.HermitianLatticeCounting.P.quantumDet_neg_transpose M.E M.gl _`. Set `Yv : ℂ` to `-u - (m : ℂ) / 2`. Establish `e2 : ((m + 1 : ℕ) : ℂ) - 1 - (u + m) = Yv + (((m + 1 : ℕ) : ℂ) - 1) / 2`.

Simplify using `only [Yv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : eval u (∏ s, (X - C (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2))) = ((-1 : ℂ) ^ (m + 1)) * Formalism.QuantumDeterminants.capP χ Yv`. Establish `hs : ((-1 : ℂ) ^ (m + 1)) = ∏ _s : Fin (m + 1), (-1 : ℂ)` using `by simp`.

Rewrite using `[hs, Formalism.QuantumDeterminants.capP, ← Finset.prod_mul_distrib, eval_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [eval_sub, eval_X, eval_C, Yv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `e4 : diagHom (n` using `m + 1) (qdet (negT M) (u + m)) - algebraMap ℂ _ (eval u (∏ s, (X - C (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)))) = diagHom (n := m + 1) (((-1 : ℂ) ^ (m + 1)) • (qdet M.E (Yv + (((m + 1 : ℕ) : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ Yv • (1 : Module.End ℂ M.V))) := by`. Rewrite using `[e1, e2, e3, smul_sub, smul_smul, map_sub]`. Use `congr 1`. Use `beta_reduce`. Rewrite using `[e4]`.

Conclude with `IsNilpotent.map (IsNilpotent.smul ⟨k, hk Yv⟩ _) diagHom`. Introduce `u v`. Conclude with `(commute_qdet (fun a b => hcen (u + m) a b) (v + m)).map diagHom`. Introduce `u`. Use `commute_diag_om M _ fun a b => ?_` and prove the remaining obligations.

Use `hcen (u + m) b a` as an intermediate fact. Simplify `this` using `[negT]`.
-/
theorem isNilpotent_om (m : ℕ) (M : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (h : HasChar M χ) :
    IsNilpotent (aeval (om M) (∏ s, (X - C (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)))) := by
  obtain ⟨k, hk⟩ := h
  have hF := glRel_negT M.gl
  have hcen : ∀ u c d, Commute (qdet (negT M) u) (negT M c d) := fun u c d =>
    qDetCentral _ _ _ hF u c d
  refine isNilpotent_aeval_of_resolvent (p := fun u => colOp (coM M (u + m)))
    (f := fun u => diagHom (qdet (negT M) (u + m))) ?_ ?_ (om M) _ (fun u => resolvent M u) ?_ ?_ ?_
  · exact isPoly_colOp _ fun i j => (IsPolyFun.const _).mul (isPoly_qminor _ _ _ _)
  · exact (isPoly_qminor (negT M) id id _).map diagHom
  · intro u
    have e1 : qdet (negT M) (u + m) =
        ((-1 : ℂ) ^ (m + 1)) • qdet M.E (((m + 1 : ℕ) : ℂ) - 1 - (u + m)) :=
      Formalism.HermitianLatticeCounting.P.quantumDet_neg_transpose M.E M.gl _
    let Yv : ℂ := -u - (m : ℂ) / 2
    have e2 : ((m + 1 : ℕ) : ℂ) - 1 - (u + m) = Yv + (((m + 1 : ℕ) : ℂ) - 1) / 2 := by
      simp only [Yv]; push_cast; ring
    have e3 : eval u (∏ s, (X - C (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2))) =
        ((-1 : ℂ) ^ (m + 1)) * Formalism.QuantumDeterminants.capP χ Yv := by
      have hs : ((-1 : ℂ) ^ (m + 1)) = ∏ _s : Fin (m + 1), (-1 : ℂ) := by simp
      rw [hs, Formalism.QuantumDeterminants.capP, ← Finset.prod_mul_distrib, eval_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [eval_sub, eval_X, eval_C, Yv]
      push_cast
      ring
    have e4 : diagHom (n := m + 1) (qdet (negT M) (u + m)) -
        algebraMap ℂ _ (eval u (∏ s, (X - C (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)))) =
        diagHom (n := m + 1) (((-1 : ℂ) ^ (m + 1)) • (qdet M.E (Yv + (((m + 1 : ℕ) : ℂ) - 1) / 2) -
          Formalism.QuantumDeterminants.capP χ Yv • (1 : Module.End ℂ M.V))) := by
      rw [e1, e2, e3, smul_sub, smul_smul, map_sub]
      congr 1
    beta_reduce
    rw [e4]
    exact IsNilpotent.map (IsNilpotent.smul ⟨k, hk Yv⟩ _) diagHom
  · intro u v
    exact (commute_qdet (fun a b => hcen (u + m) a b) (v + m)).map diagHom
  · intro u
    refine commute_diag_om M _ fun a b => ?_
    have := hcen (u + m) b a
    simpa [negT] using this

/- English proof (translation)
Introduce `n M χ h`. Consider the cases of `n with`. Consider the case `zero => exact Subsingleton.elim _ _`. Consider the case `succ m`. Take `⟨K, hK⟩` from `isNilpotent_om m M χ h`.

Conclude with `iSup_maxGen_eq_top (om M) (fun r => χ r - (((m + 1 : ℕ) : ℂ) - 1) / 2) K hK`.
-/
theorem tensDecomp : CompanionTheory.RgExh.Dec.J.TensDecomp := by
  intro n M χ h
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    obtain ⟨K, hK⟩ := isNilpotent_om m M χ h
    exact iSup_maxGen_eq_top (om M) (fun r => χ r - (((m + 1 : ℕ) : ℂ) - 1) / 2) K hK

end Main

end GlobalTheory.CompanionTheory.TensStep
