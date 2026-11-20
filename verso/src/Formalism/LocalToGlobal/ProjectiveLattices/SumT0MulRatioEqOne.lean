import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain TensorProduct

/- English proof (translation)
Use `⟨fun x y => map_add _ x y, fun x y => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a m`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul b n`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_apply]`. Rewrite using `[hd.mul, TensorProduct.add_tmul, mul_comm n m]`. Consider the case `add y z hy hz`.

Rewrite using `[mul_add, map_add, hy, hz, map_add, mul_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x z hx hz`. Rewrite using `[add_mul, map_add, hx, hz, map_add, add_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isDer_tensor {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing M] [Algebra R M]
    (d : A →ₗ[R] A) (hd : IsDer d) : IsDer (TensorProduct.map d (LinearMap.id : M →ₗ[R] M)) := by
  refine ⟨fun x y => map_add _ x y, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b n =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [hd.mul, TensorProduct.add_tmul, mul_comm n m]
    | add y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, mul_add]
      ring
  | add x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, add_mul]
    ring

/- English proof (translation)
Distinguish the cases in `hy0 : y = 0`. Rewrite using `[hy0, div_zero, h.der_zero]`. Establish `e` using `h.mul (x / y) y`. Rewrite `e` using `[div_mul_cancel₀ x hy0, hx, hy, mul_zero, zero_add]`. Conclude with `(mul_eq_zero.mp e.symm).resolve_left hy0`.
-/
theorem der_div_eq_zero {L : Type*} [Field L] {δ : L → L} (h : IsDer δ) {x y : L} (hx : δ x = 0) (hy : δ y = 0) :
    δ (x / y) = 0 := by
  by_cases hy0 : y = 0
  · rw [hy0, div_zero, h.der_zero]
  · have e := h.mul (x / y) y
    rw [div_mul_cancel₀ x hy0, hx, hy, mul_zero, zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hy0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

/- English proof (translation)
Take `⟨δ, hδ, hf⟩` from `IsDer.ofLoc (gI X la N).primeCompl (fun f => algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f)) (fun x y => by simp only [map_add]) (fun x y => by simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul])`. Take `⟨δ', hδ', h'⟩` from `IsDer.ofLoc (nonZeroDivisors (Op X la N)) (fun z => algebraMap (Op X la N) (Kp X la N) (δ z)) (fun x y => by simp only [hδ.add, map_add]) (fun x y => by simp only [hδ.mul, map_add, map_mul])`. Establish `hval : ∀ f : Pol X la N, δ' (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) = algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f))`. Introduce `f`. Rewrite using `[h', hf]`.

Establish `hOl : ∀ a : X.Ol la, δ' (algebraMap (X.Ol la) (Kp X la N) a) = 0`. Introduce `a`. Establish `e : algebraMap (X.Ol la) (Kp X la N) a = algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C a))`. Rewrite using `[IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N), IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N), MvPolynomial.algebraMap_eq]`. Rewrite using `[e, hval, MvPolynomial.pderiv_C, map_zero, map_zero]`.

Use `⟨δ', hδ', hval, fun c => ?_⟩` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := X.Ol la) c`. Rewrite using `[map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Conclude with `der_div_eq_zero hδ' (hOl a) (hOl b)`.
-/
theorem exists_derKp (p : Idx D j N) : ∃ δ : Kp X la N → Kp X la N, IsDer δ ∧
    (∀ f : Pol X la N, δ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f))) ∧
    ∀ c : X.Kl la, δ (algebraMap (X.Kl la) (Kp X la N) c) = 0 := by
  obtain ⟨δ, hδ, hf⟩ := IsDer.ofLoc (gI X la N).primeCompl
    (fun f => algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f))
    (fun x y => by simp only [map_add])
    (fun x y => by simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul])
  obtain ⟨δ', hδ', h'⟩ := IsDer.ofLoc (nonZeroDivisors (Op X la N))
    (fun z => algebraMap (Op X la N) (Kp X la N) (δ z))
    (fun x y => by simp only [hδ.add, map_add]) (fun x y => by simp only [hδ.mul, map_add, map_mul])
  have hval : ∀ f : Pol X la N, δ' (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f)) := by
    intro f
    rw [h', hf]
  have hOl : ∀ a : X.Ol la, δ' (algebraMap (X.Ol la) (Kp X la N) a) = 0 := by
    intro a
    have e : algebraMap (X.Ol la) (Kp X la N) a =
        algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C a)) := by
      rw [IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N), MvPolynomial.algebraMap_eq]
    rw [e, hval, MvPolynomial.pderiv_C, map_zero, map_zero]
  refine ⟨δ', hδ', hval, fun c => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.Ol la) c
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact der_div_eq_zero hδ' (hOl a) (hOl b)

def dK (p : Idx D j N) : Kp X la N → Kp X la N := Classical.choose (exists_derKp X la N p)

/- English proof (translation)
The claim follows from `(Classical.choose_spec (exists_derKp X la N p)).1`.
-/
theorem dK_isDer (p : Idx D j N) : IsDer (dK X la N p) := (Classical.choose_spec (exists_derKp X la N p)).1

/- English proof (translation)
The claim follows from `(Classical.choose_spec (exists_derKp X la N p)).2.1 f`.
-/
theorem dK_pol (p : Idx D j N) (f : Pol X la N) :
    dK X la N p (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f)) :=
  (Classical.choose_spec (exists_derKp X la N p)).2.1 f

/- English proof (translation)
The claim follows from `(Classical.choose_spec (exists_derKp X la N p)).2.2 c`.
-/
theorem dK_Kl (p : Idx D j N) (c : X.Kl la) : dK X la N p (algebraMap (X.Kl la) (Kp X la N) c) = 0 :=
  (Classical.choose_spec (exists_derKp X la N p)).2.2 c

/- English proof (translation)
Use `dK_pol X la N p (MvPolynomial.X q)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.pderiv_X, Pi.single_apply]`. Rewrite using `[show Tv X la N q = algebraMap (Pol X la N) (Op X la N) (MvPolynomial.X q) from rfl, this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dK_Tv (p q : Idx D j N) :
    dK X la N p (algebraMap (Op X la N) (Kp X la N) (Tv X la N q)) = if q = p then 1 else 0 := by
  classical
  have := dK_pol X la N p (MvPolynomial.X q)
  rw [MvPolynomial.pderiv_X, Pi.single_apply] at this
  rw [show Tv X la N q = algebraMap (Pol X la N) (Op X la N) (MvPolynomial.X q) from rfl, this]
  split_ifs <;> simp

def dKl (p : Idx D j N) : Kp X la N →ₗ[X.Kl la] Kp X la N where
  toFun := dK X la N p
  map_add' := (dK_isDer X la N p).add
  map_smul' c x := by
    rw [Algebra.smul_def, (dK_isDer X la N p).mul, dK_Kl, mul_zero, add_zero, RingHom.id_apply, Algebra.smul_def]

def dR (p : Idx D j N) : Rp X la N → Rp X la N := fun r =>
  TensorProduct.map (dKl X la N p) (LinearMap.id : X.Vl la →ₗ[X.Kl la] X.Vl la) r

/- English proof (translation)
The claim follows from `isDer_tensor (dKl X la N p) (dK_isDer X la N p)`.
-/
theorem dR_isDer (p : Idx D j N) : IsDer (dR X la N p) :=
  isDer_tensor (dKl X la N p) (dK_isDer X la N p)

/- English proof (translation)
Use `show TensorProduct.map (dKl X la N p) LinearMap.id (c ⊗ₜ[X.Kl la] (1 : X.Vl la)) = dK X la N p c ⊗ₜ[X.Kl la] (1 : X.Vl la)`. Rewrite using `[TensorProduct.map_tmul, LinearMap.id_apply]`. Both sides reduce to the same expression.
-/
theorem dR_algebraMap (p : Idx D j N) (c : Kp X la N) :
    dR X la N p (algebraMap (Kp X la N) (Rp X la N) c) = algebraMap (Kp X la N) (Rp X la N) (dK X la N p c) := by
  show TensorProduct.map (dKl X la N p) LinearMap.id (c ⊗ₜ[X.Kl la] (1 : X.Vl la)) = dK X la N p c ⊗ₜ[X.Kl la] (1 : X.Vl la)
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

/- English proof (translation)
Use `show TensorProduct.map (dKl X la N p) LinearMap.id ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = 0`. Rewrite using `[TensorProduct.map_tmul]`. Use `show dK X la N p 1 ⊗ₜ[X.Kl la] _ = 0`. Rewrite using `[(dK_isDer X la N p).der_one, TensorProduct.zero_tmul]`.
-/
theorem dR_emb (p : Idx D j N) (F : X.Forms) : dR X la N p (emb X la N F) = 0 := by
  show TensorProduct.map (dKl X la N p) LinearMap.id ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = 0
  rw [TensorProduct.map_tmul]
  show dK X la N p 1 ⊗ₜ[X.Kl la] _ = 0
  rw [(dK_isDer X la N p).der_one, TensorProduct.zero_tmul]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, (dR_isDer X la N p).mul, dR_algebraMap, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dR_smul (p : Idx D j N) (c : Kp X la N) (r : Rp X la N) :
    dR X la N p (c • r) = dK X la N p c • r + c • dR X la N p r := by
  rw [Algebra.smul_def, (dR_isDer X la N p).mul, dR_algebraMap, Algebra.smul_def, Algebra.smul_def]
  ring

/- English proof (translation)
Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, rfl⟩` from `hx`. Rewrite using `[dR_emb]`. Conclude with `Submodule.zero_mem _`.

Consider the case `zero => rw [(dR_isDer X la N p).der_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [(dR_isDer X la N p).add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x hx0 hx`.

Rewrite using `[dR_smul]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ hx0) (Submodule.smul_mem _ _ hx)`.
-/
theorem dR_Vw (p : Idx D j N) (u : WeightFamilies.Wt D j) {r : Rp X la N} (hr : r ∈ Vw X la N u) :
    dR X la N p r ∈ Vw X la N u := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, rfl⟩ := hx
    rw [dR_emb]
    exact Submodule.zero_mem _
  | zero => rw [(dR_isDer X la N p).der_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [(dR_isDer X la N p).add]; exact Submodule.add_mem _ hx hy
  | smul c x hx0 hx =>
    rw [dR_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx0) (Submodule.smul_mem _ _ hx)

section Sec

variable {X la N} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

/- English proof (translation)
Unfold `sec`. Rewrite using `[(dR_isDer X la N (0, l)).der_sum]`. Simplify using `only [dR_smul, dR_emb, smul_zero, add_zero, dK_Tv, Prod.mk.injEq]`. Use `split_ifs with hi`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hi]`.
-/
theorem dR_sec (l : Fin N) (i : Fin (WeightFamilies.dimY D j + 1)) :
    dR X la N (0, l) (sec X la w i) = if i = 0 then emb X la N (X.inc wL (w l)) else 0 := by
  classical
  unfold sec
  rw [(dR_isDer X la N (0, l)).der_sum]
  simp only [dR_smul, dR_emb, smul_zero, add_zero, dK_Tv, Prod.mk.injEq]
  split_ifs with hi
  · subst hi
    simp
  · simp [hi]

end Sec

section Lw

variable {N} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (l : Fin N)

/- English proof (translation)
The claim follows from `IsDer.ofLoc (Submonoid.powers (sec X la w 0)) (fun r => algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r)) (fun x y => by simp only [(dR_isDer X la N (0, l)).add, map_add]) (fun x y => by simp only [(dR_isDer X la N (0, l)).mul, map_add, map_mul])`.
-/
theorem exists_derLw : ∃ δ : Lw X la w → Lw X la w, IsDer δ ∧
    ∀ r, δ (algebraMap (Rp X la N) (Lw X la w) r) = algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r) :=
  IsDer.ofLoc (Submonoid.powers (sec X la w 0)) (fun r => algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r))
    (fun x y => by simp only [(dR_isDer X la N (0, l)).add, map_add])
    (fun x y => by simp only [(dR_isDer X la N (0, l)).mul, map_add, map_mul])

def dL : Lw X la w → Lw X la w := Classical.choose (exists_derLw X la w l)

/- English proof (translation)
The claim follows from `(Classical.choose_spec (exists_derLw X la w l)).1`.
-/
theorem dL_isDer : IsDer (dL X la w l) := (Classical.choose_spec (exists_derLw X la w l)).1

/- English proof (translation)
The claim follows from `(Classical.choose_spec (exists_derLw X la w l)).2 r`.
-/
theorem dL_alg (r : Rp X la N) :
    dL X la w l (algebraMap (Rp X la N) (Lw X la w) r) = algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r) :=
  (Classical.choose_spec (exists_derLw X la w l)).2 r

/- English proof (translation)
Establish `h` using `section_mul_inverse_eq_one X la w`. Establish `e1` using `(dL_isDer X la w l).mul (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0)) (w0inv X la w)`. Rewrite `e1` using `[h, (dL_isDer X la w l).der_one, dL_alg, dR_sec, if_pos rfl]`. Take the linear combination `(-(w0inv X la w)) * e1 - dL X la w l (w0inv X la w) * h`.
-/
theorem dL_w0inv : dL X la w l (w0inv X la w) =
    -(w0inv X la w ^ 2 * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w l)))) := by
  have h := section_mul_inverse_eq_one X la w
  have e1 := (dL_isDer X la w l).mul (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0)) (w0inv X la w)
  rw [h, (dL_isDer X la w l).der_one, dL_alg, dR_sec, if_pos rfl] at e1
  linear_combination (-(w0inv X la w)) * e1 - dL X la w l (w0inv X la w) * h

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => simp [(dL_isDer X la w l).der_one]`. Consider the case `succ k`. Rewrite using `[(dL_isDer X la w l).der_pow_succ, dL_w0inv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dL_w0inv_pow (k : ℕ) : dL X la w l (w0inv X la w ^ k) =
    -((k : Lw X la w) * w0inv X la w ^ (k + 1) * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w l)))) := by
  cases k with
  | zero => simp [(dL_isDer X la w l).der_one]
  | succ k =>
    rw [(dL_isDer X la w l).der_pow_succ, dL_w0inv]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[frac_apply, frac_apply, frac_apply, (dL_isDer X la w l).mul, dL_w0inv_pow, dL_alg, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dL_frac (k : ℕ) (g : Rp X la N) : dL X la w l (frac X la w k g) =
    frac X la w k (dR X la N (0, l) g) - (k : Lw X la w) * frac X la w (k + 1) (emb X la N (X.inc wL (w l)) * g) := by
  rw [frac_apply, frac_apply, frac_apply, (dL_isDer X la w l).mul, dL_w0inv_pow, dL_alg, map_mul]
  ring

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)))`.
-/
theorem mem_Frac0_emb (k : Fin N) :
    frac X la w 1 (emb X la N (X.inc wL (w k))) ∈ Frac0 X la w :=
  Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)))

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_Frac0]`. Take `⟨k, g, hg, rfl⟩` from `(mem_Hfr X la w).1 hx`. Rewrite using `[dL_frac]`. Use `Submodule.sub_mem _ (frac_mem_Hfr X la w (dR_Vw X la N (0, l) _ hg)) ?_` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul]`.

Use `nsmul_mem (frac_mem_Hfr X la w ?_) k` and prove the remaining obligations. Use `mul_mem_Vw X la N (emb_mem_Vw X la N wL (w l)) hg` as an intermediate fact. Rewrite `this` using `[wadd_addL]`. Then use the resulting hypothesis.
-/
theorem dL_mem {x : Lw X la w} (hx : x ∈ Frac0 X la w) : dL X la w l x ∈ Frac0 X la w := by
  rw [mem_Frac0] at hx ⊢
  obtain ⟨k, g, hg, rfl⟩ := (mem_Hfr X la w).1 hx
  rw [dL_frac]
  refine Submodule.sub_mem _ (frac_mem_Hfr X la w (dR_Vw X la N (0, l) _ hg)) ?_
  rw [← nsmul_eq_mul]
  refine nsmul_mem (frac_mem_Hfr X la w ?_) k
  have := mul_mem_Vw X la N (emb_mem_Vw X la N wL (w l)) hg
  rwa [wadd_addL] at this

def dF : Frac0 X la w → Frac0 X la w := fun x => ⟨dL X la w l x, dL_mem X la w l x.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y => Subtype.ext ((dL_isDer X la w l).add x y), fun x y => Subtype.ext ((dL_isDer X la w l).mul x y)⟩`.
-/
theorem dF_isDer : IsDer (dF X la w l) :=
  ⟨fun x y => Subtype.ext ((dL_isDer X la w l).add x y), fun x y => Subtype.ext ((dL_isDer X la w l).mul x y)⟩

def xr (k : Fin N) : Frac0 X la w := ⟨frac X la w 1 (emb X la N (X.inc wL (w k))), mem_Frac0_emb X la w k⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show dL X la w l (frac X la w 1 (emb X la N (X.inc wL (w k)))) = -(frac X la w 1 (emb X la N (X.inc wL (w k))) * frac X la w 1 (emb X la N (X.inc wL (w l))))`. Rewrite using `[dL_frac, dR_emb, map_zero, zero_sub, frac_mul, Nat.cast_one, one_mul, mul_comm (emb X la N _)]`.
-/
theorem dF_xr (k : Fin N) : dF X la w l (xr X la w k) = -(xr X la w k * xr X la w l) := by
  apply Subtype.ext
  show dL X la w l (frac X la w 1 (emb X la N (X.inc wL (w k)))) =
    -(frac X la w 1 (emb X la N (X.inc wL (w k))) * frac X la w 1 (emb X la N (X.inc wL (w l))))
  rw [dL_frac, dR_emb, map_zero, zero_sub, frac_mul, Nat.cast_one, one_mul, mul_comm (emb X la N _)]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show dL X la w l (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) (dK X la N (0, l) c)`. Rewrite using `[IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), dL_alg, dR_algebraMap, ← IsScalarTower.algebraMap_apply]`.
-/
theorem dF_algebraMap (c : Kp X la N) :
    dF X la w l (algebraMap (Kp X la N) (Frac0 X la w) c) = algebraMap (Kp X la N) (Frac0 X la w) (dK X la N (0, l) c) := by
  apply Subtype.ext
  show dL X la w l (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) (dK X la N (0, l) c)
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), dL_alg, dR_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Establish `e : dF X la w l (sfr X la w i.succ) = -(sfr X la w i.succ * ⟨frac X la w 1 (emb X la N (X.inc wL (w l))), mem_Frac0_emb X la w l⟩)`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show dL X la w l (frac X la w 1 (sec X la w i.succ)) = -(frac X la w 1 (sec X la w i.succ) * frac X la w 1 (emb X la N (X.inc wL (w l))))`. Rewrite using `[dL_frac, dR_sec, if_neg (Fin.succ_ne_zero i), map_zero, zero_sub, frac_mul, Nat.cast_one, one_mul, mul_comm (emb X la N _)]`. Rewrite using `[e]`. Conclude with `neg_mem (Ideal.mul_mem_right _ _ (sfr_succ_mem_Jid X la w i))`. Consider the case `zero => rw [(dF_isDer X la w l).der_zero]`.

Conclude with `Ideal.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [(dF_isDer X la w l).add]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `smul a x hx0 hx`. Rewrite using `[smul_eq_mul, (dF_isDer X la w l).mul]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)`.
-/
theorem dF_Jid {x : Frac0 X la w} (hx : x ∈ Jid X la w) : dF X la w l x ∈ Jid X la w := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have e : dF X la w l (sfr X la w i.succ) = -(sfr X la w i.succ * ⟨frac X la w 1 (emb X la N (X.inc wL (w l))),
        mem_Frac0_emb X la w l⟩) := by
      apply Subtype.ext
      show dL X la w l (frac X la w 1 (sec X la w i.succ)) = -(frac X la w 1 (sec X la w i.succ) *
        frac X la w 1 (emb X la N (X.inc wL (w l))))
      rw [dL_frac, dR_sec, if_neg (Fin.succ_ne_zero i), map_zero, zero_sub, frac_mul, Nat.cast_one, one_mul,
        mul_comm (emb X la N _)]
    rw [e]
    exact neg_mem (Ideal.mul_mem_right _ _ (sfr_succ_mem_Jid X la w i))
  | zero => rw [(dF_isDer X la w l).der_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [(dF_isDer X la w l).add]; exact Ideal.add_mem _ hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, (dF_isDer X la w l).mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

/- English proof (translation)
Take `⟨δ, hδ, h⟩` from `(dF_isDer X la w l).quot (Jid X la w) (fun x hx => dF_Jid X la w l hx)`. Conclude with `⟨δ, hδ, fun x => h x⟩`.
-/
theorem exists_derOsK : ∃ δ : OsK X la w → OsK X la w, IsDer δ ∧
    ∀ x, δ (toOsK X la w x) = toOsK X la w (dF X la w l x) := by
  obtain ⟨δ, hδ, h⟩ := (dF_isDer X la w l).quot (Jid X la w) (fun x hx => dF_Jid X la w l hx)
  exact ⟨δ, hδ, fun x => h x⟩

/- English proof (translation)
Establish `e : ∀ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) * frac X la w 1 (emb X la N (X.inc wL (w k))) = frac X la w 1 ((algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) • emb X la N (X.inc wL (w k)))`. Introduce `k`. Rewrite using `[LinearMap.map_smul, Algebra.smul_def]`. Establish `hL : ∑ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) * frac X la w 1 (emb X la N (X.inc wL (w k))) = 1`. Repeatedly rewrite using `[e]`.

Rewrite using `[← map_sum]`. Use `show frac X la w 1 (sec X la w 0) = 1`. Rewrite using `[frac_apply, pow_one, section_mul_inverse_eq_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (Frac0 X la w).val (∑ k, _) = (Frac0 X la w).val 1`.

Rewrite using `[map_sum, map_one]`. Simplify using `only [map_mul, AlgHom.commutes]`. Conclude with `hL`.
-/
theorem sum_T0_mul_ratio_eq_one : ∑ k, algebraMap (Kp X la N) (Frac0 X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
    xr X la w k = 1 := by
  have e : ∀ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
      frac X la w 1 (emb X la N (X.inc wL (w k))) = frac X la w 1
        ((algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) • emb X la N (X.inc wL (w k))) := by
    intro k
    rw [LinearMap.map_smul, Algebra.smul_def]
  have hL : ∑ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
      frac X la w 1 (emb X la N (X.inc wL (w k))) = 1 := by
    simp_rw [e]
    rw [← map_sum]
    show frac X la w 1 (sec X la w 0) = 1
    rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  apply Subtype.ext
  show (Frac0 X la w).val (∑ k, _) = (Frac0 X la w).val 1
  rw [map_sum, map_one]
  simp only [map_mul, AlgHom.commutes]
  exact hL

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show (Frac0 X la w).val (sfr X la w i.succ) = (Frac0 X la w).val (∑ k, _)`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, AlgHom.commutes]`. Use `show frac X la w 1 (sec X la w i.succ) = ∑ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i.succ, k))) * frac X la w 1 (emb X la N (X.inc wL (w k)))`.

Unfold `sec`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, Algebra.smul_def]`.
-/
theorem sfr_eq_sum (i : Fin (WeightFamilies.dimY D j)) : sfr X la w i.succ =
    ∑ k, algebraMap (Kp X la N) (Frac0 X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i.succ, k))) * xr X la w k := by
  apply Subtype.ext
  show (Frac0 X la w).val (sfr X la w i.succ) = (Frac0 X la w).val (∑ k, _)
  rw [map_sum]
  simp only [map_mul, AlgHom.commutes]
  show frac X la w 1 (sec X la w i.succ) = ∑ k, algebraMap (Kp X la N) (Lw X la w)
    (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i.succ, k))) * frac X la w 1 (emb X la N (X.inc wL (w k)))
  unfold sec
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, Algebra.smul_def]

end Lw

end Formalism.L2.Pj.GenericSectionMinimum
