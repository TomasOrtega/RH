import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Stab

open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

/- English proof (translation)
The claim follows from `isInt_iff.2 (show ∑ k, M i k * x k ∈ _ from sum_mem fun k _ => mul_mem (isInt_iff.1 (hM i k)) (isInt_iff.1 (hx k)))`.
-/
theorem isInt_mulVec {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((M *ᵥ x) i) :=
  isInt_iff.2 (show ∑ k, M i k * x k ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hM i k)) (isInt_iff.1 (hx k)))

/- English proof (translation)
The claim follows from `isInt_iff.2 (show ∑ k, x k * M k i ∈ _ from sum_mem fun k _ => mul_mem (isInt_iff.1 (hx k)) (isInt_iff.1 (hM k i)))`.
-/
theorem isInt_vecMul {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((x ᵥ* M) i) :=
  isInt_iff.2 (show ∑ k, x k * M k i ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hx k)) (isInt_iff.1 (hM k i)))

/- English proof (translation)
The claim follows from `funext fun i => RingHom.map_mulVec f M y i`.
-/
theorem map_mulVec' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (y : Fin n → R) : (fun i => f ((M *ᵥ y) i)) = M.map f *ᵥ fun i => f (y i) :=
  funext fun i => RingHom.map_mulVec f M y i

/- English proof (translation)
Establish `hG : G.map π * N.map π = (M.map (π.comp c))ᵀ * G.map π`. Rewrite using `[← Matrix.map_mul, h, Matrix.map_mul]`. Both sides reduce to the same expression. Establish `hc` using `map_mulVec' (π.comp c) M y`. Simplify using `only [RingHom.comp_apply] at hc`.

Rewrite using `[Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hG, Matrix.mul_assoc, ← Matrix.vecMul_mulVec, hc]`.
-/
theorem dual_move {R K : Type} [CommRing R] [Field K] (c : R →+* R) (π : R →+* K) {n : ℕ}
    (G M N : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) K) (h : G * N = (M.map c)ᵀ * G) (y : Fin n → R) :
    (fun i => π (c ((M *ᵥ y) i))) ᵥ* (G.map π * β.1) =
      ((fun i => π (c (y i))) ᵥ* (G.map π * β.1)) ᵥ* ((β⁻¹).1 * N.map π * β.1) := by
  have hG : G.map π * N.map π = (M.map (π.comp c))ᵀ * G.map π := by
    rw [← Matrix.map_mul, h, Matrix.map_mul]
    rfl
  have hc := map_mulVec' (π.comp c) M y
  simp only [RingHom.comp_apply] at hc
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ β.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hG, Matrix.mul_assoc,
    ← Matrix.vecMul_mulVec, hc]

/- English proof (translation)
Establish `h1 : (a + b) • (M - 1) = M - 1` using `Matrix.ext fun i j => h i j`. Establish `h3 : (a + b) • (M *ᵥ y - y) = M *ᵥ y - y`. Use `congrArg (· *ᵥ y) h1` as an intermediate fact. Simplify `this` using `only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Rewrite using `[← map_mulVec']`.

Use function extensionality and compare the values at `i`. Establish `h4 : (a + b) * ((M *ᵥ y) i - y i) = (M *ᵥ y) i - y i` using `congrFun h3 i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, ← map_add, ← map_sub]`. Use `congr 1`. Take the linear combination `-h4`.
-/
theorem split_move {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (a b : R)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, (a + b) * (M - 1) i j = (M - 1) i j) (y : Fin n → R) :
    (M.map f *ᵥ fun i => f (y i)) = ((fun i => f (a * (M *ᵥ y) i)) + fun i => f (b * (M *ᵥ y) i)) +
      (((fun i => f (y i)) - fun i => f (a * y i)) - fun i => f (b * y i)) := by
  have h1 : (a + b) • (M - 1) = M - 1 := Matrix.ext fun i j => h i j
  have h3 : (a + b) • (M *ᵥ y - y) = M *ᵥ y - y := by
    have := congrArg (· *ᵥ y) h1
    simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
  rw [← map_mulVec']
  funext i
  have h4 : (a + b) * ((M *ᵥ y) i - y i) = (M *ᵥ y) i - y i := congrFun h3 i
  simp only [Pi.add_apply, Pi.sub_apply, ← map_add, ← map_sub]
  congr 1
  linear_combination -h4

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, RingHom.map_zero _⟩`. Consider the case `tmul α x => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, RingHom.map_add _ _ _⟩`.
-/
theorem finPart_surj (z : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ a : AE D, finPart D a = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul α x => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

/- English proof (translation)
Establish `h` using `GlobalTheory.SplitHeckeLabel.smul_mem_latHat (GlobalTheory.PlaceModel.latFrame V) (x := finPart D a) (y := fun i => finPart D (y i)) (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hy)`. Rewrite `h` using `[GlobalTheory.PlaceModel.coe_latFrame]`. Establish `e : (fun i => finPart D (a * y i)) = finPart D a • fun i => finPart D (y i)`. Use function extensionality and compare the values at `fun i => RingHom.map_mul _ _ _`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem idem_mul_mem (V : HSp D) {a : AE D} (ha : a * a = a) {y : Fin V.rank → AE D}
    (hy : (fun i => finPart D (y i)) ∈ LamHat V) : (fun i => finPart D (a * y i)) ∈ LamHat V := by
  have h := GlobalTheory.SplitHeckeLabel.smul_mem_latHat (GlobalTheory.PlaceModel.latFrame V) (x := finPart D a)
    (y := fun i => finPart D (y i))
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
    (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hy)
  rw [GlobalTheory.PlaceModel.coe_latFrame] at h
  have e : (fun i => finPart D (a * y i)) = finPart D a • fun i => finPart D (y i) :=
    funext fun i => RingHom.map_mul _ _ _
  rw [e]
  exact h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

/- English proof (translation)
Establish `h : (e + cA D e) • (mt V g - 1) = mt V g - 1` using `Matrix.ext fun i j => hg i j`. Establish `h1 : mt V g⁻¹ - 1 = -((mt V g - 1) * mt V g⁻¹)`. Rewrite using `[Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]`. Establish `h2 : (e + cA D e) • (mt V g⁻¹ - 1) = mt V g⁻¹ - 1`. Rewrite using `[h1, smul_neg, ← Matrix.smul_mul, h]`.

Conclude with `fun i j => congrFun (congrFun h2 i) j`.
-/
theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h1 : mt V g⁻¹ - 1 = -((mt V g - 1) * mt V g⁻¹) := by
    rw [Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  have h2 : (e + cA D e) • (mt V g⁻¹ - 1) = mt V g⁻¹ - 1 := by
    rw [h1, smul_neg, ← Matrix.smul_mul, h]
  exact fun i j => congrFun (congrFun h2 i) j

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `h : infPart D ((mt V g - 1) i j) = 0`. Rewrite using `[← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he, GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]`. Rewrite `h` using `[Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]`. Use `show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j`.

Rewrite using `[h, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`. Rewrite using `[RingHom.map_one]`. Rewrite using `[RingHom.map_zero]`.
-/
theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {V : HSp D}
  {β : GL (Fin V.rank) (Fv D.host.F v)}

/- English proof (translation)
Introduce `i j`. Use `choose y hy using fun k => hπ.1 (β.1 k j)`. Establish `hcol : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1`. Use function extensionality and compare the values at `k`. Rewrite using `[hy, Matrix.mulVec_single_one]`.

Both sides reduce to the same expression. Establish `h1` using `(hβ y).2 fun k => by`. Rewrite using `[hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mulVec_single_one]`. Conclude with `intM_one k j`. Establish `h2` using `h _ h1`.

Rewrite `h2` using `[finMat_eq, ← map_mulVec']`. Establish `h3 : mt V g *ᵥ (fun k => e * y k) = fun k => e * (mt V g *ᵥ y) k` using `Matrix.mulVec_smul _ e y`. Rewrite `h2` using `[h3]`. Establish `h4` using `(hβ _).1 h2 i`. Rewrite `h4` using `[map_mulVec', hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`.

Rewrite using `[rho_val]`. Conclude with `h4`.
-/
theorem intM_of_stable (hπ : Chart e v π) (hβ : Frame V e π β) {g : GA D V}
    (h : ∀ y ∈ LamHat V, finMat D.sp.cm.sig V.gram g *ᵥ y ∈ LamHat V) : IntM (Ov D v) (rho V π β g).1 := by
  intro i j
  choose y hy using fun k => hπ.1 (β.1 k j)
  have hcol : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, Matrix.mulVec_single_one]
    rfl
  have h1 := (hβ y).2 fun k => by
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mulVec_single_one]
    exact intM_one k j
  have h2 := h _ h1
  rw [finMat_eq, ← map_mulVec'] at h2
  have h3 : mt V g *ᵥ (fun k => e * y k) = fun k => e * (mt V g *ᵥ y) k := Matrix.mulVec_smul _ e y
  rw [h3] at h2
  have h4 := (hβ _).1 h2 i
  rw [map_mulVec', hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h4
  rw [rho_val]
  exact h4

/- English proof (translation)
Use `choose y hy using fun k => finPart_surj (z k)`. Take `rfl : z = fun k => finPart D (y k)` from `funext fun k => (hy k).symm`. Establish `he'` using `GlobalTheory.SplitScalar.isSplitIdem_conj he`. Establish `a1` using `idem_mul_mem V he.1 hz`. Establish `a2` using `idem_mul_mem V he'.1 hz`.

Establish `b1 : (fun i => finPart D (e * (mt V g *ᵥ y) i)) ∈ LamHat V`. Use `(hβ _).2 fun i => ?_` and prove the remaining obligations. Use `isInt_mulVec h1 ((hβ y).1 a1) i` as an intermediate fact. Rewrite `this` using `[rho_val, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, ← Matrix.mulVec_mulVec, ← map_mulVec']`. Then use the resulting hypothesis. Establish `b2 : (fun i => finPart D (cA D e * (mt V g *ᵥ y) i)) ∈ LamHat V`.

Use `(hd _).2 fun i => ?_` and prove the remaining obligations. Use `isInt_vecMul h2 ((hd y).1 a2) i` as an intermediate fact. Rewrite `this` using `[rho_val]`. Conclude with `(congrFun (dual_move (cA D) π (V.gram.map (incA D)) _ _ β (gram_mul_inv V g) y) i).symm ▸ this`. Rewrite using `[finMat_eq, split_move (finPart D) e (cA D e) (mt V g) hg y]`.

Conclude with `add_mem (add_mem b1 b2) (sub_mem (sub_mem hz a1) a2)`.
-/
theorem stable_of_intM (he : IsSplitIdem D e) (hβ : Frame V e π β)
    (hd : ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j))
    {g : GA D V} (hg : SuppAt e V g) (h1 : IntM (Ov D v) (rho V π β g).1) (h2 : IntM (Ov D v) (rho V π β g⁻¹).1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ LamHat V) :
    finMat D.sp.cm.sig V.gram g *ᵥ z ∈ LamHat V := by
  choose y hy using fun k => finPart_surj (z k)
  obtain rfl : z = fun k => finPart D (y k) := funext fun k => (hy k).symm
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have a1 := idem_mul_mem V he.1 hz
  have a2 := idem_mul_mem V he'.1 hz
  have b1 : (fun i => finPart D (e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hβ _).2 fun i => ?_
    have := isInt_mulVec h1 ((hβ y).1 a1) i
    rwa [rho_val, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← map_mulVec'] at this
  have b2 : (fun i => finPart D (cA D e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hd _).2 fun i => ?_
    have := isInt_vecMul h2 ((hd y).1 a2) i
    rw [rho_val] at this
    exact (congrFun (dual_move (cA D) π (V.gram.map (incA D)) _ _ β (gram_mul_inv V g) y) i).symm ▸ this
  rw [finMat_eq, split_move (finPart D) e (cA D e) (mt V g) hg y]
  exact add_mem (add_mem b1 b2) (sub_mem (sub_mem hz a1) a2)

/- English proof (translation)
Rewrite using `[finMat_eq, finMat_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mulVec]`.
-/
theorem finMat_mul_inv (g : GA D V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig V.gram g *ᵥ (finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y) = y := by
  rw [finMat_eq, finMat_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mulVec]

/- English proof (translation)
Introduce `D e v π he hπ V β hβ g hg`. Establish `hd` using `GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace e v π he hπ V β hβ`. Unfold `GInt`. Rewrite using `[← map_inv]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h, -⟩`. Conclude with `⟨intM_of_stable hπ hβ fun y hy => (h y).1 hy, intM_of_stable hπ hβ fun y hy => (h _).2 (by rw [finMat_mul_inv]; exact hy)⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨mem_GfC he hg, fun y => ⟨stable_of_intM he hβ hd hg h1 h2 y, fun hy => ?_⟩, fun w hw => absurd hw (Finset.notMem_empty w)⟩` and prove the remaining obligations. Establish `h3` using `stable_of_intM he hβ hd (suppAt_inv hg) h2 (by rw [inv_inv]; exact h1) _ hy`.

Establish `h4` using `finMat_mul_inv g⁻¹ y`. Rewrite `h4` using `[inv_inv]`. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis.
-/
theorem mem_KsphC_iff_gInt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  intro D e v π he hπ V β hβ g hg
  have hd := GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace e v π he hπ V β hβ
  unfold GInt
  rw [← map_inv]
  constructor
  · rintro ⟨-, h, -⟩
    exact ⟨intM_of_stable hπ hβ fun y hy => (h y).1 hy,
      intM_of_stable hπ hβ fun y hy => (h _).2 (by rw [finMat_mul_inv]; exact hy)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mem_GfC he hg, fun y => ⟨stable_of_intM he hβ hd hg h1 h2 y, fun hy => ?_⟩,
      fun w hw => absurd hw (Finset.notMem_empty w)⟩
    have h3 := stable_of_intM he hβ hd (suppAt_inv hg) h2 (by rw [inv_inv]; exact h1) _ hy
    have h4 := finMat_mul_inv g⁻¹ y
    rw [inv_inv] at h4
    rwa [h4] at h3

end GlobalTheory.SplitHecke.Stab

end
