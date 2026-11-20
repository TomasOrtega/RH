import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.TransportUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {A : Type} [CommRing A]

/- English proof (translation)
Set `e : (Fin n → A) ≃ₗ[A] (Fin m → A)` to `LinearEquiv.ofBijective (Matrix.toLin' x) h`. Establish `hx : x = LinearMap.toMatrix' e.toLinearMap` using `(LinearMap.toMatrix'_toLin' x).symm`. Use `⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, ← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules.

Rewrite using `[hx, ← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules.
-/
theorem exists_inv {m n : ℕ} {x : Matrix (Fin m) (Fin n) A}
    (h : Function.Bijective (x.mulVec : (Fin n → A) → (Fin m → A))) :
    ∃ y : Matrix (Fin n) (Fin m) A, y * x = 1 ∧ x * y = 1 := by
  let e : (Fin n → A) ≃ₗ[A] (Fin m → A) := LinearEquiv.ofBijective (Matrix.toLin' x) h
  have hx : x = LinearMap.toMatrix' e.toLinearMap := (LinearMap.toMatrix'_toLin' x).symm
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp

/- English proof (translation)
Establish `e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b`. Introduce `J a b`. Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]`. Establish `e3 : σ ∘ (k *ᵥ a) = (σ ∘ a) ᵥ* Formalism.UG.cT σ k`. Use function extensionality and compare the values at `i`.

Rewrite using `[Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]`. Rewrite using `[e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`.
-/
theorem hform_mulVec (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (k *ᵥ a) = (σ ∘ a) ᵥ* Formalism.UG.cT σ k := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

/- English proof (translation)
Use `⟨fun h a b => by rw [hform_mulVec, h], fun h => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[hform_mulVec]`. Simplify `this` using `[Formalism.UG.hform, Pi.single_apply, apply_ite σ]`.
-/
theorem unitary_iff (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT σ k * J * k = J ↔ ∀ a b, Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ J a b := by
  refine ⟨fun h a b => by rw [hform_mulVec, h], fun h => ?_⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec] at this
  simpa [Formalism.UG.hform, Pi.single_apply, apply_ite σ] using this

/- English proof (translation)
Establish `h1 : k * (e • β.val) = e • β.val`. Use extensionality with `i j`. Take `⟨c, hc⟩` from `h j`. Establish `: k *ᵥ (e • (β.val *ᵥ Pi.single j 1)) = e • (β.val *ᵥ Pi.single j 1)`. Rewrite using `[hc, mulVec_mulVec, hk]`.

Use `congrFun this i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply]`. Establish `h2` using `congrArg (· * (β⁻¹).val) h1`. Simplify `h2` using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`.
-/
theorem smul_eq_of_fix {m n : ℕ} {e : A} (β : GL (Fin m) A) {B : Matrix (Fin m) (Fin n) A}
    {k : Matrix (Fin m) (Fin m) A} (h : ∀ j, ∃ c, e • (β.val *ᵥ Pi.single j 1) = B *ᵥ c) (hk : k * B = B) :
    e • k = e • (1 : Matrix (Fin m) (Fin m) A) := by
  have h1 : k * (e • β.val) = e • β.val := by
    ext i j
    obtain ⟨c, hc⟩ := h j
    have : k *ᵥ (e • (β.val *ᵥ Pi.single j 1)) = e • (β.val *ᵥ Pi.single j 1) := by
      rw [hc, mulVec_mulVec, hk]
    have := congrFun this i
    simpa [Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply] using this
  have h2 := congrArg (· * (β⁻¹).val) h1
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using h2

/- English proof (translation)
Rewrite using `[← hB, Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.smul_mul, Matrix.one_mul]`.
-/
theorem fix_of_smul_eq {m n : ℕ} {e : A} {B : Matrix (Fin m) (Fin n) A} {k : Matrix (Fin m) (Fin m) A}
    (h : e • k = e • (1 : Matrix (Fin m) (Fin m) A)) (hB : e • B = B) : k * B = B := by
  rw [← hB, Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.smul_mul, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : (e • Formalism.UG.cT σ k) * J = (e • (1 : Matrix (Fin n) (Fin n) A)) * J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Use `_ = _ := by rw [← he, Matrix.mul_smul, hk, he, Matrix.smul_mul, Matrix.one_mul]`. Establish `h2` using `hJ.mul_right_cancel h1`.

Use extensionality with `i j`. Use `congrArg σ (congrFun (congrFun h2 j) i)` as an intermediate fact. Simplify `this` using `[Formalism.UG.cT, hσ, Matrix.one_apply, apply_ite σ, eq_comm]`.
-/
theorem conj_smul_eq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J k : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J)
    (hk : Formalism.UG.cT σ k * J * k = J) {e : A} (he : e • k = e • (1 : Matrix (Fin n) (Fin n) A)) :
    σ e • k = σ e • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : (e • Formalism.UG.cT σ k) * J = (e • (1 : Matrix (Fin n) (Fin n) A)) * J := by
    calc (e • Formalism.UG.cT σ k) * J = Formalism.UG.cT σ k * J * (e • (1 : Matrix (Fin n) (Fin n) A)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = _ := by rw [← he, Matrix.mul_smul, hk, he, Matrix.smul_mul, Matrix.one_mul]
  have h2 := hJ.mul_right_cancel h1
  ext i j
  have := congrArg σ (congrFun (congrFun h2 j) i)
  simpa [Formalism.UG.cT, hσ, Matrix.one_apply, apply_ite σ, eq_comm] using this

/- English proof (translation)
Rewrite using `[Units.ext_iff, ← Matrix.ext_iff]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, sub_eq_zero]`. Simplify using `[Formalism.UG.bc, Matrix.one_apply, apply_ite φ]`.
-/
theorem bc_eq_one_iff {B : Type} [CommRing B] (φ : A →+* B) {n : ℕ} (k : GL (Fin n) A) :
    Formalism.UG.bc φ k = 1 ↔ ∀ i j, φ (k.val i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero]
  simp [Formalism.UG.bc, Matrix.one_apply, apply_ite φ]

end Gen

variable {D : D7}

/- English proof (translation)
Rewrite using `[← Matrix.ext_iff]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, sub_eq_zero, ← idem_mul_eq_iff]`. Both sides reduce to the same expression.
-/
theorem idem_smul_iff (w : Pl D.host.E) {n : ℕ} (k l : Matrix (Fin n) (Fin n) (EAf D)) :
    idem w • k = idem w • l ↔ ∀ i j, GlobalTheory.StdFrames.cpt w (k i j - l i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero, ← idem_mul_eq_iff]
  rfl

/- English proof (translation)
Rewrite using `[idem_smul_iff, idem_smul_iff]`. Use `(bc_eq_one_iff _ k).trans ?_` and prove the remaining obligations. Establish `h` using `fun z => GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (GlobalTheory.StdFrames.toAd_spec D) (w.under (𝓞 D.host.F)) z`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Conclude with `⟨fun i j => (h _).1 (H i j) w rfl, fun i j => (h _).1 (H i j) _ (GlobalTheory.IdemSupport.under_cP w)⟩`. Introduce and unpack `⟨H1, H2⟩ i j`. Use `(h _).2 fun P hP => ?_` and prove the remaining obligations. Break down `GlobalTheory.IdemSupport.eq_or_eq_cP hP with rfl | rfl` into its components or cases. Conclude with `H1 i j`.

Conclude with `H2 i j`.
-/
theorem bc_prV_eq_one_iff (w : Pl D.host.E) {n : ℕ} (k : GL (Fin n) (EAf D)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) (w.under (𝓞 D.host.F))) k = 1 ↔
      idem w • k.val = idem w • (1 : Matrix (Fin n) (Fin n) (EAf D)) ∧
      idem (GlobalTheory.IdemSupport.cP w) • k.val = idem (GlobalTheory.IdemSupport.cP w) • (1 : Matrix (Fin n) (Fin n) (EAf D)) := by
  rw [idem_smul_iff, idem_smul_iff]
  refine (bc_eq_one_iff _ k).trans ?_
  have h := fun z => GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (GlobalTheory.StdFrames.toAd_spec D) (w.under (𝓞 D.host.F)) z
  constructor
  · intro H
    exact ⟨fun i j => (h _).1 (H i j) w rfl, fun i j => (h _).1 (H i j) _ (GlobalTheory.IdemSupport.under_cP w)⟩
  · rintro ⟨H1, H2⟩ i j
    refine (h _).2 fun P hP => ?_
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hP with rfl | rfl
    · exact H1 i j
    · exact H2 i j

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_level_iff (W : HSp D) (L : Lat W) (k : GL (Fin W.rank) (EAf D)) :
    k ∈ Formalism.UG.levelAfL D.sp.cm.sig W.gram L ↔
      Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) ∧
        ∀ a, a ∈ hat L ↔ k.val *ᵥ a ∈ hat L := Iff.rfl

/- English proof (translation)
Rewrite using `[mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem col_mem_gen {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (β : GL (Fin n) A) (j i : Fin n) :
    ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) i ∈ S := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Take `⟨-, e, he, -, hc⟩` from `hB`. Take `rfl` from `eq_idem he`. Take `⟨β, rfl⟩` from `exists_eq_lat hL`. Use `smul_eq_of_fix β (fun j => ?_) h1` and prove the remaining obligations. Establish `h` using `(mem_hat_lat β _).2 (col_mem_gen (OA D) β j)`.

Take `⟨c, hc'⟩` from `(hc _).1 ⟨smul_mem_hat (idem_mem w) h, by rw [smul_smul, idem_mul_self]⟩`. Conclude with `⟨_, hc'⟩`.
-/
theorem idem_smul_eq_of_fix {W : HSp D} {L : Lat W} (hL : Submodule.IsLattice D.host.E L) {w : Pl D.host.E} {n : ℕ}
    {B : Matrix (Fin W.rank) (Fin n) (EAf D)} (hB : IsBasisAt W w L B) {k : Matrix (Fin W.rank) (Fin W.rank) (EAf D)}
    (h1 : HMul.hMul k B = B) : idem w • k = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  obtain ⟨-, e, he, -, hc⟩ := hB
  obtain rfl := eq_idem he
  obtain ⟨β, rfl⟩ := exists_eq_lat hL
  refine smul_eq_of_fix β (fun j => ?_) h1
  have h := (mem_hat_lat β _).2 (col_mem_gen (OA D) β j)
  obtain ⟨c, hc'⟩ := (hc _).1 ⟨smul_mem_hat (idem_mem w) h, by rw [smul_smul, idem_mul_self]⟩
  exact ⟨_, hc'⟩

/- English proof (translation)
Introduce `D W Y L Λ S _ n be be' hL hbe x hx x'`. Take `⟨⟨hb, hf⟩, hl, hs⟩` from `hx`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hb', hf'⟩, hl', hs'⟩`. Take `⟨y, y1, y2⟩` from `exists_inv hb`.

Take `⟨y', y1', y2'⟩` from `exists_inv hb'`. Set `k : GL (Fin W.rank) (EAf D)` to `⟨HMul.hMul y x', HMul.hMul y' x, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x', y2', Matrix.one_mul, y1], by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x, y2, Matrix.one_mul, y1']⟩`. Establish `hk : HMul.hMul x k.val = x'`. Express the relevant statement in the definitionally equal form `HMul.hMul x (HMul.hMul y x') = x'`. Rewrite using `[← Matrix.mul_assoc, y2, Matrix.one_mul]`.

Establish `hkv : ∀ a, x *ᵥ (k.val *ᵥ a) = x' *ᵥ a` using `fun a => by rw [mulVec_mulVec, hk]`. Establish `hU : Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D)` using `(unitary_iff _ _ _).2 fun a b => by`. Rewrite using `[← hA_eq, ← hA_eq, ← hf, hkv, hkv, hf']`. Use `⟨k, ⟨(mem_level_iff W L k).2 ⟨hU, fun a => ?_⟩, fun w hw => ?_⟩, hk.symm⟩` and prove the remaining obligations. Rewrite using `[hl (k.val *ᵥ a), hkv, hl']`.

Establish `h1 : HMul.hMul k.val (be w) = be w`. Express the relevant statement in the definitionally equal form `HMul.hMul (HMul.hMul y x') (be w) = be w`. Rewrite using `[Matrix.mul_assoc, hs' w hw, ← hs w hw, ← Matrix.mul_assoc, y1, Matrix.one_mul]`. Establish `h2 : idem w • k.val = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D))` using `idem_smul_eq_of_fix hL (hbe w hw) h1`. Use `(bc_prV_eq_one_iff w k).2 ⟨h2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cjA_idem]`. Conclude with `conj_smul_eq (cjA D) cjA_cjA (GlobalTheory.StdFrames.isUnit_gram W) hU h2`. Introduce and unpack `⟨k, ⟨hk, hk1⟩, rfl⟩`. Take `⟨hU, hst⟩` from `(mem_level_iff W L k).1 hk`. Use `⟨⟨?_, fun a b => ?_⟩, fun a => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `: (HMul.hMul x k.val : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)).mulVec = x.mulVec ∘ k.val.mulVec` using `funext fun a => (mulVec_mulVec _ _ _).symm`. Rewrite using `[this]`. Use `hb.comp (Function.bijective_iff_has_inverse.2 ⟨(k⁻¹).val.mulVec, fun a => ?_, fun a => ?_⟩)` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, Units.inv_mul, one_mulVec]`. Rewrite using `[mulVec_mulVec, Units.mul_inv, one_mulVec]`.

Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, hf, hA_eq, hA_eq]`. Conclude with `(unitary_iff _ _ _).1 hU b a`. Rewrite using `[← mulVec_mulVec, ← hl, ← hst]`. Take `⟨-, e, he, hB, -⟩` from `hbe w hw`. Take `rfl` from `eq_idem he`.

Establish `h2` using `((bc_prV_eq_one_iff w k).1 (hk1 w hw)).1`. Establish `h3 : HMul.hMul k.val (be w) = be w` using `fix_of_smul_eq h2 hB`. Rewrite using `[Matrix.mul_assoc, h3, hs w hw]`.
-/
theorem transport_unique : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S _ n be be' hL hbe x hx x'
  obtain ⟨⟨hb, hf⟩, hl, hs⟩ := hx
  constructor
  · rintro ⟨⟨hb', hf'⟩, hl', hs'⟩
    obtain ⟨y, y1, y2⟩ := exists_inv hb
    obtain ⟨y', y1', y2'⟩ := exists_inv hb'
    let k : GL (Fin W.rank) (EAf D) := ⟨HMul.hMul y x', HMul.hMul y' x,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x', y2', Matrix.one_mul, y1],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x, y2, Matrix.one_mul, y1']⟩
    have hk : HMul.hMul x k.val = x' := by
      change HMul.hMul x (HMul.hMul y x') = x'
      rw [← Matrix.mul_assoc, y2, Matrix.one_mul]
    have hkv : ∀ a, x *ᵥ (k.val *ᵥ a) = x' *ᵥ a := fun a => by rw [mulVec_mulVec, hk]
    have hU : Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) :=
      (unitary_iff _ _ _).2 fun a b => by
        rw [← hA_eq, ← hA_eq, ← hf, hkv, hkv, hf']
    refine ⟨k, ⟨(mem_level_iff W L k).2 ⟨hU, fun a => ?_⟩, fun w hw => ?_⟩, hk.symm⟩
    · rw [hl (k.val *ᵥ a), hkv, hl']
    · have h1 : HMul.hMul k.val (be w) = be w := by
        change HMul.hMul (HMul.hMul y x') (be w) = be w
        rw [Matrix.mul_assoc, hs' w hw, ← hs w hw, ← Matrix.mul_assoc, y1, Matrix.one_mul]
      have h2 : idem w • k.val = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) :=
        idem_smul_eq_of_fix hL (hbe w hw) h1
      refine (bc_prV_eq_one_iff w k).2 ⟨h2, ?_⟩
      rw [← cjA_idem]
      exact conj_smul_eq (cjA D) cjA_cjA (GlobalTheory.StdFrames.isUnit_gram W) hU h2
  · rintro ⟨k, ⟨hk, hk1⟩, rfl⟩
    obtain ⟨hU, hst⟩ := (mem_level_iff W L k).1 hk
    refine ⟨⟨?_, fun a b => ?_⟩, fun a => ?_, fun w hw => ?_⟩
    · have : (HMul.hMul x k.val : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)).mulVec = x.mulVec ∘ k.val.mulVec := funext fun a => (mulVec_mulVec _ _ _).symm
      rw [this]
      refine hb.comp (Function.bijective_iff_has_inverse.2 ⟨(k⁻¹).val.mulVec, fun a => ?_, fun a => ?_⟩)
      · rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, hf, hA_eq, hA_eq]
      exact (unitary_iff _ _ _).1 hU b a
    · rw [← mulVec_mulVec, ← hl, ← hst]
    · obtain ⟨-, e, he, hB, -⟩ := hbe w hw
      obtain rfl := eq_idem he
      have h2 := ((bc_prV_eq_one_iff w k).1 (hk1 w hw)).1
      have h3 : HMul.hMul k.val (be w) = be w := fix_of_smul_eq h2 hB
      rw [Matrix.mul_assoc, h3, hs w hw]

end GlobalTheory.TransportUnique

end
