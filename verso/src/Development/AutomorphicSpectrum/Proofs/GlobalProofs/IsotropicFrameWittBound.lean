import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.IsoFrameBound

open Formalism.UG (cT)

variable {E : Type} [Field E]

/- English proof (translation)
Establish `hAA : (A.map s).map s = A` using `by ext i j; simp [hs]`. Establish `key : ∀ (B : Matrix (Fin a) (Fin b) E) (v : Fin a → E), v ∈ LinearMap.range B.mulVecLin → (fun i => s (v i)) ∈ LinearMap.range (B.map s).mulVecLin`. Introduce and unpack `B v ⟨w, rfl⟩`. Use `⟨fun i => s (w i), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Matrix.mulVecLin_apply]`. Conclude with `(RingHom.map_mulVec s B w i).symm`. Set `j : LinearMap.range A.mulVecLin ≃+ LinearMap.range (A.map s).mulVecLin` to `{ toFun := fun v => ⟨fun i => s (v.1 i), key A v.1 v.2⟩ invFun := fun v => ⟨fun i => s (v.1 i), by`. Use `key (A.map s) v.1 v.2` as an intermediate fact. Rewrite using `[hAA] at this⟩` and apply the resulting hypothesis.

Use `left_inv := fun v => by ext i; simp [hs]`. Use `right_inv := fun v => by ext i; simp [hs]`. Use the proof step `map_add' := fun v w => by ext i; simp }`. Establish `hb : Function.Bijective s` using `⟨s.injective, fun x => ⟨s x, hs x⟩⟩`. Use `rank_eq_of_equiv_equiv s j hb (fun c v => Subtype.ext (funext fun i => by show s (c * v.1 i) = s c * s (v.1 i)` as an intermediate fact.

Conclude with `map_mul s _ _))`. Use `show Module.finrank E _ = Module.finrank E _`. Conclude with `congrArg Cardinal.toNat this.symm`.
-/
theorem rank_map_of_invol (s : E →+* E) (hs : ∀ x, s (s x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    (A.map s).rank = A.rank := by
  have hAA : (A.map s).map s = A := by ext i j; simp [hs]
  have key : ∀ (B : Matrix (Fin a) (Fin b) E) (v : Fin a → E), v ∈ LinearMap.range B.mulVecLin →
      (fun i => s (v i)) ∈ LinearMap.range (B.map s).mulVecLin := by
    rintro B v ⟨w, rfl⟩
    refine ⟨fun i => s (w i), ?_⟩
    funext i
    simp only [Matrix.mulVecLin_apply]
    exact (RingHom.map_mulVec s B w i).symm
  let j : LinearMap.range A.mulVecLin ≃+ LinearMap.range (A.map s).mulVecLin :=
    { toFun := fun v => ⟨fun i => s (v.1 i), key A v.1 v.2⟩
      invFun := fun v => ⟨fun i => s (v.1 i), by
        have := key (A.map s) v.1 v.2
        rwa [hAA] at this⟩
      left_inv := fun v => by ext i; simp [hs]
      right_inv := fun v => by ext i; simp [hs]
      map_add' := fun v w => by ext i; simp }
  have hb : Function.Bijective s := ⟨s.injective, fun x => ⟨s x, hs x⟩⟩
  have := rank_eq_of_equiv_equiv s j hb (fun c v => Subtype.ext (funext fun i => by
    show s (c * v.1 i) = s c * s (v.1 i)
    exact map_mul s _ _))
  show Module.finrank E _ = Module.finrank E _
  exact congrArg Cardinal.toNat this.symm

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq (s : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `e : (fun i => s (u i)) ᵥ* cT s P = fun i => s ((P *ᵥ u) i)` using `by show _ ᵥ* (P.map s)ᵀ = _`. Rewrite using `[Matrix.vecMul_transpose]`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec s P u i).symm`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (fun i => s (u i)) (cT s P) (J *ᵥ v), e]`.
-/
theorem dot_cT (s : E →+* E) {n k : ℕ} (P : Matrix (Fin n) (Fin k) E) (J : Matrix (Fin n) (Fin n) E)
    (u : Fin k → E) (v : Fin n → E) :
    (fun i => s ((P *ᵥ u) i)) ⬝ᵥ (J *ᵥ v) = (fun i => s (u i)) ⬝ᵥ ((cT s P * J) *ᵥ v) := by
  have e : (fun i => s (u i)) ᵥ* cT s P = fun i => s ((P *ᵥ u) i) := by
    show _ ᵥ* (P.map s)ᵀ = _
    rw [Matrix.vecMul_transpose]
    funext i
    exact (RingHom.map_mulVec s P u i).symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (fun i => s (u i)) (cT s P) (J *ᵥ v), e]

/- English proof (translation)
Take `⟨M, hM⟩ : ∃ M, M = cT s X * J * C` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Q = cT s Y * J * C` from `⟨_, rfl⟩`. Take `⟨M', hM'⟩ : ∃ M', M' = cT s C * J * X` from `⟨_, rfl⟩`. Establish `hXX : cT s (cT s X) = X` using `by ext i j; simp [cT, hs]`. Establish `hMM : M' = cT s M`.

Rewrite using `[hM, hM', Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ, hXX, Matrix.mul_assoc]`. Establish `step : ∀ a, M *ᵥ a = 0 → X *ᵥ (Q *ᵥ a) = C *ᵥ a`. Introduce `a ha`. Take `⟨b, hb⟩ : ∃ b, b = Q *ᵥ a` from `⟨_, rfl⟩`. Take `⟨z, hz⟩ : ∃ z, z = C *ᵥ a - X *ᵥ b` from `⟨_, rfl⟩`.

Establish `hA : (cT s X * J) *ᵥ z = 0`. Rewrite using `[hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ha, xx, Matrix.zero_mulVec, sub_zero]`. Establish `hB : (cT s Y * J) *ᵥ z = 0`. Rewrite using `[hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, yx, Matrix.one_mulVec, ← hQ, hb, sub_self]`. Establish `hh : Formalism.UG.hform s J z z = 0`.

Rewrite using `[hform_eq]`. Establish `e1 : (fun i => s (z i)) = (fun i => s ((C *ᵥ a) i)) - (fun i => s ((X *ᵥ b) i))`. Use function extensionality and compare the values at `i`. Simplify using `[hz]`. Establish `e2 : (cT s C * J) *ᵥ z = - (M' *ᵥ b)`.

Rewrite using `[hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec, zero_sub, hM']`. Establish `e3 : (fun i => s (a i)) ᵥ* cT s M = 0` using `by show _ ᵥ* (M.map s)ᵀ = 0`. Rewrite using `[Matrix.vecMul_transpose]`. Use function extensionality and compare the values at `i`. Use `RingHom.map_mulVec s M a i` as an intermediate fact.

Rewrite `this` using `[ha]`. Conclude with `this.symm.trans (by simp)`. Rewrite using `[e1, sub_dotProduct, dot_cT, dot_cT, hA, dotProduct_zero, sub_zero, e2, dotProduct_neg, neg_eq_zero, hMM, Matrix.dotProduct_mulVec, e3, zero_dotProduct]`. Establish `h0` using `an z hA hB hh`. Rewrite using `[← hb]`.

Rewrite `h0` using `[hz]`. Conclude with `(sub_eq_zero.1 h0).symm`. Establish `hCi : Function.Injective C.mulVec` using `Matrix.mulVec_injective_iff.2 hC`. Set `φ : LinearMap.ker M.mulVecLin →ₗ[E] LinearMap.ker M'.mulVecLin` to `(Q.mulVecLin.comp (LinearMap.ker M.mulVecLin).subtype).codRestrict _ (fun a => by`. Establish `ha : M *ᵥ a.1 = 0` using `a.2`.

Rewrite using `[LinearMap.mem_ker]`. Use `show M' *ᵥ (Q *ᵥ a.1) = 0`. Rewrite using `[hM', ← Matrix.mulVec_mulVec, step a.1 ha, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec])`. Establish `hφ : Function.Injective φ`. Use `(injective_iff_map_eq_zero φ).2 fun a h => ?_` and prove the remaining obligations.

Establish `h1 : Q *ᵥ a.1 = 0` using `congrArg Subtype.val h`. Establish `ha : M *ᵥ a.1 = 0` using `a.2`. Establish `h2` using `step a.1 ha`. Rewrite `h2` using `[h1, Matrix.mulVec_zero]`. Conclude with `Subtype.ext (hCi (h2.symm.trans (Matrix.mulVec_zero C).symm))`.

Establish `h1` using `LinearMap.finrank_le_finrank_of_injective hφ`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker M.mulVecLin`. Establish `h3` using `LinearMap.finrank_range_add_finrank_ker M'.mulVecLin`. Establish `h4 : M'.rank = M.rank`. Rewrite using `[hMM]`.

Simplify using `only [cT]`. Rewrite using `[Matrix.rank_transpose, rank_map_of_invol s hs]`. Simplify using `only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2 h3`. Establish `h5 : Module.finrank E (LinearMap.range M.mulVecLin) = M.rank` using `rfl`. Establish `h6 : Module.finrank E (LinearMap.range M'.mulVecLin) = M'.rank` using `rfl`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_frames (s : E →+* E) (hs : ∀ x, s (s x) = x) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : cT s J = J) (X Y : Matrix (Fin n) (Fin m) E) (C : Matrix (Fin n) (Fin r) E)
    (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (cc : cT s C * J * C = 0)
    (an : ∀ z : Fin n → E, (cT s X * J) *ᵥ z = 0 → (cT s Y * J) *ᵥ z = 0 → Formalism.UG.hform s J z z = 0 → z = 0)
    (hC : LinearIndependent E Cᵀ) : r ≤ m := by
  obtain ⟨M, hM⟩ : ∃ M, M = cT s X * J * C := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cT s Y * J * C := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M', M' = cT s C * J * X := ⟨_, rfl⟩
  have hXX : cT s (cT s X) = X := by ext i j; simp [cT, hs]
  have hMM : M' = cT s M := by
    rw [hM, hM', Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ, hXX, Matrix.mul_assoc]
  have step : ∀ a, M *ᵥ a = 0 → X *ᵥ (Q *ᵥ a) = C *ᵥ a := by
    intro a ha
    obtain ⟨b, hb⟩ : ∃ b, b = Q *ᵥ a := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, z = C *ᵥ a - X *ᵥ b := ⟨_, rfl⟩
    have hA : (cT s X * J) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ha, xx,
        Matrix.zero_mulVec, sub_zero]
    have hB : (cT s Y * J) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, yx, Matrix.one_mulVec, ← hQ, hb,
        sub_self]
    have hh : Formalism.UG.hform s J z z = 0 := by
      rw [hform_eq]
      have e1 : (fun i => s (z i)) = (fun i => s ((C *ᵥ a) i)) - (fun i => s ((X *ᵥ b) i)) := by
        funext i; simp [hz]
      have e2 : (cT s C * J) *ᵥ z = - (M' *ᵥ b) := by
        rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec, zero_sub, hM']
      have e3 : (fun i => s (a i)) ᵥ* cT s M = 0 := by
        show _ ᵥ* (M.map s)ᵀ = 0
        rw [Matrix.vecMul_transpose]
        funext i
        have := RingHom.map_mulVec s M a i
        rw [ha] at this
        exact this.symm.trans (by simp)
      rw [e1, sub_dotProduct, dot_cT, dot_cT, hA, dotProduct_zero, sub_zero, e2, dotProduct_neg, neg_eq_zero,
        hMM, Matrix.dotProduct_mulVec, e3, zero_dotProduct]
    have h0 := an z hA hB hh
    rw [← hb]
    rw [hz] at h0
    exact (sub_eq_zero.1 h0).symm
  have hCi : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  let φ : LinearMap.ker M.mulVecLin →ₗ[E] LinearMap.ker M'.mulVecLin :=
    (Q.mulVecLin.comp (LinearMap.ker M.mulVecLin).subtype).codRestrict _ (fun a => by
      have ha : M *ᵥ a.1 = 0 := a.2
      rw [LinearMap.mem_ker]
      show M' *ᵥ (Q *ᵥ a.1) = 0
      rw [hM', ← Matrix.mulVec_mulVec, step a.1 ha, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec])
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a h => ?_
    have h1 : Q *ᵥ a.1 = 0 := congrArg Subtype.val h
    have ha : M *ᵥ a.1 = 0 := a.2
    have h2 := step a.1 ha
    rw [h1, Matrix.mulVec_zero] at h2
    exact Subtype.ext (hCi (h2.symm.trans (Matrix.mulVec_zero C).symm))
  have h1 := LinearMap.finrank_le_finrank_of_injective hφ
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h3 := LinearMap.finrank_range_add_finrank_ker M'.mulVecLin
  have h4 : M'.rank = M.rank := by
    rw [hMM]
    simp only [cT]
    rw [Matrix.rank_transpose, rank_map_of_invol s hs]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2 h3
  have h5 : Module.finrank E (LinearMap.range M.mulVecLin) = M.rank := rfl
  have h6 : Module.finrank E (LinearMap.range M'.mulVecLin) = M'.rank := rfl
  omega

/- English proof (translation)
Introduce `D V m X Y hW r C hC`. Establish `hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x` using `fun _ => rfl`. Establish `hJ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram`. Use extensionality with `i j`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]`.

Conclude with `V.herm.eq (V.frame j) (V.frame i)`. Conclude with `le_of_frames (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => by simp only [hσ, star_star]) V.gram hJ X Y C hW.xx (GlobalTheory.WittFrame.yx_eq_one D V m X Y hW) hC.2.2 (fun z h1 h2 h3 => hW.aniso z h1 h2 h3) hC.2.1`.
-/
theorem isoFrame_le_wittFrame : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsIsoFrame V C → r ≤ m := by
  intro D V m X Y hW r C hC
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  exact le_of_frames (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => by simp only [hσ, star_star]) V.gram hJ X Y C
    hW.xx (GlobalTheory.WittFrame.yx_eq_one D V m X Y hW) hC.2.2 (fun z h1 h2 h3 => hW.aniso z h1 h2 h3) hC.2.1

end GlobalTheory.CompanionTheory.IsoFrameBound
end
