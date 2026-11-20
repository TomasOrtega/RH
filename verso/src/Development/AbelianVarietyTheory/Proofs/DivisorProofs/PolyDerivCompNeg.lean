import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Parity

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.I2.polyDeriv`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : Multiset.card (Finsupp.toMultiset m) = d`. Rewrite using `[Finsupp.card_toMultiset, ← hP (MvPolynomial.mem_support_iff.1 hm), Finsupp.weight_apply]`.

Simplify using `only [Pi.one_apply, smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Establish `h` using `(ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W).iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (x := 0) (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))`. Rewrite `h` using `[Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ]`. Establish `e : (fun z => F (-z)) = F ∘ (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W)` using `rfl`.

Rewrite using `[e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]`. Establish `e2 : ∀ t : W, ((ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) : W →L[ℂ] W) t = (-1 : ℂ) • t` using `fun t => by simp`. Simplify using `only [e2]`. Rewrite using `[ContinuousMultilinearMap.map_smul_univ]`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.

Rewrite using `[← hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polyDeriv_comp_neg {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (P : MvPolynomial σ ℂ) (d : ℕ)
    (hP : P.IsHomogeneous d) (u : σ → W) (F : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => F (-z)) 0 = (-1) ^ d * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    rw [Finsupp.card_toMultiset, ← hP (MvPolynomial.mem_support_iff.1 hm), Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have h := (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W).iteratedFDerivWithin_comp_right F uniqueDiffOn_univ
    (x := 0) (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have e : (fun z => F (-z)) = F ∘ (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  have e2 : ∀ t : W, ((ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) : W →L[ℂ] W) t = (-1 : ℂ) • t := fun t => by simp
  simp only [e2]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hd]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

def reflTF (n g : ℕ) : TF n g ≃+ TF n g where
  toFun φ := fun x => φ (-x)
  invFun φ := fun x => φ (-x)
  left_inv φ := by funext x; simp
  right_inv φ := by funext x; simp
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reflTF_smul (a : ℂ) (φ : TF n g) : reflTF n g (a • φ) = a • reflTF n g φ := rfl

/- English proof (translation)
Take `⟨R, hR, h1, h2⟩` from `h`. Use `⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Use `(h1 (-x) hx k i).neg` as an intermediate fact. Simplify using `using this`. Use `h2 (-x) (-y) fun k i => (hy k i).neg` as an intermediate fact.

Express the relevant statement in the definitionally equal form `φ _ = φ _`. Rewrite using `[← this, neg_add, smul_neg]`.
-/
theorem isSB_reflTF {φ : TF n g} (h : GlobalTheory.SW.IsSB φ) : GlobalTheory.SW.IsSB (reflTF n g φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h1 (-x) hx k i).neg
    simpa using this
  · have := h2 (-x) (-y) fun k i => (hy k i).neg
    change φ _ = φ _
    rw [← this, neg_add, smul_neg]

/- English proof (translation)
Unfold `thA thS`. Use `congr 1`. Simplify using `only [Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]`. Rewrite using `[← (Equiv.neg (Matrix (Fin n) (Fin g) ℚ)).tsum_eq]`. Use `tsum_congr fun y => ?_` and prove the remaining obligations.

Establish `e : ∀ k, qv ((-y) k) = -qv (y k)` using `fun k => by`. Use function extensionality and compare the values at `i`. Simplify using `[qv]`. Establish `e' : reflTF n g φ (-y) = φ y`. Express the relevant statement in the definitionally equal form `φ (- -y) = φ y`.

Rewrite using `[neg_neg]`. Simplify using `only [Equiv.neg_apply, e, e', Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]`.
-/
theorem thA_reflTF (φ : TF n g) (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (reflTF n g φ) x z = thA X bas idx φ x (-z) := by
  unfold thA thS
  congr 1
  · simp only [Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  · rw [← (Equiv.neg (Matrix (Fin n) (Fin g) ℚ)).tsum_eq]
    refine tsum_congr fun y => ?_
    have e : ∀ k, qv ((-y) k) = -qv (y k) := fun k => by
      funext i
      simp [qv]
    have e' : reflTF n g φ (-y) = φ y := by
      change φ (- -y) = φ y
      rw [neg_neg]
    simp only [Equiv.neg_apply, e, e', Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/- English proof (translation)
Establish `e : ∀ k, crd X bas ((-y) k) = -crd X bas (y k)` using `fun k => by`. Use `crd_smul hs (-1) (y k)` as an intermediate fact. Rewrite `this` using `[neg_one_smul, neg_one_smul]`. Conclude with `this`. Use function extensionality and compare the values at `x`.

Express the relevant statement in the definitionally equal form `heisS _ _ φ (-x) = φ _ * _`. Unfold `heisS`. Use `congr 2`. Use extensionality with `k i`. Simplify using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Use `congr 2`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[e, dotProduct]`.
-/
theorem reflTF_heisG (hs : IsSympl X bas) (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) :
    reflTF n g (heisG X bas y φ) = heisG X bas (-y) (reflTF n g φ) := by
  have e : ∀ k, crd X bas ((-y) k) = -crd X bas (y k) := fun k => by
    have := crd_smul hs (-1) (y k)
    rw [neg_one_smul, neg_one_smul] at this
    exact this
  funext x
  change heisS _ _ φ (-x) = φ _ * _
  unfold heisS
  congr 2
  · ext k i
    simp [e]
    ring
  · congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [e, dotProduct]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `EFBil X _ _ = EFBil X _ _`. Simplify using the standard rewrite rules.
-/
theorem EF_neg_smul_neg (w : E) (u : Fin r → E) : EF X (-u) (w • -u) = EF X u (w • u) := by
  change EFBil X _ _ = EFBil X _ _
  simp

/- English proof (translation)
Establish `e : ∀ k, (-y) k = -(y k)` using `fun _ => rfl`. Simplify using `only [epsW, e, EF_neg_smul_neg]`.
-/
theorem epsW_neg (w : E) (y : Matrix (Fin n) (Fin r) E) : epsW X w (-y) = epsW X w y := by
  have e : ∀ k, (-y) k = -(y k) := fun _ => rfl
  simp only [epsW, e, EF_neg_smul_neg]

/- English proof (translation)
Unfold `projA`. Rewrite using `[reflTF_smul]`. Use `congr 1`. Establish `hm : Set.MapsTo (reflTF n g) ((fun y => epsW X w y • heisG X bas y φ) '' A) ((fun y => epsW X w y • heisG X bas y φ) '' A)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `⟨-y, A.neg_mem hy, by simp only [reflTF_smul, reflTF_heisG hs, hφ, epsW_neg]⟩`. Establish `hi : ∀ ψ, reflTF n g (reflTF n g ψ) = ψ` using `(reflTF n g).left_inv`. Rewrite using `[AddEquiv.map_finsum]`. Simplify using `only [AddEquiv.map_finsum]`. Conclude with `finsum_mem_eq_of_bijOn (reflTF n g) ⟨hm, (reflTF n g).injective.injOn, fun ψ hψ => ⟨_, hm hψ, hi ψ⟩⟩ fun _ _ => rfl`.
-/
theorem reflTF_projA (hs : IsSympl X bas) (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) {φ : TF n g}
    (hφ : reflTF n g φ = φ) : reflTF n g (projA X bas w A φ) = projA X bas w A φ := by
  unfold projA
  rw [reflTF_smul]
  congr 1
  have hm : Set.MapsTo (reflTF n g) ((fun y => epsW X w y • heisG X bas y φ) '' A)
      ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, A.neg_mem hy, by simp only [reflTF_smul, reflTF_heisG hs, hφ, epsW_neg]⟩
  have hi : ∀ ψ, reflTF n g (reflTF n g ψ) = ψ := (reflTF n g).left_inv
  rw [AddEquiv.map_finsum]
  simp only [AddEquiv.map_finsum]
  exact finsum_mem_eq_of_bijOn (reflTF n g)
    ⟨hm, (reflTF n g).injective.injOn, fun ψ hψ => ⟨_, hm hψ, hi ψ⟩⟩ fun _ _ => rfl

/- English proof (translation)
Use `⟨h.1.comp differentiable_id.neg, fun v hv => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Use `congrFun (h.2 (-v) (L.neg_mem hv)) (-z)` as an intermediate fact. Establish `e : pv X idx x (-v) = -pv X idx x v`. Unfold `pv`.

Rewrite using `[per_neg]`. Both sides reduce to the same expression. Simplify using `only [Pi.smul_apply, fock, eps1, EF_neg_smul_neg, e] at this ⊢`. Rewrite using `[← this, smul_neg, ← neg_add, ← neg_add]`. Simplify using `only [hx, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]`.
-/
theorem isTheta1_neg {w : E} {x : Frame X.Ψ r} {L : Lt E r} {θ : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L θ) : IsTheta1 X bas idx w x L fun z => θ (-z) := by
  refine ⟨h.1.comp differentiable_id.neg, fun v hv => ?_⟩
  funext z
  have := congrFun (h.2 (-v) (L.neg_mem hv)) (-z)
  have e : pv X idx x (-v) = -pv X idx x v := by
    unfold pv
    rw [per_neg]
    rfl
  simp only [Pi.smul_apply, fock, eps1, EF_neg_smul_neg, e] at this ⊢
  rw [← this, smul_neg, ← neg_add, ← neg_add]
  simp only [hx, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1`. Use `⟨h2.comp (differentiable_pi.2 fun k => ?_), fun u hu => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = b`. Substitute `hk` using the available equality. Simplify using `only [Function.update_self]`.

Conclude with `differentiable_id`. Simplify using `only [Function.update_of_ne hk]`. Conclude with `differentiable_const _`. Use function extensionality and compare the values at `t set y : Matrix (Fin n) (Fin r) E := Pi.single b u with hy`. Establish `hyb : y b = u` using `Pi.single_eq_same _ _`.

Establish `hyk : ∀ k, k ≠ b → y k = 0` using `fun k hk => Pi.single_eq_of_ne hk _`. Establish `hm : y ∈ tens (stdL E n) L` using `(TensLat.mem_tens_stdL L _).2 fun k => by`. Distinguish the cases in `hk : k = b`. Rewrite using `[hk, hyb]`. Conclude with `hu`.

Rewrite using `[hyk k hk]`. Conclude with `L.zero_mem`. Establish `hp : pv X idx x 0 = 0`. Unfold `pv`. Rewrite using `[per_zero]`.

Both sides reduce to the same expression. Establish `e1 : epsW X w y = eps1 X w u`. Unfold `epsW eps1`. Rewrite using `[Finset.sum_eq_single b, hyb]`. Introduce `k _ hk`.

Rewrite using `[hyk k hk]`. Express the relevant statement in the definitionally equal form `EFBil X _ _ = 0`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `e2` using `(h1 y (Function.update z₀ b t)).2`.

Rewrite `e2` using `[Finset.sum_eq_single b, hyb, Function.update_self]`. Establish `e3 : (fun k => Function.update z₀ b t k + pv X idx x (y k)) = Function.update z₀ b (t + pv X idx x u)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = b`. Rewrite using `[hk, hyb, Function.update_self, Function.update_self]`.

Rewrite using `[hyk k hk, hp, add_zero, Function.update_of_ne hk, Function.update_of_ne hk]`. Rewrite `e2` using `[e3]`. Use `conv_rhs => rw [← hv.2.2 y hm, GlobalTheory.SW.UnAct.thA_smul]`. Simplify using `only [Pi.smul_apply, fock, e1, e2, Nat.cast_one, _root_.one_mul]`. Introduce `k _ hk`.

Rewrite using `[hyk k hk, hp]`. Simplify using `[hx]`. Simplify using the standard rewrite rules.
-/
theorem isTheta1_update (hs : IsSympl X bas) (hn : Even n) {w : E} {L : Lt E r} {v : TF n g}
    (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) (z₀ : Fin n → Fin g → ℂ) (b : Fin n) :
    IsTheta1 X bas idx w x L fun t => thA X bas idx v x (Function.update z₀ b t) := by
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1
  refine ⟨h2.comp (differentiable_pi.2 fun k => ?_), fun u hu => ?_⟩
  · by_cases hk : k = b
    · subst hk
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne hk]
      exact differentiable_const _
  · funext t
    set y : Matrix (Fin n) (Fin r) E := Pi.single b u with hy
    have hyb : y b = u := Pi.single_eq_same _ _
    have hyk : ∀ k, k ≠ b → y k = 0 := fun k hk => Pi.single_eq_of_ne hk _
    have hm : y ∈ tens (stdL E n) L := (TensLat.mem_tens_stdL L _).2 fun k => by
      by_cases hk : k = b
      · rw [hk, hyb]; exact hu
      · rw [hyk k hk]; exact L.zero_mem
    have hp : pv X idx x 0 = 0 := by
      unfold pv
      rw [per_zero]
      rfl
    have e1 : epsW X w y = eps1 X w u := by
      unfold epsW eps1
      rw [Finset.sum_eq_single b, hyb]
      · intro k _ hk
        rw [hyk k hk]
        change EFBil X _ _ = 0
        simp
      · simp
    have e2 := (h1 y (Function.update z₀ b t)).2
    rw [Finset.sum_eq_single b, hyb, Function.update_self] at e2
    · have e3 : (fun k => Function.update z₀ b t k + pv X idx x (y k)) = Function.update z₀ b (t + pv X idx x u) := by
        funext k
        by_cases hk : k = b
        · rw [hk, hyb, Function.update_self, Function.update_self]
        · rw [hyk k hk, hp, add_zero, Function.update_of_ne hk, Function.update_of_ne hk]
      rw [e3] at e2
      conv_rhs => rw [← hv.2.2 y hm, GlobalTheory.SW.UnAct.thA_smul]
      simp only [Pi.smul_apply, fock, e1, e2, Nat.cast_one, _root_.one_mul]
    · intro k _ hk
      rw [hyk k hk, hp]
      simp [hx]
    · simp

include idx in

/- English proof (translation)
Use `(((thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1).2.2 _ (isSB_reflTF hv.1)).2 ?_).symm` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[thA_reflTF]`. Break down `Nat.eq_zero_or_pos n with rfl | hpos` into its components or cases. Rewrite using `[Subsingleton.elim (-z) z]`.

Distinguish the cases in `h0 : thA X bas idx v x = 0`. Simplify using `[h0]`. Take `⟨z₀, hz₀⟩` from `Function.ne_iff.1 h0`. Establish `hθ` using `isTheta1_update idx hs hn hv hd z₀ ⟨0, hpos⟩`. Use `set θ := fun t => thA X bas idx v x (Function.update z₀ ⟨0, hpos⟩ t) with hθd`.

Establish `ht : θ (z₀ ⟨0, hpos⟩) ≠ 0` using `by simpa [hθd] using hz₀`. Take `⟨a, ha⟩` from `GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx n hs hn w hw hw' L hL x hd _ θ (isTheta1_neg idx hθ) hθ (Function.ne_iff.2 ⟨_, ht⟩)`. Establish `ha' : ∀ t, θ (-t) = a * θ t` using `congrFun ha`. Establish `haa : a ^ 2 = 1`. Use `ha' (-z₀ ⟨0, hpos⟩)` as an intermediate fact.

Rewrite `this` using `[neg_neg, ha']`. Conclude with `mul_right_cancel₀ ht (by linear_combination -this)`. Take `⟨κ, hκ⟩` from `GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g bas idx n hs hn w hw hw' L hL v hv x hd θ hθ`. Establish `hκ0 : κ ≠ 0`. Introduce and unpack `rfl`.

Use `hκ fun _ => z₀ ⟨0, hpos⟩` as an intermediate fact. Rewrite `this` using `[zero_mul]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun _ _ => ht) this`. Use `mul_left_cancel₀ hκ0 ?_` and prove the remaining obligations. Rewrite using `[← hκ, ← hκ]`.

Take `⟨m, hm⟩` from `hn`. Establish `: a ^ n = 1` using `by rw [hm, ← two_mul, pow_mul, haa, one_pow]`. Simplify using `only [Pi.neg_apply, ha', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, this, _root_.one_mul]`.
-/
theorem reflTF_vac (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r}
    (hL : SelfD X L) {v : TF n g} (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) :
    reflTF n g v = v := by
  refine (((thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1).2.2 _ (isSB_reflTF hv.1)).2 ?_).symm
  funext z
  rw [thA_reflTF]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Subsingleton.elim (-z) z]
  by_cases h0 : thA X bas idx v x = 0
  · simp [h0]
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  have hθ := isTheta1_update idx hs hn hv hd z₀ ⟨0, hpos⟩
  set θ := fun t => thA X bas idx v x (Function.update z₀ ⟨0, hpos⟩ t) with hθd
  have ht : θ (z₀ ⟨0, hpos⟩) ≠ 0 := by simpa [hθd] using hz₀
  obtain ⟨a, ha⟩ := GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx n hs hn w hw hw' L hL x hd _ θ
    (isTheta1_neg idx hθ) hθ (Function.ne_iff.2 ⟨_, ht⟩)
  have ha' : ∀ t, θ (-t) = a * θ t := congrFun ha
  have haa : a ^ 2 = 1 := by
    have := ha' (-z₀ ⟨0, hpos⟩)
    rw [neg_neg, ha'] at this
    exact mul_right_cancel₀ ht (by linear_combination -this)
  obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g bas idx n hs hn w hw hw' L hL v hv x hd θ hθ
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have := hκ fun _ => z₀ ⟨0, hpos⟩
    rw [zero_mul] at this
    exact Finset.prod_ne_zero_iff.2 (fun _ _ => ht) this
  refine mul_left_cancel₀ hκ0 ?_
  rw [← hκ, ← hκ]
  obtain ⟨m, hm⟩ := hn
  have : a ^ n = 1 := by rw [hm, ← two_mul, pow_mul, haa, one_pow]
  simp only [Pi.neg_apply, ha', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, this,
    _root_.one_mul]

/- English proof (translation)
Introduce `E _ _ _ r g n X bas idx hs hn q0 hq w hw hw' L hL v hv Λ _ _ Q _ c Y P d hP x hd`. Establish `h1` using `reflTF_projA hs w (tens Λ.La L) (reflTF_vac idx hs hn hw hw' hL hv hd)`. Establish `h2 : gphi X bas w Λ.La L v c (fun q => -Y q) = reflTF n g (gphi X bas w Λ.La L v c Y)`. Unfold `gphi`. Rewrite using `[AddEquiv.map_finsum]`.

Simplify using `only [reflTF_smul, reflTF_heisG hs, h1]`. Unfold `thP`. Rewrite using `[h2, ← polyDeriv_comp_neg P d hP]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Conclude with `thA_reflTF idx _ x z`.
-/
theorem thP_gphi_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ Λ : Formalism.L2.Pj.GenLat E n, Λ.Unimod → Λ.La.FG → ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ∀ x ∈ X.dom, thP X hq bas idx (gphi X bas w Λ.La L v c (fun q => -Y q)) P x = (-1) ^ d * thP X hq bas idx (gphi X bas w Λ.La L v c Y) P x := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq w hw hw' L hL v hv Λ _ _ Q _ c Y P d hP x hd
  have h1 := reflTF_projA hs w (tens Λ.La L) (reflTF_vac idx hs hn hw hw' hL hv hd)
  have h2 : gphi X bas w Λ.La L v c (fun q => -Y q) = reflTF n g (gphi X bas w Λ.La L v c Y) := by
    unfold gphi
    rw [AddEquiv.map_finsum]
    simp only [reflTF_smul, reflTF_heisG hs, h1]
  unfold thP
  rw [h2, ← polyDeriv_comp_neg P d hP]
  congr 1
  funext z
  exact thA_reflTF idx _ x z

end GlobalTheory.AdTh.Parity
