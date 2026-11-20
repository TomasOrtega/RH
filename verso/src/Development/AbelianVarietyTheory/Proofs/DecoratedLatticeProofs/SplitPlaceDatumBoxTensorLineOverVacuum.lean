import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulHalf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
open scoped TensorProduct

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.BoxDatum

variable {D : D7}

/- English proof (translation)
Take `⟨s, rfl⟩` from `hL`. Use `choose N hN hm using fun t => GlobalTheory.VacUnique.Den.exists_nsmul_mem_lattice L' hL' (M.mulVec t)`. Use `⟨∏ t ∈ s, N t, Finset.prod_pos fun t _ => hN t, fun t ht => ?_⟩` and prove the remaining obligations. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`.

Rewrite using `[← Finset.prod_erase_mul s N (Finset.mem_coe.1 hx), mul_nsmul']`. Conclude with `nsmul_mem (hm x) _`. Consider the case `zero => rw [Matrix.mulVec_zero, nsmul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add, nsmul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [Matrix.mulVec_smul, smul_comm]`. Conclude with `L'.smul_mem c hx`.
-/
theorem exists_nsmul_mulVec {m m' : ℕ} (M : Matrix (Fin m') (Fin m) D.host.E)
    {L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin m → D.host.E)}
    {L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin m' → D.host.E)} (hL : L.FG)
    (hL' : Submodule.IsLattice D.host.E L') : ∃ N : ℕ, 0 < N ∧ ∀ t ∈ L, N • M.mulVec t ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  choose N hN hm using fun t => GlobalTheory.VacUnique.Den.exists_nsmul_mem_lattice L' hL' (M.mulVec t)
  refine ⟨∏ t ∈ s, N t, Finset.prod_pos fun t _ => hN t, fun t ht => ?_⟩
  induction ht using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s N (Finset.mem_coe.1 hx), mul_nsmul']
    exact nsmul_mem (hm x) _
  | zero => rw [Matrix.mulVec_zero, nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, nsmul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact L'.smul_mem c hx

/- English proof (translation)
Take `⟨N, hN, h⟩` from `exists_nsmul_mulVec M hL hL'`. Use `⟨N, hN, fun u hu => ?_⟩` and prove the remaining obligations. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩` from `hw`.

Use `AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, _, h t ht, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]`. Establish `e : ∀ l, (incA D (M i l) : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t l * ∑ k, star (s k) * S.gram k j)) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (M i l * (a * t l * ∑ k, star (s k) * S.gram k j))` using `fun l => by`. Express the relevant statement in the definitionally equal form `((1 : AF D.host.F) ⊗ₜ[D.host.F] M i l) * _ = _`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Simplify using `only [e]`. Rewrite using `[← TensorProduct.tmul_sum, ← TensorProduct.mk_apply, ← map_nsmul, TensorProduct.mk_apply]`. Use `congr 1`. Generalize the expression as in `∑ k, star (s k) * S.gram k j = c`.

Simplify using `only [nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Consider the case `zero => rw [Matrix.mul_zero, nsmul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mul_add, nsmul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [Matrix.mul_neg, neg_nsmul]`. Conclude with `neg_mem hx`.
-/
theorem exists_nsmul_rat_mul (S : HSp D) {T T' : HSp D} (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (LS : Set (Fin S.rank → D.host.E)) {L : Lat T} {L' : Lat T'} (hL : L.FG)
    (hL' : Submodule.IsLattice D.host.E L') (P : Pl D → Prop) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T LS (L : Set _) P, N • (rat M ⬝ u : WO S T') ∈ latO S T' LS (L' : Set _) P := by
  obtain ⟨N, hN, h⟩ := exists_nsmul_mulVec M hL hL'
  refine ⟨N, hN, fun u hu => ?_⟩
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, _, h t ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply,
      Matrix.mulVec, dotProduct]
    have e : ∀ l, (incA D (M i l) : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t l * ∑ k, star (s k) * S.gram k j)) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (M i l * (a * t l * ∑ k, star (s k) * S.gram k j)) := fun l => by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i l) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp only [e]
    rw [← TensorProduct.tmul_sum, ← TensorProduct.mk_apply, ← map_nsmul, TensorProduct.mk_apply]
    congr 1
    generalize ∑ k, star (s k) * S.gram k j = c
    simp only [nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => by ring
  | zero => rw [Matrix.mul_zero, nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, neg_nsmul]; exact neg_mem hx

/- English proof (translation)
Use `⟨Submodule.fg_span_singleton ζ, ?_⟩` and prove the remaining obligations. Establish `h0 : ζ ≠ 0` using `fun h0 => h.2 (by simp [h0])`. Rewrite using `[Submodule.span_span_of_tower]`. Establish `hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1` using `by simp [h.1]`. Conclude with `(finrank_eq_one_iff_of_nonzero ζ h0).1 hr`.
-/
theorem isLattice_span {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
  have h0 : ζ ≠ 0 := fun h0 => h.2 (by simp [h0])
  rw [Submodule.span_span_of_tower]
  have hr : Module.finrank D.host.E (Fin L.rank → D.host.E) = 1 := by simp [h.1]
  exact (finrank_eq_one_iff_of_nonzero ζ h0).1 hr

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply, Finset.mul_sum] exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hu a j]`.
-/
theorem isHalf_mul {l m n : ℕ} {e : AE D} (M : Mx D l m) {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (M ⬝ u : Mx D l n) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hu a j]

variable {S X T L : HSp D}

def boxMap (o : OrthDec X T L) (S : HSp D) (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ)) :
    (WO S X → ℂ) →ₗ[ℂ] (WO S X → ℂ) where
  toFun Φ z := T₃ (fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1) (o.resT S z).2
  map_add' Φ Φ' := by
    funext z
    have : (fun w => T₂ (fun x => (Φ + Φ') ((o.resT S).symm (x, w))) (o.resT S z).1) =
        (fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1) +
          fun w => T₂ (fun x => Φ' ((o.resT S).symm (x, w))) (o.resT S z).1 := by
      funext w
      exact congrFun (T₂.map_add (fun x => Φ ((o.resT S).symm (x, w))) fun x => Φ' ((o.resT S).symm (x, w))) _
    rw [this, map_add]; rfl
  map_smul' c Φ := by
    funext z
    have : (fun w => T₂ (fun x => (c • Φ) ((o.resT S).symm (x, w))) (o.resT S z).1) =
        c • fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1 := by
      funext w
      exact congrFun (T₂.map_smul c fun x => Φ ((o.resT S).symm (x, w))) _
    rw [this, map_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem boxMap_apply (o : OrthDec X T L) (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ))
    (Φ : WO S X → ℂ) (z : WO S X) : boxMap o S T₂ T₃ Φ z =
      T₃ (fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) (o.resT S z).1) (o.resT S z).2 := rfl

/- English proof (translation)
Use function extensionality and compare the values at `z`. Rewrite using `[boxMap_apply]`. Establish `: (fun w => T₂ (fun x => o.boxT S φ φ' ((o.resT S).symm (x, w))) (o.resT S z).1) = T₂ φ (o.resT S z).1 • φ'`. Use function extensionality and compare the values at `w`. Establish `e : (fun x => o.boxT S φ φ' ((o.resT S).symm (x, w))) = φ' w • φ`.

Use function extensionality and compare the values at `x`. Simplify using `only [OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, mul_comm]`. Rewrite using `[e, map_smul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_comm]`. Rewrite using `[this, map_smul]`.

Both sides reduce to the same expression.
-/
theorem boxMap_boxT (o : OrthDec X T L) (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ))
    (φ : WO S T → ℂ) (φ' : WO S L → ℂ) : boxMap o S T₂ T₃ (o.boxT S φ φ') = o.boxT S (T₂ φ) (T₃ φ') := by
  funext z
  rw [boxMap_apply]
  have : (fun w => T₂ (fun x => o.boxT S φ φ' ((o.resT S).symm (x, w))) (o.resT S z).1) =
      T₂ φ (o.resT S z).1 • φ' := by
    funext w
    have e : (fun x => o.boxT S φ φ' ((o.resT S).symm (x, w))) = φ' w • φ := by
      funext x
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [this, map_smul]; rfl

/- English proof (translation)
The claim follows from `isHalf_mul o.pA ht`.
-/
theorem half_fst (o : OrthDec X T L) {e : AE D} {t : WO S X} (ht : IsHalf e t) : IsHalf e (o.resT S t).1 :=
  isHalf_mul o.pA ht

/- English proof (translation)
The claim follows from `isHalf_mul o.pB ht`.
-/
theorem half_snd (o : OrthDec X T L) {e : AE D} {t : WO S X} (ht : IsHalf e t) : IsHalf e (o.resT S t).2 :=
  isHalf_mul o.pB ht

/- English proof (translation)
The claim follows from `GlobalTheory.FinPl.Rebase.isHalf_add (isHalf_mul o.jA hx) (isHalf_mul o.jB hw)`.
-/
theorem half_symm (o : OrthDec X T L) {e : AE D} {x : WO S T} {w : WO S L} (hx : IsHalf e x) (hw : IsHalf e w) :
    IsHalf e ((o.resT S).symm (x, w)) :=
  GlobalTheory.FinPl.Rebase.isHalf_add (isHalf_mul o.jA hx) (isHalf_mul o.jB hw)

/- English proof (translation)
Introduce `_ _` and use `mul_zero _`.
-/
theorem half_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := fun _ _ => mul_zero _

structure Near (o : OrthDec X T L) (ΛX : AddSubgroup (WO S X)) (ΛT : AddSubgroup (WO S T)) (ΛL : AddSubgroup (WO S L))
    (N : ℕ) : Prop where
  pos : 0 < N
  fst : ∀ t ∈ ΛX, N • (o.resT S t).1 ∈ ΛT
  snd : ∀ t ∈ ΛX, N • (o.resT S t).2 ∈ ΛL
  inl : ∀ u ∈ ΛT, N • (o.resT S).symm (u, 0) ∈ ΛX
  inr : ∀ u ∈ ΛL, N • (o.resT S).symm (0, u) ∈ ΛX

/- English proof (translation)
Take `⟨a, ha, h1⟩` from `exists_nsmul_rat_mul S o.qA LS hX.fg hT P`. Take `⟨b, hb, h2⟩` from `exists_nsmul_rat_mul S o.qB LS hX.fg hL P`. Take `⟨c, hc, h3⟩` from `exists_nsmul_rat_mul S o.iA LS hT.fg hX P`. Take `⟨d, hd, h4⟩` from `exists_nsmul_rat_mul S o.iB LS hL.fg hX P`. Use `⟨a * b * c * d, by positivity, fun t ht => ?_, fun t ht => ?_, fun u hu => ?_, fun u hu => ?_⟩` and prove the remaining obligations.

Rewrite using `[show a * b * c * d = a * (b * c * d) by ring, mul_nsmul]`. Conclude with `nsmul_mem (h1 t ht) _`. Rewrite using `[show a * b * c * d = b * (a * c * d) by ring, mul_nsmul]`. Conclude with `nsmul_mem (h2 t ht) _`. Rewrite using `[show a * b * c * d = c * (a * b * d) by ring, mul_nsmul, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]`.

Conclude with `nsmul_mem (h3 u hu) _`. Rewrite using `[show a * b * c * d = d * (a * b * c) by ring, mul_nsmul, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]`. Conclude with `nsmul_mem (h4 u hu) _`.
-/
theorem exists_near (o : OrthDec X T L) (LS : Set (Fin S.rank → D.host.E)) {LX : Lat X} {LT : Lat T} {LL : Lat L}
    (hX : Submodule.IsLattice D.host.E LX) (hT : Submodule.IsLattice D.host.E LT) (hL : Submodule.IsLattice D.host.E LL)
    (P : Pl D → Prop) :
    ∃ N, Near o (latO S X LS (LX : Set _) P) (latO S T LS (LT : Set _) P) (latO S L LS (LL : Set _) P) N := by
  obtain ⟨a, ha, h1⟩ := exists_nsmul_rat_mul S o.qA LS hX.fg hT P
  obtain ⟨b, hb, h2⟩ := exists_nsmul_rat_mul S o.qB LS hX.fg hL P
  obtain ⟨c, hc, h3⟩ := exists_nsmul_rat_mul S o.iA LS hT.fg hX P
  obtain ⟨d, hd, h4⟩ := exists_nsmul_rat_mul S o.iB LS hL.fg hX P
  refine ⟨a * b * c * d, by positivity, fun t ht => ?_, fun t ht => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [show a * b * c * d = a * (b * c * d) by ring, mul_nsmul]
    exact nsmul_mem (h1 t ht) _
  · rw [show a * b * c * d = b * (a * c * d) by ring, mul_nsmul]
    exact nsmul_mem (h2 t ht) _
  · rw [show a * b * c * d = c * (a * b * d) by ring, mul_nsmul, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
    exact nsmul_mem (h3 u hu) _
  · rw [show a * b * c * d = d * (a * b * c) by ring, mul_nsmul, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact nsmul_mem (h4 u hu) _

section Slices

variable {o : OrthDec X T L} {ΛX : AddSubgroup (WO S X)} {ΛT : AddSubgroup (WO S T)} {ΛL : AddSubgroup (WO S L)} {N : ℕ}
  {e : AE D}

/- English proof (translation)
Rewrite using `[← map_nsmul, ← map_add, Prod.smul_mk, Prod.mk_add_mk, nsmul_zero, add_zero]`.
-/
theorem symm_add_left (o : OrthDec X T L) (x u : WO S T) (w : WO S L) (K : ℕ) :
    (o.resT S).symm (x + K • u, w) = (o.resT S).symm (x, w) + K • (o.resT S).symm (u, 0) := by
  rw [← map_nsmul, ← map_add, Prod.smul_mk, Prod.mk_add_mk, nsmul_zero, add_zero]

/- English proof (translation)
Rewrite using `[← map_nsmul, ← map_add, Prod.smul_mk, Prod.mk_add_mk, nsmul_zero, add_zero]`.
-/
theorem symm_add_right (o : OrthDec X T L) (x : WO S T) (w u : WO S L) (K : ℕ) :
    (o.resT S).symm (x, w + K • u) = (o.resT S).symm (x, w) + K • (o.resT S).symm (0, u) := by
  rw [← map_nsmul, ← map_add, Prod.smul_mk, Prod.mk_add_mk, nsmul_zero, add_zero]

/- English proof (translation)
Take `⟨h1, k, hk, h2, h3⟩` from `hΦ`. Use `⟨fun x hx => ?_, N * k, Nat.mul_pos h.pos hk, fun u hu hh x => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `half_fst o (h1 _ hx)` as an intermediate fact. Rewrite `this` using `[AddEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `beta_reduce`.

Rewrite using `[symm_add_left, mul_nsmul]`. Conclude with `h2 _ (h.inl u hu) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_symm o hh (half_zero e)) N) _`. Use `h.fst _ (h3 _ hx)` as an intermediate fact. Rewrite `this` using `[map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_fst, ← mul_nsmul']`. Then use the resulting hypothesis.
-/
theorem sb_slice_left (h : Near o ΛX ΛT ΛL N) {Φ : WO S X → ℂ} (hΦ : IsSBHalf e ΛX Φ) (w : WO S L) :
    IsSBHalf e ΛT fun x => Φ ((o.resT S).symm (x, w)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  refine ⟨fun x hx => ?_, N * k, Nat.mul_pos h.pos hk, fun u hu hh x => ?_, fun x hx => ?_⟩
  · have := half_fst o (h1 _ hx)
    rwa [AddEquiv.apply_symm_apply] at this
  · beta_reduce
    rw [symm_add_left, mul_nsmul]
    exact h2 _ (h.inl u hu) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_symm o hh (half_zero e)) N) _
  · have := h.fst _ (h3 _ hx)
    rwa [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_fst, ← mul_nsmul'] at this

/- English proof (translation)
Take `⟨h1, k, hk, h2, h3⟩` from `hΦ`. Establish `hne : ∀ w, T₂ (fun x => Φ ((o.resT S).symm (x, w))) z ≠ 0 → ∃ x, Φ ((o.resT S).symm (x, w)) ≠ 0`. Introduce `w hw`. Assume the negation of the conclusion as `hc`. Use `hw ?_` and prove the remaining obligations.

Establish `: (fun x => Φ ((o.resT S).symm (x, w))) = 0` using `funext fun x => by`. Assume the negation of the conclusion as `hx`. Conclude with `hc ⟨x, hx⟩`. Rewrite using `[this, map_zero]`. Both sides reduce to the same expression.

Use `⟨fun w hw => ?_, N * k, Nat.mul_pos h.pos hk, fun u hu hh w => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hne w hw`. Use `half_snd o (h1 _ hx)` as an intermediate fact. Rewrite `this` using `[AddEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `: (fun x => Φ ((o.resT S).symm (x, w + (N * k) • u))) = fun x => Φ ((o.resT S).symm (x, w))`.

Use function extensionality and compare the values at `x`. Rewrite using `[symm_add_right, mul_nsmul]`. Conclude with `h2 _ (h.inr u hu) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_symm o (half_zero e) hh) N) _`. Simplify using `only [this]`. Take `⟨x, hx⟩` from `hne w hw`.

Use `h.snd _ (h3 _ hx)` as an intermediate fact. Rewrite `this` using `[map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_snd, ← mul_nsmul']`. Then use the resulting hypothesis.
-/
theorem sb_slice_right (h : Near o ΛX ΛT ΛL N) {Φ : WO S X → ℂ} (hΦ : IsSBHalf e ΛX Φ)
    (T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (z : WO S T) :
    IsSBHalf e ΛL fun w => T₂ (fun x => Φ ((o.resT S).symm (x, w))) z := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hne : ∀ w, T₂ (fun x => Φ ((o.resT S).symm (x, w))) z ≠ 0 → ∃ x, Φ ((o.resT S).symm (x, w)) ≠ 0 := by
    intro w hw
    by_contra hc
    refine hw ?_
    have : (fun x => Φ ((o.resT S).symm (x, w))) = 0 := funext fun x => by
      by_contra hx; exact hc ⟨x, hx⟩
    rw [this, map_zero]; rfl
  refine ⟨fun w hw => ?_, N * k, Nat.mul_pos h.pos hk, fun u hu hh w => ?_, fun w hw => ?_⟩
  · obtain ⟨x, hx⟩ := hne w hw
    have := half_snd o (h1 _ hx)
    rwa [AddEquiv.apply_symm_apply] at this
  · have : (fun x => Φ ((o.resT S).symm (x, w + (N * k) • u))) = fun x => Φ ((o.resT S).symm (x, w)) := by
      funext x
      rw [symm_add_right, mul_nsmul]
      exact h2 _ (h.inr u hu) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_symm o (half_zero e) hh) N) _
    simp only [this]
  · obtain ⟨x, hx⟩ := hne w hw
    have := h.snd _ (h3 _ hx)
    rwa [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_snd, ← mul_nsmul'] at this

/- English proof (translation)
Take `⟨a1, a, ha, a2, a3⟩` from `hφ`. Take `⟨b1, b, hb, b2, b3⟩` from `hφ'`. Establish `hN` using `h.pos`. Use `⟨fun t ht => ?_, N * a * b, by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite using `[← (o.resT S).symm_apply_apply t]`.

Conclude with `half_symm o (a1 _ (left_ne_zero_of_mul ht)) (b1 _ (right_ne_zero_of_mul ht))`. Simplify using `only [OrthDec.boxT]`. Rewrite using `[map_add, map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]`. Use `congr 1`. Rewrite using `[show N * a * b = N * b * a by ring, mul_nsmul, mul_nsmul]`.

Conclude with `a2 _ (nsmul_mem (h.fst u hu) b) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_fst o hh) N) b) _`. Rewrite using `[mul_nsmul, mul_nsmul]`. Conclude with `b2 _ (nsmul_mem (h.snd u hu) a) (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_snd o hh) N) a) _`. Establish `p1` using `h.inl _ (nsmul_mem (a3 _ (left_ne_zero_of_mul ht)) b)`. Establish `p2` using `h.inr _ (nsmul_mem (b3 _ (right_ne_zero_of_mul ht)) a)`.

Use `add_mem p1 p2` as an intermediate fact. Rewrite `this` using `[← nsmul_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add, ← mul_nsmul, ← mul_nsmul, mul_comm b a, ← Prod.smul_mk, map_nsmul, Prod.mk.eta, AddEquiv.symm_apply_apply, ← mul_nsmul']`. Rewrite using `[mul_assoc]` and apply the resulting hypothesis.
-/
theorem sb_boxT (h : Near o ΛX ΛT ΛL N) {φ : WO S T → ℂ} {φ' : WO S L → ℂ} (hφ : IsSBHalf e ΛT φ)
    (hφ' : IsSBHalf e ΛL φ') : IsSBHalf e ΛX (o.boxT S φ φ') := by
  obtain ⟨a1, a, ha, a2, a3⟩ := hφ
  obtain ⟨b1, b, hb, b2, b3⟩ := hφ'
  have hN := h.pos
  refine ⟨fun t ht => ?_, N * a * b, by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  · rw [← (o.resT S).symm_apply_apply t]
    exact half_symm o (a1 _ (left_ne_zero_of_mul ht)) (b1 _ (right_ne_zero_of_mul ht))
  · simp only [OrthDec.boxT]
    rw [map_add, map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    congr 1
    · rw [show N * a * b = N * b * a by ring, mul_nsmul, mul_nsmul]
      exact a2 _ (nsmul_mem (h.fst u hu) b)
        (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_fst o hh) N) b) _
    · rw [mul_nsmul, mul_nsmul]
      exact b2 _ (nsmul_mem (h.snd u hu) a)
        (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (GlobalTheory.FinPl.DatumBack.isHalf_nsmul' (half_snd o hh) N) a) _
  · have p1 := h.inl _ (nsmul_mem (a3 _ (left_ne_zero_of_mul ht)) b)
    have p2 := h.inr _ (nsmul_mem (b3 _ (right_ne_zero_of_mul ht)) a)
    have := add_mem p1 p2
    rw [← nsmul_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add, ← mul_nsmul, ← mul_nsmul, mul_comm b a,
      ← Prod.smul_mk, map_nsmul, Prod.mk.eta, AddEquiv.symm_apply_apply, ← mul_nsmul'] at this
    rwa [mul_assoc]

/- English proof (translation)
Use `⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, by rw [one_smul]⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[boxMap_apply]`. Establish `e1 : (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w) + x)) (o.resT S z).1) = ψ (symplOH S T (o.resT S z).1 (o.resT S x).1) • fun w => (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w))) ((o.resT S z).1 + (o.resT S x).1)) (w + (o.resT S x).2)`. Use function extensionality and compare the values at `w`.

Establish `e2 : (fun x' => Φ ((o.resT S).symm (x', w) + x)) = fun x' => (fun x' => Φ ((o.resT S).symm (x', w + (o.resT S x).2))) (x' + (o.resT S x).1)`. Use function extensionality and compare the values at `x'`. Use `show _ = Φ ((o.resT S).symm ((x', w) + o.resT S x))`. Rewrite using `[map_add, AddEquiv.symm_apply_apply]`. Rewrite using `[e2, h₂.trans _ (sb_slice_left h hΦ _) _ (half_fst o hx)]`.

Both sides reduce to the same expression. Rewrite using `[e1, map_smul, h₃.trans _ (sb_slice_right h hΦ T₂ _) _ (half_snd o hx)]`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[boxMap_apply, o.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, mul_assoc]`. Use function extensionality and compare the values at `z`.

Rewrite using `[boxMap_apply]`. Establish `e1 : (fun w => T₂ (fun x' => ψ (symplO S X ((o.resT S).symm (x', w)) y) * Φ ((o.resT S).symm (x', w))) (o.resT S z).1) = ψ (symplOH S T (o.resT S z).1 (o.resT S y).1) • fun w => ψ (symplO S L w (o.resT S y).2) * (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w))) ((o.resT S z).1 …`. Use function extensionality and compare the values at `w`. Establish `e2 : (fun x' => ψ (symplO S X ((o.resT S).symm (x', w)) y) * Φ ((o.resT S).symm (x', w))) = ψ (symplO S L w (o.resT S y).2) • fun x' => ψ (symplO S T x' (o.resT S y).1) * (fun x' => Φ ((o.resT S).symm (x', w))) x'`. Use function extensionality and compare the values at `x'`.

Rewrite using `[o.symplO_resT, AddEquiv.apply_symm_apply, AddChar.map_add_eq_mul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, map_smul, h₂.modul _ (sb_slice_left h hΦ _) _ (half_fst o hy)]`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, map_smul, h₃.modul _ (sb_slice_right h hΦ T₂ _) _ (half_snd o hy)]`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[boxMap_apply, o.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, mul_assoc]`.
-/
theorem isPlaceModel_boxMap {ψ : AddChar (AF D.host.F) ℂ} (h : Near o ΛX ΛT ΛL N) {f₂ : WO S T → ℂ} {f₃ : WO S L → ℂ}
    {T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {T₃ : (WO S L → ℂ) →ₗ[ℂ] (WO S L → ℂ)}
    (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e ΛT 1 f₂ T₂)
    (h₃ : IsPlaceModel ψ (symplO S L) (heisO ψ S L) e ΛL 1 f₃ T₃) :
    IsPlaceModel ψ (symplO S X) (heisO ψ S X) e ΛX 1 (boxMap o S T₂ T₃ (halfInd e ΛX)) (boxMap o S T₂ T₃) := by
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, by rw [one_smul]⟩
  · funext z
    rw [boxMap_apply]
    have e1 : (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w) + x)) (o.resT S z).1) =
        ψ (symplOH S T (o.resT S z).1 (o.resT S x).1) • fun w =>
          (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w))) ((o.resT S z).1 + (o.resT S x).1)) (w + (o.resT S x).2) := by
      funext w
      have e2 : (fun x' => Φ ((o.resT S).symm (x', w) + x)) =
          fun x' => (fun x' => Φ ((o.resT S).symm (x', w + (o.resT S x).2))) (x' + (o.resT S x).1) := by
        funext x'
        show _ = Φ ((o.resT S).symm ((x', w) + o.resT S x))
        rw [map_add, AddEquiv.symm_apply_apply]
      rw [e2, h₂.trans _ (sb_slice_left h hΦ _) _ (half_fst o hx)]
      rfl
    rw [e1, map_smul, h₃.trans _ (sb_slice_right h hΦ T₂ _) _ (half_snd o hx)]
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    rw [boxMap_apply, o.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, mul_assoc]
  · funext z
    rw [boxMap_apply]
    have e1 : (fun w => T₂ (fun x' => ψ (symplO S X ((o.resT S).symm (x', w)) y) * Φ ((o.resT S).symm (x', w)))
          (o.resT S z).1) =
        ψ (symplOH S T (o.resT S z).1 (o.resT S y).1) • fun w => ψ (symplO S L w (o.resT S y).2) *
          (fun w => T₂ (fun x' => Φ ((o.resT S).symm (x', w))) ((o.resT S z).1 + (o.resT S y).1)) w := by
      funext w
      have e2 : (fun x' => ψ (symplO S X ((o.resT S).symm (x', w)) y) * Φ ((o.resT S).symm (x', w))) =
          ψ (symplO S L w (o.resT S y).2) • fun x' => ψ (symplO S T x' (o.resT S y).1) *
            (fun x' => Φ ((o.resT S).symm (x', w))) x' := by
        funext x'
        rw [o.symplO_resT, AddEquiv.apply_symm_apply, AddChar.map_add_eq_mul]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e2, map_smul, h₂.modul _ (sb_slice_left h hΦ _) _ (half_fst o hy)]
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, map_smul, h₃.modul _ (sb_slice_right h hΦ T₂ _) _ (half_snd o hy)]
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    rw [boxMap_apply, o.symplOH_resT, AddChar.map_add_eq_mul, map_add, Prod.fst_add, Prod.snd_add, mul_assoc]

end Slices

/- English proof (translation)
Rewrite using `[GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_apply, Finsupp.sum]`. Conclude with `Finset.sum_induction _ (IsThetaFunO ψ S X) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero fun u _ => GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)`.
-/
theorem isTheta_comb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (c : WO S X →₀ ℂ) {f : WO S X → ℂ}
    (hf : IsThetaFunO ψ S X f) : IsThetaFunO ψ S X (comb ψ S X c f) := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_induction _ (IsThetaFunO ψ S X) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
    fun u _ => GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.FinPl.OverProof in

/- English proof (translation)
Introduce `D k _ _ _ _ p n n'' _ _ _ _ ψ hψ _ S X T L o ζ hζ β γ γ₀ hγ LS LT LX hS hT hX f₂ F₂ Ψ₂ hO b g₃ T₃ hg₃ h₃ hSB`. Take `⟨T₂, h₂⟩` from `hO.2.2.2.2.1`. Establish `hF : F₂ = T₂ (extFun β γ Ψ₂)` using `hO.2.2.2.2.2 T₂ h₂`. Take `⟨N, hN⟩` from `exists_near (S := S) o (LS : Set _) hX.1 hT.1 (isLattice_span hζ) (· = p.v)`. Establish `h₀` using `isPlaceModel_boxMap hN h₂ h₃`.

Take `⟨ε, hε, heq⟩` from `p.above`. Establish `hs` using `p.split`. Establish `he` using `hs.1`. Establish `hec` using `hs.2.1`. Establish `heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e` using `by rw [← heq]; linear_combination he + hec`.

Take `⟨hLL', hXX, -, hfin, hden⟩` from `dualPair hψ hS hX hs hε heq`. Establish `hdX : ∀ x ∈ half S X p.e, ∃ k : ℕ, 0 < k ∧ k • x ∈ latO S X (LS : Set _) (LX : Set _) (· = p.v)`. Introduce `x hx`. Take `⟨k, hk, hkx⟩` from `exists_nsmul_mem_latO' hS.1 hX.1 x (infPart_half hε heε hx)`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations.

Use `(idem_smul_mem hε he heε hkx).1` as an intermediate fact. Rewrite `this` using `[smul_comm, (mem_half S X).1 hx]`. Then use the resulting hypothesis. Establish `hb` using `sb_boxT hN (GlobalTheory.isSBHalf_halfInd p.e _) (GlobalTheory.isSBHalf_halfInd p.e _)`. Take `⟨c, -, hc⟩` from `GlobalTheory.FinPl.DatumBack.exists_back ψ hec _ hLL' hXX hfin hdX hden hb fun h0 => by`. Use `congrFun h0 0` as an intermediate fact.

Rewrite `this` using `[OrthDec.boxT_zero]`. Simplify using `[halfInd, half_zero] at this`. Establish `v₂` using `h₂.vac`. Establish `v₃` using `h₃.vac`. Rewrite `v₂`, `v₃` using `[one_smul]`.

Use `⟨_, hS, hX, ⟨?_, GlobalTheory.FinPl.Rebase.latVac_image D k p ψ hψ S X LS LS LX LX hS hX hS hX _ _ h₀⟩, hSB, ⟨_, h₀⟩, fun T' hT' => ?_⟩` and prove the remaining obligations. Rewrite using `[hc _ _ h₀, boxMap_boxT, v₂, v₃]`. Conclude with `isTheta_comb hψ c (o.isThetaFunO_boxT hO.2.2.1.1 hg₃)`. Use `beta_reduce`. Rewrite using `[← placeModel_unique_of_dual ψ _ hLL' hXX hfin hden h₀ hT' (isSBHalf_extFun D k p _ n S X β γ₀ LS LX hS hX _ hSB), GlobalTheory.FinPl.ExtZero.extFun_tensRow D k p n n'' X T L S o ζ hζ γ γ₀ β hγ Ψ₂ b, boxMap_boxT, hF]`.
-/
theorem over_boxT : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S X T L'' : HSp D) (o'' : OrthDec X T L'') (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o'' ζ₀ γ γ₀ → ∀ (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → ∀ (f₂ F₂ : WO S T → ℂ) (Ψ₂ : Matrix n'' n k → ℂ), Over ψ β γ LS LT f₂ Ψ₂ F₂ → ∀ (b : (n → k) → ℂ) (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ → IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ → GlobalTheory.FinPl.tensRow Ψ₂ b ∈ SB (Matrix (n'' ⊕ Fin 1) n k) → ∃ g, Over ψ β γ₀ LS LX g (GlobalTheory.FinPl.tensRow Ψ₂ b) (o''.boxT S F₂ (T₃ (rowFun β ζ₀ b))) := by
  intro D k _ _ _ _ p n n'' _ _ _ _ ψ hψ _ S X T L o ζ hζ β γ γ₀ hγ LS LT LX hS hT hX f₂ F₂ Ψ₂ hO b g₃ T₃ hg₃ h₃ hSB
  obtain ⟨T₂, h₂⟩ := hO.2.2.2.2.1
  have hF : F₂ = T₂ (extFun β γ Ψ₂) := hO.2.2.2.2.2 T₂ h₂
  obtain ⟨N, hN⟩ := exists_near (S := S) o (LS : Set _) hX.1 hT.1 (isLattice_span hζ) (· = p.v)
  have h₀ := isPlaceModel_boxMap hN h₂ h₃
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  obtain ⟨hLL', hXX, -, hfin, hden⟩ := dualPair hψ hS hX hs hε heq
  have hdX : ∀ x ∈ half S X p.e, ∃ k : ℕ, 0 < k ∧ k • x ∈ latO S X (LS : Set _) (LX : Set _) (· = p.v) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := exists_nsmul_mem_latO' hS.1 hX.1 x (infPart_half hε heε hx)
    refine ⟨k, hk, ?_⟩
    have := (idem_smul_mem hε he heε hkx).1
    rwa [smul_comm, (mem_half S X).1 hx] at this
  have hb := sb_boxT hN (GlobalTheory.isSBHalf_halfInd p.e _) (GlobalTheory.isSBHalf_halfInd p.e _)
  obtain ⟨c, -, hc⟩ := GlobalTheory.FinPl.DatumBack.exists_back ψ hec _ hLL' hXX hfin hdX hden hb fun h0 => by
    have := congrFun h0 0
    rw [OrthDec.boxT_zero] at this
    simp [halfInd, half_zero] at this
  have v₂ := h₂.vac
  have v₃ := h₃.vac
  rw [one_smul] at v₂ v₃
  refine ⟨_, hS, hX, ⟨?_, GlobalTheory.FinPl.Rebase.latVac_image D k p ψ hψ S X LS LS LX LX hS hX hS hX _ _ h₀⟩, hSB, ⟨_, h₀⟩,
    fun T' hT' => ?_⟩
  · rw [hc _ _ h₀, boxMap_boxT, v₂, v₃]
    exact isTheta_comb hψ c (o.isThetaFunO_boxT hO.2.2.1.1 hg₃)
  · beta_reduce
    rw [← placeModel_unique_of_dual ψ _ hLL' hXX hfin hden h₀ hT'
      (isSBHalf_extFun D k p _ n S X β γ₀ LS LX hS hX _ hSB),
      GlobalTheory.FinPl.ExtZero.extFun_tensRow D k p n n'' X T L S o ζ hζ γ γ₀ β hγ Ψ₂ b, boxMap_boxT, hF]

end GlobalTheory.FinPl.BoxDatum

end
