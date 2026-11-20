import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftNearOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongruenceUnipotentMatrixReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf

noncomputable section

section Loc
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.TopCongr GlobalTheory.LocMod
namespace GlobalTheory.Fam.TopFrames
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Distinguish the cases in `hx : IntM x`. Establish `e : x * g = x + x * (g - 1)` using `by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]`. Rewrite using `[e, hp x _ hx (hx.mul_maxM hg)]`. Take `⟨u, hu, rfl⟩` from `exists_mem_KOne hg`. Establish `h1 : f x = 0` using `by_contra fun h => hx (hs x h)`.

Establish `h2 : f (x * u.val) = 0` using `by_contra fun h => hx (by`. Use `(hs _ h).mul (mem_KO.1 (KOne_le_KO hu)).2` as an intermediate fact. Rewrite using `[Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this)` and apply the resulting hypothesis. Rewrite using `[h1, h2]`.
-/
theorem mul_right_invariant {a b : Type} [Fintype b] [DecidableEq b] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix b b k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (x * g) = f x := by
  by_cases hx : IntM x
  · have e : x * g = x + x * (g - 1) := by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
    rw [e, hp x _ hx (hx.mul_maxM hg)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (x * u.val) = 0 := by_contra fun h => hx (by
      have := (hs _ h).mul (mem_KO.1 (KOne_le_KO hu)).2
      rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this)
    rw [h1, h2]

/- English proof (translation)
Use `mul_right_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x` and prove the remaining obligations. Unfold `Chain.xiTop at hx`. Take `⟨h1, h2⟩` from `mul_ne_zero_iff.1 hx`. Introduce and unpack `(i | i) j`. Rewrite `h1` using `[phiTop_eq]`.

Simplify using `using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i) ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))`. Conclude with `by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))`. Unfold `Chain.xiTop`. Establish `hxy` using `hx.add hy.intM`. Rewrite using `[Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _), phiTop_eq, phiTop_eq]`.

Use `congr 1`. Establish `e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0`. Use extensionality with `i (j | j)`. Both sides reduce to the same expression. Conclude with `j.elim0`.

Rewrite using `[e, submatrix_add]`. Use `TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[submatrix_apply]`. Break down `stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j` into its components or cases. Conclude with `hy _ _`.

Conclude with `j.elim0`. Establish `e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ())` using `rfl`. Rewrite using `[e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]`.
-/
theorem xiTop_mul_right [MeasurableSpace k] [BorelSpace k] {ν : Measure k} (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] {g : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k} (hg : MaxM (g - 1))
    (x : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) :
    (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (x * g) =
      (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  refine mul_right_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x
  · unfold Chain.xiTop at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rintro (i | i) j
    · rw [phiTop_eq] at h1
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i)
        ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))
    · exact by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))
  · unfold Chain.xiTop
    have hxy := hx.add hy.intM
    rw [Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _),
      phiTop_eq, phiTop_eq]
    congr 1
    · have e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0 := by
        ext i (j | j)
        · rfl
        · exact j.elim0
      rw [e, submatrix_add]
      refine TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_
      rw [submatrix_apply]
      rcases stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j
      · exact hy _ _
      · exact j.elim0
    · have e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ()) := rfl
      rw [e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]

/- English proof (translation)
Rewrite using `[← F.γβ, ← Matrix.mul_sub]`. Conclude with `hF.mul_maxM hM`.
-/
theorem coords_near {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k n Y) (hF : IntM F.γ) {M : Matrix (Fin n) Y k}
    (hM : MaxM (M - F.β)) : MaxM (F.γ * M - 1) := by
  rw [← F.γβ, ← Matrix.mul_sub]
  exact hF.mul_maxM hM

/- English proof (translation)
Establish `e : FT.γ * z * FS.β * (FS.γ * β) = FT.γ * M * x`. Rewrite using `[Matrix.mul_assoc _ FS.β, ← Matrix.mul_assoc FS.β, FS.βγ, Matrix.one_mul, Matrix.mul_assoc, ← hx, Matrix.mul_assoc]`. Rewrite using `[← xiTop_mul_right hν S t (coords_near FS hS hβ), e]`. Conclude with `xiTop_mul_congr k ν hν s κ S t _ (coords_near FT hT hM) x`.
-/
theorem xiTop_frames [MeasurableSpace k] [BorelSpace k] {ν : Measure k} (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] {a b : ℕ} (FS : Frame k a (XIx (Fin κ) t (s + 1)))
    (FT : Frame k b (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit)) (hS : IntM FS.γ) (hT : IntM FT.γ) {β M} (hβ : MaxM (β - FS.β))
    (hM : MaxM (M - FT.β)) (z : Matrix (Fin b) (Fin a) k) {x} (hx : M * x = z * β) :
    (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (FT.γ * z * FS.β) =
      (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  have e : FT.γ * z * FS.β * (FS.γ * β) = FT.γ * M * x := by
    rw [Matrix.mul_assoc _ FS.β, ← Matrix.mul_assoc FS.β, FS.βγ, Matrix.one_mul, Matrix.mul_assoc, ← hx, Matrix.mul_assoc]
  rw [← xiTop_mul_right hν S t (coords_near FS hS hβ), e]
  exact xiTop_mul_congr k ν hν s κ S t _ (coords_near FT hT hM) x

end GlobalTheory.Fam.TopFrames
end Loc

section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix
open GlobalTheory.SeeSaw.BaseFrame GlobalTheory.TopStep
namespace GlobalTheory.Fam.TopFrames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  [StarRing E] {hc : Formalism.BasicNotions.CMData F E}

/- English proof (translation)
Establish `key : ∀ (f : Sp E n ≃ₗ[E] Sp E n) i j, Valued.v (kMat w.1 (1 : GL (Fin n) (AfE F E)) f i j - (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) = w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0)` using `fun f i j => by`. Rewrite using `[kMat_one, Matrix.one_apply, if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl, ← valued_algebraMap, map_sub (algebraMap E (w.1.adicCompletion E)), apply_ite (algebraMap E _), map_one, map_zero]`. Establish `h2` using `val_kMat_sub_lt h w hg`. Establish `h3` using `val_kMat_sub_lt h₀ w hf`. Rewrite `h2`, `h3` using `[← one_mul k, kMat_mul]`.

Establish `hc1 : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n)` using `fun x => by simp`. Establish `i1` using `val_kMat_le (P := w.1) (f := 1) (hN ▸ h₀.lat : Formalism.L2.Herm.Carries k (stdLat E n) (stdLat E n)) fun _ => Iff.rfl`. Establish `i2` using `val_kMat_le (P := w.1) (f := f) hc1 (hN ▸ hf.1 : CharValCompare.IsFr w.1 (stdLat E n) f)`. Rewrite using `[← key]`. Conclude with `near_right _ i2 (near_left _ i1 (fun i j => by rw [key]; exact hg1 i j) h2) h3 i j`.
-/
theorem lift_near_of_lift {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} {k : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}
    {p₀ : DecoF E n ST SG Q'} (h : IsPtOf hc k p) (h₀ : IsPtOf hc k p₀) (hN : p₀.deco.1.N = stdLat E n) (w : SG)
    {g f : Sp E n ≃ₗ[E] Sp E n} (hg : IsLiftFr p.deco.1 w g)
    (hg1 : ∀ i j : Fin n, w.1.valuation E (g (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    (hf : IsLiftFr p₀.deco.1 w f) (i j : Fin n) :
    w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  have key : ∀ (f : Sp E n ≃ₗ[E] Sp E n) i j, Valued.v (kMat w.1 (1 : GL (Fin n) (AfE F E)) f i j -
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) =
      w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) := fun f i j => by
    rw [kMat_one, Matrix.one_apply, if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl, ← valued_algebraMap,
      map_sub (algebraMap E (w.1.adicCompletion E)), apply_ite (algebraMap E _), map_one, map_zero]
  have h2 := val_kMat_sub_lt h w hg
  have h3 := val_kMat_sub_lt h₀ w hf
  rw [← one_mul k, kMat_mul] at h2 h3
  have hc1 : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n) := fun x => by simp
  have i1 := val_kMat_le (P := w.1) (f := 1) (hN ▸ h₀.lat : Formalism.L2.Herm.Carries k (stdLat E n) (stdLat E n)) fun _ => Iff.rfl
  have i2 := val_kMat_le (P := w.1) (f := f) hc1 (hN ▸ hf.1 : CharValCompare.IsFr w.1 (stdLat E n) f)
  rw [← key]
  exact near_right _ i2 (near_left _ i1 (fun i j => by rw [key]; exact hg1 i j) h2) h3 i j

omit [StarRing E] in

/- English proof (translation)
Establish `e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j`. Simplify using `only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `congr 1`. Use `conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.

Rewrite using `[e]`. Use `intAt_sum _ fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `hy j`. Rewrite `h1`, the goal using `[GlobalTheory.AtTypeExists.intAt_iff, map_mul]`. Use `le_trans (mul_le_mul_left ?_ _) h1` and prove the remaining obligations.

Rewrite using `[hq]`. Establish `h2` using `hf i j`. Generalize the expression as in `P.valuation E _ = v at h2`. Distinguish the cases in `h0 : v = 0`. Rewrite using `[h0]`.

Conclude with `zero_le`. Rewrite `h2`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h2` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem intAt_sub_of_near {P : HeightOneSpectrum (𝓞 E)} {q : E} (hq : P.valuation E q = WithZero.exp (-1 : ℤ))
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ i j : Fin n, P.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    {y : Sp E n} (hy : ∀ i, IntAt P (q * y i)) (i : Fin n) : IntAt P (f y i - y i) := by
  have e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [e]
  refine intAt_sum _ fun j _ => ?_
  have h1 := hy j
  rw [GlobalTheory.AtTypeExists.intAt_iff, map_mul] at h1 ⊢
  refine le_trans (mul_le_mul_left ?_ _) h1
  rw [hq]
  have h2 := hf i j
  generalize P.valuation E _ = v at h2
  by_cases h0 : v = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h2 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => Iff.rfl, fun x hx => if_pos hx⟩`.
-/
theorem isLiftFr_base [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (w : SG) :
    IsLiftFr (DecoF.base (E := E) (n := n) (ST := ST) (SG := SG) (Q := Q)).deco.1 w 1 :=
  ⟨fun _ => Iff.rfl, fun x hx => if_pos hx⟩

omit [StarRing E] in

/- English proof (translation)
Rewrite using `[← if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl, ← Pi.single_apply j (1 : E) i]`. Break down `idx_cases hN i with ⟨i, rfl⟩ | rfl` into its components or cases. Use `congrFun (prH_sumE hN (1 : Sp E n ≃ₗ[E] Sp E n) t (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[prH_apply]`. Rewrite using `[this]`.

Use `show P.valuation E (_ - _) < 1`. Rewrite using `[LinearEquiv.coe_one, id, prH_apply, sub_self, map_zero]`. Conclude with `zero_lt_one`. Rewrite using `[sumE_last, Pi.single_apply] split_ifs`. Rewrite using `[mul_one]` and apply the resulting hypothesis.

Simplify using the standard rewrite rules.
-/
theorem sumE_near {N : ℕ} (hN : N = n + 1) {P : HeightOneSpectrum (𝓞 E)} {t : Eˣ} (ht : P.valuation E ((t : E) - 1) < 1) (i j : Fin N) :
    P.valuation E (sumE hN (1 : Sp E n ≃ₗ[E] Sp E n) t (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  rw [← if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl, ← Pi.single_apply j (1 : E) i]
  rcases idx_cases hN i with ⟨i, rfl⟩ | rfl
  · have := congrFun (prH_sumE hN (1 : Sp E n ≃ₗ[E] Sp E n) t (Pi.single j 1)) i
    rw [prH_apply] at this
    rw [this]
    show P.valuation E (_ - _) < 1
    rw [LinearEquiv.coe_one, id, prH_apply, sub_self, map_zero]
    exact zero_lt_one
  · rw [sumE_last, Pi.single_apply]
    split_ifs
    · rwa [mul_one]
    · simp

end GlobalTheory.Fam.TopFrames
end Gen

section World
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
namespace GlobalTheory.Fam.TopFrames

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]`. Consider the case `tmul x y => rfl`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]`.
-/
theorem prV_comm {D : D7} (v : GlobalTheory.FinPl.Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) : Formalism.UG.prV (E := D.host.E) v
    ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom y) =
    (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E).toAlgHom.toRingHom (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

/- English proof (translation)
Rewrite `hx` using `[GlobalTheory.FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf]`. Establish `h` using `RingHom.mem_ker.1 (hx.2 ⟨v, hv⟩)`. Use `(prV_comm v (finPart D x)).trans ?_` and prove the remaining obligations. Rewrite using `[show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D x) = 0 from h, RingHom.map_zero]`.
-/
theorem prV_eq_zero {D : D7} {Q : GlobalTheory.FinPl.Pl D → Prop} {x : AE D} (hx : x ∈ GlobalTheory.FinPl.idAt D Q) {v : GlobalTheory.FinPl.Pl D} (hv : ¬ Q v) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D x) = 0 := by
  rw [GlobalTheory.FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at hx
  have h := RingHom.mem_ker.1 (hx.2 ⟨v, hv⟩)
  refine (prV_comm v (finPart D x)).trans ?_
  rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D x) = 0 from h, RingHom.map_zero]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hn` using the available equality. Rewrite `hh` using `[GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.SetCut.mem_congGrp_iff]`. Use extensionality with `r s`. Establish `key` using `prV_eq_zero (hh r s) hv`. Establish `e1 : mt S h r s = (mt S h - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s`.

Rewrite using `[Matrix.sub_apply, sub_add_cancel]`. Simplify using `only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]`. Rewrite using `[e1, RingHom.map_add, RingHom.map_add, key, zero_add, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem finM_map_prV {D : D7} (S : HSp D) {n : ℕ} (hn : S.rank = n) {Q : GlobalTheory.FinPl.Pl D → Prop} {h : GA D S}
    (hh : h ∈ GlobalTheory.FinPl.grpAt S Q) {v : GlobalTheory.FinPl.Pl D} (hv : ¬ Q v) : (finM S hn h).map (Formalism.UG.prV (E := D.host.E) v) = 1 := by
  subst hn
  rw [GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.SetCut.mem_congGrp_iff] at hh
  ext r s
  have key := prV_eq_zero (hh r s) hv
  have e1 : mt S h r s = (mt S h - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s := by
    rw [Matrix.sub_apply, sub_add_cancel]
  simp only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [e1, RingHom.map_add, RingHom.map_add, key, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

section Tw
variable {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀}

/- English proof (translation)
Substitute `hj` using the available equality. Use `letI := GlobalTheory.Mem.Col2.starE B`. Use `haveI : NeZero (B.R.N B.R.m - 1) := ⟨by`. Establish `h1` using `B.R.two_le_m`. Establish `h2 : B.R.N B.R.m = B.R.k + B.R.m * (B.R.t + 1)` using `rfl`.

Establish `h3 : B.R.m ≤ B.R.m * (B.R.t + 1)` using `Nat.le_mul_of_pos_right _ (Nat.succ_pos _)`. Use the proof step `omega⟩`. Establish `hQ : ∀ Q : Formalism.L2.Col.QE I.sel (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K), (B.primes X).piT u ∉ Q.1.asIdeal` using `fun Q => ((TwistPrimes.twist_primes_away I hI).2 u a Q.1 Q.2).2.1`. Establish `h1` using `hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _) ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩`. Rewrite `h1` using `[one_mul]`.

Establish `e : Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 B.R.m β).1.1 P = (A.p0 B.R.m β).1.1.deco.1.liftFr ⟨P.1, hP⟩` using `dif_pos hP`. Establish `hu` using `unitOf_val (Formalism.L2.Col.piT_notMem_vGs l.pr u ⟨P.1, hP⟩)`. Rewrite using `[e]`. Use `lift_near_of_lift h1 (hA.base _ le_rfl β).1 (hA.base _ le_rfl β).2 ⟨P.1, hP⟩ (g := GlobalTheory.TopStep.sumE (Formalism.L2.Col.N_m_succ B.R) 1 (unitOf ((B.primes X).piT u))) ?_ (sumE_near _ ?_) (GlobalTheory.TopStep.liftFr_spec (A.p0 B.R.m β).1.1.deco.2 ⟨P.1, hP⟩) r c` and prove the remaining obligations. Rewrite using `[tilF_deco I.sel (I.tup a) l.pr u hQ]`.

Conclude with `GlobalTheory.TopStep.isLiftFr_tilH _ _ (Formalism.L2.Col.conj_piT_notMem l.pr u) (Formalism.L2.Col.piT_notMem_vGs l.pr u) _ (isLiftFr_base _) _ hu`. Take `⟨i, -, -, -, -, -, -, -, -, -, h⟩` from `GlobalTheory.SeeSaw.LevelData.type_prime hP`. Rewrite using `[hu]`. Establish `h2` using `(P.1.valuation_lt_one_iff_mem (K := B.fields.E) _).2 (h u)`. Establish `h3 : ((X.piT u - 1 : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).piT u : B.fields.E) - 1` using `(algebraMap (𝓞 B.fields.E) B.fields.E).map_sub _ 1`.

Conclude with `h3 ▸ h2`.
-/
theorem top_near (hI : I.Ok) (hA : A.Is) (P : BadPr I a) (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j = B.R.m) (β : Ch₀ j) (r c) :
    HeightOneSpectrum.valuation B.fields.E P.1
      (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P (Pi.single c 1) r - if r.val = c.val then 1 else 0) < 1 := by
  subst hj
  letI := GlobalTheory.Mem.Col2.starE B
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have h1 := B.R.two_le_m
    have h2 : B.R.N B.R.m = B.R.k + B.R.m * (B.R.t + 1) := rfl
    have h3 : B.R.m ≤ B.R.m * (B.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega⟩
  have hQ : ∀ Q : Formalism.L2.Col.QE I.sel (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K),
      (B.primes X).piT u ∉ Q.1.asIdeal := fun Q => ((TwistPrimes.twist_primes_away I hI).2 u a Q.1 Q.2).2.1
  have h1 := hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _)
    ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rw [one_mul] at h1
  have e : Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 B.R.m β).1.1 P = (A.p0 B.R.m β).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have hu := unitOf_val (Formalism.L2.Col.piT_notMem_vGs l.pr u ⟨P.1, hP⟩)
  rw [e]
  refine lift_near_of_lift h1 (hA.base _ le_rfl β).1 (hA.base _ le_rfl β).2 ⟨P.1, hP⟩
    (g := GlobalTheory.TopStep.sumE (Formalism.L2.Col.N_m_succ B.R) 1 (unitOf ((B.primes X).piT u))) ?_ (sumE_near _ ?_)
    (GlobalTheory.TopStep.liftFr_spec (A.p0 B.R.m β).1.1.deco.2 ⟨P.1, hP⟩) r c
  · rw [tilF_deco I.sel (I.tup a) l.pr u hQ]
    exact GlobalTheory.TopStep.isLiftFr_tilH _ _ (Formalism.L2.Col.conj_piT_notMem l.pr u) (Formalism.L2.Col.piT_notMem_vGs l.pr u) _
      (isLiftFr_base _) _ hu
  · obtain ⟨i, -, -, -, -, -, -, -, -, -, h⟩ := GlobalTheory.SeeSaw.LevelData.type_prime hP
    rw [hu]
    have h2 := (P.1.valuation_lt_one_iff_mem (K := B.fields.E) _).2 (h u)
    have h3 : ((X.piT u - 1 : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).piT u : B.fields.E) - 1 :=
      (algebraMap (𝓞 B.fields.E) B.fields.E).map_sub _ 1
    exact h3 ▸ h2

/- English proof (translation)
Establish `h0` using `(A.p0 j β).repY_mem hj`. Take `⟨y, hy, hY⟩` from `(A.p0 j β).mem_ybSet hj`. Use `set z := Formalism.L2.Col.repY (A.p0 j β).1.2 with hz`. Rewrite `h0` using `[hY]`. Establish `h1` using `(Formalism.L2.Col.mem_locLat _ _ _ _).1 hy P`.

Establish `h2` using `(Formalism.L2.Col.mem_locLat _ _ _ _).1 h0 P`. Simplify using `only [if_pos hP, zpow_zero, inv_one, one_smul, _root_.zpow_neg, inv_inv, zpow_one] at h1 h2`. Establish `h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) • z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.p0 j β).1.1.deco.1.N`. Establish `h4` using `add_mem h1 (Submodule.smul_mem _ ((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) h2)`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← algebraMap_smul B.fields.E ((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E), map_natCast, ← smul_add, add_sub_cancel]`. Rewrite `h3` using `[← (ptFr (A.p0 j β).1.1 P.1).apply_symm_apply (_ • z)]`. Establish `h5` using `(isFr_ptFr (A.p0 j β).1.1 P.1 _).1 h3`. Rewrite `h5` using `[← frsF_eq_ptFr I.sel (I.tup a), map_smul]`. Conclude with `GlobalTheory.TopStep.mem_stdAt.1 h5 i`.
-/
theorem intAt_q_mul (P : BadPr I a) (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j + 1 = B.R.m) (β : Ch₀ j) (i) :
    Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) *
      (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P).symm (Formalism.L2.Col.repY (A.p0 j β).1.2) i) := by
  have h0 := (A.p0 j β).repY_mem hj
  obtain ⟨y, hy, hY⟩ := (A.p0 j β).mem_ybSet hj
  set z := Formalism.L2.Col.repY (A.p0 j β).1.2 with hz
  rw [hY] at h0
  have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy P
  have h2 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 h0 P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul, _root_.zpow_neg, inv_inv, zpow_one] at h1 h2
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) • z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.p0 j β).1.1.deco.1.N := by
    have h4 := add_mem h1 (Submodule.smul_mem _ ((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) h2)
    convert h4 using 1
    rw [← algebraMap_smul B.fields.E ((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E), map_natCast, ← smul_add, add_sub_cancel]
  rw [← (ptFr (A.p0 j β).1.1 P.1).apply_symm_apply (_ • z)] at h3
  have h5 := (isFr_ptFr (A.p0 j β).1.1 P.1 _).1 h3
  rw [← frsF_eq_ptFr I.sel (I.tup a), map_smul] at h5
  exact GlobalTheory.TopStep.mem_stdAt.1 h5 i

end Tw

variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `letI := GlobalTheory.Mem.Col2.starE B`. Establish `hm : j ≤ B.R.m` using `by omega`. Take `⟨k₀, h, -, h1, h2, h3, -⟩` from `hJ.pen j hj β`. Establish `h4 : ¬ ∃ i, (J.G i).q.v = P.1.under (𝓞 B.host.F)`. Introduce and unpack `⟨i, hi⟩`.

Rewrite `hi` using `[(GlobalTheory.LocMod.PinEx.place_facts _ (J.G i).idem).1]`. Establish `h5` using `((TwistPrimes.twist_primes_away I hW.tr.ok).2 u (W.P.I.tup t) (J.pl i) ((hW.tq.Q t _).1 (J.mem i))).1`. Break down `(under_eq_iff B.host (J.pl i) P.1).1 hi.symm with h6 | h6` into its components or cases. Conclude with `h5.2.1 (h6 ▸ hP)`. Conclude with `h5.2.2.2.1 (h6 ▸ hP)`.

Establish `h5` using `finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 h4`. Establish `h6` using `(TrueColsTest.kStd_spec X u (B.R.N j)).2.1 (P.1.under (𝓞 B.host.F)) fun hT => Formalism.L2.Col.rls_T_notUnder l.pr u _ hT ⟨P.1, hP, rfl⟩`. Establish `hk : Formalism.UG.bc (Formalism.UG.prV (E` using `B.host.E) (P.1.under (𝓞 B.host.F))) (J.A.kb j β) = 1 := by`. Use `Units.ext ?_` and prove the remaining obligations. Establish `h7` using `(hJ.is.kA j hm β).2.1`.

Rewrite `h7` using `[h2, GlobalTheory.AdForm.Model.finM_mul, h1]`. Establish `h8 : (J.A.kb j β).1.map (Formalism.UG.prV (E` using `B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := by`. Rewrite using `[← h7]`. Use `Matrix.map_mul.trans ?_` and prove the remaining obligations. Establish `h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E` using `B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := congrArg Units.val h6`.

Conclude with `(congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (B.host.E ⊗[B.host.F] (P.1.under (𝓞 B.host.F)).adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)`. Conclude with `h8`. Establish `e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hP⟩` using `dif_pos hP`. Establish `h9` using `(hJ.is.base j hm β).1`. Rewrite using `[e]`.

Conclude with `GlobalTheory.SeeSaw.BaseFrame.lift_near_one (y := 1) (by rw [one_mul]; exact h9) (by rw [one_mul]; exact h9) h9 (hJ.is.base j hm β).2 ⟨P.1, hP⟩ hk (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hP⟩) r c`.
-/
theorem pen_near (hW : AllTrue W) {a : GeoAll W u} {t : W.P.T} {J : QJ a t} (hJ : J.Reads) (P : BadPr I (W.P.I.tup t))
    (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j + 1 = B.R.m) (β : J.Ch₀ j) (r c) :
    HeightOneSpectrum.valuation B.fields.E P.1
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P (Pi.single c 1) r - if r.val = c.val then 1 else 0) < 1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  have hm : j ≤ B.R.m := by omega
  obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj β
  have h4 : ¬ ∃ i, (J.G i).q.v = P.1.under (𝓞 B.host.F) := by
    rintro ⟨i, hi⟩
    rw [(GlobalTheory.LocMod.PinEx.place_facts _ (J.G i).idem).1] at hi
    have h5 := ((TwistPrimes.twist_primes_away I hW.tr.ok).2 u (W.P.I.tup t) (J.pl i) ((hW.tq.Q t _).1 (J.mem i))).1
    rcases (under_eq_iff B.host (J.pl i) P.1).1 hi.symm with h6 | h6
    · exact h5.2.1 (h6 ▸ hP)
    · exact h5.2.2.2.1 (h6 ▸ hP)
  have h5 := finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 h4
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 (P.1.under (𝓞 B.host.F))
    fun hT => Formalism.L2.Col.rls_T_notUnder l.pr u _ hT ⟨P.1, hP, rfl⟩
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (J.A.kb j β) = 1 := by
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm β).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j β).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] (P.1.under (𝓞 B.host.F)).adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have h9 := (hJ.is.base j hm β).1
  rw [e]
  exact GlobalTheory.SeeSaw.BaseFrame.lift_near_one (y := 1) (by rw [one_mul]; exact h9) (by rw [one_mul]; exact h9) h9 (hJ.is.base j hm β).2
    ⟨P.1, hP⟩ hk (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hP⟩) r c

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `letI := a.fld`. Use `letI := a.val`. Use `letI := a.top`. Use `letI := a.loc`. Establish `hA' : ∀ j (h : j = (I.rec7 l Z).R.m) r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0`.

Introduce and unpack `_ rfl`. Conclude with `hA`. Establish `hB' : ∀ j (h : j = (I.rec7 l Z).R.m) r, ((a.g.oT j h).iB *ᵥ a.o.ζ₀) r = if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0`. Introduce and unpack `_ rfl r`. Conclude with `hTr.z0 r`.

Take `⟨-, ⟨e, he, hT⟩, hz⟩` from `hIs.stdG n`. Rewrite using `[(a.G n).last]`. Use `⟨fun c => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[fromCols_apply_inl, hT, Matrix.mul_apply, Finset.sum_eq_single (e c)]`. Rewrite using `[Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, ← he c]`.

Use `(congrArg (TopLoc.emb a n) (hA' _ _ r (e c))).trans ?_` and prove the remaining obligations. Use `split_ifs`. Use `exacts [map_one _, map_zero _]`. Introduce `b _ hb`. Rewrite using `[Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]`.

Conclude with `fun h => absurd (Finset.mem_univ _) h`. Rewrite using `[fromCols_apply_inr, hz]`. Use `Eq.trans ?_ (congrArg (TopLoc.emb a n) (hB' _ (a.G n).hs r))` and prove the remaining obligations. Use `Eq.trans ?_ (map_sum (TopLoc.emb a n) (fun b => (a.g.oT _ (a.G n).hs).iB r b * a.o.ζ₀ b) Finset.univ).symm` and prove the remaining obligations. Use `show ∑ b, TopLoc.emb a n ((a.g.oT _ (a.G n).hs).iB r b) * TopLoc.emb a n (a.o.ζ₀ b) = _`.

Conclude with `Finset.sum_congr rfl fun b _ => (map_mul (TopLoc.emb a n) _ _).symm`.
-/
theorem fm_eq {a : GeoAll W u} (hIs : a.Is) (hTr : a.True) (hA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0)
    (n : Fin a.n) (r) : (∀ c, (a.G n).FM.β r (Sum.inl c) = if r.val = GlobalTheory.SymBridge.zPos c then 1 else 0) ∧
      (a.G n).FM.β r (Sum.inr ()) = TopLoc.emb a n (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) := by
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have hA' : ∀ j (h : j = (I.rec7 l Z).R.m) r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0 := by
    rintro _ rfl
    exact hA
  have hB' : ∀ j (h : j = (I.rec7 l Z).R.m) r, ((a.g.oT j h).iB *ᵥ a.o.ζ₀) r =
      if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    rintro _ rfl r
    exact hTr.z0 r
  obtain ⟨-, ⟨e, he, hT⟩, hz⟩ := hIs.stdG n
  rw [(a.G n).last]
  refine ⟨fun c => ?_, ?_⟩
  · rw [fromCols_apply_inl, hT, Matrix.mul_apply, Finset.sum_eq_single (e c)]
    · rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, ← he c]
      refine (congrArg (TopLoc.emb a n) (hA' _ _ r (e c))).trans ?_
      split_ifs
      exacts [map_one _, map_zero _]
    · intro b _ hb
      rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [fromCols_apply_inr, hz]
    refine Eq.trans ?_ (congrArg (TopLoc.emb a n) (hB' _ (a.G n).hs r))
    refine Eq.trans ?_ (map_sum (TopLoc.emb a n) (fun b => (a.g.oT _ (a.G n).hs).iB r b * a.o.ζ₀ b) Finset.univ).symm
    show ∑ b, TopLoc.emb a n ((a.g.oT _ (a.G n).hs).iB r b) * TopLoc.emb a n (a.o.ζ₀ b) = _
    exact Finset.sum_congr rfl fun b _ => (map_mul (TopLoc.emb a n) _ _).symm

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hA n t J hJ α γ P hP C hC hj z`. Establish `hint : ∀ x : B.fields.E, TopLoc.emb a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt P.1 x`. Establish `hR` using `(hIs.tie (fun t => (TopLocFac.nonempty_rowCh (pk W) (lvP W) u a.g hTr.pinX.std t).some) fun t => (TopLocFac.nonempty_colCh _ _).some).2`. Rewrite using `[hP]`. Conclude with `(GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1`.

Establish `hs : (a.G n).s + 1 + 1 = B.R.m` using `(a.G n).hs`. Establish `hm : (a.G n).s + 1 ≤ B.R.m` using `Nat.le_of_succ_le hj`. Establish `hPv : P.1 ∈ (B.primes X).vGs` using `hP ▸ (hW.lev.2.1 _).1 (a.pl n).2`. Establish `hlt` using `GlobalTheory.SeeSaw.LevelData.val_lt_one_iff hint`. Take `⟨e', he'⟩` from `exists_xOrd B.R ((a.G n).s + 1)`.

Take `⟨e, he⟩` from `exists_topOrd B.R (a.G n).s hs`. Establish `hF` using `pen_near hW hJ P hPv hs (J.ι _ α)`. Establish `hF'` using `top_near hW.tr.ok hJ.is P hPv hs (J.ι _ γ)`. Establish `hq` using `intAt_q_mul (A := J.A) P hPv hs (J.ι _ α)`. Establish `hco` using `hJ.cosG n α e' he'`.

Establish `hx : locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (homOf I l Z ((a.G n).s + 1) hj z) = GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I …`. Unfold `locXi`. Rewrite using `[dif_neg (by omega), dif_neg (by omega), dif_pos hs]`. Both sides reduce to the same expression. Rewrite using `[hx]`.

Use `clear hx`. Generalize the expression as in `Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P = f at hF hq ⊢`. Generalize the expression as in `Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P = f' at hF' ⊢`. Generalize the expression as in `Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢`. Take `⟨-, -, -, -, -, -, -, -, -, -, g10⟩` from `id (GlobalTheory.SeeSaw.LevelData.type_prime hPv)`.

Establish `hqv : HeightOneSpectrum.valuation B.fields.E P.1 (Formalism.L2.Col.qOf P.1 : B.fields.E) = WithZero.exp (-1 : ℤ)`. Take `⟨i, g1, -, -, g4, -⟩` from `GlobalTheory.SeeSaw.LevelData.type_prime hPv`. Conclude with `GlobalTheory.AtTypeExists.valuation_norm P.1 (g1 ▸ g4)`. Establish `hy : (Submodule.Quotient.mk ((a.G n).S.y0 (Fin B.R.t)) : _ ⧸ box _ (1 : (a.G n).kˣ)) = Submodule.Quotient.mk fun r => TopLoc.emb a n (f.symm y (e' r))`. Use `GlobalTheory.SeeSaw.StdMatch.mk_eq_mk_of_int fun c => ?_` and prove the remaining obligations.

Establish `h1` using `(hint _).2 (intAt_sub_of_near hqv hF hq (e' c))`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply, map_sub]`. Establish `h2 : TopLoc.emb a n (y (e' c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k]` using `hco c`. Establish `h3` using `sub_mem h2 h1`. Rewrite `h3` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis.

Use `Eq.trans ?_ (hC e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r) _ _ hq)` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (fun w => ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) w _) hy)` and prove the remaining obligations. Establish `e1` using `GlobalTheory.SeeSaw.StdMatch.mul_toLoc (TopLoc.emb a n) (rankN (I.rec7 l Z) _ hm) (rankN (I.rec7 l Z) _ hj) f f' e' e (Matrix.of fun r c => TopLoc.emb a n (f (Pi.single (e' c) 1) (finCongr (rankN (I.rec7 l Z) _ hm) r))) (Matrix.of fun r c => TopLoc.emb a n (f' (Pi.single (e c) 1) …`. Use `xiTop_frames (a.G n).unitVol (a.G n).S (Fin B.R.t) ((a.G n).FX _ le_rfl) (a.G n).FM (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hm).2.2) ((a.G n).latX _ le_rfl)) (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hj).2.2) ( …` and prove the remaining obligations. Take `⟨e₁, h1, h2⟩` from `(hIs.stdG n).1 ((a.G n).s + 1) le_rfl`.

Establish `h3` using `(hlt _).2 (hF (finCongr (rankN (I.rec7 l Z) _ hm) r) (e' c))`. Rewrite `h3` using `[map_sub, apply_ite (TopLoc.emb a n), map_one, map_zero, (he' c).trans (h1 c).symm]`. Establish `h4 : ((a.G n).FX ((a.G n).s + 1) le_rfl).β r c = if r.val = (e₁ c).val then 1 else 0` using `(congrFun (congrFun h2 r) c).trans (Matrix.one_apply.trans (if_congr Fin.ext_iff rfl rfl))`. Conclude with `(congrArg (fun w => valuation (a.G n).k (_ - w)) h4).trans_lt h3`. Establish `h3` using `(hlt _).2 (hF' (finCongr (rankN (I.rec7 l Z) _ hj) r) (e c))`.

Rewrite `h3` using `[map_sub, apply_ite (TopLoc.emb a n), map_one, map_zero, he c]`. Take `⟨h1, h2⟩` from `fm_eq hIs hTr hA n r`. Use `show valuation (a.G n).k (_ - (a.G n).FM.β r c) < 1`. Break down `c with c | c` into its components or cases. Conclude with `(congrArg (fun w => valuation (a.G n).k (_ - w)) (h1 c)).trans_lt h3`.

Use `(congrArg (fun w => valuation (a.G n).k (_ - w)) h2).trans_lt ?_` and prove the remaining obligations. Establish `h4` using `(hlt ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E)).2 ((P.1.valuation_lt_one_iff_mem _).2 (g10 u))`. Establish `h5 : TopLoc.emb a n ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E) = TopLoc.emb a n ((X.piT u : 𝓞 B.host.E) : B.host.E) - 1` using `((TopLoc.emb a n).map_sub ((X.piT u : 𝓞 B.host.E) : B.host.E) 1).trans (congrArg _ (TopLoc.emb a n).map_one)`. Rewrite `h4` using `[h5]`. Use `replace h3 : valuation (a.G n).k (TopLoc.emb a n (f' (Pi.single (e (Sum.inr c)) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)) - if (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 then 1 else 0) < 1 := h3`.

Establish `h6 : 0 < B.R.N B.R.m`. Use `(e (Sum.inr c)).2` as an intermediate fact. Rewrite using `[← hs]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hr : r.val + 1 = B.R.N B.R.m`.

Rewrite `h3` using `[if_pos (show (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from Nat.eq_sub_of_add_eq hr)]`. Rewrite using `[if_pos hr]`. Establish `h7` using `Valuation.map_sub_lt _ h3 h4`. Rewrite `h7` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[if_neg (show ¬ (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from fun h => hr (by`.

Establish `h8 : r.val = B.R.N B.R.m - 1` using `h`. Use the proof step `omega))] at h3`. Rewrite using `[if_neg hr, map_zero]`. Conclude with `h3`.
-/
theorem xiStd_eq_const_mul_locXi : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (t : W.P.T) (J : QJ a t), J.Reads → ∀ (α : J.Ch ((a.G n).s + 1)) (γ : J.Ch ((a.G n).s + 1 + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ C : ℂ,
  (∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
     GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
     ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => GlobalTheory.Fam.TopLoc.emb a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y')) →
  ∀ (hj : (a.G n).s + 1 + 1 ≤ B.R.m) z, GlobalTheory.Fam.TopLoc.xiStd a n z =
    C * B.embLL (GlobalTheory.QTw.locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (GlobalTheory.QTw.homOf I l Z ((a.G n).s + 1) hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hA n t J hJ α γ P hP C hC hj z
  have hint : ∀ x : B.fields.E, TopLoc.emb a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt P.1 x := by
    have hR := (hIs.tie (fun t => (TopLocFac.nonempty_rowCh (pk W) (lvP W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hm : (a.G n).s + 1 ≤ B.R.m := Nat.le_of_succ_le hj
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  have hlt := GlobalTheory.SeeSaw.LevelData.val_lt_one_iff hint
  obtain ⟨e', he'⟩ := exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨e, he⟩ := exists_topOrd B.R (a.G n).s hs
  have hF := pen_near hW hJ P hPv hs (J.ι _ α)
  have hF' := top_near hW.tr.ok hJ.is P hPv hs (J.ι _ γ)
  have hq := intAt_q_mul (A := J.A) P hPv hs (J.ι _ α)
  have hco := hJ.cosG n α e' he'
  have hx : locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (homOf I l Z ((a.G n).s + 1) hj z) =
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P
        (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P) (homOf I l Z ((a.G n).s + 1) hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2)) := by
    unfold locXi
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos hs]
    rfl
  rw [hx]
  clear hx
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P = f at hF hq ⊢
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P = f' at hF' ⊢
  generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g10⟩ := id (GlobalTheory.SeeSaw.LevelData.type_prime hPv)
  have hqv : HeightOneSpectrum.valuation B.fields.E P.1 (Formalism.L2.Col.qOf P.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime hPv
    exact GlobalTheory.AtTypeExists.valuation_norm P.1 (g1 ▸ g4)
  have hy : (Submodule.Quotient.mk ((a.G n).S.y0 (Fin B.R.t)) : _ ⧸ box _ (1 : (a.G n).kˣ)) =
      Submodule.Quotient.mk fun r => TopLoc.emb a n (f.symm y (e' r)) := by
    refine GlobalTheory.SeeSaw.StdMatch.mk_eq_mk_of_int fun c => ?_
    have h1 := (hint _).2 (intAt_sub_of_near hqv hF hq (e' c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : TopLoc.emb a n (y (e' c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco c
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  refine Eq.trans ?_ (hC e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r) _ _ hq)
  refine Eq.trans ?_ (congrArg (fun w => ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) w _) hy)
  have e1 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (TopLoc.emb a n) (rankN (I.rec7 l Z) _ hm) (rankN (I.rec7 l Z) _ hj) f f' e' e
    (Matrix.of fun r c => TopLoc.emb a n (f (Pi.single (e' c) 1) (finCongr (rankN (I.rec7 l Z) _ hm) r)))
    (Matrix.of fun r c => TopLoc.emb a n (f' (Pi.single (e c) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)))
    (fun _ _ => rfl) (fun _ _ => rfl) z
  refine xiTop_frames (a.G n).unitVol (a.G n).S (Fin B.R.t) ((a.G n).FX _ le_rfl) (a.G n).FM
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hm).2.2) ((a.G n).latX _ le_rfl))
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hj).2.2) (a.G n).latM) (fun r c => ?_) (fun r c => ?_) _ e1
  · obtain ⟨e₁, h1, h2⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
    have h3 := (hlt _).2 (hF (finCongr (rankN (I.rec7 l Z) _ hm) r) (e' c))
    rw [map_sub, apply_ite (TopLoc.emb a n), map_one, map_zero, (he' c).trans (h1 c).symm] at h3
    have h4 : ((a.G n).FX ((a.G n).s + 1) le_rfl).β r c = if r.val = (e₁ c).val then 1 else 0 :=
      (congrFun (congrFun h2 r) c).trans (Matrix.one_apply.trans (if_congr Fin.ext_iff rfl rfl))
    exact (congrArg (fun w => valuation (a.G n).k (_ - w)) h4).trans_lt h3
  · have h3 := (hlt _).2 (hF' (finCongr (rankN (I.rec7 l Z) _ hj) r) (e c))
    rw [map_sub, apply_ite (TopLoc.emb a n), map_one, map_zero, he c] at h3
    obtain ⟨h1, h2⟩ := fm_eq hIs hTr hA n r
    show valuation (a.G n).k (_ - (a.G n).FM.β r c) < 1
    rcases c with c | c
    · exact (congrArg (fun w => valuation (a.G n).k (_ - w)) (h1 c)).trans_lt h3
    · refine (congrArg (fun w => valuation (a.G n).k (_ - w)) h2).trans_lt ?_
      have h4 := (hlt ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E)).2 ((P.1.valuation_lt_one_iff_mem _).2 (g10 u))
      have h5 : TopLoc.emb a n ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E) = TopLoc.emb a n ((X.piT u : 𝓞 B.host.E) : B.host.E) - 1 :=
        ((TopLoc.emb a n).map_sub ((X.piT u : 𝓞 B.host.E) : B.host.E) 1).trans (congrArg _ (TopLoc.emb a n).map_one)
      rw [h5] at h4
      replace h3 : valuation (a.G n).k (TopLoc.emb a n (f' (Pi.single (e (Sum.inr c)) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)) -
          if (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 then 1 else 0) < 1 := h3
      have h6 : 0 < B.R.N B.R.m := by
        have := (e (Sum.inr c)).2
        rw [← hs]
        omega
      by_cases hr : r.val + 1 = B.R.N B.R.m
      · rw [if_pos (show (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from Nat.eq_sub_of_add_eq hr)] at h3
        rw [if_pos hr]
        have h7 := Valuation.map_sub_lt _ h3 h4
        rwa [sub_sub_sub_cancel_right] at h7
      · rw [if_neg (show ¬ (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from fun h => hr (by
          have h8 : r.val = B.R.N B.R.m - 1 := h
          omega))] at h3
        rw [if_neg hr, map_zero]
        exact h3

end GlobalTheory.Fam.TopFrames
end World
end
