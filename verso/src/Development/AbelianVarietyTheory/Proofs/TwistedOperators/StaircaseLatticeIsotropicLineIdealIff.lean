import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairLine

variable {D : D7}

open GlobalTheory.SeeSaw

/- English proof (translation)
Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, hαv, b, hb, rfl⟩` from `hy`. Rewrite using `[GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]`. Conclude with `GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x) hb)`.

Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `add_mem hy hz`. Consider the case `neg y _ hy => rw [mul_neg]`.

Conclude with `neg_mem hy`.
-/
theorem incA_mul_mem_idV {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
    rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
    exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv
      (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x) hb)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `incA_mul_mem_idV x h` as an intermediate fact. Rewrite `this` using `[← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx, FractionalIdeal.spanSingleton_one, one_mul]`. Then use the resulting hypothesis. Introduce `h`.

Use `incA_mul_mem_idV x⁻¹ h` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_idV_inv_mul {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : D.host.E} (hx : x ≠ 0) (s : AE D) :
    s ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟) v ↔ incA D x * s ∈ idV 𝔟 v := by
  constructor
  · intro h
    have := incA_mul_mem_idV x h
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at this
  · intro h
    have := incA_mul_mem_idV x⁻¹ h
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e` using `d.gram`. Express the relevant statement in the definitionally equal form `d.aᴴ * B.gram * d.a = _ at e`. Rewrite using `[e]`. Use function extensionality and compare the values at `q`.

Simplify using `only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, Pi.single_apply, Fin.ext_iff]`. Use `p.2` as an intermediate fact. Use `q.2` as an intermediate fact. Distinguish the cases in `hq : q.1 = p.1`. Rewrite using `[if_pos (by omega), if_neg (by omega), if_pos hq]`.

Rewrite using `[if_neg (by omega), if_neg hq]`. Establish `e` using `d.perp`. Express the relevant statement in the definitionally equal form `(frameMat B A d.ι)ᴴ * B.gram * d.a = 0 at e`. Establish `hg : B.gramᴴ = B.gram` using `Matrix.ext fun i j => B.herm.eq (B.frame j) (B.frame i)`. Use `congrArg Matrix.conjTranspose e` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hg, Matrix.conjTranspose_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.
-/
theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) :
    (d.aᴴ * B.gram * d.a) ⟨c - 1 - p.1, by omega⟩ = Pi.single p 1 ∧
      (d.aᴴ * B.gram * frameMat B A d.ι) = 0 := by
  refine ⟨?_, ?_⟩
  · have e := d.gram
    change d.aᴴ * B.gram * d.a = _ at e
    rw [e]
    funext q
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, Pi.single_apply, Fin.ext_iff]
    have := p.2; have := q.2
    by_cases hq : q.1 = p.1
    · rw [if_pos (by omega), if_neg (by omega), if_pos hq]
    · rw [if_neg (by omega), if_neg hq]
  · have e := d.perp
    change (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 at e
    have hg : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq (B.frame j) (B.frame i)
    have := congrArg Matrix.conjTranspose e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hg,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this

/- English proof (translation)
Take `⟨hf1, hf2⟩` from `hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero d p hp`. Generalize the expression as in `(⟨c - 1 - p.1, by omega⟩ : Fin c) = q at hf1`. Take `⟨φ, hφ⟩ : ∃ φ : Fin B.rank → D.host.E, φ = (d.aᴴ * B.gram) q` from `⟨_, rfl⟩`. Establish `hφa : ∀ u : Fin c → D.host.E, φ ⬝ᵥ (d.a *ᵥ u) = u p`. Introduce `u`.

Rewrite using `[Matrix.dotProduct_mulVec, hφ]`. Establish `: (d.aᴴ * B.gram) q ᵥ* d.a = (d.aᴴ * B.gram * d.a) q` using `rfl`. Rewrite using `[this, hf1]`. Simplify using `[Pi.single_apply, dotProduct]`. Establish `hφM : ∀ y, φ ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0`.

Introduce `y`. Rewrite using `[Matrix.dotProduct_mulVec, hφ]`. Establish `: (d.aᴴ * B.gram) q ᵥ* frameMat B A d.ι = (d.aᴴ * B.gram * frameMat B A d.ι) q` using `rfl`. Rewrite using `[this, hf2]`. Conclude with `zero_dotProduct y`.

Establish `h3 : ∑ l, φ l * d.a l p = 1`. Use `congrFun hf1 p` as an intermediate fact. Rewrite `this` using `[Pi.single_eq_same, Matrix.mul_apply]`. Rewrite using `[hφ]`. Conclude with `this`.

Set `Φ : (Fin B.rank → AE D) →+ AE D` to `{ toFun := fun z => ∑ l, incA D (φ l) * z l map_zero' := by simp map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hle : latV B (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔟 p) v).comap Φ`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨α, hα, hαv, a', ha', x, hx, rfl⟩`. Rewrite `ha'` using `[Set.mem_singleton_iff]`. Substitute `ha'` using the available equality. Take `⟨y, -, u, hu, rfl⟩` from `hx`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap]`.

Use `show ∑ l, incA D (φ l) * _ ∈ _`. Simplify using `only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]`. Rewrite using `[← TensorProduct.tmul_sum]`. Establish `: ∑ l, φ l * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) l = u p`. Establish `h1` using `hφa u`.

Establish `h2` using `hφM y`. Rewrite using `[← h1, ← add_zero (φ ⬝ᵥ (d.a *ᵥ u)), ← h2, ← dotProduct_add, add_comm]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (hu p)`.

Establish `h2 : Φ (fun k => t * incA D (d.a k p)) ∈ idV (𝔟 p) v` using `hle h`. Establish `e : Φ (fun k => t * incA D (d.a k p)) = t` using `by show ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, mul_left_comm]`. Use `_ = t := by rw [h3, map_one, mul_one]`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Introduce `h`. Proceed by induction on `h using AddSubgroup.closure_induction with`.

Consider the case `mem s hs`. Take `⟨α, hα, hαv, b, hb, rfl⟩` from `hs`. Use `AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, d.a *ᵥ Pi.single p b, ⟨0, Λ.zero_mem, Pi.single p b, fun r => ?_, by simp⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hr : r = p`. Substitute `hr` using the available equality.

Simplify using `using hb`. Rewrite using `[Pi.single_eq_of_ne hr]`. Conclude with `(𝔟 r).zero_mem`. Use function extensionality and compare the values at `k`. Rewrite using `[mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]`.

Use `congr 1`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Consider the case `zero`. Use `(latV B (d.lat Λ 𝔟) (· = v)).zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[add_mul]`.

Consider the case `neg x _ hx`. Use `neg_mem hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[neg_mul]`.
-/
theorem line_mem {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FI D) (v : GlobalTheory.FinPl.Pl D) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔟 p) v := by
  classical
  obtain ⟨hf1, hf2⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero d p hp
  generalize (⟨c - 1 - p.1, by omega⟩ : Fin c) = q at hf1
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin B.rank → D.host.E, φ = (d.aᴴ * B.gram) q := ⟨_, rfl⟩
  have hφa : ∀ u : Fin c → D.host.E, φ ⬝ᵥ (d.a *ᵥ u) = u p := by
    intro u
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* d.a = (d.aᴴ * B.gram * d.a) q := rfl
    rw [this, hf1]
    simp [Pi.single_apply, dotProduct]
  have hφM : ∀ y, φ ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* frameMat B A d.ι = (d.aᴴ * B.gram * frameMat B A d.ι) q := rfl
    rw [this, hf2]
    exact zero_dotProduct y
  have h3 : ∑ l, φ l * d.a l p = 1 := by
    have := congrFun hf1 p
    rw [Pi.single_eq_same, Matrix.mul_apply] at this
    rw [hφ]; exact this
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun z => ∑ l, incA D (φ l) * z l
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  constructor
  · intro h
    have hle : latV B (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔟 p) v).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, hαv, a', ha', x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show ∑ l, incA D (φ l) * _ ∈ _
      simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum]
      have : ∑ l, φ l * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) l = u p := by
        have h1 := hφa u
        have h2 := hφM y
        rw [← h1, ← add_zero (φ ⬝ᵥ (d.a *ᵥ u)), ← h2, ← dotProduct_add, add_comm]
        rfl
      rw [this]
      exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (hu p)
    have h2 : Φ (fun k => t * incA D (d.a k p)) ∈ idV (𝔟 p) v := hle h
    have e : Φ (fun k => t * incA D (d.a k p)) = t := by
      show ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t
      calc ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t * incA D (∑ l, φ l * d.a l p) := by
            rw [map_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_mul, mul_left_comm]
        _ = t := by rw [h3, map_one, mul_one]
    rwa [e] at h2
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hs
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, d.a *ᵥ Pi.single p b,
        ⟨0, Λ.zero_mem, Pi.single p b, fun r => ?_, by simp⟩, ?_⟩
      · by_cases hr : r = p
        · subst hr; simpa using hb
        · rw [Pi.single_eq_of_ne hr]; exact (𝔟 r).zero_mem
      · funext k
        rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero =>
      convert (latV B (d.lat Λ 𝔟) (· = v)).zero_mem using 1
      funext k; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext k; simp [add_mul]
    | neg x _ hx =>
      convert neg_mem hx using 1
      funext k; simp [neg_mul]

open GlobalTheory.ChiGrid in

/- English proof (translation)
Introduce `D hoff T L μ0 hL sc G W M hM F hF ρ h v i a ha`. Take `⟨hc, he, -⟩` from `hF.hJ ρ h`. Establish `hx : ((-D.host.xi0) ^ (i.1 + 1)) ≠ 0` using `pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)`. Establish `e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a = fun k => (incA D ((-D.host.xi0) ^ (i.1 + 1)) * a) * incA D ((G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) i))`. Use function extensionality and compare the values at `k`.

Use `show a * incA D ((F.dJ ρ h).e k i) = _`. Rewrite using `[he]`. Use `show a * incA D ((-D.host.xi0) ^ (i.1 + 1) * _) = _`. Rewrite using `[map_mul, ← mul_assoc, mul_comm a]`. Establish `e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1))` using `G.sp.colLat _ _ _`.

Establish `hi` using `i.2`. Rewrite using `[e1, e2, line_mem _ _ _ v _ (by simp only [Fin.val_castLE]; omega), mem_idV_inv_mul hx]`. Simplify using `only [stairId, Fin.val_castLE, Nat.add_sub_cancel]`.
-/
theorem colMul_dJ_mem_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hx : ((-D.host.xi0) ^ (i.1 + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a = fun k => (incA D ((-D.host.xi0) ^ (i.1 + 1)) * a) *
      incA D ((G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) i)) := by
    funext k
    show a * incA D ((F.dJ ρ h).e k i) = _
    rw [he]
    show a * incA D ((-D.host.xi0) ^ (i.1 + 1) * _) = _
    rw [map_mul, ← mul_assoc, mul_comm a]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat _ _ _
  have hi := i.2
  rw [e1, e2, line_mem _ _ _ v _ (by simp only [Fin.val_castLE]; omega), mem_idV_inv_mul hx]
  simp only [stairId, Fin.val_castLE, Nat.add_sub_cancel]

end GlobalTheory.StairLine
