import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDenNotMemOfCountEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatHalfInt

variable {D : D7}

/- English proof (translation)
Establish `key : ∀ y ∈ intAE D, (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`.

Rewrite using `[Algebra.TensorProduct.comm_tmul]`. Conclude with `GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`. Conclude with `key _ hw`.
-/
theorem toEAf_mem_of_finPart {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ y ∈ intAE D,
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      rw [Algebra.TensorProduct.comm_tmul]
      exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨β, hβ, o', rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨β, hβ, o' * o, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.

Both sides reduce to the same expression. Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [neg_mul]`. Conclude with `neg_mem hx`.
-/
theorem mul_int_mem {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) (o : 𝓞 D.host.E) :
    w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o', rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β, hβ, o' * o, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

/- English proof (translation)
Take `⟨b, c, hc, hbc⟩` from `GlobalTheory.exists_den_not_mem_of_count_eq_zero P D.host.AA hP ha`. Establish `hc0 : c ≠ 0` using `fun h => hc (h ▸ zero_mem _)`. Establish `h1 : finPart D (e * incA D ((c : D.host.E))⁻¹) ∈ intAE D`. Assume the negation of the conclusion as `h`. Conclude with `hc ((he.2 c hc0).2 h)`.

Establish `hc' : (c : D.host.E) ≠ 0` using `by exact_mod_cast hc0`. Establish `e0 : a = ((c : D.host.E))⁻¹ * (b : D.host.E)`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ hc']`. Conclude with `hbc`. Establish `e1 : e * incA D a = e * incA D ((c : D.host.E))⁻¹ * incA D (b : D.host.E)`.

Rewrite using `[mul_assoc, ← map_mul, ← e0]`. Rewrite using `[e1, RingHom.map_mul]`. Conclude with `mul_int_mem h1 b`.
-/
theorem idemAt_mul_mem {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P)
    (hP : FractionalIdeal.count D.host.E P D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    finPart D (e * incA D a) ∈ intAE D := by
  obtain ⟨b, c, hc, hbc⟩ := GlobalTheory.exists_den_not_mem_of_count_eq_zero P D.host.AA hP ha
  have hc0 : c ≠ 0 := fun h => hc (h ▸ zero_mem _)
  have h1 : finPart D (e * incA D ((c : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact hc ((he.2 c hc0).2 h)
  have hc' : (c : D.host.E) ≠ 0 := by exact_mod_cast hc0
  have e0 : a = ((c : D.host.E))⁻¹ * (b : D.host.E) := by
    rw [eq_inv_mul_iff_mul_eq₀ hc']
    exact hbc
  have e1 : e * incA D a = e * incA D ((c : D.host.E))⁻¹ * incA D (b : D.host.E) := by
    rw [mul_assoc, ← map_mul, ← e0]
  rw [e1, RingHom.map_mul]
  exact mul_int_mem h1 b

/- English proof (translation)
Establish `e1 : toEAf D (idem R) * eToEAf D a = toEAf D (idem R * incA D a)` using `by rw [RingHom.map_mul]; rfl`. Rewrite using `[e1]`. Apply `toEAf_mem_of_finPart` to reduce the goal to its premises. Unfold `idem`. Rewrite using `[Finset.sum_mul, map_sum]`.

Use `sum_mem fun PP hPP => ?_` and prove the remaining obligations. Take `⟨P, -, hRP, e, ⟨es, hes, -⟩, -⟩` from `hR.split`. Establish `hex : ∃ e, Formalism.L2.NTheta.IsIdemAt e PP` using `⟨es PP, hes PP (hRP hPP)⟩`. Establish `hat : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP` using `Classical.epsilon_spec hex`. Conclude with `idemAt_mul_mem hat (hR.prime PP (Or.inr hPP) PP (Or.inl rfl)) ha`.
-/
theorem idem_mul_mem {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R) {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (idem R) * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have e1 : toEAf D (idem R) * eToEAf D a = toEAf D (idem R * incA D a) := by rw [RingHom.map_mul]; rfl
  rw [e1]
  apply toEAf_mem_of_finPart
  unfold idem
  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  obtain ⟨P, -, hRP, e, ⟨es, hes, -⟩, -⟩ := hR.split
  have hex : ∃ e, Formalism.L2.NTheta.IsIdemAt e PP := ⟨es PP, hes PP (hRP hPP)⟩
  have hat : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := Classical.epsilon_spec hex
  exact idemAt_mul_mem hat (hR.prime PP (Or.inr hPP) PP (Or.inl rfl)) ha

end GlobalTheory.LatHalfInt

namespace GlobalTheory.LatHalfInt

variable {D : D7}

/- English proof (translation)
Use `set v : Fin S.rank → EAf D := fun j => eToEAf D (∑ i, star (s i) * S.gram i j) with hv`. Establish `key : ∀ y ∈ Formalism.L2.Herm.hatL Λ, ∑ j, v j * y j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨l, hl, rfl⟩` from `hy`. Take `⟨b, hb⟩` from `(hS.2 l).1 hl s hs`. Establish `e1 : ∑ j, v j * Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F) (l j) = eToEAf D (b : D.host.E)`. Rewrite using `[hb, map_sum]`. Simplify using `only [hv, map_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `eToEAf D _ * eToEAf D _ = _`. Rewrite using `[← map_mul]`. Rewrite using `[e1]`.

Conclude with `GlobalTheory.PlaceDatum.tmul_mem_int ⟨b, rfl⟩ (one_mem _)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Conclude with `add_mem hx hy`.

Consider the case `smul r x _ hx`. Establish `e2 : ∑ j, v j * (r • x) j = (r : EAf D) * ∑ j, v j * x j`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `mul_mem r.2 hx`. Establish `hcol : (fun j => β.val j k) ∈ Formalism.L2.Herm.hatL Λ`. Use `(hβ _).2 fun i => ?_` and prove the remaining obligations.

Establish `e3 : ((β⁻¹).val *ᵥ fun j => β.val j k) i = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i k`. Rewrite using `[← Units.inv_mul β]`. Simplify using `[Matrix.mulVec, Matrix.mul_apply, dotProduct]`. Rewrite using `[e3, Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `key _ hcol` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct]`.
-/
theorem row_frame_mem {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hS : IsSelfDualC S Λ)
    {β : GL (Fin S.rank) (EAf D)} (hβ : IsFrame β Λ) {s : Fin S.rank → D.host.E} (hs : s ∈ Λ) (k : Fin S.rank) :
    ((fun j => eToEAf D (∑ i, star (s i) * S.gram i j)) ᵥ* β.val) k ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set v : Fin S.rank → EAf D := fun j => eToEAf D (∑ i, star (s i) * S.gram i j) with hv
  have key : ∀ y ∈ Formalism.L2.Herm.hatL Λ, ∑ j, v j * y j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨b, hb⟩ := (hS.2 l).1 hl s hs
      have e1 : ∑ j, v j * Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F) (l j) = eToEAf D (b : D.host.E) := by
        rw [hb, map_sum]
        simp only [hv, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        change eToEAf D _ * eToEAf D _ = _
        rw [← map_mul]
      rw [e1]
      exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨b, rfl⟩ (one_mem _)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul r x _ hx =>
      have e2 : ∑ j, v j * (r • x) j = (r : EAf D) * ∑ j, v j * x j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
        ring
      rw [e2]
      exact mul_mem r.2 hx
  have hcol : (fun j => β.val j k) ∈ Formalism.L2.Herm.hatL Λ := by
    refine (hβ _).2 fun i => ?_
    have e3 : ((β⁻¹).val *ᵥ fun j => β.val j k) i = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i k := by
      rw [← Units.inv_mul β]
      simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [e3, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have := key _ hcol
  simpa [Matrix.vecMul, dotProduct] using this

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem sandwich_apply {R : Type} [CommRing R] {m n p q : Type} [Fintype n] [Fintype p] (A : Matrix m n R)
    (B : Matrix p q R) (z : R) (u : n → R) (v : p → R) (i : m) (j : q) :
    (A * Matrix.of (fun a b => z * u a * v b) * B) i j = z * (A *ᵥ u) i * (v ᵥ* B) j := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.LatHalfInt

namespace GlobalTheory.LatHalfInt

variable {D : D7}

/- English proof (translation)
The claim follows from `(GlobalTheory.AdelicLatMove.toEAf_cA (incA D x)).symm`.
-/
theorem cF_eToEAf (x : D.host.E) : GlobalTheory.AdelicLatMove.cF D (eToEAf D x) = eToEAf D (star x) :=
  (GlobalTheory.AdelicLatMove.toEAf_cA (incA D x)).symm

/- English proof (translation)
Introduce `D S T F hF R hR x hx hlat`. Set `fO : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (EAf D)` to `AddMonoidHom.mk' (frMapO S T F.βS F.βT) (fun x y => by unfold frMapO; rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul])`. Set `fA : WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D)` to `AddMonoidHom.mk' (frMapAdj S T F.βS F.βT) (GlobalTheory.PlaceVec.frMapAdj_add S T F.βS F.βT)`. Set `mR : WO S T →+ WO S T` to `AddMonoidHom.mk' (fun u => Matrix.of fun i j => idem R * u i j) (fun u v => by ext i j; simp [mul_add])`. Set `p : WO S T → Prop` to `fun u => IsIntM (fO (mR u)) ∧ IsIntM (fA (mR u))`.

Establish `hadd : ∀ u v, p u → p v → p (u + v)`. Introduce `u v hu hv`. Simplify using `only [p, map_add]`. Conclude with `⟨fun i j => add_mem (hu.1 i j) (hv.1 i j), fun i j => add_mem (hu.2 i j) (hv.2 i j)⟩`. Establish `hneg : ∀ u, p u → p (-u)`.

Introduce `u hu`. Simplify using `only [p, map_neg]`. Conclude with `⟨fun i j => neg_mem (hu.1 i j), fun i j => neg_mem (hu.2 i j)⟩`. Establish `hzero : p 0`. Simplify using `only [p, map_zero]`.

Conclude with `⟨fun i j => zero_mem _, fun i j => zero_mem _⟩`. Establish `hgen : ∀ α ∈ intAf D.host.F, ∀ a ∈ D.host.AA, ∀ s ∈ F.ΛS, ∀ t ∈ F.ΛT, p (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))`. Introduce `α hα a ha s hs t ht`. Use `set z : EAf D := toEAf D (idem R) * eToEAf D a * ((1 : D.host.E) ⊗ₜ[D.host.F] α) with hzdef`. Use `set col : Fin T.rank → EAf D := fun i => eToEAf D (t i) with hcol`.

Use `set row : Fin S.rank → EAf D := fun j => eToEAf D (∑ k, star (s k) * S.gram k j) with hrow`. Establish `hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `mul_mem (idem_mul_mem hR ha) (GlobalTheory.PlaceDatum.tmul_mem_int (one_mem _) hα)`. Establish `hm : ∀ m : D.host.E, (m ⊗ₜ[D.host.F] α : EAf D) = eToEAf D m * ((1 : D.host.E) ⊗ₜ[D.host.F] α)`. Introduce `m`. Express the relevant statement in the definitionally equal form `_ = (m ⊗ₜ[D.host.F] (1 : Af D.host.F)) * _`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `hY : (mR (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))).map (toEAf D) = Matrix.of fun i j => z * col i * row j`. Use extensionality with `i j`. Simplify using `only [mR, AddMonoidHom.mk'_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.LatVac.finTens, GlobalTheory.LatVac.genMap]`. Rewrite using `[map_mul]`.

Express the relevant statement in the definitionally equal form `toEAf D (idem R) * ((a * t i * ∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] α) = _`. Rewrite using `[hm, map_mul, map_mul]`. Simplify using `only [hzdef, hcol, hrow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcolI : ∀ i, ((F.βT⁻¹).val *ᵥ col) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `(hF.frT col).1 (Submodule.subset_span ⟨t, ht, rfl⟩)`.

Establish `hrowI : ∀ j, (row ᵥ* F.βS.val) j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun j => row_frame_mem hF.sdS hF.frS hs j`. Prove the components needed by the constructor for the conclusion. Introduce `i j`. Establish `e1 : fO (mR (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) = (F.βT⁻¹).val * Matrix.of (fun i j => z * col i * row j) * F.βS.val`. Express the relevant statement in the definitionally equal form `frMapO S T F.βS F.βT _ = _`.

Unfold `frMapO`. Rewrite using `[hY]`. Rewrite using `[e1, sandwich_apply]`. Conclude with `mul_mem (mul_mem hz (hcolI i)) (hrowI j)`. Introduce `i j`.

Establish `eT : ((Matrix.of fun i j => z * col i * row j).map (GlobalTheory.AdelicLatMove.cF D))ᵀ = Matrix.of fun a b => GlobalTheory.AdelicLatMove.cF D z * GlobalTheory.AdelicLatMove.cF D (row a) * GlobalTheory.AdelicLatMove.cF D (col b)`. Use extensionality with `a b`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : fA (mR (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) = ((F.βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) * Matrix.of (fun a b => GlobalTheory.AdelicLatMove.cF D z * GlobalTheory.AdelicLatMove.cF D (row a) * GlobalTheory.AdelicLatMove.cF D (col b)) * (T.gra …`.

Express the relevant statement in the definitionally equal form `frMapAdj S T F.βS F.βT _ = _`. Rewrite using `[GlobalTheory.PlaceVec.frMapAdj_eq, hY, eT]`. Establish `hr : (fun a => GlobalTheory.AdelicLatMove.cF D (row a)) = fun a => eToEAf D ((S.gram *ᵥ s) a)`. Use function extensionality and compare the values at `a`. Simplify using `only [hrow, cF_eToEAf, star_sum, star_mul', star_star, GlobalTheory.LatVac.gram_star, Matrix.mulVec, dotProduct]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (fun b => GlobalTheory.AdelicLatMove.cF D (col b)) = fun b => eToEAf D (star (t b))`. Use function extensionality and compare the values at `b`.

Simplify using `only [hcol, cF_eToEAf]`. Establish `hv1 : ((F.βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) *ᵥ (fun a => GlobalTheory.AdelicLatMove.cF D (row a)) = (F.βS⁻¹).val *ᵥ fun a => eToEAf D (s a)`. Rewrite using `[← Matrix.mulVec_mulVec, hr]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Rewrite using `[show (fun a => eToEAf D ((S.gram *ᵥ s) a)) = (eToEAf D) ∘ (S.gram *ᵥ s) from rfl, ← RingHom.map_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.one_mulVec]`. Establish `hv2 : (fun b => GlobalTheory.AdelicLatMove.cF D (col b)) ᵥ* (T.gram.map (eToEAf D) * F.βT.val) = (fun k => eToEAf D (∑ i, star (t i) * T.gram i k)) ᵥ* F.βT.val`. Rewrite using `[← Matrix.vecMul_vecMul, hc]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[show (fun b => eToEAf D (star (t b))) = (eToEAf D) ∘ (star t) from rfl, ← RingHom.map_vecMul]`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.star_apply]`. Rewrite using `[e1, sandwich_apply, hv1, hv2]`. Use `mul_mem (mul_mem (GlobalTheory.PlaceVec.cF_mem_int hz) ?_) (row_frame_mem hF.sdT hF.frT ht j)` and prove the remaining obligations. Conclude with `(hF.frS _).1 (Submodule.subset_span ⟨s, hs, rfl⟩) i`.

Establish `hmem : ∀ α ∈ intAf D.host.F, ∀ M ∈ GlobalTheory.LatVac.latRat S T (F.ΛS : Set (Fin S.rank → D.host.E)) (F.ΛT : Set (Fin T.rank → D.host.E)), p (GlobalTheory.LatVac.finTens α M)`. Introduce `α hα M hM`. Proceed by induction on `hM using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, s, hs, t, ht, rfl⟩` from `hw`.

Conclude with `hgen α hα a ha s hs t ht`. Consider the case `zero => rw [GlobalTheory.LatVac.finTens_zero]`. Conclude with `hzero`. Consider the case `add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]`. Conclude with `hadd _ _ hx hy`.

Consider the case `neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]`. Conclude with `hneg _ hx`. Establish `hp : p x` using `GlobalTheory.LatVac.latO_induction hmem hzero hadd hneg hlat`. Establish `e : mR x = x` using `Matrix.ext fun i j => hx i j`. Express the relevant statement in the definitionally equal form `IsIntM (frMapO S T F.βS F.βT (mR x)) ∧ IsIntM (frMapAdj S T F.βS F.βT (mR x)) at hp`.

Rewrite `hp` using `[e]`. Then use the resulting hypothesis.
-/
theorem frMap_int_of_mem_lat : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)},
    PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → x ∈ F.lat →
      IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) := by
  intro D S T F hF R hR x hx hlat
  let fO : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
    AddMonoidHom.mk' (frMapO S T F.βS F.βT) (fun x y => by unfold frMapO; rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul])
  let fA : WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
    AddMonoidHom.mk' (frMapAdj S T F.βS F.βT) (GlobalTheory.PlaceVec.frMapAdj_add S T F.βS F.βT)
  let mR : WO S T →+ WO S T :=
    AddMonoidHom.mk' (fun u => Matrix.of fun i j => idem R * u i j) (fun u v => by ext i j; simp [mul_add])
  let p : WO S T → Prop := fun u => IsIntM (fO (mR u)) ∧ IsIntM (fA (mR u))
  have hadd : ∀ u v, p u → p v → p (u + v) := by
    intro u v hu hv
    simp only [p, map_add]
    exact ⟨fun i j => add_mem (hu.1 i j) (hv.1 i j), fun i j => add_mem (hu.2 i j) (hv.2 i j)⟩
  have hneg : ∀ u, p u → p (-u) := by
    intro u hu
    simp only [p, map_neg]
    exact ⟨fun i j => neg_mem (hu.1 i j), fun i j => neg_mem (hu.2 i j)⟩
  have hzero : p 0 := by
    simp only [p, map_zero]
    exact ⟨fun i j => zero_mem _, fun i j => zero_mem _⟩
  have hgen : ∀ α ∈ intAf D.host.F, ∀ a ∈ D.host.AA, ∀ s ∈ F.ΛS, ∀ t ∈ F.ΛT,
      p (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t)) := by
    intro α hα a ha s hs t ht
    set z : EAf D := toEAf D (idem R) * eToEAf D a * ((1 : D.host.E) ⊗ₜ[D.host.F] α) with hzdef
    set col : Fin T.rank → EAf D := fun i => eToEAf D (t i) with hcol
    set row : Fin S.rank → EAf D := fun j => eToEAf D (∑ k, star (s k) * S.gram k j) with hrow
    have hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      mul_mem (idem_mul_mem hR ha) (GlobalTheory.PlaceDatum.tmul_mem_int (one_mem _) hα)
    have hm : ∀ m : D.host.E, (m ⊗ₜ[D.host.F] α : EAf D) = eToEAf D m * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      intro m
      change _ = (m ⊗ₜ[D.host.F] (1 : Af D.host.F)) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hY : (mR (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))).map (toEAf D) =
        Matrix.of fun i j => z * col i * row j := by
      ext i j
      simp only [mR, AddMonoidHom.mk'_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.LatVac.finTens,
        GlobalTheory.LatVac.genMap]
      rw [map_mul]
      change toEAf D (idem R) * ((a * t i * ∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] α) = _
      rw [hm, map_mul, map_mul]
      simp only [hzdef, hcol, hrow]
      ring
    have hcolI : ∀ i, ((F.βT⁻¹).val *ᵥ col) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      (hF.frT col).1 (Submodule.subset_span ⟨t, ht, rfl⟩)
    have hrowI : ∀ j, (row ᵥ* F.βS.val) j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun j => row_frame_mem hF.sdS hF.frS hs j
    constructor
    · intro i j
      have e1 : fO (mR (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) =
          (F.βT⁻¹).val * Matrix.of (fun i j => z * col i * row j) * F.βS.val := by
        change frMapO S T F.βS F.βT _ = _
        unfold frMapO
        rw [hY]
      rw [e1, sandwich_apply]
      exact mul_mem (mul_mem hz (hcolI i)) (hrowI j)
    · intro i j
      have eT : ((Matrix.of fun i j => z * col i * row j).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
          Matrix.of fun a b => GlobalTheory.AdelicLatMove.cF D z * GlobalTheory.AdelicLatMove.cF D (row a) *
            GlobalTheory.AdelicLatMove.cF D (col b) := by
        ext a b
        simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_mul]
        ring
      have e1 : fA (mR (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) =
          ((F.βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) *
            Matrix.of (fun a b => GlobalTheory.AdelicLatMove.cF D z * GlobalTheory.AdelicLatMove.cF D (row a) *
              GlobalTheory.AdelicLatMove.cF D (col b)) * (T.gram.map (eToEAf D) * F.βT.val) := by
        change frMapAdj S T F.βS F.βT _ = _
        rw [GlobalTheory.PlaceVec.frMapAdj_eq, hY, eT]
      have hr : (fun a => GlobalTheory.AdelicLatMove.cF D (row a)) = fun a => eToEAf D ((S.gram *ᵥ s) a) := by
        funext a
        simp only [hrow, cF_eToEAf, star_sum, star_mul', star_star, GlobalTheory.LatVac.gram_star, Matrix.mulVec, dotProduct]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      have hc : (fun b => GlobalTheory.AdelicLatMove.cF D (col b)) = fun b => eToEAf D (star (t b)) := by
        funext b
        simp only [hcol, cF_eToEAf]
      have hv1 : ((F.βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) *ᵥ (fun a => GlobalTheory.AdelicLatMove.cF D (row a)) =
          (F.βS⁻¹).val *ᵥ fun a => eToEAf D (s a) := by
        rw [← Matrix.mulVec_mulVec, hr]
        congr 1
        funext a
        rw [show (fun a => eToEAf D ((S.gram *ᵥ s) a)) = (eToEAf D) ∘ (S.gram *ᵥ s) from rfl,
          ← RingHom.map_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
          Matrix.one_mulVec]
      have hv2 : (fun b => GlobalTheory.AdelicLatMove.cF D (col b)) ᵥ* (T.gram.map (eToEAf D) * F.βT.val) =
          (fun k => eToEAf D (∑ i, star (t i) * T.gram i k)) ᵥ* F.βT.val := by
        rw [← Matrix.vecMul_vecMul, hc]
        congr 1
        funext k
        rw [show (fun b => eToEAf D (star (t b))) = (eToEAf D) ∘ (star t) from rfl, ← RingHom.map_vecMul]
        simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
      rw [e1, sandwich_apply, hv1, hv2]
      refine mul_mem (mul_mem (GlobalTheory.PlaceVec.cF_mem_int hz) ?_) (row_frame_mem hF.sdT hF.frT ht j)
      exact (hF.frS _).1 (Submodule.subset_span ⟨s, hs, rfl⟩) i
  have hmem : ∀ α ∈ intAf D.host.F, ∀ M ∈ GlobalTheory.LatVac.latRat S T (F.ΛS : Set (Fin S.rank → D.host.E))
      (F.ΛT : Set (Fin T.rank → D.host.E)), p (GlobalTheory.LatVac.finTens α M) := by
    intro α hα M hM
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact hgen α hα a ha s hs t ht
    | zero => rw [GlobalTheory.LatVac.finTens_zero]; exact hzero
    | add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]; exact hadd _ _ hx hy
    | neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]; exact hneg _ hx
  have hp : p x := GlobalTheory.LatVac.latO_induction hmem hzero hadd hneg hlat
  have e : mR x = x := Matrix.ext fun i j => hx i j
  change IsIntM (frMapO S T F.βS F.βT (mR x)) ∧ IsIntM (frMapAdj S T F.βS F.βT (mR x)) at hp
  rwa [e] at hp

end GlobalTheory.LatHalfInt
