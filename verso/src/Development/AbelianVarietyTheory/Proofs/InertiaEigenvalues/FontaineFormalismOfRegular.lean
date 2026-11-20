import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismTensorEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfFixed

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.FontCmp
open scoped Formalism.Per

namespace GlobalTheory.RegularRing

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13; revert K B W G ι h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 a σ hσ hreg v hv s h; exact @_root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed)`. Consider the case `exact @_root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed`. Consider the case `exact _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed`. Consider the case `(apply _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed ..)`.
-/
theorem linearIndepOn_of_invariant {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W) (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * a g b' = a g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn B v s := by
  first
  | (rename_i h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13; revert K B W G ι h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 a σ hσ hreg v hv s h; exact @_root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed)
  | exact @_root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed
  | exact _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed
  | (apply _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed ..)

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

def FracInv : Prop :=
  ∀ b b' : B, b ≠ 0 → (∀ g, b * PD.actB g b' = PD.actB g b * b') → ∃ c : K₀, b' = algebraMap K₀ B c * b

def LineUnit : Prop :=
  ∀ b : B, b ≠ 0 → (∀ g, ∃ x : Qp, PD.actB g b = algebraMap Qp B x * b) → IsUnit b

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

def sig (ρ : Representation LL G V) (g : G) : B ⊗[Qp] V →ₗ[Qp] B ⊗[Qp] V :=
  TensorProduct.map (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_tmul (ρ : Representation LL G V) (g : G) (b : B) (v : V) :
    sig PD ρ g (b ⊗ₜ[Qp] v) = PD.actB g b ⊗ₜ[Qp] ρ g v := rfl

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c v => simp [sig_tmul, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem sig_smul (ρ : Representation LL G V) (g : G) (b : B) (w : B ⊗[Qp] V) :
    sig PD ρ g (b • w) = PD.actB g b • sig PD ρ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [sig_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c v => simp [sig_tmul, actVB]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem comm_sig (ρ : Representation LL G V) (g : G) (w : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (sig PD ρ g w) = actVB PD ρ g (TensorProduct.comm Qp B V w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [sig_tmul, actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `TensorProduct.comm Qp B V w ∈ Dcris PD ρ ↔ _`. Rewrite using `[mem_Dcris]`. Use `forall_congr' fun g => ?_` and prove the remaining obligations. Rewrite using `[← comm_sig, (TensorProduct.comm Qp B V).injective.eq_iff]`.
-/
theorem mem_DcrisK₀ (ρ : Representation LL G V) (w : B ⊗[Qp] V) :
    w ∈ DcrisK₀ PD ρ ↔ ∀ g, sig PD ρ g w = w := by
  change TensorProduct.comm Qp B V w ∈ Dcris PD ρ ↔ _
  rw [mem_Dcris]
  refine forall_congr' fun g => ?_
  rw [← comm_sig, (TensorProduct.comm Qp B V).injective.eq_iff]

def swapD (ρ : Representation LL G V) : ↥(DcrisK₀ PD ρ) ≃ₗ[Qp] ↥(Dcris PD ρ) where
  toFun x := ⟨TensorProduct.comm Qp B V x, x.2⟩
  invFun y := ⟨(TensorProduct.comm Qp B V).symm y, by
    change TensorProduct.comm Qp B V _ ∈ Dcris PD ρ
    rw [LinearEquiv.apply_symm_apply]; exact y.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul (TensorProduct.comm Qp B V) c _)
  left_inv x := Subtype.ext ((TensorProduct.comm Qp B V).symm_apply_apply _)
  right_inv y := Subtype.ext ((TensorProduct.comm Qp B V).apply_symm_apply _)

/- English proof (translation)
Rewrite using `[Module.finrank_mul_finrank, Module.finrank_mul_finrank, (swapD PD ρ).finrank_eq]`.
-/
theorem finrank_swap (ρ : Representation LL G V) :
    finrank Qp K₀ * finrank K₀ ↥(DcrisK₀ PD ρ) = finrank Qp LL * finrank LL ↥(Dcris PD ρ) := by
  rw [Module.finrank_mul_finrank, Module.finrank_mul_finrank, (swapD PD ρ).finrank_eq]

/- English proof (translation)
Use `haveI := PD.finK₀`. Establish `h1` using `finrank_swap PD ρ`. Establish `h2` using `Module.finrank_mul_finrank Qp LL V`. Establish `h3 : 0 < finrank Qp LL` using `finrank_pos`. Establish `h4 : 0 < finrank Qp K₀` using `finrank_pos`.

Unfold `IsCrys`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h1` using `[h, mul_left_comm, h2]`. Conclude with `Nat.eq_of_mul_eq_mul_left h4 h1`.

Introduce `h`. Rewrite `h1` using `[h, ← h2, mul_left_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_left h3 h1).symm`.
-/
theorem isCrys_iff_finrank [FiniteDimensional Qp LL] (ρ : Representation LL G V) :
    IsCrys PD ρ ↔ finrank K₀ ↥(DcrisK₀ PD ρ) = finrank Qp V := by
  haveI := PD.finK₀
  have h1 := finrank_swap PD ρ
  have h2 := Module.finrank_mul_finrank Qp LL V
  have h3 : 0 < finrank Qp LL := finrank_pos
  have h4 : 0 < finrank Qp K₀ := finrank_pos
  unfold IsCrys
  constructor
  · intro h
    rw [h, mul_left_comm, h2] at h1
    exact Nat.eq_of_mul_eq_mul_left h4 h1
  · intro h
    rw [h, ← h2, mul_left_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left h3 h1).symm

variable [IsDomain B]

/- English proof (translation)
Establish `h1 : LinearIndependent K₀ fun i => (d i : B ⊗[Qp] V)` using `hd.map' (DcrisK₀ PD ρ).subtype (DcrisK₀ PD ρ).ker_subtype`. Rewrite using `[linearIndependent_iff_finset_linearIndependent]`. Introduce `s`. Conclude with `linearIndepOn_of_invariant (fun g b => PD.actB g b) (fun g => (sig PD ρ g).toAddMonoidHom) (sig_smul PD ρ) hf _ (fun g i => (mem_DcrisK₀ PD ρ _).1 (d i).2 g) s (h1.linearIndepOn _)`.
-/
theorem indepB (hf : FracInv PD) (ρ : Representation LL G V) {ι : Type} (d : ι → ↥(DcrisK₀ PD ρ))
    (hd : LinearIndependent K₀ d) : LinearIndependent B fun i => (d i : B ⊗[Qp] V) := by
  have h1 : LinearIndependent K₀ fun i => (d i : B ⊗[Qp] V) :=
    hd.map' (DcrisK₀ PD ρ).subtype (DcrisK₀ PD ρ).ker_subtype
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndepOn_of_invariant (fun g b => PD.actB g b) (fun g => (sig PD ρ g).toAddMonoidHom)
    (sig_smul PD ρ) hf _ (fun g i => (mem_DcrisK₀ PD ρ _).1 (d i).2 g) s (h1.linearIndepOn _)

/- English proof (translation)
Establish `hr : Module.rank K₀ ↥(DcrisK₀ PD ρ) ≤ finrank Qp V`. Use `rank_le fun s hs => ?_` and prove the remaining obligations. Simplify using `using LinearIndependent.fintype_card_le_finrank (indepB PD hf ρ _ hs)`. Use `haveI : Module.Finite K₀ ↥(DcrisK₀ PD ρ) := by`. Rewrite using `[← Module.rank_lt_aleph0_iff]`.

Conclude with `lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0`. Conclude with `⟨inferInstance, finrank_le_of_rank_le hr⟩`.
-/
theorem finite_le₀ (hf : FracInv PD) [FiniteDimensional Qp V] (ρ : Representation LL G V) :
    Module.Finite K₀ ↥(DcrisK₀ PD ρ) ∧ finrank K₀ ↥(DcrisK₀ PD ρ) ≤ finrank Qp V := by
  have hr : Module.rank K₀ ↥(DcrisK₀ PD ρ) ≤ finrank Qp V := by
    refine rank_le fun s hs => ?_
    simpa using LinearIndependent.fintype_card_le_finrank (indepB PD hf ρ _ hs)
  haveI : Module.Finite K₀ ↥(DcrisK₀ PD ρ) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0
  exact ⟨inferInstance, finrank_le_of_rank_le hr⟩

/- English proof (translation)
Use `haveI := PD.finK₀`. Use `haveI : FiniteDimensional Qp V := Module.Finite.trans LL V`. Take `⟨h1, h2⟩` from `finite_le₀ PD hf ρ`. Use `haveI : Module.Finite Qp ↥(DcrisK₀ PD ρ) := Module.Finite.trans K₀ _`. Use `haveI : Module.Finite Qp ↥(Dcris PD ρ) := Module.Finite.equiv (swapD PD ρ)`.

Use `⟨Module.Finite.of_restrictScalars_finite Qp LL _, ?_⟩` and prove the remaining obligations. Establish `h3` using `Nat.mul_le_mul_left (finrank Qp K₀) h2`. Rewrite `h3` using `[finrank_swap, ← Module.finrank_mul_finrank Qp LL V, mul_left_comm]`. Conclude with `Nat.le_of_mul_le_mul_left h3 finrank_pos`.
-/
theorem finite_le (hf : FracInv PD) [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (ρ : Representation LL G V) :
    Module.Finite LL ↥(Dcris PD ρ) ∧ finrank LL ↥(Dcris PD ρ) ≤ finrank Qp K₀ * finrank LL V := by
  haveI := PD.finK₀
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_le₀ PD hf ρ
  haveI : Module.Finite Qp ↥(DcrisK₀ PD ρ) := Module.Finite.trans K₀ _
  haveI : Module.Finite Qp ↥(Dcris PD ρ) := Module.Finite.equiv (swapD PD ρ)
  refine ⟨Module.Finite.of_restrictScalars_finite Qp LL _, ?_⟩
  have h3 := Nat.mul_le_mul_left (finrank Qp K₀) h2
  rw [finrank_swap, ← Module.finrank_mul_finrank Qp LL V, mul_left_comm] at h3
  exact Nat.le_of_mul_le_mul_left h3 finrank_pos

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis K₀ ↥(DcrisK₀ PD ρ)`. Establish `h` using `indepB PD hf ρ e e.linearIndependent`. Establish `h2 : (fun i => (e i : B ⊗[Qp] V)) = comparison PD ρ ∘ (Algebra.TensorProduct.basis B e)`. Use function extensionality and compare the values at `i`. Simplify using `[comparison_tmul]`.

Rewrite `h` using `[h2]`. Conclude with `LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis B e).span_eq h`.
-/
theorem comparison_injective (hf : FracInv PD) (ρ : Representation LL G V) :
    Function.Injective (comparison PD ρ) := by
  let e := Module.Free.chooseBasis K₀ ↥(DcrisK₀ PD ρ)
  have h := indepB PD hf ρ e e.linearIndependent
  have h2 : (fun i => (e i : B ⊗[Qp] V)) = comparison PD ρ ∘ (Algebra.TensorProduct.basis B e) := by
    funext i
    simp [comparison_tmul]
  rw [h2] at h
  exact LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis B e).span_eq h

/- English proof (translation)
Set `v` to `Module.finBasis Qp V`. Set `e` to `Algebra.TensorProduct.basis B v`. Set `A` to `e.toMatrix d`. Establish `hA : A.det ≠ 0`. Introduce `h0`.

Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hc` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `Fintype.linearIndependent_iff.1 hi c ?_ i` and prove the remaining obligations. Apply `e.repr.injective` to reduce the goal to its premises.

Use extensionality with `j`. Use `congrFun hc0 j` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, A, Basis.toMatrix_apply, Pi.zero_apply] at this`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply]`. Rewrite using `[← this]`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k = ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j)`. Introduce `g w k`. Use `conv_lhs => rw [← e.sum_repr w]`. Simplify using `only [map_sum, sig_smul, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`. Simplify using `[e, sig_tmul, Algebra.algebraMap_eq_smul_one]`. Establish `hdet : IsUnit A.det`.

Use `hu _ hA fun g => ?_` and prove the remaining obligations. Set `M : Matrix (Fin (finrank Qp V)) (Fin (finrank Qp V)) Qp` to `fun k j => v.repr (ρ g (v j)) k`. Establish `h1 : A = (algebraMap Qp B).mapMatrix M * (PD.actB g : B →+* B).mapMatrix A`. Use extensionality with `k i`. Rewrite using `[Matrix.mul_apply]`.

Express the relevant statement in the definitionally equal form `e.repr (d i) k = _`. Use `conv_lhs => rw [← hd g i, hrep]`. Both sides reduce to the same expression. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]`.

Establish `h3 : M.det ≠ 0` using `fun h => hA (by rw [h2, h, map_zero, zero_mul])`. Use `⟨M.det⁻¹, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [h2]`. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ h3, map_one, one_mul]`. Both sides reduce to the same expression.

Conclude with `((Basis.is_basis_iff_det e).2 hdet).2`.
-/
theorem span_eq_top_of_invariant (hu : LineUnit PD) [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (d : Fin (finrank Qp V) → B ⊗[Qp] V) (hd : ∀ g i, sig PD ρ g (d i) = d i)
    (hi : LinearIndependent B d) : Submodule.span B (Set.range d) = ⊤ := by
  classical
  let v := Module.finBasis Qp V
  let e := Algebra.TensorProduct.basis B v
  let A := e.toMatrix d
  have hA : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext i
    refine Fintype.linearIndependent_iff.1 hi c ?_ i
    apply e.repr.injective
    ext j
    have := congrFun hc0 j
    simp only [Matrix.mulVec, dotProduct, A, Basis.toMatrix_apply, Pi.zero_apply] at this
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k =
      ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]
    simp only [map_sum, sig_smul, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  have hdet : IsUnit A.det := by
    refine hu _ hA fun g => ?_
    let M : Matrix (Fin (finrank Qp V)) (Fin (finrank Qp V)) Qp := fun k j => v.repr (ρ g (v j)) k
    have h1 : A = (algebraMap Qp B).mapMatrix M * (PD.actB g : B →+* B).mapMatrix A := by
      ext k i
      rw [Matrix.mul_apply]
      change e.repr (d i) k = _
      conv_lhs => rw [← hd g i, hrep]
      rfl
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det] at h2
    have h3 : M.det ≠ 0 := fun h => hA (by rw [h2, h, map_zero, zero_mul])
    refine ⟨M.det⁻¹, ?_⟩
    conv_rhs => rw [h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h3, map_one, one_mul]
    rfl
  exact ((Basis.is_basis_iff_det e).2 hdet).2

/- English proof (translation)
Use `haveI : FiniteDimensional Qp V := Module.Finite.trans LL V`. Take `⟨h1, h2⟩` from `finite_le₀ PD hf ρ`. Rewrite using `[isCrys_iff_finrank]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Set `e` to `Module.finBasisOfFinrankEq K₀ _ h`. Rewrite using `[eq_top_iff, ← span_eq_top_of_invariant PD hu ρ (fun i => e i) (fun g i => (mem_DcrisK₀ PD ρ _).1 (e i).2 g) (indepB PD hf ρ e e.linearIndependent)]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(e i).2`.

Introduce `h`. Use `le_antisymm h2 ?_` and prove the remaining obligations. Establish `hs : Function.Surjective (comparison PD ρ)`. Rewrite using `[← LinearMap.range_eq_top, comparison, LinearMap.range_liftBaseChange, Submodule.range_subtype, h]`. Simplify using `using LinearMap.finrank_le_finrank_of_surjective hs`.
-/
theorem isCrys_iff_span (hf : FracInv PD) (hu : LineUnit PD) [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (ρ : Representation LL G V) :
    IsCrys PD ρ ↔ Submodule.span B (DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) = ⊤ := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_le₀ PD hf ρ
  rw [isCrys_iff_finrank]
  constructor
  · intro h
    let e := Module.finBasisOfFinrankEq K₀ _ h
    rw [eq_top_iff, ← span_eq_top_of_invariant PD hu ρ (fun i => e i)
      (fun g i => (mem_DcrisK₀ PD ρ _).1 (e i).2 g) (indepB PD hf ρ e e.linearIndependent)]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact (e i).2
  · intro h
    refine le_antisymm h2 ?_
    have hs : Function.Surjective (comparison PD ρ) := by
      rw [← LinearMap.range_eq_top, comparison, LinearMap.range_liftBaseChange, Submodule.range_subtype, h]
    simpa using LinearMap.finrank_le_finrank_of_surjective hs

/- English proof (translation)
Use `⟨comparison_injective PD hf ρ, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.range_eq_top, comparison, LinearMap.range_liftBaseChange, Submodule.range_subtype, (isCrys_iff_span PD hf hu ρ).1 h]`.
-/
theorem comparison_bijective (hf : FracInv PD) (hu : LineUnit PD) [FiniteDimensional Qp LL]
    [FiniteDimensional LL V] (ρ : Representation LL G V) (h : IsCrys PD ρ) :
    Function.Bijective (comparison PD ρ) := by
  refine ⟨comparison_injective PD hf ρ, ?_⟩
  rw [← LinearMap.range_eq_top, comparison, LinearMap.range_liftBaseChange, Submodule.range_subtype,
    (isCrys_iff_span PD hf hu ρ).1 h]

omit [IsDomain B] in

/- English proof (translation)
Establish `hm : ∀ g y, (f.restrictScalars Qp).baseChange B (sig PD ρ g y) = sig PD ρ' g ((f.restrictScalars Qp).baseChange B y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [sig_tmul, hf g]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite `hx`, the goal using `[mem_DcrisK₀]`. Introduce `g`. Rewrite using `[← hm, hx]`.
-/
theorem baseChange_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) (x : B ⊗[Qp] V) (hx : x ∈ DcrisK₀ PD ρ) :
    (f.restrictScalars Qp).baseChange B x ∈ DcrisK₀ PD ρ' := by
  have hm : ∀ g y, (f.restrictScalars Qp).baseChange B (sig PD ρ g y) =
      sig PD ρ' g ((f.restrictScalars Qp).baseChange B y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [sig_tmul, hf g]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [mem_DcrisK₀] at hx ⊢
  intro g
  rw [← hm, hx]

omit [IsDomain B] in
/- English proof (translation)
Establish `h1 : Submodule.span B (DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) ≤ (Submodule.span B (DcrisK₀ PD ρ' : Set (B ⊗[Qp] V'))).comap ((f.restrictScalars Qp).baseChange B)` using `Submodule.span_le.2 fun x hx => Submodule.subset_span (baseChange_mem PD hf x hx)`. Conclude with `h1 (h ▸ Submodule.mem_top : b ⊗ₜ[Qp] v ∈ _)`.
-/
theorem tmul_mem_span {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) (h : Submodule.span B (DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) = ⊤) (b : B) (v : V) :
    b ⊗ₜ[Qp] f v ∈ Submodule.span B (DcrisK₀ PD ρ' : Set (B ⊗[Qp] V')) := by
  have h1 : Submodule.span B (DcrisK₀ PD ρ : Set (B ⊗[Qp] V)) ≤
      (Submodule.span B (DcrisK₀ PD ρ' : Set (B ⊗[Qp] V'))).comap ((f.restrictScalars Qp).baseChange B) :=
    Submodule.span_le.2 fun x hx => Submodule.subset_span (baseChange_mem PD hf x hx)
  exact h1 (h ▸ Submodule.mem_top : b ⊗ₜ[Qp] v ∈ _)

omit [IsDomain B] in
/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact S.zero_mem`. Consider the case `tmul b v => exact h b v`.

Consider the case `add a b ha hb => exact S.add_mem ha hb`.
-/
theorem eq_top_of_tmul (S : Submodule B (B ⊗[Qp] V)) (h : ∀ b v, b ⊗ₜ[Qp] v ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul b v => exact h b v
  | add a b ha hb => exact S.add_mem ha hb

variable (LL) [FiniteDimensional Qp LL]

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f he hs h`. Rewrite `h`, the goal using `[isCrys_iff_span PD hf hu]`. Use `eq_top_of_tmul _ fun b v => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `hs v`. Conclude with `tmul_mem_span PD he h b v`.
-/
theorem quotCrys (hf : FracInv PD) (hu : LineUnit PD) : QuotCrys PD LL := by
  intro V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f he hs h
  rw [isCrys_iff_span PD hf hu] at h ⊢
  refine eq_top_of_tmul _ fun b v => ?_
  obtain ⟨v, rfl⟩ := hs v
  exact tmul_mem_span PD he h b v

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' h h'`. Rewrite `h`, `h'`, the goal using `[isCrys_iff_span PD hf hu]`. Use `eq_top_of_tmul _ fun b v => ?_` and prove the remaining obligations. Establish `h1 : IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V')` using `fun g x => by`. Simplify using `[Representation.prod]`.

Establish `h2 : IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V')` using `fun g x => by`. Simplify using `[Representation.prod]`. Establish `h3 : v = LinearMap.inl LL V V' v.1 + LinearMap.inr LL V V' v.2` using `by simp`. Rewrite using `[h3, tmul_add]`. Conclude with `Submodule.add_mem _ (tmul_mem_span PD h1 h b _) (tmul_mem_span PD h2 h' b _)`.
-/
theorem sumCrys (hf : FracInv PD) (hu : LineUnit PD) : SumCrys PD LL := by
  intro V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' h h'
  rw [isCrys_iff_span PD hf hu] at h h' ⊢
  refine eq_top_of_tmul _ fun b v => ?_
  have h1 : IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V') := fun g x => by
    simp [Representation.prod]
  have h2 : IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V') := fun g x => by
    simp [Representation.prod]
  have h3 : v = LinearMap.inl LL V V' v.1 + LinearMap.inr LL V V' v.2 := by simp
  rw [h3, tmul_add]
  exact Submodule.add_mem _ (tmul_mem_span PD h1 h b _) (tmul_mem_span PD h2 h' b _)

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' h h'`. Establish `hc` using `comparison_bijective PD hf hu ρ h`. Establish `hc'` using `comparison_bijective PD hf hu ρ' h'`. Rewrite using `[isCrys_iff_span PD hf hu]`. Use `set S := Submodule.span B (DcrisK₀ PD (ρ.tprod ρ') : Set (B ⊗[Qp] (V ⊗[LL] V')))`.

Set `c` to `(TensorProduct.comm Qp B (V ⊗[LL] V')).symm`. Establish `hcm : ∀ (b : B) z, c (mB LL b z) = b • c z` using `fun b z => by`. Apply `(TensorProduct.comm Qp B (V ⊗[LL] V')).injective` to reduce the goal to its premises. Rewrite using `[comm_smulB (LL := LL), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Establish `key : ∀ (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B), c (prodB (LL` using `LL) (x ⊗ₜ[LL] y)) ∈ S := by`.

Introduce `x y`. Proceed by induction on `x using cmp_ind PD hc with`. Consider the case `h0 => simp`. Consider the case `hadd x x' hx hx' => rw [add_tmul, map_add, map_add]`. Conclude with `S.add_mem hx hx'`.

Consider the case `hb b d`. Rewrite using `[prod_mB_left, hcm]`. Use `S.smul_mem _ ?_` and prove the remaining obligations. Proceed by induction on `y using cmp_ind PD hc' with`. Consider the case `h0 => simp`.

Consider the case `hadd x x' hx hx' => rw [tmul_add, map_add, map_add]`. Conclude with `S.add_mem hx hx'`. Consider the case `hb b' d'`. Rewrite using `[prod_mB_right, hcm]`. Use `S.smul_mem _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TensorProduct.comm Qp B _ _ ∈ Dcris PD _`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `prod_mem PD d d'`. Use `eq_top_of_tmul _ fun b w => ?_` and prove the remaining obligations. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a a' ha ha' => rw [tmul_add]`. Conclude with `S.add_mem ha ha'`. Consider the case `tmul v v'`. Use `key (v ⊗ₜ b) (v' ⊗ₜ 1)` as an intermediate fact.

Rewrite `this` using `[prodB_tmul, mul_one]`. Conclude with `this`.
-/
theorem tensorCrys (hf : FracInv PD) (hu : LineUnit PD) : TensorCrys PD LL := by
  intro V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' h h'
  have hc := comparison_bijective PD hf hu ρ h
  have hc' := comparison_bijective PD hf hu ρ' h'
  rw [isCrys_iff_span PD hf hu]
  set S := Submodule.span B (DcrisK₀ PD (ρ.tprod ρ') : Set (B ⊗[Qp] (V ⊗[LL] V')))
  let c := (TensorProduct.comm Qp B (V ⊗[LL] V')).symm
  have hcm : ∀ (b : B) z, c (mB LL b z) = b • c z := fun b z => by
    apply (TensorProduct.comm Qp B (V ⊗[LL] V')).injective
    rw [comm_smulB (LL := LL), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key : ∀ (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B), c (prodB (LL := LL) (x ⊗ₜ[LL] y)) ∈ S := by
    intro x y
    induction x using cmp_ind PD hc with
    | h0 => simp
    | hadd x x' hx hx' => rw [add_tmul, map_add, map_add]; exact S.add_mem hx hx'
    | hb b d =>
      rw [prod_mB_left, hcm]
      refine S.smul_mem _ ?_
      induction y using cmp_ind PD hc' with
      | h0 => simp
      | hadd x x' hx hx' => rw [tmul_add, map_add, map_add]; exact S.add_mem hx hx'
      | hb b' d' =>
        rw [prod_mB_right, hcm]
        refine S.smul_mem _ (Submodule.subset_span ?_)
        change TensorProduct.comm Qp B _ _ ∈ Dcris PD _
        rw [LinearEquiv.apply_symm_apply]
        exact prod_mem PD d d'
  refine eq_top_of_tmul _ fun b w => ?_
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [tmul_add]; exact S.add_mem ha ha'
  | tmul v v' =>
    have := key (v ⊗ₜ b) (v' ⊗ₜ 1)
    rw [prodB_tmul, mul_one] at this
    exact this

omit [IsDomain B] in

/- English proof (translation)
Use `haveI : FiniteDimensional Qp V := Module.Finite.trans LL V`. Use `haveI : FiniteDimensional Qp (Dual LL V) := Module.Finite.trans LL _`. Take `⟨lam, hlam⟩` from `exists_ne (0 : Dual Qp LL)`. Set `φ : Dual LL V →ₗ[Qp] Dual Qp V` to `{ toFun := fun f => lam ∘ₗ f.restrictScalars Qp map_add' := fun f f' => by ext; simp map_smul' := fun c f => by ext; simp }`. Establish `hφ : Function.Injective φ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `f h0`. Assume the negation of the conclusion as `hne`. Apply `hlam` to reduce the goal to its premises. Use extensionality with `a`.

Take `⟨v, rfl⟩` from `LinearMap.surjective_of_ne_zero hne a`. Conclude with `LinearMap.congr_fun h0 v`. Use `⟨lam, LinearMap.linearEquivOfInjective φ hφ ?_, fun f v => rfl⟩` and prove the remaining obligations. Rewrite using `[← Module.finrank_mul_finrank Qp LL (Dual LL V), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, Module.finrank_mul_finrank]`.
-/
theorem exists_dual_equiv (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] : ∃ (lam : LL →ₗ[Qp] Qp) (e : Dual LL V ≃ₗ[Qp] Dual Qp V),
      ∀ f v, e f v = lam (f v) := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  haveI : FiniteDimensional Qp (Dual LL V) := Module.Finite.trans LL _
  obtain ⟨lam, hlam⟩ := exists_ne (0 : Dual Qp LL)
  let φ : Dual LL V →ₗ[Qp] Dual Qp V :=
    { toFun := fun f => lam ∘ₗ f.restrictScalars Qp
      map_add' := fun f f' => by ext; simp
      map_smul' := fun c f => by ext; simp }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro f h0
    by_contra hne
    apply hlam
    ext a
    obtain ⟨v, rfl⟩ := LinearMap.surjective_of_ne_zero hne a
    exact LinearMap.congr_fun h0 v
  refine ⟨lam, LinearMap.linearEquivOfInjective φ hφ ?_, fun f v => rfl⟩
  rw [← Module.finrank_mul_finrank Qp LL (Dual LL V), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq,
    Module.finrank_mul_finrank]

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ h`. Use `haveI : FiniteDimensional Qp V := Module.Finite.trans LL V`. Take `⟨lam, e, he⟩` from `exists_dual_equiv (Qp := Qp) LL V`. Set `ibc` to `TensorProduct.isBaseChange Qp V B`. Set `Φ : B ⊗[Qp] Dual LL V ≃ₗ[B] Dual B (B ⊗[Qp] V)` to `(e.baseChange Qp B _ _).trans ibc.toDualBaseChange`.

Establish `hΦ : ∀ (b c : B) (f : Dual LL V) (v : V), Φ (b ⊗ₜ f) (c ⊗ₜ v) = c * (b * algebraMap Qp B (lam (f v)))`. Introduce `b c f v`. Establish `h1 : c ⊗ₜ[Qp] v = c • (TensorProduct.mk Qp B V 1 v)` using `by simp [smul_tmul']`. Rewrite using `[h1, map_smul, ← he, ← ibc.toDualBaseChange_tmul]`. Both sides reduce to the same expression.

Establish `hG : ∀ g x y, Φ (sig PD ρ.dual g x) (sig PD ρ g y) = PD.actB g (Φ x y)`. Introduce `g x y`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']`.

Consider the case `tmul b f`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a a' ha ha' => simp only [map_add, ha, ha']`. Consider the case `tmul c v`.

Rewrite using `[sig_tmul, sig_tmul, hΦ, hΦ, map_mul, map_mul, IsScalarTower.algebraMap_apply Qp K₀ B (lam (f v)), AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]`. Simplify using `[Representation.dual_apply, Module.Dual.transpose_apply]`. Take `⟨h1, -⟩` from `finite_le₀ PD hf ρ`. Set `d₀` to `Module.finBasis K₀ ↥(DcrisK₀ PD ρ)`. Set `d` to `(Algebra.TensorProduct.basis B d₀).map (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))`.

Establish `hd : ∀ g i, sig PD ρ g (d i) = d i`. Introduce `g i`. Establish `: d i = (d₀ i : B ⊗[Qp] V)` using `by simp [d, comparison_tmul]`. Rewrite using `[this]`. Conclude with `(mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g`.

Rewrite using `[isCrys_iff_span PD hf hu, eq_top_iff, ← (d.dualBasis.map Φ.symm).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_DcrisK₀]`. Introduce `g`.

Apply `Φ.injective` to reduce the goal to its premises. Use `d.ext fun j => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hd g j, hG]`. Rewrite using `[Basis.map_apply, LinearEquiv.apply_symm_apply, Basis.dualBasis_apply_self]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dualCrys (hf : FracInv PD) (hu : LineUnit PD) : DualCrys PD LL := by
  classical
  intro V _ _ _ _ _ ρ h
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨lam, e, he⟩ := exists_dual_equiv (Qp := Qp) LL V
  let ibc := TensorProduct.isBaseChange Qp V B
  let Φ : B ⊗[Qp] Dual LL V ≃ₗ[B] Dual B (B ⊗[Qp] V) := (e.baseChange Qp B _ _).trans ibc.toDualBaseChange
  have hΦ : ∀ (b c : B) (f : Dual LL V) (v : V),
      Φ (b ⊗ₜ f) (c ⊗ₜ v) = c * (b * algebraMap Qp B (lam (f v))) := by
    intro b c f v
    have h1 : c ⊗ₜ[Qp] v = c • (TensorProduct.mk Qp B V 1 v) := by simp [smul_tmul']
    rw [h1, map_smul, ← he, ← ibc.toDualBaseChange_tmul]
    rfl
  have hG : ∀ g x y, Φ (sig PD ρ.dual g x) (sig PD ρ g y) = PD.actB g (Φ x y) := by
    intro g x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
    | tmul b f =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a a' ha ha' => simp only [map_add, ha, ha']
      | tmul c v =>
        rw [sig_tmul, sig_tmul, hΦ, hΦ, map_mul, map_mul, IsScalarTower.algebraMap_apply Qp K₀ B (lam (f v)),
          AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
        simp [Representation.dual_apply, Module.Dual.transpose_apply]
  obtain ⟨h1, -⟩ := finite_le₀ PD hf ρ
  let d₀ := Module.finBasis K₀ ↥(DcrisK₀ PD ρ)
  let d := (Algebra.TensorProduct.basis B d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))
  have hd : ∀ g i, sig PD ρ g (d i) = d i := by
    intro g i
    have : d i = (d₀ i : B ⊗[Qp] V) := by simp [d, comparison_tmul]
    rw [this]
    exact (mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g
  rw [isCrys_iff_span PD hf hu, eq_top_iff, ← (d.dualBasis.map Φ.symm).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_DcrisK₀]
  intro g
  apply Φ.injective
  refine d.ext fun j => ?_
  conv_lhs => rw [← hd g j, hG]
  rw [Basis.map_apply, LinearEquiv.apply_symm_apply, Basis.dualBasis_apply_self]
  split_ifs <;> simp

omit [IsDomain B] [FiniteDimensional Qp LL] in
variable {LL} in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [tensorB]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tensorB_eq (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    tensorB (Qp := Qp) (B := B) f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [tensorB]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsDomain B] [FiniteDimensional Qp LL] in
variable {LL} in

/- English proof (translation)
Establish `hex : Function.Exact ((i.restrictScalars Qp).rTensor B) ((p.restrictScalars Qp).rTensor B)` using `rTensor_exact B (f := i.restrictScalars Qp) (g := p.restrictScalars Qp) h2 h3`. Establish `hinj : Function.Injective ((i.restrictScalars Qp).rTensor B)` using `Module.Flat.rTensor_preserves_injective_linearMap _ h1`. Establish `hci : ∀ x, (DcrisMap PD hi x : V ⊗[Qp] B) = (i.restrictScalars Qp).rTensor B x` using `fun x => tensorB_eq i x.1`. Establish `hcp : ∀ x, (DcrisMap PD hp x : V' ⊗[Qp] B) = (p.restrictScalars Qp).rTensor B x` using `fun x => tensorB_eq p x.1`. Establish `hm : ∀ g y, (i.restrictScalars Qp).rTensor B (actVB PD ρ₀ g y) = actVB PD ρ g ((i.restrictScalars Qp).rTensor B y)`.

Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB, hi g]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Use `⟨fun x y h => Subtype.ext (hinj ?_), fun x => ⟨fun h => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hci, ← hci, h]`. Take `⟨y, hy⟩` from `(hex x).1 (by rw [← hcp, h]; rfl)`. Use `⟨⟨y, (mem_Dcris PD ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext ((hci _).trans hy)⟩` and prove the remaining obligations. Rewrite using `[hm, hy]`.

Conclude with `(mem_Dcris PD ρ _).1 x.2 g`. Introduce and unpack `⟨y, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcp, hci]`. Conclude with `(hex _).2 ⟨_, rfl⟩`.
-/
theorem left_exact {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    {ρ₀ : Representation LL G V₀} {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    {i : V₀ →ₗ[LL] V} {p : V →ₗ[LL] V'} (hi : IsEquivariant ρ₀ ρ i) (hp : IsEquivariant ρ ρ' p)
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p) :
    Function.Injective (DcrisMap PD hi) ∧ Function.Exact (DcrisMap PD hi) (DcrisMap PD hp) := by
  have hex : Function.Exact ((i.restrictScalars Qp).rTensor B) ((p.restrictScalars Qp).rTensor B) :=
    rTensor_exact B (f := i.restrictScalars Qp) (g := p.restrictScalars Qp) h2 h3
  have hinj : Function.Injective ((i.restrictScalars Qp).rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ h1
  have hci : ∀ x, (DcrisMap PD hi x : V ⊗[Qp] B) = (i.restrictScalars Qp).rTensor B x :=
    fun x => tensorB_eq i x.1
  have hcp : ∀ x, (DcrisMap PD hp x : V' ⊗[Qp] B) = (p.restrictScalars Qp).rTensor B x :=
    fun x => tensorB_eq p x.1
  have hm : ∀ g y, (i.restrictScalars Qp).rTensor B (actVB PD ρ₀ g y) =
      actVB PD ρ g ((i.restrictScalars Qp).rTensor B y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, hi g]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨fun x y h => Subtype.ext (hinj ?_), fun x => ⟨fun h => ?_, ?_⟩⟩
  · rw [← hci, ← hci, h]
  · obtain ⟨y, hy⟩ := (hex x).1 (by rw [← hcp, h]; rfl)
    refine ⟨⟨y, (mem_Dcris PD ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext ((hci _).trans hy)⟩
    rw [hm, hy]
    exact (mem_Dcris PD ρ _).1 x.2 g
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    rw [hcp, hci]
    exact (hex _).2 ⟨_, rfl⟩

/- English proof (translation)
Introduce `V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f he hi h`. Establish `hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ g)`. Introduce and unpack `g _ ⟨v, rfl⟩`. Conclude with `⟨ρ' g v, he g v⟩`. Establish `hq : IsEquivariant ρ (ρ.quotient (LinearMap.range f) hst) (LinearMap.range f).mkQ` using `fun g v => rfl`.

Take `⟨h1, h2⟩` from `left_exact PD he hq hi (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective`. Take `⟨a1, a2⟩` from `finite_le PD hf ρ'`. Take `⟨b1, b2⟩` from `finite_le PD hf ρ`. Take `⟨c1, c2⟩` from `finite_le PD hf (ρ.quotient (LinearMap.range f) hst)`. Establish `h3` using `(DcrisMap PD hq).finrank_range_add_finrank_ker`.

Rewrite `h3` using `[h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1]`. Establish `h4` using `(LinearMap.range (DcrisMap PD hq)).finrank_le`. Establish `h5` using `(LinearMap.range f).finrank_quotient_add_finrank`. Rewrite `h5` using `[LinearMap.finrank_range_of_inj hi]`. Unfold `IsCrys at h ⊢`.

Rewrite `h` using `[← h5, mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem subCrys (hf : FracInv PD) : SubCrys PD LL := by
  intro V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f he hi h
  have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ' g v, he g v⟩
  have hq : IsEquivariant ρ (ρ.quotient (LinearMap.range f) hst) (LinearMap.range f).mkQ := fun g v => rfl
  obtain ⟨h1, h2⟩ := left_exact PD he hq hi (LinearMap.exact_map_mkQ_range f)
    (LinearMap.range f).mkQ_surjective
  obtain ⟨a1, a2⟩ := finite_le PD hf ρ'
  obtain ⟨b1, b2⟩ := finite_le PD hf ρ
  obtain ⟨c1, c2⟩ := finite_le PD hf (ρ.quotient (LinearMap.range f) hst)
  have h3 := (DcrisMap PD hq).finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1] at h3
  have h4 := (LinearMap.range (DcrisMap PD hq)).finrank_le
  have h5 := (LinearMap.range f).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hi] at h5
  unfold IsCrys at h ⊢
  rw [← h5, mul_add] at h
  omega

/- English proof (translation)
Introduce `V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ i p hi hp h1 h2 h3 c₀ c₁ c₂`. Take `⟨e1, e2⟩` from `left_exact PD hi hp h1 h2 h3`. Use `⟨e1, e2, ?_⟩` and prove the remaining obligations. Take `⟨a1, -⟩` from `finite_le PD hf ρ₁`. Take `⟨b1, -⟩` from `finite_le PD hf ρ₂`.

Establish `h4` using `(DcrisMap PD hp).finrank_range_add_finrank_ker`. Rewrite `h4` using `[e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1]`. Establish `h5` using `p.finrank_range_add_finrank_ker`. Rewrite `h5` using `[h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top]`. Rewrite using `[← LinearMap.range_eq_top]`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Unfold `IsCrys at c₀ c₁ c₂`. Rewrite `c₁` using `[← h5, mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dcrisExact (hf : FracInv PD) : DcrisExact PD LL := by
  intro V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ i p hi hp h1 h2 h3 c₀ c₁ c₂
  obtain ⟨e1, e2⟩ := left_exact PD hi hp h1 h2 h3
  refine ⟨e1, e2, ?_⟩
  obtain ⟨a1, -⟩ := finite_le PD hf ρ₁
  obtain ⟨b1, -⟩ := finite_le PD hf ρ₂
  have h4 := (DcrisMap PD hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  unfold IsCrys at c₀ c₁ c₂
  rw [← h5, mul_add] at c₁
  omega

omit [FiniteDimensional Qp LL] in

/- English proof (translation)
Use `haveI := PD.finK₀`. Set `s : K₀ ≃ₐ[Qp] K₀` to `AlgEquiv.ofBijective PD.σ PD.σ_bij`. Establish `hfix : IntermediateField.fixedField (Subgroup.zpowers s) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `c hc`.

Establish `h1 : PD.σ c = c` using `(IntermediateField.mem_fixedField_iff _ _).1 hc s (Subgroup.mem_zpowers s)`. Take `⟨x, hx⟩` from `PD.fund (algebraMap K₀ B c) (by rw [PD.φ_K₀, h1]) (by`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, Algebra.algebraMap_eq_smul_one]`. Conclude with `(PD.Fil 0).smul_mem _ PD.one_mem)`. Rewrite `hx` using `[IsScalarTower.algebraMap_apply Qp K₀ B]`.

Conclude with `⟨x, (algebraMap K₀ B).injective hx⟩`. Establish `hcard : Nat.card (Subgroup.zpowers s) = finrank Qp K₀`. Rewrite using `[← IntermediateField.finrank_fixedField_eq_card, hfix, IntermediateField.finrank_bot']`. Set `F : Subgroup.zpowers s → (K₀ →ₐ[Qp] LL)` to `fun γ => τ.comp (γ.1 : K₀ →ₐ[Qp] K₀)`. Establish `hF : Function.Injective F` using `fun a b h => Subtype.ext (AlgEquiv.ext fun c => τ.toRingHom.injective (AlgHom.congr_fun h c))`.

Take `⟨⟨γ, hγ⟩, rfl⟩` from `(hF.bijective_of_nat_card_le (hc.trans hcard.symm).le).2 τ'`. Take `⟨n, rfl⟩` from `mem_powers_iff_mem_zpowers.2 hγ`. Use `⟨n, fun c => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ ((s ^ n) c) = _`. Rewrite using `[AlgEquiv.coe_pow]`.

Both sides reduce to the same expression.
-/
theorem exists_pow_sigma (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (τ τ' : K₀ →ₐ[Qp] LL) :
    ∃ n : ℕ, ∀ c, τ' c = τ (PD.σ^[n] c) := by
  haveI := PD.finK₀
  let s : K₀ ≃ₐ[Qp] K₀ := AlgEquiv.ofBijective PD.σ PD.σ_bij
  have hfix : IntermediateField.fixedField (Subgroup.zpowers s) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have h1 : PD.σ c = c := (IntermediateField.mem_fixedField_iff _ _).1 hc s (Subgroup.mem_zpowers s)
    obtain ⟨x, hx⟩ := PD.fund (algebraMap K₀ B c) (by rw [PD.φ_K₀, h1]) (by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem)
    rw [IsScalarTower.algebraMap_apply Qp K₀ B] at hx
    exact ⟨x, (algebraMap K₀ B).injective hx⟩
  have hcard : Nat.card (Subgroup.zpowers s) = finrank Qp K₀ := by
    rw [← IntermediateField.finrank_fixedField_eq_card, hfix, IntermediateField.finrank_bot']
  let F : Subgroup.zpowers s → (K₀ →ₐ[Qp] LL) := fun γ => τ.comp (γ.1 : K₀ →ₐ[Qp] K₀)
  have hF : Function.Injective F := fun a b h =>
    Subtype.ext (AlgEquiv.ext fun c => τ.toRingHom.injective (AlgHom.congr_fun h c))
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := (hF.bijective_of_nat_card_le (hc.trans hcard.symm).le).2 τ'
  obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.2 hγ
  refine ⟨n, fun c => ?_⟩
  change τ ((s ^ n) c) = _
  rw [AlgEquiv.coe_pow]
  rfl

omit [IsDomain B] [FiniteDimensional Qp LL] in
variable {LL} in

/- English proof (translation)
Use `haveI : Module.Finite LL ↥(DcrisL PD ρ τ) := Submodule.finiteDimensional_of_le inf_le_left`. Establish `h1 : ∀ g x, φVB PD (LL` using `LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v b => simp [actVB, φVB, PD.φ_comm]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `h2 : ∀ (c : K₀) (x : V ⊗[Qp] B), φVB PD (LL` using `LL) (mB LL (algebraMap K₀ B c) x) = mB LL (algebraMap K₀ B (PD.σ c)) (φVB PD (LL := LL) x) := by`. Introduce `c x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v b => simp [mB, φVB, PD.φ_K₀]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `h3 : ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL` using `LL) x ∈ DcrisL PD ρ τ := by`. Introduce `x hx`.

Rewrite `hx`, the goal using `[mem_DcrisL, mem_Dcris]`. Use `⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `PD.σ_bij.2 c`. Rewrite using `[← h2, hx.2, map_smul, h]`. Establish `h4 : Function.Injective (φVB PD (LL` using `LL) (V := V)) := Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj`.

Conclude with `LinearMap.finrank_le_finrank_of_injective (f := (φVB PD (LL := LL)).restrict h3) fun x y hxy => Subtype.ext (h4 (congrArg Subtype.val hxy))`.
-/
theorem letter_le (ρ : Representation LL G V) [Module.Finite LL ↥(Dcris PD ρ)] (τ τ' : K₀ →ₐ[Qp] LL)
    (h : ∀ c, τ' c = τ (PD.σ c)) : finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ) := by
  haveI : Module.Finite LL ↥(DcrisL PD ρ τ) := Submodule.finiteDimensional_of_le inf_le_left
  have h1 : ∀ g x, φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ (c : K₀) (x : V ⊗[Qp] B), φVB PD (LL := LL) (mB LL (algebraMap K₀ B c) x) =
      mB LL (algebraMap K₀ B (PD.σ c)) (φVB PD (LL := LL) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h3 : ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL := LL) x ∈ DcrisL PD ρ τ := by
    intro x hx
    rw [mem_DcrisL, mem_Dcris] at hx ⊢
    refine ⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩
    obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
    rw [← h2, hx.2, map_smul, h]
  have h4 : Function.Injective (φVB PD (LL := LL) (V := V)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj
  exact LinearMap.finrank_le_finrank_of_injective (f := (φVB PD (LL := LL)).restrict h3)
    fun x y hxy => Subtype.ext (h4 (congrArg Subtype.val hxy))

omit [IsDomain B] [FiniteDimensional Qp LL] in
variable {LL} in

/- English proof (translation)
Set `v` to `Module.finBasis Qp K₀`. Set `A : Matrix (K₀ →ₐ[Qp] LL) (Fin (finrank Qp K₀)) LL` to `fun τ i => τ (v i)`. Establish `hA : LinearIndependent LL A.row`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc0`.

Use `Fintype.linearIndependent_iff.1 (linearIndependent_algHom_toLinearMap Qp K₀ LL) c ?_` and prove the remaining obligations. Use `v.ext fun i => ?_` and prove the remaining obligations. Simplify `congrFun hc0 i` using `[A, Matrix.row]`. Establish `hsurj : Function.Surjective A.mulVecLin`. Rewrite using `[← LinearMap.range_eq_top]`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use `hA.rank_matrix` as an intermediate fact. Rewrite `this` using `[Matrix.rank]`. Rewrite using `[this, finrank_fintype_fun_eq_card]`. Establish `hinj : Function.Injective A.mulVecLin` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hc])).2 hsurj`.

Set `μ : (Fin (finrank Qp K₀) → LL) →ₗ[LL] (M →ₗ[LL] M)` to `Fintype.linearCombination LL fun i => m (v i)`. Establish `hμ : ∀ a x, μ a x = ∑ i, a i • m (v i) x` using `fun a x => by`. Simplify using `[μ, Fintype.linearCombination_apply]`. Establish `hsum : ∀ (c : K₀) x, m c x = μ (fun i => algebraMap Qp LL (v.repr c i)) x`. Introduce `c x`.

Set `f : K₀ →+ M` to `AddMonoidHom.mk' (fun a => m a x) fun a b => hadd a b x`. Express the relevant statement in the definitionally equal form `f c = _`. Use `conv_lhs => rw [← v.sum_repr c, map_sum]`. Rewrite using `[hμ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `m _ x = _`. Rewrite using `[Algebra.smul_def, hmul, hq]`. Establish `hev : ∀ (c : K₀) τ, A.mulVecLin (fun i => algebraMap Qp LL (v.repr c i)) τ = τ c`. Introduce `c τ`. Use `conv_rhs => rw [← v.sum_repr c, map_sum]`.

Express the relevant statement in the definitionally equal form `∑ i, τ (v i) * algebraMap Qp LL (v.repr c i) = _`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, Algebra.smul_def, mul_comm]`. Use `choose e he using fun τ : K₀ →ₐ[Qp] LL => hsurj (Pi.single τ 1)`. Establish `hone : ∀ x, ∑ τ, μ (e τ) x = x`. Introduce `x`.

Establish `h1 : ∑ τ, e τ = fun i => algebraMap Qp LL (v.repr 1 i)`. Apply `hinj` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Rewrite using `[hev, map_sum]`. Simplify using `[he, Pi.single_apply]`.

Rewrite using `[← LinearMap.sum_apply, ← map_sum, h1, ← hsum]`. Simplify using `using hq 1 x`. Establish `heig : ∀ τ c x, m c (μ (e τ) x) = τ c • μ (e τ) x`. Introduce `τ c x`. Establish `h1 : (∑ i, e τ i • fun j => algebraMap Qp LL (v.repr (c * v i) j)) = τ c • e τ`.

Apply `hinj` to reduce the goal to its premises. Use function extensionality and compare the values at `τ'`. Establish `h2 : ∑ i, τ' (v i) * e τ i = (Pi.single τ 1 : _ → LL) τ'` using `congrFun (he τ) τ'`. Rewrite using `[map_sum, map_smul, he]`. Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply, hev, map_mul, smul_eq_mul]`.

Establish `h3 : ∑ i, e τ i * (τ' c * τ' (v i)) = τ' c * ∑ i, τ' (v i) * e τ i`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[h3, h2]`. Distinguish the cases in `h : τ' = τ`.

Rewrite using `[h]`. Simplify using `[h]`. Rewrite using `[← LinearMap.smul_apply, ← map_smul, ← h1, map_sum, LinearMap.sum_apply, hμ, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, ← hsum, hmul]`.

Establish `hon : ∀ τ τ', ∀ x ∈ L τ', μ (e τ) x = (Pi.single τ 1 : _ → LL) τ' • x`. Introduce `τ τ' x hx`. Establish `h2 : ∑ i, τ' (v i) * e τ i = (Pi.single τ 1 : _ → LL) τ'` using `congrFun (he τ) τ'`. Rewrite using `[hμ, ← h2, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [((hL τ' x).1 hx).2, smul_smul, mul_comm]`.

Establish `hmem : ∀ τ, ∀ x ∈ D, μ (e τ) x ∈ L τ` using `fun τ x hx => (hL τ _).2 ⟨by`. Rewrite using `[hμ]`. Conclude with `D.sum_mem fun i _ => D.smul_mem _ (hD _ _ hx), fun c => heig τ c x⟩`. Set `F : D →ₗ[LL] ∀ τ, L τ` to `LinearMap.pi fun τ => (μ (e τ)).restrict (hmem τ)`. Establish `hF : ∀ x τ, (F x τ : M) = μ (e τ) x` using `fun _ _ => rfl`.

Establish `hb : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hone x, ← hone y]`.

Conclude with `Finset.sum_congr rfl fun τ _ => by rw [← hF, ← hF, h]`. Introduce `y`. Use `⟨⟨∑ τ, (y τ : M), D.sum_mem fun τ _ => ((hL τ _).1 (y τ).2).1⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hF, map_sum, Finset.sum_congr rfl fun τ' _ => hon τ τ' _ (y τ').2]`. Simplify using `[Pi.single_apply]`. Use `haveI : ∀ τ, Module.Finite LL (L τ) := fun τ => Submodule.finiteDimensional_of_le (S₂ := D) fun x hx => ((hL τ x).1 hx).1`. Rewrite using `[(LinearEquiv.ofBijective F hb).finrank_eq, Module.finrank_pi_fintype]`.
-/
theorem finrank_eq_sum_letters [FiniteDimensional Qp K₀] [Fintype (K₀ →ₐ[Qp] LL)]
    (hc : Fintype.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) {M : Type} [AddCommGroup M] [Module LL M]
    (m : K₀ → M →ₗ[LL] M) (hadd : ∀ a b x, m (a + b) x = m a x + m b x)
    (hmul : ∀ a b x, m (a * b) x = m a (m b x))
    (hq : ∀ (q : Qp) x, m (algebraMap Qp K₀ q) x = algebraMap Qp LL q • x)
    (D : Submodule LL M) [Module.Finite LL D] (hD : ∀ a, ∀ x ∈ D, m a x ∈ D)
    (L : (K₀ →ₐ[Qp] LL) → Submodule LL M) (hL : ∀ τ x, x ∈ L τ ↔ x ∈ D ∧ ∀ c, m c x = τ c • x) :
    finrank LL D = ∑ τ, finrank LL (L τ) := by
  classical
  let v := Module.finBasis Qp K₀
  let A : Matrix (K₀ →ₐ[Qp] LL) (Fin (finrank Qp K₀)) LL := fun τ i => τ (v i)
  have hA : LinearIndependent LL A.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    refine Fintype.linearIndependent_iff.1 (linearIndependent_algHom_toLinearMap Qp K₀ LL) c ?_
    refine v.ext fun i => ?_
    simpa [A, Matrix.row] using congrFun hc0 i
  have hsurj : Function.Surjective A.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have := hA.rank_matrix
    rw [Matrix.rank] at this
    rw [this, finrank_fintype_fun_eq_card]
  have hinj : Function.Injective A.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hc])).2 hsurj
  let μ : (Fin (finrank Qp K₀) → LL) →ₗ[LL] (M →ₗ[LL] M) := Fintype.linearCombination LL fun i => m (v i)
  have hμ : ∀ a x, μ a x = ∑ i, a i • m (v i) x := fun a x => by
    simp [μ, Fintype.linearCombination_apply]
  have hsum : ∀ (c : K₀) x, m c x = μ (fun i => algebraMap Qp LL (v.repr c i)) x := by
    intro c x
    let f : K₀ →+ M := AddMonoidHom.mk' (fun a => m a x) fun a b => hadd a b x
    change f c = _
    conv_lhs => rw [← v.sum_repr c, map_sum]
    rw [hμ]
    refine Finset.sum_congr rfl fun i _ => ?_
    change m _ x = _
    rw [Algebra.smul_def, hmul, hq]
  have hev : ∀ (c : K₀) τ, A.mulVecLin (fun i => algebraMap Qp LL (v.repr c i)) τ = τ c := by
    intro c τ
    conv_rhs => rw [← v.sum_repr c, map_sum]
    change ∑ i, τ (v i) * algebraMap Qp LL (v.repr c i) = _
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Algebra.smul_def, mul_comm]
  choose e he using fun τ : K₀ →ₐ[Qp] LL => hsurj (Pi.single τ 1)
  have hone : ∀ x, ∑ τ, μ (e τ) x = x := by
    intro x
    have h1 : ∑ τ, e τ = fun i => algebraMap Qp LL (v.repr 1 i) := by
      apply hinj
      funext τ
      rw [hev, map_sum]
      simp [he, Pi.single_apply]
    rw [← LinearMap.sum_apply, ← map_sum, h1, ← hsum]
    simpa using hq 1 x
  have heig : ∀ τ c x, m c (μ (e τ) x) = τ c • μ (e τ) x := by
    intro τ c x
    have h1 : (∑ i, e τ i • fun j => algebraMap Qp LL (v.repr (c * v i) j)) = τ c • e τ := by
      apply hinj
      funext τ'
      have h2 : ∑ i, τ' (v i) * e τ i = (Pi.single τ 1 : _ → LL) τ' := congrFun (he τ) τ'
      rw [map_sum, map_smul, he]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, hev, map_mul, smul_eq_mul]
      have h3 : ∑ i, e τ i * (τ' c * τ' (v i)) = τ' c * ∑ i, τ' (v i) * e τ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h3, h2]
      by_cases h : τ' = τ
      · rw [h]
      · simp [h]
    rw [← LinearMap.smul_apply, ← map_smul, ← h1, map_sum, LinearMap.sum_apply, hμ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, ← hsum, hmul]
  have hon : ∀ τ τ', ∀ x ∈ L τ', μ (e τ) x = (Pi.single τ 1 : _ → LL) τ' • x := by
    intro τ τ' x hx
    have h2 : ∑ i, τ' (v i) * e τ i = (Pi.single τ 1 : _ → LL) τ' := congrFun (he τ) τ'
    rw [hμ, ← h2, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [((hL τ' x).1 hx).2, smul_smul, mul_comm]
  have hmem : ∀ τ, ∀ x ∈ D, μ (e τ) x ∈ L τ := fun τ x hx => (hL τ _).2 ⟨by
    rw [hμ]
    exact D.sum_mem fun i _ => D.smul_mem _ (hD _ _ hx), fun c => heig τ c x⟩
  let F : D →ₗ[LL] ∀ τ, L τ := LinearMap.pi fun τ => (μ (e τ)).restrict (hmem τ)
  have hF : ∀ x τ, (F x τ : M) = μ (e τ) x := fun _ _ => rfl
  have hb : Function.Bijective F := by
    constructor
    · intro x y h
      apply Subtype.ext
      rw [← hone x, ← hone y]
      exact Finset.sum_congr rfl fun τ _ => by rw [← hF, ← hF, h]
    · intro y
      refine ⟨⟨∑ τ, (y τ : M), D.sum_mem fun τ _ => ((hL τ _).1 (y τ).2).1⟩, ?_⟩
      funext τ
      apply Subtype.ext
      rw [hF, map_sum, Finset.sum_congr rfl fun τ' _ => hon τ τ' _ (y τ').2]
      simp [Pi.single_apply]
  haveI : ∀ τ, Module.Finite LL (L τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := D) fun x hx => ((hL τ x).1 hx).1
  rw [(LinearEquiv.ofBijective F hb).finrank_eq, Module.finrank_pi_fintype]

/- English proof (translation)
Introduce `hc V _ _ _ _ _ ρ h τ`. Use `haveI := PD.finK₀`. Take `⟨h1, -⟩` from `finite_le PD hf ρ`. Use `⟨Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left, ?_⟩` and prove the remaining obligations. Establish `hle : ∀ (n : ℕ) (τ τ' : K₀ →ₐ[Qp] LL), (∀ c, τ' c = τ (PD.σ^[n] c)) → finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `τ τ' h`. Rewrite using `[show τ' = τ from AlgHom.ext h]`.

Consider the case `succ n ih`. Introduce `τ τ' h`. Conclude with `(ih (τ.comp PD.σ) τ' fun c => by rw [h, Function.iterate_succ_apply']; rfl).trans (letter_le PD ρ τ _ fun _ => rfl)`. Establish `heq : ∀ τ', finrank LL ↥(DcrisL PD ρ τ') = finrank LL ↥(DcrisL PD ρ τ)` using `fun τ' => by`. Take `⟨n, hn⟩` from `exists_pow_sigma PD LL hc τ τ'`.

Take `⟨n', hn'⟩` from `exists_pow_sigma PD LL hc τ' τ`. Conclude with `le_antisymm (hle n _ _ hn) (hle n' _ _ hn')`. Rewrite `hc` using `[Nat.card_eq_fintype_card]`. Establish `hs` using `finrank_eq_sum_letters hc (fun c => mB LL (algebraMap K₀ B c)) (fun a b x => by rw [map_add, mB_add]) (fun a b x => by rw [map_mul, mB_mul]) (fun q (x : V ⊗[Qp] B) => by`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v b`. Rewrite using `[← IsScalarTower.algebraMap_apply, algebraMap_smul, ← tmul_smul, Algebra.smul_def]`. Both sides reduce to the same expression. Consider the case `add a b ha hb => simp only [map_add, smul_add, ha, hb])`.

Use the proof step `(Dcris PD ρ) (fun a x hx => (mK PD ρ a ⟨x, hx⟩).2) (DcrisL PD ρ) (mem_DcrisL PD ρ)`. Simplify using `only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc] at hs`. Unfold `IsCrys at h`. Conclude with `Nat.eq_of_mul_eq_mul_left finrank_pos (hs.symm.trans h)`.
-/
theorem letterDim (hf : FracInv PD) : LetterDim PD LL := by
  intro hc V _ _ _ _ _ ρ h τ
  haveI := PD.finK₀
  obtain ⟨h1, -⟩ := finite_le PD hf ρ
  refine ⟨Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left, ?_⟩
  have hle : ∀ (n : ℕ) (τ τ' : K₀ →ₐ[Qp] LL), (∀ c, τ' c = τ (PD.σ^[n] c)) →
      finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ) := by
    intro n
    induction n with
    | zero =>
      intro τ τ' h
      rw [show τ' = τ from AlgHom.ext h]
    | succ n ih =>
      intro τ τ' h
      exact (ih (τ.comp PD.σ) τ' fun c => by rw [h, Function.iterate_succ_apply']; rfl).trans
        (letter_le PD ρ τ _ fun _ => rfl)
  have heq : ∀ τ', finrank LL ↥(DcrisL PD ρ τ') = finrank LL ↥(DcrisL PD ρ τ) := fun τ' => by
    obtain ⟨n, hn⟩ := exists_pow_sigma PD LL hc τ τ'
    obtain ⟨n', hn'⟩ := exists_pow_sigma PD LL hc τ' τ
    exact le_antisymm (hle n _ _ hn) (hle n' _ _ hn')
  rw [Nat.card_eq_fintype_card] at hc
  have hs := finrank_eq_sum_letters hc (fun c => mB LL (algebraMap K₀ B c))
    (fun a b x => by rw [map_add, mB_add]) (fun a b x => by rw [map_mul, mB_mul])
    (fun q (x : V ⊗[Qp] B) => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        rw [← IsScalarTower.algebraMap_apply, algebraMap_smul, ← tmul_smul, Algebra.smul_def]
        rfl
      | add a b ha hb => simp only [map_add, smul_add, ha, hb])
    (Dcris PD ρ) (fun a x hx => (mK PD ρ a ⟨x, hx⟩).2) (DcrisL PD ρ) (mem_DcrisL PD ρ)
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc] at hs
  unfold IsCrys at h
  exact Nat.eq_of_mul_eq_mul_left finrank_pos (hs.symm.trans h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨invariantsEq PD, ⟨fun _ _ _ _ _ _ ρ => (finite_le PD hf ρ).2, fun _ _ _ _ _ _ ρ => (finite_le PD hf ρ).1⟩, fun _ _ _ _ _ _ ρ h => comparison_bijective PD hf hu ρ h, subCrys PD LL hf, quotCrys PD LL hf hu, sumCrys PD LL hf hu, tensorCrys PD LL hf hu, dualCrys PD LL hf hu, dcrisEx …`.
-/
theorem formalismFor (hf : FracInv PD) (hu : LineUnit PD) : FormalismFor PD LL :=
  ⟨invariantsEq PD,
    ⟨fun _ _ _ _ _ _ ρ => (finite_le PD hf ρ).2, fun _ _ _ _ _ _ ρ => (finite_le PD hf ρ).1⟩,
    fun _ _ _ _ _ _ ρ h => comparison_bijective PD hf hu ρ h, subCrys PD LL hf, quotCrys PD LL hf hu,
    sumCrys PD LL hf hu, tensorCrys PD LL hf hu, dualCrys PD LL hf hu, dcrisExact PD LL hf,
    letterDim PD LL hf⟩

end Generic

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : GlobalTheory.Per.Core l}

/- English proof (translation)
The claim follows from `T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1`.
-/
theorem isField_of_tied (T : LocTied l P AI) : IsField P.R.BdR :=
  T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1

/- English proof (translation)
The claim follows from `letI : Field P.R.BdR := (isField_of_tied T).toField (P.PD K).ι_inj.isDomain (P.PD K).ι.toRingHom`.
-/
theorem isDomain_of_tied (T : LocTied l P AI) (K : FinExt l) : IsDomain P.R.B :=
  letI : Field P.R.BdR := (isField_of_tied T).toField
  (P.PD K).ι_inj.isDomain (P.PD K).ι.toRingHom

/- English proof (translation)
Introduce `b b' hb h`. Establish `hb' : (P.PD K).ι b ≠ 0` using `fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm))`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ↥K.1, (P.PD K).ι b' = algebraMap ↥K.1 P.R.BdR c * (P.PD K).ι b := by`. Take `⟨u, hu⟩` from `(isField_of_tied T).mul_inv_cancel hb'`. Take `⟨c, hc⟩` from `(P.PD K).invdR ((P.PD K).ι b' * u) fun g => by`.

Establish `h1` using `congrArg (P.PD K).ι (h g)`. Rewrite `h1` using `[map_mul, map_mul, (P.PD K).ι_comm, (P.PD K).ι_comm]`. Establish `h2` using `congrArg ((P.PD K).actdR g) hu`. Rewrite `h2` using `[map_mul, map_one]`. Rewrite using `[map_mul]`.

Take the linear combination `(u * (P.PD K).actdR g u) * h1 + ((P.PD K).ι b' * u) * h2 - ((P.PD K).actdR g ((P.PD K).ι b') * (P.PD K).actdR g u) * hu`. Conclude with `⟨c, by rw [hc, mul_assoc, mul_comm u, hu, mul_one]⟩`. Establish `hcU : (c : Om l) ∈ MaximalUnramifiedExtension l`. Assume the negation of the conclusion as `hn`. Establish `hli : LinearIndependent ↥(MaximalUnramifiedExtension l) ![(1 : Om l), (c : Om l)]`.

Rewrite using `[LinearIndependent.pair_iff' one_ne_zero]`. Introduce `a ha`. Apply `hn` to reduce the goal to its premises. Rewrite using `[← ha, Algebra.smul_def, mul_one]`. Conclude with `a.2`.

Establish `h0` using `hinj 2 _ hli ![T.eB b', - T.eB b] (by`. Establish `h1` using `congrArg T.eD hc`. Rewrite `h1` using `[map_mul, P.PD_ι, P.PD_ι, hfit.ι, hfit.ι]`. Establish `h2 : T.eD (algebraMap ↥K.1 P.R.BdR c) = C.oD (c : Om l)` using `hfit.o _`. Rewrite `h1` using `[h2]`.

Simplify using `[Fin.sum_univ_two, h1]) 1`. Apply `hb` to reduce the goal to its premises. Apply `T.eB.injective` to reduce the goal to its premises. Simplify using `using h0`. Use `⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, AlgHom.commutes, hc]`. Both sides reduce to the same expression.
-/
theorem fracInv (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K : FinExt l) : FracInv (P.PD K) := by
  intro b b' hb h
  have hb' : (P.PD K).ι b ≠ 0 := fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ : ∃ c : ↥K.1, (P.PD K).ι b' = algebraMap ↥K.1 P.R.BdR c * (P.PD K).ι b := by
    obtain ⟨u, hu⟩ := (isField_of_tied T).mul_inv_cancel hb'
    obtain ⟨c, hc⟩ := (P.PD K).invdR ((P.PD K).ι b' * u) fun g => by
      have h1 := congrArg (P.PD K).ι (h g)
      rw [map_mul, map_mul, (P.PD K).ι_comm, (P.PD K).ι_comm] at h1
      have h2 := congrArg ((P.PD K).actdR g) hu
      rw [map_mul, map_one] at h2
      rw [map_mul]
      linear_combination (u * (P.PD K).actdR g u) * h1 + ((P.PD K).ι b' * u) * h2 -
        ((P.PD K).actdR g ((P.PD K).ι b') * (P.PD K).actdR g u) * hu
    exact ⟨c, by rw [hc, mul_assoc, mul_comm u, hu, mul_one]⟩
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    by_contra hn
    have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) ![(1 : Om l), (c : Om l)] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      apply hn
      rw [← ha, Algebra.smul_def, mul_one]
      exact a.2
    have h0 := hinj 2 _ hli ![T.eB b', - T.eB b] (by
      have h1 := congrArg T.eD hc
      rw [map_mul, P.PD_ι, P.PD_ι, hfit.ι, hfit.ι] at h1
      have h2 : T.eD (algebraMap ↥K.1 P.R.BdR c) = C.oD (c : Om l) := hfit.o _
      rw [h2] at h1
      simp [Fin.sum_univ_two, h1]) 1
    apply hb
    apply T.eB.injective
    simpa using h0
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

/- English proof (translation)
Introduce `b hb h`. Establish `h1` using `hreg K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hg => by`. Take `⟨x, hx⟩` from `h ⟨g, hg⟩`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[P.PD_actB]`.

Rewrite using `[← T.actB, hx, map_mul, IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hfit.u]`. Both sides reduce to the same expression. Simplify using `using h1.map T.eB.symm`.
-/
theorem lineUnit (hfit : GlobalTheory.MemLoc.Fits T C) (hreg : C.Regular) (K : FinExt l) : LineUnit (P.PD K) := by
  intro b hb h
  have h1 := hreg K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hg => by
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    refine ⟨x, ?_⟩
    rw [P.PD_actB] at hx
    rw [← T.actB, hx, map_mul, IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hfit.u]
    rfl
  simpa using h1.map T.eB.symm

end Tied

/- English proof (translation)
Take `⟨T⟩` from `hs`. Take `⟨C, hfit⟩` from `GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T`. Rewrite using `[fontaineFormalism_iff]`. Introduce `K LL`. Use `haveI := LL.2`.

Use `haveI := isDomain_of_tied T K`. Conclude with `formalismFor (P.PD K) ↥LL.1 (fracInv hfit (h C).1 K) (lineUnit hfit (h C).2 K)`.
-/
theorem fontaineFormalism_of_regular (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (h : ∀ C : GlobalTheory.Per.Core l, C.TensorInj ∧ C.Regular) (hs : GlobalTheory.Per.IsStd P AI) :
    FontaineFormalism l P := by
  obtain ⟨T⟩ := hs
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  rw [fontaineFormalism_iff]
  intro K LL
  haveI := LL.2
  haveI := isDomain_of_tied T K
  exact formalismFor (P.PD K) ↥LL.1 (fracInv hfit (h C).1 K) (lineUnit hfit (h C).2 K)

/- English proof (translation)
The claim follows from `fontaineFormalism_of_regular l P AI (fun C => ⟨hF.tensorInj C, hF.regular C⟩) hs`.
-/
theorem fontaineFormalism (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P) (hs : GlobalTheory.Per.IsStd P AI) : FontaineFormalism l P :=
  fontaineFormalism_of_regular l P AI (fun C => ⟨hF.tensorInj C, hF.regular C⟩) hs

/- English proof (translation)
The claim follows from `(fontaineFormalismTensor_equiv l P).2 ((fontaineFormalism_equiv l P).1 (fontaineFormalism hF l P AI hs))`.
-/
theorem fontaineFormalismTensor (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P) (hs : GlobalTheory.Per.IsStd P AI) : FontaineFormalismTensor l P :=
  (fontaineFormalismTensor_equiv l P).2 ((fontaineFormalism_equiv l P).1 (fontaineFormalism hF l P AI hs))

end GlobalTheory.RegularRing
