import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal

noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.LatticeRep

variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]

def Transl (W : X → M →ₗ[ℂ] M) (A : Submodule R X) : Set M := {m | ∃ x v, Fixes W A v ∧ m = W x v}

def IsLatSystem (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X)
    (ρ : Γ →* Module.End R X) : Prop :=
  IsHeis σ w γ W ∧ GoodNorm σ lam ∧ SelfDual γ A ∧ Submodule.span ℂ (Transl W A) = ⊤ ∧
    (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) ∧ ∀ g, idx A (A.map (ρ g)) ≠ 0

def IsLatRep (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X) (ρ : Γ →* Module.End R X)
    (Om : Γ →* Module.End ℂ M) : Prop :=
  (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g v, Fixes W A v → Om g v = normOp lam W A (A.map (ρ g)) v

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
/- English proof (translation)
Establish `hm : m ∈ Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A)`. Rewrite using `[hs]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨x, v, hv, rfl⟩` from `hy`. Conclude with `mem x v hv`. Consider the case `zero => exact zero`. Consider the case `add a b _ _ ha hb => exact add a b ha hb`. Consider the case `smul c a _ ha => exact smul c a ha`.
-/
theorem _root_.GlobalTheory.LatticeRep.transl_induction (hs : Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) = ⊤) {p : M → Prop}
    (mem : ∀ x v, _root_.GlobalTheory.FinWeil.Fixes W A v → p (W x v)) (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (smul : ∀ (c : ℂ) a, p a → p (c • a)) (m : M) : p m := by
  have hm : m ∈ Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) := by
    rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, v, hv, rfl⟩ := hy
    exact mem x v hv
  | zero => exact zero
  | add a b _ _ ha hb => exact add a b ha hb
  | smul c a _ ha => exact smul c a ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Conclude with `ha`. Introduce `hx`.

Conclude with `⟨_, hx, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩`.
-/
theorem mem_map_iff (ρ : Γ →* Module.End R X) (g : Γ) (A : Submodule R X) (x : X) :
    x ∈ A.map (ρ g) ↔ ρ g⁻¹ x ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]; exact ha
  · intro hx
    exact ⟨_, hx, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩

/- English proof (translation)
Take `⟨-, -, hA, -, hρ, -⟩` from `h`. Establish `e : ∀ x, ρ g (ρ g⁻¹ x) = x` using `fun x => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Introduce `x`. Rewrite using `[mem_map_iff, hA]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `hx _ ⟨a, ha, rfl⟩`. Rewrite using `[← hx a ha, ← hρ g (ρ g⁻¹ x), e]`. Introduce `hx a ha`. Rewrite using `[← hρ g, e]`.

Conclude with `hx _ ⟨a, ha, rfl⟩`.
-/
theorem IsLatSystem.selfDual_map (h : IsLatSystem σ w γ W lam A ρ) (g : Γ) : SelfDual γ (A.map (ρ g)) := by
  obtain ⟨-, -, hA, -, hρ, -⟩ := h
  have e : ∀ x, ρ g (ρ g⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro x
  rw [mem_map_iff, hA]
  constructor
  · rintro hx _ ⟨a, ha, rfl⟩
    rw [← hx a ha, ← hρ g (ρ g⁻¹ x), e]
  · intro hx a ha
    rw [← hρ g, e]
    exact hx _ ⟨a, ha, rfl⟩

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.FinWeil.sumOp`. Establish `hz : ∀ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, q = 0`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H b => exact (QuotientAddGroup.eq_zero_iff b).mpr (hBA b.2)`.

Rewrite using `[finsum_eq_single _ 0 (fun q hq => absurd (hz q) hq)]`. Conclude with `hv _ (hBA (Quotient.out (0 : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)).2)`.
-/
private theorem sumOp_eq_self_of_le {B : Submodule R X} (hBA : B ≤ A) {v : M}
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : _root_.GlobalTheory.FinWeil.sumOp W A B v = v := by
  unfold _root_.GlobalTheory.FinWeil.sumOp
  have hz : ∀ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b => exact (QuotientAddGroup.eq_zero_iff b).mpr (hBA b.2)
  rw [finsum_eq_single _ 0 (fun q hq => absurd (hz q) hq)]
  exact hv _ (hBA (Quotient.out (0 : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)).2)

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in

/- English proof (translation)
Rewrite using `[hO.2 g v hv]`. Unfold `_root_.GlobalTheory.FinWeil.normOp _root_.GlobalTheory.FinWeil.idx`. Establish `hidx : A.toAddSubgroup.relIndex (A.map (ρ g)).toAddSubgroup = 1` using `AddSubgroup.relIndex_eq_one.mpr hg`. Rewrite using `[hidx, map_one, inv_one, one_smul]`. Conclude with `sumOp_eq_self_of_le hg hv`.
-/
theorem _root_.GlobalTheory.LatticeRep.IsLatRep.fix_of_map_le (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) {g : Γ}
    (hg : A.map (ρ g) ≤ A) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : Om g v = v := by
  rw [hO.2 g v hv]
  unfold _root_.GlobalTheory.FinWeil.normOp _root_.GlobalTheory.FinWeil.idx
  have hidx : A.toAddSubgroup.relIndex (A.map (ρ g)).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr hg
  rw [hidx, map_one, inv_one, one_smul]
  exact sumOp_eq_self_of_le hg hv

/- English proof (translation)
Use `transl_induction h.2.2.2.1 (p := fun m => Om g m = m) (fun x v hv => ?_) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb]) (fun c a ha => by rw [map_smul, ha]) m` and prove the remaining obligations. Rewrite using `[hO.1, hg, hO.fix_of_map_le h _ hv]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Rewrite using `[hg]`. Conclude with `ha`.
-/
theorem IsLatRep.eq_self_of_trivial (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) {g : Γ}
    (hg : ∀ x, ρ g x = x) (m : M) : Om g m = m := by
  refine transl_induction h.2.2.2.1 (p := fun m => Om g m = m) (fun x v hv => ?_) (map_zero _)
    (fun a b ha hb => by rw [map_add, ha, hb]) (fun c a ha => by rw [map_smul, ha]) m
  rw [hO.1, hg, hO.fix_of_map_le h _ hv]
  rintro _ ⟨a, ha, rfl⟩
  rw [hg]; exact ha

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.FinWeil.idx at h`. Establish `: Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)` using `AddSubgroup.index_ne_zero_iff_finite.mp h`. Unfold `_root_.GlobalTheory.FinWeil.sumOp`. Rewrite using `[map_finsum φ (Set.toFinite _)]`. Simplify using `only [hφ]`.
-/
private theorem map_sumOp_of_commute {B : Submodule R X} (φ : M →ₗ[ℂ] M)
    (h : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) (hφ : ∀ x m, φ (W x m) = W x (φ m)) (v : M) :
    φ (_root_.GlobalTheory.FinWeil.sumOp W A B v) = _root_.GlobalTheory.FinWeil.sumOp W A B (φ v) := by
  unfold _root_.GlobalTheory.FinWeil.idx at h
  have : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    AddSubgroup.index_ne_zero_iff_finite.mp h
  unfold _root_.GlobalTheory.FinWeil.sumOp
  rw [map_finsum φ (Set.toFinite _)]
  simp only [hφ]

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in

/- English proof (translation)
Use `_root_.GlobalTheory.LatticeRep.transl_induction (p := fun m => Om g (φ m) = φ (Om g m)) h.2.2.2.1 (fun x v hv => ?_) ?_ (fun a b ha hb => ?_) (fun c a ha => ?_) m` and prove the remaining obligations. Establish `hφv : _root_.GlobalTheory.FinWeil.Fixes W A (φ v)` using `fun a ha => by rw [← hφ, hv a ha]`. Rewrite using `[hφ, hO.1, hO.1, hO.2 g _ hφv, hO.2 g _ hv, hφ]`. Use `congr 1`. Unfold `_root_.GlobalTheory.FinWeil.normOp`.

Rewrite using `[map_smul, map_sumOp_of_commute φ (h.2.2.2.2.2 g) hφ]`. Simplify using the standard rewrite rules. Simplify using `only [map_add, ha, hb]`. Simplify using `only [map_smul, ha]`.
-/
theorem _root_.GlobalTheory.LatticeRep.IsLatRep.comm (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) (φ : M →ₗ[ℂ] M)
    (hφ : ∀ x m, φ (W x m) = W x (φ m)) (g : Γ) (m : M) : Om g (φ m) = φ (Om g m) := by
  refine _root_.GlobalTheory.LatticeRep.transl_induction (p := fun m => Om g (φ m) = φ (Om g m))
    h.2.2.2.1 (fun x v hv => ?_) ?_
    (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · have hφv : _root_.GlobalTheory.FinWeil.Fixes W A (φ v) := fun a ha => by rw [← hφ, hv a ha]
    rw [hφ, hO.1, hO.1, hO.2 g _ hφv, hO.2 g _ hv, hφ]
    congr 1
    unfold _root_.GlobalTheory.FinWeil.normOp
    rw [map_smul, map_sumOp_of_commute φ (h.2.2.2.2.2 g) hφ]
  · simp
  · simp only [map_add, ha, hb]
  · simp only [map_smul, ha]

/- English proof (translation)
Use `transl_induction h.2.2.2.1 (p := fun m => ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A → (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m) (fun x v hv => ?_) ⟨∅, Set.finite_empty, fun g _ _ => map_zero _⟩ (fun a b ha hb => ?_) (fun c a ha => ?_) m` and prove the remaining obligations. Use `⟨{x}, Set.finite_singleton x, fun g hg hx => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hx x rfl`. Establish `h3` using `h.1.comp x (ρ g x - x) v`. Rewrite `h3` using `[hv _ h1, h2, one_smul, add_sub_cancel]`.

Rewrite using `[hO.1, hO.fix_of_map_le h hg hv, h3]`. Take `⟨s, hs, h1⟩` from `ha`. Take `⟨t, ht, h2⟩` from `hb`. Conclude with `⟨s ∪ t, hs.union ht, fun g hg hx => by`. Rewrite using `[map_add, h1 g hg fun x hx' => hx x (Or.inl hx'), h2 g hg fun x hx' => hx x (Or.inr hx')]⟩`.

Take `⟨s, hs, h1⟩` from `ha`. Conclude with `⟨s, hs, fun g hg hx => by rw [map_smul, h1 g hg hx]⟩`.
-/
theorem IsLatRep.exists_stab (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) (m : M) :
    ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A → (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m := by
  refine transl_induction h.2.2.2.1 (p := fun m => ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A →
    (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m) (fun x v hv => ?_)
    ⟨∅, Set.finite_empty, fun g _ _ => map_zero _⟩ (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · refine ⟨{x}, Set.finite_singleton x, fun g hg hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx x rfl
    have h3 := h.1.comp x (ρ g x - x) v
    rw [hv _ h1, h2, one_smul, add_sub_cancel] at h3
    rw [hO.1, hO.fix_of_map_le h hg hv, h3]
  · obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    exact ⟨s ∪ t, hs.union ht, fun g hg hx => by
      rw [map_add, h1 g hg fun x hx' => hx x (Or.inl hx'), h2 g hg fun x hx' => hx x (Or.inr hx')]⟩
  · obtain ⟨s, hs, h1⟩ := ha
    exact ⟨s, hs, fun g hg hx => by rw [map_smul, h1 g hg hx]⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `N.exists_isCompl`. Set `e` to `Submodule.prodEquivOfIsCompl N C hC`. Set `P : Γ →* Module.End ℂ (N × C)` to `{ toFun := fun g => (O g).prodMap LinearMap.id map_one' := by rw [map_one]; exact LinearMap.prodMap_one map_mul' := fun g k => by rw [map_mul, LinearMap.prodMap_mul]; rfl }`. Use `⟨(e.conjRingEquiv.toMonoidHom).comp P, fun g m => ?_⟩` and prove the remaining obligations. Use `show e (P g (e.symm m)) = _`.

Rewrite using `[Submodule.prodEquivOfIsCompl_symm_apply_left]`. Simplify using `[P, e]`.
-/
theorem exists_extend {V : Type} [AddCommGroup V] [Module ℂ V] (N : Submodule ℂ V) (O : Γ →* Module.End ℂ N) :
    ∃ om : Γ →* Module.End ℂ V, ∀ g (m : N), om g m = O g m := by
  obtain ⟨C, hC⟩ := N.exists_isCompl
  let e := Submodule.prodEquivOfIsCompl N C hC
  let P : Γ →* Module.End ℂ (N × C) :=
    { toFun := fun g => (O g).prodMap LinearMap.id
      map_one' := by rw [map_one]; exact LinearMap.prodMap_one
      map_mul' := fun g k => by rw [map_mul, LinearMap.prodMap_mul]; rfl }
  refine ⟨(e.conjRingEquiv.toMonoidHom).comp P, fun g m => ?_⟩
  show e (P g (e.symm m)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [P, e]

end GlobalTheory.LatticeRep

end
