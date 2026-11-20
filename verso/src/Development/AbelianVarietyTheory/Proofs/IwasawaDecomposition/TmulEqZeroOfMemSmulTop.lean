import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineSummand

variable {O X k : Type} [CommRing O] [AddCommGroup X] [Module O X] [Field k] {p : ℕ} [CharP k p]

/- English proof (translation)
Use `show (TensorProduct.mk ℤ k X c) (p • y) = 0`. Rewrite using `[map_nsmul, TensorProduct.mk_apply, TensorProduct.smul_tmul', nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, TensorProduct.zero_tmul]`.
-/
theorem tmul_nsmul_eq_zero (c : k) (y : X) : c ⊗ₜ[ℤ] (p • y) = 0 := by
  show (TensorProduct.mk ℤ k X c) (p • y) = 0
  rw [map_nsmul, TensorProduct.mk_apply, TensorProduct.smul_tmul', nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    TensorProduct.zero_tmul]

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun x => c ⊗ₜ[ℤ] x = 0) hx (fun r hr n _ => ?_) fun x y hx hy => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Establish `e : (a * (p : O)) • n = p • (a • n)` using `by rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[e]`. Conclude with `tmul_nsmul_eq_zero c _`.

Simplify using `only [TensorProduct.tmul_add, hx, hy, add_zero]`.
-/
theorem tmul_eq_zero_of_mem_smul_top {x : X} (hx : x ∈ (Ideal.span {(p : O)} • ⊤ : Submodule O X)) (c : k) :
    c ⊗ₜ[ℤ] x = 0 := by
  refine Submodule.smul_induction_on (p := fun x => c ⊗ₜ[ℤ] x = 0) hx (fun r hr n _ => ?_) fun x y hx hy => ?_
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have e : (a * (p : O)) • n = p • (a • n) := by rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [e]
    exact tmul_nsmul_eq_zero c _
  · simp only [TensorProduct.tmul_add, hx, hy, add_zero]

variable (k) in

/- English proof (translation)
Set `g : X →ₗ[ℤ] X ⧸ P` to `P.mkQ.restrictScalars ℤ`. Establish `hex` using `lTensor_exact k (LinearMap.exact_subtype_ker_map g) P.mkQ_surjective`. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Use `(injective_iff_map_eq_zero _).2 fun y hy => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `(hex y).1 hy`.

Use `clear hy`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c x`. Rewrite using `[LinearMap.lTensor_tmul]`.

Conclude with `hP _ ((Submodule.Quotient.mk_eq_zero P).1 (LinearMap.mem_ker.1 x.2)) c`. Consider the case `add u v hu hv => rw [map_add, hu, hv, add_zero]`.
-/
theorem baseChange_mkQ_injective (P : Submodule O X) (hP : ∀ x ∈ P, ∀ c : k, c ⊗ₜ[ℤ] x = 0) :
    Function.Injective ((P.mkQ.restrictScalars ℤ).baseChange k) := by
  let g : X →ₗ[ℤ] X ⧸ P := P.mkQ.restrictScalars ℤ
  have hex := lTensor_exact k (LinearMap.exact_subtype_ker_map g) P.mkQ_surjective
  rw [LinearMap.baseChange_eq_ltensor]
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := (hex y).1 hy
  clear hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [LinearMap.lTensor_tmul]
    exact hP _ ((Submodule.Quotient.mk_eq_zero P).1 (LinearMap.mem_ker.1 x.2)) c
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

end GlobalTheory.LineSummand

namespace GlobalTheory.LineSummand

variable {O X k : Type} [CommRing O] [AddCommGroup X] [Module O X] [Field k] {p : ℕ} [CharP k p]

variable (k) in

/- English proof (translation)
Use `set ρb : O →+* Module.End k (k ⊗[ℤ] X) := baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)`. Set `bar : Submodule O (X ⧸ P) → Submodule k (k ⊗[ℤ] X)` to `fun m => Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ m ∧ s = 1 ⊗ₜ a}`. Establish `hρ : ∀ (a : O) (c : k) (x : X), ρb a (c ⊗ₜ x) = c ⊗ₜ (a • x)` using `fun a c x => by`. Simplify using `[ρb, baseChangeAction_apply, LinearMap.baseChange_tmul]`. Establish `hz : ∀ x ∈ P, (1 : k) ⊗ₜ[ℤ] x = 0` using `fun x hx => hPz x hx 1`.

Establish `hst : ∀ (m : Submodule O (X ⧸ P)) (a : O), ∀ x ∈ bar m, ρb a x ∈ bar m`. Introduce `m a x hx`. Use `(Submodule.span_le (p := (bar m).comap (ρb a))).2 (fun s hs => ?_) hx` and prove the remaining obligations. Take `⟨b, hb, rfl⟩` from `hs`. Use `show ρb a (1 ⊗ₜ b) ∈ bar m`.

Rewrite using `[hρ]`. Conclude with `Submodule.subset_span ⟨a • b, by rw [Submodule.Quotient.mk_smul]; exact m.smul_mem a hb, rfl⟩`. Establish `htop : bar l ⊔ bar l' = ⊤`. Use `Submodule.eq_top_iff'.2 fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => exact zero_mem _`. Consider the case `tmul c a`. Establish `e1 : c ⊗ₜ[ℤ] a = c • ((1 : k) ⊗ₜ[ℤ] a)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e1]`. Use `Submodule.smul_mem _ c ?_` and prove the remaining obligations.

Establish `hm : (Submodule.Quotient.mk a : X ⧸ P) ∈ l ⊔ l'` using `h.sup_eq_top ▸ Submodule.mem_top`. Take `⟨u, hu, u', hu', e2⟩` from `Submodule.mem_sup.1 hm`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective P u`. Take `⟨b', rfl⟩` from `Submodule.Quotient.mk_surjective P u'`. Establish `hd : a - b - b' ∈ P`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, ← e2]`. Normalize the expressions using the abelian group laws. Establish `e3 : (1 : k) ⊗ₜ[ℤ] a = 1 ⊗ₜ b + 1 ⊗ₜ b' + 1 ⊗ₜ (a - b - b')`. Rewrite using `[← TensorProduct.tmul_add, ← TensorProduct.tmul_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[e3, hz _ hd, add_zero]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨b, hu, rfl⟩) (Submodule.subset_span ⟨b', hu', rfl⟩)`. Consider the case `add x y hx hy => exact add_mem hx hy`. Set `π : X →ₗ[ℤ] X ⧸ P` to `P.mkQ.restrictScalars ℤ`.

Set `proj : (X ⧸ P) →ₗ[O] l` to `LinearMap.ofIsCompl h LinearMap.id 0`. Set `q : X →ₗ[ℤ] l` to `(proj ∘ₗ P.mkQ).restrictScalars ℤ`. Set `ls : l →ₗ[ℤ] X ⧸ P` to `l.subtype.restrictScalars ℤ`. Establish `hπ : Function.Injective (π.baseChange k)` using `baseChange_mkQ_injective k P hPz`. Establish `h1 : bar l ≤ LinearMap.eqLocus (π.baseChange k) ((ls.baseChange k) ∘ₗ (q.baseChange k))`.

Use `Submodule.span_le.2 fun s hs => ?_` and prove the remaining obligations. Take `⟨b, hb, rfl⟩` from `hs`. Use `show π.baseChange k (1 ⊗ₜ b) = ls.baseChange k (q.baseChange k (1 ⊗ₜ b))`. Rewrite using `[LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]`. Use `congr 1`.

Use `show Submodule.Quotient.mk b = ((proj (Submodule.Quotient.mk b) : l) : X ⧸ P)`. Use `LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩` as an intermediate fact. Conclude with `(congrArg Subtype.val this).symm`. Establish `h2 : bar l' ≤ LinearMap.ker (q.baseChange k)`. Use `Submodule.span_le.2 fun s hs => ?_` and prove the remaining obligations.

Take `⟨b, hb, rfl⟩` from `hs`. Use `show q.baseChange k (1 ⊗ₜ b) = 0`. Rewrite using `[LinearMap.baseChange_tmul]`. Use `LinearMap.ofIsCompl_apply_right h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩` as an intermediate fact. Use `show (1 : k) ⊗ₜ[ℤ] proj (Submodule.Quotient.mk b) = 0`.

Rewrite using `[this, LinearMap.zero_apply, TensorProduct.tmul_zero]`. Establish `hcompl : IsCompl (bar l) (bar l')`. Use `⟨Submodule.disjoint_def.2 fun x hx hx' => hπ ?_, codisjoint_iff.2 htop⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_eqLocus.1 (h1 hx), LinearMap.comp_apply, LinearMap.mem_ker.1 (h2 hx'), map_zero, map_zero]`. Take `⟨a₀, ha₀⟩` from `Submodule.Quotient.mk_surjective P (e.symm 1 : X ⧸ P)`.

Establish `hmk : ∀ c : O, (Submodule.Quotient.mk (c • a₀) : X ⧸ P) = (e.symm (Ideal.Quotient.mk _ c) : X ⧸ P)`. Introduce `c`. Establish `: (Ideal.Quotient.mk (Ideal.span {(p : O)}) c) = c • 1`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[Submodule.Quotient.mk_smul, ha₀, this, map_smul, Submodule.coe_smul]`. Use `⟨bar l', 1 ⊗ₜ a₀, hcompl, hst l, hst l', le_antisymm ?_ ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.span_le.2 fun s hs => ?_` and prove the remaining obligations. Take `⟨b, hb, rfl⟩` from `hs`. Take `⟨c, hc⟩` from `Ideal.Quotient.mk_surjective (e ⟨_, hb⟩)`.

Establish `hd : b - c • a₀ ∈ P`. Rewrite using `[← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, hmk, hc, LinearEquiv.symm_apply_apply, sub_self]`. Establish `e4 : (1 : k) ⊗ₜ[ℤ] b = ρb c (1 ⊗ₜ a₀) + 1 ⊗ₜ (b - c • a₀)`. Rewrite using `[hρ, ← TensorProduct.tmul_add, add_sub_cancel]`. Rewrite using `[SetLike.mem_coe, e4, hz _ hd, add_zero]`.

Conclude with `Submodule.subset_span ⟨c, rfl⟩`. Use `Submodule.span_le.2 fun s hs => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hs`. Use `show ρb c (1 ⊗ₜ a₀) ∈ bar l`. Rewrite using `[hρ]`.

Conclude with `Submodule.subset_span ⟨c • a₀, by rw [hmk]; exact (e.symm _).2, rfl⟩`. Set `fA : O →ₗ[ℤ] X` to `(LinearMap.toSpanSingleton O X a₀).restrictScalars ℤ`. Establish `hT : ∀ t, tensorAction ρb t (1 ⊗ₜ a₀) = fA.baseChange k t`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul c a`. Rewrite using `[tensorAction_tmul, hρ, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Consider the case `add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add]`.

Set `mO : O →ₗ[ℤ] O ⧸ Ideal.span {(p : O)}` to `(Submodule.mkQ (Ideal.span {(p : O)})).restrictScalars ℤ`. Set `es : (O ⧸ Ideal.span {(p : O)}) →ₗ[ℤ] l` to `(e.symm : (O ⧸ Ideal.span {(p : O)}) →ₗ[O] l).restrictScalars ℤ`. Establish `key : ∀ t, π.baseChange k (fA.baseChange k t) = ls.baseChange k (es.baseChange k (mO.baseChange k t))`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul c a`. Simplify using `only [LinearMap.baseChange_tmul]`. Use `congr 1`. Conclude with `hmk a`.

Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Establish `hmO : Function.Injective (mO.baseChange k)`. Use `baseChange_mkQ_injective k (Ideal.span {(p : O)}) fun x hx c => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Establish `e5 : a * (p : O) = p • a` using `by rw [mul_comm, ← nsmul_eq_mul]`.

Rewrite using `[e5]`. Conclude with `tmul_nsmul_eq_zero c a`. Establish `hes : Function.Injective (es.baseChange k)`. Use `Function.LeftInverse.injective (g := ((e : l →ₗ[O] O ⧸ Ideal.span {(p : O)}).restrictScalars ℤ).baseChange k) fun y => ?_` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul c u => simp [es]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Establish `hls : Function.Injective (ls.baseChange k)`. Use `Function.LeftInverse.injective (g := (proj.restrictScalars ℤ).baseChange k) fun y => ?_` and prove the remaining obligations.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c u`. Simplify using `only [LinearMap.baseChange_tmul]`. Use `congr 1`.

Conclude with `LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) u`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Introduce `t ht`. Rewrite `ht` using `[hT]`. Establish `h0 : ls.baseChange k (es.baseChange k (mO.baseChange k t)) = 0` using `by rw [← key, ht, map_zero]`.

Conclude with `(injective_iff_map_eq_zero _).1 hmO _ ((injective_iff_map_eq_zero _).1 hes _ ((injective_iff_map_eq_zero _).1 hls _ h0))`.
-/
theorem line_summand (P : Submodule O X) (hPz : ∀ x ∈ P, ∀ c : k, c ⊗ₜ[ℤ] x = 0) (l l' : Submodule O (X ⧸ P))
    (h : IsCompl l l')
    (e : l ≃ₗ[O] (O ⧸ Ideal.span {(p : O)})) :
    ∃ (M' : Submodule k (k ⊗[ℤ] X)) (n₀ : k ⊗[ℤ] X),
      IsCompl (Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a}) M' ∧
      (∀ a, ∀ x ∈ Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a},
        baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a x ∈
          Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a}) ∧
      (∀ a, ∀ x ∈ M', baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a x ∈ M') ∧
      Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a} =
        Submodule.span k (Set.range fun a => baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a n₀) ∧
      ∀ t : k ⊗[ℤ] O, tensorAction (baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)) t n₀ = 0 → t = 0 := by
  set ρb : O →+* Module.End k (k ⊗[ℤ] X) := baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)
  let bar : Submodule O (X ⧸ P) → Submodule k (k ⊗[ℤ] X) := fun m =>
    Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ m ∧ s = 1 ⊗ₜ a}
  have hρ : ∀ (a : O) (c : k) (x : X), ρb a (c ⊗ₜ x) = c ⊗ₜ (a • x) := fun a c x => by
    simp [ρb, baseChangeAction_apply, LinearMap.baseChange_tmul]
  have hz : ∀ x ∈ P, (1 : k) ⊗ₜ[ℤ] x = 0 := fun x hx => hPz x hx 1

  have hst : ∀ (m : Submodule O (X ⧸ P)) (a : O), ∀ x ∈ bar m, ρb a x ∈ bar m := by
    intro m a x hx
    refine (Submodule.span_le (p := (bar m).comap (ρb a))).2 (fun s hs => ?_) hx
    obtain ⟨b, hb, rfl⟩ := hs
    show ρb a (1 ⊗ₜ b) ∈ bar m
    rw [hρ]
    exact Submodule.subset_span ⟨a • b, by rw [Submodule.Quotient.mk_smul]; exact m.smul_mem a hb, rfl⟩

  have htop : bar l ⊔ bar l' = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c a =>
      have e1 : c ⊗ₜ[ℤ] a = c • ((1 : k) ⊗ₜ[ℤ] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1]
      refine Submodule.smul_mem _ c ?_
      have hm : (Submodule.Quotient.mk a : X ⧸ P) ∈ l ⊔ l' := h.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, u', hu', e2⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective P u
      obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective P u'
      have hd : a - b - b' ∈ P := by
        rw [← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, ← e2]
        abel
      have e3 : (1 : k) ⊗ₜ[ℤ] a = 1 ⊗ₜ b + 1 ⊗ₜ b' + 1 ⊗ₜ (a - b - b') := by
        rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add]
        congr 1
        abel
      rw [e3, hz _ hd, add_zero]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨b, hu, rfl⟩) (Submodule.subset_span ⟨b', hu', rfl⟩)
    | add x y hx hy => exact add_mem hx hy

  let π : X →ₗ[ℤ] X ⧸ P := P.mkQ.restrictScalars ℤ
  let proj : (X ⧸ P) →ₗ[O] l := LinearMap.ofIsCompl h LinearMap.id 0
  let q : X →ₗ[ℤ] l := (proj ∘ₗ P.mkQ).restrictScalars ℤ
  let ls : l →ₗ[ℤ] X ⧸ P := l.subtype.restrictScalars ℤ
  have hπ : Function.Injective (π.baseChange k) :=
    baseChange_mkQ_injective k P hPz
  have h1 : bar l ≤ LinearMap.eqLocus (π.baseChange k) ((ls.baseChange k) ∘ₗ (q.baseChange k)) := by
    refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    show π.baseChange k (1 ⊗ₜ b) = ls.baseChange k (q.baseChange k (1 ⊗ₜ b))
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    congr 1
    show Submodule.Quotient.mk b = ((proj (Submodule.Quotient.mk b) : l) : X ⧸ P)
    have := LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩
    exact (congrArg Subtype.val this).symm
  have h2 : bar l' ≤ LinearMap.ker (q.baseChange k) := by
    refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    show q.baseChange k (1 ⊗ₜ b) = 0
    rw [LinearMap.baseChange_tmul]
    have := LinearMap.ofIsCompl_apply_right h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩
    show (1 : k) ⊗ₜ[ℤ] proj (Submodule.Quotient.mk b) = 0
    rw [this, LinearMap.zero_apply, TensorProduct.tmul_zero]
  have hcompl : IsCompl (bar l) (bar l') := by
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => hπ ?_, codisjoint_iff.2 htop⟩
    rw [LinearMap.mem_eqLocus.1 (h1 hx), LinearMap.comp_apply, LinearMap.mem_ker.1 (h2 hx'), map_zero, map_zero]

  obtain ⟨a₀, ha₀⟩ := Submodule.Quotient.mk_surjective P (e.symm 1 : X ⧸ P)
  have hmk : ∀ c : O, (Submodule.Quotient.mk (c • a₀) : X ⧸ P) = (e.symm (Ideal.Quotient.mk _ c) : X ⧸ P) := by
    intro c
    have : (Ideal.Quotient.mk (Ideal.span {(p : O)}) c) = c • 1 := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Submodule.Quotient.mk_smul, ha₀, this, map_smul, Submodule.coe_smul]
  refine ⟨bar l', 1 ⊗ₜ a₀, hcompl, hst l, hst l', le_antisymm ?_ ?_, ?_⟩
  · refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e ⟨_, hb⟩)
    have hd : b - c • a₀ ∈ P := by
      rw [← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, hmk, hc, LinearEquiv.symm_apply_apply, sub_self]
    have e4 : (1 : k) ⊗ₜ[ℤ] b = ρb c (1 ⊗ₜ a₀) + 1 ⊗ₜ (b - c • a₀) := by
      rw [hρ, ← TensorProduct.tmul_add, add_sub_cancel]
    rw [SetLike.mem_coe, e4, hz _ hd, add_zero]
    exact Submodule.subset_span ⟨c, rfl⟩
  · refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨c, rfl⟩ := hs
    show ρb c (1 ⊗ₜ a₀) ∈ bar l
    rw [hρ]
    exact Submodule.subset_span ⟨c • a₀, by rw [hmk]; exact (e.symm _).2, rfl⟩
  ·
    let fA : O →ₗ[ℤ] X := (LinearMap.toSpanSingleton O X a₀).restrictScalars ℤ
    have hT : ∀ t, tensorAction ρb t (1 ⊗ₜ a₀) = fA.baseChange k t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        rw [tensorAction_tmul, hρ, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      | add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add]
    let mO : O →ₗ[ℤ] O ⧸ Ideal.span {(p : O)} := (Submodule.mkQ (Ideal.span {(p : O)})).restrictScalars ℤ
    let es : (O ⧸ Ideal.span {(p : O)}) →ₗ[ℤ] l := (e.symm : (O ⧸ Ideal.span {(p : O)}) →ₗ[O] l).restrictScalars ℤ
    have key : ∀ t, π.baseChange k (fA.baseChange k t) = ls.baseChange k (es.baseChange k (mO.baseChange k t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        simp only [LinearMap.baseChange_tmul]
        congr 1
        exact hmk a
      | add s t hs ht => simp only [map_add, hs, ht]
    have hmO : Function.Injective (mO.baseChange k) := by
      refine baseChange_mkQ_injective k (Ideal.span {(p : O)}) fun x hx c => ?_
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have e5 : a * (p : O) = p • a := by rw [mul_comm, ← nsmul_eq_mul]
      rw [e5]
      exact tmul_nsmul_eq_zero c a
    have hes : Function.Injective (es.baseChange k) := by
      refine Function.LeftInverse.injective (g := ((e : l →ₗ[O] O ⧸ Ideal.span {(p : O)}).restrictScalars ℤ).baseChange k)
        fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c u => simp [es]
      | add s t hs ht => simp only [map_add, hs, ht]
    have hls : Function.Injective (ls.baseChange k) := by
      refine Function.LeftInverse.injective (g := (proj.restrictScalars ℤ).baseChange k) fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c u =>
        simp only [LinearMap.baseChange_tmul]
        congr 1
        exact LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) u
      | add s t hs ht => simp only [map_add, hs, ht]
    intro t ht
    rw [hT] at ht
    have h0 : ls.baseChange k (es.baseChange k (mO.baseChange k t)) = 0 := by rw [← key, ht, map_zero]
    exact (injective_iff_map_eq_zero _).1 hmO _ ((injective_iff_map_eq_zero _).1 hes _
      ((injective_iff_map_eq_zero _).1 hls _ h0))

end GlobalTheory.LineSummand

namespace GlobalTheory.LineSummand

/- English proof (translation)
Introduce `D A N j S κ p ct l`. Take `⟨l', hl'⟩` from `l.2.1`. Take `⟨e⟩` from `l.2.2`. Conclude with `line_summand ct.kbar _ (fun x hx c => tmul_eq_zero_of_mem_smul_top (p := p) hx c) l.1 l' hl' e`.
-/
theorem sum1_bar_line : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (l : ct.Sum1),
  ∃ (M' : Submodule ct.kbar ct.LaBar) (n₀ : ct.LaBar), IsCompl l.bar M' ∧
    (∀ a, ∀ x ∈ l.bar, (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a x ∈ l.bar) ∧ (∀ a, ∀ x ∈ M', (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a x ∈ M') ∧
    l.bar = Submodule.span ct.kbar (Set.range fun a => (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a n₀) ∧
    ∀ t : ct.kbar ⊗[ℤ] 𝓞 D.host.E, tensorAction (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) t n₀ = 0 → t = 0 := by
  intro D A N j S κ p ct l
  obtain ⟨l', hl'⟩ := l.2.1
  obtain ⟨e⟩ := l.2.2
  exact line_summand ct.kbar _ (fun x hx c => tmul_eq_zero_of_mem_smul_top (p := p) hx c) l.1 l' hl' e

end GlobalTheory.LineSummand
