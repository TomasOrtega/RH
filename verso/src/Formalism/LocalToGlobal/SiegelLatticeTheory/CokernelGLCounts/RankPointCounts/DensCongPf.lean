import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel

section Act

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι]

def act (A : Matrix ι ι E) (v : ι → V) : ι → V := fun b => ∑ a, A a b • v a

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [act, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]`.
-/
theorem act_act (A B : Matrix ι ι E) (v : ι → V) : act A (act B v) = act (B * A) v := by
  funext b
  simp only [act, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty]`. Conclude with `H.h_zero_left y`. Consider the case `insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, H.h_add_left, ih]`.
-/
theorem h_sum_left {κ : Type} (s : Finset κ) (f : κ → V) (y : V) : H.h (∑ c ∈ s, f c) y = ∑ c ∈ s, H.h (f c) y := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact H.h_zero_left y
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, H.h_add_left, ih]

/- English proof (translation)
Rewrite using `[H.h_herm x y, M.L.cj_cj]`.
-/
theorem h_right (x y : V) : H.h x y = M.L.cj (H.h y x) := by
  rw [H.h_herm x y, M.L.cj_cj]

/- English proof (translation)
Rewrite using `[h_right, h_sum_left, map_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => (h_right H x (f c)).symm`.
-/
theorem h_sum_right {κ : Type} (s : Finset κ) (f : κ → V) (x : V) : H.h x (∑ c ∈ s, f c) = ∑ c ∈ s, H.h x (f c) := by
  rw [h_right, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun c _ => (h_right H x (f c)).symm

/- English proof (translation)
Rewrite using `[h_right, H.h_smul_left, map_mul, ← h_right]`.
-/
theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [h_right, H.h_smul_left, map_mul, ← h_right]

/- English proof (translation)
Simplify using `only [act, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[h_sum_left]`. Simplify using `only [H.h_smul_left, h_sum_right, h_smul_right, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring`.
-/
theorem gram_act (A : Matrix ι ι E) (v : ι → V) (a b : ι) :
    H.h (act A v b) (act A v a) =
      ((A.map M.L.cj).transpose * Matrix.of (fun c d => H.h (v d) (v c)) * A) a b := by
  simp only [act, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [h_sum_left]
  simp only [H.h_smul_left, h_sum_right, h_smul_right, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Act

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem act_one (v : ι → V) : act (1 : Matrix ι ι E) v = v := by
  funext b
  simp only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
The claim follows from `S.smul_mem ⟨o, ho⟩ hx`.
-/
theorem o_mul_mem (S : Submodule M.L.O E) {o x : E} (ho : o ∈ M.L.O) (hx : x ∈ S) : o * x ∈ S :=
  S.smul_mem ⟨o, ho⟩ hx

/- English proof (translation)
Introduce `a b`. Rewrite using `[gram_act, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply]`. Use `S.sum_mem fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `S.sum_mem fun d _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm _ (A c b), ← mul_assoc]`. Rewrite using `[mul_comm (A c b)]`. Use `o_mul_mem S (Subring.mul_mem _ (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (hAO d a)) (hAO c b)) (hv d c)` and prove the remaining obligations.
-/
theorem cong_act (S : Submodule M.L.O E) (A G : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a b, H.h (v b) (v a) - G a b ∈ S) :
    ∀ a b, H.h (act A v b) (act A v a) - ((A.map M.L.cj).transpose * G * A) a b ∈ S := by
  intro a b
  rw [gram_act, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply]
  refine S.sum_mem fun c _ => ?_
  rw [Finset.sum_mul]
  refine S.sum_mem fun d _ => ?_
  rw [mul_comm _ (A c b), ← mul_assoc]
  rw [mul_comm (A c b)]
  refine o_mul_mem S (Subring.mul_mem _ (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (hAO d a)) (hAO c b)) (hv d c)

/- English proof (translation)
The claim follows from `abelian₂.sum_mem fun a _ => abelian₂.smul_mem ⟨A a b, hAO a b⟩ (hv a)`.
-/
theorem mem_lam_act (abelian₂ : Submodule M.L.O V) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a, v a ∈ abelian₂) (b : ι) : act A v b ∈ abelian₂ :=
  abelian₂.sum_mem fun a _ => abelian₂.smul_mem ⟨A a b, hAO a b⟩ (hv a)

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (⟨A a b, hAO a b⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem mem_span_act (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span M.L.O (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (⟨A a b, hAO a b⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (A a b) (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem mem_spanE_act (A : Matrix ι ι E) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (A a b) (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hv`. Establish `hback : act B (act A v) = v` using `by rw [act_act, hAB, act_one]`. Use `⟨mem_lam_act abelian₂ A hAO v h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite `h2`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`.

Establish `e : ∑ b, g b • act A v b = ∑ a, (A *ᵥ g) a • v a`. Simplify using `only [act, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]`. Rewrite `hg` using `[e]`.

Establish `h0` using `h2 _ hg`. Establish `hAg : A *ᵥ g = 0` using `funext h0`. Establish `: g = B *ᵥ (A *ᵥ g)` using `by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]`. Introduce `b`. Rewrite using `[this, hAg, Matrix.mulVec_zero]`.

Both sides reduce to the same expression. Introduce `x hx hxs`. Establish `hxv : x ∈ Submodule.span E (Set.range v)`. Use `Submodule.span_le.2 ?_ hxs` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `mem_spanE_act A v b`. Establish `hO` using `h3 x hx hxv`. Use `Submodule.span_le.2 ?_ hO` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `: v a = act B (act A v) a` using `by rw [hback]`.

Rewrite using `[SetLike.mem_coe, this]`. Conclude with `mem_span_act B hBO (act A v) a`.
-/
theorem prim_act (abelian₂ : Submodule M.L.O V) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (hBA : B * A = 1) (v : ι → V) (hv : H.Prim abelian₂ v) :
    H.Prim abelian₂ (act A v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hback : act B (act A v) = v := by rw [act_act, hAB, act_one]
  refine ⟨mem_lam_act abelian₂ A hAO v h1, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at h2 ⊢
    intro g hg
    have e : ∑ b, g b • act A v b = ∑ a, (A *ᵥ g) a • v a := by
      simp only [act, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [e] at hg
    have h0 := h2 _ hg
    have hAg : A *ᵥ g = 0 := funext h0
    have : g = B *ᵥ (A *ᵥ g) := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    intro b
    rw [this, hAg, Matrix.mulVec_zero]
    rfl
  · intro x hx hxs
    have hxv : x ∈ Submodule.span E (Set.range v) := by
      refine Submodule.span_le.2 ?_ hxs
      rintro _ ⟨b, rfl⟩
      exact mem_spanE_act A v b
    have hO := h3 x hx hxv
    refine Submodule.span_le.2 ?_ hO
    rintro _ ⟨a, rfl⟩
    have : v a = act B (act A v) a := by rw [hback]
    rw [SetLike.mem_coe, this]
    exact mem_span_act B hBO (act A v) a

end Main

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Count

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Conclude with `M.L.O.sum_mem fun σ _ => Subring.zsmul_mem _ (M.L.O.prod_mem fun i _ => hA _ _) _`.
-/
theorem det_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : A.det ∈ M.L.O := by
  rw [Matrix.det_apply]
  exact M.L.O.sum_mem fun σ _ => Subring.zsmul_mem _ (M.L.O.prod_mem fun i _ => hA _ _) _

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.adjugate_apply]`. Use `det_mem _ fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [M.L.O.one_mem, M.L.O.zero_mem]`. Conclude with `hA a b`.
-/
theorem adj_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : ∀ i j, A.adjugate i j ∈ M.L.O := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_mem _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]
  · exact hA a b

def cls (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (G₀ : Matrix ι ι E) :
    Set (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) abelian₂) :=
  Set.range fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
    fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)

def psi (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (x : ι → V ⧸ H.smulLat c abelian₂) : ι → V ⧸ H.smulLat c abelian₂ :=
  fun b => ∑ a, (⟨A a b, hAO a b⟩ : M.L.O) • x a

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [psi, act]`. Rewrite using `[show (Submodule.Quotient.mk (∑ a, A a b • v a) : V ⧸ H.smulLat c abelian₂) = (H.smulLat c abelian₂).mkQ (∑ a, A a b • v a) from rfl, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show _ = (H.smulLat c abelian₂).mkQ ((⟨A a b, hAO a b⟩ : M.L.O) • v a)`.

Rewrite using `[LinearMap.map_smul]`. Both sides reduce to the same expression.
-/
theorem psi_mk (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) :
    psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (v a)) =
      fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act A v a) := by
  funext b
  simp only [psi, act]
  rw [show (Submodule.Quotient.mk (∑ a, A a b • v a) : V ⧸ H.smulLat c abelian₂) =
    (H.smulLat c abelian₂).mkQ (∑ a, A a b • v a) from rfl, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show _ = (H.smulLat c abelian₂).mkQ ((⟨A a b, hAO a b⟩ : M.L.O) • v a)
  rw [LinearMap.map_smul]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [psi, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `e : ∀ a, ∑ y, ((⟨B y b, hBO y b⟩ : M.L.O) * ⟨A a y, hAO a y⟩) • x a = (if a = b then (1 : M.L.O) else 0) • x a`. Introduce `a`.

Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrFun (congrFun hAB a) b`. Rewrite `h` using `[Matrix.mul_apply]`.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]`. Rewrite using `[Finset.sum_congr rfl (fun y _ => mul_comm (B y b) (A a y)), h, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[Finset.sum_congr rfl fun a _ => e a]`. Simplify using the standard rewrite rules.
-/
theorem psi_psi (abelian₂ : Submodule M.L.O V) (c : E) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (x : ι → V ⧸ H.smulLat c abelian₂) :
    psi H abelian₂ c B hBO (psi H abelian₂ c A hAO x) = x := by
  funext b
  simp only [psi, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ a, ∑ y, ((⟨B y b, hBO y b⟩ : M.L.O) * ⟨A a y, hAO a y⟩) • x a =
      (if a = b then (1 : M.L.O) else 0) • x a := by
    intro a
    rw [← Finset.sum_smul]
    congr 1
    apply Subtype.ext
    have h := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at h
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [Finset.sum_congr rfl (fun y _ => mul_comm (B y b) (A a y)), h, Matrix.one_apply]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp

/- English proof (translation)
Take `⟨y, hy, hdy⟩` from `hAd`. Use `set B : Matrix ι ι E := y • A.adjugate with hB`. Establish `hBO : ∀ i j, B i j ∈ M.L.O` using `fun i j => by`. Rewrite using `[hB, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Subring.mul_mem _ hy (adj_mem A hAO i j)`.

Establish `hAB : A * B = 1`. Rewrite using `[hB, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdy, one_smul]`. Establish `hBA : B * A = 1`. Rewrite using `[hB, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdy, one_smul]`. Use `set c : E := algebraMap F E (ϖ : F)`.

Use `set S : Submodule M.L.O E := Submodule.span M.L.O {c}`. Use `set G' := (A.map M.L.cj).transpose * G * A with hG'`. Establish `hGback : (B.map M.L.cj).transpose * G' * B = G`. Establish `e1 : (B.map M.L.cj).transpose * (A.map M.L.cj).transpose = 1`. Rewrite using `[← Matrix.transpose_mul]`.

Establish `: A.map M.L.cj * B.map M.L.cj = (A * B).map M.L.cj`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, map_sum]`. Rewrite using `[this, hAB]`. Use extensionality with `i j`.

Simplify using `[Matrix.one_apply, eq_comm]`. Rewrite using `[hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, hAB, Matrix.mul_one]`. Establish `hset : cls H ϖ abelian₂ G' = psi H abelian₂ c A hAO '' cls H ϖ abelian₂ G`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨v', hP, hC⟩, rfl⟩`. Use `⟨fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act B v' a), ⟨⟨act B v', prim_act H abelian₂ B A hBO hAO hBA hAB v' hP, ?_⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `cong_act H S B G' hBO v' hC` as an intermediate fact. Rewrite `this` using `[hGback]`. Then use the resulting hypothesis. Use `show psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act B v' a)) = _`.

Rewrite using `[psi_mk, act_act, hBA, act_one]`. Introduce and unpack `⟨_, ⟨⟨v, hP, hC⟩, rfl⟩, rfl⟩`. Use `⟨⟨act A v, prim_act H abelian₂ A B hAO hBO hAB hBA v hP, cong_act H S A G hAO v hC⟩, ?_⟩` and prove the remaining obligations. Conclude with `(psi_mk H abelian₂ c A hAO v).symm`. Establish `hinj : Function.Injective (psi H abelian₂ c A hAO)` using `fun x x' h => by`.

Rewrite using `[← psi_psi H abelian₂ c A B hAO hBO hAB x, ← psi_psi H abelian₂ c A B hAO hBO hAB x', h]`. Establish `hcard : Nat.card (cls H ϖ abelian₂ G') = Nat.card (cls H ϖ abelian₂ G)`. Rewrite using `[hset, Nat.card_image_of_injective hinj]`. Unfold `Loc.HermSp.dens`. Conclude with `congrArg (fun n : ℕ => (n : ℝ) / _) hcard`.
-/
theorem densCong_body (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (G A : Matrix ι ι E)
    (hAO : ∀ i j, A i j ∈ M.L.O) (hAd : ∃ y ∈ M.L.O, A.det * y = 1) :
    H.dens ϖ abelian₂ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ abelian₂ G := by
  obtain ⟨y, hy, hdy⟩ := hAd
  set B : Matrix ι ι E := y • A.adjugate with hB
  have hBO : ∀ i j, B i j ∈ M.L.O := fun i j => by
    rw [hB, Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hy (adj_mem A hAO i j)
  have hAB : A * B = 1 := by
    rw [hB, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdy, one_smul]
  have hBA : B * A = 1 := by
    rw [hB, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdy, one_smul]
  set c : E := algebraMap F E (ϖ : F)
  set S : Submodule M.L.O E := Submodule.span M.L.O {c}
  set G' := (A.map M.L.cj).transpose * G * A with hG'
  have hGback : (B.map M.L.cj).transpose * G' * B = G := by
    have e1 : (B.map M.L.cj).transpose * (A.map M.L.cj).transpose = 1 := by
      rw [← Matrix.transpose_mul]
      have : A.map M.L.cj * B.map M.L.cj = (A * B).map M.L.cj := by
        ext i j; simp [Matrix.mul_apply, map_sum]
      rw [this, hAB]
      ext i j; simp [Matrix.one_apply, eq_comm]
    rw [hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, hAB, Matrix.mul_one]
  have hset : cls H ϖ abelian₂ G' = psi H abelian₂ c A hAO '' cls H ϖ abelian₂ G := by
    ext x
    constructor
    · rintro ⟨⟨v', hP, hC⟩, rfl⟩
      refine ⟨fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act B v' a),
        ⟨⟨act B v', prim_act H abelian₂ B A hBO hAO hBA hAB v' hP, ?_⟩, rfl⟩, ?_⟩
      · have := cong_act H S B G' hBO v' hC
        rwa [hGback] at this
      · show psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act B v' a)) = _
        rw [psi_mk, act_act, hBA, act_one]
    · rintro ⟨_, ⟨⟨v, hP, hC⟩, rfl⟩, rfl⟩
      refine ⟨⟨act A v, prim_act H abelian₂ A B hAO hBO hAB hBA v hP, cong_act H S A G hAO v hC⟩, ?_⟩
      exact (psi_mk H abelian₂ c A hAO v).symm
  have hinj : Function.Injective (psi H abelian₂ c A hAO) := fun x x' h => by
    rw [← psi_psi H abelian₂ c A B hAO hBO hAB x, ← psi_psi H abelian₂ c A B hAO hBO hAB x', h]
  have hcard : Nat.card (cls H ϖ abelian₂ G') = Nat.card (cls H ϖ abelian₂ G) := by
    rw [hset, Nat.card_image_of_injective hinj]
  unfold Loc.HermSp.dens
  exact congrArg (fun n : ℕ => (n : ℝ) / _) hcard

end Count

end Formalism.L2.SG.Pf.DensCongPf
