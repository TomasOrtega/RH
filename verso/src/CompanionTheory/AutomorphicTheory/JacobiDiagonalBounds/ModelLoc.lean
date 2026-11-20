import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NFModel

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

variable {P : M.Par}

def Loc (a : MA.A P (MA.DQ P)) : Prop :=
  ∀ (U : Set (MA.E P.r)), IsOpen U → ∀ f : M.Ty P → MA.SmQ P.r P.TT,
    (∀ ρ (q : MA.Qp P.r P.TT), q.1 ∈ U → MA.evQ P (f ρ) q = 0) →
    ∀ ρ (q : MA.Qp P.r P.TT), q.1 ∈ U → MA.evQ P (MA.actA P a f ρ) q = 0

def locAlg (P : M.Par) : Subalgebra ℂ (MA.A P (MA.DQ P)) where
  carrier := {a | Loc a}
  mul_mem' {a b} ha hb U hU f hf := by
    rw [Gauge.actA_mul]; exact ha U hU _ (hb U hU f hf)
  add_mem' {a b} ha hb U hU f hf ρ q hq := by
    rw [Gauge.actA_add]
    show MA.evQ P (MA.actA P a f ρ) q + MA.evQ P (MA.actA P b f ρ) q = 0
    rw [ha U hU f hf ρ q hq, hb U hU f hf ρ q hq, add_zero]
  algebraMap_mem' c U _ f hf ρ q hq := by
    rw [Algebra.algebraMap_eq_smul_one, act_smul, jdh_actA_one]
    show c * MA.evQ P (f ρ) q = 0
    rw [hf ρ q hq, mul_zero]

def evA (q : MA.Qp P.r P.TT) : MA.SmQ P.r P.TT →+ ℂ where
  toFun f := MA.evQ P f q
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Introduce `U _ f hf ρ q hq`. Use `(map_sum (evA q) (fun π' => (X ρ π').1 (f π')) Finset.univ).trans (Finset.sum_eq_zero fun π' _ => ?_)` and prove the remaining obligations. Take `⟨z, hz⟩` from `h ρ π'`. Rewrite using `[hz]`. Use `show z * MA.evQ P (f π') q = 0`.

Rewrite using `[hf π' q hq, mul_zero]`.
-/
theorem loc_central (X : MA.A P (MA.DQ P)) (h : ∀ i j, ∃ z : ℂ, X i j = algebraMap ℂ _ z) : X ∈ locAlg P := by
  intro U _ f hf ρ q hq
  refine (map_sum (evA q) (fun π' => (X ρ π').1 (f π')) Finset.univ).trans (Finset.sum_eq_zero fun π' _ => ?_)
  obtain ⟨z, hz⟩ := h ρ π'
  rw [hz]
  show z * MA.evQ P (f π') q = 0
  rw [hf π' q hq, mul_zero]

/- English proof (translation)
Introduce `_ _ f hf ρ q hq` and use `by rw [mulBy_fn, hf ρ q hq, mul_zero]`.
-/
theorem loc_fn (g gb : MA.SmQ P.r P.TT) : MA.sc P (MA.DQ P) ((MA.DQ P).fnP g gb) ∈ locAlg P :=
  fun _ _ f hf ρ q hq => by rw [mulBy_fn, hf ρ q hq, mul_zero]

/- English proof (translation)
Establish `h0 : MA.ext f.1 =ᶠ[nhds q.1] fun _ => 0` using `by filter_upwards [hU.mem_nhds hq] with x hx`. Unfold `MA.ext`. Use `split_ifs with h`. Conclude with `hf ⟨x, h⟩ hx`. Both sides reduce to the same expression.

Use `show MA.coordE v q.1 * MA.wirt v (MA.ext f.1) q.1 = 0`. Simplify using `[MA.wirt, h0.fderiv_eq]`.
-/
theorem euler_loc (v : M.Var P.r) {U : Set (MA.E P.r)} (hU : IsOpen U) (f : MA.SmQ P.r P.TT)
    (hf : ∀ q : MA.Qp P.r P.TT, q.1 ∈ U → MA.evQ P f q = 0) (q : MA.Qp P.r P.TT) (hq : q.1 ∈ U) :
    MA.evQ P (MA.eulerQ v f) q = 0 := by
  have h0 : MA.ext f.1 =ᶠ[nhds q.1] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hq] with x hx
    unfold MA.ext
    split_ifs with h
    · exact hf ⟨x, h⟩ hx
    · rfl
  show MA.coordE v q.1 * MA.wirt v (MA.ext f.1) q.1 = 0
  simp [MA.wirt, h0.fderiv_eq]

/- English proof (translation)
Introduce `U hU f hf ρ q hq` and use `by rw [act_sc]; exact euler_loc v hU (f ρ) (hf ρ) q hq`.
-/
theorem loc_ev (v : M.Var P.r) (Z : (MA.DQ P).Op) :
    MA.sc P (MA.DQ P) ((MA.DQ P).mkP ((MA.DQ P).ev v) Z) ∈ locAlg P := fun U hU f hf ρ q hq => by
  rw [act_sc]; exact euler_loc v hU (f ρ) (hf ρ) q hq

/- English proof (translation)
Establish `e : (Matrix.diagonal fun π => x + a π • y) = MA.sc P (MA.DQ P) x + MA.kap P (MA.DQ P) a * MA.sc P (MA.DQ P) y`. Rewrite using `[kap_diag, MA.sc, MA.sc, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]`. Use `congr 1`. Rewrite using `[e]`. Conclude with `add_mem hx (mul_mem (loc_central _ (kap_central a)) hy)`.
-/
theorem loc_diag_smul (a : M.Ty P → ℂ) (x y : (MA.DQ P).Pr) (hx : MA.sc P (MA.DQ P) x ∈ locAlg P)
    (hy : MA.sc P (MA.DQ P) y ∈ locAlg P) : (Matrix.diagonal fun π => x + a π • y) ∈ locAlg P := by
  have e : (Matrix.diagonal fun π => x + a π • y) =
      MA.sc P (MA.DQ P) x + MA.kap P (MA.DQ P) a * MA.sc P (MA.DQ P) y := by
    rw [kap_diag, MA.sc, MA.sc, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add]
    congr 1
  rw [e]
  exact add_mem hx (mul_mem (loc_central _ (kap_central a)) hy)

/- English proof (translation)
Simplify using `only [MA.sc, map_mul]`.
-/
theorem sc_mul' (x y : (MA.DQ P).Pr) : MA.sc P (MA.DQ P) (x * y) = MA.sc P (MA.DQ P) x * MA.sc P (MA.DQ P) y := by
  simp only [MA.sc, map_mul]

/- English proof (translation)
Introduce `U hU f hf ρ q hq` and use `by rw [act_sc] show MA.evQ P g q * MA.evQ P (MA.eulerQ v (f ρ)) q = 0 rw [euler_loc v hU (f ρ) (hf ρ) q hq, mul_zero]`.
-/
theorem loc_dz (g : MA.SmQ P.r P.TT) (v : M.Var P.r) (Z : (MA.DQ P).Op) :
    MA.sc P (MA.DQ P) ((MA.DQ P).mkP ((MA.DQ P).mulOp g * (MA.DQ P).ev v) Z) ∈ locAlg P := fun U hU f hf ρ q hq => by
  rw [act_sc]
  show MA.evQ P g q * MA.evQ P (MA.eulerQ v (f ρ)) q = 0
  rw [euler_loc v hU (f ρ) (hf ρ) q hq, mul_zero]

variable {L : LevelData (MA.A P (MA.DQ P)) P.r}

/- English proof (translation)
Use `(Subring.closure_le (t := (locAlg P).toSubring)).2 (fun f hf => ?_) hf` and prove the remaining obligations. Take `⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, -⟩` from `hM`. Simplify using `only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hf`. Break down `hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)` into its components or cases. Rewrite using `[hc]`.

Conclude with `loc_fn _ _`. Rewrite using `[hci]`. Conclude with `loc_fn _ _`. Rewrite using `[hcb]`. Conclude with `loc_fn _ _`.

Rewrite using `[hcbi]`. Conclude with `loc_fn _ _`. Break down `h with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Rewrite using `[hz]`. Conclude with `loc_fn _ _`.

Rewrite using `[hzi]`. Conclude with `loc_fn _ _`. Rewrite using `[hzb]`. Conclude with `loc_fn _ _`. Rewrite using `[hzbi]`.

Conclude with `loc_fn _ _`. Rewrite using `[hg]`. Conclude with `loc_fn _ _`. Rewrite using `[hgi]`. Conclude with `loc_fn _ _`.
-/
theorem loc_fns (hM : MA.IsModelLevel P (MA.DQ P) L) {f : MA.A P (MA.DQ P)} (hf : f ∈ Subring.closure L.fns) :
    f ∈ locAlg P := by
  refine (Subring.closure_le (t := (locAlg P).toSubring)).2 (fun f hf => ?_) hf
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, -⟩ := hM
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · rw [hc]; exact loc_fn _ _
  · rw [hci]; exact loc_fn _ _
  · rw [hcb]; exact loc_fn _ _
  · rw [hcbi]; exact loc_fn _ _
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact loc_fn _ _
    · rw [hzi]; exact loc_fn _ _
    · rw [hzb]; exact loc_fn _ _
    · rw [hzbi]; exact loc_fn _ _
    · rw [hg]; exact loc_fn _ _
    · rw [hgi]; exact loc_fn _ _

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce `i j`. Rewrite using `[List.prod_nil, Matrix.one_apply]`. Use `split_ifs`.

Use `exacts [B.one_mem, B.zero_mem]`. Consider the case `cons X l ih`. Introduce `i j`. Rewrite using `[List.prod_cons, Matrix.mul_apply]`. Conclude with `B.sum_mem fun k _ => B.mul_mem (h X List.mem_cons_self i k) (ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)) k j)`.
-/
theorem mat_prod_mem {A : Type} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (l : List (Matrix (Fin 2) (Fin 2) A))
    (h : ∀ X ∈ l, ∀ i j, X i j ∈ B) : ∀ i j, l.prod i j ∈ B := by
  induction l with
  | nil =>
    intro i j
    rw [List.prod_nil, Matrix.one_apply]
    split_ifs
    exacts [B.one_mem, B.zero_mem]
  | cons X l ih =>
    intro i j
    rw [List.prod_cons, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (h X List.mem_cons_self i k)
      (ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)) k j)

/- English proof (translation)
Establish `hp : ∀ l, L.p l ∈ locAlg P` using `fun l => by rw [hM.1]; exact loc_ev _ _`. Establish `hpb : ∀ l, L.pb l ∈ locAlg P` using `fun l => by rw [hM.2.1]; exact loc_ev _ _`. Establish `hn : L.nab ∈ locAlg P`. Rewrite using `[hM.2.2.2.2.2.2.2.2.2.2.2.2.1]`. Conclude with `loc_diag_smul _ _ _ (loc_dz _ _ _) (by rw [sc_mul']; exact mul_mem (loc_fn _ _) (loc_fn _ _))`.

Establish `hns : L.nabs ∈ locAlg P`. Rewrite using `[hM.2.2.2.2.2.2.2.2.2.2.2.2.2.1]`. Use `loc_diag_smul _ _ _ ?_ (by rw [sc_mul']; exact mul_mem (loc_fn _ _) (loc_fn _ _))` and prove the remaining obligations. Rewrite using `[MA.sc, map_neg]`. Conclude with `neg_mem (loc_dz _ _ _)`.

Establish `F` using `fun {f} (hf : f ∈ Subring.closure L.fns) => loc_fns hM hf`. Establish `hT : ∀ Y i j, L.Tprod Y i j ∈ locAlg P` using `fun Y => mat_prod_mem _ _ fun X hX i j => by`. Take `⟨l, rfl⟩` from `List.mem_ofFn.1 (List.mem_reverse.1 hX)`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `add_mem (Subalgebra.algebraMap_mem _ _) (hp l)`.

Conclude with `neg_mem (F (clF L (RuleGD.m_c L l)))`. Conclude with `F (clF L (RuleGD.m_ci L l))`. Conclude with `zero_mem _`. Establish `hTv : ∀ Y i j, L.Tvprod Y i j ∈ locAlg P` using `fun Y => mat_prod_mem _ _ fun X hX i j => by`. Take `⟨l, rfl⟩` from `List.mem_ofFn.1 (List.mem_reverse.1 hX)`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `sub_mem (Subalgebra.algebraMap_mem _ _) (hpb l)`. Conclude with `neg_mem (F (clF L (RuleGD.m_cb L l)))`. Conclude with `F (clF L (RuleGD.m_cbi L l))`. Conclude with `zero_mem _`.

Break down `hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)` into its components or cases. Conclude with `mul_mem (F (cDr L)) (hT y 0 0)`. Conclude with `mul_mem (mul_mem (F (cDrb L)) (F (cGG L))) (add_mem (mul_mem (sub_mem (neg_mem hn) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (F (cζb L)) (F (cGGi L))))) (hT y 0 0)) (hT y 1 0))`. Conclude with `mul_mem (F (cDrb L)) (hTv y 0 0)`. Conclude with `mul_mem (mul_mem (F (cDr L)) (F (cGG L))) (add_mem (mul_mem (sub_mem (neg_mem hns) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (F (cζ L)) (F (cGGi L))))) (hTv y 0 0)) (hTv y 1 0))`.
-/
theorem loc_hat (hM : MA.IsModelLevel P (MA.DQ P) L) {X : MA.A P (MA.DQ P)} (hX : X ∈ hats L) : X ∈ locAlg P := by
  have hp : ∀ l, L.p l ∈ locAlg P := fun l => by rw [hM.1]; exact loc_ev _ _
  have hpb : ∀ l, L.pb l ∈ locAlg P := fun l => by rw [hM.2.1]; exact loc_ev _ _
  have hn : L.nab ∈ locAlg P := by
    rw [hM.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact loc_diag_smul _ _ _ (loc_dz _ _ _) (by rw [sc_mul']; exact mul_mem (loc_fn _ _) (loc_fn _ _))
  have hns : L.nabs ∈ locAlg P := by
    rw [hM.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    refine loc_diag_smul _ _ _ ?_ (by rw [sc_mul']; exact mul_mem (loc_fn _ _) (loc_fn _ _))
    rw [MA.sc, map_neg]
    exact neg_mem (loc_dz _ _ _)
  have F := fun {f} (hf : f ∈ Subring.closure L.fns) => loc_fns hM hf
  have hT : ∀ Y i j, L.Tprod Y i j ∈ locAlg P := fun Y => mat_prod_mem _ _ fun X hX i j => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hX)
    fin_cases i <;> fin_cases j
    · exact add_mem (Subalgebra.algebraMap_mem _ _) (hp l)
    · exact neg_mem (F (clF L (RuleGD.m_c L l)))
    · exact F (clF L (RuleGD.m_ci L l))
    · exact zero_mem _
  have hTv : ∀ Y i j, L.Tvprod Y i j ∈ locAlg P := fun Y => mat_prod_mem _ _ fun X hX i j => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hX)
    fin_cases i <;> fin_cases j
    · exact sub_mem (Subalgebra.algebraMap_mem _ _) (hpb l)
    · exact neg_mem (F (clF L (RuleGD.m_cb L l)))
    · exact F (clF L (RuleGD.m_cbi L l))
    · exact zero_mem _
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · exact mul_mem (F (cDr L)) (hT y 0 0)
  · exact mul_mem (mul_mem (F (cDrb L)) (F (cGG L))) (add_mem (mul_mem (sub_mem (neg_mem hn)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (F (cζb L)) (F (cGGi L))))) (hT y 0 0)) (hT y 1 0))
  · exact mul_mem (F (cDrb L)) (hTv y 0 0)
  · exact mul_mem (mul_mem (F (cDr L)) (F (cGG L))) (add_mem (mul_mem (sub_mem (neg_mem hns)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (F (cζ L)) (F (cGGi L))))) (hTv y 0 0)) (hTv y 1 0))

/- English proof (translation)
Establish `F` using `fun {f} (hf : f ∈ Subring.closure L.fns) => loc_fns hM hf`. Use `(Algebra.adjoin_le (S := locAlg P) fun x hx => ?_) hb` and prove the remaining obligations. Break down `hx with (((hx | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩)` into its components or cases. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl | rfl | rfl` into its components or cases.

Conclude with `F (cζi L)`. Conclude with `F (cζbi L)`. Conclude with `mul_mem (F (cD L)) (F (cDbi L))`. Conclude with `mul_mem (F (cDb L)) (F (cDi L))`. Conclude with `loc_central _ (kap_central g)`.

Conclude with `mul_mem (mul_mem (F (cDrb L)) (F (cDri L))) (loc_central _ (SS_central i))`. Use `show star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i) ∈ locAlg P`. Take `⟨d1, d2⟩` from `model_star_D hM`. Establish `d1' : star L.Drb = L.Dr` using `by rw [← d1, star_star]`. Rewrite using `[star_mul, star_mul, d2, d1']`.

Use `mul_mem (loc_central _ fun a b => ?_) (mul_mem (F (cDrbi L)) (F (cDr L)))` and prove the remaining obligations. Take `⟨z, hz⟩` from `SS_central (P := P) i b a`. Conclude with `⟨star z, by rw [Matrix.star_apply, hz, algebraMap_star_comm]⟩`.
-/
theorem loc_BB (hM : MA.IsModelLevel P (MA.DQ P) L) {b : MA.A P (MA.DQ P)} (hb : b ∈ BB P L) : b ∈ locAlg P := by
  have F := fun {f} (hf : f ∈ Subring.closure L.fns) => loc_fns hM hf
  refine (Algebra.adjoin_le (S := locAlg P) fun x hx => ?_) hb
  rcases hx with (((hx | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact F (cζi L)
    · exact F (cζbi L)
    · exact mul_mem (F (cD L)) (F (cDbi L))
    · exact mul_mem (F (cDb L)) (F (cDi L))
  · exact loc_central _ (kap_central g)
  · exact mul_mem (mul_mem (F (cDrb L)) (F (cDri L))) (loc_central _ (SS_central i))
  · show star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i) ∈ locAlg P
    obtain ⟨d1, d2⟩ := model_star_D hM
    have d1' : star L.Drb = L.Dr := by rw [← d1, star_star]
    rw [star_mul, star_mul, d2, d1']
    refine mul_mem (loc_central _ fun a b => ?_) (mul_mem (F (cDrbi L)) (F (cDr L)))
    obtain ⟨z, hz⟩ := SS_central (P := P) i b a
    exact ⟨star z, by rw [Matrix.star_apply, hz, algebraMap_star_comm]⟩

/- English proof (translation)
Use `(Submodule.span_le (p := Subalgebra.toSubmodule (locAlg P))).2 ?_ hx` and prove the remaining obligations. Introduce and unpack `y ⟨b, hb, h, -, hh, rfl⟩`. Use `show _ ∈ locAlg P`. Conclude with `mul_mem (mul_mem (loc_BB hM hb) (pow_mem (loc_fns hM (cDi L)) n)) (list_prod_mem fun a ha => loc_hat hM (hh a ha))`.
-/
theorem loc_nfs (hM : MA.IsModelLevel P (MA.DQ P) L) {n : ℕ} {x : MA.A P (MA.DQ P)}
    (hx : x ∈ NFs L (BB P L) (L.Di ^ n) n) : x ∈ locAlg P := by
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (locAlg P))).2 ?_ hx
  rintro y ⟨b, hb, h, -, hh, rfl⟩
  show _ ∈ locAlg P
  exact mul_mem (mul_mem (loc_BB hM hb) (pow_mem (loc_fns hM (cDi L)) n))
    (list_prod_mem fun a ha => loc_hat hM (hh a ha))

/- English proof (translation)
Establish `h0` using `ha U hU (f - g) (fun ρ q hq => by show MA.evQ P (f ρ) q - MA.evQ P (g ρ) q = 0`. Rewrite using `[h ρ q hq, sub_self]) ρ q hq`. Establish `e : MA.actA P a f = MA.actA P a (f - g) + MA.actA P a g` using `by rw [← jdh_actA_addR, sub_add_cancel]`. Rewrite using `[e]`. Use `show MA.evQ P (MA.actA P a (f - g) ρ) q + _ = _`.

Rewrite using `[h0, zero_add]`. Both sides reduce to the same expression.
-/
theorem Loc.congr {a : MA.A P (MA.DQ P)} (ha : Loc a) {U : Set (MA.E P.r)} (hU : IsOpen U)
    {f g : M.Ty P → MA.SmQ P.r P.TT} (h : ∀ ρ (q : MA.Qp P.r P.TT), q.1 ∈ U → MA.evQ P (f ρ) q = MA.evQ P (g ρ) q)
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) (hq : q.1 ∈ U) :
    MA.evQ P (MA.actA P a f ρ) q = MA.evQ P (MA.actA P a g ρ) q := by
  have h0 := ha U hU (f - g) (fun ρ q hq => by
    show MA.evQ P (f ρ) q - MA.evQ P (g ρ) q = 0
    rw [h ρ q hq, sub_self]) ρ q hq
  have e : MA.actA P a f = MA.actA P a (f - g) + MA.actA P a g := by rw [← jdh_actA_addR, sub_add_cancel]
  rw [e]
  show MA.evQ P (MA.actA P a (f - g) ρ) q + _ = _
  rw [h0, zero_add]
  rfl

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
