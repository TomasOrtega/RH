import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Abstract

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}

/- English proof (translation)
The claim follows from `L.fns_comm x hx y hy`.
-/
theorem fn_comm6 (L : R.LevelData A r) {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : x * y = y * x := L.fns_comm x hx y hy

/- English proof (translation)
Conclude with `Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))`.
-/
theorem c_fns (L : R.LevelData A r) (l : Fin r) : L.c l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))
/- English proof (translation)
Conclude with `Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))`.
-/
theorem ci_fns (L : R.LevelData A r) (l : Fin r) : L.ci l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))
/- English proof (translation)
Conclude with `Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))`.
-/
theorem cb_fns (L : R.LevelData A r) (l : Fin r) : L.cb l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))
/- English proof (translation)
Conclude with `Or.inl (Or.inr ⟨l, rfl⟩)`.
-/
theorem cbi_fns (L : R.LevelData A r) (l : Fin r) : L.cbi l ∈ L.fns := by
  exact Or.inl (Or.inr ⟨l, rfl⟩)

/- English proof (translation)
Establish `hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y` using `fun x hx y hy => L.fns_comm x hx y hy`. Introduce `x hx y hy`. Simplify using `only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Break down `hy with rfl | rfl | rfl` into its components or cases. Rewrite using `[hp]`.

Use `Commute.neg_right ?_` and prove the remaining obligations. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `L.p_pb l m`. Conclude with `(L.pb_c m l).symm`. Conclude with `(L.pb_ci m l).symm`.

Rewrite using `[hc]`. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `L.p_cb l m`. Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))`. Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))`.

Rewrite using `[hci]`. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `L.p_cbi l m`. Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))`. Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))`.
-/
theorem hol_comm_star (L : R.LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (l m : Fin r) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x (star y) := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hy with rfl | rfl | rfl
  · rw [hp]
    refine Commute.neg_right ?_
    rcases hx with rfl | rfl | rfl
    · exact L.p_pb l m
    · exact (L.pb_c m l).symm
    · exact (L.pb_ci m l).symm
  · rw [hc]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cb l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
  · rw [hci]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cbi l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))

/- English proof (translation)
Establish `hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y` using `fun x hx y hy => L.fns_comm x hx y hy`. Establish `hlm' : m ≠ l` using `fun h => hlm h.symm`. Introduce `x hx y hy`. Simplify using `only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl`.

Conclude with `L.p_p l m`. Use `L.p_c l m` as an intermediate fact. Rewrite `this` using `[if_neg hlm, add_zero]`. Conclude with `this`. Use `L.p_ci l m` as an intermediate fact.

Rewrite `this` using `[if_neg hlm, sub_zero]`. Conclude with `this`. Use `L.p_c m l` as an intermediate fact. Rewrite `this` using `[if_neg hlm', add_zero]`. Conclude with `this.symm`.

Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))`. Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))`. Use `L.p_ci m l` as an intermediate fact. Rewrite `this` using `[if_neg hlm', sub_zero]`. Conclude with `this.symm`.

Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))`. Conclude with `hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))`.
-/
theorem hol_comm_hol (L : R.LevelData A r) {l m : Fin r} (hlm : l ≠ m) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x y := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  have hlm' : m ≠ l := fun h => hlm h.symm
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact L.p_p l m
  · have := L.p_c l m; rw [if_neg hlm, add_zero] at this; exact this
  · have := L.p_ci l m; rw [if_neg hlm, sub_zero] at this; exact this
  · have := L.p_c m l; rw [if_neg hlm', add_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))
  · have := L.p_ci m l; rw [if_neg hlm', sub_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))

/- English proof (translation)
Take `⟨h1, h2, -, h4⟩` from `hw`. Use `⟨h1, h2, h4.imp fun {l l'} h => ?_⟩` and prove the remaining obligations. Unfold `RegL`. Use `split_ifs`. Simplify using `using h 1 (by norm_num)`.

Introduce `h'`. Apply `h (-1) (by norm_num)` to reduce the goal to its premises. Use `push_cast`. Take the linear combination `-h'`.
-/
theorem good_of_adm {S : Type} (st : Fr.Start A) (w : List (Letter ℂ S)) (hw : Fr.admitted st w) : Good w := by
  obtain ⟨h1, h2, -, h4⟩ := hw
  refine ⟨h1, h2, h4.imp fun {l l'} h => ?_⟩
  unfold RegL
  split_ifs
  · simpa using h 1 (by norm_num)
  · intro h'
    apply h (-1) (by norm_num)
    push_cast
    linear_combination -h'

end Abstract

section Pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show a * c = c * a`. Conclude with `h1`. Use `show MulOpposite.op b * MulOpposite.op d = MulOpposite.op d * MulOpposite.op b`. Rewrite using `[← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]`.
-/
theorem pair_operator_commute {a b c d : Module.End ℂ V} (h1 : a * c = c * a) (h2 : d * b = b * d) :
    (mkP a b : Pr V) * mkP c d = mkP c d * mkP a b := by
  refine Prod.ext ?_ ?_
  · show a * c = c * a
    exact h1
  · show MulOpposite.op b * MulOpposite.op d = MulOpposite.op d * MulOpposite.op b
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]

end Pairs

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Establish `hs : ∀ a b : Module.End ℂ (RadSp k r z z' π π'), star (mkP a b : Pr (RadSp k r z z' π π')) = mkP b a` using `fun a b => rfl`. Use `⟨fun l => ?_, fun l => ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[hp, hpb, hs]`. Use `Prod.ext rfl ?_` and prove the remaining obligations.

Use `show MulOpposite.op (X.op l 0) = -MulOpposite.op (-X.op l 0)`. Rewrite using `[← MulOpposite.op_neg, neg_neg]`. Rewrite using `[hc, hcb, hs]`. Rewrite using `[hci, hcbi, hs]`.
-/
theorem star_site_ops {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) :
    (∀ l, star (L.p l) = -L.pb l) ∧ (∀ l, star (L.c l) = L.cb l) ∧ ∀ l, star (L.ci l) = L.cbi l := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have hs : ∀ a b : Module.End ℂ (RadSp k r z z' π π'), star (mkP a b : Pr (RadSp k r z z' π π')) = mkP b a :=
    fun a b => rfl
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_⟩
  · rw [hp, hpb, hs]
    refine Prod.ext rfl ?_
    show MulOpposite.op (X.op l 0) = -MulOpposite.op (-X.op l 0)
    rw [← MulOpposite.op_neg, neg_neg]
  · rw [hc, hcb, hs]
  · rw [hci, hcbi, hs]

/- English proof (translation)
Take `⟨hp, hc, hci⟩` from `star_site_ops hL`. Use `⟨⟨L.c_ci l, L.ci_c l, ?_⟩, hol_comm_star L hp hc hci l l⟩` and prove the remaining obligations. Establish `h` using `L.p_c l l`. Rewrite `h` using `[if_pos rfl]`. Conclude with `h`.
-/
theorem isSite_actual {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) (l : Fin r) : IsSite (site L l) := by
  obtain ⟨hp, hc, hci⟩ := star_site_ops hL
  refine ⟨⟨L.c_ci l, L.ci_c l, ?_⟩, hol_comm_star L hp hc hci l l⟩
  have h := L.p_c l l
  rw [if_pos rfl] at h
  exact h

/- English proof (translation)
Establish `hmul : ∀ M N : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → (∀ a b, N a b ∈ 𝒜) → ∀ a b, (M * N) a b ∈ 𝒜`. Introduce `M N hM hN a b`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hM a c) (hN c b)`. Establish `hone : ∀ a b, (1 : M2 (Pr (RadSp k r z z' π π'))) a b ∈ 𝒜`.

Introduce `a b`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Establish `hct : ∀ M : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → ∀ a b, Mᴴ a b ∈ 𝒜`. Introduce `M hM a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Conclude with `star_mem (hM b a)`. Establish `hts : ∀ (Y' : ℂ) (l : Fin r), i.val ≤ l.val → ∀ a b, Ts (site L l) Y' a b ∈ 𝒜`.

Introduce `Y' l hl a b`. Take `⟨hp, hc, hci⟩` from `hS l hl`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Conclude with `add_mem (algebraMap_mem 𝒜 Y') hp`. Conclude with `neg_mem hc`.

Conclude with `hci`. Conclude with `zero_mem _`. Establish `htp : ∀ (Y' : ℂ) (n j : ℕ), r - j = n → i.val ≤ j → ∀ a b, tprod L Y' j a b ∈ 𝒜`. Introduce `Y' n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `j hj hij`. Rewrite using `[tprod, dif_neg (by omega)]`. Conclude with `hone`. Consider the case `succ n ih`.

Introduce `j hj hij`. Rewrite using `[tprod, dif_pos (by omega)]`. Conclude with `hmul _ _ (ih (j + 1) (by omega) (by omega)) (hts Y' ⟨j, by omega⟩ hij)`. Unfold `QQi`. Conclude with `hmul _ _ (hmul _ _ (hct _ (htp _ _ _ rfl le_rfl)) hQ) (htp _ _ _ rfl le_rfl) a b`.
-/
theorem QQi_mem_all (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1)) (Y : ℂ)
    (hQ : ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    QQi L st i Y a b ∈ 𝒜 := by
  have hmul : ∀ M N : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → (∀ a b, N a b ∈ 𝒜) →
      ∀ a b, (M * N) a b ∈ 𝒜 := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hM a c) (hN c b)
  have hone : ∀ a b, (1 : M2 (Pr (RadSp k r z z' π π'))) a b ∈ 𝒜 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hct : ∀ M : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → ∀ a b, Mᴴ a b ∈ 𝒜 := by
    intro M hM a b
    rw [Matrix.conjTranspose_apply]
    exact star_mem (hM b a)
  have hts : ∀ (Y' : ℂ) (l : Fin r), i.val ≤ l.val → ∀ a b, Ts (site L l) Y' a b ∈ 𝒜 := by
    intro Y' l hl a b
    obtain ⟨hp, hc, hci⟩ := hS l hl
    fin_cases a <;> fin_cases b
    · exact add_mem (algebraMap_mem 𝒜 Y') hp
    · exact neg_mem hc
    · exact hci
    · exact zero_mem _
  have htp : ∀ (Y' : ℂ) (n j : ℕ), r - j = n → i.val ≤ j → ∀ a b, tprod L Y' j a b ∈ 𝒜 := by
    intro Y' n
    induction n with
    | zero =>
      intro j hj hij
      rw [tprod, dif_neg (by omega)]
      exact hone
    | succ n ih =>
      intro j hj hij
      rw [tprod, dif_pos (by omega)]
      exact hmul _ _ (ih (j + 1) (by omega) (by omega)) (hts Y' ⟨j, by omega⟩ hij)
  unfold QQi
  exact hmul _ _ (hmul _ _ (hct _ (htp _ _ _ rfl le_rfl)) hQ) (htp _ _ _ rfl le_rfl) a b

/- English proof (translation)
Establish `ht : ∀ Y' : ℂ, tprod L Y' (l.castSucc : ℕ) = tprod L Y' (l.succ : ℕ) * Ts (site L l) Y'`. Introduce `Y'`. Rewrite using `[tprod, dif_pos (show (l.castSucc : ℕ) < r from l.isLt)]`. Both sides reduce to the same expression. Unfold `QQi`.

Rewrite using `[ht, ht, hY, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem QQi_castSucc (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) (Y : ℂ) (hY : star Y = Y) :
    QQi L st l.castSucc Y = (Ts (site L l) Y)ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have ht : ∀ Y' : ℂ, tprod L Y' (l.castSucc : ℕ) = tprod L Y' (l.succ : ℕ) * Ts (site L l) Y' := by
    intro Y'
    rw [tprod, dif_pos (show (l.castSucc : ℕ) < r from l.isLt)]
    rfl
  unfold QQi
  rw [ht, ht, hY, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Take `⟨hpl, -, hL, hQQ, -⟩` from `hD`. Take `⟨sp, sc, sci⟩` from `star_site_ops hL`. Take `⟨hp, -, hc, hci, -⟩` from `hL`. Establish `ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b` using `fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1`. Establish `htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b`.

Introduce `i Y a b`. Rewrite using `[mul_neg, neg_mul, ht]`. Introduce `Y`. Establish `hmem : ∀ a b, QQi L st l.succ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l))`. Use `QQi_mem_all L st _ l.succ Y ?_ ?_` and prove the remaining obligations.

Introduce `a b`. Rewrite using `[hQQ Y, Matrix.smul_apply]`. Use `SMulMemClass.smul_mem _ ?_` and prove the remaining obligations. Simplify using `only [ActualOps.QQ, Matrix.of_apply]`. Rewrite using `[StarSubalgebra.mem_centralizer_iff]`.

Introduce `g hg`. Simplify using `only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg`. Break down `hg with rfl | rfl | rfl` into its components or cases. Rewrite using `[hp l]`. Conclude with `⟨pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩`.

Rewrite using `[hc l]`. Conclude with `⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩`. Rewrite using `[hci l]`. Conclude with `⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩`. Introduce `m hm`.

Establish `hne : l ≠ m`. Introduce `h`. Rewrite `hm` using `[← h, Fin.val_succ]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ y ∈ hol (site L m), y ∈ StarSubalgebra.centralizer ℂ (hol (site L l))`.

Introduce `y hy`. Rewrite using `[StarSubalgebra.mem_centralizer_iff]`. Introduce `g hg`. Conclude with `⟨hol_comm_hol L hne g hg y hy, (hol_comm_star L sp sc sci m l y hy g hg).symm⟩`. Conclude with `⟨key _ (by simp [hol, site]), key _ (by simp [hol, site]), key _ (by simp [hol, site])⟩`.

Introduce `a b x hx`. Establish `h` using `hmem a b`. Rewrite `h` using `[StarSubalgebra.mem_centralizer_iff]`. Break down `hx with hx | hx` into its components or cases. Conclude with `(h x hx).1.symm`.

Establish `h2` using `(h _ hx).2`. Rewrite `h2` using `[star_star]`. Conclude with `h2.symm`.
-/
theorem qqCommutes_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) : QQCommutes (QQi L st l.succ) (site L l) := by
  obtain ⟨hpl, -, hL, hQQ, -⟩ := hD
  obtain ⟨sp, sc, sci⟩ := star_site_ops hL
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
    fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
  have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
    intro i Y a b; rw [mul_neg, neg_mul, ht]
  intro Y
  have hmem : ∀ a b, QQi L st l.succ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    refine QQi_mem_all L st _ l.succ Y ?_ ?_
    · intro a b
      rw [hQQ Y, Matrix.smul_apply]
      refine SMulMemClass.smul_mem _ ?_
      simp only [ActualOps.QQ, Matrix.of_apply]
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · rw [hp l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hc l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hci l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · intro m hm
      have hne : l ≠ m := by
        intro h; rw [← h, Fin.val_succ] at hm; omega
      have key : ∀ y ∈ hol (site L m), y ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
        intro y hy
        rw [StarSubalgebra.mem_centralizer_iff]
        intro g hg
        exact ⟨hol_comm_hol L hne g hg y hy, (hol_comm_star L sp sc sci m l y hy g hg).symm⟩
      exact ⟨key _ (by simp [hol, site]), key _ (by simp [hol, site]), key _ (by simp [hol, site])⟩
  intro a b x hx
  have h := hmem a b
  rw [StarSubalgebra.mem_centralizer_iff] at h
  rcases hx with hx | hx
  · exact (h x hx).1.symm
  · have h2 := (h _ hx).2
    rw [star_star] at h2
    exact h2.symm

/- English proof (translation)
The claim follows from `(by have hL := hD.2.2.1 exact Formalism.FourierDecayAlt.P.site_exchange_relation ℂ _ S (site L l) (QQi L st l.succ) (QQi L st l.castSucc) w (isSite_actual hL l) (qqCommutes_actual P z z' π π' X μ L st l0 hD l) (fun Y hY => QQi_castSucc L st l Y hY) (good_of_adm st w hw.1))`.
-/
theorem siteStep_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (w : List (Letter ℂ S)) (hD : IsData P z z' π π' X μ L st l0) (hw : WordOK P z z' π π' st l0 w) (l : Fin P.r) :
    star (bTl L l w) * RRi L st l.succ w * bTl L l w = RRi L st l.castSucc w := (by
    have hL := hD.2.2.1
    exact Formalism.FourierDecayAlt.P.site_exchange_relation ℂ _ S (site L l) (QQi L st l.succ) (QQi L st l.castSucc) w
      (isSite_actual hL l) (qqCommutes_actual P z z' π π' X μ L st l0 hD l)
      (fun Y hY => QQi_castSucc L st l Y hY) (good_of_adm st w hw.1))

end Top

end Formalism.FourierDecayAlt.P5.HerA
