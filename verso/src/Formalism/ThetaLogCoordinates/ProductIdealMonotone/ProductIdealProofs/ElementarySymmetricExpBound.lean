import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ElementarySymmetricExpBound
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbits
import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ProductIdealProofs.LePowOddOfFloorLogbLe

noncomputable section

open scoped BigOperators Classical Pointwise

namespace Formalism.InvariantFactorPaths.G0

open Formalism.G0

/- English proof (translation)
Introduce `R X _ _ _ _ _ π M M' P g E hPM' hM'M h`. Take `⟨C, hCM, hCg, hC⟩` from `h`. Set `f : (C → R) →ₗ[R] X ⧸ P` to `{ toFun := fun a => ∑ c : C, a c • P.mkQ (c : X) map_add' := by`. Introduce `a b`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`.

Use the proof step `map_smul' := by`. Introduce `r a`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }`. Set `W : Submodule R (X ⧸ P)` to `M'.map (P.mkQ ∘ₗ ((π ^ E) • LinearMap.id))`. Set `U : Submodule R (C → R)` to `W.comap f`.

Take `⟨n, b⟩` from `Submodule.basisOfPid (Pi.basisFun R C) U`. Establish `hn : n ≤ C.card`. Establish `hli : LinearIndependent R (U.subtype ∘ b)` using `b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Establish `h1` using `hli.fintype_card_le_finrank`. Simplify `h1` using `[Module.finrank_fintype_fun_eq_card, Fintype.card_coe]`.

Establish `hm : ∀ i, ∃ x ∈ M', P.mkQ (π ^ E • x) = f (b i)`. Introduce `i`. Establish `h1 : f (b i) ∈ W` using `(b i).2`. Take `⟨x, hx, hxe⟩` from `Submodule.mem_map.mp h1`. Conclude with `⟨x, hx, hxe⟩`.

Use `choose mm hmM hmf using hm`. Use `⟨Finset.univ.image mm, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp (Finset.mem_coe.mp hz)`. Conclude with `hmM i`.

Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `hn.trans hCg`. Introduce `x hx`. Take `⟨p, hp, z, hz, hpz⟩` from `Submodule.mem_sup.mp (hC x (hM'M hx))`.

Take `⟨coef, -, hcoef⟩` from `Submodule.mem_span_finset.mp hz`. Establish `hfa : f (fun c => coef c) = P.mkQ (π ^ E • x)` using `by show ∑ c : C, coef c • P.mkQ (c : X) = _`. Rewrite using `[← hpz, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr hp, zero_add, ← hcoef, map_sum, ← Finset.sum_coe_sort C]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Establish `ha : (fun c : C => coef (c : X)) ∈ U` using `by show f _ ∈ W`. Rewrite using `[hfa]`. Conclude with `Submodule.mem_map.mpr ⟨x, hx, rfl⟩`. Establish `hsum` using `congrArg Subtype.val (b.sum_repr ⟨_, ha⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hsum`.

Use `set r := b.repr ⟨_, ha⟩ with hr`. Establish `hq : P.mkQ (π ^ E • x) = P.mkQ (∑ i, r i • π ^ E • mm i)`. Rewrite using `[← hfa, ← hsum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, hmf i]`.

Establish `hmem : π ^ E • x - ∑ i, r i • π ^ E • mm i ∈ P`. Rewrite using `[← Submodule.ker_mkQ P, LinearMap.mem_ker, map_sub, hq, sub_self]`. Establish `hspan : ∑ i, r i • π ^ E • mm i ∈ Submodule.span R (↑(Finset.univ.image mm) : Set X)` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mm (Finset.mem_univ i)))))`. Conclude with `Submodule.mem_sup.mpr ⟨_, hmem, _, hspan, sub_add_cancel _ _⟩`.
-/
theorem invariant_factors_submodule : InvariantFactorsSubmodule := by
  intro R X _ _ _ _ _ π M M' P g E hPM' hM'M h
  classical
  obtain ⟨C, hCM, hCg, hC⟩ := h

  let f : (C → R) →ₗ[R] X ⧸ P :=
    { toFun := fun a => ∑ c : C, a c • P.mkQ (c : X)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  let W : Submodule R (X ⧸ P) := M'.map (P.mkQ ∘ₗ ((π ^ E) • LinearMap.id))
  let U : Submodule R (C → R) := W.comap f

  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun R C) U
  have hn : n ≤ C.card := by
    have hli : LinearIndependent R (U.subtype ∘ b) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have h1 := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h1
  have hm : ∀ i, ∃ x ∈ M', P.mkQ (π ^ E • x) = f (b i) := by
    intro i
    have h1 : f (b i) ∈ W := (b i).2
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp h1
    exact ⟨x, hx, hxe⟩
  choose mm hmM hmf using hm
  refine ⟨Finset.univ.image mm, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    exact hmM i
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hn.trans hCg
  · intro x hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp (hC x (hM'M hx))
    obtain ⟨coef, -, hcoef⟩ := Submodule.mem_span_finset.mp hz
    have hfa : f (fun c => coef c) = P.mkQ (π ^ E • x) := by
      show ∑ c : C, coef c • P.mkQ (c : X) = _
      rw [← hpz, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr hp, zero_add,
        ← hcoef, map_sum, ← Finset.sum_coe_sort C]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul]
    have ha : (fun c : C => coef (c : X)) ∈ U := by
      show f _ ∈ W
      rw [hfa]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨_, ha⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨_, ha⟩ with hr
    have hq : P.mkQ (π ^ E • x) = P.mkQ (∑ i, r i • π ^ E • mm i) := by
      rw [← hfa, ← hsum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, hmf i]
    have hmem : π ^ E • x - ∑ i, r i • π ^ E • mm i ∈ P := by
      rw [← Submodule.ker_mkQ P, LinearMap.mem_ker, map_sub, hq, sub_self]
    have hspan : ∑ i, r i • π ^ E • mm i ∈
        Submodule.span R (↑(Finset.univ.image mm) : Set X) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mm (Finset.mem_univ i)))))
    exact Submodule.mem_sup.mpr ⟨_, hmem, _, hspan, sub_add_cancel _ _⟩

/- English proof (translation)
Introduce `R X _ _ _ _ _ π A B NA NB g E e hBA hNA hNANB hNBB h`. Take `⟨C, hC, hCg, hCx⟩` from `invariant_factors_submodule π A (B ⊔ NA) NA g E le_sup_right (sup_le hBA hNA) h`. Use `⟨C.image (fun c => π ^ e • c), ?_, Finset.card_image_le.trans hCg, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.mp (Finset.mem_coe.mp hz)`.

Take `⟨b, hb, k, hk, hbk⟩` from `Submodule.mem_sup.mp (hC hc)`. Rewrite using `[← hbk, smul_add]`. Conclude with `B.add_mem (B.smul_mem _ hb) (hNBB (hNANB (Submodule.smul_mem_pointwise_smul k _ _ hk)))`. Introduce `x hx`. Take `⟨p, hp, z, hz, hpz⟩` from `Submodule.mem_sup.mp (hCx x (le_sup_left (a := B) hx))`.

Rewrite using `[pow_add, mul_comm, mul_smul, ← hpz, smul_add]`. Establish `hz' : π ^ e • z ∈ Submodule.span R (↑(C.image (fun c => π ^ e • c)) : Set X)`. Use `Submodule.span_induction (p := fun z _ => π ^ e • z ∈ Submodule.span R (↑(C.image (fun c => π ^ e • c)) : Set X)) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce `c hc`. Conclude with `Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc))`.

Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`. Rewrite using `[smul_add]`. Conclude with `add_mem ha hb`. Introduce `r a _ ha`.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ _ ha`. Conclude with `Submodule.mem_sup.mpr ⟨_, hNANB (Submodule.smul_mem_pointwise_smul _ _ _ hp), _, hz', rfl⟩`.
-/
theorem inverse_shift : InvShift := by
  intro R X _ _ _ _ _ π A B NA NB g E e hBA hNA hNANB hNBB h
  classical
  obtain ⟨C, hC, hCg, hCx⟩ :=
    invariant_factors_submodule π A (B ⊔ NA) NA g E le_sup_right (sup_le hBA hNA) h
  refine ⟨C.image (fun c => π ^ e • c), ?_, Finset.card_image_le.trans hCg, ?_⟩
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    obtain ⟨b, hb, k, hk, hbk⟩ := Submodule.mem_sup.mp (hC hc)
    rw [← hbk, smul_add]
    exact B.add_mem (B.smul_mem _ hb)
      (hNBB (hNANB (Submodule.smul_mem_pointwise_smul k _ _ hk)))
  · intro x hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp (hCx x (le_sup_left (a := B) hx))
    rw [pow_add, mul_comm, mul_smul, ← hpz, smul_add]
    have hz' : π ^ e • z ∈ Submodule.span R (↑(C.image (fun c => π ^ e • c)) : Set X) := by
      refine Submodule.span_induction (p := fun z _ => π ^ e • z ∈
        Submodule.span R (↑(C.image (fun c => π ^ e • c)) : Set X)) ?_ ?_ ?_ ?_ hz
      · intro c hc
        exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc))
      · simp
      · intro a b _ _ ha hb
        rw [smul_add]
        exact add_mem ha hb
      · intro r a _ ha
        rw [smul_comm]
        exact Submodule.smul_mem _ _ ha
    exact Submodule.mem_sup.mpr ⟨_, hNANB (Submodule.smul_mem_pointwise_smul _ _ _ hp), _, hz', rfl⟩

/- English proof (translation)
Unfold `pp`. Break down `le_total x y with h | h` into its components or cases. Rewrite using `[max_eq_right h, max_eq_right (by linarith : x - y ≤ 0)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[max_eq_left h, max_eq_left (by linarith : 0 ≤ x - y)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem max_eq_add_pp (x y : ℝ) : max x y = y + pp (x - y) := by
  unfold pp
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : x - y ≤ 0)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith : 0 ≤ x - y)]
    ring

/- English proof (translation)
Establish `hl : ∀ (c : Fin V → R) (f : Fin V → Module.End R X) (l : List (Fin V)), (l.map fun v => c v • f v).prod = (l.map c).prod • (l.map f).prod`. Introduce `c f l`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, smul_mul_smul_comm]`.

Establish `hf : (fun v => if E v = true then y v ^ m else (π ^ Sv v) • (1 : Module.End R X)) = fun v => π ^ (if E v = true then 0 else Sv v) • (if E v = true then y v ^ m else (π ^ (fun _ => 0) v) • (1 : Module.End R X))`. Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases h : E v = true <;> simp [h]`. Unfold `monoOp`. Rewrite using `[hf, hl, ← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]`.
-/
theorem monoOp_eq_smul {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (Sv : Fin V → ℕ) (E : Fin V → Bool) :
    monoOp π y m Sv E =
      π ^ (∑ v, if E v = true then 0 else Sv v) • monoOp π y m (fun _ => 0) E := by
  have hl : ∀ (c : Fin V → R) (f : Fin V → Module.End R X) (l : List (Fin V)),
      (l.map fun v => c v • f v).prod = (l.map c).prod • (l.map f).prod := by
    intro c f l
    induction l with
    | nil => simp
    | cons a l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons,
        List.map_cons, List.prod_cons, smul_mul_smul_comm]
  have hf : (fun v => if E v = true then y v ^ m else (π ^ Sv v) • (1 : Module.End R X)) =
      fun v => π ^ (if E v = true then 0 else Sv v) •
        (if E v = true then y v ^ m else (π ^ (fun _ => 0) v) • (1 : Module.End R X)) := by
    funext v
    by_cases h : E v = true <;> simp [h]
  unfold monoOp
  rw [hf, hl, ← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro t z hz`. Simplify using `using hz`. Consider the case `succ k ih`. Introduce `t z hz`.

Establish `h1` using `h _ _ (ih t z hz)`. Rewrite using `[pow_succ', mul_smul]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fil_pow_smul {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] (π : R) (vπ : ℝ)
    (Fil : ℝ → Submodule R Z) (h : ∀ t z, z ∈ Fil t → π • z ∈ Fil (t + vπ)) (k : ℕ) :
    ∀ t z, z ∈ Fil t → π ^ k • z ∈ Fil (t + vπ * (k : ℝ)) := by
  induction k with
  | zero => intro t z hz; simpa using hz
  | succ k ih =>
    intro t z hz
    have h1 := h _ _ (ih t z hz)
    rw [pow_succ', mul_smul]
    convert h1 using 2
    push_cast
    ring

/- English proof (translation)
Introduce `R X Z _ _ _ _ _ π vπ V m M y Sv K Fil g Pr g0 rest hanti hπ hS hE F hF`. Establish `key : ∀ E : Fin V → Bool, M.map (monoOp π y m Sv E) ≤ (Fil ((∑ j, ∑ v, max (g v j - Pr v j) (g0 v j)) + rest)).comap K`. Introduce `E`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Submodule.mem_comap, monoOp_eq_smul, LinearMap.smul_apply, map_smul]`.

Establish `h1` using `fil_pow_smul π vπ Fil hπ (∑ v, if E v = true then 0 else Sv v) _ _ (hE E x hx)`. Use `hanti ?_ h1` and prove the remaining obligations. Establish `hsplit : ∀ j, ∑ v, max (g v j - Pr v j) (g0 v j) = (∑ v with E v = true, max (g v j - Pr v j) (g0 v j)) + ∑ v with E v = false, g0 v j + ∑ v with E v = false, pp (g v j - Pr v j - g0 v j)`. Introduce `j`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => E v = true)]`.

Simplify using `only [Bool.not_eq_true]`. Rewrite using `[add_assoc, ← Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun v _ => max_eq_add_pp _ _`. Establish `hpp : ∑ j, ∑ v with E v = false, pp (g v j - Pr v j - g0 v j) ≤ vπ * ((∑ v, if E v = true then 0 else Sv v : ℕ) : ℝ)`.

Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum, Finset.sum_filter]`. Use `congr 1`. Use `push_cast`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `cases E v <;> simp`. Simplify using `only [hsplit, Finset.sum_add_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `iSup_le key hF`.
-/
theorem almost_everywhere_spherical : AlmostEverywhereSpherical := by
  intro R X Z _ _ _ _ _ π vπ V m M y Sv K Fil g Pr g0 rest hanti hπ hS hE F hF
  have key : ∀ E : Fin V → Bool, M.map (monoOp π y m Sv E) ≤
      (Fil ((∑ j, ∑ v, max (g v j - Pr v j) (g0 v j)) + rest)).comap K := by
    intro E
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.mem_comap, monoOp_eq_smul, LinearMap.smul_apply, map_smul]
    have h1 := fil_pow_smul π vπ Fil hπ (∑ v, if E v = true then 0 else Sv v) _ _ (hE E x hx)
    refine hanti ?_ h1

    have hsplit : ∀ j, ∑ v, max (g v j - Pr v j) (g0 v j) =
        (∑ v with E v = true, max (g v j - Pr v j) (g0 v j)) + ∑ v with E v = false, g0 v j
          + ∑ v with E v = false, pp (g v j - Pr v j - g0 v j) := by
      intro j
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => E v = true)]
      simp only [Bool.not_eq_true]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun v _ => max_eq_add_pp _ _
    have hpp : ∑ j, ∑ v with E v = false, pp (g v j - Pr v j - g0 v j) ≤
        vπ * ((∑ v, if E v = true then 0 else Sv v : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      calc ∑ v with E v = false, ∑ j, pp (g v j - Pr v j - g0 v j)
          ≤ ∑ v with E v = false, vπ * (Sv v : ℝ) := Finset.sum_le_sum fun v _ => hS v
        _ = vπ * ((∑ v, if E v = true then 0 else Sv v : ℕ) : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_filter]
          congr 1
          push_cast
          refine Finset.sum_congr rfl fun v _ => ?_
          cases E v <;> simp
    simp only [hsplit, Finset.sum_add_distrib]
    linarith
  exact iSup_le key hF

end Formalism.InvariantFactorPaths.G0
