import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section CycEval

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Unfold `cycEval`. Use `finsum_congr fun W => ?_` and prove the remaining obligations. Distinguish the cases in `hW : Z W = 0`. Rewrite using `[hW, zero_mul, zero_mul]`. Rewrite using `[h W hW]`.
-/
theorem cycEval_congr_support {n n' Z : Ideal (MRing ι R) → ℤ} (h : ∀ W, Z W ≠ 0 → n W = n' W) :
    cycEval n Z = cycEval n' Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · rw [hW, zero_mul, zero_mul]
  · rw [h W hW]

/- English proof (translation)
Rewrite using `[cycEval_eq_sum hZ, cycEval_eq_sum hZ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cycEval_mul_left (c : ℤ) (n Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => c * n W) Z = c * cycEval n Z := by
  rw [cycEval_eq_sum hZ, cycEval_eq_sum hZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

/- English proof (translation)
Rewrite using `[cycEval_eq_sum hZ]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[cycEval_eq_sum hZ]`.
-/
theorem cycEval_finset_sum {α : Type*} (S : Finset α) (F : α → Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => ∑ a ∈ S, F a W) Z = ∑ a ∈ S, cycEval (F a) Z := by
  rw [cycEval_eq_sum hZ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cycEval_eq_sum hZ]

/- English proof (translation)
Establish `h₃ : (Function.support (Z₁ - Z₂)).Finite` using `(h₁.union h₂).subset (Function.support_sub Z₁ Z₂)`. Set `S` to `h₁.toFinset ∪ h₂.toFinset`. Establish `e : ∀ Z : Ideal (MRing ι R) → ℤ, Function.support Z ⊆ S → cycEval n Z = ∑ W ∈ S, Z W * n W`. Introduce `Z hZS`. Unfold `cycEval`.

Use `finsum_eq_sum_of_support_subset _ fun W hW => hZS (Function.support_mul_subset_left _ _ hW)` and prove the remaining obligations. Establish `s₁ : Function.support Z₁ ⊆ S` using `fun W hW => by simp [S, hW]`. Establish `s₂ : Function.support Z₂ ⊆ S` using `fun W hW => by simp [S, hW]`. Rewrite using `[e Z₁ s₁, e Z₂ s₂, e (Z₁ - Z₂) ((Function.support_sub Z₁ Z₂).trans (Set.union_subset s₁ s₂)), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cycEval_sub_cycle (n Z₁ Z₂ : Ideal (MRing ι R) → ℤ) (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) :
    cycEval n Z₁ - cycEval n Z₂ = cycEval n (Z₁ - Z₂) := by
  have h₃ : (Function.support (Z₁ - Z₂)).Finite :=
    (h₁.union h₂).subset (Function.support_sub Z₁ Z₂)
  let S := h₁.toFinset ∪ h₂.toFinset
  have e : ∀ Z : Ideal (MRing ι R) → ℤ, Function.support Z ⊆ S → cycEval n Z = ∑ W ∈ S, Z W * n W := by
    intro Z hZS
    unfold cycEval
    refine finsum_eq_sum_of_support_subset _ fun W hW => hZS (Function.support_mul_subset_left _ _ hW)
  have s₁ : Function.support Z₁ ⊆ S := fun W hW => by simp [S, hW]
  have s₂ : Function.support Z₂ ⊆ S := fun W hW => by simp [S, hW]
  rw [e Z₁ s₁, e Z₂ s₂, e (Z₁ - Z₂) ((Function.support_sub Z₁ Z₂).trans (Set.union_subset s₁ s₂)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [Pi.sub_apply]
  ring

end CycEval

section Additivity

/- English proof (translation)
Establish `hPmh : IsMultiHomogIdeal P` using `hP.multiProj.multiHomog`. Establish `: P.IsPrime` using `hP.multiProj.isPrime`. Establish `hϖP : (C ϖ : MRing ι O) ∉ P`. Introduce `h`. Establish `h' : ϖ ∈ P.comap (C : O →+* MRing ι O)` using `h`.

Rewrite `h'` using `[hP.noTorsion, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero h'`. Unfold `divCycle at hW`. Use `split_ifs at hW with hW''`. Use `swap`.

Conclude with `absurd rfl hW`. Establish `hWm : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P s c hPmh hs) hW''.1`. Establish `hWp : W.IsPrime` using `hW''.1.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW''.1.1.2`. Establish `hlt : P < W` using `lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))`.

Establish `hdrop` using `DimStrictDrop.full (MRing ι O) P W hlt`. Rewrite `hdrop` using `[hP.dim]`. Establish `hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) < ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[SpecialQuotDim.full O ϖ hϖ K ι W hϖW]`. Use `lt_of_lt_of_le (lt_natCast_of_add_one_le hdrop) ?_` and prove the remaining obligations.

Conclude with `(by omega : e + 1 + 1 + Fintype.card K ≤ l.length + 2 + Fintype.card K)` after adjusting the coercions. Establish `key` using `IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W) (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm) hdim a₁ a₂ l.get`. Establish `e' : ∀ c, vNumL W (c :: l) = intNum (IsLocalRing.ResidueField O) (specialIdeal W) (Matrix.vecCons c l.get)`. Introduce `c`. Express the relevant statement in the definitionally equal form `_ = vNum W (Matrix.vecCons c l.get)`.

Rewrite using `[vNum_vecCons_eq, List.ofFn_get]`. Rewrite using `[e', e', e', key]`.
-/
theorem vNumL_add_of_divCycle_ne_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1))
    {c : K → ℕ} {s : MRing ι O} (hs : IsMultiHomog s c) {W : Ideal (MRing ι O)}
    (hW : divCycle P s W ≠ 0) (hϖW : (C ϖ : MRing ι O) ∈ W) (a₁ a₂ : K → ℤ) (l : List (K → ℤ))
    (hl : e ≤ l.length) :
    vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l) := by
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  unfold divCycle at hW
  split_ifs at hW with hW''
  swap
  · exact absurd rfl hW
  have hWm : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P s c hPmh hs) hW''.1
  have hWp : W.IsPrime := hW''.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW''.1.1.2
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
    refine lt_of_lt_of_le (lt_natCast_of_add_one_le hdrop) ?_
    exact_mod_cast (by omega : e + 1 + 1 + Fintype.card K ≤ l.length + 2 + Fintype.card K)
  have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W)
    (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
    hdim a₁ a₂ l.get
  have e' : ∀ c, vNumL W (c :: l) =
      intNum (IsLocalRing.ResidueField O) (specialIdeal W) (Matrix.vecCons c l.get) := by
    intro c
    change _ = vNum W (Matrix.vecCons c l.get)
    rw [vNum_vecCons_eq, List.ofFn_get]
  rw [e', e', e', key]

end Additivity

section Cut

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

/- English proof (translation)
Establish `h` using `hC3 O ϖ hϖ K ι P l.length hP b f g hD c s hs hsP hgen l.get`. Simplify using `only [vNum_vecCons_eq, List.ofFn_get] at h`. Conclude with `h`.
-/
theorem cut_list (hC3 : CutByEffectiveDivisor.Statement.{0}) (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {c : K → ℕ} {s : MRing ι O}
    (hs : IsMultiHomog s c) (hsP : s ∉ P)
    (hgen : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g)
    (l : List (K → ℤ)) (hP : IsModelOver P (l.length + 1)) :
    cycEval (fun G => vNumL G ((fun k => (c k : ℤ)) :: l)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W (b :: l)
        else cycEval (fun G => vNumL G l) (ratDiv W f g)) (divCycle P s) := by
  have h := hC3 O ϖ hϖ K ι P l.length hP b f g hD c s hs hsP hgen l.get
  simp only [vNum_vecCons_eq, List.ofFn_get] at h
  exact h

open Classical in

/- English proof (translation)
Establish `e1` using `cut_list hC3 hϖ hD hs hsP (fun H hH => hgen H (Or.inl hH)) l hP`. Establish `e2` using `cut_list hC3 hϖ hD hh hhP (fun H hH => hgen H (Or.inr hH)) l hP`. Establish `hr : ratDiv P s h = divCycle P s - divCycle P h` using `rfl`. Establish `hfg` using `ratDiv_finite_support P f g`. Rewrite using `[hr, ← cycEval_sub_cycle _ _ _ (divCycle_finite_support P s) (divCycle_finite_support P h), ← e1, ← e2, cycEval_eq_sum hfg, cycEval_eq_sum hfg, cycEval_eq_sum hfg, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun G hG => ?_` and prove the remaining obligations. Establish `hG' : ratDiv P f g G ≠ 0` using `by simpa using hG`. Establish `hadd` using `vNumL_add_of_ratDiv_ne_zero hϖ hP hD hG' (fun k => (cs k : ℤ) - ch k) (fun k => (ch k : ℤ)) l le_rfl`. Establish `e : ((fun k => (cs k : ℤ) - ch k) + fun k => (ch k : ℤ)) = fun k => (cs k : ℤ)`. Use function extensionality and compare the values at `k`.

Simplify using the standard rewrite rules. Rewrite `hadd` using `[e]`. Rewrite using `[hadd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cut_list_ratDiv (hC3 : CutByEffectiveDivisor.Statement.{0}) (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    {cs ch : K → ℕ} {s h : MRing ι O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hsP : s ∉ P)
    (hhP : h ∉ P)
    (hgen : ∀ H, (divCycle P s H ≠ 0 ∨ divCycle P h H ≠ 0) → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b f g)
    (l : List (K → ℤ)) (hP : IsModelOver P (l.length + 1)) :
    cycEval (fun G => vNumL G ((fun k => (cs k : ℤ) - ch k) :: l)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W (b :: l)
        else cycEval (fun G => vNumL G l) (ratDiv W f g)) (ratDiv P s h) := by
  have e1 := cut_list hC3 hϖ hD hs hsP (fun H hH => hgen H (Or.inl hH)) l hP
  have e2 := cut_list hC3 hϖ hD hh hhP (fun H hH => hgen H (Or.inr hH)) l hP
  have hr : ratDiv P s h = divCycle P s - divCycle P h := rfl
  have hfg := ratDiv_finite_support P f g
  rw [hr, ← cycEval_sub_cycle _ _ _ (divCycle_finite_support P s) (divCycle_finite_support P h), ← e1, ← e2,
    cycEval_eq_sum hfg, cycEval_eq_sum hfg, cycEval_eq_sum hfg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hG' : ratDiv P f g G ≠ 0 := by simpa using hG
  have hadd := vNumL_add_of_ratDiv_ne_zero hϖ hP hD hG' (fun k => (cs k : ℤ) - ch k)
    (fun k => (ch k : ℤ)) l le_rfl
  have e : ((fun k => (cs k : ℤ) - ch k) + fun k => (ch k : ℤ)) = fun k => (cs k : ℤ) := by
    funext k
    simp
  rw [e] at hadd
  rw [hadd]
  ring

open Classical in

/- English proof (translation)
Use `set c : K → ℤ := fun k => (cs k : ℤ) - ch k with hc`. Use `set cl : Fin r ⊕ Fin r → K → ℤ := Sum.elim z z' with hcl`. Establish `hsh` using `ratDiv_finite_support P s h`. Establish `hlen : ∀ i, ∀ μ ∈ (Bs i).support, (classList cl μ ++ Q).length = e`. Introduce `i μ hμ`.

Rewrite using `[List.length_append, classList_length_of_mem_support _ (hBs.homogeneous i) hμ]`. Use linear arithmetic over natural numbers and integers. Establish `step : ∀ i, ∀ μ ∈ (Bs i).support, cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) = cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W ((z i - z' i) :: (classList cl μ ++ Q)) else cycEval (fun G => vNumL G (classList cl μ ++ Q)) (ratDiv W (fs …`. Introduce `i μ hμ`. Use `cut_list_ratDiv hC3 hϖ (hD i) hs hh hsP hhP (fun H hH hϖH => hgen H hH hϖH i) _ ?_` and prove the remaining obligations.

Rewrite using `[hlen i μ hμ]`. Conclude with `hP`. Establish `hL : pairNum P z z' fs gs Bs (c :: Q) = ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i))`. Unfold `pairNum`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `e1 : (fun W : Ideal (MRing ι O) => classNum (Sum.elim z z') (Bs i) (c :: Q) W) = fun W : Ideal (MRing ι O) => ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL W (c :: (classList cl μ ++ Q))`. Use function extensionality and compare the values at `W`. Unfold `classNum`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[vNumL_perm W List.perm_middle]`.

Rewrite using `[e1, cycEval_finset_sum _ _ _ (ratDiv_finite_support P (fs i) (gs i))]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[cycEval_mul_left _ _ _ (ratDiv_finite_support P (fs i) (gs i))]`. Rewrite using `[hL]`. Establish `hR : ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) = cycEval (fun W => ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * (if (C ϖ : MRing ι O) ∈ W then vNumL W ((z i - z' i) :: (classList cl μ ++ Q)) else cy …`.

Rewrite using `[cycEval_finset_sum _ _ _ hsh]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[cycEval_finset_sum _ _ _ hsh]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[cycEval_mul_left _ _ _ hsh, step i μ hμ]`.

Rewrite using `[hR]`. Use `cycEval_congr_support fun W hW => ?_` and prove the remaining obligations. Distinguish the cases in `hϖW : (C ϖ : MRing ι O) ∈ W`. Simplify using `only [if_pos hϖW]`. Establish `hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length → vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l)`.

Introduce `a₁ a₂ l hl`. Distinguish the cases in `h1 : divCycle P s W = 0`. Establish `h2 : divCycle P h W ≠ 0`. Introduce `h2`. Apply `hW` to reduce the goal to its premises.

Simplify using `[ratDiv, h1, h2]`. Conclude with `vNumL_add_of_divCycle_ne_zero hϖ hP hh h2 hϖW a₁ a₂ l hl`. Conclude with `vNumL_add_of_divCycle_ne_zero hϖ hP hs h1 hϖW a₁ a₂ l hl`. Establish `ht : e ≤ (m - 1) + Q.length` using `by omega`. Establish `e2 : ∀ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL W ((z i - z' i) :: (classList cl μ ++ Q)) = classNum cl (pairDiff i * Bs i) Q W` using `fun i => (classNum_pairDiff_mul hadd z z' i (hBs.homogeneous i) Q ht).symm`.

Simplify using `only [e2]`. Establish `e3` using `map_sum (classNumAddHom cl Q W) (fun i => pairDiff i * Bs i) Finset.univ`. Simplify using `only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e3`. Rewrite using `[← e3]`. Establish `e4 : ∑ i, pairDiff i * Bs i = rename Sum.inl A - rename Sum.inr A`.

Rewrite using `[hBs.expansion]`. Both sides reduce to the same expression. Rewrite using `[e4]`. Establish `e5` using `map_sub (classNumAddHom cl Q W) (rename Sum.inl A) (rename Sum.inr A)`. Simplify using `only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e5`.

Rewrite using `[e5, classNum_rename_vars, classNum_rename_vars]`. Both sides reduce to the same expression. Simplify using `only [if_neg hϖW]`. Unfold `pairNum`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `e1 : (fun G : Ideal (MRing ι O) => classNum (Sum.elim z z') (Bs i) Q G) = fun G : Ideal (MRing ι O) => ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL G (classList cl μ ++ Q)` using `rfl`. Rewrite using `[e1, cycEval_finset_sum _ _ _ (ratDiv_finite_support W (fs i) (gs i))]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[cycEval_mul_left _ _ _ (ratDiv_finite_support W (fs i) (gs i))]`.
-/
theorem pairNum_cut_section (hC3 : CutByEffectiveDivisor.Statement.{0}) (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1)) {r : ℕ} (z z' : Fin r → K → ℤ)
    (fs gs : Fin r → MRing ι O) (hD : ∀ i, IsVerticalDivisor P ϖ (z i - z' i) (fs i) (gs i))
    {cs ch : K → ℕ} {s h : MRing ι O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hsP : s ∉ P)
    (hhP : h ∉ P)
    (hgen : ∀ H, (divCycle P s H ≠ 0 ∨ divCycle P h H ≠ 0) → (C ϖ : MRing ι O) ∉ H →
      ∀ i, IsVerticalDivisor H ϖ (z i - z' i) (fs i) (gs i))
    {m : ℕ} (hm : 1 ≤ m) {A : MvPolynomial (Fin r) ℤ} {Bs : Fin r → MvPolynomial (Fin r ⊕ Fin r) ℤ}
    (hBs : IsPairExpansion m A Bs) (Q : List (K → ℤ)) (hQ : Q.length + m = e + 1) :
    pairNum P z z' fs gs Bs ((fun k => (cs k : ℤ) - ch k) :: Q) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then classNum z A Q W - classNum z' A Q W
        else pairNum W z z' fs gs Bs Q) (ratDiv P s h) := by
  set c : K → ℤ := fun k => (cs k : ℤ) - ch k with hc
  set cl : Fin r ⊕ Fin r → K → ℤ := Sum.elim z z' with hcl
  have hsh := ratDiv_finite_support P s h
  have hlen : ∀ i, ∀ μ ∈ (Bs i).support, (classList cl μ ++ Q).length = e := by
    intro i μ hμ
    rw [List.length_append, classList_length_of_mem_support _ (hBs.homogeneous i) hμ]
    omega

  have step : ∀ i, ∀ μ ∈ (Bs i).support,
      cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) =
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W ((z i - z' i) :: (classList cl μ ++ Q))
          else cycEval (fun G => vNumL G (classList cl μ ++ Q)) (ratDiv W (fs i) (gs i))) (ratDiv P s h) := by
    intro i μ hμ
    refine cut_list_ratDiv hC3 hϖ (hD i) hs hh hsP hhP (fun H hH hϖH => hgen H hH hϖH i) _ ?_
    rw [hlen i μ hμ]
    exact hP

  have hL : pairNum P z z' fs gs Bs (c :: Q) = ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ *
      cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) := by
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (fun W : Ideal (MRing ι O) => classNum (Sum.elim z z') (Bs i) (c :: Q) W) =
        fun W : Ideal (MRing ι O) => ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL W (c :: (classList cl μ ++ Q)) := by
      funext W
      unfold classNum
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [vNumL_perm W List.perm_middle]
    rw [e1, cycEval_finset_sum _ _ _ (ratDiv_finite_support P (fs i) (gs i))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [cycEval_mul_left _ _ _ (ratDiv_finite_support P (fs i) (gs i))]
  rw [hL]
  have hR : ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ *
      cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) =
      cycEval (fun W => ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ *
        (if (C ϖ : MRing ι O) ∈ W then vNumL W ((z i - z' i) :: (classList cl μ ++ Q))
          else cycEval (fun G => vNumL G (classList cl μ ++ Q)) (ratDiv W (fs i) (gs i)))) (ratDiv P s h) := by
    rw [cycEval_finset_sum _ _ _ hsh]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cycEval_finset_sum _ _ _ hsh]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [cycEval_mul_left _ _ _ hsh, step i μ hμ]
  rw [hR]
  refine cycEval_congr_support fun W hW => ?_
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · simp only [if_pos hϖW]

    have hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
        vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l) := by
      intro a₁ a₂ l hl
      by_cases h1 : divCycle P s W = 0
      · have h2 : divCycle P h W ≠ 0 := by
          intro h2
          apply hW
          simp [ratDiv, h1, h2]
        exact vNumL_add_of_divCycle_ne_zero hϖ hP hh h2 hϖW a₁ a₂ l hl
      · exact vNumL_add_of_divCycle_ne_zero hϖ hP hs h1 hϖW a₁ a₂ l hl
    have ht : e ≤ (m - 1) + Q.length := by omega
    have e2 : ∀ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL W ((z i - z' i) :: (classList cl μ ++ Q)) =
        classNum cl (pairDiff i * Bs i) Q W := fun i =>
      (classNum_pairDiff_mul hadd z z' i (hBs.homogeneous i) Q ht).symm
    simp only [e2]
    have e3 := map_sum (classNumAddHom cl Q W) (fun i => pairDiff i * Bs i) Finset.univ
    simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e3
    rw [← e3]
    have e4 : ∑ i, pairDiff i * Bs i = rename Sum.inl A - rename Sum.inr A := by
      rw [hBs.expansion]
      rfl
    rw [e4]
    have e5 := map_sub (classNumAddHom cl Q W) (rename Sum.inl A) (rename Sum.inr A)
    simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e5
    rw [e5, classNum_rename_vars, classNum_rename_vars]
    rfl
  · simp only [if_neg hϖW]
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (fun G : Ideal (MRing ι O) => classNum (Sum.elim z z') (Bs i) Q G) =
        fun G : Ideal (MRing ι O) => ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL G (classList cl μ ++ Q) := rfl
    rw [e1, cycEval_finset_sum _ _ _ (ratDiv_finite_support W (fs i) (gs i))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [cycEval_mul_left _ _ _ (ratDiv_finite_support W (fs i) (gs i))]

end Cut

end

end GroundTheory.Heights₂.Heights.NumbersDVR
