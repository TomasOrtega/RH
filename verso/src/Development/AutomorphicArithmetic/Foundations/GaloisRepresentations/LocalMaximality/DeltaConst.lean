import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

/- English proof (translation)
Use function extensionality and compare the values at `t`. Express the relevant statement in the definitionally equal form `∑ i ∈ t, GlobalTheory.cubeSign t i • (if (t.erase i).card = 1 then v else 0) = 0`. Distinguish the cases in `h2 : t.card = 2`. Take `⟨a, b, hab, rfl⟩` from `Finset.card_eq_two.1 h2`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases.

Establish `s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = 1` using `GlobalTheory.cubeSign_eq_one_of_forall_le (by`. Introduce `j hj`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hj`. Break down `hj with rfl | rfl` into its components or cases. Conclude with `le_rfl`.

Conclude with `h.le)`. Establish `s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = -1`. Establish `: ({a, b} : Finset ι).filter (· < b) = {a}`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl | rfl, h'⟩`. Both sides reduce to the same expression. Conclude with `absurd h' (lt_irrefl _)`. Introduce and unpack `rfl`.

Conclude with `⟨Or.inl rfl, h⟩`. Simplify using `[GlobalTheory.cubeSign, this]`. Rewrite using `[Finset.sum_pair hab, s1, s2]`. Establish `e1 : (({a, b} : Finset ι).erase a).card = 1`. Rewrite using `[Finset.card_erase_of_mem (by simp), h2]`.

Establish `e2 : (({a, b} : Finset ι).erase b).card = 1`. Rewrite using `[Finset.card_erase_of_mem (by simp), h2]`. Rewrite using `[if_pos e1, if_pos e2]`. Simplify using the standard rewrite rules. Establish `s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = 1` using `GlobalTheory.cubeSign_eq_one_of_forall_le (by`.

Introduce `j hj`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hj`. Break down `hj with rfl | rfl` into its components or cases. Conclude with `h.le`. Conclude with `le_rfl)`.

Establish `s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = -1`. Establish `: ({a, b} : Finset ι).filter (· < a) = {b}`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨rfl | rfl, h'⟩`. Conclude with `absurd h' (lt_irrefl _)`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨Or.inr rfl, h⟩`.

Simplify using `[GlobalTheory.cubeSign, this]`. Rewrite using `[Finset.sum_pair hab, s1, s2]`. Establish `e1 : (({a, b} : Finset ι).erase a).card = 1`. Rewrite using `[Finset.card_erase_of_mem (by simp), h2]`. Establish `e2 : (({a, b} : Finset ι).erase b).card = 1`.

Rewrite using `[Finset.card_erase_of_mem (by simp), h2]`. Rewrite using `[if_pos e1, if_pos e2]`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `: (t.erase i).card ≠ 1`.

Rewrite using `[Finset.card_erase_of_mem hi]`. Use `Finset.card_pos.2 ⟨i, hi⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`.
-/
private theorem delta_const' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) :
    deltaL ℂ ι E (fun J => if J.card = 1 then v else 0) = 0 := by
  funext t
  change ∑ i ∈ t, GlobalTheory.cubeSign t i • (if (t.erase i).card = 1 then v else 0) = 0
  by_cases h2 : t.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · have s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = 1 := GlobalTheory.cubeSign_eq_one_of_forall_le (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact le_rfl
        · exact h.le)
      have s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = -1 := by
        have : ({a, b} : Finset ι).filter (· < b) = {a} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h'⟩
            · rfl
            · exact absurd h' (lt_irrefl _)
          · rintro rfl; exact ⟨Or.inl rfl, h⟩
        simp [GlobalTheory.cubeSign, this]
      rw [Finset.sum_pair hab, s1, s2]
      have e1 : (({a, b} : Finset ι).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      have e2 : (({a, b} : Finset ι).erase b).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      rw [if_pos e1, if_pos e2]; simp
    · have s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = 1 := GlobalTheory.cubeSign_eq_one_of_forall_le (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact h.le
        · exact le_rfl)
      have s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = -1 := by
        have : ({a, b} : Finset ι).filter (· < a) = {b} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h'⟩
            · exact absurd h' (lt_irrefl _)
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, h⟩
        simp [GlobalTheory.cubeSign, this]
      rw [Finset.sum_pair hab, s1, s2]
      have e1 : (({a, b} : Finset ι).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      have e2 : (({a, b} : Finset ι).erase b).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      rw [if_pos e1, if_pos e2]; simp
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : (t.erase i).card ≠ 1 := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[lft, uni]`.
-/
private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i; simp [lft, uni]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[rgt, uni]`.
-/
private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i; simp [rgt, uni]

/- English proof (translation)
The claim follows from `Submodule.span_mono (by rintro y ⟨b, hb, v, hv, rfl⟩ exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩)`.
-/
private theorem omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono (by
    rintro y ⟨b, hb, v, hv, rfl⟩
    exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩)

/- English proof (translation)
Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, v, hv, rfl⟩` from `hy`. Rewrite using `[smul_smul]`. Conclude with `Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, rfl⟩`.

Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a c _ _ ha hc => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hc`. Consider the case `smul z a _ ha => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ z ha`.
-/
private theorem omB_smul' {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {q : ℕ} {r : L} (hr : r ∈ B)
    {m : DR ℂ L} (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    rw [smul_smul]
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
  | smul z a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ z ha

/- English proof (translation)
Use `show c ∈ Submodule.pi Set.univ _ ↔ _`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, forall_true_left]`.
-/
private theorem mem_acxC' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left]

/- English proof (translation)
Establish `hn : I.Nonempty` using `⟨0, h⟩`. Rewrite using `[pk, dif_pos hn]`. Conclude with `le_antisymm (I.min'_le 0 h) (Fin.zero_le _)`.
-/
private theorem pk_zero {d : ℕ} {I : Finset (Fin (d + 1))} (h : 0 ∈ I) : pk I = 0 := by
  have hn : I.Nonempty := ⟨0, h⟩
  rw [pk, dif_pos hn]
  exact le_antisymm (I.min'_le 0 h) (Fin.zero_le _)

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

/- English proof (translation)
The claim follows from `(integralClosure (rA ℂ (xv x) I) K').algebraMap_mem ⟨(x 0 : F) / x m, Algebra.subset_adjoin ⟨m, hm, 0, rfl⟩⟩`.
-/
private theorem inv_mem_rB (I : Finset (Fin (d + 1))) {m : Fin (d + 1)} (hm : m ∈ I) :
    algebraMap F K' ((x 0 : F) / x m) ∈ rB ℂ K' (xv x) I :=
  (integralClosure (rA ℂ (xv x) I) K').algebraMap_mem ⟨(x 0 : F) / x m, Algebra.subset_adjoin ⟨m, hm, 0, rfl⟩⟩

/- English proof (translation)
Rewrite using `[Fin.prod_univ_succ, div_self (x 0).ne_zero, map_one, one_mul]`. Both sides reduce to the same expression.
-/
private theorem prod_tt :
    ∏ l, tt K' x l = ∏ m : Fin (d + 1), algebraMap F K' ((x m : F) / x 0) := by
  rw [Fin.prod_univ_succ, div_self (x 0).ne_zero, map_one, one_mul]
  rfl

/- English proof (translation)
Rewrite using `[prod_tt, ← Finset.prod_mul_prod_compl I, ← mul_assoc, ← Finset.prod_mul_distrib]`. Rewrite using `[Finset.prod_eq_one, one_mul]`. Introduce `m _`. Rewrite using `[← map_mul, div_mul_div_comm, mul_comm (x 0 : F), div_self (mul_ne_zero (x m).ne_zero (x 0).ne_zero), map_one]`.
-/
private theorem prod_compl (I : Finset (Fin (d + 1))) :
    (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) * ∏ l, tt K' x l =
      ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0) := by
  rw [prod_tt, ← Finset.prod_mul_prod_compl I, ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one, one_mul]
  intro m _
  rw [← map_mul, div_mul_div_comm, mul_comm (x 0 : F), div_self (mul_ne_zero (x m).ne_zero (x 0).ne_zero), map_one]

/- English proof (translation)
Rewrite using `[← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]`.
-/
private theorem prod_X (I : Finset (Fin (d + 1))) :
    ∏ m ∈ I, algebraMap F K' (x m : F) =
      algebraMap F K' (x 0 : F) ^ I.card * ∏ m ∈ I, algebraMap F K' ((x m : F) / x 0) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]

/- English proof (translation)
Establish `: algebraMap F K' (x 0 : F) ^ d = ∏ _l : Fin d, algebraMap F K' (x 0 : F)` using `by simp`. Rewrite using `[this, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[tt, ← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]`.
-/
private theorem prod_tt_X :
    ∏ l : Fin d, algebraMap F K' (x l.succ : F) = algebraMap F K' (x 0 : F) ^ d * ∏ l, tt K' x l := by
  have : algebraMap F K' (x 0 : F) ^ d = ∏ _l : Fin d, algebraMap F K' (x 0 : F) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [tt, ← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]

end

/- English proof (translation)
Introduce `hMJ hTh hDt hSB hRY _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY h`. Take `⟨hw, h1, h0, hL⟩` from `hTh d K' (DR ℂ K') (sysY x j2 d)`. Take `⟨τ, hτ⟩` from `hY.covY.exists_isTop`. Take `⟨-, hdt, hvol, hom, -⟩` from `hDt F K' d x hY.covY τ hτ`. Take `⟨hR0, -, hmono, -, -⟩` from `hRY F K K' d x j2 hY`.

Take `⟨v, hv⟩ : ∃ v : DR ℂ K', v = (h : K') • vol0 ℂ K' (xv x)` from `⟨_, rfl⟩`. Set `b : Finset (Fin (d + 1)) → DR ℂ K'` to `fun J => if J.card = 1 then v else 0`. Set `θ` to `detC (sysY x j2 d).rowT`. Establish `hval : ∀ I J L, (sysY x j2 d).mj 0 θ b (uni (uni I J) L) = ((-1 : ℤ) ^ ((0 + 1) * L.card)) • (θ (uni I L) • b J)`. Introduce `I J L`.

Simplify using `only [Sys.mj, lft_uni', rgt_uni']`. Both sides reduce to the same expression. Establish `hcore : ∀ (I : Finset (Fin (d + 1))) (j : Fin (d + 1)), 0 ∈ I → (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v ∈ omB ℂ K' (RY (xv x) j2 I {j}) d`. Introduce `I j h0I`. Establish `hle : rB ℂ K' (xv x) {0} ≤ RY (xv x) j2 I {j}`.

Use `hmono {0} I ∅ {j} (Finset.singleton_subset_iff.2 h0I) (Finset.empty_subset _)` as an intermediate fact. Rewrite `this` using `[hR0]`. Then use the resulting hypothesis. Establish `hwm : (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) ∈ RY (xv x) j2 I {j}` using `(le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I {j}) (Subalgebra.prod_mem _ fun m hm => inv_mem_rB x I hm)`. Establish `hd : dtS K' x Finset.univ ∈ omB ℂ K' (RY (xv x) j2 I {j}) d`. Use `omB_mono' hle _ (hdt Finset.univ)` as an intermediate fact.

Simplify using `using this`. Establish `e : (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v = (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) • (h : K') • dtS K' x Finset.univ`. Rewrite using `[hvol, hom, hv, smul_smul, smul_smul, smul_smul, ← prod_compl]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `omB_smul' hwm (omB_smul' (hle h.2) hd)`. Use `⟨(sysY x j2 d).mj 0 θ b, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(hSB d K' (DR ℂ K') (sysY x j2 d) (Fin d) n10 (gT x j2) (d + 2)).2.1]`. Introduce `I J`.

Use `split_ifs with hIJ`. Use `(mem_acxC' _ _ _ _).2 fun L => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(sysY x j2 d).mj 0 θ b (uni (uni I J) L) ∈ _`. Rewrite using `[hval]`. Distinguish the cases in `hJ : J.card = 1`.

Break down `hL I L with hz | ⟨h0I, hc, ε, hε⟩` into its components or cases. Establish `: θ (uni I L) = 0` using `hz`. Simplify using `[this]`. Take `⟨j, rfl⟩` from `Finset.card_eq_one.1 hJ`. Establish `hcard : ((L.card : ℤ) = (d : ℤ) + 2 - I.card - ({j} : Finset (Fin (d + 1))).card)`.

Simplify using `only [Finset.card_singleton]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos hcard, pk_zero h0I]`. Use `⟨(((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v), Submodule.smul_of_tower_mem _ _ (hcore I j h0I), ?_⟩` and prove the remaining obligations. Establish `hU : (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') = algebraMap F K' (x 0 : F) ^ L.card`.

Rewrite using `[Units.coe_prod, Finset.prod_congr rfl (g := fun _ => algebraMap F K' (x 0 : F)) (fun l _ => by simp [Sys.u, n10, sysY]), Finset.prod_const]`. Establish `hθ : θ (uni I L) = ε • (algebraMap F K' (x 0 : F) ^ L.card * ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0))`. Establish `hcc : Iᶜ.card = L.card`. Rewrite using `[Finset.card_compl, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← hcc, ← prod_X]`. Conclude with `hε`. Establish `hb : b {j} = v` using `if_pos (Finset.card_singleton j)`. Express the relevant statement in the definitionally equal form `(((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') • ((((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v)) = _`. Rewrite using `[hU, hθ, hb, Units.smul_def, smul_assoc]`.

Simplify using `only [mul_smul]`. Rewrite using `[smul_comm (algebraMap F K' (x 0 : F) ^ L.card) ((-1 : ℤ) ^ ((0 + 1) * L.card)), smul_comm (algebraMap F K' (x 0 : F) ^ L.card) (ε : ℤ)]`. Establish `: b J = 0` using `if_neg hJ`. Simplify using `[this]`. Use `(Submodule.mem_bot _).2 (funext fun L => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(sysY x j2 d).mj 0 θ b (uni (uni I J) L) = 0`. Rewrite using `[hval]`. Distinguish the cases in `hJ : J.card = 1`. Establish `hI : ¬ I.Nonempty` using `fun hI => hIJ ⟨hI, Finset.card_pos.1 (by omega)⟩`. Break down `hL I L with hz | ⟨h0I, -⟩` into its components or cases.

Establish `: θ (uni I L) = 0` using `hz`. Simplify using `[this]`. Conclude with `absurd ⟨0, h0I⟩ hI`. Establish `: b J = 0` using `if_neg hJ`. Simplify using `[this]`.

Conclude with `hMJ d K' (DR ℂ K') (sysY x j2 d) (Fin d) (gT x j2) 0 θ b hw (delta_const' v) (fun J hJ => if_neg hJ)`. Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `(sysY x j2 d).mj 0 θ b (uni s ∅) = edge1 (locCoch ℂ K' (xv x) h) s`. Simplify using `only [Sys.mj, lft_uni', rgt_uni', edge1, Finset.card_empty, mul_zero, pow_zero, one_smul]`. Distinguish the cases in `hc : (rgt s).card = 1`.

Rewrite using `[if_pos hc]`. Establish `hb : b (rgt s) = v` using `if_pos hc`. Rewrite using `[hb]`. Distinguish the cases in `hu : lft s = Finset.univ`. Establish `hθ : θ (uni Finset.univ ∅) = 1` using `h1`.

Rewrite using `[hu, hθ, locCoch, if_pos rfl, hv]`. Simplify using `[sysY]`. Rewrite using `[locCoch, if_neg hu]`. Break down `hL (lft s) ∅ with hz | ⟨-, hc', -⟩` into its components or cases. Establish `: θ (uni (lft s) ∅) = 0` using `hz`.

Rewrite using `[this]`. Simplify using `[sysY]`. It suffices to derive a contradiction. Apply `hu` to reduce the goal to its premises. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises.

Simplify using `using hc'`. Rewrite using `[if_neg hc]`. Establish `hb : b (rgt s) = 0` using `if_neg hc`. Rewrite using `[hb, map_zero]`. Introduce `j`.

Rewrite using `[hval]`. Establish `hb : b {j} = v` using `if_pos (Finset.card_singleton j)`. Establish `hθ : θ (uni {0} Finset.univ) = ∏ l : Fin d, algebraMap F K' (x l.succ : F)` using `h0`. Rewrite using `[hb, hθ, prod_tt_X, hv, hvol, hom, Finset.card_univ, Fintype.card_fin, zero_add, one_mul, ← Int.cast_smul_eq_zsmul K', smul_smul, smul_smul, smul_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem yXi_of :
    MJ → ThT → DtBasic → SysBasic → RYBasic → OmLoc → YXi := by
  intro hMJ hTh hDt hSB hRY _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY h
  obtain ⟨hw, h1, h0, hL⟩ := hTh d K' (DR ℂ K') (sysY x j2 d)
  obtain ⟨τ, hτ⟩ := hY.covY.exists_isTop
  obtain ⟨-, hdt, hvol, hom, -⟩ := hDt F K' d x hY.covY τ hτ
  obtain ⟨hR0, -, hmono, -, -⟩ := hRY F K K' d x j2 hY
  obtain ⟨v, hv⟩ : ∃ v : DR ℂ K', v = (h : K') • vol0 ℂ K' (xv x) := ⟨_, rfl⟩
  let b : Finset (Fin (d + 1)) → DR ℂ K' := fun J => if J.card = 1 then v else 0
  let θ := detC (sysY x j2 d).rowT
  have hval : ∀ I J L, (sysY x j2 d).mj 0 θ b (uni (uni I J) L) =
      ((-1 : ℤ) ^ ((0 + 1) * L.card)) • (θ (uni I L) • b J) := by
    intro I J L
    simp only [Sys.mj, lft_uni', rgt_uni']
    rfl
  have hcore : ∀ (I : Finset (Fin (d + 1))) (j : Fin (d + 1)), 0 ∈ I →
      (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v ∈ omB ℂ K' (RY (xv x) j2 I {j}) d := by
    intro I j h0I
    have hle : rB ℂ K' (xv x) {0} ≤ RY (xv x) j2 I {j} := by
      have := hmono {0} I ∅ {j} (Finset.singleton_subset_iff.2 h0I) (Finset.empty_subset _)
      rwa [hR0] at this
    have hwm : (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) ∈ RY (xv x) j2 I {j} :=
      (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I {j})
        (Subalgebra.prod_mem _ fun m hm => inv_mem_rB x I hm)
    have hd : dtS K' x Finset.univ ∈ omB ℂ K' (RY (xv x) j2 I {j}) d := by
      have := omB_mono' hle _ (hdt Finset.univ)
      simpa using this
    have e : (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v =
        (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) • (h : K') • dtS K' x Finset.univ := by
      rw [hvol, hom, hv, smul_smul, smul_smul, smul_smul, ← prod_compl]
      congr 1
      ring
    rw [e]
    exact omB_smul' hwm (omB_smul' (hle h.2) hd)
  refine ⟨(sysY x j2 d).mj 0 θ b, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [(hSB d K' (DR ℂ K') (sysY x j2 d) (Fin d) n10 (gT x j2) (d + 2)).2.1]
    intro I J
    split_ifs with hIJ
    · refine (mem_acxC' _ _ _ _).2 fun L => ?_
      change (sysY x j2 d).mj 0 θ b (uni (uni I J) L) ∈ _
      rw [hval]
      by_cases hJ : J.card = 1
      · rcases hL I L with hz | ⟨h0I, hc, ε, hε⟩
        · have : θ (uni I L) = 0 := hz
          simp [this]
        · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hJ
          have hcard : ((L.card : ℤ) = (d : ℤ) + 2 - I.card - ({j} : Finset (Fin (d + 1))).card) := by
            simp only [Finset.card_singleton]
            omega
          rw [if_pos hcard, pk_zero h0I]
          refine ⟨(((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v),
            Submodule.smul_of_tower_mem _ _ (hcore I j h0I), ?_⟩
          have hU : (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') = algebraMap F K' (x 0 : F) ^ L.card := by
            rw [Units.coe_prod, Finset.prod_congr rfl (g := fun _ => algebraMap F K' (x 0 : F))
              (fun l _ => by simp [Sys.u, n10, sysY]), Finset.prod_const]
          have hθ : θ (uni I L) = ε • (algebraMap F K' (x 0 : F) ^ L.card * ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) := by
            have hcc : Iᶜ.card = L.card := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            rw [← hcc, ← prod_X]
            exact hε
          have hb : b {j} = v := if_pos (Finset.card_singleton j)
          change (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') • ((((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v)) = _
          rw [hU, hθ, hb, Units.smul_def, smul_assoc]
          simp only [mul_smul]
          rw [smul_comm (algebraMap F K' (x 0 : F) ^ L.card) ((-1 : ℤ) ^ ((0 + 1) * L.card)),
            smul_comm (algebraMap F K' (x 0 : F) ^ L.card) (ε : ℤ)]
      · have : b J = 0 := if_neg hJ
        simp [this]
    · refine (Submodule.mem_bot _).2 (funext fun L => ?_)
      change (sysY x j2 d).mj 0 θ b (uni (uni I J) L) = 0
      rw [hval]
      by_cases hJ : J.card = 1
      · have hI : ¬ I.Nonempty := fun hI => hIJ ⟨hI, Finset.card_pos.1 (by omega)⟩
        rcases hL I L with hz | ⟨h0I, -⟩
        · have : θ (uni I L) = 0 := hz
          simp [this]
        · exact absurd ⟨0, h0I⟩ hI
      · have : b J = 0 := if_neg hJ
        simp [this]
  · exact hMJ d K' (DR ℂ K') (sysY x j2 d) (Fin d) (gT x j2) 0 θ b hw (delta_const' v) (fun J hJ => if_neg hJ)
  · funext s
    change (sysY x j2 d).mj 0 θ b (uni s ∅) = edge1 (locCoch ℂ K' (xv x) h) s
    simp only [Sys.mj, lft_uni', rgt_uni', edge1, Finset.card_empty, mul_zero, pow_zero, one_smul]
    by_cases hc : (rgt s).card = 1
    · rw [if_pos hc]
      have hb : b (rgt s) = v := if_pos hc
      rw [hb]
      by_cases hu : lft s = Finset.univ
      · have hθ : θ (uni Finset.univ ∅) = 1 := h1
        rw [hu, hθ, locCoch, if_pos rfl, hv]
        simp [sysY]
      · rw [locCoch, if_neg hu]
        rcases hL (lft s) ∅ with hz | ⟨-, hc', -⟩
        · have : θ (uni (lft s) ∅) = 0 := hz
          rw [this]
          simp [sysY]
        · exfalso
          apply hu
          apply Finset.eq_univ_of_card
          simpa using hc'
    · rw [if_neg hc]
      have hb : b (rgt s) = 0 := if_neg hc
      rw [hb, map_zero]
  · intro j
    rw [hval]
    have hb : b {j} = v := if_pos (Finset.card_singleton j)
    have hθ : θ (uni {0} Finset.univ) = ∏ l : Fin d, algebraMap F K' (x l.succ : F) := h0
    rw [hb, hθ, prod_tt_X, hv, hvol, hom, Finset.card_univ, Fintype.card_fin, zero_add, one_mul,
      ← Int.cast_smul_eq_zsmul K', smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

end UpperTheory.Gal.productCup_of_system
