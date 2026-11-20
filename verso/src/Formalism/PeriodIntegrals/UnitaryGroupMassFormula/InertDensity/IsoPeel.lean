import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.FinrankInfKerAddOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ExistsTraceNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ValMain

open Finset Module

noncomputable section

namespace DensInertW

open DensInertW.Sub

section
variable {L : Type} [Field L]

/- English proof (translation)
Rewrite `h`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `h (Fin.cons (-(∑ j, g j * a j)) g) (by` as an intermediate fact. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Rewrite using `[← hg]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, neg_smul]`. Use the proof step `abel) i.succ`. Simplify using `using this`.
-/
theorem iso_li_tail {n c : ℕ} (x : Fin n → L) (X' : Fin c → Fin n → L) (a : Fin c → L)
    (h : LinearIndependent L (Fin.cons x X' : Fin (c + 1) → Fin n → L)) :
    LinearIndependent L (fun i => X' i - a i • x) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have := h (Fin.cons (-(∑ j, g j * a j)) g) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hg]
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, neg_smul]
    abel) i.succ
  simpa using this

/- English proof (translation)
Rewrite `hU`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hg`. Establish `h1` using `congrArg φ hg`.

Simplify using `only [map_add, map_sum, map_smul, hφx, hφU, smul_eq_mul, mul_one, add_zero, mul_add, mul_zero, map_zero] at h1`. Establish `h2 : ∑ i, g i.succ • U i = 0`. Establish `e : ∑ i, g i.succ • U i + (g 0 + ∑ i, g i.succ * a i) • x = 0`. Rewrite using `[← hg]`. Simplify using `only [smul_add, Finset.sum_add_distrib, add_smul, Finset.sum_smul, smul_smul]`.

Normalize the expressions using the abelian group laws. Establish `h1' : g 0 + ∑ i, g i.succ * a i = 0` using `by simpa using h1`. Rewrite `e` using `[h1', zero_smul, add_zero]`. Conclude with `e`. Establish `hs` using `hU _ h2`.

Introduce `i`. Use `Fin.cases ?_ (fun j => hs j) i` and prove the remaining obligations. Simplify `h1` using `[hs]`.
-/
theorem iso_li_cons {n c : ℕ} (x : Fin n → L) (U : Fin c → Fin n → L) (a : Fin c → L)
    (φ : (Fin n → L) →ₗ[L] L) (hφx : φ x = 1) (hφU : ∀ i, φ (U i) = 0)
    (hU : LinearIndependent L U) :
    LinearIndependent L (Fin.cons x (fun i => U i + a i • x) : Fin (c + 1) → Fin n → L) := by
  rw [Fintype.linearIndependent_iff] at hU ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have h1 := congrArg φ hg
  simp only [map_add, map_sum, map_smul, hφx, hφU, smul_eq_mul, mul_one, add_zero, mul_add, mul_zero,
    map_zero] at h1
  have h2 : ∑ i, g i.succ • U i = 0 := by
    have e : ∑ i, g i.succ • U i + (g 0 + ∑ i, g i.succ * a i) • x = 0 := by
      rw [← hg]
      simp only [smul_add, Finset.sum_add_distrib, add_smul, Finset.sum_smul, smul_smul]
      abel
    have h1' : g 0 + ∑ i, g i.succ * a i = 0 := by simpa using h1
    rw [h1', zero_smul, add_zero] at e
    exact e
  have hs := hU _ h2
  intro i
  refine Fin.cases ?_ (fun j => hs j) i
  simpa [hs] using h1

def isoP {n m : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L))
    (X : Fin m → Fin n → L) : Prop :=
  (∀ i, X i ∈ W) ∧ LinearIndependent L X ∧ ∀ i j, hf q M (X i) (X j) = 0

open Classical in
/- English proof (translation)
Rewrite using `[cntT, ← Set.ncard_coe_finset]`. Use `congr 1`. Use extensionality with `X`. Simplify using `[isoP]`.
-/
theorem iso_cntT_zero_eq [Fintype L] {n m q : ℕ} (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) :
    cntT q M W (0 : Matrix (Fin m) (Fin m) L) = (Finset.univ.filter (isoP (m := m) q M W)).card := by
  rw [cntT, ← Set.ncard_coe_finset]
  congr 1
  ext X
  simp [isoP]

open Classical in
/- English proof (translation)
Establish `hq : q ≠ 0`. Introduce and unpack `rfl`. Use `hinv 0` as an intermediate fact. Simplify using `at this`. Establish `hzero : ∀ v w, hf q M v w = 0 → hf q M w v = 0` using `fun v w h => by`.

Rewrite using `[hf_symm hadd hinv hM v w, h, zero_pow hq]`. Rewrite using `[← Finset.card_univ, ← Finset.card_product]`. Use `Finset.card_nbij' (fun X => ((fun i => hf q M (X i.succ) y), fun i => X i.succ - hf q M (X i.succ) y • x)) (fun p => Fin.cons x (fun i => p.2 i + p.1 i • x)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `X hX`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX`.

Take `⟨⟨hW, hli, hiso⟩, hX0⟩` from `hX`. Simplify using `only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq]`. Use `⟨fun i => ?_, ?_, fun i j => ?_⟩` and prove the remaining obligations. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `W.sub_mem (hW _) (W.smul_mem _ hxW)`.

Use `show hf q M _ x = 0`. Rewrite using `[hf_sub_left, hf_smul_left, hxx, mul_zero, sub_zero, ← hX0]`. Conclude with `hiso _ _`. Use `show hf q M _ y = 0`. Rewrite using `[hf_sub_left, hf_smul_left, hxy, mul_one, sub_self]`.

Establish `h` using `hli`. Rewrite `h` using `[← Fin.cons_self_tail X, hX0]`. Conclude with `iso_li_tail x _ _ h`. Simplify using `only [hf_sub_left, hf_sub_right hq hadd, hf_smul_left, hf_smul_right]`. Rewrite using `[← hX0]`.

Simplify using `[hiso]`. Introduce and unpack `⟨a, U⟩ hp`. Simplify using `only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq] at hp`. Take `⟨hUW, hUli, hUiso⟩` from `hp`. Establish `hU : ∀ i, U i ∈ W ∧ hf q M (U i) x = 0 ∧ hf q M (U i) y = 0` using `fun i => by`.

Use `hUW i` as an intermediate fact. Simplify using `only [Submodule.mem_inf, LinearMap.mem_ker] at this`. Conclude with `⟨this.1.1, this.1.2, this.2⟩`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]`. Use `⟨⟨fun i => ?_, ?_, fun i j => ?_⟩, rfl⟩` and prove the remaining obligations.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hxW`. Simplify using `only [Fin.cons_succ]`. Conclude with `W.add_mem (hU j).1 (W.smul_mem _ hxW)`. Conclude with `iso_li_cons x U a (hfL q M y) hxy (fun i => (hU i).2.2) hUli`.

Apply the tactic sequence `refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Conclude with `hxx`. Simplify using `only [hf_add_right hadd, hf_smul_right, hxx, mul_zero, add_zero]`. Conclude with `hzero _ _ (hU j').2.1`.

Simplify using `only [hf_add_left, hf_smul_left, hxx, mul_zero, add_zero]`. Conclude with `(hU i').2.1`. Simplify using `only [hf_add_left, hf_add_right hadd, hf_smul_left, hf_smul_right, hxx, (hU i').2.1, hzero _ _ (hU j').2.1, hUiso]`. Expand and normalize the polynomial expressions, which then agree. Introduce `X hX`.

Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[hX.2]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨a, U⟩ hp`. Simplify using `only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq] at hp`. Establish `hUy : ∀ i, hf q M (U i) y = 0` using `fun i => by`. Use `hp.1 i` as an intermediate fact. Simplify using `only [Submodule.mem_inf, LinearMap.mem_ker] at this`.

Conclude with `this.2`. Establish `ha : ∀ i, hf q M (U i + a i • x) y = a i` using `fun i => by`. Rewrite using `[hf_add_left, hf_smul_left, hxy, hUy, mul_one, zero_add]`. Simplify using `only [Fin.cons_succ]`. Use `Prod.ext (funext fun i => ha i) (funext fun i => ?_)` and prove the remaining obligations.

Simplify using `only [ha]`. Simplify using the standard rewrite rules.
-/
theorem iso_fiber [Fintype L] {n c q : ℕ} {M : Matrix (Fin n) (Fin n) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : IsHerm q M) (W : Submodule L (Fin n → L)) (x y : Fin n → L)
    (hxW : x ∈ W) (hyW : y ∈ W) (hxx : hf q M x x = 0) (hxy : hf q M x y = 1) :
    (Finset.univ.filter (fun X : Fin (c + 1) → Fin n → L => isoP q M W X ∧ X 0 = x)).card =
      Fintype.card (Fin c → L) * (Finset.univ.filter (isoP (m := c) q M
        (W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)))).card := by
  have hq : q ≠ 0 := by
    rintro rfl
    have := hinv 0
    simp at this
  have hzero : ∀ v w, hf q M v w = 0 → hf q M w v = 0 := fun v w h => by
    rw [hf_symm hadd hinv hM v w, h, zero_pow hq]
  rw [← Finset.card_univ, ← Finset.card_product]
  refine Finset.card_nbij'
    (fun X => ((fun i => hf q M (X i.succ) y), fun i => X i.succ - hf q M (X i.succ) y • x))
    (fun p => Fin.cons x (fun i => p.2 i + p.1 i • x)) ?_ ?_ ?_ ?_
  · rintro X hX
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX
    obtain ⟨⟨hW, hli, hiso⟩, hX0⟩ := hX
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq]
    refine ⟨fun i => ?_, ?_, fun i j => ?_⟩
    · refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
      · exact W.sub_mem (hW _) (W.smul_mem _ hxW)
      · show hf q M _ x = 0
        rw [hf_sub_left, hf_smul_left, hxx, mul_zero, sub_zero, ← hX0]
        exact hiso _ _
      · show hf q M _ y = 0
        rw [hf_sub_left, hf_smul_left, hxy, mul_one, sub_self]
    · have h := hli
      rw [← Fin.cons_self_tail X, hX0] at h
      exact iso_li_tail x _ _ h
    · simp only [hf_sub_left, hf_sub_right hq hadd, hf_smul_left, hf_smul_right]
      rw [← hX0]
      simp [hiso]
  · rintro ⟨a, U⟩ hp
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq] at hp
    obtain ⟨hUW, hUli, hUiso⟩ := hp
    have hU : ∀ i, U i ∈ W ∧ hf q M (U i) x = 0 ∧ hf q M (U i) y = 0 := fun i => by
      have := hUW i
      simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨⟨fun i => ?_, ?_, fun i j => ?_⟩, rfl⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hxW
      · simp only [Fin.cons_succ]
        exact W.add_mem (hU j).1 (W.smul_mem _ hxW)
    · exact iso_li_cons x U a (hfL q M y) hxy (fun i => (hU i).2.2) hUli
    · refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        simp only [Fin.cons_zero, Fin.cons_succ]
      · exact hxx
      · simp only [hf_add_right hadd, hf_smul_right, hxx, mul_zero, add_zero]
        exact hzero _ _ (hU j').2.1
      · simp only [hf_add_left, hf_smul_left, hxx, mul_zero, add_zero]
        exact (hU i').2.1
      · simp only [hf_add_left, hf_add_right hadd, hf_smul_left, hf_smul_right, hxx, (hU i').2.1,
          hzero _ _ (hU j').2.1, hUiso]
        ring
  · intro X hX
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hX.2]
    · simp
  · rintro ⟨a, U⟩ hp
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq] at hp
    have hUy : ∀ i, hf q M (U i) y = 0 := fun i => by
      have := hp.1 i
      simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
      exact this.2
    have ha : ∀ i, hf q M (U i + a i • x) y = a i := fun i => by
      rw [hf_add_left, hf_smul_left, hxy, hUy, mul_one, zero_add]
    simp only [Fin.cons_succ]
    refine Prod.ext (funext fun i => ha i) (funext fun i => ?_)
    simp only [ha]
    simp

end

/- English proof (translation)
Introduce `K L _ _ _ _ _ hKL n M W hM hW c k hk`. Use `set q := Fintype.card K with hq_def`. Establish `hcardL : Fintype.card L = q ^ 2`. Rewrite using `[Module.card_eq_pow_finrank (K := K), hKL]`. Establish `hinv : ∀ a : L, (a ^ q) ^ q = a` using `fun a => by`.

Rewrite using `[← pow_mul, ← sq, ← hcardL, FiniteField.pow_card]`. Establish `hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q`. Take `⟨nn, hp, hpn⟩` from `FiniteField.card K (ringChar K)`. Use `haveI : Fact (ringChar K).Prime := ⟨hp⟩`. Use `haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)`.

Introduce `a b`. Rewrite using `[hq_def, hpn]`. Conclude with `add_pow_char_pow a b (ringChar K) nn`. Establish `hq0 : q ≠ 0` using `Fintype.card_ne_zero`. Establish `hsymm : ∀ a b, hf q M b a = (hf q M a b) ^ q` using `hf_symm hadd hinv hM`.

Rewrite using `[iso_cntT_zero_eq]`. Use `set S : Finset (Fin n → L) := Finset.univ.filter (fun v => v ∈ W ∧ v ≠ 0 ∧ hf q M v v = 0) with hS`. Establish `hmaps : ∀ X ∈ Finset.univ.filter (isoP (m` using `c + 1) q M W), X 0 ∈ S := by`. Introduce `X hX`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, isoP] at hX`.

Simplify using `only [hS, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨hX.1 0, hX.2.1.ne_zero 0, hX.2.2 0 0⟩`. Rewrite using `[Finset.card_eq_sum_card_fiberwise hmaps]`. Establish `hfib : ∀ x ∈ S, (((Finset.univ.filter (isoP (m` using `c + 1) q M W)).filter (fun X => X 0 = x)).card : ℤ) = (q : ℤ) ^ (2 * c) * k := by`. Introduce `x hx`.

Simplify using `only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx`. Take `⟨hxW, hx0, hxx⟩` from `hx`. Establish `hex : ∃ v ∈ W, hf q M x v ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hx0 (hW x hxW h)`. Take `⟨v, hvW, hv⟩` from `hex`. Take `⟨y, hy⟩ : ∃ y : Fin n → L, y = ((hf q M x v)⁻¹ ^ q) • v` from `⟨_, rfl⟩`. Establish `hxy : hf q M x y = 1`. Rewrite using `[hy, hf_smul_right, hinv, inv_mul_cancel₀ hv]`.

Establish `hyW : y ∈ W`. Rewrite using `[hy]`. Conclude with `W.smul_mem _ hvW`. Establish `hyx : hf q M y x = 1` using `by rw [hsymm, hxy, one_pow]`. Use `set W' : Submodule L (Fin n → L) := W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y) with hW'`.

Establish `hmemW' : ∀ u, u ∈ W' ↔ u ∈ W ∧ hf q M u x = 0 ∧ hf q M u y = 0` using `fun u => by`. Simplify using `only [hW', Submodule.mem_inf, LinearMap.mem_ker]`. Conclude with `⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩`. Establish `hdec : ∀ u ∈ W, ∃ u' ∈ W', ∃ α β : L, u = u' + α • x + β • y`. Introduce `u hu`.

Use `⟨u - (hf q M u y - hf q M u x * hf q M y y) • x - hf q M u x • y, ?_, hf q M u y - hf q M u x * hf q M y y, hf q M u x, by abel⟩` and prove the remaining obligations. Rewrite using `[hmemW']`. Use `⟨W.sub_mem (W.sub_mem hu (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hxx, hyx]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hxy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnd : NonDeg q M W'`. Introduce `w hw hwall`. Rewrite `hw` using `[hmemW']`.

Take `⟨hwW, hwx, hwy⟩` from `hw`. Apply `hW w hwW` to reduce the goal to its premises. Introduce `u hu`. Take `⟨u', hu', α, β, rfl⟩` from `hdec u hu`. Rewrite using `[hf_add_right hadd, hf_add_right hadd, hf_smul_right, hf_smul_right, hwall u' hu', hwx, hwy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdim : Module.finrank L W' + 2 = Module.finrank L W`. Set `ψ : W →ₗ[L] L × L` to `LinearMap.prod ((hfL q M x).comp W.subtype) ((hfL q M y).comp W.subtype)`. Establish `hψ : ∀ w : W, ψ w = (hf q M w x, hf q M w y)` using `fun w => rfl`. Establish `hsurj : Function.Surjective ψ`.

Introduce and unpack `⟨s, t⟩`. Use `⟨(t - s * hf q M y y) • ⟨x, hxW⟩ + s • ⟨y, hyW⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ]`. Simplify using `only [Submodule.coe_add, Submodule.coe_smul, hf_add_left, hf_smul_left, hxx, hyx, hxy]`. Apply the tactic sequence `ext <;> simp <;> ring`.

Establish `hrange : LinearMap.range ψ = ⊤` using `LinearMap.range_eq_top.2 hsurj`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker ψ`. Rewrite `hrn` using `[hrange, finrank_top, Module.finrank_prod, Module.finrank_self]`. Establish `hmap : (LinearMap.ker ψ).map W.subtype = W'`. Use extensionality with `u`.

Rewrite using `[hmemW', Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Rewrite `hw` using `[LinearMap.mem_ker, hψ, Prod.mk_eq_zero]`. Conclude with `⟨w.2, hw.1, hw.2⟩`.

Introduce and unpack `⟨huW, hux, huy⟩`. Use `⟨⟨u, huW⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, hψ, Prod.mk_eq_zero]`. Conclude with `⟨hux, huy⟩`. Establish `hfr : Module.finrank L W' = Module.finrank L (LinearMap.ker ψ)`.

Rewrite using `[← hmap]`. Conclude with `(Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq.symm`. Use linear arithmetic over natural numbers and integers. Establish `hkW'` using `hk W' hnd hdim`. Rewrite `hkW'` using `[iso_cntT_zero_eq]`.

Rewrite using `[Finset.filter_filter, iso_fiber hadd hinv hM W x y hxW hyW hxx hxy]`. Use `push_cast`. Rewrite using `[hkW', Fintype.card_fun, Fintype.card_fin, hcardL]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hval` using `hv K L hKL n M W hM hW 0 (by rw [zero_pow hq0])`. Simplify using `only [if_true] at hval`. Establish `hT : ({v : Fin n → L | v ∈ W ∧ hf q M v v = 0}.ncard) = (Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).card`. Rewrite using `[← Set.ncard_coe_finset]`. Use `congr 1`.

Use extensionality with `v`. Simplify using the standard rewrite rules. Establish `hS' : S = (Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).erase 0`. Use extensionality with `v`. Simplify using `only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]`.

The claim follows by propositional logic. Establish `h0mem : (0 : Fin n → L) ∈ Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0`. Simplify using `[hf_zero_left]`. Establish `hcardS` using `Finset.card_erase_add_one h0mem`. Rewrite `hcardS` using `[← hS']`.

Rewrite `hval` using `[hT]`. Use `push_cast`. Rewrite using `[Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]`. Establish `hScast : (S.card : ℤ) = valZ q (Module.finrank L W) - 1`. Establish `h1 : (S.card : ℤ) + 1 = ((Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).card : ℤ)`.

Conclude with `hcardS` after adjusting the coercions. Rewrite `hval` using `[← hq_def]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hScast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isoPeel_of_valCount (hv : ValCount) : IsoPeel := by
  intro K L _ _ _ _ _ hKL n M W hM hW c k hk
  classical
  set q := Fintype.card K with hq_def
  have hcardL : Fintype.card L = q ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K), hKL]
  have hinv : ∀ a : L, (a ^ q) ^ q = a := fun a => by
    rw [← pow_mul, ← sq, ← hcardL, FiniteField.pow_card]
  have hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q := by
    obtain ⟨nn, hp, hpn⟩ := FiniteField.card K (ringChar K)
    haveI : Fact (ringChar K).Prime := ⟨hp⟩
    haveI : CharP L (ringChar K) :=
      charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
    intro a b
    rw [hq_def, hpn]
    exact add_pow_char_pow a b (ringChar K) nn
  have hq0 : q ≠ 0 := Fintype.card_ne_zero
  have hsymm : ∀ a b, hf q M b a = (hf q M a b) ^ q := hf_symm hadd hinv hM
  rw [iso_cntT_zero_eq]
  set S : Finset (Fin n → L) := Finset.univ.filter (fun v => v ∈ W ∧ v ≠ 0 ∧ hf q M v v = 0) with hS
  have hmaps : ∀ X ∈ Finset.univ.filter (isoP (m := c + 1) q M W), X 0 ∈ S := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isoP] at hX
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hX.1 0, hX.2.1.ne_zero 0, hX.2.2 0 0⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]

  have hfib : ∀ x ∈ S, (((Finset.univ.filter (isoP (m := c + 1) q M W)).filter
      (fun X => X 0 = x)).card : ℤ) = (q : ℤ) ^ (2 * c) * k := by
    intro x hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxW, hx0, hxx⟩ := hx
    have hex : ∃ v ∈ W, hf q M x v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (hW x hxW h)
    obtain ⟨v, hvW, hv⟩ := hex
    obtain ⟨y, hy⟩ : ∃ y : Fin n → L, y = ((hf q M x v)⁻¹ ^ q) • v := ⟨_, rfl⟩
    have hxy : hf q M x y = 1 := by
      rw [hy, hf_smul_right, hinv, inv_mul_cancel₀ hv]
    have hyW : y ∈ W := by
      rw [hy]
      exact W.smul_mem _ hvW
    have hyx : hf q M y x = 1 := by rw [hsymm, hxy, one_pow]
    set W' : Submodule L (Fin n → L) :=
      W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y) with hW'
    have hmemW' : ∀ u, u ∈ W' ↔ u ∈ W ∧ hf q M u x = 0 ∧ hf q M u y = 0 := fun u => by
      simp only [hW', Submodule.mem_inf, LinearMap.mem_ker]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

    have hdec : ∀ u ∈ W, ∃ u' ∈ W', ∃ α β : L, u = u' + α • x + β • y := by
      intro u hu
      refine ⟨u - (hf q M u y - hf q M u x * hf q M y y) • x - hf q M u x • y, ?_,
        hf q M u y - hf q M u x * hf q M y y, hf q M u x, by abel⟩
      rw [hmemW']
      refine ⟨W.sub_mem (W.sub_mem hu (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_, ?_⟩
      · rw [hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hxx, hyx]
        ring
      · rw [hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hxy]
        ring
    have hnd : NonDeg q M W' := by
      intro w hw hwall
      rw [hmemW'] at hw
      obtain ⟨hwW, hwx, hwy⟩ := hw
      apply hW w hwW
      intro u hu
      obtain ⟨u', hu', α, β, rfl⟩ := hdec u hu
      rw [hf_add_right hadd, hf_add_right hadd, hf_smul_right, hf_smul_right, hwall u' hu', hwx, hwy]
      ring

    have hdim : Module.finrank L W' + 2 = Module.finrank L W := by
      let ψ : W →ₗ[L] L × L := LinearMap.prod ((hfL q M x).comp W.subtype) ((hfL q M y).comp W.subtype)
      have hψ : ∀ w : W, ψ w = (hf q M w x, hf q M w y) := fun w => rfl
      have hsurj : Function.Surjective ψ := by
        rintro ⟨s, t⟩
        refine ⟨(t - s * hf q M y y) • ⟨x, hxW⟩ + s • ⟨y, hyW⟩, ?_⟩
        rw [hψ]
        simp only [Submodule.coe_add, Submodule.coe_smul, hf_add_left, hf_smul_left, hxx, hyx, hxy]
        ext <;> simp <;> ring
      have hrange : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.2 hsurj
      have hrn := LinearMap.finrank_range_add_finrank_ker ψ
      rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at hrn
      have hmap : (LinearMap.ker ψ).map W.subtype = W' := by
        ext u
        rw [hmemW', Submodule.mem_map]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [LinearMap.mem_ker, hψ, Prod.mk_eq_zero] at hw
          exact ⟨w.2, hw.1, hw.2⟩
        · rintro ⟨huW, hux, huy⟩
          refine ⟨⟨u, huW⟩, ?_, rfl⟩
          rw [LinearMap.mem_ker, hψ, Prod.mk_eq_zero]
          exact ⟨hux, huy⟩
      have hfr : Module.finrank L W' = Module.finrank L (LinearMap.ker ψ) := by
        rw [← hmap]
        exact (Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq.symm
      omega
    have hkW' := hk W' hnd hdim
    rw [iso_cntT_zero_eq] at hkW'
    rw [Finset.filter_filter, iso_fiber hadd hinv hM W x y hxW hyW hxx hxy]
    push_cast
    rw [hkW', Fintype.card_fun, Fintype.card_fin, hcardL]
    push_cast
    ring

  have hval := hv K L hKL n M W hM hW 0 (by rw [zero_pow hq0])
  simp only [if_true] at hval
  have hT : ({v : Fin n → L | v ∈ W ∧ hf q M v v = 0}.ncard) =
      (Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  have hS' : S = (Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).erase 0 := by
    ext v
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  have h0mem : (0 : Fin n → L) ∈ Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0 := by
    simp [hf_zero_left]
  have hcardS := Finset.card_erase_add_one h0mem
  rw [← hS'] at hcardS
  rw [hT] at hval
  push_cast
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  have hScast : (S.card : ℤ) = valZ q (Module.finrank L W) - 1 := by
    have h1 : (S.card : ℤ) + 1 = ((Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).card : ℤ) := by
      exact_mod_cast hcardS
    rw [← hq_def] at hval
    linarith
  rw [hScast]
  ring

/- English proof (translation)
The claim follows from `isoPeel_of_valCount valuation_count`.
-/
theorem isotropic_valuation_peel : IsoPeel := isoPeel_of_valCount valuation_count

end DensInertW
